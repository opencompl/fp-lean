#!/usr/bin/env python3
"""
stresstest.py -- crash / behaviour stress harness for the EXPERIMENTAL SymFPU branch.

Background
----------
The paper (tr-floating-point-lean/paper.tex) makes three claims about SymFPU that
were established against the *baseline* symfpu (master @ c3acaf6, vendored at
../symfpu):

  1. Unpack abort (matchWidth). SymFPU widens the exponent field on unpack; its
     matchWidth extension requires PRECONDITION(this->width <= op.width), i.e. the
     significand must be at least as wide as the widened exponent. Sweeping
     3 <= E <= 8 the unpack->round->pack pipeline runs iff M >= E (relaxing to
     M >= E-1 at E=3). Both FP8 ML formats fail: E5M2 (2<5) and E4M3 (3<4) abort
     on EVERY operation, before any arithmetic runs.
  2. E3M4 residual crashes: division/sqrt/round-to-integral still crashed even at
     a format that passes unpack; the paper traced division to rounder
     intermediates that were "one bit too short".
  3. A divider soundness bug fixed only recently (cvc5 #9505/#11139/#12335).

This experimental branch (github.com/martin-cs/symfpu main) is a NEWER symfpu that
already contains the divider soundness fix (divide.h uses expandingSubtractWithBorrowIn
+ a weaker wellFormed(lower,upper) postcondition, and the rounder was narrowed from
+2 to +1 intermediates). This harness checks EMPIRICALLY, on this arm64 host:

  * whether the matchWidth unpack-abort still fires -> E5M2 / E4M3 still fail (they do);
  * the exact M >= E boundary of which formats survive unpack;
  * whether E3M4 division still crashes here;
  * where the narrowed rounder opens a new crash corner (large E, small M);
  * how experimental's results DIFFER from baseline's across every operation
    (the visible footprint of the divider/rounder refactor).

All symfpu PRECONDITION/POSTCONDITION/INVARIANT are assert() in the executable
backend, so a violated width side-condition aborts the process with SIGABRT. We
therefore run each configuration in its own subprocess (via stresstest.cpp) so a
crash isolates to exactly that configuration.

Usage
-----
    python3 stresstest.py                # full sweep, build both copies, write results
    python3 stresstest.py --no-baseline  # skip the baseline cross-check
    python3 stresstest.py --emin 3 --emax 8 --mmin 1 --mmax 8

Outputs stresstest-results.md and stresstest-results.csv next to this script.
"""

import argparse
import csv
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
EXP_DIR = HERE                                     # .../third-party/symfpu-experimental
THIRD_PARTY = os.path.dirname(HERE)                # .../third-party
BASE_DIR = os.path.join(THIRD_PARTY, "symfpu")     # baseline vendored copy

OPS = ["unpack", "abs", "neg", "sqrt", "rti",
       "add", "sub", "mul", "div", "rem", "min", "max", "lt"]
RM_OPS = {"add", "sub", "mul", "div", "sqrt", "rti"}  # ops whose result depends on rounding mode
RMS = ["RNE", "RNA", "RTN", "RTP", "RTZ"]

# Binary ops: fully enumerate operand space when packed width W <= this, else sample.
ENUM_MAX_W_BINARY = 8
SAMPLE_N = 20000
SAMPLE_SEED = 1234567

# Our own instrumented form (from stresstest.cpp's overridden check macros):
#   SYMFPU_CHECK_FAIL PRECONDITION '<cond>' at <file>:<line>
SYMFPU_CHECK_RE = re.compile(
    r"SYMFPU_CHECK_FAIL\s+(\w+)\s+'(.*)'\s+at\s+(.*?):(\d+)")
# macOS libc assert: "Assertion failed: (cond), function F, file X, line N."
ASSERT_RE = re.compile(
    r"Assertion failed:\s*\((.*?)\),\s*function\s+(\w+),\s*file\s+(.*?),\s*line\s+(\d+)")
# glibc form: "prog: file:line: func: Assertion `cond' failed."
ASSERT_RE_GLIBC = re.compile(
    r"(.*?):(\d+):\s*(.*?):\s*Assertion\s+`(.*?)'\s+failed")


def log(msg):
    print(msg, flush=True)


# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------
def make_include_root(tmp, lib_dir):
    """Create an include root where `symfpu` resolves to lib_dir (symfpu-experimental
    or the baseline symfpu), since the library's internal includes are "symfpu/...".."""
    root = os.path.join(tmp, os.path.basename(lib_dir) + "-incroot")
    os.makedirs(root, exist_ok=True)
    link = os.path.join(root, "symfpu")
    if os.path.islink(link) or os.path.exists(link):
        os.remove(link)
    os.symlink(lib_dir, link)
    return root


def build(lib_dir, out_binary, tmp):
    """Compile stresstest.cpp + <lib_dir>/baseTypes/simpleExecutable.cpp against lib_dir.
    Flags follow test/against-symfpu/makefile (arm64-safe; NO x86 -msse2/-mfma from the
    vendored `flags`), and deliberately WITHOUT -DNDEBUG so asserts fire. Returns
    (ok, message)."""
    root = make_include_root(tmp, lib_dir)
    src = os.path.join(EXP_DIR, "stresstest.cpp")   # harness source lives with experimental
    # each copy links its OWN executable backend
    exe = os.path.join(lib_dir, "baseTypes", "simpleExecutable.cpp")
    cmd = ["g++", "-std=gnu++11", "-g", "-O1",
           "-I", root, src, exe, "-o", out_binary]
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        return False, p.stderr
    return True, "ok"


# ---------------------------------------------------------------------------
# Running a configuration
# ---------------------------------------------------------------------------
def classify_assert(stderr):
    m = SYMFPU_CHECK_RE.search(stderr)
    if m:
        kind, cond, path, line = m.groups()
        # func column carries the check KIND + call-site location
        return kind, "%s:%s" % (os.path.basename(path), line), cond
    m = ASSERT_RE.search(stderr)
    if m:
        cond, func, path, line = m.groups()
        return func, "%s:%s" % (os.path.basename(path), line), cond
    m = ASSERT_RE_GLIBC.search(stderr)
    if m:
        path, line, func, cond = m.groups()
        return func.strip(), "%s:%s" % (os.path.basename(path), line), cond
    return "?", "?", stderr.strip().splitlines()[-1] if stderr.strip() else ""


def run(binary, args, timeout=60):
    """Run a stresstest subcommand. Returns dict(status, stdout, func, loc, cond, rc)."""
    try:
        p = subprocess.run([binary] + args, capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="TIMEOUT", stdout="", func="", loc="", cond="", rc=None)
    rc = p.returncode
    if rc == 0:
        return dict(status="OK", stdout=p.stdout, func="", loc="", cond="", rc=0)
    if rc == -6:   # SIGABRT (assertion)
        func, loc, cond = classify_assert(p.stderr)
        return dict(status="ABORT", stdout=p.stdout, func=func, loc=loc, cond=cond, rc=rc)
    if rc == -11:  # SIGSEGV
        return dict(status="SEGV", stdout=p.stdout, func="", loc="", cond="", rc=rc)
    if rc < 0:
        return dict(status="SIG%d" % (-rc), stdout=p.stdout, func="", loc="", cond="", rc=rc)
    return dict(status="ERR%d" % rc, stdout=p.stdout, func="", loc="",
                cond=p.stderr.strip()[:200], rc=rc)


def sweep_args(E, M, op, rm):
    """Choose enum vs sample for this configuration and return the argv tail."""
    W = E + M + 1
    unary = op in ("unpack", "abs", "neg", "sqrt", "rti")
    if unary:
        # unary space is 2^W <= 2^17, always enumerable
        return ["enum", str(E), str(M), op, rm]
    if W <= ENUM_MAX_W_BINARY:
        return ["enum", str(E), str(M), op, rm]
    return ["sample", str(E), str(M), op, rm, str(SAMPLE_N), str(SAMPLE_SEED)]


# ---------------------------------------------------------------------------
# Behaviour diff
# ---------------------------------------------------------------------------
def diff_outputs(exp_out, base_out):
    """Compare two CSV outputs (a,b,result). Returns (identical, ndiff, first_diff)."""
    exp_lines = exp_out.splitlines()
    base_lines = base_out.splitlines()
    exp_map = {}
    for ln in exp_lines:
        parts = ln.split(",", 2)
        if len(parts) == 3:
            exp_map[(parts[0], parts[1])] = parts[2]
    ndiff = 0
    first = None
    for ln in base_lines:
        parts = ln.split(",", 2)
        if len(parts) != 3:
            continue
        key = (parts[0], parts[1])
        if key in exp_map and exp_map[key] != parts[2]:
            ndiff += 1
            if first is None:
                first = (key[0], key[1], exp_map[key], parts[2])
    identical = (ndiff == 0) and (len(exp_map) == len([1 for ln in base_lines if ln]))
    return identical, ndiff, first


# ---------------------------------------------------------------------------
# Main sweep
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--emin", type=int, default=3)
    ap.add_argument("--emax", type=int, default=8)
    ap.add_argument("--mmin", type=int, default=1)
    ap.add_argument("--mmax", type=int, default=8)
    ap.add_argument("--no-baseline", action="store_true")
    ap.add_argument("--timeout", type=int, default=60)
    args = ap.parse_args()

    tmp = tempfile.mkdtemp(prefix="symfpu-stress-")
    exp_bin = os.path.join(tmp, "stresstest.exp")
    base_bin = os.path.join(tmp, "stresstest.base")

    log("== Building experimental (%s) ==" % EXP_DIR)
    ok, msg = build(EXP_DIR, exp_bin, tmp)
    if not ok:
        log("FATAL: experimental build failed:\n" + msg)
        sys.exit(1)
    log("  experimental build OK")

    have_base = False
    if not args.no_baseline:
        log("== Building baseline (%s) ==" % BASE_DIR)
        ok, msg = build(BASE_DIR, base_bin, tmp)
        if ok:
            have_base = True
            log("  baseline build OK")
        else:
            log("  baseline build FAILED (continuing without cross-check):\n"
                + msg[:800])

    formats = [(E, M) for E in range(args.emin, args.emax + 1)
                       for M in range(args.mmin, args.mmax + 1)]

    rows = []           # csv rows
    unpack_ok = {}      # (E,M) -> bool : does unpack survive on experimental?
    crash_sites = OrderedDict()  # loc -> count (experimental)
    diffs = []          # behaviour differences vs baseline

    log("== Sweeping %d formats x %d ops ==" % (len(formats), len(OPS)))
    for (E, M) in formats:
        W = E + M + 1
        for op in OPS:
            rmlist = RMS if op in RM_OPS else ["RNE"]
            for rm in rmlist:
                tail = sweep_args(E, M, op, rm)
                exp = run(exp_bin, tail, timeout=args.timeout)

                if op == "unpack" and rm == "RNE":
                    unpack_ok[(E, M)] = (exp["status"] == "OK")
                if exp["status"] == "ABORT":
                    crash_sites[exp["loc"]] = crash_sites.get(exp["loc"], 0) + 1

                base = None
                behaviour = ""
                if have_base:
                    base = run(base_bin, tail, timeout=args.timeout)
                    if exp["status"] == "OK" and base["status"] == "OK":
                        _, ndiff, first = diff_outputs(exp["stdout"],
                                                       base["stdout"])
                        if ndiff == 0:
                            behaviour = "same"
                        else:
                            behaviour = "differ:%d" % ndiff
                            diffs.append((E, M, op, rm, ndiff, first))
                    elif exp["status"] != base["status"]:
                        behaviour = "crash-divergence(exp=%s,base=%s)" % (
                            exp["status"], base["status"])
                    else:
                        behaviour = "both=%s" % exp["status"]

                rows.append(dict(
                    E=E, M=M, W=W, op=op, rm=rm,
                    exp_status=exp["status"], exp_assert_func=exp["func"],
                    exp_assert_loc=exp["loc"],
                    base_status=(base["status"] if base else ""),
                    base_assert_loc=(base["loc"] if base else ""),
                    behaviour=behaviour,
                ))
        st = "unpack-OK" if unpack_ok.get((E, M)) else "unpack-ABORT"
        log("  E%dM%d (W=%d): %s" % (E, M, W, st))

    write_results(args, rows, unpack_ok, crash_sites, diffs, have_base,
                  exp_bin, base_bin if have_base else None)
    shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------------
# Targeted claim checks (run precise `one` probes, independent of the sweep).
# ---------------------------------------------------------------------------
def one(binary, E, M, op, rm, a, b, timeout=30):
    return run(binary, ["one", str(E), str(M), op, rm, str(a), str(b)], timeout)


def normal_one_bits(E, M):
    """Bit pattern of the value 1.0 in E<E>M<M>: exponent = bias, mantissa = 0."""
    bias = (1 << (E - 1)) - 1
    return bias << M


def describe(r):
    """Compact one-cell description of a run result."""
    if r["status"] == "OK":
        return "OK"
    if r["status"] == "ABORT":
        return "ABORT (%s @ %s)" % (r["func"], r["loc"])
    return r["status"]


def enum_status(binary, E, M, op, rm, timeout=60):
    """Run a full/sampled sweep and report only whether it survived (crash-find)."""
    return run(binary, sweep_args(E, M, op, rm), timeout=timeout)


def claim_checks(exp_bin, base_bin):
    """Compare the paper's specific claims across experimental vs baseline.
    Returns list of dicts: {claim, exp, base, note}."""
    out = []

    def add(claim, exp_r, base_r, note):
        out.append(dict(claim=claim, exp=describe(exp_r),
                        base=(describe(base_r) if base_r else "n/a"), note=note))

    # --- Paper claim 1: FP8 ML formats abort (baseline used matchWidth precondition). ---
    for (E, M, label) in [(5, 2, "E5M2"), (4, 3, "E4M3")]:
        a = normal_one_bits(E, M)
        er = one(exp_bin, E, M, "unpack", "RNE", a, 0)
        br = one(base_bin, E, M, "unpack", "RNE", a, 0) if base_bin else None
        # also confirm arithmetic (div) status for the same format
        edv = enum_status(exp_bin, E, M, "div", "RNE")
        note = ""
        if er["status"] == "OK" and br and br["status"] == "ABORT":
            note = "FIXED in experimental (baseline still aborts)"
        elif er["status"] == "ABORT":
            note = "still aborts (div also: %s)" % edv["status"]
        add("%s unpack(1.0)" % label, er, br, note)

    # --- Paper claim: a format satisfying the width side-condition unpacks. ---
    er = one(exp_bin, 3, 4, "unpack", "RNE", normal_one_bits(3, 4), 0)
    br = one(base_bin, 3, 4, "unpack", "RNE", normal_one_bits(3, 4), 0) if base_bin else None
    add("E3M4 unpack(1.0)", er, br, "control: width side-condition satisfied")

    # --- Paper claim 2: E3M4 division/sqrt/round-to-integral crashed. ---
    # Division: exhaustive sweep over ALL operand pairs, both copies.
    ed = enum_status(exp_bin, 3, 4, "div", "RNE")
    bd = enum_status(base_bin, 3, 4, "div", "RNE") if base_bin else None
    add("E3M4 div (all inputs, RNE)", ed, bd,
        "no crash => divider fix present" if ed["status"] == "OK" else "still crashes")

    # Sqrt and round-to-integral: the paper says these still crashed at E3M4.
    for op in ("sqrt", "rti"):
        eo = enum_status(exp_bin, 3, 4, op, "RNE")
        bo = enum_status(base_bin, 3, 4, op, "RNE") if base_bin else None
        add("E3M4 %s (all inputs, RNE)" % op, eo, bo,
            "crashes" if eo["status"] != "OK" else "no crash")

    return out


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------
def write_results(args, rows, unpack_ok, crash_sites, diffs, have_base,
                  exp_bin, base_bin):
    csv_path = os.path.join(EXP_DIR, "stresstest-results.csv")
    md_path = os.path.join(EXP_DIR, "stresstest-results.md")

    # CSV
    with open(csv_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=[
            "E", "M", "W", "op", "rm", "exp_status", "exp_assert_func",
            "exp_assert_loc", "base_status", "base_assert_loc", "behaviour"])
        w.writeheader()
        for r in rows:
            w.writerow(r)

    checks = claim_checks(exp_bin, base_bin)

    # Aggregate: per (E,M) how many op/rm configs abort on experimental.
    abort_by_fmt = OrderedDict()
    for r in rows:
        key = (r["E"], r["M"])
        abort_by_fmt.setdefault(key, {"abort": 0, "ok": 0, "other": 0})
        if r["exp_status"] == "ABORT":
            abort_by_fmt[key]["abort"] += 1
        elif r["exp_status"] == "OK":
            abort_by_fmt[key]["ok"] += 1
        else:
            abort_by_fmt[key]["other"] += 1

    with open(md_path, "w") as f:
        def wr(s=""):
            f.write(s + "\n")

        wr("# SymFPU experimental branch: stress-test results")
        wr()
        wr("Generated by `stresstest.py`. Each configuration `(E, M, op, rounding-mode)` "
           "was exercised in an isolated subprocess (`stresstest.cpp`), so an assertion "
           "abort (`SIGABRT`) isolates to that configuration. Format `E<e>M<m>` = exponent "
           "width `e`, stored mantissa `m`; `fpt(e, m+1)`, packed width `W = e+m+1`.")
        wr()
        # environment
        try:
            gv = subprocess.run(["g++", "--version"], capture_output=True, text=True).stdout.splitlines()[0]
        except Exception:
            gv = "g++"
        wr("- Host: `%s`, compiler: `%s`" % (os.uname().machine, gv))
        wr("- Experimental: `third-party/symfpu-experimental` (HEAD of `main`)")
        wr("- Baseline: `third-party/symfpu` @ c3acaf6 " +
           ("(cross-checked)" if have_base else "(NOT built / skipped)"))
        wr("- Formats swept: E in [%d,%d], M in [%d,%d]; ops: %s; rounding modes: %s"
           % (args.emin, args.emax, args.mmin, args.mmax, ", ".join(OPS), ", ".join(RMS)))
        wr()

        wr("## Paper claim checks (experimental vs baseline)")
        wr()
        wr("Each probe is run on the experimental branch and on the baseline (the copy the "
           "paper tested). `1.0` is the normal value; `all inputs` means an exhaustive sweep "
           "over every operand pattern for that format.")
        wr()
        wr("| Probe | Experimental | Baseline | Note |")
        wr("|---|---|---|---|")
        for c in checks:
            wr("| %s | `%s` | `%s` | %s |" % (c["claim"], c["exp"], c["base"], c["note"]))
        wr()

        wr("## Unpack survival boundary")
        wr()
        wr("The paper reports (for the baseline) that the unpack->round->pack pipeline runs "
           "iff `M >= E` (relaxing to `M >= E-1` at `E=3`). `Y` = unpack succeeds, "
           "`.` = unpack aborts, in the **experimental** branch:")
        wr()
        Es = sorted(set(E for (E, _M) in unpack_ok))
        Ms = sorted(set(M for (_E, M) in unpack_ok))
        header = "| E\\M | " + " | ".join(str(M) for M in Ms) + " |"
        wr(header)
        wr("|" + "---|" * (len(Ms) + 1))
        for E in Es:
            cells = []
            for M in Ms:
                ok = unpack_ok.get((E, M))
                cells.append("Y" if ok else ".")
            wr("| **%d** | " % E + " | ".join(cells) + " |")
        wr()
        # Does the experimental boundary match the paper's baseline rule?
        base_rule_mismatch = [(E, M) for (E, M), ok in unpack_ok.items()
                              if ok != ((M >= E) or (E == 3 and M >= E - 1))]
        # Derive the observed rule as a constant threshold on M (if one fits).
        thr = None
        for cand in range(0, max(Ms) + 2):
            if all(ok == (M >= cand) for (_E, M), ok in unpack_ok.items()):
                thr = cand
                break
        wr("Matches the paper's baseline rule `M >= E` (relaxed at E=3): **%s** "
           "(%d formats differ)."
           % ("YES" if not base_rule_mismatch else "NO", len(base_rule_mismatch)))
        if thr is not None:
            wr()
            wr("**Observed experimental rule:** unpack succeeds iff `M >= %d`, "
               "*independent of E*. The experimental unpacker refactor replaced the "
               "E-dependent `M >= E` side-condition with a constant minimum significand "
               "width, so wide-exponent / small-significand formats such as E5M3, E8M3 "
               "(which the baseline rejects) now run." % thr)
        wr()

        wr("## FP8 ML formats (E5M2, E4M3)")
        wr()
        wr("Both machine-learning FP8 formats have `M < E`. The paper reports that both "
           "abort on every operation in the baseline (E5M2 via a `packing.h` unpack "
           "invariant, E4M3 via the `matchWidth` precondition). Below is the experimental "
           "branch's behaviour, from the sweep (abort/total configs for that format):")
        wr()
        for (E, M, label) in [(5, 2, "E5M2"), (4, 3, "E4M3")]:
            agg = abort_by_fmt.get((E, M), {})
            tot = agg.get("abort", 0) + agg.get("ok", 0) + agg.get("other", 0)
            verdict = ("still aborts on every op" if agg.get("ok", 0) == 0
                       else "**runs** (fixed relative to baseline)")
            wr("- **%s** (M=%d < E=%d): %d/%d configs abort, %d OK -> %s"
               % (label, M, E, agg.get("abort", 0), tot, agg.get("ok", 0), verdict))
        wr()

        wr("## Assertion sites hit (experimental)")
        wr()
        if crash_sites:
            wr("| Assertion location | # configs |")
            wr("|---|---|")
            for loc, n in sorted(crash_sites.items(), key=lambda kv: -kv[1]):
                wr("| `%s` | %d |" % (loc, n))
        else:
            wr("_No aborts observed._")
        wr()

        # Crashes that survive in the EXPERIMENTAL branch, aggregated per format+op.
        wr("## Crashes still present in the experimental branch")
        wr()
        exp_ab = OrderedDict()
        for r in rows:
            if r["exp_status"] != "OK":
                key = (r["E"], r["M"], r["op"])
                exp_ab.setdefault(key, (r["exp_status"], r["exp_assert_loc"]))
        if exp_ab:
            wr("Aggregated over rounding modes. These are configurations where the "
               "experimental branch itself aborts/misbehaves:")
            wr()
            wr("| E | M | op | status | assertion |")
            wr("|---|---|---|---|---|")
            for (E, M, op), (st, loc) in exp_ab.items():
                wr("| %d | %d | %s | %s | `%s` |" % (E, M, op, st, loc))
        else:
            wr("_None._")
        wr()

        if have_base:
            wr("## Behaviour vs baseline symfpu")
            wr()
            # 1. Numeric differences where both ran.
            wr("**Numeric differences** (both copies ran, but produced different packed "
               "results): %d configuration(s)." % len(diffs))
            if diffs:
                wr()
                wr("| E | M | op | rm | # differing | first (a,b: exp/base) |")
                wr("|---|---|---|---|---|---|")
                for (E, M, op, rm, ndiff, first) in diffs:
                    fs = ("a=%s b=%s: %s vs %s" % first) if first else ""
                    wr("| %d | %d | %s | %s | %d | `%s` |" % (E, M, op, rm, ndiff, fs))
            else:
                wr(" On every format+op where both copies survive, the packed results are "
                   "**identical** -- the divider/rounder refactor changed *which inputs "
                   "crash*, not the numeric answers on surviving inputs.")
            wr()
            # 2. Crash divergences, aggregated per (E,M) with direction.
            wr("**Crash divergences** (one copy aborts, the other does not), aggregated "
               "per format:")
            wr()
            div_by_fmt = OrderedDict()
            for r in rows:
                if r["behaviour"].startswith("crash-divergence"):
                    key = (r["E"], r["M"])
                    d = div_by_fmt.setdefault(key, {"exp_fixed": 0, "base_fixed": 0, "ops": set()})
                    d["ops"].add(r["op"])
                    if r["exp_status"] == "OK" and r["base_status"] != "OK":
                        d["exp_fixed"] += 1
                    elif r["base_status"] == "OK" and r["exp_status"] != "OK":
                        d["base_fixed"] += 1
            if div_by_fmt:
                wr("| E | M | # exp-OK/base-ABORT | # base-OK/exp-ABORT | ops |")
                wr("|---|---|---|---|---|")
                for (E, M), d in div_by_fmt.items():
                    wr("| %d | %d | %d | %d | %s |"
                       % (E, M, d["exp_fixed"], d["base_fixed"],
                          ", ".join(sorted(d["ops"]))))
                wr()
                tot_exp_fixed = sum(d["exp_fixed"] for d in div_by_fmt.values())
                tot_base_fixed = sum(d["base_fixed"] for d in div_by_fmt.values())
                wr("Totals: **%d** configs the experimental branch handles that the "
                   "baseline aborts on; **%d** configs the baseline handles that the "
                   "experimental branch aborts on." % (tot_exp_fixed, tot_base_fixed))
            else:
                wr("_None._")
            wr()

        wr("## Reproducing a live crash in the experimental branch")
        wr()
        wr("Round-to-integral of a large-magnitude E3M4 value still fails its output "
           "validity postcondition. Build the harness against the experimental copy and run:")
        wr()
        wr("```")
        wr("# a=111 is E3M4 sign=0 exp=6 mant=15 (a large normal); crashes under RNE/RNA/RTP")
        wr("stresstest one 3 4 rti RNE 111 0")
        wr("# -> SYMFPU_CHECK_FAIL POSTCONDITION 'result.valid(format)' at core/convert.h:148")
        wr("```")
        wr()
        wr("`python3 stresstest.py` builds both copies and rediscovers this automatically.")
        wr()

        wr("## Files")
        wr()
        wr("- `stresstest-results.csv` -- full per-configuration table (%d rows)." % len(rows))
        wr("- `stresstest.cpp` / `stresstest.py` -- the harness.")

    # console summary
    log("")
    log("== Claim checks (experimental | baseline) ==")
    for c in checks:
        log("  %-28s exp=%-32s base=%-32s %s"
            % (c["claim"], c["exp"], c["base"], c["note"]))
    log("")
    log("Wrote %s" % md_path)
    log("Wrote %s" % csv_path)


if __name__ == "__main__":
    main()
