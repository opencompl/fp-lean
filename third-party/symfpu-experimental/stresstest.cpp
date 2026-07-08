// stresstest.cpp -- crash / behaviour stress harness for SymFPU's executable backend.
//
// This is a standalone driver over symfpu::simpleExecutable (the concrete
// arbitrary-precision "software float" backend that cvc5/Bitwuzla use for
// constant folding and that fp.lean uses for differential testing). It exercises
// unpack + every floating-point operation across arbitrary (E, M) formats so that
// a Python driver (stresstest.py) can detect assertion aborts (SIGABRT), segfaults,
// and behaviour differences between the experimental and baseline SymFPU.
//
// SymFPU's PRECONDITION / POSTCONDITION / INVARIANT are all assert() in this
// backend (baseTypes/simpleExecutable.h), so a violated width side-condition
// terminates the process. We therefore do ONE logical sweep per process and let
// the driver fork a fresh process per configuration; a crash then isolates to
// exactly the offending configuration/input.
//
// Include prefix is "symfpu/..." (as the library expects). The build (see
// stresstest.py) points -I at a root where `symfpu` resolves to whichever copy
// (experimental or baseline) we are testing.
//
// Format convention (matches test/against-symfpu/test.cpp): a paper "E<e>M<m>"
// format uses exponent width e and STORED mantissa width m; symfpu's
// significandWidth INCLUDES the hidden bit, so fpt = (e, m+1) and the packed
// bit-width is W = e + m + 1.  e.g. E3M4 -> fpt(3,5), W=8.

#include <cstddef>
#include <cstdio>
#include <cstdlib>

// Override SymFPU's check macros BEFORE including the library so a failed check
// reports its exact call site (which check, in which file/line) instead of the
// anonymous `assert(b)` inside precondition()/postcondition()/invariant(). This
// lets the driver attribute a crash to, e.g., the `matchWidth` precondition in
// unpackedFloat.h vs. the `wellFormed` postcondition in divide.h. properties.h
// only defines these #ifndef, so our definitions win.
static inline void symfpu_check(const char *kind, const char *cond,
                                const char *file, int line, bool ok) {
  if (!ok) {
    fprintf(stderr, "SYMFPU_CHECK_FAIL %s '%s' at %s:%d\n", kind, cond, file, line);
    fflush(stderr);
    abort();
  }
}
#define PRECONDITION(X)  symfpu_check("PRECONDITION",  #X, __FILE__, __LINE__, (bool)(X))
#define POSTCONDITION(X) symfpu_check("POSTCONDITION", #X, __FILE__, __LINE__, (bool)(X))
#define INVARIANT(X)     symfpu_check("INVARIANT",     #X, __FILE__, __LINE__, (bool)(X))

#include "symfpu/baseTypes/simpleExecutable.h"
#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/add.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/convert.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>

using namespace symfpu::simpleExecutable;
typedef symfpu::unpackedFloat<traits> uf;
typedef traits::ubv ubv;
typedef traits::fpt fpt;
typedef traits::rm rm;

// ----------------------------------------------------------------------------
// Rounding-mode parsing.
// ----------------------------------------------------------------------------
static bool parse_rm(const char *s, rm &out) {
  if (!strcmp(s, "RNE")) { out = traits::RNE(); return true; }
  if (!strcmp(s, "RNA")) { out = traits::RNA(); return true; }
  if (!strcmp(s, "RTN")) { out = traits::RTN(); return true; }
  if (!strcmp(s, "RTP")) { out = traits::RTP(); return true; }
  if (!strcmp(s, "RTZ")) { out = traits::RTZ(); return true; }
  return false;
}

// ----------------------------------------------------------------------------
// Perform ONE operation on packed operands a, b. Returns a result string:
//   "<bits>"      for value-returning ops (the packed result bit pattern), or
//   "P<0|1>"      for the predicate op `lt`.
// May abort() via a failed symfpu assertion -- that is exactly what we want to
// observe (the caller's process dies with SIGABRT and the driver records it).
// ----------------------------------------------------------------------------
static std::string run_op(unsigned E, unsigned M, const std::string &op,
                          rm mode, uint64_t a, uint64_t b) {
  unsigned W = E + M + 1;
  fpt fmt(E, M + 1);
  ubv pa(W, a), pb(W, b);

  // `unpack` isolates the unpack-time abort (the matchWidth precondition) with
  // no arithmetic at all: unpack then repack a single operand.
  if (op == "unpack") {
    uf ua(symfpu::unpack<traits>(fmt, pa));
    return std::to_string(symfpu::pack<traits>(fmt, ua).contents());
  }
  if (op == "abs") {
    uf ua(symfpu::unpack<traits>(fmt, pa));
    uf uc(symfpu::absolute<traits>(fmt, ua));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "neg") {
    uf ua(symfpu::unpack<traits>(fmt, pa));
    uf uc(symfpu::negate<traits>(fmt, ua));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "sqrt") {  // unary, needs rounding mode
    uf ua(symfpu::unpack<traits>(fmt, pa));
    uf uc(symfpu::sqrt<traits>(fmt, mode, ua));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "rti") {   // round-to-integral, unary, needs rounding mode
    uf ua(symfpu::unpack<traits>(fmt, pa));
    uf uc(symfpu::roundToIntegral<traits>(fmt, mode, ua));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }

  // Binary ops.
  uf ua(symfpu::unpack<traits>(fmt, pa));
  uf ub(symfpu::unpack<traits>(fmt, pb));

  if (op == "add") {
    uf uc(symfpu::add<traits>(fmt, mode, ua, ub, traits::prop(true)));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "sub") {
    uf uc(symfpu::add<traits>(fmt, mode, ua, ub, traits::prop(false)));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "mul") {
    uf uc(symfpu::multiply<traits>(fmt, mode, ua, ub));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "div") {
    uf uc(symfpu::divide<traits>(fmt, mode, ua, ub));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "rem") {  // remainder takes no rounding mode
    uf uc(symfpu::remainder<traits>(fmt, ua, ub));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "min") {
    uf uc(symfpu::min<traits>(fmt, ua, ub, ua.getSign()));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "max") {
    uf uc(symfpu::max<traits>(fmt, ua, ub, ua.getSign()));
    return std::to_string(symfpu::pack<traits>(fmt, uc).contents());
  }
  if (op == "lt") {
    bool r = symfpu::lessThan<traits>(fmt, ua, ub);
    return std::string("P") + (r ? "1" : "0");
  }

  fprintf(stderr, "unknown op: %s\n", op.c_str());
  exit(2);
}

static bool is_unary(const std::string &op) {
  return op == "unpack" || op == "abs" || op == "neg" ||
         op == "sqrt" || op == "rti";
}
static bool needs_rm(const std::string &op) {
  return op == "add" || op == "sub" || op == "mul" || op == "div" ||
         op == "sqrt" || op == "rti";
}

// ----------------------------------------------------------------------------
// Curated "corner" operands for a format: the special values and the extreme
// magnitudes (max-normal, min-subnormal, ...) that stress the rounder's
// narrowed intermediates -- exactly the max-normal / min-subnormal corner the
// experimental divider refactor targets.
// Layout of a packed value: [ sign(1) | exponent(E) | mantissa(M) ].
// ----------------------------------------------------------------------------
static std::vector<uint64_t> corners(unsigned E, unsigned M) {
  uint64_t signbit = (uint64_t)1 << (E + M);
  uint64_t expAll  = ((uint64_t)1 << E) - 1;   // all-ones exponent field
  uint64_t mantAll = ((uint64_t)1 << M) - 1;   // all-ones mantissa field
  uint64_t bias    = ((uint64_t)1 << (E - 1)) - 1;

  auto mk = [&](uint64_t exp, uint64_t mant) -> uint64_t {
    return (exp << M) | mant;
  };

  std::vector<uint64_t> base;
  base.push_back(mk(0, 0));                 // +0
  base.push_back(mk(0, 1));                 // min positive subnormal
  base.push_back(mk(0, mantAll));           // max subnormal
  base.push_back(mk(1, 0));                 // min positive normal
  base.push_back(mk(bias, 0));              // 1.0
  base.push_back(mk(expAll - 1, mantAll));  // max normal
  base.push_back(mk(expAll, 0));            // +inf
  if (M > 0) base.push_back(mk(expAll, 1)); // sNaN-ish (nonzero mantissa)
  if (M > 0) base.push_back(mk(expAll, mantAll)); // qNaN-ish

  std::vector<uint64_t> out;
  for (uint64_t v : base) { out.push_back(v); out.push_back(v | signbit); }
  return out;
}

// A small xorshift so we don't depend on <random> ABI details.
static uint64_t xorshift(uint64_t &s) {
  s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s;
}

// ----------------------------------------------------------------------------
// Subcommands.
// ----------------------------------------------------------------------------
static int cmd_one(unsigned E, unsigned M, const std::string &op, rm mode,
                   uint64_t a, uint64_t b) {
  std::string r = run_op(E, M, op, mode, a, b);
  printf("OK %s\n", r.c_str());
  return 0;
}

// Enumerate ALL operand patterns. Binary ops iterate both operands; unary ops
// iterate only a (b column reported as 0). Emits CSV: a,b,result
static int cmd_enum(unsigned E, unsigned M, const std::string &op, rm mode) {
  unsigned W = E + M + 1;
  uint64_t N = (uint64_t)1 << W;
  if (is_unary(op)) {
    for (uint64_t a = 0; a < N; ++a) {
      std::string r = run_op(E, M, op, mode, a, 0);
      printf("%llu,0,%s\n", (unsigned long long)a, r.c_str());
    }
  } else {
    for (uint64_t a = 0; a < N; ++a)
      for (uint64_t b = 0; b < N; ++b) {
        std::string r = run_op(E, M, op, mode, a, b);
        printf("%llu,%llu,%s\n", (unsigned long long)a,
               (unsigned long long)b, r.c_str());
      }
  }
  return 0;
}

// Curated corners x corners, plus `Nrand` random operand pairs. For formats too
// wide for full enumeration. Emits the same CSV: a,b,result
static int cmd_sample(unsigned E, unsigned M, const std::string &op, rm mode,
                      uint64_t Nrand, uint64_t seed) {
  unsigned W = E + M + 1;
  uint64_t mask = (W >= 64) ? ~0ULL : (((uint64_t)1 << W) - 1);
  std::vector<uint64_t> cs = corners(E, M);

  if (is_unary(op)) {
    for (uint64_t a : cs) {
      std::string r = run_op(E, M, op, mode, a, 0);
      printf("%llu,0,%s\n", (unsigned long long)a, r.c_str());
    }
    uint64_t s = seed ? seed : 0x9e3779b97f4a7c15ULL;
    for (uint64_t k = 0; k < Nrand; ++k) {
      uint64_t a = xorshift(s) & mask;
      std::string r = run_op(E, M, op, mode, a, 0);
      printf("%llu,0,%s\n", (unsigned long long)a, r.c_str());
    }
    return 0;
  }

  for (uint64_t a : cs)
    for (uint64_t b : cs) {
      std::string r = run_op(E, M, op, mode, a, b);
      printf("%llu,%llu,%s\n", (unsigned long long)a,
             (unsigned long long)b, r.c_str());
    }
  uint64_t s = seed ? seed : 0x9e3779b97f4a7c15ULL;
  for (uint64_t k = 0; k < Nrand; ++k) {
    uint64_t a = xorshift(s) & mask;
    uint64_t b = xorshift(s) & mask;
    std::string r = run_op(E, M, op, mode, a, b);
    printf("%llu,%llu,%s\n", (unsigned long long)a,
           (unsigned long long)b, r.c_str());
  }
  return 0;
}

static void usage() {
  fprintf(stderr,
    "usage:\n"
    "  stresstest one    E M op rm a b\n"
    "  stresstest enum   E M op rm\n"
    "  stresstest sample E M op rm Nrand seed\n"
    "  ops: unpack abs neg sqrt rti add sub mul div rem min max lt\n"
    "  rm : RNE RNA RTN RTP RTZ\n");
}

int main(int argc, char **argv) {
  if (argc < 2) { usage(); return 2; }
  std::string cmd = argv[1];

  auto need = [&](int n) { if (argc < n) { usage(); exit(2); } };

  if (cmd == "one")    need(8);
  else if (cmd == "enum")   need(6);
  else if (cmd == "sample") need(8);
  else { usage(); return 2; }

  unsigned E = (unsigned)strtoul(argv[2], nullptr, 10);
  unsigned M = (unsigned)strtoul(argv[3], nullptr, 10);
  std::string op = argv[4];
  rm mode = traits::RNE();
  if (needs_rm(op) && !parse_rm(argv[5], mode)) {
    fprintf(stderr, "bad rm: %s\n", argv[5]); return 2;
  }
  // For ops that ignore the rounding mode we still accept (and ignore) argv[5].

  if (cmd == "one") {
    uint64_t a = strtoull(argv[6], nullptr, 10);
    uint64_t b = strtoull(argv[7], nullptr, 10);
    return cmd_one(E, M, op, mode, a, b);
  }
  if (cmd == "enum") {
    return cmd_enum(E, M, op, mode);
  }
  // sample
  uint64_t Nrand = strtoull(argv[6], nullptr, 10);
  uint64_t seed  = strtoull(argv[7], nullptr, 10);
  return cmd_sample(E, M, op, mode, Nrand, seed);
}
