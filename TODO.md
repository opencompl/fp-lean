# TODO / Known Issues

## Double-namespace-prefix in `Fp/Theorems/PackedFloat/Ordering.lean`

`Ordering.lean` opens `namespace PackedFloat` (at file scope, **not** nested under
`namespace Fp` like the rest of the codebase) and *also* prefixes each theorem name
with `PackedFloat.`. The result is doubly-qualified declaration names such as:

- `PackedFloat.PackedFloat.one_le_ex_of_isNorm`
- `PackedFloat.PackedFloat.ex_le_ex_of_isNonzeroSubnorm_of_not_isNorm`
- (every theorem in the file)

This is confirmed in the build artifact
`.lake/build/lib/lean/Fp/Theorems/PackedFloat/Ordering.ilean`
(`{"decls":{"PackedFloat.PackedFloat.ex_le_ex_of_isNonzeroSu...`).

**Impact:** call sites that expect the single-prefixed `PackedFloat.<name>` fail with
"unknown constant". E.g. `PackedFloat.one_le_ex_of_isNorm` does not resolve; the real
name is `PackedFloat.PackedFloat.one_le_ex_of_isNorm`. This is surprising and
error-prone (other files are `Fp.PackedFloat.<name>`).

**Fix options:**
1. Wrap `Ordering.lean` in `namespace Fp` (like sibling files) and drop the explicit
   `PackedFloat.` prefix on declarations, so names become `Fp.PackedFloat.<name>`.
   Requires updating intra-file references and any external `PackedFloat.PackedFloat.*`
   call sites.
2. Or: keep `namespace PackedFloat` but drop the per-decl `PackedFloat.` prefix so names
   become `PackedFloat.<name>` (single). Still inconsistent with `Fp.*` convention but
   less confusing.

Option 1 is preferred for consistency. Until fixed, prefer building the small needed
fact locally (e.g. derive `1 ≤ ex.toNat` from `isNorm` ⇒ `ex ≠ 0` directly) rather than
reaching into `Ordering.lean`'s doubly-prefixed API.
