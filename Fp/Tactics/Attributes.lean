import Lean

register_simp_attr bv_float_normalize

/-!
# FP pack/unpack normalization simp sets

The following simp attributes drive the staged rewriting pipeline that eliminates
the redundant `pack`/`unpack` round-trips between chained floating-point
operations. They are applied *in order*, ahead of `bv_decide`, so that the
`unpack (pack (op-output))` pattern can be cancelled *before* `pack`/`unpack` are
lowered to `BitVec` by `bv_normalize`.
-/

/-- Stage 0: constant-fold FP operations whose arguments are all literals. -/
register_simp_attr fp_normalize_consts

/-- Stage 1: expand each surface `PackedFloat.*` operation into its
`unpack`/`EUnpackedFloat`-op/`pack` form, leaving `pack`/`unpack` opaque. -/
register_simp_attr fp_expand_pack_unpack

/-- Stage 3: cancel the intermediate round-trips
`(EUnpackedFloat.op …).pack.unpack = EUnpackedFloat.op …`. -/
register_simp_attr fp_normalize_pack_unpack_eunpacked
