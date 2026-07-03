import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: LinearRepresentations_Serre_1977's presentation of the finite dihedral group by the generators `r` and `s`
  with the relations `r^n = 1`, `s^2 = 1`, and `srs = r⁻¹`;
- `core/canonical`: mathlib's owner `DihedralGroup n`, together with its canonical constructors
  `DihedralGroup.r`, `DihedralGroup.sr` and the upstream formulas for multiplication, inversion,
  normal form, and cardinality;
- `bridge/view`: the single source-facing conjugation theorem below, which packages the primitive
  multiplication rules into the textbook relation `srs = r⁻¹`.

Primitive/derived split:
- primitive data: none is re-owned in this file; all group structure and canonical API come
  directly from `DihedralGroup n`;
- derived API: only the source-facing conjugation relation is stated locally, since mathlib already
  owns the underlying multiplication and inverse formulas. -/

/- Definition 5-5.3-1: for `n ≠ 0`, the dihedral group of the regular `n`-gon is the canonical
mathlib group `DihedralGroup n`, whose elements are the rotations `DihedralGroup.r i` and the
reflections `DihedralGroup.sr i` indexed by `i : ZMod n`. -/
recall DihedralGroup

/- The canonical rotation generator `DihedralGroup.r 1` satisfies the textbook relation
`r ^ n = 1`. -/
recall DihedralGroup.r_one_pow_n

/- Each canonical reflection `DihedralGroup.sr i` has square `1`; in particular the basic
reflection `DihedralGroup.sr 0` satisfies `s ^ 2 = 1`. -/
recall DihedralGroup.sr_mul_self

/- The inverse of the rotation `DihedralGroup.r j` is the rotation `DihedralGroup.r (-j)`. -/
recall DihedralGroup.inv_r

namespace DihedralGroup

-- Proof sketch: combine the canonical multiplication formulas `sr_mul_r` and `sr_mul_sr`, then
-- rewrite the resulting rotation `r (-j)` using the canonical inverse formula `inv_r`.
/-- Conjugating a rotation by a reflection gives the inverse rotation; the textbook relation
`sr 0 * r 1 * sr 0 = (r 1)⁻¹` is the specialization `i = 0`, `j = 1`. -/
theorem sr_mul_r_mul_sr_eq_inv_r (i j : ZMod n) :
    sr i * r j * sr i = (r j)⁻¹ := by
  simp

end DihedralGroup

/- The canonical equivalence `DihedralGroup.equivSum` expresses the unique normal form in which
every element is either a rotation `r^k` or a reflection `sr^k`. -/
recall DihedralGroup.equivSum

/- For `n ≠ 0`, the finite dihedral group has order `2n`. -/
recall DihedralGroup.card
