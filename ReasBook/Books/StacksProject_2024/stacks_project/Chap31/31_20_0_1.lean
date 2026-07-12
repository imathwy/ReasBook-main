import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

private lemma ideal_smul_top_eq_self_submodule (I : Ideal R) :
    ((I • (⊤ : Submodule R R)) : Submodule R R) = (I : Submodule R R) := by
  ext x
  constructor
  · intro hx
    rw [Ideal.smul_top_eq_map] at hx
    simpa using hx
  · intro hx
    rw [Ideal.smul_top_eq_map]
    simpa using hx

-- Semantic recall: the `lean_leansearch` endpoint rate-limited on this call, so the owner/API
-- choice was verified against mathlib's regular-sequence declarations via `Ideal.ofList`,
-- `RingTheory.Sequence.IsWeaklyRegular.regular_mod_prev`, and the standard scalar-action map
-- `LinearMap.lsmul`.

/-- 31.20.0.1: the element `rs[i]` acts on the quotient by the previous generators via scalar
multiplication. For the structure sheaf over itself, this is the source map
`\mathcal O_X / (f_1, \ldots, f_{i-1}) \to \mathcal O_X / (f_1, \ldots, f_{i-1})`
given by multiplication by `f_i`. -/
abbrev quotientMulByPrev (rs : List R) (i : Fin rs.length) :
    (R ⧸ Ideal.ofList (List.take i rs)) →ₗ[R]
      (R ⧸ Ideal.ofList (List.take i rs)) :=
  LinearMap.lsmul R _ rs[i]

/-- The quotient-multiplication map acts by scalar multiplication with the `i`-th element. -/
@[simp] theorem quotientMulByPrev_apply
    (rs : List R) (i : Fin rs.length) (x : R ⧸ Ideal.ofList (List.take i rs)) :
    quotientMulByPrev rs i x = rs[i] • x :=
  rfl

/-- For a weakly regular sequence, the quotient-multiplication map by the next generator is
scalar-regular on the corresponding successive quotient. -/
theorem IsWeaklyRegular.isSMulRegular_quotientMulByPrev
    {rs : List R} (h : IsWeaklyRegular R rs) (i : Fin rs.length) :
    IsSMulRegular
      (R ⧸ Ideal.ofList (List.take i rs))
      rs[i] := by
  let e :
      (R ⧸ (Ideal.ofList (List.take i rs) • (⊤ : Submodule R R))) ≃ₗ[R]
        (R ⧸ Ideal.ofList (List.take i rs)) :=
    Submodule.quotEquivOfEq _ _ <|
      ideal_smul_top_eq_self_submodule (Ideal.ofList (List.take i rs))
  exact (e.isSMulRegular_congr rs[i]).mp <| h.regular_mod_prev i i.2

end RingTheory.Sequence
