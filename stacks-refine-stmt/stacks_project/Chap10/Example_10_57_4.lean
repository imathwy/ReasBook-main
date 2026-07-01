import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Polynomial

variable (R : Type u) [CommRing R]

/-- The standard `ℕ`-grading on `R[X]`, transported from the canonical grading on the additive
monoid algebra model `R[ℕ]` via `Polynomial.toFinsuppIsoLinear`. -/
abbrev standardGrading (n : ℕ) : Submodule R R[X] :=
  Submodule.map (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap (AddMonoidAlgebra.grade R n)

instance instSetLikeGradedMonoidStandardGrading : SetLike.GradedMonoid (standardGrading R) where
  one_mem := by
    refine ⟨AddMonoidAlgebra.single 0 (1 : R), AddMonoidAlgebra.single_mem_grade 0 1, ?_⟩
    ext n
    change
      ((Polynomial.toFinsuppIso R).symm (AddMonoidAlgebra.single 0 (1 : R))).coeff n =
        (1 : R[X]).coeff n
    rw [Polynomial.toFinsuppIso_symm_apply, Polynomial.coeff_ofFinsupp, AddMonoidAlgebra.single_apply]
    simp [coeff_one, eq_comm]
  mul_mem {i j} a b ha hb := by
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    refine ⟨a' * b', SetLike.mul_mem_graded ha' hb', ?_⟩
    ext n
    exact congrArg (fun p : R[X] ↦ p.coeff n) ((Polynomial.toFinsuppIso R).symm.map_mul a' b')

instance instGradedAlgebraStandardGrading : GradedAlgebra (standardGrading R) :=
  DirectSum.IsInternal.gradedAlgebra <| by
    sorry

/-- The degree-zero piece of the standard grading is canonically `R`, via constant polynomials. -/
private theorem eq_single_zero_of_mem_grade_zero {x : AddMonoidAlgebra R ℕ}
    (hx : x ∈ AddMonoidAlgebra.grade R 0) :
    x = AddMonoidAlgebra.single 0 (x 0) := by
  ext n
  by_cases hn : n = 0
  · subst hn
    simp
  · have hx' := (AddMonoidAlgebra.mem_grade_iff R 0 x).mp hx
    have hnot : n ∉ x.support := by
      intro hn'
      exact hn (by simpa using hx' hn')
    simp [hn, Finsupp.notMem_support_iff.mp hnot]

private noncomputable def addMonoidAlgebraGradeZeroRingEquiv :
    ↥(AddMonoidAlgebra.grade R 0) ≃+* R where
  toFun x := x.1 0
  invFun r := ⟨AddMonoidAlgebra.single 0 r, AddMonoidAlgebra.single_mem_grade 0 r⟩
  left_inv x := by
    apply Subtype.ext
    exact (eq_single_zero_of_mem_grade_zero R x.2).symm
  right_inv r := by
    simp
  map_mul' x y := by
    change (x.1 * y.1) 0 = x.1 0 * y.1 0
    rw [eq_single_zero_of_mem_grade_zero R x.2, eq_single_zero_of_mem_grade_zero R y.2]
    simp
  map_add' x y := by
    simp

private noncomputable def standardGradingDegreeZeroToAddMonoidAlgebra :
    ↥(standardGrading R 0) ≃+* ↥(AddMonoidAlgebra.grade R 0) where
  toFun p := by
    refine ⟨Polynomial.toFinsuppIso R p.1, ?_⟩
    rcases p.2 with ⟨q, hq, hq'⟩
    have h : q = Polynomial.toFinsuppIso R p.1 := by
      simpa using congrArg (Polynomial.toFinsuppIso R) hq'
    simpa [h] using hq
  invFun q := ⟨(Polynomial.toFinsuppIso R).symm q.1, ⟨q.1, q.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    rfl
  map_add' p q := by
    rfl

private noncomputable def standardGradingDegreeZeroRingEquiv : ↥(standardGrading R 0) ≃+* R :=
  (standardGradingDegreeZeroToAddMonoidAlgebra R).trans (addMonoidAlgebraGradeZeroRingEquiv R)

end Polynomial

section

variable (R : Type u) [CommRing R]

local notation "𝒮" => Polynomial.standardGrading R

private noncomputable def standardGradingDegreeZeroSpecIso :
    Spec (.of ↥(𝒮 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso (Polynomial.standardGradingDegreeZeroRingEquiv R).toCommRingCatIso.op).symm

/-- Example 10.57.4 (1), map form: if `S = R[X]` with `deg(X) = 1`, then the natural map
`Proj(S) → Spec(R)` is the degree-zero structure morphism followed by the canonical identification
`Spec(S₀) ≅ Spec(R)`. -/
noncomputable def polynomial_standardGrading_toSpec :
    Proj 𝒮 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom

private instance : IsIso (Proj.toSpecZero 𝒮) := by
  sorry

instance : IsIso (polynomial_standardGrading_toSpec R) := by
  change IsIso (Proj.toSpecZero 𝒮 ≫ (standardGradingDegreeZeroSpecIso R).hom)
  infer_instance

/-- Example 10.57.4 (1), canonical form: `Proj(R[X])` with `deg(X) = 1` is canonically isomorphic
to `Spec(R)`. -/
noncomputable def polynomial_standardGrading_isoSpec :
    Proj 𝒮 ≅ Spec (.of R) :=
  asIso (polynomial_standardGrading_toSpec R)

/-- Example 10.57.4 (2): if `p` is a point of `Proj(R[X])` for the standard grading, equivalently a
relevant homogeneous prime ideal of `R[X]`, then `p` is the extension of its contraction to `R`.
Equivalently, for `p₀ = p ∩ R`, one has `p = p₀R[X]`. -/
-- Proof sketch: under `polynomial_standardGrading_isoSpec R`, the point `p` corresponds to its
-- contraction along `C : R →+* R[X]`, so its underlying ideal is the extension of that contracted
-- prime.
theorem polynomial_standardGrading_point_asIdeal_eq_map_comap_C
    (p : ProjectiveSpectrum 𝒮) :
    p.asHomogeneousIdeal.toIdeal =
      Ideal.map Polynomial.C (Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal) := by
  sorry

end
