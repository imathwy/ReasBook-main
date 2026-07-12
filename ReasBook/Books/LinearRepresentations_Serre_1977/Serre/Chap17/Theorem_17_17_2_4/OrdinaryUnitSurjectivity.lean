import Mathlib
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_4.CharacterTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectionFormulaClass
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.DecompositionUnit

/-!
# Ordinary row: unit preimage implies surjectivity

For the ordinary Grothendieck ring `R₀[k](G)`, once the ring unit `1 ⊗ [trivial]` of
`ℚ ⊗ R₀[k](G)` lies in the image of rationalized cyclic-subgroup induction, the whole induction
map is surjective.  This is Serre's "`y = 1 · y`" step (the image is an ideal containing the
unit), the ordinary analogue of the projective unit-preimage surjectivity in
`Theorem_17_17_2_4.lean`.
-/

open scoped MonoidAlgebra Representation TensorProduct

noncomputable section

universe u

namespace Representation

section OrdinaryUnit

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

private local instance instR0Monoid (H : Type u) [Group H] [Finite H] :
    AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)).toAddCommMonoid

private local instance instR0Group (H : Type u) [Group H] [Finite H] :
    AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup (finiteRepGrothendieckRelations k H)

private local instance instR0IntModule (H : Type u) [Group H] [Finite H] :
    Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

private local instance : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) := Classical.decEq _

/-- Right multiplication by a fixed Grothendieck class is an integral linear map. -/
def mul_intLinearMap (z : R₀[k](G)) : R₀[k](G) →ₗ[ℤ] R₀[k](G) where
  toFun a := a * z
  map_add' a b := add_mul a b z
  map_smul' n a := by
    rw [← Int.cast_smul_eq_zsmul (R := R₀[k](G)) (n := n) (b := a)]
    rw [smul_mul_assoc]
    rw [Int.cast_smul_eq_zsmul (R := R₀[k](G)) (n := n) (b := a * z)]
    simp

/-- The rationalized right-multiplication acts on `q ⊗ [trivial]` as the identity (since
`[trivial] = 1`). -/
theorem baseChange_mul_unit_tmul (q : ℚ) (z : R₀[k](G)) :
    ((mul_intLinearMap k G z).baseChange ℚ)
        (q ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) =
      q ⊗ₜ[ℤ] z := by
  rw [LinearMap.baseChange_tmul]
  change q ⊗ₜ[ℤ] (([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) * z) = q ⊗ₜ[ℤ] z
  rw [finiteRepGrothendieckClass_trivial_eq_one (G := G) k, one_mul]

/-- The projection formula after rationalizing the ordinary Grothendieck ring. -/
theorem rationalized_mul_projection_formula
    (H : _root_.Subgroup.cyclicSubgroups G)
    (a : ℚ ⊗[ℤ] R₀[k](H.1)) (z : R₀[k](G)) :
    ((mul_intLinearMap k G z).baseChange ℚ)
        ((Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1) a) =
      (Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1)
        (((mul_intLinearMap k H.1
            (Representation.Subgroup.finiteRepGrothendieckGroupRestriction
              k H.1 z)).baseChange ℚ) a) := by
  refine TensorProduct.induction_on a ?_ ?_ ?_
  · simp [Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction]
  · intro q x
    simp only [Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
      LinearMap.baseChange_tmul]
    change q ⊗ₜ[ℤ] ((Representation.Subgroup.finiteRepGrothendieckGroupInduction k H.1 x) * z) =
      q ⊗ₜ[ℤ] (Representation.Subgroup.finiteRepGrothendieckGroupInduction k H.1
        (x * Representation.Subgroup.finiteRepGrothendieckGroupRestriction k H.1 z))
    rw [finiteRepGrothendieckGroupInduction_mul H.1 x z]
  · intro x y hx hy
    simpa [map_add] using congrArg₂ HAdd.hAdd hx hy

/-- The direct-sum version of the rationalized projection formula. -/
theorem cyclic_mul_lsum_mapRange_eq_mul_lsum
    (ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1))
    (z : R₀[k](G)) :
    cyclic_rationalized_induction_lsum k G
      (DFinsupp.mapRange.linearMap
        (fun H : _root_.Subgroup.cyclicSubgroups G =>
          ((mul_intLinearMap k H.1
            (Representation.Subgroup.finiteRepGrothendieckGroupRestriction
              k H.1 z)).baseChange ℚ)) ξ) =
      ((mul_intLinearMap k G z).baseChange ℚ)
        (cyclic_rationalized_induction_lsum k G ξ) := by
  let f : ∀ H : _root_.Subgroup.cyclicSubgroups G,
      (ℚ ⊗[ℤ] R₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] R₀[k](H.1)) :=
    fun H =>
      ((mul_intLinearMap k H.1
        (Representation.Subgroup.finiteRepGrothendieckGroupRestriction
          k H.1 z)).baseChange ℚ)
  let hP : ∀ H : _root_.Subgroup.cyclicSubgroups G,
      (ℚ ⊗[ℤ] R₀[k](H.1)) →ₗ[ℚ] (ℚ ⊗[ℤ] R₀[k](G)) :=
    fun H =>
      Representation.Subgroup.finiteRepGrothendieckGroupRationalizedInduction (k := k) (G := G) H.1
  have hmaps :
      (DFinsupp.lsum ℚ fun H => (hP H).comp (f H)) =
        ((mul_intLinearMap k G z).baseChange ℚ).comp
          (cyclic_rationalized_induction_lsum k G) := by
    apply DFinsupp.lhom_ext
    intro H x
    simpa [f, hP, LinearMap.comp_apply] using
      (rationalized_mul_projection_formula k G H x z).symm
  calc
    cyclic_rationalized_induction_lsum k G
        (DFinsupp.mapRange.linearMap f ξ)
        = (DFinsupp.lsum ℚ fun H => (hP H).comp (f H)) ξ := by
            simpa [f, hP] using
              (DFinsupp.sum_mapRange_index.linearMap (f := f) (h := hP) (l := ξ))
    _ = ((mul_intLinearMap k G z).baseChange ℚ)
          (cyclic_rationalized_induction_lsum k G ξ) := by
            simpa [LinearMap.comp_apply] using congrArg (fun e => e ξ) hmaps

/-- **Ordinary unit preimage implies surjectivity.** If `1 ⊗ [trivial]` is hit by rationalized
cyclic induction, then rationalized cyclic induction is surjective. -/
theorem cyclic_ordinary_rationalized_induction_surjective_of_unit_preimage
    (ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[k](H.1))
    (hξ : cyclic_rationalized_induction_lsum k G ξ =
        (1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G))) :
    Function.Surjective (cyclic_rationalized_induction_lsum k G) := by
  intro w
  refine TensorProduct.induction_on w ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro q z
    refine ⟨DFinsupp.mapRange.linearMap
      (fun H : _root_.Subgroup.cyclicSubgroups G =>
        ((mul_intLinearMap k H.1
          (Representation.Subgroup.finiteRepGrothendieckGroupRestriction
            k H.1 z)).baseChange ℚ)) ((q : ℚ) • ξ), ?_⟩
    rw [cyclic_mul_lsum_mapRange_eq_mul_lsum, map_smul, hξ]
    rw [TensorProduct.smul_tmul']
    rw [baseChange_mul_unit_tmul]
    simp
  · intro x y hx hy
    rcases hx with ⟨vx, hvx⟩
    rcases hy with ⟨vy, hvy⟩
    exact ⟨vx + vy, by simp [map_add, hvx, hvy]⟩

end OrdinaryUnit

end Representation
