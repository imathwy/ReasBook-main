import Mathlib
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectionFormula
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.SubgroupRestriction
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2.FiniteRepTensorRing

noncomputable section

universe u

open CategoryTheory
open scoped Representation TensorProduct

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable (S : Subgroup G) (V : FDRep k S) (W : FDRep k G)

/-- Projection-formula isomorphism at the level of finite-dimensional representations:
`Ind_S^G(V) ⊗ W ≅ Ind_S^G(V ⊗ Res_S W)`.  Obtained by transporting the representation-level
isomorphism `projRepIso` through the fully faithful forgetful functor `FDRep k G ⥤ Rep k G`. -/
noncomputable def projFDRepIso :
    MonoidalCategory.tensorObj (FDRep.subgroupInduction V) W
      ≅ FDRep.subgroupInduction (MonoidalCategory.tensorObj V (FDRep.subgroupRestriction W)) :=
  (forget₂ (FDRep k G) (Rep k G)).preimageIso (projRepIso S (Rep.of V.ρ) (Rep.of W.ρ))

/-- Projection-formula class equality in `R₀[k](G)`:
`[Ind_S^G(V) ⊗ W] = [Ind_S^G(V ⊗ Res_S W)]`. -/
lemma projFormula_class :
    [MonoidalCategory.tensorObj (FDRep.subgroupInduction V) W]₀
      = [FDRep.subgroupInduction (MonoidalCategory.tensorObj V (FDRep.subgroupRestriction W))]₀ :=
  finiteRepGrothendieckClass_eq_of_iso (projFDRepIso S V W)

end

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/-- The projection formula on generator classes `a = [V]`, `y = [W]`. -/
private lemma projFormula_gen (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    (Representation.Subgroup.finiteRepGrothendieckGroupInduction k H [V]₀) * [W]₀
      = Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
          ([V]₀ * Representation.Subgroup.finiteRepGrothendieckGroupRestriction k H [W]₀) := by
  rw [Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class,
    finiteRepGrothendieckClass_mul,
    Representation.Subgroup.finiteRepGrothendieckGroupRestriction_apply_class,
    finiteRepGrothendieckClass_mul,
    Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class]
  exact projFormula_class H V W

-- Proof sketch: Serre's projection (push–pull) formula `Ind_H(a)·y = Ind_H(a·Res_H y)` on the
-- Grothendieck ring `R_k(G)`.  Both sides are biadditive in `a` and `y`, so it suffices to check
-- the generator case `a = [V]`, `y = [W]`, where it reduces to the projection-formula class
-- equality `projFormula_class`.
/-- The projection formula on `R₀[k]`: for `a ∈ R_k(H)` and `y ∈ R_k(G)`,
`Ind_H^G(a) · y = Ind_H^G(a · Res_H^G y)`. -/
theorem finiteRepGrothendieckGroupInduction_mul (H : Subgroup G)
    (a : R₀[k](H)) (y : R₀[k](G)) :
    (Representation.Subgroup.finiteRepGrothendieckGroupInduction k H a) * y =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (a * Representation.Subgroup.finiteRepGrothendieckGroupRestriction k H y) := by
  refine QuotientAddGroup.induction_on a ?_
  intro va
  refine QuotientAddGroup.induction_on y ?_
  intro vy
  refine FreeAbelianGroup.induction_on va ?_ ?_ ?_ ?_
  · simp
  · intro V
    refine FreeAbelianGroup.induction_on vy ?_ ?_ ?_ ?_
    · simp
    · intro W
      exact projFormula_gen H V W
    · intro W hW
      simp [map_neg, mul_neg, hW]
    · intro W₁ W₂ hW₁ hW₂
      simp [map_add, mul_add, hW₁, hW₂]
  · intro va hva
    simp [map_neg, neg_mul, hva]
  · intro va₁ va₂ hva₁ hva₂
    simp [map_add, add_mul, hva₁, hva₂]

end

end Representation
