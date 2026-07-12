import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_5.SubgroupInduction
import LinearRepresentations_Serre_1977.Chap17.Corollary_17_17_2_2.ElementarySubgroupInduction
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectionFormula
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.ProjectiveSubgroupRestriction

/-!
# Projective projection (push–pull) formula

The projective analog of `finiteRepGrothendieckGroupInduction_mul`: on the `R₀[k](G)`-module
`P₀[k](G)`, for `a ∈ R₀[k](H)` and `p ∈ P₀[k](G)`,
`Ind_H^G(a) • p = Ind_H^G (a • Res_H^G p)`.

The key geometric input is the **projective Frobenius reciprocity** isomorphism
`(Ind_H^G V) ⊗ₚ P ≅ Ind_H^G (V ⊗ₚ Res_H^G P)` of finite projective owners, obtained by lifting the
representation-level `projRepIso` through the equivalence `Rep k G ≌ ModuleCat k[G]`.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped Representation MonoidAlgebra TensorProduct

namespace Representation

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]

/-- A `Rep`-level iso of the underlying `.toRep`s of two finite projective owners yields an iso of
the owners (public counterpart of the private helper in `Exercise_15_15_1_2`). -/
theorem finiteProjective_nonempty_iso_of_toRep_iso'
    {P Q : FiniteProjectiveGroupAlgebraModule k G}
    (hPQ : Nonempty (P.toRep ≅ Q.toRep)) : Nonempty (P ≅ Q) := by
  rcases hPQ with ⟨e⟩
  let eMod := Rep.toModuleMonoidAlgebra.mapIso e
  let eLin : P.V ≃ₗ[k[G]] Q.V :=
    (Rep.counitIso P.V).toLinearEquiv.symm.trans
      (eMod.toLinearEquiv.trans (Rep.counitIso Q.V).toLinearEquiv)
  exact
    (Representation.finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) P Q).2 ⟨eLin⟩

/-- **Projective Frobenius reciprocity** for finite projective owners:
`(Ind_H^G V) ⊗ₚ P ≅ Ind_H^G (V ⊗ₚ Res_H^G P)`.  Lifts the representation-level `projRepIso` through
`Rep k G ≌ ModuleCat k[G]` (using that `Rep.of Z.ρ = Z`, the round-trips are the equivalence unit
isos on the tensor / restriction / induction packagings). -/
theorem projProjFrob_nonempty_iso {H : Subgroup G} (V : FDRep k H)
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    Nonempty (((FDRep.subgroupInduction V) ⊗ₚ P) ≅
      FiniteProjectiveGroupAlgebraModule.subgroupInduction
        (V ⊗ₚ FiniteProjectiveGroupAlgebraModule.subgroupRestriction P)) := by
  apply finiteProjective_nonempty_iso_of_toRep_iso' (k := k) (G := G)
  let ρ₁ : Rep k G := Rep.of <| Representation.tprod (FDRep.ρ (FDRep.subgroupInduction V)) P.toRep.ρ
  have e₁ : (((FDRep.subgroupInduction V) ⊗ₚ P).toRep) ≅ ρ₁ := by
    simpa [ρ₁, FiniteProjectiveGroupAlgebraModule.tprod,
      FiniteProjectiveGroupAlgebraModule.toRep] using (Rep.unitIso ρ₁).symm
  have e₂ : ρ₁ ≅ Rep.ind H.subtype
      (MonoidalCategory.tensorObj (Rep.of V.ρ) (Rep.res H.subtype (Rep.of P.toRep.ρ))) := by
    simpa [ρ₁] using projRepIso H (Rep.of V.ρ) (Rep.of P.toRep.ρ)
  have eRes : (Rep.res H.subtype (Rep.of P.toRep.ρ)) ≅
      (FiniteProjectiveGroupAlgebraModule.subgroupRestriction P).toRep := by
    simpa [FiniteProjectiveGroupAlgebraModule.subgroupRestriction,
      FiniteProjectiveGroupAlgebraModule.toRep] using (Rep.unitIso (Rep.res H.subtype P.toRep))
  have eConn : MonoidalCategory.tensorObj (Rep.of V.ρ) (Rep.res H.subtype (Rep.of P.toRep.ρ)) ≅
      (V ⊗ₚ FiniteProjectiveGroupAlgebraModule.subgroupRestriction P).toRep := by
    refine (MonoidalCategory.whiskerLeftIso (Rep.of V.ρ) eRes) ≪≫ ?_
    simpa [FiniteProjectiveGroupAlgebraModule.tprod, FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso (Rep.of (Representation.tprod (FDRep.ρ V)
        (FiniteProjectiveGroupAlgebraModule.subgroupRestriction P).toRep.ρ)))
  have e₄ : Rep.ind H.subtype (V ⊗ₚ FiniteProjectiveGroupAlgebraModule.subgroupRestriction P).toRep ≅
      (FiniteProjectiveGroupAlgebraModule.subgroupInduction
        (V ⊗ₚ FiniteProjectiveGroupAlgebraModule.subgroupRestriction P)).toRep := by
    simpa [FiniteProjectiveGroupAlgebraModule.subgroupInduction,
      FiniteProjectiveGroupAlgebraModule.toRep] using
      (Rep.unitIso (Rep.ind H.subtype
        (V ⊗ₚ FiniteProjectiveGroupAlgebraModule.subgroupRestriction P).toRep))
  exact ⟨e₁ ≪≫ e₂ ≪≫ (Functor.mapIso (Rep.indFunctor k H.subtype) eConn) ≪≫ e₄⟩

/-- The projective projection formula on generator classes `a = [V]₀`, `p = [P]ₚ₀`. -/
theorem projFormula_proj_gen (H : Subgroup G) (V : FDRep k H)
    (P : FiniteProjectiveGroupAlgebraModule k G) :
    (Subgroup.finiteRepGrothendieckGroupInduction k H [V]₀) • [P]ₚ₀ =
      Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction k H
        ([V]₀ • Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction k H [P]ₚ₀) := by
  rw [Subgroup.finiteRepGrothendieckGroupInduction_apply_class,
    finiteProjectiveGroupAlgebraGrothendieckClass_smul,
    Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction_apply_class,
    finiteProjectiveGroupAlgebraGrothendieckClass_smul,
    Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction_apply_class]
  exact finiteProjectiveGroupAlgebraGrothendieckClass_eq_of_nonempty_iso
    (projProjFrob_nonempty_iso V P)

/-- **The projective projection (push–pull) formula** on `P₀[k]` as an `R₀[k]`-module: for
`a ∈ R₀[k](H)` and `p ∈ P₀[k](G)`, `Ind_H^G(a) • p = Ind_H^G (a • Res_H^G p)`. -/
theorem finiteProjectiveGroupAlgebraGrothendieckGroupInduction_smul (H : Subgroup G)
    (a : R₀[k](H)) (p : P₀[k](G)) :
    (Subgroup.finiteRepGrothendieckGroupInduction k H a) • p =
      Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction k H
        (a • Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRestriction k H p) := by
  refine QuotientAddGroup.induction_on a ?_
  intro va
  refine QuotientAddGroup.induction_on p ?_
  intro vp
  refine FreeAbelianGroup.induction_on va ?_ ?_ ?_ ?_
  · simp
  · intro V
    refine FreeAbelianGroup.induction_on vp ?_ ?_ ?_ ?_
    · simp
    · intro P; exact projFormula_proj_gen H V P
    · intro P hP; simp [map_neg, smul_neg, hP]
    · intro P₁ P₂ hP₁ hP₂; simp [map_add, smul_add, hP₁, hP₂]
  · intro va hva; simp [map_neg, neg_smul, hva]
  · intro va₁ va₂ hva₁ hva₂; simp [map_add, add_smul, hva₁, hva₂]

end Representation
