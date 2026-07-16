import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra
open scoped Representation
open scoped TensorProduct

namespace Representation

section SubgroupRestriction

section
/-!
Restriction homomorphism `Res_H^G : R_k(G) → R_k(H)` on Grothendieck groups of finite-dimensional
`k`-representations, mirroring the subgroup-induction construction in
`Serre.Chap16.Theorem_16_16_1_5.SubgroupInduction`.  Restriction along a subgroup inclusion is
*exact* (it is simultaneously a left and a right adjoint, by
`Rep.indResAdjunction` and `Rep.resCoindAdjunction`) and does not change the
underlying `k`-vector space, so it descends to the Grothendieck group.

This is the `Res` half of the projection formula `Ind_H(a) * y = Ind_H(a * Res_H y)` used in the
proof of Serre's Theorem 39 (Theorem 17-17.2-1).
-/

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

namespace FDRep

/-- Restricting a finite-dimensional `k`-representation of `G` to a subgroup `H ≤ G` stays
finite-dimensional: the underlying `k`-vector space is unchanged. -/
theorem subgroupRestriction_finite {H : Subgroup G} (V : FDRep k G) :
    Module.Finite k (Rep.res H.subtype (Rep.of V.ρ)) := by
  -- `Rep.res` keeps the same carrier, so finiteness is inherited from `V`.
  change Module.Finite k V.V
  infer_instance

/-- The finite-dimensional `k[H]`-representation obtained by restricting a finite-dimensional
`k[G]`-representation along `H ≤ G`. -/
abbrev subgroupRestriction {H : Subgroup G} (V : FDRep k G) : FDRep k H :=
  let ρ := Rep.res H.subtype (Rep.of V.ρ)
  let _ : Module.Finite k ρ := subgroupRestriction_finite V
  FDRep.of ρ.ρ

end FDRep

/-- Helper: the restricted morphism on bundled finite-dimensional representations is obtained by
transporting `(Rep.resFunctor H.subtype).map` back through `FDRep`. -/
private abbrev subgroupRestriction_map {H : Subgroup G} {V W : FDRep k G} (f : V ⟶ W) :
    FDRep.subgroupRestriction (k := k) (G := G) (H := H) V ⟶
      FDRep.subgroupRestriction (k := k) (G := G) (H := H) W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    ((Rep.resFunctor H.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f))

/-- Helper: forgetting a restricted `FDRep` morphism recovers the underlying `Rep.resFunctor`
morphism. -/
private theorem subgroupRestriction_map_forget {H : Subgroup G} {V W : FDRep k G} (f : V ⟶ W) :
    (forget₂ (FDRep k H) (Rep k H)).map (subgroupRestriction_map (k := k) (G := G) (H := H) f) =
      (Rep.resFunctor H.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  change (FDRep.forget₂HomLinearEquiv
      (FDRep.subgroupRestriction (H := H) V) (FDRep.subgroupRestriction (H := H) W)).symm
    ((FDRep.forget₂HomLinearEquiv
      (FDRep.subgroupRestriction (H := H) V) (FDRep.subgroupRestriction (H := H) W))
      ((Rep.resFunctor H.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f))) =
    (Rep.resFunctor H.subtype).map ((forget₂ (FDRep k G) (Rep k G)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper: a short complex of `FDRep k G` restricts termwise to a short complex of `FDRep k H`. -/
private abbrev subgroupRestriction_shortComplex {H : Subgroup G}
    (S : ShortComplex (FDRep k G)) : ShortComplex (FDRep k H) :=
  ShortComplex.mk
    (subgroupRestriction_map (k := k) (G := G) (H := H) S.f)
    (subgroupRestriction_map (k := k) (G := G) (H := H) S.g)
    (by
      -- After forgetting to `Rep`, this is the image of `S` under restriction.
      apply (forget₂ (FDRep k H) (Rep k H)).map_injective
      rw [Functor.map_comp]
      rw [subgroupRestriction_map_forget (k := k) (G := G) (H := H) S.f]
      rw [subgroupRestriction_map_forget (k := k) (G := G) (H := H) S.g]
      simpa using
        (((S.map (forget₂ (FDRep k G) (Rep k G))).map
          (Rep.resFunctor (k := k) H.subtype)).zero))

/-- Helper: restriction along `H ≤ G` preserves short exact sequences of finite-dimensional
representations. -/
private theorem subgroupRestriction_shortExact {H : Subgroup G}
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) :
    (subgroupRestriction_shortComplex (k := k) (G := G) (H := H) S).ShortExact := by
  -- Check exactness after forgetting to `Rep`, then reflect it back to `FDRep`.
  have hRep :
      (((subgroupRestriction_shortComplex (k := k) (G := G) (H := H) S).map
        (forget₂ (FDRep k H) (Rep k H)))).ShortExact := by
    simpa [subgroupRestriction_shortComplex, subgroupRestriction_map_forget] using
      (hS.map_of_exact (forget₂ (FDRep k G) (Rep k G))).map_of_exact
        (Rep.resFunctor (k := k) H.subtype)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((subgroupRestriction_shortComplex (k := k) (G := G) (H := H) S).exact_map_iff_of_faithful
        (forget₂ (FDRep k H) (Rep k H))).1 hRep.exact
  · exact (forget₂ (FDRep k H) (Rep k H)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep k H) (Rep k H)).epi_of_epi_map hRep.epi_g

/-- The additive lift on the free abelian group of finite-dimensional `k[G]`-representations
sending `[V]` to the restricted class `[Res_H^G V]`. -/
private abbrev finiteRepGrothendieckGroupRestrictionLift (H : Subgroup G) :
    FreeAbelianGroup (FDRep k G) →+ R₀[k](H) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.subgroupRestriction (H := H) V]₀

/-- The defining relations of `R_k(G)` map to zero under subgroup restriction on the free abelian
group of finite-dimensional representations. -/
private theorem finiteRepGrothendieckRelations_le_restrictionLift_ker (H : Subgroup G) :
    finiteRepGrothendieckRelations k G ≤
      (finiteRepGrothendieckGroupRestrictionLift (k := k) (G := G) H).ker := by
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [FDRep.subgroupRestriction (H := H) S.X₂]₀ - [FDRep.subgroupRestriction (H := H) S.X₁]₀ -
      [FDRep.subgroupRestriction (H := H) S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := H)
      (subgroupRestriction_shortComplex (k := k) (G := G) (H := H) S)
      (subgroupRestriction_shortExact (k := k) (G := G) (H := H) S hS)
  calc
    [FDRep.subgroupRestriction (H := H) S.X₂]₀ - [FDRep.subgroupRestriction (H := H) S.X₁]₀ =
        ([FDRep.subgroupRestriction (H := H) S.X₁]₀ +
            [FDRep.subgroupRestriction (H := H) S.X₃]₀) -
          [FDRep.subgroupRestriction (H := H) S.X₁]₀ := by
            rw [hrelation]
    _ = [FDRep.subgroupRestriction (H := H) S.X₃]₀ := by
          abel

namespace Subgroup

/-- The restriction homomorphism `Res_H^G : R_k(G) → R_k(H)` on Grothendieck groups of
finite-dimensional `k`-representations. -/
def finiteRepGrothendieckGroupRestriction (k : Type u) [Field k] (H : Subgroup G) :
    R₀[k](G) →+ R₀[k](H) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (finiteRepGrothendieckGroupRestrictionLift (k := k) (G := G) H)
    (finiteRepGrothendieckRelations_le_restrictionLift_ker (k := k) (G := G) H)

/-- On a generator class, subgroup restriction on `R_k(G)` gives the class of the restricted
representation in `R_k(H)`. -/
@[simp] theorem finiteRepGrothendieckGroupRestriction_apply_class
    (H : Subgroup G) (V : FDRep k G) :
    finiteRepGrothendieckGroupRestriction k H [V]₀ =
      [FDRep.subgroupRestriction (H := H) V]₀ := by
  rfl

end Subgroup

end

end SubgroupRestriction

end Representation
