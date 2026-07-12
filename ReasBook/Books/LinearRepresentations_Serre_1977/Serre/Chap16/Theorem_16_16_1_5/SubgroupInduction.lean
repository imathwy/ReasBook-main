import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1

noncomputable section

universe u

open CategoryTheory
open scoped MonoidAlgebra
open scoped Representation
open scoped TensorProduct

namespace Representation

section SubgroupInduction

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

/-- Inducing a finite-dimensional `k`-representation from a subgroup `H ≤ G` yields a
finite-dimensional `k`-representation of `G`. -/
theorem subgroupInduction_finite {H : Subgroup G} (V : FDRep k H) :
    Module.Finite k (Rep.ind H.subtype (Rep.of V.ρ)) := by
  -- Package the coinvariants quotient first so the finite-generation proof stays on the canonical
  -- induction owner.
  let ρ := Representation.tprod ((leftRegular k G).comp H.subtype) V.ρ
  let M :=
    (TensorProduct k (G →₀ k) V) ⧸
      Representation.Coinvariants.ker (k := k) (G := H)
        (V := TensorProduct k (G →₀ k) V) ρ
  let _ : Module.Finite k M := by
    infer_instance
  change Module.Finite k M
  infer_instance

/-- The finite-dimensional `k[G]`-representation induced from a finite-dimensional
`k[H]`-representation. -/
abbrev subgroupInduction {H : Subgroup G} (V : FDRep k H) : FDRep k G :=
  let ρ := Rep.ind H.subtype (Rep.of V.ρ)
  let _ : Module.Finite k ρ := subgroupInduction_finite V
  FDRep.of ρ.ρ

end FDRep

/-- Helper for Theorem 16-16.1-5: the induced morphism on bundled finite-dimensional
representations is obtained by transporting `Rep.indMap` back through `FDRep`. -/
private abbrev subgroupInduction_map {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    FDRep.subgroupInduction V ⟶ FDRep.subgroupInduction W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))

/-- Helper for Theorem 16-16.1-5: forgetting an induced `FDRep` morphism recovers the
underlying `Rep.indMap`. -/
private theorem subgroupInduction_map_forget {H : Subgroup G} {V W : FDRep k H} (f : V ⟶ W) :
    (forget₂ (FDRep k G) (Rep k G)).map (subgroupInduction_map (k := k) (G := G) f) =
      Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f) := by
  -- `subgroupInduction_map` is defined by transport across `FDRep.forget₂HomLinearEquiv`.
  change (FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W)).symm
    ((FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction V)
      (FDRep.subgroupInduction W))
      (Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f))) =
    Rep.indMap H.subtype ((forget₂ (FDRep k H) (Rep k H)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Theorem 16-16.1-5: a short complex of `FDRep k H` induces termwise to a short
complex of `FDRep k G`. -/
private abbrev subgroupInduction_shortComplex {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) : ShortComplex (FDRep k G) :=
  ShortComplex.mk
    (subgroupInduction_map (k := k) (G := G) S.f)
    (subgroupInduction_map (k := k) (G := G) S.g)
    (by
      -- After forgetting to `Rep`, this is exactly the image of `S` under subgroup induction.
      apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      rw [Functor.map_comp]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.f]
      rw [subgroupInduction_map_forget (k := k) (G := G) S.g]
      simpa using
        (((S.map (forget₂ (FDRep k H) (Rep k H))).map
          (Rep.indFunctor k H.subtype)).zero))

/-- Helper for Theorem 16-16.1-5: induction along `H ≤ G` preserves short exact sequences of
finite-dimensional representations. -/
private theorem subgroupInduction_shortExact {H : Subgroup G}
    (S : ShortComplex (FDRep k H)) (hS : S.ShortExact) :
    (subgroupInduction_shortComplex (k := k) (G := G) S).ShortExact := by
  -- First check exactness after forgetting to `Rep`, then reflect it back to `FDRep`.
  have hRep :
      (((subgroupInduction_shortComplex (k := k) (G := G) S).map
        (forget₂ (FDRep k G) (Rep k G)))).ShortExact := by
    simpa [subgroupInduction_shortComplex, subgroupInduction_map_forget] using
      (hS.map_of_exact (forget₂ (FDRep k H) (Rep k H))).map_of_exact
        (Rep.indFunctor k H.subtype)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((subgroupInduction_shortComplex (k := k) (G := G) S).exact_map_iff_of_faithful
        (forget₂ (FDRep k G) (Rep k G))).1 hRep.exact
  · exact (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g

/-- The additive lift on the free abelian group of finite-dimensional `k[H]`-representations
sending `[V]` to the induced class `[Ind_H^G(V)]`. -/
private abbrev finiteRepGrothendieckGroupInductionLift (H : Subgroup G) :
    FreeAbelianGroup (FDRep k H) →+ R₀[k](G) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.subgroupInduction V]₀

/-- The defining relations of `R_k(H)` map to zero under subgroup induction on the free abelian
group of finite-dimensional representations. -/
private theorem finiteRepGrothendieckRelations_le_inductionLift_ker (H : Subgroup G) :
    finiteRepGrothendieckRelations k H ≤ (finiteRepGrothendieckGroupInductionLift H).ker := by
  -- Evaluate subgroup induction on each defining short-exact-sequence generator.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [FDRep.subgroupInduction S.X₂]₀ - [FDRep.subgroupInduction S.X₁]₀ -
      [FDRep.subgroupInduction S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G)
      (subgroupInduction_shortComplex (k := k) (G := G) S)
      (subgroupInduction_shortExact (k := k) (G := G) S hS)
  calc
    [FDRep.subgroupInduction S.X₂]₀ - [FDRep.subgroupInduction S.X₁]₀ =
        ([FDRep.subgroupInduction S.X₁]₀ + [FDRep.subgroupInduction S.X₃]₀) -
          [FDRep.subgroupInduction S.X₁]₀ := by
            rw [hrelation]
    _ = [FDRep.subgroupInduction S.X₃]₀ := by
          abel

namespace Subgroup

/-- The induction homomorphism `Ind_H^G : R_k(H) → R_k(G)` on Grothendieck groups of
finite-dimensional `k`-representations. -/
def finiteRepGrothendieckGroupInduction (k : Type u) [Field k] (H : Subgroup G) :
    R₀[k](H) →+ R₀[k](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k H)
    (finiteRepGrothendieckGroupInductionLift (k := k) (G := G) H)
    (finiteRepGrothendieckRelations_le_inductionLift_ker (k := k) (G := G) H)

/-- On a generator class, subgroup induction on `R_k(H)` gives the class of the induced
representation in `R_k(G)`. -/
@[simp] theorem finiteRepGrothendieckGroupInduction_apply_class
    (H : Subgroup G) (V : FDRep k H) :
    finiteRepGrothendieckGroupInduction k H [V]₀ = [FDRep.subgroupInduction V]₀ := by
  -- Evaluate the quotient lift on the generator `FreeAbelianGroup.of V`.
  rfl
end Subgroup

end

end SubgroupInduction

end Representation
