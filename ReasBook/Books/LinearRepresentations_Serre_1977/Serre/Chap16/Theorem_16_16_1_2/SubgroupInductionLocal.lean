import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3.GrothendieckBasics
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1

noncomputable section

universe u

namespace Representation

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

section

variable {F : Type u} [Field F]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

/-- Helper for Theorem 16-16.1-2: inducing a finite-dimensional representation from a subgroup
keeps finite-dimensionality over the base field. -/
theorem subgroupInductionFinite_splitInjective {H : Subgroup G} (V : FDRep F H) :
    Module.Finite F (Rep.ind H.subtype (Rep.of V.ρ)) := by
  -- The canonical induced representation is a quotient of a finite tensor product, so it is finite
  -- over the base field.
  let ρ := Representation.tprod ((leftRegular F G).comp H.subtype) V.ρ
  let M :=
    (TensorProduct F (G →₀ F) V) ⧸
      Representation.Coinvariants.ker (k := F) (G := H)
        (V := TensorProduct F (G →₀ F) V) ρ
  let _ : Module.Finite F M := by
    infer_instance
  change Module.Finite F M
  infer_instance

/-- Helper for Theorem 16-16.1-2: the finite-dimensional representation induced from a subgroup
representation, using theorem-local names to avoid importing later item modules. -/
abbrev subgroupInduction_splitInjective {H : Subgroup G} (V : FDRep F H) : FDRep F G :=
  let ρ := Rep.ind H.subtype (Rep.of V.ρ)
  let _ : Module.Finite F ρ := subgroupInductionFinite_splitInjective V
  FDRep.of ρ.ρ

end FDRep

/-- Helper for Theorem 16-16.1-2: the induced morphism on theorem-local bundled induced
representations. -/
private abbrev subgroupInductionMap_splitInjective {H : Subgroup G} {V W : FDRep F H}
    (f : V ⟶ W) :
    FDRep.subgroupInduction_splitInjective V ⟶ FDRep.subgroupInduction_splitInjective W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (Rep.indMap H.subtype ((forget₂ (FDRep F H) (Rep F H)).map f))

/-- Helper for Theorem 16-16.1-2: forgetting the theorem-local induced morphism recovers the
ordinary induced morphism in `Rep`. -/
private theorem subgroupInductionMap_forget_splitInjective {H : Subgroup G} {V W : FDRep F H}
    (f : V ⟶ W) :
    (forget₂ (FDRep F G) (Rep F G)).map
        (subgroupInductionMap_splitInjective (F := F) (G := G) f) =
      Rep.indMap H.subtype ((forget₂ (FDRep F H) (Rep F H)).map f) := by
  -- The map was defined by transporting through the faithful forgetful linear equivalence.
  change (FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction_splitInjective V)
      (FDRep.subgroupInduction_splitInjective W)).symm
    ((FDRep.forget₂HomLinearEquiv (FDRep.subgroupInduction_splitInjective V)
      (FDRep.subgroupInduction_splitInjective W))
      (Rep.indMap H.subtype ((forget₂ (FDRep F H) (Rep F H)).map f))) =
    Rep.indMap H.subtype ((forget₂ (FDRep F H) (Rep F H)).map f)
  exact (FDRep.forget₂HomLinearEquiv _ _).left_inv _

/-- Helper for Theorem 16-16.1-2: the theorem-local induced maps form a short complex. -/
private theorem subgroupInductionShortComplex_zero_splitInjective {H : Subgroup G}
    (S : ShortComplex (FDRep F H)) :
    subgroupInductionMap_splitInjective (F := F) (G := G) S.f ≫
        subgroupInductionMap_splitInjective (F := F) (G := G) S.g = 0 := by
  -- Check the zero-composition after forgetting to `Rep`, where it is functoriality of
  -- `Rep.indFunctor`.
  apply (forget₂ (FDRep F G) (Rep F G)).map_injective
  rw [Functor.map_comp]
  rw [subgroupInductionMap_forget_splitInjective (F := F) (G := G) S.f]
  rw [subgroupInductionMap_forget_splitInjective (F := F) (G := G) S.g]
  simpa using
    (((S.map (forget₂ (FDRep F H) (Rep F H))).map
      (Rep.indFunctor F H.subtype)).zero)

/-- Helper for Theorem 16-16.1-2: termwise theorem-local induction of a short complex of subgroup
representations. -/
private abbrev subgroupInductionShortComplex_splitInjective {H : Subgroup G}
    (S : ShortComplex (FDRep F H)) : ShortComplex (FDRep F G) :=
  ShortComplex.mk
    (subgroupInductionMap_splitInjective (F := F) (G := G) S.f)
    (subgroupInductionMap_splitInjective (F := F) (G := G) S.g)
    (subgroupInductionShortComplex_zero_splitInjective (F := F) (G := G) S)

/-- Helper for Theorem 16-16.1-2: theorem-local subgroup induction preserves short exact
sequences. -/
private theorem subgroupInductionShortExact_splitInjective {H : Subgroup G}
    (S : ShortComplex (FDRep F H)) (hS : S.ShortExact) :
    (subgroupInductionShortComplex_splitInjective (F := F) (G := G) S).ShortExact := by
  -- Prove exactness after forgetting to `Rep`, then reflect it through the faithful forgetful
  -- functor back to `FDRep`.
  have hRep :
      (((subgroupInductionShortComplex_splitInjective (F := F) (G := G) S).map
        (forget₂ (FDRep F G) (Rep F G)))).ShortExact := by
    simpa [subgroupInductionShortComplex_splitInjective,
      subgroupInductionMap_forget_splitInjective] using
      (hS.map_of_exact (forget₂ (FDRep F H) (Rep F H))).map_of_exact
        (Rep.indFunctor F H.subtype)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact
      ((subgroupInductionShortComplex_splitInjective (F := F) (G := G) S).exact_map_iff_of_faithful
        (forget₂ (FDRep F G) (Rep F G))).1 hRep.exact
  · exact (forget₂ (FDRep F G) (Rep F G)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep F G) (Rep F G)).epi_of_epi_map hRep.epi_g

/-- Helper for Theorem 16-16.1-2: the free-abelian lift sending a subgroup class to its
theorem-local induced class. -/
private abbrev finiteRepGrothendieckGroupInductionLift_splitInjective (H : Subgroup G) :
    FreeAbelianGroup (FDRep F H) →+ R₀[F](G) :=
  FreeAbelianGroup.lift fun V ↦ [FDRep.subgroupInduction_splitInjective V]₀

/-- Helper for Theorem 16-16.1-2: theorem-local induction kills Grothendieck short-exact
relations. -/
private theorem finiteRepGrothendieckRelations_le_inductionLift_ker_splitInjective
    (H : Subgroup G) :
    finiteRepGrothendieckRelations F H ≤
      (finiteRepGrothendieckGroupInductionLift_splitInjective (F := F) (G := G) H).ker := by
  -- Evaluate a relation generator and replace the middle induced class using exactness of
  -- theorem-local subgroup induction.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change [FDRep.subgroupInduction_splitInjective S.X₂]₀ -
      [FDRep.subgroupInduction_splitInjective S.X₁]₀ -
        [FDRep.subgroupInduction_splitInjective S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := F) (G := G)
      (subgroupInductionShortComplex_splitInjective (F := F) (G := G) S)
      (subgroupInductionShortExact_splitInjective (F := F) (G := G) S hS)
  calc
    [FDRep.subgroupInduction_splitInjective S.X₂]₀ -
        [FDRep.subgroupInduction_splitInjective S.X₁]₀ =
        ([FDRep.subgroupInduction_splitInjective S.X₁]₀ +
            [FDRep.subgroupInduction_splitInjective S.X₃]₀) -
          [FDRep.subgroupInduction_splitInjective S.X₁]₀ := by
            rw [hrelation]
    _ = [FDRep.subgroupInduction_splitInjective S.X₃]₀ := by
          abel

/-- Helper for Theorem 16-16.1-2: theorem-local subgroup induction on finite-representation
Grothendieck groups, kept acyclic from the later Theorem 16-16.1-5 owner. -/
def finiteRepGrothendieckGroupInduction_splitInjective (F : Type u) [Field F]
    (H : Subgroup G) :
    R₀[F](H) →+ R₀[F](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations F H)
    (finiteRepGrothendieckGroupInductionLift_splitInjective (F := F) (G := G) H)
    (finiteRepGrothendieckRelations_le_inductionLift_ker_splitInjective (F := F) (G := G) H)

/-- Helper for Theorem 16-16.1-2: theorem-local subgroup induction sends a generator class to the
class of the theorem-local induced representation. -/
@[simp] theorem finiteRepGrothendieckGroupInduction_splitInjective_apply_class
    (H : Subgroup G) (V : FDRep F H) :
    finiteRepGrothendieckGroupInduction_splitInjective F H [V]₀ =
      [FDRep.subgroupInduction_splitInjective V]₀ := by
  -- The quotient lift evaluates directly on free generators.
  rfl

end

end Representation
