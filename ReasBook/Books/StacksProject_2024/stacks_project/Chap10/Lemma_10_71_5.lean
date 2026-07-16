import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ProjectiveResolution
open CochainComplex.HomComplex
open HomologicalComplex
open ChainComplex

noncomputable section

universe u v

section

variable {R : Type u} [Ring R]
variable {M1 M2 N : Type v}
variable [AddCommGroup M1] [Module R M1]
variable [AddCommGroup M2] [Module R M2]
variable [AddCommGroup N] [Module R N]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

local notation "cochainSingle[" M "]" =>
  CategoryTheory.Functor.obj (CochainComplex.singleFunctor (ModuleCat R) 0) (ModuleCat.of R M)

local notation "freeResolution[" π "]" =>
  IsFreeResolution.toProjectiveResolution π

local notation "resolutionHomComplex[" π "]" =>
  CochainComplex.HomComplex
    (ProjectiveResolution.cochainComplex freeResolution[π])
    cochainSingle[N]

namespace ProjectiveResolution.Hom

noncomputable def homComplexMap
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    (γ : freeResolution[πF].Hom freeResolution[πG] f) :
    resolutionHomComplex[πG] ⟶ resolutionHomComplex[πF] := by
  exact
    { f := fun j ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ (Cochain.ofHom γ.hom').comp z (zero_add j)
          map_zero' := by simp
          map_add' := by simp [Cochain.comp_add] }
      comm' := fun j k hjk ↦ by
        ext z
        change δ j k ((Cochain.ofHom γ.hom').comp z (zero_add j)) =
          (Cochain.ofHom γ.hom').comp (δ j k z) (zero_add k)
        exact δ_ofHom_comp γ.hom' z k }

end ProjectiveResolution.Hom

open ProjectiveResolution.Hom

/-- Lemma 10.71.5: any two compatible lifts of a module map between free resolutions induce the
same map on the cohomology of the contravariant `Hom_R(-, N)` complex. -/
-- Proof sketch: the two compatible lifts are morphisms of the associated projective resolutions,
-- hence `ProjectiveResolution.liftHomotopy` gives a homotopy between their induced cochain maps
-- `α.hom'` and `β.hom'`. Precomposition with these morphisms defines the canonical maps on the
-- `CochainComplex.HomComplex` computing `Hom_R(-, N)` cohomology, and `Homotopy.homologyMap_eq`
-- identifies the induced cohomology maps.
theorem resolution_homologyMap_eq_of_compatible_lifts
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2)
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α β : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℤ) :
    homologyMap (homComplexMap β : resolutionHomComplex[πG] ⟶
      resolutionHomComplex[πF]) i =
      homologyMap (homComplexMap α : resolutionHomComplex[πG] ⟶
        resolutionHomComplex[πF]) i :=
      sorry

/-- Compatible lifts of an isomorphism induce isomorphisms on all `Hom_R(-, N)` cohomology
groups. -/
-- Proof sketch: choose a compatible lift of the inverse using the projective-resolution lifting
-- API. The two composites are compatible lifts of the identity, so the previous theorem shows
-- that the induced cohomology maps are inverse to one another.
theorem resolution_homologyMap_isIso_of_isIso
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2) [IsIso f]
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℤ) :
    IsIso
      (homologyMap (homComplexMap α : resolutionHomComplex[πG] ⟶
        resolutionHomComplex[πF]) i) :=
      sorry

/-- An endomorphism lift of the identity induces the identity on the cohomology of
`Hom_R(-, N)`. -/
-- Proof sketch: apply the compatibility-independence statement to the given identity lift and the
-- identity morphism of the free resolution.
theorem resolution_homologyMap_eq_id_of_identity_lift
    (πF : F ⟶ moduleSingle[M1]) [IsFreeResolution πF]
    (α : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
    (i : ℤ) :
    homologyMap (homComplexMap α : resolutionHomComplex[πF] ⟶
      resolutionHomComplex[πF]) i = 𝟙 _ := sorry

end
