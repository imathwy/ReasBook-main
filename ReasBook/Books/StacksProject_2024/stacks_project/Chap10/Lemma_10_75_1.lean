import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ProjectiveResolution
open ChainComplex
open HomologicalComplex
open MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {M1 M2 : Type u}
variable [AddCommGroup M1] [Module R M1]
variable [AddCommGroup M2] [Module R M2]
variable {F G : ChainComplex (ModuleCat R) ℕ}

local notation "moduleSingle[" M "]" =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

local notation "freeResolution[" π "]" =>
  IsFreeResolution.toProjectiveResolution π

local notation "tensorFunctor[" N "]" =>
  CategoryTheory.Functor.mapHomologicalComplex
    (tensorLeft (ModuleCat.of R N)) (ComplexShape.down ℕ)

namespace ProjectiveResolution.Hom

/-- The chain map on tensor complexes induced by a compatible lift between free resolutions. -/
noncomputable def tensorComplexMap
    (N : Type u) [AddCommGroup N] [Module R N]
    {πF : F ⟶ moduleSingle[M1]} {πG : G ⟶ moduleSingle[M2]}
    [IsFreeResolution πF] [IsFreeResolution πG]
    {f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2}
    (γ : freeResolution[πF].Hom freeResolution[πG] f) :
    (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G :=
  (tensorFunctor[N]).map γ.hom

end ProjectiveResolution.Hom

open ProjectiveResolution.Hom

-- Proof sketch: the compatible lift data is already packaged by
-- `freeResolution[πF].Hom freeResolution[πG] f`. The associated projective-resolution lifts
-- `α.hom` and `β.hom` are homotopic by `ProjectiveResolution.liftHomotopy`; tensoring with the
-- fixed module `N` sends that homotopy to a homotopy of tensor complexes, and homotopic chain
-- maps induce the same map on homology.
/-- Lemma 10.75.1 (1): any two augmentation-compatible lifts of a module map between free
resolutions induce the same map on the homology of the tensor complexes with `N`. -/
theorem tensor_resolution_homologyMap_eq_of_compatible_lifts
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2)
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α β : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℕ) :
    homologyMap
        (tensorComplexMap N β : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i =
      homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i := sorry

-- Proof sketch: lift the inverse module isomorphism to a morphism of the associated projective
-- resolutions. The two composites are compatible lifts of the identity, so part `(1)` shows that
-- the induced homology maps on the tensor complexes are inverse to one another.
/-- Lemma 10.75.1 (2): if the module map is an isomorphism, then any compatible lift between free
resolutions induces an isomorphism on every homology group after tensoring with `N`. -/
theorem tensor_resolution_homologyMap_isIso_of_isIso
    (N : Type u) [AddCommGroup N] [Module R N]
    (f : ModuleCat.of R M1 ⟶ ModuleCat.of R M2) [IsIso f]
    (πF : F ⟶ moduleSingle[M1]) (πG : G ⟶ moduleSingle[M2])
    [IsFreeResolution πF] [IsFreeResolution πG]
    (α : freeResolution[πF].Hom freeResolution[πG] f)
    (i : ℕ) :
    IsIso
      (homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj G) i) :=
  sorry

-- Proof sketch: apply part `(1)` to the given identity lift and the identity morphism of the
-- associated projective resolution. The identity lift tensors to the identity chain map, so the
-- induced map on homology is the identity.
/-- Lemma 10.75.1 (3): an endomorphism lift of the identity map on a free resolution induces the
identity on every homology group after tensoring with `N`. -/
theorem tensor_resolution_homologyMap_eq_id_of_identity_lift
    (N : Type u) [AddCommGroup N] [Module R N]
    (πF : F ⟶ moduleSingle[M1]) [IsFreeResolution πF]
    (α : freeResolution[πF].Hom freeResolution[πF] (𝟙 (ModuleCat.of R M1)))
    (i : ℕ) :
    homologyMap
        (tensorComplexMap N α : (tensorFunctor[N]).obj F ⟶ (tensorFunctor[N]).obj F) i =
      𝟙 _ := sorry

end
