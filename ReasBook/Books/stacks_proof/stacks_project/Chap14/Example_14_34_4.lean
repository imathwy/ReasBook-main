import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_6
import StacksProject_2024.Chap14.Example_14_33_1
import StacksProject_2024.Chap14.Lemma_14_31_9
import StacksProject_2024.Chap14.Lemma_14_33_2
import StacksProject_2024.Chap14.Lemma_14_34_2
import StacksProject_2024.Chap14.Lemma_14_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Functor
open scoped Simplicial
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (R : Type u) [Ring R]

private abbrev freeForgetResolutionFunctor (R : Type u) [Ring R] :
    ModuleCat R ⥤ ModuleCat R :=
  (ModuleCat.adj R).toComonad.toFunctor

private theorem freeForgetAdjunctionResolution_realization :
    IteratedEndofunctorRealization (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (iteratedEndofunctorResolution
        (ModuleCat.adj R).toComonad.ε
        (ModuleCat.adj R).toComonad.δ
        (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
        (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
        (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))) :=
  iteratedEndofunctorResolution_realization
    (ModuleCat.adj R).toComonad.ε
    (ModuleCat.adj R).toComonad.δ
    (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
    (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
    (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))

/-- The augmented simplicial endofunctor resolution attached to the free-forgetful adjunction on
`ModuleCat R`. -/
private noncomputable def freeForgetAdjunctionAugmentedResolution :
    SimplicialObject.Augmented (ModuleCat R ⥤ ModuleCat R) where
  left :=
    iteratedEndofunctorResolution
      (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (adjunction_iteratedEndofunctor_hσδ₀ (ModuleCat.adj R))
      (adjunction_iteratedEndofunctor_hσδ₁ (ModuleCat.adj R))
      (adjunction_iteratedEndofunctor_hσσ (ModuleCat.adj R))
  right := 𝟭 (ModuleCat R)
  hom :=
    iteratedEndofunctorAugmentation
      (ModuleCat.adj R).toComonad.ε
      (ModuleCat.adj R).toComonad.δ
      (freeForgetAdjunctionResolution_realization R)

/-- Evaluating the canonical augmented free-forgetful adjunction resolution at an `R`-module `M`
gives the augmented simplicial `R`-module whose `n`-simplices are the `n`-fold iterates of the
comonad `ModuleCat.free R ⋙ forget (ModuleCat R)` applied to `M`. -/
abbrev freeForgetAdjunctionAugmentedModuleResolution (M : ModuleCat R) :
    SimplicialObject.Augmented (ModuleCat R) :=
  (whiskeringObj (ModuleCat R ⥤ ModuleCat R) (ModuleCat R)
      ((evaluation (ModuleCat R) (ModuleCat R)).obj M)).obj
    (freeForgetAdjunctionAugmentedResolution R)

/- The source-facing underlying simplicial object is the left side of the evaluated augmented
resolution. -/
abbrev freeForgetAdjunctionModuleResolution (M : ModuleCat R) :
    SimplicialObject (ModuleCat R) :=
  (freeForgetAdjunctionAugmentedModuleResolution R M).left

-- Proof sketch: evaluate the object-part equality from
-- `freeForgetAdjunctionResolution_realization R` in degree `n` at the module `M`.
/-- The degree-`n` term of the evaluated free-forgetful resolution is the value at `M` of the
iterated comonad endofunctor. -/
theorem freeForgetAdjunctionModuleResolution_obj_eq (M : ModuleCat R) (n : ℕ) :
    (freeForgetAdjunctionModuleResolution R M).obj (op ⦋n⦌) =
      ((ModuleCat.adj R).toComonad.toFunctor)⦅n⦆.obj M := by
  -- Evaluate the realization witness in simplicial degree `n` at the chosen module `M`.
  simpa [freeForgetAdjunctionModuleResolution, freeForgetAdjunctionAugmentedModuleResolution] using
    congrArg (fun Z : ModuleCat R ⥤ ModuleCat R ↦ Z.obj M)
      ((freeForgetAdjunctionResolution_realization R).obj_eq n)

/-- Forgetting the evaluated augmented free-forgetful resolution to sets. -/
abbrev freeForgetAdjunctionAugmentedUnderlyingSet (M : ModuleCat R) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (ModuleCat R) (Type u) (forget (ModuleCat R))).obj
    (freeForgetAdjunctionAugmentedModuleResolution R M)

/-- Forgetting the evaluated augmented free-forgetful resolution to additive groups. -/
abbrev freeForgetAdjunctionAugmentedUnderlyingAddCommGrp (M : ModuleCat R) :
    SimplicialObject.Augmented AddCommGrpCat :=
  (whiskeringObj (ModuleCat R) AddCommGrpCat (forget₂ (ModuleCat R) AddCommGrpCat)).obj
    (freeForgetAdjunctionAugmentedModuleResolution R M)

-- Proof sketch: apply `postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence` to the
-- free-forgetful adjunction `ModuleCat.adj R`, then evaluate the resulting simplicial homotopy
-- equivalence in the module `M`.
/-- Example 14.34.4: for a ring `R` and an `R`-module `M`, evaluating the standard simplicial
resolution of the free-forgetful adjunction at `M` gives a simplicial `R`-module with terms
`R[M]`, `R[R[M]]`, `R[R[R[M]]]`, and so on, whose augmentation to the constant simplicial object
on `M` becomes a simplicial homotopy equivalence after forgetting to sets. -/
@[stacks 0G5T]
theorem freeForgetAdjunctionModuleResolutionForgetAugmentation_isHomotopyEquivalence
    (M : ModuleCat R) :
    IsHomotopyEquivalence (freeForgetAdjunctionAugmentedUnderlyingSet R M).hom := by
  -- Specialize Lemma 14.34.3 to the free-forgetful adjunction and then evaluate at `M`.
  rcases
      postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
        (adj := ModuleCat.adj R)
        (hX := freeForgetAdjunctionResolution_realization R) with
    ⟨e, he⟩
  refine ⟨
    { hom := Functor.whiskerRight e.hom ((evaluation (ModuleCat R) (Type u)).obj M)
      inv := Functor.whiskerRight e.inv ((evaluation (ModuleCat R) (Type u)).obj M)
      homotopyHomInvId := by
        -- Whiskering the homotopy witness by evaluation turns it into the desired simplicial-set
        -- homotopy after evaluating the functor-valued resolution at `M`.
        simpa [freeForgetAdjunctionAugmentedUnderlyingSet, freeForgetAdjunctionAugmentedModuleResolution,
          freeForgetAdjunctionAugmentedResolution] using
          Homotopic.whiskerRight e.homotopyHomInvId
            ((evaluation (ModuleCat R) (Type u)).obj M)
      homotopyInvHomId := by
        -- The same evaluation argument applies to the other composite.
        simpa [freeForgetAdjunctionAugmentedUnderlyingSet, freeForgetAdjunctionAugmentedModuleResolution,
          freeForgetAdjunctionAugmentedResolution] using
          Homotopic.whiskerRight e.homotopyInvHomId
            ((evaluation (ModuleCat R) (Type u)).obj M) },
    ?_⟩
  -- Evaluating the forward map of the functor-valued homotopy equivalence gives the displayed
  -- augmentation of simplicial sets.
  simpa [freeForgetAdjunctionAugmentedUnderlyingSet, freeForgetAdjunctionAugmentedModuleResolution,
    freeForgetAdjunctionAugmentedResolution] using
    congrArg
      (fun f ↦ Functor.whiskerRight f ((evaluation (ModuleCat R) (Type u)).obj M))
      he

/-- Helper for Example 14.34.4: forgetting the `R`-module structure conjugates the homology map
of a chain map with the homology map of the forgotten chain map via `mapHomologyIso`. -/
private theorem forget_to_addCommGrp_homologyMap_formula
    {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).map (HomologicalComplex.homologyMap φ i) =
      ((K.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).inv ≫
        HomologicalComplex.homologyMap
          (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.down ℕ)).map φ) i ≫
        ((L.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom := by
  -- Rewrite the inverse-form naturality square into the forward transport formula used below.
  calc
    (forget₂ (ModuleCat R) AddCommGrpCat).map (HomologicalComplex.homologyMap φ i) =
        (forget₂ (ModuleCat R) AddCommGrpCat).map (HomologicalComplex.homologyMap φ i) ≫
          ((L.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).inv ≫
            ((L.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom := by
              simp
    _ =
        ((K.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).inv ≫
          HomologicalComplex.homologyMap
            (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
              (ComplexShape.down ℕ)).map φ) i ≫
            ((L.sc i).mapHomologyIso (forget₂ (ModuleCat R) AddCommGrpCat)).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ ((L.sc i).mapHomologyIso
                    (forget₂ (ModuleCat R) AddCommGrpCat)).hom)
                  (ShortComplex.mapHomologyIso_inv_naturality
                    (F := forget₂ (ModuleCat R) AddCommGrpCat)
                    (φ := φ.sc i))

/-- Helper for Example 14.34.4: the forgetful functor to additive groups reflects
quasi-isomorphisms of chain complexes of `R`-modules. -/
private theorem moduleCat_forget_reflects_quasiIso
    {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L)
    (hφ :
      QuasiIso
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ)) :
    QuasiIso φ := by
  -- Check the quasi-isomorphism degreewise after transporting homology through the forgetful
  -- comparison isomorphisms.
  rw [quasiIso_iff] at hφ ⊢
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap] at hφ ⊢
  letI :
      IsIso
        (((forget₂ (ModuleCat R) AddCommGrpCat).map
          (HomologicalComplex.homologyMap φ i))) := by
    rw [forget_to_addCommGrp_homologyMap_formula (R := R) (φ := φ) (i := i)]
    infer_instance
  -- Since `forget₂ (ModuleCat R) AddCommGrpCat` reflects isomorphisms, the original homology map
  -- is already an isomorphism.
  exact isIso_of_reflects_iso (HomologicalComplex.homologyMap φ i)
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Helper for Example 14.34.4: a quasi-isomorphism on normalized Moore complexes induces a
quasi-isomorphism on alternating face map complexes for simplicial abelian groups. -/
private theorem alternatingFaceMapComplex_map_quasiIso_of_normalizedMooreComplex_quasiIso
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hqis : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
  let _ : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f) := hqis
  let eX :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj X)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj X) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let eY :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj Y)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj Y) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let _ : QuasiIso (inclusionOfMooreComplexMap X) := by
    -- The Dold-Kan comparison `N(X) ⟶ s(X)` is itself a quasi-isomorphism.
    simpa [eX] using (show QuasiIso eX.hom from inferInstance)
  let _ : QuasiIso (inclusionOfMooreComplexMap Y) := by
    -- The same comparison is available on the target simplicial abelian group.
    simpa [eY] using (show QuasiIso eY.hom from inferInstance)
  have hnat :
      ((normalizedMooreComplex AddCommGrpCat).map f) ≫ inclusionOfMooreComplexMap Y =
        inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex AddCommGrpCat.{u}).map f := by
    -- Naturality of `inclusionOfMooreComplexMap` relates the normalized and alternating maps.
    simpa using (inclusionOfMooreComplex AddCommGrpCat).naturality f
  have hcomp :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
    have hcomp' :
        QuasiIso
          (((normalizedMooreComplex AddCommGrpCat).map f) ≫
            inclusionOfMooreComplexMap Y) := by
      infer_instance
    -- Rewriting along the naturality square transports the known quasi-isomorphism.
    rw [← hnat]
    exact hcomp'
  let _ :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := hcomp
  -- Cancel the left comparison quasi-isomorphism to finish on the alternating face map complex.
  exact
    quasiIso_of_comp_left
      (inclusionOfMooreComplexMap X)
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)

/-- Helper for Example 14.34.4: the remaining source-faithful 14.31.9-style step is to prove the
forgotten augmentation is a quasi-isomorphism on normalized Moore complexes. -/
private theorem freeForgetAdjunctionUnderlyingAddCommGrp_normalizedMoore_quasiIso
    (M : ModuleCat R) :
    QuasiIso
      ((normalizedMooreComplex AddCommGrpCat).map
        (freeForgetAdjunctionAugmentedUnderlyingAddCommGrp R M).hom) := by
  -- Route correction: use the canonical 14.31.9 bridge instead of recreating the reduced-lift
  -- argument locally.
  exact
    CategoryTheory.SimplicialObject.normalizedMooreComplex_map_quasiIso_of_homotopyEquivalence
      (f := (freeForgetAdjunctionAugmentedUnderlyingAddCommGrp R M).hom)
      (by
        -- Forgetting the simplicial abelian-group augmentation to sets recovers the previously
        -- established simplicial homotopy equivalence.
        simpa [freeForgetAdjunctionAugmentedUnderlyingAddCommGrp,
          freeForgetAdjunctionAugmentedUnderlyingSet,
          freeForgetAdjunctionAugmentedModuleResolution] using
          freeForgetAdjunctionModuleResolutionForgetAugmentation_isHomotopyEquivalence
            (R := R) M)

/-- Helper for Example 14.34.4: once the normalized Moore comparison is known for the forgotten
augmentation, the alternating face map complex comparison follows formally. -/
private theorem freeForgetAdjunctionUnderlyingAddCommGrp_quasiIso
    (M : ModuleCat R) :
    QuasiIso
      ((alternatingFaceMapComplex AddCommGrpCat).map
        (freeForgetAdjunctionAugmentedUnderlyingAddCommGrp R M).hom) := by
  -- The Dold-Kan comparison upgrades the normalized-Moore quasi-isomorphism to the displayed
  -- alternating-face augmentation.
  exact
    alternatingFaceMapComplex_map_quasiIso_of_normalizedMooreComplex_quasiIso
      (f := (freeForgetAdjunctionAugmentedUnderlyingAddCommGrp R M).hom)
      (freeForgetAdjunctionUnderlyingAddCommGrp_normalizedMoore_quasiIso (R := R) M)

/-- Helper for Example 14.34.4: forgetting the alternating-face augmentation of the simplicial
`R`-module resolution agrees degreewise with the alternating-face augmentation of the forgotten
augmented simplicial abelian group. -/
private theorem forgotten_freeForgetAdjunctionAlternatingFaceMapComplex_map_eq
    (M : ModuleCat R) :
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (AlternatingFaceMapComplex.ε.app (freeForgetAdjunctionAugmentedModuleResolution R M))) =
        ((alternatingFaceMapComplex AddCommGrpCat).map
          (freeForgetAdjunctionAugmentedUnderlyingAddCommGrp R M).hom) := by
  -- Both chain maps are obtained by applying the same alternating-face construction after
  -- forgetting from `ModuleCat R` to `AddCommGrpCat`.
  ext n
  rfl

/-- Helper for Example 14.34.4: after forgetting to additive groups, the alternating-face
augmentation is expected to agree with the source-faithful simplicial-abelian-group comparison. -/
private theorem forgotten_freeForgetAdjunctionAlternatingFaceMapComplex_quasiIso
    (M : ModuleCat R) :
    QuasiIso
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (AlternatingFaceMapComplex.ε.app (freeForgetAdjunctionAugmentedModuleResolution R M))) := by
  -- Rewrite the forgotten chain map to the already-established simplicial-abelian-group
  -- augmentation map.
  rw [forgotten_freeForgetAdjunctionAlternatingFaceMapComplex_map_eq (R := R) (M := M)]
  exact freeForgetAdjunctionUnderlyingAddCommGrp_quasiIso (R := R) M

-- Proof sketch: use the simplicial homotopy equivalence of the augmentation together with the
-- comparison lemmas between simplicial homotopy equivalences and quasi-isomorphisms of Moore or
-- alternating-face complexes; the target is `ChainComplex.single₀ (ModuleCat R)` on `M`, so this
-- says exactly that the associated chain complex has homology `M` in degree `0` and vanishing
-- homology in positive degrees.
/-- The augmentation of the alternating face map complex of the free-forgetful resolution is a
quasi-isomorphism to the complex concentrated in degree `0` at `M`. -/
theorem freeForgetAdjunctionModuleResolutionAlternatingFaceMapComplex_quasiIso
    (M : ModuleCat R) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (freeForgetAdjunctionAugmentedModuleResolution R M)) :=
  by
  -- Route correction: the main theorem now uses the localized forgotten-`AddCommGrpCat` bridge,
  -- so the only remaining blocker sits in the normalized-Moore comparison helper above.
  refine
    moduleCat_forget_reflects_quasiIso
      (R := R)
      (φ := AlternatingFaceMapComplex.ε.app (freeForgetAdjunctionAugmentedModuleResolution R M))
      (forgotten_freeForgetAdjunctionAlternatingFaceMapComplex_quasiIso (R := R) M)

end CategoryTheory
