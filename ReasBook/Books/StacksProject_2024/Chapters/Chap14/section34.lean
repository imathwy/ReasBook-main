import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_34_2 (from Chap14) -/
open CategoryTheory
open scoped IteratedEndofunctor

attribute [local instance] endofunctorMonoidalCategory

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable {U : 𝒮 ⥤ 𝒜} {V : 𝒜 ⥤ 𝒮}

section

variable (adj : U ⊣ V)

local notation "T" => adj.toComonad.toFunctor
local notation "ε" => adj.toComonad.ε
local notation "δ" => adj.toComonad.δ

/- Domain-style sampling:
- primary domain: simplicial endofunctor resolutions attached to an adjunction via its induced
  comonad;
- sampled owner declarations:
  `IteratedEndofunctorRealization`,
  `iteratedEndofunctorResolution`,
  `iteratedEndofunctorResolution_realization`,
  `iteratedEndofunctorAugmentation`;
- best owner abstraction: the chapter owner
  `iteratedEndofunctorResolution adj.toComonad.ε adj.toComonad.δ ...`, specialized directly to
  the comonad of `adj`;
- primitive data: the comonad attached to `adj`, namely the endofunctor
  `adj.toComonad.toFunctor` with counit `adj.toComonad.ε` and comultiplication
  `adj.toComonad.δ`;
- derived API: the canonical chapter owners specialized to `adj.toComonad`, together with the
  existence/uniqueness theorem below;
- source/core/bridge triage:
  - `source-facing`: the existence statement below;
  - `core/canonical`: the chapter owners `IteratedEndofunctorRealization`,
    `iteratedEndofunctorResolution`, and `iteratedEndofunctorAugmentation`;
  - `bridge/view`: the three low-degree comonad-law identities supplying the hypotheses of
    `iteratedEndofunctorResolution`, `iteratedEndofunctorResolution_realization`,
    `iteratedEndofunctorAugmentation`, and
    `iteratedEndofunctor_exists_unique_simplicial_object`.

This item should therefore expose only the low-degree bridge theorems and the source-facing
existence statement, so direct downstream files can call the canonical owners specialized to
`adj.toComonad` instead of going through a parallel local wrapper API.
-/

/-- The first degree-`0` simplicial identity for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσδ₀ :
    (s[T, δ]⦅0, 0⦆) ≫ d[T, ε]⦅0, 0⦆ = 𝟙 T := by
  ext X
  dsimp [Adjunction.toComonad, iteratedFaceMap, iteratedDegeneracyMap]
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl]
  rw [Fin.lastCases_castSucc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  have h : U.map (adj.unit.app (V.obj X)) ≫ (V ⋙ U).map (adj.counit.app X) =
      𝟙 (U.obj (V.obj X)) := by
    simpa [Adjunction.toComonad] using adj.toComonad.right_counit X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ U.map (V.map (adj.counit.app X)) ≫ 𝟙 (U.obj (V.obj X)) =
        U.map (adj.unit.app (V.obj X)) ≫ U.map (V.map (adj.counit.app X)) := by
    simp
  exact hs.trans h

/-- The second degree-`0` simplicial identity for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσδ₁ :
    (s[T, δ]⦅0, 0⦆) ≫ d[T, ε]⦅0, 1⦆ = 𝟙 T := by
  ext X
  dsimp [Adjunction.toComonad, iteratedFaceMap, iteratedDegeneracyMap]
  rw [show (1 : Fin 2) = Fin.last 1 by rfl]
  rw [Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  have h : U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) =
      𝟙 (U.obj (V.obj X)) := by
    exact adj.toComonad.left_counit X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) ≫ 𝟙 (U.obj (V.obj X)) =
        U.map (adj.unit.app (V.obj X)) ≫ adj.counit.app (U.obj (V.obj X)) := by
    simp
  exact hs.trans h

/-- The degree-`1` degeneracy compatibility for the comonad induced by an adjunction. -/
theorem adjunction_iteratedEndofunctor_hσσ :
    (s[T, δ]⦅0, 0⦆) ≫ s[T, δ]⦅1, 0⦆ = (s[T, δ]⦅0, 0⦆) ≫ s[T, δ]⦅1, 1⦆ := by
  ext X
  dsimp [Adjunction.toComonad, iteratedDegeneracyMap]
  rw [show (0 : Fin 2) = Fin.castSucc 0 by rfl, show (1 : Fin 2) = Fin.last 1 by rfl]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app]
  have h :
      U.map (adj.unit.app (V.obj X)) ≫ (V ⋙ U).map (U.map (adj.unit.app (V.obj X))) =
        U.map (adj.unit.app (V.obj X)) ≫ U.map (adj.unit.app (V.obj (U.obj (V.obj X)))) := by
    simpa [Adjunction.toComonad] using adj.toComonad.coassoc X
  have hs :
      U.map (adj.unit.app (V.obj X)) ≫ U.map (adj.unit.app (V.obj (U.obj (V.obj X)))) =
        U.map (adj.unit.app (V.obj X)) ≫
          U.map (adj.unit.app (V.obj ((V ⋙ U)⦅0⦆.obj X))) ≫
            𝟙 (U.obj (V.obj (U.obj (V.obj ((V ⋙ U)⦅0⦆.obj X))))) := by
    simp [iteratedEndofunctor]
  exact h.trans hs

-- Proof sketch: apply `iteratedEndofunctor_exists_unique_simplicial_object` to the comonad
-- `adj.toComonad`. The two degree-`0` identities are the comonad counit identities, and the
-- degree-`1` compatibility is comonad coassociativity.
/-- Lemma 14.34.2: in the situation of an adjunction `U ⊣ V`, the iterated endofunctor system on
`𝒜` obtained from the comonad `adj.toComonad` is realized by a unique simplicial object of
endofunctors of `𝒜`. -/
theorem adjunction_resolution_exists_unique :
    ∃! X : SimplicialObject (𝒜 ⥤ 𝒜),
      IteratedEndofunctorRealization ε δ X := by
  simpa using
    iteratedEndofunctor_exists_unique_simplicial_object
      ε
      δ
      (adjunction_iteratedEndofunctor_hσδ₀ adj)
      (adjunction_iteratedEndofunctor_hσδ₁ adj)
      (adjunction_iteratedEndofunctor_hσσ adj)

end

end CategoryTheory

/-! ### Lemma_14_34_3 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped IteratedEndofunctor
open scoped Simplicial

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable {U : 𝒮 ⥤ 𝒜} {V : 𝒜 ⥤ 𝒮}

/- Domain-style sampling for Lemma 14.34.3:
- primary domain: simplicial resolutions attached to an adjunction via its induced comonad, and
  simplicial homotopy equivalences of the resulting augmentations;
- sampled owner declarations:
  `IteratedEndofunctorRealization`,
  `iteratedEndofunctorAugmentation`,
  `prePostcomposeAugmented`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`;
- best owner abstraction: the source-facing augmentations in Lemma 14.34.3 already live on the
  canonical owners `prePostcomposeAugmented ... (iteratedEndofunctorAugmentation ...)`; the only
  additional primitive data needed for the explicit inverse is the degree-`0` section induced by
  the adjunction unit;
- primitive data vs. derived API:
  primitive data are `adj`, the realization witness `hX`, and the degree-`0` sections below;
  the simplicial inverses obtained from `SimplicialObject.fromZero` and the homotopy-equivalence
  statements are derived API;
- source/core/bridge triage:
  - `source-facing`: the two augmentation morphisms in the statement of Lemma 14.34.3;
  - `core/canonical`: `IteratedEndofunctorRealization`, `iteratedEndofunctorAugmentation`,
    `prePostcomposeAugmented`, and `SimplicialObject.IsHomotopyEquivalence`;
  - `bridge/view`: the explicit degree-`0` sections and their induced `fromZero` simplicial maps.
-/

section

variable (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
variable (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X)

local notation "aug" =>
  iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX

local notation "postAug" =>
  prePostcomposeAugmented (𝟭 𝒜) V aug

local notation "preAug" =>
  prePostcomposeAugmented U (𝟭 𝒜) aug

/-- The degree-`0` section of the postcomposed adjunction-resolution augmentation induced by the
unit of `adj`. -/
def postcompose_adjunctionResolutionAugmentation_zeroSection :
    V ⟶ (postAug).left _⦋0⦌ :=
  V.rightUnitor.inv ≫ V.whiskerLeft adj.unit ≫ (V.associator U V).inv ≫
    eqToHom (congrArg (fun Z : 𝒜 ⥤ 𝒜 ↦ Z ⋙ V) (hX.obj_eq 0).symm)

-- Proof sketch: unfold the degree-`0` augmentation component, which is the counit
-- `adj.toComonad.ε = adj.counit`, and compute the composite with the unit-induced section above.
-- After evaluating at an object `A : 𝒜`, this is exactly the right triangle identity for `adj`.
/-- The unit-induced degree-`0` map is a section of the degree-`0` augmentation component after
postcomposition by `V`. -/
theorem postcompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero :
    postcompose_adjunctionResolutionAugmentation_zeroSection adj hX ≫
        (postAug).hom.app (op ⦋0⦌) =
      𝟙 V := sorry

/-- The degree-`0` section of the precomposed adjunction-resolution augmentation induced by the
unit of `adj`. -/
def precompose_adjunctionResolutionAugmentation_zeroSection :
    U ⟶ (preAug).left _⦋0⦌ :=
  U.leftUnitor.inv ≫ whiskerRight adj.unit U ≫ (U.associator V U).hom ≫
    eqToHom (congrArg (fun Z : 𝒜 ⥤ 𝒜 ↦ U ⋙ Z) (hX.obj_eq 0).symm)

-- Proof sketch: unfold the degree-`0` augmentation component and evaluate at an object
-- `S : 𝒮`; the resulting composite is the left triangle identity for `adj`.
/-- The unit-induced degree-`0` map is a section of the degree-`0` augmentation component after
precomposition by `U`. -/
theorem precompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero :
    precompose_adjunctionResolutionAugmentation_zeroSection adj hX ≫
        (preAug).hom.app (op ⦋0⦌) =
      𝟙 U := sorry

-- Proof sketch: apply Lemma 14.33.4 to the canonical augmentation
-- after postcomposition by `V`, using the unit of the adjunction to construct a section of
-- the degree-`0` component. Then apply Lemma 14.33.5 to show the two composites are simplicially
-- homotopic to the relevant identities, with the triangle identity providing the degree-`0`
-- equality.
/-- Lemma 14.34.3 (1): after postcomposing the standard simplicial resolution attached to an
adjunction `U ⊣ V` with `V`, the induced augmentation to the constant simplicial object on `V` is a
simplicial homotopy equivalence. -/
theorem postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
    (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X) :
    IsHomotopyEquivalence
      (prePostcomposeAugmented (𝟭 𝒜) V
        (iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX)).hom := by
  let εX := iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX
  have hsection :
      (prePostcomposeAugmented (𝟭 𝒜) V εX).left.fromZero
          (postcompose_adjunctionResolutionAugmentation_zeroSection adj hX) ≫
        (prePostcomposeAugmented (𝟭 𝒜) V εX).hom =
      𝟙 _ := by
    simpa using
      prePostcomposeAugmentation_fromZero_comp_eq_id
        (𝟭 𝒜)
        V
        εX
        (postcompose_adjunctionResolutionAugmentation_zeroSection adj hX)
        (postcompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero adj hX)
  sorry

-- Proof sketch: apply Lemma 14.33.4 to the canonical augmentation
-- after precomposition by `U`, using the unit of the adjunction to construct a section of
-- the degree-`0` component. Then apply Lemma 14.33.5 to show the two composites are simplicially
-- homotopic to the relevant identities, with the other triangle identity providing the degree-`0`
-- equality.
/-- Lemma 14.34.3 (2): after precomposing the standard simplicial resolution attached to an
adjunction `U ⊣ V` with `U`, the induced augmentation to the constant simplicial object on `U` is a
simplicial homotopy equivalence. -/
theorem precompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
    (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X) :
    IsHomotopyEquivalence
      (prePostcomposeAugmented U (𝟭 𝒜)
        (iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX)).hom := by
  let εX := iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX
  have hsection :
      (prePostcomposeAugmented U (𝟭 𝒜) εX).left.fromZero
          (precompose_adjunctionResolutionAugmentation_zeroSection adj hX) ≫
        (prePostcomposeAugmented U (𝟭 𝒜) εX).hom =
      𝟙 _ := by
    simpa using
      prePostcomposeAugmentation_fromZero_comp_eq_id
        U
        (𝟭 𝒜)
        εX
        (precompose_adjunctionResolutionAugmentation_zeroSection adj hX)
        (precompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero adj hX)
  sorry

end

end CategoryTheory

/-! ### Example_14_34_4 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
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
      ((ModuleCat.adj R).toComonad.toFunctor)⦅n⦆.obj M := sorry

/-- Forgetting the evaluated augmented free-forgetful resolution to sets. -/
abbrev freeForgetAdjunctionAugmentedUnderlyingSet (M : ModuleCat R) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (ModuleCat R) (Type u) (forget (ModuleCat R))).obj
    (freeForgetAdjunctionAugmentedModuleResolution R M)

-- Proof sketch: apply `postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence` to the
-- free-forgetful adjunction `ModuleCat.adj R`, then evaluate the resulting simplicial homotopy
-- equivalence in the module `M`.
/-- Example 14.34.4: for a ring `R` and an `R`-module `M`, evaluating the standard simplicial
resolution of the free-forgetful adjunction at `M` gives a simplicial `R`-module with terms
`R[M]`, `R[R[M]]`, `R[R[R[M]]]`, and so on, whose augmentation to the constant simplicial object
on `M` becomes a simplicial homotopy equivalence after forgetting to sets. -/
theorem freeForgetAdjunctionModuleResolutionForgetAugmentation_isHomotopyEquivalence
    (M : ModuleCat R) :
    IsHomotopyEquivalence (freeForgetAdjunctionAugmentedUnderlyingSet R M).hom := sorry

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
  sorry

end CategoryTheory

/-! ### Example_14_34_5 (from Chap14) -/
open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

/- Domain-style sampling for Example 14.34.5:
- primary domain: the polynomial `A`-algebra resolution of an `A`-algebra as an augmented
  simplicial object in `Under A`, together with its forgetful views to sets and to `A`-modules;
- sampled same-kind owner declarations:
  `Arrow.augmentedCechNerve`,
  `SimplicialObject.Augmented`,
  `commAlgCatEquivUnder`,
  `AlternatingFaceMapComplex.ε`;
- best owner abstraction: the source-facing owner is the augmented Čech nerve of the counit
  `A[B] ⟶ B` in `Under A`; the forgetful functors to sets and to `A`-modules are bridge/view data
  derived from that owner, not primary public owners;
- primitive vs. derived split:
  primitive data are the counit `A[B] ⟶ B` and its canonical augmented Čech nerve in `Under A`;
  derived API is the underlying augmented simplicial set, the underlying augmented simplicial
  `A`-module, and the homotopy/quasi-isomorphism properties of their augmentations.

Source/core/bridge triage:
- `source-facing`: the augmented polynomial `A`-algebra resolution of `B` in `Under A`;
- `core/canonical`: `Arrow.augmentedCechNerve`, `commAlgCatEquivUnder`, and the canonical
  forgetful functors from `CommAlgCat A`;
- `bridge/view`: the whiskered forgetful images of the source-facing owner in `Type u` and
  `ModuleCat A`. -/

/-- The augmented simplicial polynomial `A`-algebra resolution of `B`, given by the augmented Čech
nerve of the counit `A[B] ⟶ B` in `Under A`. -/
abbrev polynomialAlgebraAugmentedResolution (B : Under A) :
    SimplicialObject.Augmented (Under A) :=
  (Arrow.mk ((Under.costarAdjForget A).counit.app B)).augmentedCechNerve

private abbrev polynomialAlgebraForgetToModule : Under A ⥤ ModuleCat A :=
  (commAlgCatEquivUnder A).inverse ⋙
    forget₂ (CommAlgCat A) (AlgCat A) ⋙
      forget₂ (AlgCat A) (ModuleCat A)

/-- The augmented simplicial set obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting to underlying sets. -/
abbrev polynomialAlgebraAugmentedUnderlyingSet (B : Under A) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (Under A) (Type u) (Under.forget A ⋙ forget CommRingCat)).obj
    (polynomialAlgebraAugmentedResolution A B)

/-- The augmented simplicial `A`-module obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting the algebra structure. -/
abbrev polynomialAlgebraAugmentedModuleResolution (B : Under A) :
    SimplicialObject.Augmented (ModuleCat A) :=
  (whiskeringObj (Under A) (ModuleCat A) (polynomialAlgebraForgetToModule A)).obj
    (polynomialAlgebraAugmentedResolution A B)

-- Proof sketch: the counit map `A[B] ⟶ B` is split by the unit of the adjunction, so its
-- augmented Cech nerve has an extra degeneracy. After forgetting to sets, this gives a simplicial
-- homotopy equivalence for the augmentation of the underlying simplicial set.
/-- Example 14.34.5: for a commutative ring `A` and a commutative `A`-algebra `B`, the
augmentation of the underlying simplicial set of `polynomialAlgebraAugmentedResolution A B`
admits a simplicial homotopy inverse. -/
theorem polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence
    (B : Under A) :
    IsHomotopyEquivalence (polynomialAlgebraAugmentedUnderlyingSet A B).hom := sorry

-- Proof sketch: the extra degeneracy on the augmented Cech nerve survives under the forgetful
-- functor `Under A ⥤ ModuleCat A`. Applying the standard extra-degeneracy argument for
-- alternating-face-map complexes yields a quasi-isomorphism to the complex concentrated in degree
-- `0` at the underlying `A`-module of `B`.
/-- The augmentation of the alternating face map complex of
`polynomialAlgebraAugmentedResolution A B`, after forgetting to `A`-modules, is a
quasi-isomorphism to the complex concentrated in degree `0` at `B`. -/
theorem polynomialAlgebraResolutionAlternatingFaceMapComplex_quasiIso
    (B : Under A) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (polynomialAlgebraAugmentedModuleResolution A B)) :=
  sorry

end CategoryTheory

/-! ### Example_14_34_6 (from Chap14) -/
open CategoryTheory
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (R : Type u) [Ring R] (M : ModuleCat R)

/- Domain-style sampling:
- primary domain: low-degree face and degeneracy maps in the simplicial resolution attached to the
  free-forgetful adjunction on `ModuleCat R`;
- sampled owner declarations:
  `iteratedFaceMap`,
  `iteratedDegeneracyMap`,
  `SimplicialObject.δ`,
  `SimplicialObject.σ`;
- best owner abstraction: the source-facing formulas in this example should reuse the owner maps
  `d[T, ε]` and `s[T, δ]` from `Example_14_33_1`, specialized to the comonad of
  `ModuleCat.adj R`; separate public abbreviations for `d₀`, `d₁`, `s₀`, and `s₁` are only
  derived aliases and should not remain as parallel API;
- source/core/bridge triage:
  - `source-facing`: the four explicit formulas on nested sums in degree `1`;
  - `core/canonical`: the simplicial-resolution face and degeneracy owners
    `SimplicialObject.δ`/`SimplicialObject.σ`;
  - `bridge/view`: the specialization of `d[T, ε]` and `s[T, δ]` to the free-forgetful comonad on
    `ModuleCat R`;
- primitive data: the ring `R`, the module `M`, and the comonad
  `((ModuleCat.adj R).toComonad)` on `ModuleCat R`;
- derived API: the four degree-`1` maps and their explicit evaluations on nested finite sums.
-/

private abbrev freeForgetResolutionFunctor (R : Type u) [Ring R] :
    ModuleCat R ⥤ ModuleCat R :=
  (ModuleCat.adj R).toComonad.toFunctor

private abbrev freeForgetResolutionCounit (R : Type u) [Ring R] :
    freeForgetResolutionFunctor R ⟶ 𝟭 (ModuleCat R) :=
  (ModuleCat.adj R).toComonad.ε

private abbrev freeForgetResolutionComultiplication (R : Type u) [Ring R] :
    freeForgetResolutionFunctor R ⟶
      freeForgetResolutionFunctor R ⋙ freeForgetResolutionFunctor R :=
  (ModuleCat.adj R).toComonad.δ

local notation "T" => freeForgetResolutionFunctor R
local notation "ε" => freeForgetResolutionCounit R
local notation "δ" => freeForgetResolutionComultiplication R
local notation "d^⦅" n ", " j "⦆" => d[T, ε]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[T, δ]⦅n, j⦆

-- Proof sketch: unfold `d^⦅0, (1 : Fin 2)⦆.app M` to the degree-`1` face map
-- `iteratedFaceMap ((ModuleCat.adj R).toComonad.toFunctor) ((ModuleCat.adj R).toComonad.ε) 0 1`,
-- which is the free-module descender that
-- applies the counit to the outer copy of `R[-]`. Evaluating on the displayed finite sum combines
-- the outer and inner coefficients into a single sum in `R[M]`.
/-- Example 14.34.6 (1): for a typical element
`ξ = ∑ i, r i • [∑ j, s i j • [m i j]]` of `R[R[M]]`, the face map `d₀` collapses the outer
brackets and sends `ξ` to `∑ i, ∑ j, (r i * s i j) • [m i j]`. -/
theorem freeForgetAdjunctionModuleResolutionD0_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    d^⦅0, (1 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j) := sorry

-- Proof sketch: unfold `d^⦅0, (0 : Fin 2)⦆.app M` to the degree-`1` face map
-- `iteratedFaceMap ((ModuleCat.adj R).toComonad.toFunctor) ((ModuleCat.adj R).toComonad.ε) 0 0`,
-- which applies the counit to the inner copy of `R[-]` before reintroducing the outer bracket.
-- The displayed formula is then the universal property of the free module applied to each basis
-- element.
/-- Example 14.34.6 (2): for the same typical element `ξ`, the face map `d₁` applies the inner
free-module counit and sends `ξ` to `∑ i, r i • [∑ j, s i j • m i j]`. -/
theorem freeForgetAdjunctionModuleResolutionD1_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    d^⦅0, (0 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk (∑ j, s i j • m i j) := sorry

-- Proof sketch: unfold `s^⦅1, (1 : Fin 2)⦆.app M` to the degree-`1` degeneracy map
-- `iteratedDegeneracyMap ((ModuleCat.adj R).toComonad.toFunctor)
--   ((ModuleCat.adj R).toComonad.δ) 1 1`,
-- which inserts the comultiplication in the outer copy of `R[-]`. On basis elements this wraps
-- one more pair of brackets around the inner linear combination, and linearity extends the formula
-- to the displayed sum.
/-- Example 14.34.6 (3): for the same typical element `ξ`, the degeneracy map `s₀` inserts one
more outer pair of brackets and sends `ξ` to `∑ i, r i • [[∑ j, s i j • [m i j]]]`. -/
theorem freeForgetAdjunctionModuleResolutionS0_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    s^⦅1, (1 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk (ModuleCat.freeMk
          (∑ j, s i j • ModuleCat.freeMk (m i j))) := sorry

-- Proof sketch: unfold `s^⦅1, (0 : Fin 2)⦆.app M` to the degree-`1` degeneracy map
-- `iteratedDegeneracyMap ((ModuleCat.adj R).toComonad.toFunctor)
--   ((ModuleCat.adj R).toComonad.δ) 1 0`,
-- which inserts the comultiplication in the inner copy of `R[-]`. On each basis vector this
-- brackets every `m i j` once more inside the inner linear combination, and linearity gives the
-- displayed formula.
/-- Example 14.34.6 (4): for the same typical element `ξ`, the degeneracy map `s₁` inserts one
more inner pair of brackets and sends `ξ` to `∑ i, r i • [∑ j, s i j • [[m i j]]]`. -/
theorem freeForgetAdjunctionModuleResolutionS1_apply_nested_sum
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (r : ι → R) (s : ι → κ → R) (m : ι → κ → M) :
    s^⦅1, (0 : Fin 2)⦆.app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
        ∑ i, r i • ModuleCat.freeMk
          (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := sorry

end CategoryTheory

/-! ### Example_14_34_7 (from Chap14) -/
open CategoryTheory
open CommRingCat
open Under
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

set_option quotPrecheck false in
local notation "T" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.toFunctor
set_option quotPrecheck false in
local notation "ε" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.ε
set_option quotPrecheck false in
local notation "δ" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.δ
set_option quotPrecheck false in
local notation "Tobj(" B ")" =>
  ((CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.toFunctor).obj B
set_option quotPrecheck false in
local notation "η(" X ")" => ((CommRingCat.adj.comp (Under.costarAdjForget A)).unit).app X
set_option quotPrecheck false in
local notation "ε_(" B ")" => ((CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.ε).app B

/- Domain-style sampling for Example 14.34.7:
- primary domain: the comonad on `Under A` induced by the free `A`-algebra adjunction on
  underlying sets, together with the canonical iterated face/degeneracy maps attached to that
  comonad;
- sampled same-kind declarations:
  `CommRingCat.adj`,
  `Under.costarAdjForget`,
  `iteratedFaceMap`,
  `iteratedDegeneracyMap`,
  `d[Y, d]⦅n, j⦆`,
  `s[Y, s]⦅n, j⦆`;
- best owner abstraction: the canonical owner is the composed adjunction
  `CommRingCat.adj.comp (Under.costarAdjForget A)` and its induced comonad on `Under A`,
  accessed directly through the chapter face/degeneracy owners;
- primitive data: the composed adjunction `CommRingCat.adj.comp (Under.costarAdjForget A)`, its
  left adjoint `CommRingCat.free ⋙ Under.costar A`, and the induced comonad data;
- derived API: the four degree-`1` formulas on the canonical bracket generators supplied by the
  adjunction unit.

Source/core/bridge triage:
- `source-facing`: the bracket-generator formulas for the degree-`1` face and degeneracy maps of
  the polynomial `A`-algebra resolution;
- `core/canonical`: `CommRingCat.free`, `CommRingCat.adj`, `Under.costar`, the composed
  adjunction `CommRingCat.adj.comp (Under.costarAdjForget A)`, its induced comonad owner surface,
  and the chapter owners `iteratedFaceMap` and `iteratedDegeneracyMap`;
- `bridge/view`: the source formulas themselves, obtained by evaluating the canonical unit and
  simplicial operators in the `Under A` realization. -/

-- Proof sketch: unfold `d^⦅0, (1 : Fin 2)⦆.app B`; it is the outer counit map for the comonad
-- on `Under A`, so on the bracket generator `[x] ∈ A[A[B]]` it simply removes the outer bracket.
/-- Example 14.34.7 (1): for `x ∈ A[B]`, the face map `d₀` sends the bracket generator
`[x] ∈ A[A[B]]` to `x`. -/
theorem polynomialAlgebraResolutionD0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      x :=
  sorry

-- Proof sketch: unfold `d^⦅0, (0 : Fin 2)⦆.app B`; it applies the counit to the inner copy
-- before reintroducing the outer bracket via the adjunction unit.
/-- Example 14.34.7 (2): for `x ∈ A[B]`, the face map `d₁` sends `[x]` to `[ε(x)]`. -/
theorem polynomialAlgebraResolutionD1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η(B.right)) ((ε_(B)).right x) :=
  sorry

-- Proof sketch: unfold `s^⦅1, (1 : Fin 2)⦆.app B`; it inserts the comultiplication in the outer
-- copy, so the bracket generator `[x]` becomes the doubly bracketed element `[[x]]`.
/-- Example 14.34.7 (3): for `x ∈ A[B]`, the degeneracy map `s₀` sends `[x]` to `[[x]]`. -/
theorem polynomialAlgebraResolutionS0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right)) (η((Tobj(B)).right) x) :=
  sorry

-- Proof sketch: unfold `s^⦅1, (0 : Fin 2)⦆.app B`; it inserts the comultiplication in the inner
-- copy, which applies the polynomial functor to the bracket map `η.app B.right` before taking one
-- more outer bracket.
/-- Example 14.34.7 (4): for `x ∈ A[B]`, the degeneracy map `s₁` sends `[x]` to `[A[η](x)]`. -/
theorem polynomialAlgebraResolutionS1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right))
        ((((CommRingCat.free ⋙ Under.costar A).map (η(B.right))).right) x) :=
  sorry

end CategoryTheory

/-! ### Example_14_34_8 (from Chap14) -/
open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open CommRingCat
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

/- Domain-style sampling for Example 14.34.8:
- primary domain: simplicial resolutions attached to the free-forgetful adjunctions on
  `Under A` and on `CommRingCat`, together with the explicit `fromZero` sections giving iterated
  bracket inverse maps;
- sampled same-kind owner declarations:
  `polynomialAlgebraAugmentedUnderlyingSet`,
  `prePostcomposeAugmented`,
  `iteratedEndofunctorAugmentation`,
  `SimplicialObject.fromZero`;
- best owner abstraction: the public owners are the augmented resolutions already present upstream
  in the chapter, namely `polynomialAlgebraAugmentedUnderlyingSet A B` and the evaluated
  `commRingFreeForgetSetAugmentedResolution E`; the explicit degree-`0` unit maps and their
  induced `fromZero` morphisms are bridge/view data derived from those owners;
- primitive data vs. derived API:
  primitive data are the upstream augmented owners and the degree-`0` unit-induced section maps;
  derived API is the underlying simplicial object view, the induced iterated-bracket inverse maps,
  and the existence of homotopy equivalences with those specified forward and inverse maps.

Source/core/bridge triage:
- `source-facing`: the augmented simplicial resolutions appearing in Example 14.34.8;
- `core/canonical`: `prePostcomposeAugmented`, `iteratedEndofunctorAugmentation`, and
  `SimplicialObject.Augmented`;
- `bridge/view`: the degree-`0` maps and the induced `fromZero` simplicial morphisms. -/

-- Proof sketch: degree `0` of the augmented Čech nerve of `A[B] ⟶ B` is the source object
-- `A[B]`; forgetting the `A`-algebra structure gives the underlying set of that ring.
/-- The degree-`0` simplicial set of the polynomial resolution is the underlying set of `A[B]`. -/
theorem polynomialAlgebraAugmentedUnderlyingSet_obj_zero_eq (B : Under A) :
    (polynomialAlgebraAugmentedUnderlyingSet A B).left _⦋0⦌ =
      (Under.forget A ⋙ forget CommRingCat).obj ((Under.costar A).obj B.right) := sorry

-- Proof sketch: this is the commutative square expressing that the unit of the adjunction
-- `Under.costarAdjForget A` is a morphism in the under-category of `A`.
private theorem polynomialAlgebraResolutionForgetInverseZeroMap_sq (B : Under A) :
    CommSq B.hom (𝟙 A) ((Under.costarAdjForget A).unit.app B.right)
      ((Under.costar A).obj B.right).hom := by
  sorry

private abbrev polynomialAlgebraResolutionForgetInverseZeroHom (B : Under A) :
    B ⟶ (Under.costar A).obj B.right :=
  Under.homMk
    ((Under.costarAdjForget A).unit.app B.right)
    (polynomialAlgebraResolutionForgetInverseZeroMap_sq A B).w

/-- The degree-`0` iterated-bracket map from the underlying set of `B` into the polynomial
resolution. -/
abbrev polynomialAlgebraResolutionForgetInverseZeroMap (B : Under A) :
    (polynomialAlgebraAugmentedUnderlyingSet A B).right ⟶
      (polynomialAlgebraAugmentedUnderlyingSet A B).left _⦋0⦌ :=
  (Under.forget A ⋙ forget CommRingCat).map
      (polynomialAlgebraResolutionForgetInverseZeroHom A B) ≫
    eqToHom (polynomialAlgebraAugmentedUnderlyingSet_obj_zero_eq A B).symm

/-- The simplicial-set map sending an element `b` to the iterated bracket simplex
`[\ldots [b] \ldots ]` in each degree. -/
abbrev polynomialAlgebraResolutionForgetInverse (B : Under A) :
    (const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right ⟶
      (polynomialAlgebraAugmentedUnderlyingSet A B).left :=
  (polynomialAlgebraAugmentedUnderlyingSet A B).left.fromZero
    (polynomialAlgebraResolutionForgetInverseZeroMap A B)

-- Proof sketch: specialize Lemma 14.34.3 to the adjunction `Under.costarAdjForget A`, then
-- evaluate the resulting statement on the `A`-algebra `B`. This identifies the standard
-- adjunction resolution with the augmented Cech nerve used in Example 14.34.5 and hence with the
-- displayed simplicial ring `A[A[\cdots[A[B]]\cdots]]` after forgetting to sets.
/- Example 14.34.8 (1) reuses the owner-level augmentation theorem from
`Example_14_34_5`. -/
recall polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence

-- Proof sketch: use the explicit section in the proof of Lemma 14.34.3 for the adjunction
-- `Under.costarAdjForget A`. In degree `0` it is the unit map `B → A[B]`, and `fromZero`
-- propagates that section to degree `n` by composing with the unique map `[n] → [0]`, which gives
-- the iterated-bracket formula.
/-- Example 14.34.8 (2): the homotopy inverse for the augmentation in (1) can be chosen to be the
simplicial map whose degree-`n` component sends `b` to the nested bracket simplex
`[\ldots [b] \ldots ]`. -/
theorem polynomialAlgebraResolutionForgetAugmentation_has_iterated_bracket_inverse
    (B : Under A) :
    ∃ e : HomotopyEquiv
        (polynomialAlgebraAugmentedUnderlyingSet A B).left
        ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right),
      e.hom = (polynomialAlgebraAugmentedUnderlyingSet A B).hom ∧
      e.inv = polynomialAlgebraResolutionForgetInverse A B := sorry

/-- The augmented simplicial commutative ring obtained by evaluating the canonical precomposed
free-forgetful adjunction resolution at a set `E`, with augmentation target `A[E]`. -/
abbrev commRingFreeForgetSetAugmentedResolution (E : Type u) :
    SimplicialObject.Augmented CommRingCat :=
  (whiskeringObj (Type u ⥤ CommRingCat) CommRingCat
      ((evaluation (Type u) CommRingCat).obj E)).obj
    (prePostcomposeAugmented free (𝟭 CommRingCat)
      (iteratedEndofunctorAugmentation
        adj.toComonad.ε
        adj.toComonad.δ
        (iteratedEndofunctorResolution_realization
          adj.toComonad.ε
          adj.toComonad.δ
          (adjunction_iteratedEndofunctor_hσδ₀ adj)
          (adjunction_iteratedEndofunctor_hσδ₁ adj)
          (adjunction_iteratedEndofunctor_hσσ adj))))

/-- The underlying simplicial commutative ring of
`commRingFreeForgetSetAugmentedResolution E`; its degree-`0` term is `A[A[E]]`, and it augments
to `A[E]`. -/
abbrev commRingFreeForgetSetResolution (E : Type u) : SimplicialObject CommRingCat :=
  (commRingFreeForgetSetAugmentedResolution E).left

-- Proof sketch: in degree `0`, the precomposed standard resolution applies `CommRingCat.free` to
-- the underlying set of `A[E]`, giving `A[A[E]]`.
/-- The degree-`0` simplicial ring of the free-forgetful resolution on `E` is `A[A[E]]`. -/
theorem commRingFreeForgetSetResolution_obj_zero_eq (E : Type u) :
    (commRingFreeForgetSetResolution E) _⦋0⦌ =
      free.obj ((forget CommRingCat).obj (free.obj E)) := sorry

/-- The degree-`0` iterated-bracket map `A[E] → A[A[E]]` coming from the unit of the
free-forgetful adjunction. -/
abbrev commRingFreeForgetSetInverseZeroMap (E : Type u) :
    free.obj E ⟶ (commRingFreeForgetSetResolution E) _⦋0⦌ :=
  free.map (adj.unit.app E) ≫
    eqToHom (commRingFreeForgetSetResolution_obj_zero_eq E).symm

/-- The simplicial ring map whose degree-`n` component brackets each generator one more time. -/
abbrev commRingFreeForgetSetInverse (E : Type u) :
    (const CommRingCat).obj (free.obj E) ⟶
      commRingFreeForgetSetResolution E :=
  (commRingFreeForgetSetResolution E).fromZero
    (commRingFreeForgetSetInverseZeroMap E)

-- Proof sketch: apply the precomposition half of Lemma 14.34.3 to the free-forgetful adjunction
-- `CommRingCat.adj`, then evaluate the resulting simplicial homotopy equivalence at the set `E`.
/-- Example 14.34.8 (3): for every set `E`, the simplicial commutative ring built from the
free-forgetful adjunction on `E` is simplicially homotopy equivalent to the constant simplicial
ring on `A[E]`. -/
theorem commRingFreeForgetSetResolutionAugmentation_isHomotopyEquivalence
    (E : Type u) :
    IsHomotopyEquivalence
      (commRingFreeForgetSetAugmentedResolution E).hom := sorry

-- Proof sketch: in the proof of Lemma 14.34.3, the degree-`0` section is obtained by applying the
-- free functor to the unit map `E → A[E]`. The associated `fromZero` morphism therefore sends a
-- polynomial `∑ a_{e₁,\ldots,e_p}[e₁]\cdots[e_p]` to the same coefficient sum with every generator
-- replaced by its iterated bracket in the target degree.
/-- Example 14.34.8 (4): the homotopy inverse in (3) can be chosen so that in degree `n` it sends
`∑ a_{e₁,\ldots,e_p}[e₁]\cdots[e_p]` to the corresponding sum with each generator replaced by its
nested bracket `[\ldots [e_i] \ldots ]`. -/
theorem commRingFreeForgetSetResolutionAugmentation_has_iterated_bracket_inverse
    (E : Type u) :
    ∃ e : HomotopyEquiv
        (commRingFreeForgetSetResolution E)
        ((const CommRingCat).obj (free.obj E)),
      e.hom = (commRingFreeForgetSetAugmentedResolution E).hom ∧
      e.inv = commRingFreeForgetSetInverse E := sorry

end CategoryTheory
