import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_28_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ C) (G : C ⥤ D) (adj : F ⊣ G)

/-- The object property on the target category consisting of those objects for which the adjunction
unit `K ⟶ GF(K)` is an isomorphism. -/
abbrev unitIsomorphismProperty : ObjectProperty D :=
  fun K ↦ IsIso (adj.unit.app K)

-- Proof sketch: unfold `unitIsomorphismProperty`; membership is by definition that the chosen
-- adjunction unit `K ⟶ GF(K)` is an isomorphism.
/-- Membership in `unitIsomorphismProperty` means exactly that the adjunction unit
`K ⟶ GF(K)` is an isomorphism. -/
theorem mem_unitIsomorphismProperty_iff (K : D) :
    unitIsomorphismProperty F G adj K ↔ IsIso (adj.unit.app K) := sorry

/-- The full subcategory cut out by the unit-isomorphism condition `K ⟶ GF(K)`. -/
abbrev unitIsomorphismSubcategory :=
  (unitIsomorphismProperty F G adj).FullSubcategory

/-- The restriction of the left adjoint to the full subcategory on which the adjunction unit is an
isomorphism. -/
abbrev restrictedLeftAdjoint :
    unitIsomorphismSubcategory F G adj ⥤ C :=
  (unitIsomorphismProperty F G adj).ι ⋙ F

-- Proof sketch: the Stacks notion of “saturated” is retract-closure. If `K` is a retract of `L`
-- and the unit for `L` is an isomorphism, naturality of the adjunction unit shows that the unit
-- for `K` is a retract of an isomorphism, hence an isomorphism.
/-- Lemma 21.28.1 (1): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism form a saturated
subcategory, i.e. an object property stable under retracts. -/
theorem unitIsomorphismProperty_isStableUnderRetracts :
    (unitIsomorphismProperty F G adj).IsStableUnderRetracts := sorry

-- Proof sketch: for objects `K` and `L` in the unit-isomorphism subcategory, the adjunction gives
-- `Hom(FK, FL) ≃ Hom(K, GFL)`. Since the unit `L ⟶ GFL` is an isomorphism, composition with it
-- identifies the right-hand side with `Hom(K, L)`, giving bijectivity on homs.
/-- Lemma 21.28.1 (3): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the restriction of the left adjoint to the full subcategory of objects satisfying
`K ⟶ GF(K)` is fully faithful. -/
theorem restrictedLeftAdjoint_bijective_on_homs
    (K L : unitIsomorphismSubcategory F G adj) :
    Function.Bijective
      ((restrictedLeftAdjoint F G adj).map :
        (K ⟶ L) → (F.obj K.obj ⟶ F.obj L.obj)) := sorry

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
variable [Pretriangulated C] [Pretriangulated D]
variable (F : D ⥤ C) (G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
variable (adj : F ⊣ G) [adj.IsTriangulated]

-- Proof sketch: `F` and `G` are exact functors of triangulated categories, so the unit natural
-- transformation is compatible with distinguished triangles and shifts. Applying the
-- two-out-of-three formalism to the unit maps shows that the unit-isomorphism condition is
-- triangulated; the associated full subcategory is therefore strictly full.
/-- Lemma 21.28.1 (2): in the abstract triangulated adjunction `F ⊣ G` underlying the
ringed-topos situation, the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism
form a triangulated strictly full subcategory of the target category. -/
theorem unitIsomorphismProperty_isTriangulated :
    (unitIsomorphismProperty F G adj).IsTriangulated := sorry

end

end CategoryTheory

/-! ### Lemma_21_28_2 (from Chap21) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

/-- The object property on `D(\mathcal O_X)` cut out by the counit-isomorphism condition
`Lf^* Rf_* K ⟶ K`. -/
abbrev modulePullbackPushforwardCounitIsoProperty
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f) :
    ObjectProperty (ModuleDerived X) :=
  fun K ↦ IsIso (adj.counit.app K)

-- Proof sketch: the counit is a natural transformation, so for any isomorphism `K ≅ L` the two
-- counit components are conjugate. Hence invertibility of `Lf^* Rf_* K ⟶ K` is invariant under
-- isomorphism.
/-- Lemma 21.28.2 (1): the full subcategory of `D(\mathcal O_\mathcal C)` defined by the condition
that `Lf^* Rf_* K ⟶ K` is an isomorphism is strictly full. -/
instance modulePullbackPushforwardCounitIsoProperty_isClosedUnderIsomorphisms :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsClosedUnderIsomorphisms := sorry

-- Proof sketch: if `K` is a retract of `L`, then naturality of the counit makes
-- `Lf^* Rf_* K ⟶ K` a retract of `Lf^* Rf_* L ⟶ L`. Retracts of isomorphisms are isomorphisms, so
-- the defining property is stable under retracts/direct summands.
/-- Lemma 21.28.2 (2): the full subcategory of `D(\mathcal O_\mathcal C)` defined by the counit
isomorphism condition is saturated, i.e. stable under retracts. -/
instance modulePullbackPushforwardCounitIsoProperty_isStableUnderRetracts :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsStableUnderRetracts := sorry

/-- The counit-isomorphism condition defines a triangulated object property on
`D(\mathcal O_X)`. -/
instance modulePullbackPushforwardCounitIsoProperty_isTriangulated :
    (modulePullbackPushforwardCounitIsoProperty f adj).IsTriangulated := sorry

-- Proof sketch: the counit `Lf^* Rf_* ⟶ 𝟭` is a natural transformation between exact functors on
-- the derived category. The full subcategory where this natural transformation is an isomorphism
-- is therefore closed under shifts and distinguished triangles, and the previous two clauses give
-- strict fullness and saturation.
/-- Lemma 21.28.2 (3): the full subcategory of `D(\mathcal O_\mathcal C)` on objects `K` for which
`Lf^* Rf_* K ⟶ K` is an isomorphism is a triangulated subcategory. -/
theorem modulePullbackPushforwardCounitSubcategory_isTriangulated :
    CategoryTheory.IsTriangulated
      (modulePullbackPushforwardCounitIsoProperty f adj).FullSubcategory := sorry

-- Proof sketch: restrict the adjunction `Lf^* ⊣ Rf_*` along the full subcategory cut out by the
-- counit-isomorphism condition. On that restricted domain, every counit component is an
-- isomorphism by definition, so the standard adjunction criterion implies that the restricted
-- right adjoint `Rf_*` is fully faithful.
/-- Lemma 21.28.2 (4): the restriction of `Rf_*` to the full subcategory where
`Lf^* Rf_* K ⟶ K` is an isomorphism is fully faithful. -/
theorem modulePushforwardDerived_restriction_full_faithful :
    (((modulePullbackPushforwardCounitIsoProperty f adj).ι) ⋙
      modulePushforwardDerived f).Full ∧
      (((modulePullbackPushforwardCounitIsoProperty f adj).ι) ⋙
        modulePushforwardDerived f).Faithful :=
  sorry

end

end RingedSite.Hom

/-! ### Lemma_21_28_3 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- The bounded-below condition on an object of a derived category. -/
def DerivedCategoryIsBoundedBelow (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((DerivedCategory.homologyFunctor A i).obj K)

/-- The degree-zero derived object attached to the `q`-th cohomology object of `K`. -/
abbrev cohomologyObjectAsDerived (K : DerivedCategory A) (q : ℤ) :
    DerivedCategory A :=
  (DerivedCategory.singleFunctor A (0 : ℤ)).obj
    ((DerivedCategory.homologyFunctor A q).obj K)

variable (F : DerivedCategory B ⥤ DerivedCategory A)
variable (G : DerivedCategory A ⥤ DerivedCategory B)
variable (adj : F ⊣ G)

-- Proof sketch: let `D'` be the triangulated subcategory from Lemma `21.28.2` cut out by the
-- counit-isomorphism condition. The hypothesis says that each cohomology object `H^q(K)[0]`
-- lies in this subcategory. Using bounded-belowness, rebuild bounded truncations of `K` from
-- these cohomology objects through the standard distinguished triangles; closure under shifts
-- and triangles then implies every truncation, and hence `K` itself, lies in the same
-- subcategory.
/-- Lemma 21.28.3: if `K ∈ D(\mathcal O_{\mathcal C})` is bounded below and every degree-zero
derived object attached to a cohomology sheaf `H^q(K)` satisfies the counit isomorphism
condition for an adjunction `F ⊣ G` on derived categories, then `K` itself satisfies that
condition. Applied to `F = Lf^*` and `G = Rf_*`, this is the canonical derived-category form of
the Stacks statement that, for a flat morphism of ringed topoi, if every
`f^* Rf_* H^q(K) ⟶ H^q(K)` is an isomorphism, then so is `Lf^* Rf_* K ⟶ K`. -/
theorem counit_isIso_of_boundedBelow_of_cohomology
    (K : DerivedCategory A)
    (hK : DerivedCategoryIsBoundedBelow K)
    (hH : ∀ q : ℤ, IsIso (adj.counit.app (cohomologyObjectAsDerived K q))) :
    IsIso (adj.counit.app K) := sorry

end

end CategoryTheory

/-! ### Lemma_21_28_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The exact-functor package on module sheaves attached to pullback along a flat morphism of
ringed sites. -/
noncomputable abbrev modulePullbackExactFunctor : ModuleCat Y ⥤ₑ ModuleCat X :=
  let _ : PreservesFiniteLimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).1
  let _ : PreservesFiniteColimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).2
  ExactFunctor.of f.modulePullback

/-- The pullback functor on derived categories induced by the exact pullback on module sheaves for
a flat morphism of ringed sites. -/
noncomputable abbrev modulePullbackDerivedOfFlat : ModuleDerived Y ⥤ ModuleDerived X :=
  let _ : (modulePullbackExactFunctor f).obj.Additive :=
    (inferInstance : f.modulePullback.Additive)
  (modulePullbackExactFunctor f).obj.mapDerivedCategory

local notation "fStarDerived" => modulePullbackDerivedOfFlat f

-- Proof sketch: let `D'` be the full triangulated subcategory of `D(\mathcal O_Y)` on objects for
-- which the adjunction unit is an isomorphism. Each cohomology sheaf `H^q(K)[0]` lies in `D'` by
-- hypothesis, and bounded-below truncation induction then shows that the bounded-below object `K`
-- itself lies in `D'`.
/-- Lemma 21.28.4: for a flat morphism of ringed topoi formalized by a flat morphism of ringed
sites `f`, if a derived `\mathcal O_\mathcal D`-module `K` is bounded below and the adjunction
unit is an isomorphism on every cohomology sheaf `H^q(K)[0]`, then the unit
`K ⟶ Rf_* f^* K` is an isomorphism. In this library-facing formulation, `f^*` is the exact
pullback functor on the derived category induced by flatness. -/
theorem unit_isIso_of_boundedBelow_of_cohomologySheaf_unit_isIso
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (K : ModuleDerived Y)
    (hbounded : ∃ n : ℤ, K.IsGE n)
    (hcohom : ∀ q : ℤ,
      IsIso
        (adj.unit.app
          ((DerivedCategory.singleFunctor (ModuleCat Y) (0 : ℤ)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Y) q).obj K)))) :
    IsIso (adj.unit.app K) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_28_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A' : ObjectProperty (ModuleCat Y)) (A : ObjectProperty (ModuleCat X))
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A']
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A]

/-- The object property on `D(\mathcal O_Z)` consisting of those complexes whose cohomology
sheaves lie in the chosen subcategory `B`. -/
abbrev moduleDerivedCohomologyInProperty
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :
    ObjectProperty (ModuleDerived Z) :=
  fun K ↦ ∀ n : ℤ, B ((DerivedCategory.homologyFunctor (ModuleCat Z) n).obj K)

/-- The object property on `D(\mathcal O_Z)` consisting of bounded-below complexes whose
cohomology sheaves lie in `B`. -/
abbrev moduleDerivedBoundedBelowCohomologyInProperty
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :
    ObjectProperty (ModuleDerived Z) :=
  fun K ↦ moduleDerivedCohomologyInProperty Z B K ∧ ∃ n : ℤ, K.IsGE n

/-- The bounded-below derived full subcategory on `Z` cut out by the cohomology condition `B`. -/
abbrev ModuleDerivedPlusWithCohomologyIn
    (Z : RingedSite.{u, v}) (B : ObjectProperty (ModuleCat Z)) :=
  (moduleDerivedBoundedBelowCohomologyInProperty Z B).FullSubcategory

local notation "DplusY" => ModuleDerivedPlusWithCohomologyIn Y A'
local notation "DplusX" => ModuleDerivedPlusWithCohomologyIn X A
local notation "PplusY" => moduleDerivedBoundedBelowCohomologyInProperty Y A'
local notation "PplusX" => moduleDerivedBoundedBelowCohomologyInProperty X A

/-- The exact-functor package on module sheaves attached to pullback along a flat morphism of
ringed sites. -/
noncomputable abbrev flatModulePullbackExactFunctor : ModuleCat Y ⥤ₑ ModuleCat X :=
  let _ : CategoryTheory.Limits.PreservesFiniteLimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits f.modulePullback :=
    ((CategoryTheory.exactFunctor_iff f.modulePullback).mp
      IsFlat.pullback_exact).2
  ExactFunctor.of f.modulePullback

/-- The pullback functor on derived categories induced by the exact pullback on module sheaves for
a flat morphism of ringed sites. -/
noncomputable abbrev flatModulePullbackDerived : ModuleDerived Y ⥤ ModuleDerived X :=
  let _ : (flatModulePullbackExactFunctor f).obj.Additive :=
    (inferInstance : f.modulePullback.Additive)
  (flatModulePullbackExactFunctor f).obj.mapDerivedCategory

local notation "fStarDerived" => flatModulePullbackDerived f

/-- A module sheaf on a ringed site, viewed as a derived object concentrated in degree `0`. -/
abbrev moduleObjectAsDerived (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- The pullback functor on weak LinearRepresentations_Serre_1977 subcategories induced by pullback on module sheaves. -/
abbrev modulePullbackOnWeakSerreSubcategory
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: bounded-belowness is preserved by the exact derived pullback attached to a flat
-- morphism, and exactness identifies the cohomology sheaves of `f^* K` with the pullbacks of the
-- cohomology sheaves of `K`. The hypothesis `hpull_mem` then shows that these cohomology sheaves
-- lie in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends `D^+_{A'}(\mathcal O_Y)` to
`D^+_A(\mathcal O_X)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) (K : DplusY) :
    PplusX ((ObjectProperty.ι PplusY ⋙ fStarDerived).obj K) := sorry

/-- The pullback functor on bounded-below derived categories with cohomology in the chosen weak
LinearRepresentations_Serre_1977 subcategories. -/
abbrev modulePullbackDerivedOfFlatPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DplusY ⥤ DplusX :=
  ObjectProperty.lift PplusX
    (ObjectProperty.ι PplusY ⋙ fStarDerived)
    (modulePullbackDerivedOfFlat_obj_mem_derivedCategoryPlusWithCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: by essential surjectivity of `f^* : A'.FullSubcategory ⥤ A.FullSubcategory`,
-- every cohomology sheaf of `K ∈ D^+_A(\mathcal O_X)` is isomorphic to `f^* ℱ'` for some
-- `ℱ' ∈ A'`. The unit hypothesis identifies `ℱ'` with `Rf_* f^* ℱ'`, forcing the higher direct
-- images of `f^* ℱ'` to vanish and the degree-zero direct image to lie in `A'`. The spectral
-- sequence `R^p f_* H^q(K) ⇒ H^{p+q}(Rf_* K)` then shows that `Rf_* K` is bounded below and all of
-- its cohomology sheaves lie in `A'`.
/-- Under the hypotheses of Lemma `21.28.5`, the right derived pushforward sends
`D^+_A(\mathcal O_X)` to `D^+_{A'}(\mathcal O_Y)`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj)))
    (K : DplusX) :
    PplusY ((ObjectProperty.ι PplusX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The right derived pushforward restricted to the bounded-below derived subcategory with
cohomology in `A`. In Lemma `21.28.5`, this is the quasi-inverse to the restricted pullback
functor. -/
abbrev modulePushforwardDerivedPlusWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    DplusX ⥤ DplusY :=
  ObjectProperty.lift PplusY
    (ObjectProperty.ι PplusX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryPlusWithCohomologyIn
      f A' A hpull_mem adj hunit)

-- Proof sketch: Lemma `21.28.4` upgrades the unit-isomorphism hypothesis from degree-zero objects
-- `ℱ'[0]` with `ℱ' ∈ A'` to every bounded-below object of `D^+_{A'}(\mathcal O_Y)`, giving full
-- faithfulness of the restricted pullback. The previous helper theorem shows that the restricted
-- pushforward lands in `D^+_{A'}(\mathcal O_Y)`, and Lemmas `21.28.2`, `21.28.3`, and `4.24.4`
-- then identify it as the quasi-inverse.
/-- Lemma 21.28.5: let `f : X ⟶ Y` be a flat morphism of ringed sites, let
`A' ⊆ \operatorname{Mod}(\mathcal O_Y)` and `A ⊆ \operatorname{Mod}(\mathcal O_X)` be weak LinearRepresentations_Serre_1977
subcategories, assume pullback induces an equivalence `A' ≌ A`, and assume the adjunction unit
`ℱ'[0] ⟶ Rf_* f^*(ℱ'[0])` is an isomorphism for every `ℱ' ∈ A'`. Then the induced pullback functor
`f^* : D^+_{A'}(\mathcal O_Y) ⥤ D^+_A(\mathcal O_X)` is an equivalence of categories. The
restricted right derived pushforward defined below is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to Lemma `21.28.5`. -/
noncomputable instance instModulePullbackDerivedOfFlatPlusWithCohomologyInIsEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModuleCat Y⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (adj : fStarDerived ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatPlusWithCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatPlusWithCohomologyIn_isEquivalence f A' A hpull_mem adj hunit

end

end RingedSite.Hom

/-! ### Lemma_21_28_6 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A']
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A]

local notation "PX" => moduleDerivedCohomologyInProperty (X := X) A
local notation "PY" => moduleDerivedCohomologyInProperty (X := Y) A'
local notation "DX" => moduleDerivedWithCohomologyIn (X := X) A
local notation "DY" => moduleDerivedWithCohomologyIn (X := Y) A'

/-- A module sheaf on a ringed site, viewed as a derived object concentrated in degree `0`. -/
abbrev moduleObjectAsDerived (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- Pullback on module sheaves induces a functor between the weak LinearRepresentations_Serre_1977 full subcategories cut out
by `A'` and `A`. -/
abbrev modulePullbackOnWeakSerreSubcategory
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: pullback along a flat morphism is exact, so on the derived category it commutes
-- with cohomology objects. If every cohomology sheaf of `K` lies in `A'`, then the hypothesis
-- `hpull_mem` implies every cohomology sheaf of `f^* K` lies in `A`.
/-- Exact pullback along a flat morphism of ringed sites sends
`D_{\mathcal A'}(\mathcal O_Y)` to `D_\mathcal A(\mathcal O_X)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_derivedCategoryWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    (K : DY) :
    PX ((ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f).obj K) := sorry

/-- The pullback functor on unbounded derived categories with cohomology in the chosen weak LinearRepresentations_Serre_1977
subcategories. -/
abbrev modulePullbackDerivedOfFlatWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DY ⥤ DX :=
  ObjectProperty.lift PX
    (ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f)
    (modulePullbackDerivedOfFlat_obj_mem_derivedCategoryWithCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: first use the equivalence on `A'` together with the unit-isomorphism hypothesis
-- to obtain the degree-zero pushforward statements `R^0 f_* (f^* \mathcal F') ∈ A'` and
-- `R^p f_* (f^* \mathcal F') = 0` for `p > 0`. Essential surjectivity of pullback on `A'`
-- transfers these bounds to arbitrary objects of `A`. Then Lemma `21.25.4` with `N = 0`,
-- combined with the bounded-cohomology-basis hypotheses on `X` and `Y`, shows that `Rf_*`
-- carries every object of `D_\mathcal A(\mathcal O_X)` into `D_{\mathcal A'}(\mathcal O_Y)`.
/-- The right derived pushforward restricted to the full subcategory with cohomology in
`\mathcal A`. This is the candidate quasi-inverse in Lemma `21.28.6`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj)))
    (K : DX) :
    PY ((ObjectProperty.ι PX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The right derived pushforward on the unbounded derived subcategory with cohomology in
`\mathcal A`. In Lemma `21.28.6` this is the quasi-inverse to the restricted pullback functor. -/
abbrev modulePushforwardDerivedWithCohomologyIn
    (_hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A _hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (_basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    DX ⥤ DY :=
  ObjectProperty.lift PY
    (ObjectProperty.ι PX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn
      f A' A _hpull_mem _basisX _basisY adj _hunit)

-- Proof sketch: exact pullback commutes with the truncation functors `τ_{\ge -n}`, so the
-- restricted pullback on `D_{\mathcal A'}` and the restricted pushforward on `D_\mathcal A`
-- are compatible with truncations. Lemma `21.28.5` identifies these truncations as quasi-inverse
-- equivalences on the bounded-below subcategories, while Lemma `21.25.6` gives the truncation
-- control for `Rf_*` on unbounded objects. Passing to the limit over truncations shows that both
-- the unit `K' ⟶ Rf_* f^* K'` and the counit `f^* Rf_* K ⟶ K` are isomorphisms on the unbounded
-- derived subcategories, hence the restricted pullback is an equivalence with quasi-inverse the
-- restricted `Rf_*`.
/-- Lemma 21.28.6: let `f : X ⟶ Y` be a flat morphism of ringed topoi formalized by a flat
morphism of ringed sites, let `\mathcal A \subset \operatorname{Mod}(\mathcal O_X)` and
`\mathcal A' \subset \operatorname{Mod}(\mathcal O_Y)` be weak LinearRepresentations_Serre_1977 subcategories, assume that
pullback induces an equivalence `\mathcal A' \simeq \mathcal A`, assume
`\mathcal F' \to Rf_* f^* \mathcal F'` is an isomorphism for every
`\mathcal F' \in \operatorname{Ob}(\mathcal A')`, and assume both
`(X, \mathcal O_X, \mathcal A)` and `(Y, \mathcal O_Y, \mathcal A')` satisfy Situation
`21.25.1`. Then the induced exact pullback functor
`f^* : D_{\mathcal A'}(\mathcal O_Y) \to D_\mathcal A(\mathcal O_X)` is an equivalence of
categories. The restricted right derived pushforward defined above is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to the restricted pullback functor of Lemma `21.28.6`. -/
noncomputable instance instModulePullbackDerivedOfFlatWithCohomologyInIsEquivalence
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence (modulePullbackOnWeakSerreSubcategory f A' A hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis X.structureSheaf A)
    (_basisY : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis Y.structureSheaf A')
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerived Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatWithCohomologyIn_isEquivalence
    f A' A hpull_mem _basisX _basisY adj _hunit

end

end RingedSite.Hom

/-! ### Lemma_21_28_7 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [HasSheafify Y.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat)]

variable [Abelian ModX] [Abelian ModY]
variable [f.IsFlat]
variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable (A' : ObjectProperty ModY) (A : ObjectProperty ModX)
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A']
variable [_root_.CategoryTheory.ObjectProperty.IsWeakSerreClass A]

local notation "PX" => moduleDerivedCohomologyInProperty (X := X) A
local notation "PY" => moduleDerivedCohomologyInProperty (X := Y) A'
local notation "DX" => moduleDerivedWithCohomologyIn (X := X) A
local notation "DY" => moduleDerivedWithCohomologyIn (X := Y) A'

/-- A module sheaf on a ringed site, viewed as a derived object concentrated in degree `0`. -/
abbrev moduleObjectAsDerivedDegreeZero (Z : RingedSite.{u, v}) (ℱ : ModuleCat Z) :
    ModuleDerived Z :=
  (DerivedCategory.singleFunctor (ModuleCat Z) (0 : ℤ)).obj ℱ

/-- Pullback on module sheaves induces a functor between the weak LinearRepresentations_Serre_1977 full subcategories cut out
by `A'` and `A`. -/
abbrev modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.lift A (A'.ι ⋙ f.modulePullback) (fun ℱ' ↦ hpull_mem ℱ'.property)

-- Proof sketch: pullback along a flat morphism is exact, so it commutes with cohomology objects on
-- the derived category. The hypothesis `hpull_mem` then transports membership in `A'` of each
-- cohomology sheaf of `K` to membership in `A` of the corresponding cohomology sheaf of `f^* K`.
/-- Exact pullback along a flat morphism of ringed sites sends
`D_{\mathcal A'}(\mathcal O')` to `D_\mathcal A(\mathcal O)`. -/
theorem modulePullbackDerivedOfFlat_obj_mem_weakSerreCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    (K : DY) :
    PX ((ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f).obj K) := sorry

/-- The pullback functor on the unbounded derived subcategories cut out by the weak LinearRepresentations_Serre_1977
cohomology conditions. -/
abbrev modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ')) :
    DY ⥤ DX :=
  ObjectProperty.lift PX
    (ObjectProperty.ι PY ⋙ modulePullbackDerivedOfFlat f)
    (modulePullbackDerivedOfFlat_obj_mem_weakSerreCohomologyIn
      f A' A hpull_mem)

-- Proof sketch: use the equivalence on `A'` together with the unit-isomorphism hypothesis to
-- identify the higher direct images of objects of `A` with the corresponding vanishing and
-- degree-zero statements transported from `A'`. Apply the source-side bounded-cohomology basis and
-- the along-`f` bounded-cohomology basis from Situation `21.25.5` through Lemma `21.25.6` to pass
-- from bounded-below truncations to arbitrary unbounded objects, and conclude that `Rf_* K` has
-- all cohomology sheaves in `A'`.
/-- Under the hypotheses of Lemma `21.28.7`, the right derived pushforward sends
`D_\mathcal A(\mathcal O)` to `D_{\mathcal A'}(\mathcal O')`. -/
theorem modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_local_bounded_cohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj)))
    (K : DX) :
    PY ((ObjectProperty.ι PX ⋙ modulePushforwardDerived f).obj K) := sorry

/-- The restricted right derived pushforward used as the quasi-inverse in Lemma `21.28.7`. -/
abbrev modulePushforwardDerivedWithCohomologyInOfLocalBoundedCohomology
    (_hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A _hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (_basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    DX ⥤ DY :=
  ObjectProperty.lift PY
    (ObjectProperty.ι PX ⋙ modulePushforwardDerived f)
    (modulePushforwardDerived_obj_mem_derivedCategoryWithCohomologyIn_of_local_bounded_cohomology
      f A' A _hpull_mem _basisX _basisf adj _hunit)

-- Proof sketch: the bounded-below equivalence from Lemma `21.28.5` controls every truncation
-- `τ_{\ge -n} K`, while Lemma `21.25.6` gives the comparison isomorphisms
-- `H^j(Rf_* K) → H^j(Rf_*(τ_{\ge -n} K))` under the Situation `21.25.1` and `21.25.5`
-- hypotheses. Passing to the limit over truncations upgrades the bounded-below unit and counit
-- isomorphisms to all objects of the unbounded derived subcategories, so the restricted pullback
-- is an equivalence with quasi-inverse the restricted `Rf_*`.
/-- Lemma 21.28.7: let `f : (\mathcal C, \mathcal O) \to (\mathcal C', \mathcal O')` be a
morphism of ringed sites, let `\mathcal A \subset \operatorname{Mod}(\mathcal O)` and
`\mathcal A' \subset \operatorname{Mod}(\mathcal O')` be weak LinearRepresentations_Serre_1977 subcategories, assume `f` is
flat, assume `f^* : \mathcal A' \to \mathcal A` is an equivalence, assume
`\mathcal F' \to Rf_* f^* \mathcal F'` is an isomorphism for `\mathcal F' \in \operatorname{Ob}
(\mathcal A')`, assume `(\mathcal C, \mathcal O, \mathcal A)` satisfies Situation `21.25.1`, and
assume `f` and `\mathcal A` satisfy Situation `21.25.5`. Then
`f^* : D_{\mathcal A'}(\mathcal O') \to D_\mathcal A(\mathcal O)` is an equivalence of
categories. The restricted right derived pushforward defined above is the intended quasi-inverse. -/
theorem modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn_isEquivalence_of_local_bounded_cohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn f A' A hpull_mem) := sorry

/-- The equivalence instance attached to the restricted pullback functor of Lemma `21.28.7`. -/
noncomputable instance
    instModulePullbackDerivedOfFlatWithWeakSerreCohomologyInIsEquivalenceOfLocalBoundedCohomology
    (hpull_mem : ∀ ⦃ℱ' : ModY⦄, A' ℱ' → A (f.modulePullback.obj ℱ'))
    [Functor.IsEquivalence
      (modulePullbackOnWeakSerreSubcategoryForDerivedCohomologyIn f A' A hpull_mem)]
    (_basisX : CategoryTheory.GrothendieckTopology.bounded_cohomology_basis
      X.structureSheaf A)
    (_basisf : bounded_cohomology_basis f A)
    (adj : modulePullbackDerivedOfFlat f ⊣ modulePushforwardDerived f)
    (_hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app (moduleObjectAsDerivedDegreeZero Y ℱ'.obj))) :
    Functor.IsEquivalence
      (modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn f A' A hpull_mem) :=
  modulePullbackDerivedOfFlatWithWeakSerreCohomologyIn_isEquivalence_of_local_bounded_cohomology
    f A' A hpull_mem _basisX _basisf adj _hunit

end

end RingedSite.Hom
