import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂ u₁ u₂
universe u v

namespace CategoryTheory

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
local notation "H" => DerivedCategory.homologyFunctor A
local notation "single0" => DerivedCategory.singleFunctor A (0 : ℤ)

variable (F : DerivedCategory B ⥤ DerivedCategory A)
variable (G : DerivedCategory A ⥤ DerivedCategory B)
variable (adj : F ⊣ G)
local notation "P" => counitIsomorphismProperty F G adj
variable [F.CommShift ℤ] [F.IsTriangulated]

/- Domain-style sampling for the abstract form of Lemma 21.28.3:
- primary domain: counit-isomorphism object properties for adjunctions on derived categories;
- sampled owner declarations:
  `counitIsomorphismProperty`,
  `restrictedRightAdjoint_fullyFaithful`,
  `counitIsomorphismProperty_isTriangulated`;
- best owner abstraction:
  `source-facing`: the bounded-below cohomological detection criterion below;
  `core/canonical`: the object property `P`;
  `bridge/view`: the underlying counit-isomorphism statement `IsIso (adj.counit.app _)`.

Primitive data are the adjunction `F ⊣ G`, the exact/triangulated structure on the left adjoint
encoded by `[F.CommShift ℤ] [F.IsTriangulated]`, the bounded-below object `K`, and the cohomology
objects `H^q(K)[0]`. The raw isomorphism statement is already packaged canonically by `P`, so the
theorem below should use that owner predicate directly rather than restating its defining field.
-/

-- Proof sketch: let `D'` be the triangulated subcategory from Lemma `21.28.2` cut out by the
-- counit-isomorphism condition. The hypothesis says that each cohomology object `H^q(K)[0]`
-- lies in this subcategory. Using bounded-belowness, rebuild bounded truncations of `K` from
-- these cohomology objects through the standard distinguished triangles; closure under shifts
-- and triangles then implies every truncation, and hence `K` itself, lies in the same
-- subcategory.
/-- Lemma 21.28.3, owner form: if `K` is bounded below and every
degree-zero derived object attached to a cohomology sheaf `H^q(K)` lies in the canonical
counit-isomorphism property for an adjunction `F ⊣ G` on derived categories, then `K` itself lies
in that property. Applied to `F = Lf^*` and `G = Rf_*`, this is the derived-category form of the
Stacks statement that if every `f^* Rf_* H^q(K) ⟶ H^q(K)` is an isomorphism, then so is
`Lf^* Rf_* K ⟶ K`. -/
@[stacks 0D7S]
theorem counitIsomorphismProperty_of_boundedBelow_of_cohomology
    (K : DerivedCategory A)
    (hbounded : ∃ n : ℤ, K.IsGE n)
    (hcohom : ∀ q : ℤ, P ((single0).obj ((H q).obj K))) :
    P K := sorry

end

end CategoryTheory

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [f.modulePushforward.Additive]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(f^*).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Fact (IsFlat f)]
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat X) (0 : ℤ)
local notation:max "H^" q:max => DerivedCategory.homologyFunctor (ModuleCat X) q
local notation "LfStar" => modulePullbackDerived f
local notation "RfStar" => modulePushforwardDerived f

/- Domain-style sampling for Lemma 21.28.3:
- primary domain: flat pullback/right-derived-pushforward adjunctions on derived categories of
  module sheaves over ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePushforwardDerived`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `CategoryTheory.counitIsomorphismProperty_of_boundedBelow_of_cohomology`;
- best owner abstraction:
  `source-facing`: the flat ringed-site specialization of the counit-isomorphism criterion;
  `core/canonical`: the Chapter 21 owners `modulePullbackDerived f`,
    `modulePushforwardDerived f`, and
    `modulePullbackDerived_pushforward_adjunction f`, together with the generic theorem
    `CategoryTheory.counitIsomorphismProperty_of_boundedBelow_of_cohomology`;
  `bridge/view`: the source-facing `IsIso` statement below as a thin bridge from the canonical
    object property to the explicit counit map.

Primitive data are the flat morphism `f`, the chosen adjunction `Lf^* ⊣ Rf_*`, the bounded-below
derived object `K`, and the degree-zero counit-isomorphism hypotheses on its cohomology sheaves.
The theorem below is therefore a source-facing specialization of the generic counit-isomorphism
property theorem, not a new owner declaration.
-/

-- Proof sketch: flatness makes `f^*` exact, so its action on derived categories is the canonical
-- exact-functor owner `(f^*).mapDerivedCategory`. The right adjoint is the canonical total right
-- derived functor `Rf_*` of `pushforward f`. Apply the generic counit-isomorphism criterion to
-- this adjunction.
/-- Owner-form companion to Lemma 21.28.3: under the flat derived adjunction `Lf^* ⊣ Rf_*`, a
bounded-below object `K` lies in the counit-isomorphism property as soon as each single-cohomology
object `H^q(K)[0]` does. -/
theorem counitIsomorphismProperty_of_boundedBelow_of_cohomologySheaf
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (K : ModuleDerived X)
    (hbounded : ∃ n : ℤ, K.IsGE n)
    (hcohom : ∀ q : ℤ,
      IsIso
        (adj.counit.app
          ((single0).obj ((H^q).obj K)))) :
    counitIsomorphismProperty
      (modulePullbackDerived f)
      (modulePushforwardDerived f)
      adj
      K := by
  letI : (modulePullbackDerived f).CommShift ℤ := modulePullbackDerived_commShift_of_isFlat f
  letI : (modulePullbackDerived f).IsTriangulated := modulePullbackDerived_isTriangulated_of_isFlat f
  exact
    CategoryTheory.counitIsomorphismProperty_of_boundedBelow_of_cohomology
      (modulePullbackDerived f)
      (modulePushforwardDerived f)
      adj
      K
      hbounded
      (fun q ↦ hcohom q)

/-- Lemma 21.28.3, source-facing specialization: for a flat morphism of ringed topoi formalized
by a flat morphism of ringed sites `f`, if a derived `𝒪_X`-module `K` is
bounded below and every cohomology sheaf `H^q(K)[0]` lies in the canonical counit-isomorphism
property for `Lf^* ⊣ Rf_*`, then `K` itself lies in that property. In this library-facing
formulation, `f^*` is the exact pullback functor on the derived category induced by flatness. -/
@[stacks 0D7S]
theorem counit_isIso_of_boundedBelow_of_cohomologySheaf
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (K : ModuleDerived X)
    (hbounded : ∃ n : ℤ, K.IsGE n)
    (hcohom : ∀ q : ℤ,
      IsIso
        (adj.counit.app
          ((single0).obj ((H^q).obj K)))) :
    IsIso (adj.counit.app K) := by
  simpa [counitIsomorphismProperty] using
    counitIsomorphismProperty_of_boundedBelow_of_cohomologySheaf f adj K hbounded hcohom

end

end RingedSite.Hom
