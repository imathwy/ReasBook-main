import StacksProject_2024.Chap21.Definition_21_43_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u} [Category C]
variable {D : Type v} [Category D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable (RGamma : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
variable (X : C)

/- Domain-style sampling for Lemma 21.43.4:
- primary domain: full subcategories cut out by an `ObjectProperty`, together with restriction of
  adjoint functors to that full subcategory;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ObjectProperty.lift`,
  `CategoryTheory.ObjectProperty.liftCompιIso`,
  `CategoryTheory.Adjunction`;
- best owner abstraction:
  `source-facing`: the Section `21.43` full subcategory `QC`;
  `core/canonical`: the `ObjectProperty` owner `isQuasiCoherent` and its lift API;
  `bridge/view`: the restriction of `Lf` to `QC`, expressed directly by the canonical lift rather
    than by a parallel local wrapper.
- primitive data: `RGamma`, `derivedRestrict`, `comparison`, the functor `Lf`, and the adjunction
  `Lf ⊣ RGamma X`;
- derived API: the restricted functor on `QC` and the equivalence statement below.

This file therefore keeps `QC` as the source-facing owner from Definition `21.43.1` and reuses
the canonical `ObjectProperty.lift` surface directly instead of introducing one-off aliases for
the ambient derived category `D(𝒪(X))`, the restricted pullback, or the restricted
pushforward.
-/

local notation "QCP" => isQuasiCoherent 𝒪 RGamma derivedRestrict comparison
local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison

/-- The canonical restriction of `RΓ(X, -)` to the quasi-coherent full subcategory `QC(𝒪)`.
This is the intended quasi-inverse in Lemma `21.43.4`. -/
abbrev rGammaOnQC :
    QCoh ⥤ DerivedCategory (ModuleCat (𝒪.obj (op X))) :=
  ObjectProperty.ι QCP ⋙ RGamma X

/-- The canonical restriction of `Lf*` to the quasi-coherent full subcategory `QC(𝒪)`. -/
abbrev leftDerivedPullbackToQC
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K)) :
    DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ QCoh :=
  ObjectProperty.lift QCP Lf hLf_mem

/-- Helper for Lemma 21.43.4: the ambient adjunction unit already lands in the restricted
quasi-inverse after restricting `Lf^*` to quasi-coherent objects, objectwise. -/
private noncomputable def leftDerivedPullbackToQC_unitComponentIso
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), IsIso (adj.unit.app K))
    (K : DerivedCategory (ModuleCat (𝒪.obj (op X)))) :
    K ≅
      (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem ⋙
        rGammaOnQC 𝒪 RGamma derivedRestrict comparison X).obj K :=
  @asIso _ _ _ _ (adj.unit.app K) (hunit K)

/-- Helper for Lemma 21.43.4: the restricted unit components are natural. -/
private theorem leftDerivedPullbackToQC_unitComponentIso_naturality
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), IsIso (adj.unit.app K))
    {K L : DerivedCategory (ModuleCat (𝒪.obj (op X)))} (f : K ⟶ L) :
    f ≫ (leftDerivedPullbackToQC_unitComponentIso
        𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit L).hom =
      (leftDerivedPullbackToQC_unitComponentIso
        𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit K).hom ≫
        (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem ⋙
          rGammaOnQC 𝒪 RGamma derivedRestrict comparison X).map f := by
  -- After unfolding the restricted unit component, this is the ambient unit naturality square.
  simpa
      [leftDerivedPullbackToQC_unitComponentIso, leftDerivedPullbackToQC, rGammaOnQC]
    using adj.unit.naturality f

/-- Under the unit-isomorphism hypothesis, the restricted pullback `Lf*` followed by the
restricted sections functor `RΓ(X, -)` is naturally isomorphic to the identity on `D(𝒪(X))`. -/
noncomputable def leftDerivedPullbackToQCCompRGammaOnQCIso
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), IsIso (adj.unit.app K)) :
    𝟭 (DerivedCategory (ModuleCat (𝒪.obj (op X)))) ≅
      leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem ⋙
        rGammaOnQC 𝒪 RGamma derivedRestrict comparison X :=
  NatIso.ofComponents
    (leftDerivedPullbackToQC_unitComponentIso
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit)
    (fun f ↦ leftDerivedPullbackToQC_unitComponentIso_naturality
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit f)

/-- Helper for Lemma 21.43.4: the ambient adjunction counit becomes an isomorphism inside the
quasi-coherent full subcategory, objectwise. -/
private noncomputable def leftDerivedPullbackToQC_counitComponentIso
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hcounit : ∀ K : QCoh, IsIso (adj.counit.app K.obj))
    (K : QCoh) :
    (rGammaOnQC 𝒪 RGamma derivedRestrict comparison X ⋙
      leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem).obj K ≅ K :=
  ObjectProperty.isoMk
    QCP
    (@asIso _ _ _ _ (adj.counit.app K.obj) (hcounit K))

/-- Helper for Lemma 21.43.4: the restricted counit components are natural. -/
private theorem leftDerivedPullbackToQC_counitComponentIso_naturality
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hcounit : ∀ K : QCoh, IsIso (adj.counit.app K.obj))
    {K L : QCoh} (f : K ⟶ L) :
    (rGammaOnQC 𝒪 RGamma derivedRestrict comparison X ⋙
      leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem).map f ≫
        (leftDerivedPullbackToQC_counitComponentIso
          𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hcounit L).hom =
      (leftDerivedPullbackToQC_counitComponentIso
        𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hcounit K).hom ≫
        f := by
  -- Forgetting to the ambient category turns this into the counit naturality square.
  apply ObjectProperty.hom_ext
  simpa
      [leftDerivedPullbackToQC_counitComponentIso, leftDerivedPullbackToQC, rGammaOnQC]
    using adj.counit.naturality f.hom

/-- Under the counit-isomorphism hypothesis, the restricted sections functor `RΓ(X, -)`
followed by the restricted pullback `Lf*` is naturally isomorphic to the identity on `QC(𝒪)`. -/
noncomputable def rGammaOnQCCompLeftDerivedPullbackToQCIso
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hcounit : ∀ K : QCoh, IsIso (adj.counit.app K.obj)) :
    rGammaOnQC 𝒪 RGamma derivedRestrict comparison X ⋙
      leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem ≅
        𝟭 QCoh :=
  NatIso.ofComponents
    (leftDerivedPullbackToQC_counitComponentIso
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hcounit)
    (fun f ↦ leftDerivedPullbackToQC_counitComponentIso_naturality
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hcounit f)

-- Proof sketch: in the terminal-object situation of Lemma `21.43.4`, identify `Rf_*` with
-- `RΓ(X, -)`, restrict it to `QC(𝒪)`, and restrict `Lf*` along the defining object
-- property. The given unit and counit isomorphism hypotheses are exactly the data needed to show
-- that the restricted `Lf*` is an equivalence with quasi-inverse the restricted `Rf_*`.
/-- Lemma 21.43.4, owner form: in the terminal-object setup of Section `21.43`, once the
adjunction `Lf* ⊣ RΓ(X, -)` and the required unit/counit isomorphisms are fixed, the
restriction of `Lf*` to `QC(𝒪)` is an equivalence. -/
@[stacks 0H0R]
theorem leftDerivedPullbackToQC_isEquivalence
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), IsIso (adj.unit.app K))
    (hcounit : ∀ K : QCoh,
      IsIso (adj.counit.app K.obj)) :
    Functor.IsEquivalence
      (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem) := by
  -- Restrict the ambient adjunction to `QC(𝒪)` and use its unit/counit isomorphisms
  -- as the quasi-inverse data for the restricted `Lf*`.
  exact Functor.IsEquivalence.mk'
    (rGammaOnQC 𝒪 RGamma derivedRestrict comparison X)
    (leftDerivedPullbackToQCCompRGammaOnQCIso
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit)
    (rGammaOnQCCompLeftDerivedPullbackToQCIso
      𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hcounit)

/-- Companion instance for Lemma 21.43.4: under the unit/counit isomorphism hypotheses, the
restricted functor `Lf* : D(𝒪(X)) ⥤ QC(𝒪)` is inferred as an equivalence. -/
instance instLeftDerivedPullbackToQCIsEquivalence
    (Lf : DerivedCategory (ModuleCat (𝒪.obj (op X))) ⥤ D)
    (hLf_mem : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), QCP (Lf.obj K))
    (adj : Lf ⊣ RGamma X)
    (hunit : ∀ K : DerivedCategory (ModuleCat (𝒪.obj (op X))), IsIso (adj.unit.app K))
    (hcounit : ∀ K : QCoh, IsIso (adj.counit.app K.obj)) :
    Functor.IsEquivalence
      (leftDerivedPullbackToQC 𝒪 RGamma derivedRestrict comparison X Lf hLf_mem) :=
  leftDerivedPullbackToQC_isEquivalence
    𝒪 RGamma derivedRestrict comparison X Lf hLf_mem adj hunit hcounit

end

end CategoryTheory.ModulesOnCategory
