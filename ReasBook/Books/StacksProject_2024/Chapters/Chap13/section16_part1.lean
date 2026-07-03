import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_16_1 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

/- Domain-style sampling:
- primary domain: pointwise right derived functors on homotopy categories together with the
  canonical t-structure boundedness predicates on cochain complexes and derived categories;
- sampled owner declarations:
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.rightDerivedValueMap`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `CochainComplex.isGE_iff`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`;
- owner abstraction:
  `source-facing`: the three lemmas about derived boundedness and truncation;
  `core/canonical`: `rightDerivedValue`, `rightDerivedValueMap`, and `IsGE`;
  `bridge/view`: the cohomology-vanishing reformulation below. -/

-- Proof sketch: replace `K` by a bounded-below complex quasi-isomorphic to it using
-- Lemma 13.15.5, observe that applying `F` termwise to such a bounded-below representative stays
-- zero in degrees below `a`, and use the cofinality description of the pointwise right derived
-- value to conclude the same vanishing for `RF(K)`.
/-- Lemma 13.16.1 (1): if a cochain complex `K` is bounded below by `a` in the canonical
cohomological sense and the right derived functor of `K(\mathcal A) ⥤ D(\mathcal B)` induced by
`F` is defined at `K`, then `RF(K)` is bounded below by the same integer `a`. -/
theorem rightDerivedValue_isGE_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    (hK : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K)) :
    let X := (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K
    let _ := hK
    (rightDerivedValue Qis KtoD X).IsGE a := sorry

/-- Companion to Lemma 13.16.1 (1): the canonical bounded-below conclusion implies the textbook
degreewise vanishing statement for cohomology in every degree `< a`. -/
theorem rightDerivedValue_isZero_homology_below_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    (hK : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))
    (i : ℤ) (hi : i < a) :
    let X := (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K
    let _ := hK
    IsZero ((DerivedCategory.homologyFunctor ℬ i).obj (rightDerivedValue Qis KtoD X)) := sorry

-- Proof sketch: compare `K.truncLE a`, `K`, and `K.truncGE (a + 1)` by the standard truncation
-- triangle, transport pointwise right-derived existence across that triangle, and then use the
-- long exact cohomology sequence together with part (1) applied to `K.truncGE (a + 1)`.
/-- Lemma 13.16.1 (2): if the right derived functor induced by `F` is defined at `K` and at
`τ_{\le a}K`, then the canonical map `RF(τ_{\le a}K) ⟶ RF(K)` induces an isomorphism on
cohomology in every degree `i ≤ a`. -/
theorem rightDerivedValue_homologyMap_isIso_of_truncLE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hK : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))
    (hTrunc : Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (K.truncLE a)))
    (i : ℤ) (hi : i ≤ a) :
    let _ := hTrunc
    let _ := hK
    IsIso
      ((DerivedCategory.homologyFunctor ℬ i).map
        (rightDerivedValueMap Qis KtoD
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map (K.ιTruncLE a)))) := sorry

end

end CategoryTheory

/-! ### Definition_13_16_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Definition 13.16.2:
- primary domain: bounded-below derived categories and right derived functors.
- inspected owner declarations:
  `boundedBelowDerivedCategory`,
  `ObjectProperty.ι`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`.
- owner abstraction: the bounded-below owner `D⁺(-)`, with the degree-zero embedding
  `𝒜 ⥤ D⁺(𝒜)` obtained by lifting `DerivedCategory.singleFunctor 𝒜 0`, followed by the canonical
  inclusion `D⁺(𝒝) ⥤ D(𝒝)` and `DerivedCategory.homologyFunctor 𝒝 i`.
- primitive data: a chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(𝒝)`.
- derived API: the source-facing composite `A ↦ H^i((RF(A[0])) : D(𝒝))`.

Source/core/bridge triage:
- `source-facing`: the textbook functor `R^iF`;
- `core/canonical`: `boundedBelowDerivedCategory`, `DerivedCategory.singleFunctor`,
  `ObjectProperty.ι`, and `DerivedCategory.homologyFunctor`;
- `bridge/view`: the realization `R^iF(A) = H^i((RF(A[0])) : D(𝒝))`.

This item is a source-facing bridge built from the canonical derived-category owners, so the
file should expose only that named composite and not an unbounded surrogate owner. -/

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]

variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝)) (i : ℤ)

/- Definition 13.16.2: once a chosen functor `RF` models the bounded-below right derived
functor of an additive functor `F : 𝒜 ⥤ 𝒝`, its `i`-th right derived functor is the canonical
composite sending `A` to `H^i((RF(A[0])) : D(\mathcal B))`. -/
#check
  (ObjectProperty.lift (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.singleFunctor 𝒜 0)
      (fun A ↦ by
        exact ⟨0, inferInstance⟩) ⋙
    RF ⋙
    ObjectProperty.ι (t.plus : ObjectProperty (D(𝒝))) ⋙
      DerivedCategory.homologyFunctor 𝒝 i)

end

end CategoryTheory

/-! ### Lemma_13_16_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

/-
Domain-style sampling:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, together with the degree-zero branch `A ↦ H⁰(RF(A[0]))`;
- sampled owner declarations:
  `Functor.IsRightDerivedFunctor`,
  `Functor.totalRightDerivedUnit`,
  `single0Plus`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the source-facing bounded-below owner is a chosen
  `RF : D⁺(𝒜) ⥤ D⁺(𝒝)` equipped with a derivation witness
  `α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
    mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF`;
- primitive data: the chosen bounded-below right derived functor `RF` and its derivation witness
  `α`;
- derived API: the vanishing of `H^i(RF(A[0]))` for `i < 0`, the left exactness of
  `A ↦ H⁰(RF(A[0]))`, and the canonical comparison
  `F ⟶ (A ↦ H⁰(RF(A[0])))`;
- source/core/bridge triage:
  `source-facing`: the three bounded-below statements below;
  `core/canonical`: `Functor.IsRightDerivedFunctor`, `Functor.totalRightDerivedUnit`, and the
    bounded-below localization owners from Situation `13.15.1`;
  `bridge/view`: the bounded-below degree-zero comparison
    `Functor.toBoundedBelowRightDerivedZero`, and the later injective-resolution owners
    `Functor.rightDerived` and `Functor.toRightDerivedZero`, which are kept only as
    stronger-assumption companions.
--/

section BoundedBelow

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]

variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

-- Proof sketch: the degree-zero object `A[0]` in `D⁺(𝒜)` is concentrated in degrees `≥ 0`, so
-- any bounded-below right derived functor `RF` has no cohomology in negative degrees on `RF(A[0])`.
/-- Lemma 13.16.3 (1): for a bounded-below right derived functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the functor
`A ↦ H^i(RF(A[0]))` vanishes for every `i < 0`. -/
theorem boundedBelowRightDerived_isZero_of_neg
    (i : ℤ) (hi : i < 0) :
    IsZero (RF.boundedBelowRightDerived i) := by
  sorry

-- Proof sketch: the exactness package needed to build the long exact cohomology sequence for the
-- bounded-below derived functor `RF` is part of the proof route, not of the source-facing
-- statement. Using that exactness internally and then part `(1)` to remove the negative term
-- leaves left exactness in degree `0`.
/-- Lemma 13.16.3 (2): the degree-zero branch of a bounded-below right derived functor,
formalized as `A ↦ H^0(RF(A[0]))`, is left exact. -/
theorem boundedBelowRightDerivedZero_preservesFiniteLimits
    : PreservesFiniteLimits (RF.boundedBelowRightDerived 0) := by
  sorry

-- Proof sketch: if `F` is identified with `A ↦ H^0(RF(A[0]))`, transport left exactness along
-- that identification using part `(2)`. Conversely, when `F` is left exact, the canonical
-- degree-zero comparison attached to the bounded-below right derived functor is an isomorphism.
-- Any exactness structures on `RF` used in the proof are internal consequences of the chosen
-- right-derived-functor setup and do not belong in the public API of this source-facing lemma.
/-- Lemma 13.16.3 (3): the canonical comparison
`F ⟶ (A ↦ H^0(RF(A[0])))`, formalized as `F.toBoundedBelowRightDerivedZero RF α`, is an
isomorphism exactly when `F` is left exact. -/
theorem isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits
    : IsIso (F.toBoundedBelowRightDerivedZero RF α) ↔ PreservesFiniteLimits F := by
  sorry

end BoundedBelow

end

section RightDerived

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]

variable [HasInjectiveResolutions 𝒜]

-- Proof sketch: this is the injective-resolution specialization of the bounded-below degree-zero
-- statement above, expressed in mathlib's canonical owner `Functor.rightDerived 0`.
/-- Stronger-assumption companion to Lemma 13.16.3 (2): under injective resolutions, the degree-zero
right derived functor `R^0F`, formalized as `F.rightDerived 0`, is left exact. -/
theorem rightDerivedZero_preservesFiniteLimits :
    PreservesFiniteLimits (F.rightDerived 0) := sorry

-- Proof sketch: if `F ⟶ R^0F` is an isomorphism, transport left exactness from `R^0F` using the
-- previous companion. Conversely, if `F` is left exact, mathlib's canonical comparison
-- `F.toRightDerivedZero : F ⟶ F.rightDerived 0` is an isomorphism.
/-- Stronger-assumption companion to Lemma 13.16.3 (3): under injective resolutions, the canonical
comparison map `F ⟶ R^0F`, formalized as `F.toRightDerivedZero`, is an isomorphism exactly when
`F` is left exact. -/
theorem isIso_toRightDerivedZero_iff_preservesFiniteLimits :
    IsIso F.toRightDerivedZero ↔ PreservesFiniteLimits F := by
  constructor
  · intro h
    letI := h
    letI := rightDerivedZero_preservesFiniteLimits F
    exact preservesFiniteLimits_of_natIso (asIso F.toRightDerivedZero).symm
  · intro h
    letI := h
    infer_instance

end RightDerived

end CategoryTheory

/-! ### Lemma_13_16_4 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-
Domain-style sampling for Lemma 13.16.4:
- primary domain: right acyclicity for additive functors, stated source-faithfully through a
  chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.IsRightDerivedFunctor`,
  `Functor.toBoundedBelowRightDerivedZero`,
  `isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits`;
- best owner abstraction: the source-facing owner is
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F A`; the injective-resolution API
  `IsRightAcyclicForAdditiveFunctor`, `Functor.toRightDerivedZero`, and `Functor.rightDerived`
  is only a stronger companion bridge;
- primitive data: the chosen bounded-below right derived functor `RF` together with its
  derivation witness `α`;
- derived API: the positive-degree vanishing predicate for `A ↦ H^i(RF(A[0]))`, the main
  acyclicity characterization, and the left exact corollary.

Source/core/bridge triage:
- `source-facing`: the bounded-below statements in the `BoundedBelow` section;
- `core/canonical`: `Functor.IsRightDerivedFunctor`, `Functor.toBoundedBelowRightDerivedZero`,
  and the bounded-below acyclicity owner from `Definition 13.15.3`;
- `bridge/view`: the later unbounded injective-resolution companions in the `Unbounded` section.
-/

section BoundedBelow

variable [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization QisPlus]

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α QisPlus]

namespace Functor

/-- The proposition that all positive right derived functors determined by the bounded-below
realization `RF` vanish on `A`. -/
abbrev boundedBelowHigherRightDerivedVanishes (RF : D⁺(𝒜) ⥤ D⁺(ℬ)) (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((RF.boundedBelowRightDerived (n + 1)).obj A)

end Functor

-- Proof sketch: by Lemma `13.15.2`, the degree-zero bounded-below complex `A[0]` computes the
-- bounded-below right derived functor exactly when it computes the unbounded one. Unwinding the
-- pointwise computation in `D⁺(ℬ)`, the unit map is the comparison `F(A) ⟶ H⁰(RF(A[0]))`, while
-- the higher cohomology objects are the positive right derived functors `RⁱF(A)`.
/-- Lemma 13.16.4: an object `A` is right acyclic for the bounded-below right derived functor of
`F` if and only if the canonical comparison morphism
`F(A) ⟶ H^0(RF(A[0]))`, formalized as `(F.toBoundedBelowRightDerivedZero RF α).app A`, is an
isomorphism and all positive right derived functors determined by `RF` vanish on `A`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_isIso_toBoundedBelowRightDerivedZero_app_and_boundedBelowHigherRightDerivedVanishes
    (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      IsIso ((F.toBoundedBelowRightDerivedZero RF α).app A) ∧
        RF.boundedBelowHigherRightDerivedVanishes A := sorry

-- Proof sketch: for a left exact additive functor, Lemma `13.16.3` identifies `F` with the
-- degree-zero branch `A ↦ H⁰(RF(A[0]))` without adding extra exactness hypotheses on the chosen
-- bounded-below right derived functor `RF`. The previous theorem then reduces right acyclicity to
-- the vanishing of the positive right derived functors.
/-- For a left exact additive functor, bounded-below right acyclicity is equivalent to the
vanishing of all positive right derived functors determined by `RF`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
    [PreservesFiniteLimits F] (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      RF.boundedBelowHigherRightDerivedVanishes A := sorry

end BoundedBelow

section Unbounded

variable [HasDerivedCategory.{w} ℬ] [HasInjectiveResolutions 𝒜]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

namespace Functor

/-- Stronger-assumption companion: all positive unbounded right derived functors of `F` vanish on
`A`. -/
abbrev higherRightDerivedVanishes (F : 𝒜 ⥤ ℬ) [F.Additive] (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj A)

end Functor

-- Proof sketch: under injective resolutions, the bounded-below and unbounded right derived
-- functors agree on the degree-zero complex `A[0]`, so the source-facing bounded-below statement
-- above specializes to the usual comparison `F(A) ⟶ R⁰F(A)` and the vanishing of
-- `RⁱF(A)` for `i > 0`.
/-- Stronger-assumption companion to Lemma 13.16.4: under injective resolutions and the unbounded
right derived functor, an object `A` is right acyclic for `F` if and only if the comparison
`F(A) ⟶ R⁰F(A)` is an isomorphism and the higher right derived functors vanish on `A`. -/
theorem isRightAcyclicForAdditiveFunctor_iff_isIso_toRightDerivedZero_app_and_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      IsIso (F.toRightDerivedZero.app A) ∧
        F.higherRightDerivedVanishes A := sorry

-- Proof sketch: for a left exact additive functor, `F.toRightDerivedZero : F ⟶ R⁰F` is an
-- isomorphism, so the previous companion reduces right acyclicity to the vanishing of the
-- positive right derived functors.
/-- Stronger-assumption companion: for a left exact additive functor, unbounded right acyclicity
is equivalent to the vanishing of all higher right derived functors. -/
theorem isRightAcyclicForAdditiveFunctor_iff_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] [PreservesFiniteLimits F] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      F.higherRightDerivedVanishes A := sorry

end Unbounded

end

end CategoryTheory

/-! ### Lemma_13_16_5 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive]
variable [PreservesFiniteLimits F]

/-
Domain-style sampling for Lemma 13.16.5:
- primary domain: bounded-below right acyclicity for a left exact additive functor in short exact
  sequences;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.boundedBelowHigherRightDerivedVanishes`,
  `isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes`,
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the source-facing owner on objects is
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F`; the unbounded injective-resolution notion
  `IsRightAcyclicForAdditiveFunctor F` is only a stronger bridge/view under extra assumptions and
  should not drive the main statements here;
- primitive data: a short exact sequence in `𝒜` and bounded-below right acyclicity of the
  relevant objects;
- derived API: the five bounded-below acyclicity closure theorems and their mapped-short-exactness
  corollaries; proofs may pass through Lemma `13.16.4` and a chosen bounded-below right derived
  functor, but that proof route is not part of the public API; the exact-functor statement with
  explicit hypothesis `Epi (F.map S.g)` is a stronger companion.

Source/core/bridge triage:
- `source-facing`: bounded-below right acyclicity in the six short-exact-sequence cases from the
  source text;
- `core/canonical`: `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.boundedBelowHigherRightDerivedVanishes`, `ShortComplex.ShortExact`, and
  `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`;
-- `bridge/view`: the unbounded injective-resolution owners
  `IsRightAcyclicForAdditiveFunctor` and `Functor.higherRightDerivedVanishes`, which belong only
  in stronger-assumption companion statements. -/

section BoundedBelow

variable [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

/-- Helper for Lemma 13.16.5: the bounded-below degree-zero embedding followed by the canonical
inclusion into the unbounded derived category identifies with the usual degree-zero embedding. -/
private noncomputable def single0ToDerivedIso :
    single0ToDplus 𝒜 ⋙ ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) ≅
      DerivedCategory.singleFunctor 𝒜 0 :=
  (𝟭 𝒜).single0PlusToSingleFunctorIso ≪≫ Functor.leftUnitor _

/-- Helper for Lemma 13.16.5: a short exact sequence in `𝒜` yields a bounded-below triangle on
degree-zero objects by transporting the usual connecting morphism through `single0ToDerivedIso`. -/
private noncomputable def single0ToDplusTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (D⁺(𝒜)) :=
  Triangle.mk
    ((single0ToDplus 𝒜).map S.f)
    ((single0ToDplus 𝒜).map S.g)
    ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).preimage
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso (1 : ℤ)).inv.app
            ((single0ToDplus 𝒜).obj S.X₁)))

/-- Helper for Lemma 13.16.5: the transported bounded-below triangle attached to a short exact
sequence is distinguished. -/
private theorem single0ToDplus_triangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    single0ToDplusTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) := by
  -- Route correction: the intended proof maps this triangle to `D(𝒜)`, compares it with
  -- `hS.singleTriangle` via `single0ToDerivedIso`, and then applies
  -- `isomorphic_distinguished _ hS.singleTriangle_distinguished`.
  rw [← (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
          ((single0ToDplus 𝒜).map S.f))
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
          ((single0ToDplus 𝒜).map S.g))
        ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map
            ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).preimage
              ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
                ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
                  ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso
                    (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁))) ≫
          ((ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).commShiftIso
            (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁)) ∈
      distTriang (D(𝒜))
  rw [(ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))).map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _
    (single0ToDerivedIso.app S.X₁)
    (single0ToDerivedIso.app S.X₂)
    (single0ToDerivedIso.app S.X₃)
    ?_ ?_ ?_
  · simpa using single0ToDerivedIso.hom.naturality S.f
  · simpa using single0ToDerivedIso.hom.naturality S.g
  · -- After cancelling the commutation isomorphism and the shifted comparison isomorphism,
    -- the transported connecting morphism reduces to `hS.singleδ`.
    have hshift :
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
          (single0ToDerivedIso.inv_hom_id_app S.X₁)
    have hthird :
      single0ToDerivedIso.hom.app S.X₃ ≫
          hS.singleδ ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
              (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                  (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
          =
        single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
      calc
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                  (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                    (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
            =
          single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    k ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁))
              ((Functor.commShiftIso (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))))
                (1 : ℤ)).inv_hom_id_app ((single0ToDplus 𝒜).obj S.X₁))
        _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
          calc
            single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
                =
              single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
                𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫ k) hshift
            _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
              simp
    simpa [single0ToDplusTriangle, ShortComplex.ShortExact.singleTriangle, Category.assoc] using
      hthird

instance isClosedUnderExtensions_isBoundedBelowRightAcyclicForAdditiveFunctor :
    ObjectProperty.IsClosedUnderExtensions
      (IsBoundedBelowRightAcyclicForAdditiveFunctor F : ObjectProperty 𝒜) where
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃
    -- The main source-faithful skeleton is now in place: use the distinguished bounded-below
    -- triangle on `A[0]`, `B[0]`, `C[0]`, extract the five-term exact window, and then apply
    -- Lemma `13.16.4` degreewise to kill the endpoint terms.
    have hT : single0ToDplusTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) :=
      single0ToDplus_triangle_distinguished (𝒜 := 𝒜) hS
    clear hT
    -- TODO: the source-faithful proof uses the positive-degree long exact sequence for a
    -- bounded-below right derived functor of `F`, but that global right-derived-functor owner is
    -- not yet available in the dependency closure of this file.
    sorry

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness gives the exactness and monicity on the left of the
mapped short complex attached to a short exact sequence in `𝒜`. -/
theorem exact_mono_map_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    (S.map F).Exact ∧ Mono (F.map S.f) := by
  -- The preservation-of-finite-limits criterion packages the left exactness of `F`.
  rcases
    (F.preservesFiniteLimits_iff_forall_exact_map_and_mono).1
      (inferInstance : PreservesFiniteLimits F) S hS with
    ⟨h_exact, h_mono⟩
  exact ⟨h_exact, h_mono⟩

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness preserves exactness at the middle term of the mapped
short complex. -/
theorem exact_map_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    (S.map F).Exact := by
  -- This is the exactness component of the packaged left-exactness statement above.
  exact (exact_mono_map_of_shortExact (F := F) hS).1

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: left exactness preserves the monomorphism on the left of the mapped
short complex. -/
theorem mono_map_f_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Mono (F.map S.f) := by
  -- This is the monomorphism component of the same left-exactness package.
  exact (exact_mono_map_of_shortExact (F := F) hS).2

omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Helper for Lemma 13.16.5: once `F.map S.g` is known to be an epimorphism, the mapped sequence
is short exact. -/
theorem map_shortExact_of_epi_map_g_aux
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := by
  -- Combine left exactness on the left with the supplied surjectivity on the right.
  have h_exact : (S.map F).Exact := exact_map_of_shortExact (F := F) hS
  have h_mono : Mono (F.map S.f) := mono_map_f_of_shortExact (F := F) hS
  exact ShortComplex.ShortExact.mk' h_exact h_mono h_epi

/-- Helper for Lemma 13.16.5: in the end-acyclic case, the source-faithful long exact sequence
should show that `F.map S.g` is an epimorphism. -/
theorem epi_map_g_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    Epi (F.map S.g) := by
  -- TODO: follow the exact degree-zero window
  -- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`;
  -- the acyclicity of `S.X₁` kills `R¹F(S.X₁)`, so exactness forces `F.map S.g` to be epi.
  sorry

/-- Helper for Lemma 13.16.5: under the ambient bounded-below derived-category hypotheses, the
mapped short exact sequence in the end-acyclic case follows from the epi bridge. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends_aux
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    (S.map F).ShortExact := by
  -- First obtain surjectivity on the right from the degree-zero exact window.
  have h_epi : Epi (F.map S.g) :=
    epi_map_g_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends (F := F) hS h₁ h₃
  -- Then combine it with left exactness on the first two terms.
  exact map_shortExact_of_epi_map_g_aux (F := F) hS h_epi

-- Proof sketch: rewrite the two endpoint acyclicity hypotheses using Lemma `13.16.4` as the
-- vanishing of the positive bounded-below right derived functors for some chosen bounded-below
-- right derived functor of `F`. The long exact sequence attached to `hS` then forces the
-- corresponding groups for `S.X₂` to vanish, hence `S.X₂` is bounded-below right acyclic for
-- `F`.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (1): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `A` and `C` are right
acyclic for the bounded-below right derived functor of `F`, equivalently if the positive bounded-
below right derived functors of `F` vanish on `A` and `C`, then `B` is right acyclic for the
bounded-below right derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_middle_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂ := by
  -- Reuse the local extension-closure instance; the remaining blocker is concentrated in the
  -- instance proof above, where the long-exact-sequence argument belongs.
  exact
    ObjectProperty.prop_X₂_of_shortExact
      (P := IsBoundedBelowRightAcyclicForAdditiveFunctor F) hS h₁ h₃

-- Proof sketch: the same long exact sequence begins
-- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`. Under the bounded-below right-acyclicity
-- assumptions on `S.X₁` and `S.X₃`, Lemma `13.16.4` kills the positive bounded-below derived
-- terms, so `F(S.X₂) ⟶ F(S.X₃)` is epi and the image sequence is short exact.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (2): in the first case of Lemma 13.16.5, applying `F` to the short exact
sequence again yields a short exact sequence. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃) :
    (S.map F).ShortExact := by
  -- Reuse the auxiliary theorem so the remaining blocker stays isolated in the epi bridge.
  exact
    map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends_aux
      (F := F) hS h₁ h₃

-- Proof sketch: after identifying bounded-below right acyclicity with vanishing of the positive
-- bounded-below right derived functors, use the long exact sequence attached to `hS`. The
-- vanishings for `S.X₁` and `S.X₂` force the corresponding groups for `S.X₃` to vanish, so
-- `S.X₃` is bounded-below right acyclic.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (3): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `A` and `B` are right
acyclic for the bounded-below right derived functor of `F`, equivalently if the positive bounded-
below right derived functors of `F` vanish on `A` and `B`, then `C` is right acyclic for the
bounded-below right derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_cokernel_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃ := by
  -- TODO: realize the source-faithful long-exact-sequence proof either from a dependency-closed
  -- bounded-below right-derived-functor owner for `KplusToDplus` or from a local pointwise
  -- derived-value triangle in `K⁺(𝒜)` whose third vertex is quasi-isomorphic to `single0Plus C`.
  sorry

-- Proof sketch: the long exact sequence in bounded-below right derived functors gives
-- `0 ⟶ F(S.X₁) ⟶ F(S.X₂) ⟶ F(S.X₃) ⟶ R¹F(S.X₁) ⟶ ⋯`; when `S.X₁` and `S.X₂` are bounded-below
-- right acyclic, the term `R¹F(S.X₁)` vanishes by Lemma `13.16.4`, so the image sequence is
-- short exact.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (4): in the second case of Lemma 13.16.5, applying `F` to the short exact
sequence again yields a short exact sequence. -/
theorem map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_left_middle
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂) :
    (S.map F).ShortExact := by
  exact
    map_shortExact_of_isBoundedBelowRightAcyclicForAdditiveFunctor_ends F hS h₁
      (isBoundedBelowRightAcyclicForAdditiveFunctor_cokernel_of_shortExact F hS h₁ h₂)

-- Proof sketch: rewrite bounded-below right acyclicity using Lemma `13.16.4` and inspect the
-- long exact sequence of bounded-below right derived functors for `hS`. The vanishing for `S.X₂`
-- and `S.X₃`, together with the surjectivity of `F.map S.g`, remove the boundary term at degree
-- `0`, forcing the positive bounded-below right derived functors of `S.X₁` to vanish and hence
-- making `S.X₁` bounded-below right acyclic.
omit [HasDerivedCategory.{w} 𝒜] in
/-- Lemma 13.16.5 (5): in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`, if `B` and `C` are right
acyclic for the bounded-below right derived functor of `F` and `F(B) ⟶ F(C)` is an
epimorphism, equivalently if the positive bounded-below right derived functors of `F` vanish on
`B` and `C` and `F(B) ⟶ F(C)` is epi, then `A` is right acyclic for the bounded-below right
derived functor of `F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_kernel_of_shortExact_of_epi_map_g
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₂ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₂)
    (h₃ : IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₃)
    (h_epi : Epi (F.map S.g)) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F S.X₁ := by
  -- TODO: combine the degree-zero epi hypothesis with the positive-degree long exact window once
  -- the same dependency-closed derived-value owner used in the cokernel case is available.
  sorry

-- Proof sketch: left exactness gives exactness and monicity on the left of the mapped sequence,
-- and the additional hypothesis `Epi (F.map S.g)` supplies the right exactness. Hence the image
-- of the original short exact sequence under `F` is again short exact, so the mapped short-
-- exactness conclusion of Lemma 13.16.5 (6) does not in fact need the bounded-below right
-- acyclicity hypotheses on `B` and `C`.
omit [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ] in
/-- Lemma 13.16.5 (6): in the third case of Lemma 13.16.5, if `F(B) ⟶ F(C)` is an epimorphism,
then applying `F` to the short exact sequence again yields a short exact sequence. The source's
bounded-below right acyclicity hypotheses on `B` and `C` are mathematically redundant for this
mapped short-exactness conclusion. -/
theorem map_shortExact_of_epi_map_g
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := by
  -- This is the epi-only core used by the two source-facing mapped-short-exactness corollaries.
  exact map_shortExact_of_epi_map_g_aux (F := F) hS h_epi

end BoundedBelow

end

end CategoryTheory

/-! ### Lemma_13_16_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/- Domain-style sampling for Lemma 13.16.6:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, expressed through the canonical triangulated-to-cohomological `δ`-functor pipeline;
- sampled owner declarations:
  `ShortComplex.ShortExact.singleδ`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`,
  `Functor.boundedBelowRightDerived`,
  `single0ToDplus`;
- best owner abstraction: the public source-facing object is the canonical bounded-below
  cohomological `δ`-functor whose degree-`n` term is `RF.boundedBelowRightDerived n`, obtained by
  first building the bounded-below `DeltaFunctor` on degree-zero objects and then applying the
  owner construction `DeltaFunctor.toCohomologicalDeltaFunctor`;
- primitive data: the explicit bounded-below degree-zero `DeltaFunctor` and the exact functor
  `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- derived API: the named cohomological `δ`-functor `boundedBelowRightDerivedDeltaFunctor RF`, its
  degreewise identification with `RF.boundedBelowRightDerived n`, and the universality criterion
  once objects embed into bounded-below right-acyclic objects.

Source/core/bridge triage:
- `source-facing`: the bounded-below right-derived cohomological `δ`-functor and its universality.
- `core/canonical`: `DeltaFunctor`, `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`, and `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the bounded-below degree-zero `DeltaFunctor` on `single0ToDplus 𝒜`, plus the
  later unbounded comparison with `Functor.rightDerived`.

This file should therefore expose the source-facing cohomological `δ`-functor by direct reuse of
the chapter’s `DeltaFunctor` owners, not by existentially packaging the connecting maps. -/

local notation "plusιA" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "H" => DerivedCategory.homologyFunctor ℬ

private noncomputable def single0ToDerivedIso :
    single0ToDplus 𝒜 ⋙ plusιA ≅ DerivedCategory.singleFunctor 𝒜 0 :=
  (𝟭 𝒜).single0PlusToSingleFunctorIso ≪≫ Functor.leftUnitor _

-- Proof sketch: transport the canonical connecting morphism `hS.singleδ` for short exact
-- sequences in `𝒜` into the bounded-below derived category `D⁺(𝒜)` via the explicit
-- degree-zero comparison `single0PlusToDerivedIso`. The distinguished-triangle and naturality
-- fields are the corresponding transported versions of `hS.singleTriangle_distinguished` and the
-- naturality of `singleδ`.
/-- The canonical `δ`-functor on degree-zero objects
`single0ToDplus 𝒜 : 𝒜 ⥤ D^+(\mathcal A)`. -/
noncomputable def single0ToDplusDeltaFunctor :
    DeltaFunctor 𝒜 D⁺(𝒜) where
  toFunctor := single0ToDplus 𝒜
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app
            ((single0ToDplus 𝒜).obj S.X₁)))
  map_distinguished := by
    intro S hS
    sorry
  δ_naturality := by
    intro S T hS hT φ
    sorry

/-- The underlying functor of `single0ToDplusDeltaFunctor` is the canonical degree-zero embedding
`𝒜 ⥤ D^+(\mathcal A)`. -/
@[simp] theorem single0ToDplusDeltaFunctor_toFunctor :
    (single0ToDplusDeltaFunctor : DeltaFunctor 𝒜 D⁺(𝒜)).toFunctor = single0ToDplus 𝒜 :=
  rfl

private noncomputable def boundedBelowRightDerivedDeltaOwner :
    DeltaFunctor 𝒜 (D(ℬ)) :=
  (single0ToDplusDeltaFunctor.postcomposeExactFunctor RF).postcomposeExactFunctor plusι

private theorem boundedBelowRightDerivedDeltaOwner_hneg (X : 𝒜) :
    IsZero (((H 0).shift (-1)).obj
      ((boundedBelowRightDerivedDeltaOwner RF).toFunctor.obj X)) := by
  sorry

/-- Lemma 13.16.6 (1): for an exact bounded-below right derived functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the functors
`RF.boundedBelowRightDerived n`, i.e. `A ↦ H^n((RF(A[0])) : D(\mathcal B))`, carry canonical
connecting morphisms making them into a cohomological `δ`-functor. -/
noncomputable def boundedBelowRightDerivedDeltaFunctor :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (boundedBelowRightDerivedDeltaOwner RF) (H 0)
    (boundedBelowRightDerivedDeltaOwner_hneg RF)

/-- The degree-`n` branch of `boundedBelowRightDerivedDeltaFunctor RF` is the canonical functor
`A ↦ H^n((RF(A[0])) : D(\mathcal B))`. -/
@[simp] theorem boundedBelowRightDerivedDeltaFunctor_obj (n : ℕ) :
    ((boundedBelowRightDerivedDeltaFunctor RF n).obj) = RF.boundedBelowRightDerived n := by
  sorry

end BoundedBelow

section Universal

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

-- Proof sketch: if every object embeds into a bounded-below right-acyclic object, then Lemma
-- `13.16.4` turns that acyclicity into vanishing of all positive functors
-- `RF.boundedBelowRightDerived (n + 1)` on the chosen target object. Hence every positive degree
-- of `T` is weakly effaceable, and Lemma
-- `12.12.4` gives universality.
/-- Lemma 13.16.6 (2): if `F` is left exact and every object of `𝒜` is a subobject of an object
right acyclic for the bounded-below right derived functor of `F`, then the canonical bounded-
below right-derived cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := sorry

end Universal

section UnboundedCompanion

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] [HasInjectiveResolutions 𝒜]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

-- Proof sketch: specialize the bounded-below universality theorem to the stronger hypothesis
-- that the bounded-below degrees agree with the canonical unbounded `Functor.rightDerived`
-- functors and that every object embeds into an unbounded right-acyclic object.
/-- Stronger-assumption companion: under injective resolutions, if the bounded-below family
`A ↦ H^n((RF(A[0])) : D(\mathcal B))` is degreewise isomorphic to the canonical unbounded right
derived functors `F.rightDerived n`, then the canonical bounded-below right-derived
cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n))
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := sorry

end UnboundedCompanion

end CategoryTheory

/-! ### Lemma_13_16_7_Leray_s_acyclicity_lemma (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex supported in the
single degree `a` becomes the corresponding single object in the homotopy category. -/
noncomputable abbrev representative_single_iso_of_strict_bounds
    (K : CochainComplex 𝒜 ℤ) (a : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE a] :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a) :=
  let M : 𝒜 := Classical.choose (CochainComplex.exists_iso_single (K := K) a)
  let e : K ≅ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) a).obj M :=
    Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := K) a))
  let eX : K.X a ≅ M :=
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) a).mapIso e ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M
  (HomotopyCategory.quotient 𝒜 (up ℤ)).mapIso e ≪≫
    (HomotopyCategory.singleFunctor 𝒜 a).mapIso eX.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): quasi-isomorphisms in the unbounded
homotopy category are stable under shifts. This is the bridge needed to apply the generic
shift-stability API for `ComputesRightDerivedAt` to `K(\mathcal A) ⟶ D(\mathcal B)`. -/
local instance homotopyCategory_quasiIso_isCompatibleWithShift :
    (HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithShift ℤ where
  condition n := by
    ext X Y f
    change Qis (f⟦n⟧') ↔ Qis f
    rw [HomotopyCategory.mem_quasiIso_iff]
    rw [HomotopyCategory.mem_quasiIso_iff]
    constructor
    · intro hf j
      -- Shift the homology index back by `n` so the shifted quasi-isomorphism hypothesis matches
      -- the source of the canonical homology shift isomorphism.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n (j - n) j (by omega)) f).1
          (hf (j - n))
    · intro hf i
      -- The forward direction uses the same homology shift isomorphism with target degree
      -- `n + i`.
      simpa [Functor.comp_map] using
        (NatIso.isIso_map_iff
          ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0).shiftIso
            n i (n + i) rfl) f).2
          (hf (n + i))

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a cochain complex concentrated in a
single degree whose unique term is right `F`-acyclic computes the unbounded right derived
functor. -/
lemma computesRightDerivedAt_single_degree_of_right_acyclic
    (K : CochainComplex 𝒜 ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE a]
    (hK : IsRightAcyclicForAdditiveFunctor F (K.X a)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Identify the representative with the single complex concentrated in degree `a`.
  let e := representative_single_iso_of_strict_bounds (𝒜 := 𝒜) K a
  have hsingle_shift :
      ComputesRightDerivedAt KtoD Qis
        (((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a))⟦a⟧) := by
    -- The shift of the single complex in degree `a` is the degree-zero single complex.
    exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
      (((HomotopyCategory.singleFunctors 𝒜).shiftIso a 0 a (by simp)).symm.app (K.X a))
      hK
  have hsingle :
      ComputesRightDerivedAt KtoD Qis
        ((HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) := by
    -- Shift invariance transports the computation statement back to degree `a`.
    exact (computesRightDerivedAt_iff_shift (F := KtoD) (S := Qis)
      (X := (HomotopyCategory.singleFunctor 𝒜 a).obj (K.X a)) (n := a)).2 hsingle_shift
  -- Finally transport the computation statement across the chosen representative isomorphism.
  exact ((mapHomotopyCategoryToDerived F).computesRightDerivedObjectProperty Qis).prop_of_iso
    e.symm hsingle

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): termwise bounded-below right acyclicity
of a bounded-below homotopy object implies termwise right acyclicity of the underlying unbounded
homotopy object. -/
lemma isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    IsTermwiseRightAcyclicForAdditiveFunctor F A := by
  intro n
  -- Convert each degree-zero bounded-below computation statement to the unbounded one via the
  -- canonical comparison of Lemma `13.15.2`.
  simpa [IsRightAcyclicForAdditiveFunctor, HomotopyCategory.quotient_obj_as] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := F) ((single0Plus 𝒜).obj (A.obj.as.X n))).2 (hA n)

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): turn an `IsIso` witness into an explicit
isomorphism. -/
private noncomputable def isoOfIsIso
    {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} (hf : IsIso f) :
    X ≅ Y := by
  let invf := hf.out.choose
  have h₁ : f ≫ invf = 𝟙 X := hf.out.choose_spec.1
  have h₂ : invf ≫ f = 𝟙 Y := hf.out.choose_spec.2
  exact ⟨f, invf, h₁, h₂⟩

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): a morphism in `D(\mathcal B)` is an
isomorphism exactly when all of its cohomology maps are isomorphisms. -/
lemma derivedCategory_isIso_iff_homology_map_isIso
    {X Y : DerivedCategory ℬ} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H i).map f) := by
  constructor
  · intro hf
    intro i
    -- Any isomorphism stays an isomorphism after applying the cohomology functor.
    let _ : IsIso f := hf
    exact Functor.map_isIso (H i) f
  · intro hf
    -- Lift `f` to the homotopy category and detect isomorphisms there via quasi-isomorphisms.
    obtain ⟨g, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh.mapArrow) (Arrow.mk f)
    have hq : HomotopyCategory.quasiIso ℬ (ComplexShape.up ℤ) g.hom := by
      rw [HomotopyCategory.mem_quasiIso_iff]
      intro i
      haveI : IsIso e.hom := e.isIso_hom
      let eleft :
          (H i).obj (DerivedCategory.Qh.obj g.left) ≅ (H i).obj X :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.leftFunc e.hom))
      let eright :
          (H i).obj (DerivedCategory.Qh.obj g.right) ≅ (H i).obj Y :=
        Functor.mapIso (H i) (isoOfIsIso (Functor.map_isIso Arrow.rightFunc e.hom))
      let ef : (H i).obj X ≅ (H i).obj Y := isoOfIsIso (hf i)
      have hw :
          (H i).map (Arrow.Hom.left e.hom) ≫ (H i).map f =
            (H i).map (DerivedCategory.Qh.map g.hom) ≫ (H i).map (Arrow.Hom.right e.hom) := by
        simpa [Functor.map_comp] using congrArg ((H i).map) (Arrow.w e.hom)
      have hcomp :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫
            (H i).map (Arrow.Hom.right e.hom)) := by
        haveI : IsIso (eleft.hom ≫ ef.hom) := by infer_instance
        rw [← hw]
        change IsIso (eleft.hom ≫ ef.hom)
        infer_instance
      have heright : eright.hom = (H i).map (Arrow.Hom.right e.hom) := by
        rfl
      haveI :
          IsIso ((H i).map (DerivedCategory.Qh.map g.hom) ≫ eright.hom) := by
        rw [heright]
        exact hcomp
      have hmap : IsIso ((H i).map (DerivedCategory.Qh.map g.hom)) := by
        exact IsIso.of_isIso_comp_right ((H i).map (DerivedCategory.Qh.map g.hom)) eright.hom
      rw [← NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh ℬ i) g.hom]
      exact hmap
    have hQg : IsIso (DerivedCategory.Qh.map g.hom) :=
      (DerivedCategory.isIso_Qh_map_iff g.hom).2 hq
    haveI : IsIso e.hom := e.isIso_hom
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).1 hQg

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the canonical identity-denominator legs
for pointwise right-derived values are natural in the source morphism. -/
lemma rightDerivedValueLeg_id_naturality
    {X Y : HomotopyCategory 𝒜 (up ℤ)} (f : X ⟶ Y)
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X]
    [HasPointwiseRightDerivedFunctorAt KtoD Qis Y] :
    (mapHomotopyCategoryToDerived F).map f ≫
        rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y) =
      rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X) ≫
        rightDerivedValueMap Qis KtoD f := by
  -- The generic denominator-square compatibility specializes to the square with identity
  -- denominators on both sides.
  simpa using
    (show CommSq
        (rightDerivedValueLeg Qis KtoD (𝟙 X)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X))
        ((mapHomotopyCategoryToDerived F).map f)
        (rightDerivedValueMap Qis KtoD f)
        (rightDerivedValueLeg Qis KtoD (𝟙 Y)
          (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)) from
      rightDerivedValueMap_comp_of_square Qis KtoD f
        (𝟙 X) (𝟙 Y)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) X)
        (MorphismProperty.id_mem (HomotopyCategory.quasiIso 𝒜 (up ℤ)) Y)
        f ⟨by simp⟩).w.symm

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): the brutal bounded-support case should
be proved by induction on the width of the support interval, peeling off one term with stupid
truncation triangles. -/
lemma computesRightDerivedAt_of_strict_bounds_termwise_rightAcyclic
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n : ℤ, IsRightAcyclicForAdditiveFunctor F (K.X n)) :
    ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- TODO: follow the source proof with brutal truncations `σ_{≤ a}` and `σ_{≥ a + 1}`.
  -- The remaining blocker is a reusable homotopy-category triangle API for those stupid
  -- truncations, so that Lemmas `13.14.6` and `13.14.12` can run the bounded-support induction.
  sorry

/-- Helper for Lemma 13.16.7 (Leray's acyclicity lemma): once the bounded-support case is known,
each bounded-below termwise right-acyclic complex computes `RF` by comparing it degreewise with
its upper truncations. -/
lemma computesRightDerivedAt_obj_of_termwise_rightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj)
    (hA : IsTermwiseRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KtoD Qis A.obj := by
  -- The fixed-degree comparison is now reduced to the bounded-support computation step.
  -- The naturality square for the identity legs is packaged by
  -- `rightDerivedValueLeg_id_naturality`.
  -- TODO: compute the bounded-support truncation by the first helper above, then combine those
  -- comparisons with the missing source-side truncation/homology adapter and
  -- `rightDerivedValue_homologyMap_isIso_of_truncLE` to conclude.
  sorry

/- Domain-style sampling for Lemma 13.16.7:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, and the Leray criterion that termwise right-acyclic bounded-below complexes already
  compute the derived value;
- sampled owner declarations:
  `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`;
- best owner abstraction: the source-facing owner here is the pointwise computation predicate
  `ComputesRightDerivedAt KplusToDplus QisPlus A`; the termwise acyclicity hypothesis should be
  expressed directly using the chapter owner
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- primitive data: a bounded-below homotopy object `A`, pointwise right-derived-definedness at `A`,
  and the termwise bounded-below right-acyclicity predicate
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A`;
- derived API: the Leray comparison theorem below, asserting that `A` computes the bounded-below
  right derived functor.

Source/core/bridge triage:
- `source-facing`: the Leray acyclicity criterion for bounded-below complexes;
- `core/canonical`: `HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus`,
  `ComputesRightDerivedAt KplusToDplus QisPlus`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the bounded/unbounded comparison results from Lemma `13.15.2` and Proposition
  `13.16.8`, which should reuse this owner-level criterion rather than replace it.
-/

-- Proof sketch: argue first for bounded complexes by induction on the amplitude, using stupid
-- truncation triangles and Lemma `13.14.12` together with the fact that a single right
-- `F`-acyclic object computes the bounded-below right derived functor by Definition `13.15.3`.
-- Then truncate a bounded-below complex above degree `i + 1`, compare the long exact cohomology
-- sequences for `F(A^•)` and `RF(A^•)`, and use Lemma `13.16.1` to see that the higher
-- truncation contributes no cohomology in degrees `i` and `i + 1`.
/-- Lemma 13.16.7 (Leray's acyclicity lemma): if `A^•` is a bounded-below complex whose every term
is right acyclic for the bounded-below right derived functor of `F`, and if that right derived
functor is defined at `A^•`, then `A^•` computes the bounded-below right derived functor of `F`,
formalized by `ComputesRightDerivedAt KplusToDplus QisPlus A`. Equivalently, the canonical map
`F(A^•) ⟶ RF(A^•)` is an isomorphism in `D^+(\mathcal B)`. -/
theorem computesRightDerivedAt_of_termwise_boundedBelowRightAcyclic
    (A : K⁺(𝒜))
    (hder : HasPointwiseRightDerivedFunctorAt KplusToDplus QisPlus A)
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    ComputesRightDerivedAt KplusToDplus QisPlus A := by
  -- Route correction: the viable proof route is to pass to the unbounded homotopy category,
  -- prove the bounded-support part there using truncation triangles, and then transport the
  -- resulting computation back to `K^+`.
  have hA' : IsTermwiseRightAcyclicForAdditiveFunctor F A :=
    isTermwiseRightAcyclic_of_termwise_boundedBelowRightAcyclic (F := F) A hA
  have hder' : HasPointwiseRightDerivedFunctorAt KtoD Qis A.obj := by
    exact (right_derived_defined_at_iff_bounded_below (F := F) A).2 hder
  have hcompute' : ComputesRightDerivedAt KtoD Qis A.obj :=
    computesRightDerivedAt_obj_of_termwise_rightAcyclic (F := F) A hder' hA'
  -- The final step is the bounded/unbounded comparison from Lemma `13.15.2`.
  exact (computes_right_derived_functor_at_iff_bounded_below (F := F) A).1 hcompute'

end

end CategoryTheory

/-! ### Proposition_13_16_8 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

/- Domain-style sampling for Proposition 13.16.8:
- primary domain: bounded-below / bounded-above derived-functor existence and computation from
  acyclic resolutions in an abelian category;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction: Proposition `13.16.8` is source-facing and bounded. Its acyclicity
  hypotheses should therefore be organized around the Chapter `13` owners
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor F`, and
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F`, while the mono/epi reachability
  hypotheses are canonically owned by `ObjectProperty.HasMonoEmbedding` and
  `ObjectProperty.HasEpiCover`;
- primitive data: the additive functor `F` and the bounded mono/epi reachability owners for those
  bounded acyclicity predicates;
- derived API: pointwise and total bounded derived-functor existence, plus the computation
  theorems for termwise bounded-acyclic complexes.

Source/core/bridge triage:
- `source-facing`: the four bounded derived-functor existence statements and the two computation
  statements below;
- `core/canonical`: `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`,
  `IsBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`, and `ObjectProperty.HasEpiCover`;
- `bridge/view`: the bounded/unbounded comparison lemmas from `13.15.2`, which remain stronger
  companion transport API rather than the main public surface here.
-/

section Right

local notation "BoundedBelowRightAcyclic" =>
  (fun A : 𝒜 ↦ IsBoundedBelowRightAcyclicForAdditiveFunctor F A)

-- Proof sketch: resolve any bounded-below complex termwise by a quasi-isomorphic bounded-below
-- complex of bounded-below right `F`-acyclic objects using the mono-embedding hypothesis
-- degreewise and the
-- bounded-below resolution lemma. Then quasi-isomorphisms between such termwise right-acyclic
-- complexes are sent to quasi-isomorphisms, so Lemma `13.14.15` yields pointwise existence of
-- the bounded-below right derived functor at every object of `K^+(\mathcal A)`.
/-- Proposition 13.16.8: if every object of `𝒜` admits a monomorphism into an object that is
acyclic for the bounded-below right derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasMonoEmbedding BoundedBelowRightAcyclic`, then the bounded-below right derived
functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KplusToDplus.HasPointwiseRightDerivedFunctor QisPlus`. -/
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus := sorry

/-- Corollary: under the hypotheses of Proposition 13.16.8, the bounded-below total right
derived functor exists. -/
theorem boundedBelow_hasRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic
    [HasMonoEmbedding BoundedBelowRightAcyclic] :
    Functor.HasRightDerivedFunctor KplusToDplus QisPlus := by
  let _ : Functor.HasPointwiseRightDerivedFunctor KplusToDplus QisPlus :=
    boundedBelow_hasPointwiseRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic F
  infer_instance

-- Proof sketch: this is the bounded Leray acyclicity criterion of Lemma `13.16.7`, expressed
-- directly with the owner `IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor`.
/-- Any bounded-below complex whose terms are acyclic for the bounded-below right derived functor
computes the bounded-below right derived functor. -/
theorem computesRightDerivedFunctorAt_of_termwise_boundedBelowRightAcyclic
    [Functor.HasRightDerivedFunctor KplusToDplus QisPlus]
    (A : K⁺(𝒜))
    (hA : IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F A) :
    Functor.ComputesRightDerivedAt KplusToDplus QisPlus A := sorry

end Right

section Left

local notation "BoundedAboveLeftAcyclic" =>
  IsBoundedAboveLeftAcyclicForAdditiveFunctor F

-- Proof sketch: dualize the bounded-below argument. Use the epi-cover hypothesis by
-- bounded-above left-acyclic objects to choose bounded-above resolutions, then apply the dual
-- form of
-- Lemma `13.14.15` to obtain pointwise existence of the bounded-above left derived functor at
-- every object.
/-- If every object of `𝒜` is a quotient of an object that is acyclic for the bounded-above left
derived functor of `F`, formalized by the canonical owner
`ObjectProperty.HasEpiCover BoundedAboveLeftAcyclic`, then the bounded-above left derived
functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is everywhere defined in the canonical pointwise
sense `KminusToDminus.HasPointwiseLeftDerivedFunctor QisMinus`. -/
theorem boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus := sorry

/-- Corollary: under the dual hypotheses of Proposition 13.16.8, the bounded-above total left
derived functor exists. -/
theorem boundedAbove_hasLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic
    [HasEpiCover BoundedAboveLeftAcyclic] :
    Functor.HasLeftDerivedFunctor KminusToDminus QisMinus := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KminusToDminus QisMinus :=
    boundedAbove_hasPointwiseLeftDerivedFunctor_of_epi_from_boundedAboveLeftAcyclic F
  infer_instance

-- Proof sketch: this is the bounded-above dual of the bounded Leray acyclicity criterion,
-- expressed directly with the owner
-- `IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor`.
/-- Any bounded-above complex whose terms are acyclic for the bounded-above left derived functor
computes the bounded-above left derived functor. -/
theorem computesLeftDerivedFunctorAt_of_termwise_boundedAboveLeftAcyclic
    [Functor.HasLeftDerivedFunctor KminusToDminus QisMinus]
    (A : K⁻(𝒜))
    (hA : IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor F A) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus A := sorry

end Left

end

end CategoryTheory
