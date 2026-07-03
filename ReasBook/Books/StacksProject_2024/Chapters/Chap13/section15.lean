import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_15_2 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Lemma 13.15.2:
- primary domain: comparison of pointwise derived-functor computation between the unbounded
  homotopy localization `K(\mathcal A) ⟶ D(\mathcal B)` and its bounded-below / bounded-above
  full-subcategory views;
- sampled owner declarations:
  `LocalizerMorphism.ofEq`,
  `LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure`,
  `LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the bounded inclusions are not second derived-functor owners; they are
  bridge/view localizer morphisms from `Qis⁺(𝒜)` and `Qis⁻(𝒜)` to the ambient quasi-isomorphism
  class `HomotopyCategory.quasiIso 𝒜 (up ℤ)`, and the six statements below are their
  source-facing consequences for pointwise derived functors;
- primitive data: the canonical functors from `Situation_13_15_1`, together with the bounded
  quasi-isomorphism owners `Qis⁺(𝒜)` and `Qis⁻(𝒜)` from `Lemma_13_11_6`;
- derived API: the equivalence of pointwise derived-definedness, the comparison of pointwise
  derived values, and the corresponding `ComputesRightDerivedAt` / `ComputesLeftDerivedAt`
  equivalences.

Source/core/bridge triage:
- `source-facing`: the six bounded-vs-unbounded comparison statements of Lemma `13.15.2`;
- `core/canonical`: the mathlib `LocalizerMorphism` derivability-structure comparison API and the
  Chapter `13` owners `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt`;
- `bridge/view`: the bounded inclusions `K⁺(𝒜) ⥤ K(\mathcal A)` and `K⁻(𝒜) ⥤ K(\mathcal A)`,
  which induce the comparison between the bounded and unbounded derived setups.
-/

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

-- Proof sketch: by Lemma 13.11.5, every quasi-isomorphism out of the bounded-below object `X`
-- can be refined to one whose target is still bounded below. This is exactly the
-- `LocalizerMorphism.ofEq rfl` bridge from `Qis⁺(𝒜)` to `Qis`, together with the canonical
-- right-derivability-structure comparison API, so the pointwise right-derived existence condition
-- is unchanged.
/-- Lemma 13.15.2 (1): for a bounded-below object `X` of `K^+(\mathcal A)`, the right derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the right derived functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is defined at `X`. -/
theorem right_derived_defined_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X := sorry

-- Proof sketch: once both pointwise right-derived values exist, the localizer-morphism bridge
-- `LocalizerMorphism.ofEq rfl` for `Qis⁺(𝒜) ⟶ Qis` and the canonical derivability-structure
-- comparison supply the comparison morphism; its invertibility is exactly the pointwise
-- comparison encoded by `LocalizerMorphism.rightDerivedFunctorComparison`. The bounded-below
-- value is viewed in `D(\mathcal B)` through the canonical full-subcategory inclusion
-- `D^+(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (2): when the right-derived values at a bounded-below object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^+(\mathcal B)`. -/
noncomputable def right_derived_value_comparison_iso_bounded_below
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X] :
    rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj := sorry

-- Proof sketch: combine the equivalence of pointwise right-derived existence with the canonical
-- `isIso_iff_of_isRightDerivabilityStructure` comparison for the identity legs.
/-- Lemma 13.15.2 (3): a bounded-below object `X` computes the right derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`. -/
theorem computes_right_derived_functor_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := sorry

-- Proof sketch: this is the dual argument to part (1). Lemma 13.11.5 furnishes bounded-above
-- refinements of quasi-isomorphisms into `X`; equivalently, `LocalizerMorphism.ofEq rfl` from
-- `Qis⁻(𝒜)` to `Qis` is the left-derivability-structure bridge, so pointwise left-derived
-- existence is unchanged.
/-- Lemma 13.15.2 (4): for a bounded-above object `X` of `K^-(\mathcal A)`, the left derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the left derived functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is defined at `X`. -/
theorem left_derived_defined_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X := sorry

-- Proof sketch: after both pointwise left-derived values are defined, the localizer-morphism
-- bridge `LocalizerMorphism.ofEq rfl` for `Qis⁻(𝒜) ⟶ Qis` identifies the bounded-above and
-- unbounded structured-arrow diagrams, and the resulting canonical comparison morphism is the one
-- whose invertibility is tracked by the left-derived derivability-structure API. The
-- bounded-above value is viewed in `D(\mathcal B)` through the canonical full-subcategory
-- inclusion `D^-(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (5): when the left-derived values at a bounded-above object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^-(\mathcal B)`. -/
noncomputable def left_derived_value_comparison_iso_bounded_above
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X] :
    leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj := sorry

-- Proof sketch: combine the equivalence of pointwise left-derived existence with the comparison
-- of the canonical pointwise counit morphisms under the derived-structure bridge.
/-- Lemma 13.15.2 (6): a bounded-above object `X` computes the left derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the left derived functor of
`K^-(\mathcal A) ⥤ D^-(\mathcal B)`. -/
theorem computes_left_derived_functor_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := sorry

end

end CategoryTheory

/-! ### Definition_13_15_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Functor
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]

/- 
Domain-style sampling for Definition 13.15.3:
- primary domain: partial derived functors on `K⁺(𝒜)` and `K⁻(𝒜)` together with degree-zero
  acyclicity for derived functors;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`,
  `HomotopyCategory.singleFunctor`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the canonical partial derived-functor owners
  `Functor.totalRightDerived` and `Functor.totalLeftDerived`, specialized to the bounded-below and
  bounded-above localization functors from Situation `13.15.1`, together with the canonical
  degree-zero embedding `single0 : 𝒜 ⥤ K(𝒜)` and its bounded lifts `single0Plus 𝒜` and
  `single0Minus 𝒜`;
- primitive data: the canonical bounded degree-zero objects `(single0Plus 𝒜).obj A` and
  `(single0Minus 𝒜).obj A`, plus the bounded localization functors
  `mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)` and
  `mapBoundedAboveHomotopyCategoryToDerivedAbove (𝟭 𝒜)`;
- derived API: the bounded-below degree-zero bridge `single0ToDplus`, the source-facing partial
  derived functors from clauses `(1)` and `(2)`, and the four acyclicity predicates from clauses
  `(3)` and `(4)`.

Source/core/bridge triage:
- `source-facing`: the partial bounded derived functors and the acyclicity predicates for an
  additive functor on objects of `𝒜`;
- `core/canonical`: `Functor.totalRightDerived`, `Functor.totalLeftDerived`, the degree-zero
  owners in `K(𝒜)`, `K⁺(𝒜)`, `K⁻(𝒜)`, and `Functor.ComputesRightDerivedAt` /
  `Functor.ComputesLeftDerivedAt`;
- `bridge/view`: the bounded degree-zero bridge `single0ToDplus` and the bounded/unbounded
  comparisons from Lemma `13.15.2`, not second owner abstractions.
-/

local notation "single0" => HomotopyCategory.singleFunctor 𝒜 0

variable (𝒜)

/-- The degree-zero embedding `\mathcal A ⥤ K^+(\mathcal A)`. -/
abbrev single0Plus : 𝒜 ⥤ K⁺(𝒜) :=
  ObjectProperty.lift (HomotopyCategory.plus 𝒜) single0
    (fun A ↦ by
      simpa using
        (show CochainComplex.plus 𝒜 ((CochainComplex.singleFunctor 𝒜 0).obj A) from
          ⟨0, inferInstance⟩))

/-- The degree-zero embedding `\mathcal A ⥤ K^-(\mathcal A)`. -/
abbrev single0Minus : 𝒜 ⥤ K⁻(𝒜) :=
  ObjectProperty.lift (HomotopyCategory.minus 𝒜) single0
    (fun A ↦ by
      simpa using
        (show CochainComplex.minus 𝒜 ((CochainComplex.singleFunctor 𝒜 0).obj A) from
          ⟨0, inferInstance⟩))

end

section

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (𝒜)

/-- The canonical bounded-below degree-zero embedding `\mathcal A ⥤ D^+(\mathcal A)`. -/
abbrev single0ToDplus : 𝒜 ⥤ D⁺(𝒜) :=
  single0Plus 𝒜 ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F
local notation "single0" => HomotopyCategory.singleFunctor 𝒜 0

section PartialDerived

local notation "DplusQ" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "DminusQ" => mapBoundedAboveHomotopyCategoryToDerivedAbove (𝟭 𝒜)

section Right

variable
  [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
    (boundedBelowHomotopyQuasiIso 𝒜)]
variable [Functor.HasRightDerivedFunctor KplusToDplus QisPlus]

/- Definition 13.15.3 (1): the bounded-below partial right derived functor attached to Situation
`13.15.1` is the canonical specialization of `Functor.totalRightDerived`. -/
recall Functor.totalRightDerived

/- In the bounded-below situation, this owner is
`(mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived DplusQ QisPlus`. -/
#check
  ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived DplusQ QisPlus :
    boundedBelowDerivedCategory 𝒜 ⥤ boundedBelowDerivedCategory ℬ)

end Right

section Left

variable
  [(mapBoundedAboveHomotopyCategoryToDerivedAbove (𝟭 𝒜)).IsLocalization
    (boundedAboveHomotopyQuasiIso 𝒜)]
variable [Functor.HasLeftDerivedFunctor KminusToDminus QisMinus]

/- Definition 13.15.3 (2): the bounded-above partial left derived functor attached to Situation
`13.15.1` is the canonical specialization of `Functor.totalLeftDerived`. -/
recall Functor.totalLeftDerived

/- In the bounded-above situation, this owner is
`(mapBoundedAboveHomotopyCategoryToDerivedAbove F).totalLeftDerived DminusQ QisMinus`. -/
#check
  ((mapBoundedAboveHomotopyCategoryToDerivedAbove F).totalLeftDerived DminusQ QisMinus :
    boundedAboveDerivedCategory 𝒜 ⥤ boundedAboveDerivedCategory ℬ)

end Left

end PartialDerived

/-- Definition 13.15.3 (3): an object `A` is right acyclic for the bounded-below right derived
functor of an additive functor `F` when the degree-zero complex `A[0]` computes that derived
functor. -/
abbrev IsBoundedBelowRightAcyclicForAdditiveFunctor
    (A : 𝒜) : Prop :=
  ComputesRightDerivedAt KplusToDplus QisPlus ((single0Plus 𝒜).obj A)

/-- An object `A` is right acyclic for the unbounded right derived functor of `F` when the
degree-zero complex `A[0]` computes that right derived functor. -/
abbrev IsRightAcyclicForAdditiveFunctor
    (A : 𝒜) : Prop :=
  ComputesRightDerivedAt KtoD Qis ((HomotopyCategory.singleFunctor 𝒜 0).obj A)

/-- A bounded-below homotopy object is termwise right acyclic for the bounded-below right derived
functor of `F` when each of its cochain terms is. -/
abbrev IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor
    (A : K⁺(𝒜)) : Prop :=
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  ∀ n : ℤ, IsBoundedBelowRightAcyclicForAdditiveFunctor F (K.X n)

/-- A bounded-below homotopy object is termwise right acyclic for the unbounded right derived
functor of `F` when each of its cochain terms is. -/
abbrev IsTermwiseRightAcyclicForAdditiveFunctor
    (A : K⁺(𝒜)) : Prop :=
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  ∀ n : ℤ, IsRightAcyclicForAdditiveFunctor F (K.X n)

/-- Definition 13.15.3 (4): an object `A` is left acyclic for the bounded-above left derived
functor of `F` when the
degree-zero complex `A[0]` computes that derived functor. -/
abbrev IsBoundedAboveLeftAcyclicForAdditiveFunctor
    (A : 𝒜) : Prop :=
  ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A)

/-- An object `A` is left acyclic for the unbounded left derived functor of `F` when the
degree-zero complex `A[0]` computes that left derived functor. -/
abbrev IsLeftAcyclicForAdditiveFunctor
    (A : 𝒜) : Prop :=
  ComputesLeftDerivedAt KtoD Qis ((HomotopyCategory.singleFunctor 𝒜 0).obj A)

/-- A bounded-above homotopy object is termwise left acyclic for the bounded-above left derived
functor of `F` when each of its cochain terms is. -/
abbrev IsTermwiseBoundedAboveLeftAcyclicForAdditiveFunctor
    (A : K⁻(𝒜)) : Prop :=
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  ∀ n : ℤ, IsBoundedAboveLeftAcyclicForAdditiveFunctor F (K.X n)

/-- A bounded-above homotopy object is termwise left acyclic for the unbounded left derived
functor of `F` when each of its cochain terms is. -/
abbrev IsTermwiseLeftAcyclicForAdditiveFunctor
    (A : K⁻(𝒜)) : Prop :=
  let K : CochainComplex 𝒜 ℤ := A.obj.as
  ∀ n : ℤ, IsLeftAcyclicForAdditiveFunctor F (K.X n)

end

end CategoryTheory

/-! ### Lemma_13_15_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 13.15.4:
- primary domain: bounded-above replacements of cochain complexes by complexes whose terms lie in
  an object property, together with quasi-isomorphisms and degreewise epimorphy;
- sampled owner declarations in this domain:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `CochainComplex.Minus`,
  `CochainComplex.Minus.ι`,
  `CochainComplex.minus`,
  `QuasiIso`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction:
  `CochainComplex.MinusWithTermsIn P` should be the full subcategory of the canonical bounded-above
  owner `CochainComplex.Minus A` cut out by the termwise `P`-condition, with owner inclusion
  `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A`; the two predicates below are the
  source-facing layer adding the comparison morphism and its quasi-isomorphism / epimorphism
  properties, while the owner conversion `toMinusWithTermsIn` remains a bridge;
- primitive-vs-derived split:
  primitive data are the comparison morphism `α : Q ⟶ K` together with the three source-faithful
  properties `QuasiIso α`, `Q.IsStrictlyLE a`, and the termwise predicate
  `term_mem (n : ℤ) : P (Q.X n)`;
  the termwise-epimorphic variant adds the source-facing degreewise epimorphism predicate
  `term_epi (n : ℤ) : Epi (α.f n)`, while any complex-level `Epi α` fact is derived API from the
  canonical owner lemma `HomologicalComplex.epi_of_epi_f`.

Source/core/bridge triage:
- `source-facing`: `IsStrictlyLEQuasiIsoWithTermsIn` and
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn P`, `QuasiIso`, `ObjectProperty.HasEpiCover`,
  and the componentwise `Epi` predicate;
- `bridge/view`: the owner inclusion `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A` and its
  composite with `CochainComplex.Minus.ι A`,
  `IsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn`, and the existence theorems below, which
  package a source-level bounded-above replacement into these owner predicates.
-/

namespace CochainComplex

section

variable [HasZeroMorphisms A]

/-- The bounded-above cochain complexes whose terms satisfy the object property `P`. -/
abbrev MinusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Minus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace MinusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (MinusWithTermsIn P) (Minus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (MinusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-above cochain complexes with terms in `P` into all cochain
complexes. -/
abbrev ι (P : ObjectProperty A) : MinusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Minus.ι A

/-- A bounded-above cochain complex with terms in `P` is bounded above. -/
theorem minus {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    CochainComplex.minus A (K : CochainComplex A ℤ) := by
  simpa using (K : Minus A).property

/-- Each term of a bounded-above cochain complex with terms in `P` again satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : MinusWithTermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := by
  simpa using K.property n

/-- A bounded-above cochain complex with terms in `P` is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    ∃ b : ℤ, (K : CochainComplex A ℤ).IsStrictlyLE b :=
  (CochainComplex.minus_iff A (K : CochainComplex A ℤ)).1 K.minus

end MinusWithTermsIn

end

end CochainComplex

section

variable [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex whose terms satisfy
the object property `P` and which is quasi-isomorphic to `K`. -/
structure IsStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop where
  quasiIso : QuasiIso α
  strictlyLE : Q.IsStrictlyLE a
  term_mem (n : ℤ) : P (Q.X n)

namespace IsStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- The source-facing bounded-above replacement data canonically packages its resolving complex as
an element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  ⟨⟨Q, (CochainComplex.minus_iff A Q).2 ⟨a, h.strictlyLE⟩⟩, h.term_mem⟩

end IsStrictlyLEQuasiIsoWithTermsIn

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex with terms in `P`
which is quasi-isomorphic to `K` and termwise epimorphic. -/
structure IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop extends
    IsStrictlyLEQuasiIsoWithTermsIn P a K Q α where
  term_epi (n : ℤ) : Epi (α.f n)

namespace IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- A termwise-epimorphic morphism of cochain complexes is epimorphic as a morphism of
complexes. -/
theorem epi (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) : Epi α :=
  epi_of_epi_f α h.term_epi

/-- The termwise-epimorphic bounded-above replacement data packages its resolving complex as an
element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  h.toIsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn

end IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

end

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]

-- Proof sketch: argue by descending induction on the degree. At stage `n - 1`, choose an
-- epimorphism from an object of `P` onto the pullback `K.X (n - 1) ×_{K.X n} ker(d_Q^n)`, then
-- extend the partial complex and comparison map. The inductive construction yields a bounded-above
-- complex `Q` with terms in `P`, a termwise-epimorphic map `Q ⟶ K`, and a quasi-isomorphism.
/-- Lemma 13.15.4 (1): if a cochain complex `K` is zero in degrees above `a`, then there exists a
bounded-above cochain complex `Q` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `Q ⟶ K` that is termwise epimorphic. -/
theorem exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := sorry

-- Proof sketch: first replace `K` by the stupid truncation `K.truncLE a`, which is
-- quasi-isomorphic to `K` under the vanishing of homology above `a`. Then apply part (1) to the
-- bounded-above complex `K.truncLE a` and compose the resulting quasi-isomorphism with
-- `K.ιTruncLE a`.
/-- Lemma 13.15.4 (2): if the homology of a cochain complex `K` vanishes in degrees above `a`,
then there exists a bounded-above cochain complex `Q` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `Q ⟶ K`. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_above
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsStrictlyLEQuasiIsoWithTermsIn P a K Q α := sorry

end

/-! ### Lemma_13_15_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

namespace CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A]

/-- An object property has mono embeddings if every object admits a monomorphism into an object
satisfying the property. -/
class HasMonoEmbedding (P : ObjectProperty A) : Prop where
  exists_mono (X : A) : ∃ Y : A, P Y ∧ ∃ f : X ⟶ Y, Mono f

-- Proof sketch: take `Y = X` and the identity morphism, which is monic.
/-- The maximal object property has mono embeddings, using the identity monomorphism of each
object. -/
instance instHasMonoEmbeddingTop : HasMonoEmbedding (⊤ : ObjectProperty A) := sorry

end CategoryTheory.ObjectProperty

open CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 13.15.5:
- primary domain: bounded-below replacements of cochain complexes by complexes whose terms lie in
  an object property, together with quasi-isomorphisms and degreewise monomorphy;
- sampled owner declarations:
  `ObjectProperty.HasEpiCover`,
  `IsStrictlyGEWithTermsIn`,
  `IsTermwiseMonoStrictlyGEWithTermsIn`,
  `IsStrictlyLEQuasiIsoWithTermsIn`,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction:
  `ObjectProperty.HasMonoEmbedding` is the primitive object-property owner for the existence
  hypothesis, while `IsStrictlyGEWithTermsIn` and `IsTermwiseMonoStrictlyGEWithTermsIn` are the
  primitive bundled-target bounded-below stage owners and
  `IsStrictlyGEQuasiIsoWithTermsIn` / `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn` are the
  source-facing quasi-isomorphic refinements;
- primitive data:
  the comparison morphism `α : K ⟶ I` together with `QuasiIso α`, `I.IsStrictlyGE a`, and the
  termwise property `∀ n, P (I.X n)`;
- derived API:
  the quasi-isomorphic refinements and the two existence theorems below.

Source/core/bridge triage:
- `source-facing`: the two quasi-isomorphic bounded-below stage predicates and existence theorems
    below;
- `core/canonical`: `QuasiIso`, `I.IsStrictlyGE a`, `ObjectProperty.HasMonoEmbedding`, and the
  bundled-target owners `IsStrictlyGEWithTermsIn` / `IsTermwiseMonoStrictlyGEWithTermsIn`;
- `bridge/view`: downstream constructions such as lower truncation resolution systems, which should
  reuse these owners rather than redefine them.
-/

namespace CochainComplex

section

variable [HasZeroMorphisms A]

/-- The bounded-below cochain complexes whose terms satisfy the object property `P`. -/
abbrev PlusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Plus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace PlusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (PlusWithTermsIn P) (Plus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (PlusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-below cochain complexes with terms in `P` into all cochain
complexes. -/
abbrev ι (P : ObjectProperty A) : PlusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Plus.ι A

/-- A bounded-below cochain complex with terms in `P` is bounded below. -/
theorem plus {P : ObjectProperty A} (K : PlusWithTermsIn P) :
    CochainComplex.plus A (K : CochainComplex A ℤ) := by
  simpa using (K : Plus A).property

/-- Each term of a bounded-below cochain complex with terms in `P` again satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : PlusWithTermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := by
  simpa using K.property n

/-- A bounded-below cochain complex with terms in `P` is zero in all sufficiently negative
degrees. -/
theorem exists_isStrictlyGE {P : ObjectProperty A} (K : PlusWithTermsIn P) :
    ∃ a : ℤ, (K : CochainComplex A ℤ).IsStrictlyGE a :=
  (CochainComplex.plus_iff A (K : CochainComplex A ℤ)).1 K.plus

end PlusWithTermsIn

end

end CochainComplex

section

variable [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A morphism `α : K ⟶ I` into a bounded-below complex whose terms satisfy `P` records only the
primitive bounded-below stage data carried by the owner `CochainComplex.PlusWithTermsIn P`. -/
structure IsStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ I) : Prop where
  strictlyGE : (I : CochainComplex A ℤ).IsStrictlyGE a

/-- A morphism `α : K ⟶ I` into a bounded-below complex with terms in `P` is termwise
monomorphic if each degree component is monic. -/
structure IsTermwiseMonoStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ I) : Prop extends
    IsStrictlyGEWithTermsIn P a I α where
  term_mono (n : ℤ) : Mono (α.f n)

/-- A morphism `α : K ⟶ I` exhibits `I` as a bounded-below cochain complex whose terms satisfy the
object property `P` and which is quasi-isomorphic to `K`. -/
structure IsStrictlyGEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop where
  quasiIso : QuasiIso α
  strictlyGE : I.IsStrictlyGE a
  term_mem (n : ℤ) : P (I.X n)

/-- A morphism `α : K ⟶ I` exhibits `I` as a bounded-below cochain complex with terms in `P`
which is quasi-isomorphic to `K` and termwise monomorphic. -/
structure IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop extends
    IsStrictlyGEQuasiIsoWithTermsIn P a K I α where
  term_mono (n : ℤ) : Mono (α.f n)

namespace IsStrictlyGEWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}
variable {I : CochainComplex.PlusWithTermsIn P} {α : K ⟶ I}

/-- The primitive bounded-below stage data already packages its target as an element of the owner
`CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsStrictlyGEWithTermsIn P a I α) :
    CochainComplex.PlusWithTermsIn P :=
  I

end IsStrictlyGEWithTermsIn

namespace IsTermwiseMonoStrictlyGEWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}
variable {I : CochainComplex.PlusWithTermsIn P} {α : K ⟶ I}

/-- A termwise-monomorphic morphism of cochain complexes is monomorphic as a morphism of
complexes. -/
theorem mono (h : IsTermwiseMonoStrictlyGEWithTermsIn P a I α) : Mono α :=
  HomologicalComplex.mono_of_mono_f α h.term_mono

/-- The primitive termwise-monomorphic bounded-below stage data keeps the same bundled target. -/
abbrev toPlusWithTermsIn (h : IsTermwiseMonoStrictlyGEWithTermsIn P a I α) :
    CochainComplex.PlusWithTermsIn P :=
  I

end IsTermwiseMonoStrictlyGEWithTermsIn

namespace IsStrictlyGEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

/-- The source-facing bounded-below replacement data canonically packages its resolving complex as
an element of the owner `CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    CochainComplex.PlusWithTermsIn P :=
  ⟨⟨I, (CochainComplex.plus_iff A I).2 ⟨a, h.strictlyGE⟩⟩, h.term_mem⟩

/-- Forgetting the quasi-isomorphism keeps only the primitive bounded-below stage data owned by
`CochainComplex.PlusWithTermsIn P`. -/
abbrev toIsStrictlyGEWithTermsIn (h : IsStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    IsStrictlyGEWithTermsIn P a h.toPlusWithTermsIn α where
  strictlyGE := h.strictlyGE

end IsStrictlyGEQuasiIsoWithTermsIn

namespace IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

/-- Forgetting the quasi-isomorphism keeps only the primitive bounded-below termwise-monomorphic
stage data owned by `CochainComplex.PlusWithTermsIn P`. -/
abbrev toIsTermwiseMonoStrictlyGEWithTermsIn
    (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    IsTermwiseMonoStrictlyGEWithTermsIn P a h.toIsStrictlyGEQuasiIsoWithTermsIn.toPlusWithTermsIn α where
  toIsStrictlyGEWithTermsIn := h.toIsStrictlyGEQuasiIsoWithTermsIn.toIsStrictlyGEWithTermsIn
  term_mono := h.term_mono

/-- A termwise-monomorphic morphism of cochain complexes is monomorphic as a morphism of
complexes. -/
theorem mono (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) : Mono α :=
  h.toIsTermwiseMonoStrictlyGEWithTermsIn.mono

/-- The termwise-monomorphic bounded-below replacement data packages its resolving complex as an
element of the owner `CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    CochainComplex.PlusWithTermsIn P :=
  h.toIsStrictlyGEQuasiIsoWithTermsIn.toPlusWithTermsIn

end IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn

end

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasMonoEmbedding]

-- Proof sketch: argue by ascending induction on the degree. At stage `n + 1`, choose a
-- monomorphism from the cokernel of the partial differential into an object of `P`, splice this
-- into the next term, and extend the comparison map. The inductive construction yields a
-- bounded-below complex `I` with terms in `P`, a termwise-monomorphic map `K ⟶ I`, and a
-- quasi-isomorphism.
/-- Lemma 13.15.5 (1): if a cochain complex `K` is zero in degrees below `a`, then there exists a
bounded-below cochain complex `I` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `K ⟶ I` that is termwise monomorphic. -/
theorem exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α := sorry

-- Proof sketch: first replace `K` by the stupid truncation `K.truncGE a`, which is
-- quasi-isomorphic to `K` under the vanishing of homology below `a`. Then apply part (1) to the
-- bounded-below complex `K.truncGE a` and compose `K.πTruncGE a` with the resulting
-- quasi-isomorphism.
/-- Lemma 13.15.5 (2): if the homology of a cochain complex `K` vanishes in degrees below `a`,
then there exists a bounded-below cochain complex `I` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `K ⟶ I`. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_below
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      IsStrictlyGEQuasiIsoWithTermsIn P a K I α := sorry

end

/-! ### Lemma_13_15_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Lemma 13.15.6:
- primary domain: bounded-below right-derived acyclicity obtained from bounded-below resolutions
  by a chosen object property `P`;
- sampled owner declarations:
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`,
  `Functor.ComputesRightDerivedAt`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.computesRightDerivedAt_of_mem_subset`;
- best owner abstraction: the source-facing data here is the object property `P` together with the
  exactness hypothesis; the canonical owner for the embedding hypothesis is
  `ObjectProperty.HasMonoEmbedding`, the canonical owner for closure under quotients is
  `ObjectProperty.IsClosedUnderQuotients`, and the target acyclicity notion is the chapter owner
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- primitive data: `P`, the mono-embedding owner for `P`, the quotient-closure owner for `P`,
  and the hypothesis that `F` preserves short exactness on those short complexes;
- derived API: the acyclicity statement for the degree-zero object `A[0]` in `K⁺(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, specialized to objects `A ∈ P`;
- `core/canonical`: `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`, `Functor.ComputesRightDerivedAt`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: this theorem, which turns the source-facing object-property hypotheses into the
  canonical bounded-below acyclicity owner. -/

-- Proof sketch: apply Lemma 13.15.5 to produce, from any bounded-below complex, a
-- quasi-isomorphic bounded-below complex whose terms lie in `P`. The short-exact-sequence
-- hypotheses first imply that `P` contains a zero object, so Lemma 13.15.5 applies to produce,
-- from any bounded-below complex, a quasi-isomorphic bounded-below complex whose terms lie in
-- `P`. The short-exact-sequence hypotheses imply that applying `F` to such a resolution remains
-- exact, so quasi-isomorphisms between these resolutions become isomorphisms after applying `F`.
-- Lemma 13.14.15 then shows that every degree-zero object `A[0]` with `A ∈ P` computes the
-- pointwise right derived functor.
/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`, i.e. the degree-zero complex `A[0]` computes that pointwise right derived functor. -/
private instance containsZero_of_hasMonoEmbedding_and_isClosedUnderQuotients
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients] :
    P.ContainsZero where
  exists_zero := by
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasMonoEmbedding).exists_mono (0 : 𝒜)
    let S : ShortComplex 𝒜 := ShortComplex.mk (𝟙 Y) (0 : Y ⟶ 0) (by simp)
    have hS : S.ShortExact := by
      refine ShortComplex.Splitting.shortExact ?_
      exact
        { r := 𝟙 Y
          s := 0
          f_r := by simp [S]
          s_g := by simp [S]
          id := by simp [S] }
    exact ⟨0, isZero_zero 𝒜, by simpa [S] using P.prop_X₃_of_shortExact hS hY⟩

/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A := sorry

end

end CategoryTheory

/-! ### Lemma_13_15_7 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Limits
open ComplexShape
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F
local notation "single0" => HomotopyCategory.singleFunctor 𝒜 0

/- 
Domain-style sampling for Lemma 13.15.7:
- primary domain: unbounded left-derived acyclicity obtained from bounded-above resolutions by a
  chosen object property `P`;
- sampled owner declarations:
  `ObjectProperty.HasEpiCover`,
  `ObjectProperty.IsClosedUnderSubobjects`,
  `ObjectProperty.prop_X₁_of_shortExact`,
  `Functor.ComputesLeftDerivedAt`,
  `IsLeftAcyclicForAdditiveFunctor`,
  `computesLeftDerivedAt_of_mem_subset` and
  `computes_left_derived_functor_at_iff_bounded_above` from Lemmas `13.14.15` and `13.15.2`;
- best owner abstraction: the source-facing data here is the object property `P` together with the
  quotient-generating hypothesis, the canonical subobject-closure owner for `P`, and the
  short-exact-sequence exactness hypothesis on objects of `P`;
  the target acyclicity notion is the chapter owner `IsLeftAcyclicForAdditiveFunctor`;
- primitive data: `P`, the epi-cover owner for `P`, the canonical subobject-closure owner
  `[P.IsClosedUnderSubobjects]`, and the hypothesis that `F` preserves short exactness on short
  exact sequences whose middle and right terms lie in `P`;
- derived API: the acyclicity statement for the degree-zero object `A[0]` in `K(\mathcal A)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, specialized to objects `A ∈ P`;
- `core/canonical`: `ObjectProperty.HasEpiCover`, `ObjectProperty.IsClosedUnderSubobjects`,
  `Functor.ComputesLeftDerivedAt`, `computesLeftDerivedAt_of_mem_subset`, and
  `IsLeftAcyclicForAdditiveFunctor`;
- `bridge/view`: this theorem, which turns the source-facing object-property hypotheses into the
  canonical unbounded left-acyclicity owner.
-/

private instance containsZero_of_hasEpiCover_and_isClosedUnderSubobjects
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects] :
    P.ContainsZero where
  exists_zero := by
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasEpiCover).exists_epi (0 : 𝒜)
    exact ⟨(0 : 𝒜), isZero_zero 𝒜, P.prop_of_mono (0 : (0 : 𝒜) ⟶ Y) hY⟩

-- Proof sketch: dualize Lemma 13.15.6. Use quotient resolutions by objects of `P` to replace
-- bounded-above complexes by quasi-isomorphic complexes whose terms lie in `P`; the closure and
-- exactness hypotheses imply that applying `F` preserves exactness on those resolutions. This
-- first yields the bounded-above owner-level acyclicity statement.
/-- If every object of `𝒜` is a quotient of an object of `P`, `P` is closed under subobjects, and
`F` preserves short exactness on short exact sequences whose middle and right terms lie in `P`,
then every object `A ∈ P` is acyclic for the bounded-above left derived functor of `F`. -/
theorem isBoundedAboveLeftAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedAboveLeftAcyclicForAdditiveFunctor F A := by
  let _ : MorphismProperty.IsSaturatedMultiplicativeSystem QisMinus := by
    sorry
  let Pminus : ObjectProperty (K⁻(𝒜)) := fun X ↦
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    ∀ n : ℤ, P (K.X n)
  have hP_reaches :
      ∀ X : K⁻(𝒜), ∃ (X' : K⁻(𝒜)) (s : X' ⟶ X), Pminus X' ∧ QisMinus s := by
    intro X
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    obtain ⟨a, hX⟩ := (CochainComplex.minus_iff 𝒜 K).1 X.property
    obtain ⟨Q, α, hα⟩ :=
      exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a K hX
    let Xc : Comp⁻(𝒜) := ⟨K, X.property⟩
    have hXeq : (HomotopyCategory.Minus.quotient 𝒜).obj Xc = X := by
      cases X
      rfl
    let X' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj (hα.toMinusWithTermsIn : Comp⁻(𝒜))
    let α' : (hα.toMinusWithTermsIn : Comp⁻(𝒜)) ⟶ Xc := ⟨α⟩
    let s : X' ⟶ X := by
      simpa [X', hXeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
    refine ⟨X', s, ?_, ?_⟩
    · intro n
      simpa [Pminus, X'] using hα.toMinusWithTermsIn.term_mem n
    · change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map s)
      simpa [s, X', hXeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
  change Functor.ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A)
  have hP_isIso :
      ∀ {X X' : K⁻(𝒜)} (s : X ⟶ X'), Pminus X → Pminus X' → QisMinus s →
        IsIso ((mapBoundedAboveHomotopyCategoryToDerivedAbove F).map s) := by
    sorry
  have hsingle : Pminus ((single0Minus 𝒜).obj A) := by
    have hP0 : P (0 : 𝒜) := by
      obtain ⟨Z, hZ, hPZ⟩ := (inferInstance : P.ContainsZero).exists_zero
      exact P.prop_of_mono hZ.isoZero.inv hPZ
    intro n
    by_cases hn : n = 0
    · subst hn
      simpa [Pminus, HomotopyCategory.quotient_obj_as] using hA
    ·
      let hzero :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n hn
      exact P.prop_of_mono hzero.isoZero.hom hP0
  simpa [IsBoundedAboveLeftAcyclicForAdditiveFunctor, Pminus] using
    (Functor.computesLeftDerivedAt_of_mem_subset
      KminusToDminus QisMinus Pminus hP_reaches hP_isIso hsingle)

-- Proof sketch: apply the bounded-above theorem above and transport the result to the unbounded
-- owner via the canonical comparison theorem `computes_left_derived_functor_at_iff_bounded_above`.
/-- Lemma 13.15.7: if every object of `𝒜` is a quotient of an object of `P`, and `P` is closed
under subobjects, while `F` preserves short exactness on short exact sequences whose middle and
right terms lie in `P`, then every object `A ∈ P` is acyclic for the pointwise unbounded left
derived functor of `F`, i.e. the degree-zero complex `A[0]` computes that left derived functor. -/
theorem isLeftAcyclicForAdditiveFunctor_of_mem_quotient_generating_subset
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsLeftAcyclicForAdditiveFunctor F A := by
  let _ : IsBoundedAboveLeftAcyclicForAdditiveFunctor F A :=
    isBoundedAboveLeftAcyclicForAdditiveFunctor_of_mem F P hF_shortExact A hA
  simpa [IsLeftAcyclicForAdditiveFunctor, IsBoundedAboveLeftAcyclicForAdditiveFunctor] using
    (computes_left_derived_functor_at_iff_bounded_above
      F ((single0Minus 𝒜).obj A)).2 inferInstance

end

end CategoryTheory
