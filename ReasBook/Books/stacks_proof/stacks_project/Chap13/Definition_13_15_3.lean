import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 0157]
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
@[stacks 0157]
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
