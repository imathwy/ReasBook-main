import Mathlib.SetTheory.Cardinal.Basic
import StacksProject_2024.Chap04.Lemma_4_25_1
import StacksProject_2024.Chapters.Chap23.section03

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable (F : DividedPowerRing.{u} ⥤ Type u)

/-- Source-facing owner for Lemma 23.3.3: every element of `F` comes by functoriality from a
divided power ring whose underlying set is bounded by the fixed cardinal `κ`. -/
def HasBoundedElementSources (κ : Cardinal.{u}) : Prop :=
  ∀ ⦃A : DividedPowerRing.{u}⦄ (f : F.obj A),
    ∃ (A' : DividedPowerRing.{u}) (φ : A' ⟶ A) (f' : F.obj A'),
      F.map φ f' = f ∧ Cardinal.mk A' ≤ κ

/-- A bound on source cardinalities remains valid after enlarging the bound. -/
theorem HasBoundedElementSources.mono {κ κ' : Cardinal.{u}}
    (h_small : F.HasBoundedElementSources κ) (hκ : κ ≤ κ') :
    F.HasBoundedElementSources κ' := by
  intro A f
  obtain ⟨A', φ, f', hf, hA'⟩ := h_small f
  exact ⟨A', φ, f', hf, hA'.trans hκ⟩

/-- A bounded-source hypothesis yields a small generating family in the sense of Lemma 4.25.1. -/
theorem HasBoundedElementSources.exists_generating_family {κ : Cardinal.{u}}
    (h_small : F.HasBoundedElementSources κ) :
    ∃ (I : Type (u + 1)) (X : I → DividedPowerRing.{u}) (x : ∀ i : I, F.obj (X i)),
      ∀ ⦃A : DividedPowerRing.{u}⦄ (f : F.obj A), ∃ (i : I) (φ : X i ⟶ A), F.map φ (x i) = f := by
  let I : Type (u + 1) :=
    Σ A' : DividedPowerRing.{u}, { f' : F.obj A' // Cardinal.mk A' ≤ κ }
  let X : I → DividedPowerRing.{u} := fun i ↦ i.1
  let x : ∀ i : I, F.obj (X i) := fun i ↦ i.2.1
  refine ⟨I, X, x, ?_⟩
  intro A f
  obtain ⟨A', φ, f', hf, hA'⟩ := h_small f
  exact ⟨⟨A', ⟨f', hA'⟩⟩, φ, hf⟩

end CategoryTheory.Functor

/-
Source/core/bridge triage for Lemma 23.3.3:
- `source-facing`: the bounded-cardinality hypothesis on elements of `F`;
- `core/canonical`: `F.IsCorepresentable`;
- `bridge/view`: the small generating family built from bounded source objects, then the induced
  initial object of `F.Elements`, and finally the canonical corepresentability owner.
-/

namespace CategoryTheory.Functor

variable (F : DividedPowerRing.{u} ⥤ Type u)
variable [HasProducts.{u} DividedPowerRing.{u}] [HasProducts.{u + 1} DividedPowerRing.{u}]
  [HasEqualizers DividedPowerRing.{u}] [PreservesLimits F]

/-- Companion bridge for Lemma 23.3.3: if, in addition to `PreservesLimits F`, the functor
preserves products indexed by types in `Type (u + 1)`, then the bounded-source hypothesis feeds
directly into Lemma 4.25.1. This isolates the universe-sized product requirement coming from the
canonical generating family returned by `HasBoundedElementSources.exists_generating_family`. -/
theorem HasBoundedElementSources.isCorepresentable_of_preservesLimits_of_largeProducts
    [∀ J : Type (u + 1), PreservesLimitsOfShape (Discrete J) F]
    {κ : Cardinal.{u}} (h_small : F.HasBoundedElementSources κ) :
    F.IsCorepresentable := by
  let _ : ∀ J : Type u, PreservesLimitsOfShape (Discrete J) F := by
    intro J
    infer_instance
  let _ : PreservesLimitsOfShape WalkingParallelPair F := by
    infer_instance
  obtain ⟨I, X, x, h_generate⟩ := h_small.exists_generating_family
  exact CategoryTheory.isCorepresentable_of_preservesLimits_of_generating_family.{u, u, u + 1, u + 1}
    F X x h_generate

/-- Lemma 23.3.3: if a set-valued functor on divided power rings preserves limits and every
element comes by functoriality from a divided power ring whose underlying set is bounded by the
fixed cardinal `κ`, then the functor is representable. In mathlib's covariant convention,
representability is `F.IsCorepresentable`. -/
@[stacks 07GW]
theorem HasBoundedElementSources.isCorepresentable_of_preservesLimits
    {κ : Cardinal.{u}} (h_small : F.HasBoundedElementSources κ) :
    F.IsCorepresentable := by
  sorry

/-- Lemma 23.3.3: if a set-valued functor on divided power rings preserves limits and every
element comes by functoriality from some divided power ring whose underlying set is bounded by a
single cardinal, then the functor is representable. In mathlib's covariant convention, this is
`F.IsCorepresentable`. -/
@[stacks 07GW]
theorem isCorepresentable_of_exists_cardinal_bound_of_preservesLimits
    (h_small : ∃ κ : Cardinal.{u}, F.HasBoundedElementSources κ) :
    F.IsCorepresentable := by
  obtain ⟨κ, hκ⟩ := h_small
  exact hκ.isCorepresentable_of_preservesLimits

end CategoryTheory.Functor
