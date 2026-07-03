import Mathlib
import StacksProject_2024.Chap13.Lemma_13_26_3

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.26.2`.
- primary domain: finite filtered objects in an abelian category and their interval-indexed split
  biproduct presentations;
- sampled owner declarations:
  `DecreasingFiltration`,
  `FilteredObject`,
  `FilteredObject.IsFinite`,
  `finiteFilteredObjectCat`,
  `Set.Icc`,
  `biproduct.fromSubtype`;
- best owner abstraction: the Chapter `12` owner `FilteredObject 𝒜`, with the tail stages first
  assembled as a `DecreasingFiltration`;
- primitive data: an interval-indexed family `J : Set.Icc a b → 𝒜`;
- derived API: the tail filtration, the associated finite filtered object, and the filtered-
  injective decomposition theorem.

Source/core/bridge triage:
- `source-facing`: the characterization of filtered injective finite filtered objects by an
  interval-indexed split model;
- `core/canonical`: `DecreasingFiltration`, `FilteredObject`, `FilteredObject.IsFinite`, and
  `Fil^f(𝒜)`;
- `bridge/view`: the interval-tail filtration and the resulting bridge object
  `intervalSplitFilteredObject`. -/

section IntervalSplit

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]
  [HasFiniteBiproducts 𝒜]
variable (a b : ℤ) (J : Set.Icc a b → 𝒜)

/-- The tail direct sum stage inside the interval-indexed biproduct. -/
private noncomputable def intervalTailSubobject (p : ℤ) :
    Subobject (⨁ J) :=
  by
    letI : IsSplitMono (biproduct.fromSubtype J fun i ↦ p ≤ i.1) :=
      IsSplitMono.mk'
        { retraction := biproduct.toSubtype J fun i ↦ p ≤ i.1
          id := biproduct.fromSubtype_toSubtype J fun i ↦ p ≤ i.1 }
    exact Subobject.mk (biproduct.fromSubtype J fun i ↦ p ≤ i.1)

-- Proof sketch: if `p ≤ q`, then every summand with index at least `q` also has index at least
-- `p`, so the tail direct sums define a decreasing filtration. Equivalently, the assignment is
-- monotone on the order-dual integers.
/-- The tail filtration on the biproduct indexed by the interval `[a, b]` is monotone on `ℤᵒᵈ`.
-/
private theorem intervalTailFiltration_monotone :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject a b J p) := sorry

/-- The decreasing filtration on the interval biproduct whose `p`-th stage is the tail direct sum
over indices `q ≥ p`. -/
noncomputable def intervalTailFiltration :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject a b J p
    monotone' := intervalTailFiltration_monotone a b J }

-- Proof sketch: the stage at `b + 1` is the empty tail direct sum, hence zero, while the stage at
-- `a` contains every summand in the interval and hence is the whole biproduct.
/-- The interval-split filtered object has finite filtration. -/
private theorem intervalSplitFilteredObject_isFinite :
    ({ obj := ⨁ J
       filtration := intervalTailFiltration a b J } : FilteredObject 𝒜).IsFinite := sorry

/-- The finite filtered object attached to an interval-indexed family of summands. -/
noncomputable def intervalSplitFilteredObject :
    Fil^f(𝒜) :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration a b J },
    intervalSplitFilteredObject_isFinite a b J⟩

-- Proof sketch: this is the defining formula of `intervalSplitFilteredObject`.
/-- The stage `F^{p}` of `intervalSplitFilteredObject` is the tail direct sum over the summands
with index at least `p`. -/
@[simp]
theorem intervalSplitFilteredObject_filtration_obj (a b p : ℤ) (J : Set.Icc a b → 𝒜) :
    F^{p} ((intervalSplitFilteredObject a b J).obj) = intervalTailFiltration a b J p := rfl

end IntervalSplit

section FilteredInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local instance : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts

-- Proof sketch: if `I` is filtered injective, each graded piece is injective, and the finite
-- filtration splits into interval-indexed injective graded summands. Conversely, the graded pieces
-- of the interval-split model are exactly those injective summands.
/-- Lemma 13.26.2: a finite filtered object is filtered injective if and only if it is
isomorphic to a finite direct sum of injective objects indexed by an interval, equipped with the
tail filtration.
-/
theorem isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject
    (I : Fil^f(𝒜)) :
    IsFilteredInjective I ↔
      ∃ a b : ℤ,
        ∃ J : Set.Icc a b → 𝒜,
          ∃ e : I ≅ intervalSplitFilteredObject a b J, ∀ n, Injective (J n) := sorry

end FilteredInjective

end CategoryTheory
