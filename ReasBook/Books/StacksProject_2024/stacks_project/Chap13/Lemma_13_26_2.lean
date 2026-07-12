import Mathlib
import StacksProject_2024.Chap13.Definition_13_13_1

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

section IntervalSplit

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasZeroObject 𝒜]
  [HasFiniteBiproducts 𝒜]
variable (a b : ℤ) (J : Set.Icc a b → 𝒜)

/-- Helper for Lemma 13.26.2: the canonical interval-tail inclusion is split by the corresponding
projection onto the same subtype biproduct. -/
private theorem intervalTailSubobject_splitMono (p : ℤ) :
    IsSplitMono (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1) := by
  -- Proof comment: the projection onto the same subtype is a retraction of the tail inclusion.
  exact IsSplitMono.mk'
    { retraction := biproduct.toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1
      id := biproduct.fromSubtype_toSubtype J fun i : Set.Icc a b ↦ p ≤ i.1 }

/-- The tail direct sum stage inside the interval-indexed biproduct. -/
@[reducible]
private noncomputable def intervalTailSubobject (p : ℤ) :
    Subobject (⨁ J) :=
  letI := intervalTailSubobject_splitMono (a := a) (b := b) (J := J) p
  Subobject.mk (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- Helper for Lemma 13.26.2: increasing the cutoff index shrinks the interval tail subobject. -/
private theorem intervalTailSubobject_antitone {p q : ℤ} (hpq : p ≤ q) :
    intervalTailSubobject a b J q ≤ intervalTailSubobject a b J p := by
  -- Proof comment: every `q`-tail summand also lies in the `p`-tail, so the ambient inclusion
  -- factors through the larger tail via the canonical subtype projection.
  letI := intervalTailSubobject_splitMono (a := a) (b := b) (J := J) p
  letI := intervalTailSubobject_splitMono (a := a) (b := b) (J := J) q
  refine Subobject.mk_le_mk_of_comm
    (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ q ≤ i.1) ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  by_cases hqi : q ≤ i.1
  · have hpi : p ≤ i.1 := le_trans hpq hqi
    simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
  · by_cases hpi : p ≤ i.1
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]
    · simp [biproduct.fromSubtype_π, biproduct.toSubtype_π, hqi, hpi, Category.assoc]

/-- The tail filtration on the biproduct indexed by the interval `[a, b]` is monotone on `ℤᵒᵈ`.
-/
private theorem intervalTailFiltration_monotone :
    Monotone (fun p : ℤᵒᵈ ↦ intervalTailSubobject a b J p) := by
  intro p q hpq
  -- Proof comment: monotonicity on `ℤᵒᵈ` is exactly antitonicity on the underlying integers.
  simpa using
    intervalTailSubobject_antitone (a := a) (b := b) (J := J)
      (p := OrderDual.ofDual q) (q := OrderDual.ofDual p)
      (show OrderDual.ofDual q ≤ OrderDual.ofDual p from hpq)

/-- The decreasing filtration on the interval biproduct whose `p`-th stage is the tail direct sum
over indices `q ≥ p`. -/
noncomputable def intervalTailFiltration :
    DecreasingFiltration (⨁ J) :=
  { toFun := fun p ↦ intervalTailSubobject a b J p
    monotone' := intervalTailFiltration_monotone a b J }

/-- Helper for Lemma 13.26.2: every stage weakly to the left of the interval is the whole
interval biproduct. -/
private theorem intervalTailSubobject_eq_top_of_le_left {p : ℤ} (hp : p ≤ a) :
    intervalTailSubobject a b J p = ⊤ := by
  -- Proof comment: every interval index satisfies `p ≤ i.1`, so the subtype inclusion is an
  -- isomorphism with inverse the corresponding projection.
  letI := intervalTailSubobject_splitMono (a := a) (b := b) (J := J) p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊤
  apply le_antisymm le_top
  refine Subobject.mk_le_mk_of_comm
    (biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) ?_
  ext i
  have hi : p ≤ i.1 := le_trans hp i.2.1
  simp [hi, Category.assoc]

/-- Helper for Lemma 13.26.2: every stage strictly to the right of the interval is zero. -/
private theorem intervalTailSubobject_eq_bot_of_right_lt {p : ℤ} (hp : b < p) :
    intervalTailSubobject a b J p = ⊥ := by
  -- Proof comment: no interval index survives beyond the right endpoint, so the tail inclusion is
  -- the zero morphism and hence defines the bottom subobject.
  letI := intervalTailSubobject_splitMono (a := a) (b := b) (J := J) p
  change Subobject.mk (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)) = ⊥
  apply (Subobject.mk_eq_bot_iff_zero).2
  apply biproduct.hom_ext
  intro i
  have hib : i.1 ≤ b := i.2.2
  have hi : ¬ p ≤ i.1 := by
    omega
  simp [biproduct.fromSubtype_π, hi]

/-- The interval-split filtered object has finite filtration. -/
private theorem intervalSplitFilteredObject_isFinite :
    ({ obj := ⨁ J
       filtration := intervalTailFiltration a b J } : FilteredObject 𝒜).IsFinite := by
  refine ⟨a, b + 1, ?_, ?_⟩
  · -- Proof comment: at the left endpoint the tail already contains every interval summand.
    simpa [intervalTailFiltration] using
      intervalTailSubobject_eq_top_of_le_left (a := a) (b := b) (J := J) (p := a) le_rfl
  · -- Proof comment: the first stage strictly to the right of the interval is the empty tail.
    simpa [intervalTailFiltration] using
      intervalTailSubobject_eq_bot_of_right_lt (a := a) (b := b) (J := J) (p := b + 1) (by omega)

/-- The finite filtered object attached to an interval-indexed family of summands. -/
noncomputable def intervalSplitFilteredObject :
    Fil^f(𝒜) :=
  ⟨{ obj := ⨁ J
     filtration := intervalTailFiltration a b J },
    intervalSplitFilteredObject_isFinite a b J⟩

end IntervalSplit

section FilteredInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)

local instance : HasFiniteBiproducts 𝒜 := Abelian.hasFiniteBiproducts

open FilteredObject.Hom

/-- A finite filtered object is filtered injective when each graded piece is injective in the
ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

/-- Lemma 13.26.2: a finite filtered object is filtered injective if and only if it is
isomorphic to a finite direct sum of injective objects indexed by an interval, equipped with the
tail filtration.
-/
theorem isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject
    (I : Fil^f(𝒜)) :
    IsFilteredInjective I ↔
      ∃ a b : ℤ,
        ∃ J : Set.Icc a b → 𝒜,
          ∃ e : I ≅ intervalSplitFilteredObject a b J, ∀ n, Injective (J n) := by
  -- TODO: source-faithful route. Order the finite filtration into a window `[a, b + 1]`,
  -- descend from the common zero stage `F^(b + 1)`, split each stage row using injectivity of
  -- the successor stage and the graded piece, and package the compatible stagewise isomorphisms
  -- into a filtered isomorphism with the interval-split model. The reverse implication should
  -- identify graded pieces of the interval model with the injective summands.
  sorry

end FilteredInjective

end CategoryTheory
