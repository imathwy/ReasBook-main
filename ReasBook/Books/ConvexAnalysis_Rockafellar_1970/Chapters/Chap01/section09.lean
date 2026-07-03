import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_1_9_1 (from Chap01) -/
/-- Local notation surface for Text 1.9.1: `aff[𝕜] s` denotes the affine hull `affineSpan 𝕜 s`. -/
scoped[Rockafellar] notation:max "aff[" 𝕜 "] " s => affineSpan 𝕜 s

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open AffineSubspace
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 1.9.1 rewrites the affine span and affine independence of
  `b 0, b 1, ..., b m` in terms of a chosen base point and the corresponding tail
  difference vectors.
- `core/canonical`: the owner declarations are `affineSpan`, `AffineSubspace.mk'`,
  `vectorSpan_range_eq_span_range_vsub_right_ne`, and
  `affineIndependent_iff_linearIndependent_vsub`.
- `bridge/view`: first expose the intrinsic bridge over arbitrary index types using the complement
  subtype `{x // x ≠ i0}`, then specialize to the finite `Fin` tail view via `Fin.succAbove`,
  and finally to the textbook `0`-based view via `Fin.zero_succAbove`.
- Abstraction checks:
  - Codomain/ambient concreteness: already at the intrinsic affine-space owner layer
    (`AffineSubspace`/`Submodule`), with no concrete coordinate model.
  - Scalar-strength minimization: the recalled core bridges here are already `Ring`-level; this file
    does not strengthen to a concrete scalar model.
  - Owner concreteness: upstream from `Fin` by exposing an equivalence-indexed bridge before the
    `Fin.succAbove` specialization.
  - Topology language: not a topology statement; no ambient/intrinsic topology replacement needed.
  - Notation/owner surface: keep canonical owners (`affineSpan`, `AffineIndependent`) and expose
    the affine-span owner on theorem surfaces through the existing chapter notation `aff[𝕜]`.
- Layer target: `bridge/view`.
- Primitive data vs derived API: the family `b : Fin (m + 1) → P` is the only primitive data; the
  tail-span and tail-independence statements are derived API.
- Domain-style sampling used here:
  `AffineSubspace.mk'_eq`,
  `vectorSpan_range_eq_span_range_vsub_right_ne`,
  `affineIndependent_iff_linearIndependent_vsub`,
  `finSuccAboveEquiv`.
-/

/-- Intrinsic owner-level bridge for Text 1.9.1 (1): for any index type and chosen base index
`i0`, the affine span of a family is the translate through `b i0` of the span of the difference
vectors indexed by the complement subtype `{x // x ≠ i0}`. -/
theorem affineSpan_range_eq_mk'_span_vsub_ne
    {ι : Type*} (b : ι → P) (i0 : ι) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : { x : ι // x ≠ i0 } ↦ b i -ᵥ b i0)) := by
  rw [← mk'_eq (mem_affineSpan 𝕜 (Set.mem_range_self i0)), direction_affineSpan 𝕜 (Set.range b),
    vectorSpan_range_eq_span_range_vsub_right_ne 𝕜 b i0]

/-- Internal reindexing helper for Text 1.9.1 (1): transport the complement-subtype span formula
along an equivalence of index types. -/
private theorem affineSpan_range_eq_mk'_span_vsub_equiv
    {ι : Type*} {ι' : Type*} (b : ι → P) (i0 : ι) (e : ι' ≃ { x : ι // x ≠ i0 }) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : ι' ↦ b (e i) -ᵥ b i0)) := by
  rw [affineSpan_range_eq_mk'_span_vsub_ne (b := b) (i0 := i0)]
  congr 2
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp⟩

/-- Finite-index bridge for Text 1.9.1 (1): reindex by `Fin.succAbove i0`. -/
private theorem affineSpan_range_eq_mk'_span_vsub_succAbove
    {m : ℕ}
    (b : Fin (m + 1) → P) (i0 : Fin (m + 1)) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b (i0.succAbove i) -ᵥ b i0)) := by
  simpa [finSuccAboveEquiv_apply] using
    affineSpan_range_eq_mk'_span_vsub_equiv (b := b) (i0 := i0)
      (e := finSuccAboveEquiv i0)

/-- Source-facing Text 1.9.1 (1): the affine span of `b 0, b 1, ..., b m` is the translate through
`b 0` of the span of the tail vectors `b i.succ -ᵥ b 0`. -/
theorem affineSpan_range_eq_mk'_span_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    (aff[𝕜] (Set.range b)) = mk' (b 0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b i.succ -ᵥ b 0)) := by
  simpa [Fin.zero_succAbove] using
    affineSpan_range_eq_mk'_span_vsub_succAbove (b := b) (i0 := 0)

/-- Intrinsic owner-level bridge for Text 1.9.1 (2): affine independence is equivalent to linear
independence of the `i0`-anchored difference vectors indexed by the complement subtype
`{x // x ≠ i0}`. -/
theorem affineIndependent_iff_linearIndependent_vsub_ne
    {ι : Type*} (b : ι → P) (i0 : ι) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : { x : ι // x ≠ i0 } ↦ b i -ᵥ b i0) := by
  simpa using affineIndependent_iff_linearIndependent_vsub 𝕜 b i0

/-- Internal reindexing helper for Text 1.9.1 (2): transport the complement-subtype
linear-independence criterion along an equivalence of index types. -/
private theorem affineIndependent_iff_linearIndependent_vsub_equiv
    {ι : Type*} {ι' : Type*} (b : ι → P) (i0 : ι) (e : ι' ≃ { x : ι // x ≠ i0 }) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : ι' ↦ b (e i) -ᵥ b i0) := by
  simpa [Function.comp] using
    (affineIndependent_iff_linearIndependent_vsub_ne (b := b) (i0 := i0)).trans
      ((linearIndependent_equiv e).symm)

/-- Finite-index bridge for Text 1.9.1 (2): reindex by `Fin.succAbove i0`. -/
private theorem affineIndependent_iff_linearIndependent_vsub_succAbove
    {m : ℕ}
    (b : Fin (m + 1) → P) (i0 : Fin (m + 1)) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b (i0.succAbove i) -ᵥ b i0) := by
  simpa [finSuccAboveEquiv_apply] using
    affineIndependent_iff_linearIndependent_vsub_equiv (b := b) (i0 := i0)
      (e := finSuccAboveEquiv i0)

/-- Source-facing Text 1.9.1 (2): the points `b 0, b 1, ..., b m` are affinely independent if and
only if the difference vectors `b i.succ -ᵥ b 0` are linearly independent. -/
theorem affineIndependent_iff_linearIndependent_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b i.succ -ᵥ b 0) := by
  simpa [Fin.zero_succAbove] using
    affineIndependent_iff_linearIndependent_vsub_succAbove (b := b) (i0 := 0)

/-- Text 1.9.1: the affine span of `b 0, b 1, ..., b m` is the translate through `b 0` of the
span of the tail difference vectors, and affine independence of the points is equivalent to linear
independence of those tail vectors. -/
theorem affineSpan_and_affineIndependent_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    (aff[𝕜] (Set.range b)) = mk' (b 0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b i.succ -ᵥ b 0)) ∧
    (AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b i.succ -ᵥ b 0)) := by
  constructor
  · -- The affine-hull clause is exactly the established tail-span bridge.
    exact affineSpan_range_eq_mk'_span_vsub_tail (𝕜 := 𝕜) (b := b)
  · -- The independence clause is exactly the established tail-vector criterion.
    exact affineIndependent_iff_linearIndependent_vsub_tail (𝕜 := 𝕜) (b := b)

/-! ### Text_1_9_2 (from Chap01) -/
/-
Abstraction triage for Text 1.9.2:
- Codomain/ambient concreteness: not an extended-value codomain item (`EReal`/`WithBotTop` not
  involved); canonical ambient layer is affine spaces via `affineSpan`.
- Scalar-strength minimization: handled by the recalled owner theorems; this file introduces no
  stronger scalar specialization.
- Concrete-model owner replacement: already intrinsic (`AffineIndependent`, `affineSpan`,
  `Finset.affineCombination`), with no concrete model owner to replace.
- Intrinsic/relative topology check: not a topology statement; `closure`/`interior` language is not
  part of this item.
- Primitive vs derived owner layer: for coefficient uniqueness on a fixed support, prefer the
  primitive pointwise finite-support surface `∀ i ∈ s, ...`; treat `Set.EqOn` and indicator forms
  as bridge presentations.
-/

/- Text 1.9.2 (1): every point of the affine hull of a finite family is an affine combination of
that family. -/
recall eq_affineCombination_of_mem_affineSpan

/- Text 1.9.2 (2): affine independence of a finite family is exactly uniqueness of affine
combination coefficients whose weights sum to `1`. -/
recall affineIndependent_iff_indicator_eq_of_affineCombination_eq

section

variable {𝕜 : Type*} {V : Type*} {P : Type*} {ι : Type*}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace AffineIndependent

/-- Owner-level primitive finite-support uniqueness for affine-combination coefficients on a fixed
support. -/
theorem eq_of_affineCombination_eq {p : ι → P} (hp : AffineIndependent 𝕜 p)
    {s : Finset ι} {w₁ w₂ : ι → 𝕜}
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1)
    (hEq : s.affineCombination 𝕜 p w₁ = s.affineCombination 𝕜 p w₂) :
    ∀ i ∈ s, w₁ i = w₂ i :=
  (hp.affineCombination_eq_iff_eq (s := s) (w₁ := w₁) (w₂ := w₂) hw₁ hw₂).1 hEq

/-- Owner-level `Set.EqOn` bridge for affine-combination coefficient uniqueness on a fixed finite
support. -/
theorem eqOn_of_affineCombination_eq {p : ι → P} (hp : AffineIndependent 𝕜 p)
    {s : Finset ι} {w₁ w₂ : ι → 𝕜}
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1)
    (hEq : s.affineCombination 𝕜 p w₁ = s.affineCombination 𝕜 p w₂) :
    Set.EqOn w₁ w₂ (s : Set ι) := by
  intro i hi
  exact hp.eq_of_affineCombination_eq hw₁ hw₂ hEq i hi

end AffineIndependent

/-- Source-facing finite-support form of Text 1.9.2 (2): affine independence is equivalent to
uniqueness of normalized affine-combination coefficients on each finite support. -/
theorem affineIndependent_iff_forall_eq_of_affineCombination_eq (p : ι → P) :
    AffineIndependent 𝕜 p ↔
      ∀ (s : Finset ι) (w₁ w₂ : ι → 𝕜),
        ∑ i ∈ s, w₁ i = 1 →
          ∑ i ∈ s, w₂ i = 1 →
            s.affineCombination 𝕜 p w₁ = s.affineCombination 𝕜 p w₂ →
              ∀ i ∈ s, w₁ i = w₂ i := by
  classical
  constructor
  · intro hp s w₁ w₂ hw₁ hw₂ hEq
    exact hp.eq_of_affineCombination_eq hw₁ hw₂ hEq
  · intro h
    rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
    intro s₁ s₂ w₁ w₂ hw₁ hw₂ hEq
    let u₁ : ι → 𝕜 := Set.indicator (s₁ : Set ι) w₁
    let u₂ : ι → 𝕜 := Set.indicator (s₂ : Set ι) w₂
    have hu₁ : ∑ i ∈ s₁ ∪ s₂, u₁ i = 1 := by
      rw [show u₁ = Set.indicator (s₁ : Set ι) w₁ by rfl,
        Finset.sum_indicator_subset w₁ (s₁.subset_union_left (s₂ := s₂))]
      exact hw₁
    have hu₂ : ∑ i ∈ s₁ ∪ s₂, u₂ i = 1 := by
      rw [show u₂ = Set.indicator (s₂ : Set ι) w₂ by rfl,
        Finset.sum_indicator_subset w₂ (s₁.subset_union_right (s₂ := s₂))]
      exact hw₂
    have hEq' : (s₁ ∪ s₂).affineCombination 𝕜 p u₁ = (s₁ ∪ s₂).affineCombination 𝕜 p u₂ := by
      have hEq0 : s₁.affineCombination 𝕜 p w₁ = s₂.affineCombination 𝕜 p w₂ := hEq
      rw [Finset.affineCombination_indicator_subset w₁ p (s₁.subset_union_left (s₂ := s₂)),
        Finset.affineCombination_indicator_subset w₂ p (s₁.subset_union_right (s₂ := s₂))] at hEq0
      simpa [u₁, u₂] using hEq0
    have huEq : ∀ i ∈ s₁ ∪ s₂, u₁ i = u₂ i := h (s₁ ∪ s₂) u₁ u₂ hu₁ hu₂ hEq'
    ext i
    by_cases hi : i ∈ s₁ ∪ s₂
    · simpa [u₁, u₂] using huEq i hi
    · have hi₁ : i ∉ s₁ := fun hi₁ ↦ hi (Finset.mem_union.mpr (Or.inl hi₁))
      have hi₂ : i ∉ s₂ := fun hi₂ ↦ hi (Finset.mem_union.mpr (Or.inr hi₂))
      simp [hi₁, hi₂]

/-- `Set.EqOn` bridge form of Text 1.9.2 (2), derived from the primitive finite-support
pointwise uniqueness surface. -/
theorem affineIndependent_iff_forall_eqOn_of_affineCombination_eq (p : ι → P) :
    AffineIndependent 𝕜 p ↔
      ∀ (s : Finset ι) (w₁ w₂ : ι → 𝕜),
        ∑ i ∈ s, w₁ i = 1 →
          ∑ i ∈ s, w₂ i = 1 →
            s.affineCombination 𝕜 p w₁ = s.affineCombination 𝕜 p w₂ →
              Set.EqOn w₁ w₂ (s : Set ι) := by
  constructor
  · intro hp
    have hEq :=
      (affineIndependent_iff_forall_eq_of_affineCombination_eq (𝕜 := 𝕜) (p := p)).1 hp
    intro s w₁ w₂ hw₁ hw₂ hAff i hi
    exact hEq s w₁ w₂ hw₁ hw₂ hAff i hi
  · intro h
    refine (affineIndependent_iff_forall_eq_of_affineCombination_eq (𝕜 := 𝕜) (p := p)).2 ?_
    intro s w₁ w₂ hw₁ hw₂ hAff i hi
    exact h s w₁ w₂ hw₁ hw₂ hAff hi

end

/-! ### Text_1_9 (from Chap01) -/
variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
open scoped Rockafellar

/- Text 1.9: affine independence is the canonical predicate `AffineIndependent 𝕜`; the chapter
owner for set-level affine-hull dimension is `Set.affineDim`.
For a family `b : Fin (m + 1) → P`, the textbook criterion is that
`dim[𝕜](Set.range b) = m`.
-/
recall AffineIndependent

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.9 identifies affine independence of `m + 1` points with affine-hull
  dimension `m`.
- `core/canonical`: mathlib owns `AffineIndependent`; the chapter set-level owner for affine-hull
  dimension is `Set.affineDim`, backed by `AffineSubspace.affineDim`.
- `bridge/view`: the theorem below is the thin bridge from the owner vector-span criterion to the
  source-facing affine-dimension wording on the point-range set.
- Layer target: `bridge/view`.
- Primitive data vs derived API: this file introduces no new primitive data; it derives the
  textbook criterion from `AffineIndependent`, `Set.affineDim`, and the existing
  owner-side lemmas identifying affine independence with the dimension of the vector span and the
  direction of an affine span with that vector span.
- Domain-style sampling used here:
  `AffineIndependent`,
  `affineIndependent_iff_finrank_vectorSpan_eq`,
  `Set.affineDim`,
  `direction_affineSpan`,
  `finiteDimensional_direction_affineSpan_range`.
-/
namespace AffineIndependent

/-- Intrinsic cardinality form of Text 1.9: a finite family is affinely independent exactly when
the affine dimension of its range is `card - 1`. This is the canonical owner-layer statement;
the `m + 1` textbook form is a thin corollary. -/
theorem iff_range_affineDim_eq_card_sub_one
    {ι : Type*} [Finite ι] (b : ι → P) :
    AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let m' : ℕ := Nat.card ι - 1
    have hcard_pos : 0 < Nat.card ι := Nat.card_pos
    have hcard' : Nat.card ι = m' + 1 := by
      dsimp [m']
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hcard_pos).symm
    have hcard_fintype : Fintype.card ι = m' + 1 := by
      simpa [Nat.card_eq_fintype_card] using hcard'
    have hspan : affineSpan 𝕜 (Set.range b) ≠ ⊥ := by
      simp [affineSpan_eq_bot]
    have hmain : AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = m' := by
      change AffineIndependent 𝕜 b ↔ AffineSubspace.affineDim (affineSpan 𝕜 (Set.range b)) = m'
      rw [AffineSubspace.affineDim, if_neg hspan]
      rw [direction_affineSpan]
      simpa using affineIndependent_iff_finrank_vectorSpan_eq 𝕜 b hcard_fintype
    have hcard_int : (Fintype.card ι : ℤ) - 1 = m' := by
      calc
        (Fintype.card ι : ℤ) - 1 = (((m' + 1 : ℕ) : ℤ) - 1) := by simp [hcard_fintype]
        _ = m' := by simp
    simpa [Nat.card_eq_fintype_card, hcard_int] using hmain
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hAI : AffineIndependent 𝕜 b := affineIndependent_of_subsingleton 𝕜 b
    have hdim : dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 := by
      have hrange : Set.range b = (∅ : Set P) := by
        ext x
        simp
      simp [hrange, Set.affineDim, AffineSubspace.affineDim, Nat.card_eq_fintype_card]
    exact ⟨fun _ => hdim, fun _ => hAI⟩

/-- A family of `m + 1` points is affinely independent exactly when the affine dimension of its
range equals `m`. -/
theorem iff_range_affineDim_eq_of_card_eq
    {ι : Type*} {m : ℕ} [Finite ι] (b : ι → P) (hcard : Nat.card ι = m + 1) :
    AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = m := by
  have hmain := iff_range_affineDim_eq_card_sub_one (𝕜 := 𝕜) (b := b)
  have hcard_int : (Nat.card ι : ℤ) - 1 = m := by
    rw [hcard]
    simp
  simpa [hcard_int] using hmain

/-- Owner-level consequence of Text 1.9: an affinely independent finite family has affine-hull
dimension equal to `card - 1`. -/
theorem range_affineDim_eq_card_sub_one
    {ι : Type*} [Finite ι] {b : ι → P} (hb : AffineIndependent 𝕜 b) :
    dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 :=
  (iff_range_affineDim_eq_card_sub_one (𝕜 := 𝕜) (b := b)).1 hb

/-- Owner-level textbook cardinality form: for a finite family of cardinality `m + 1`,
affine independence forces affine dimension `m`. -/
theorem range_affineDim_eq_of_card_eq
    {ι : Type*} {m : ℕ} [Finite ι] {b : ι → P}
    (hb : AffineIndependent 𝕜 b) (hcard : Nat.card ι = m + 1) :
    dim[𝕜](Set.range b) = m :=
  (iff_range_affineDim_eq_of_card_eq (𝕜 := 𝕜) (b := b) (m := m) hcard).1 hb

end AffineIndependent

namespace Affine.Simplex

/-- Owner-level Text 1.9 corollary: the affine dimension of the vertex range of a simplex equals
its index parameter. -/
@[simp] theorem affineDim_range_points_eq {m : ℕ} (s : Affine.Simplex 𝕜 P m) :
    dim[𝕜](Set.range s.points) = m := by
  exact s.independent.range_affineDim_eq_of_card_eq (hcard := Nat.card_fin (m + 1))

end Affine.Simplex
