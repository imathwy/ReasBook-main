import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

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
