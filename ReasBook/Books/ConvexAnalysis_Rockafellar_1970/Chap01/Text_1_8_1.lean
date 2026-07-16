import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_8
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 1.8.1 rewrites membership in the affine hull of a subset as a finite affine
  combination of points of that subset.
- `core/canonical`: mathlib owns `affineSpan`, `Finset.affineCombination`, and the owner-side
  existence/membership lemmas `eq_affineCombination_of_mem_affineSpan`,
  `affineCombination_mem_affineSpan`, and `affineCombination_mem_affineSpan_of_nonempty`.
- `bridge/view`: expose subset-level theorem surfaces intrinsically over the subtype `s`, so witness
  data lives in `Finset s` rather than ambient `Finset P` plus coercion-side conditions.
- Primitive data vs derived API: the primitive witness data is a finite family of points in `s`
  together with coefficients summing to `1`.
- Layer target: keep owner-level recalls, and expose intrinsic set-level theorem surfaces.
- Abstraction checks:
  - codomain/ambient layer: already intrinsic (`affineSpan` / `aff[𝕜]`), no concrete model owner.
  - scalar strength: keep the generic `Ring` layer, with `[Nontrivial 𝕜]` only where mathematically
    needed for the converse direction.
  - topology language: not a topological item (`closure`/`interior` not involved).
  - notation/owner surface: use textbook `aff[𝕜] s` on public theorem statements.
-/

/- Text 1.8.1 (existence direction): a point of an affine hull is a finite affine combination of
points from the generating subset. -/
recall eq_affineCombination_of_mem_affineSpan

/- Text 1.8.1 (membership direction): a finite affine combination over the generating subset lies
in its affine hull. -/
recall mem_affineSpan_iff_eq_affineCombination
recall affineCombination_mem_affineSpan_of_nonempty

section

variable {𝕜 : Type*} {V : Type*} {P : Type*}
  [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

namespace Set

/-- Intrinsic set-level form of `eq_affineCombination_of_mem_affineSpan`.
The finite support lives intrinsically in the subtype `s`. -/
theorem eq_affineCombination_of_mem_aff {s : Set P} {p₁ : P}
    (h : p₁ ∈ aff[𝕜] s) :
    ∃ (fs : Finset s) (w : s → 𝕜), ∑ i ∈ fs, w i = 1 ∧
      p₁ = fs.affineCombination 𝕜 Subtype.val w := by
  simpa [Subtype.range_val] using
    (eq_affineCombination_of_mem_affineSpan (k := 𝕜) (p1 := p₁) (p := Subtype.val)
      (by simpa [Subtype.range_val] using h))

/-- Intrinsic set-level iff form of Text 1.8.1 under `[Nontrivial 𝕜]`.
This is a thin bridge to the canonical owner theorem `mem_affineSpan_iff_eq_affineCombination`. -/
theorem mem_aff_iff_exists_affineCombination [Nontrivial 𝕜] {s : Set P} {p₁ : P} :
    (p₁ ∈ aff[𝕜] s) ↔
      ∃ (fs : Finset s) (w : s → 𝕜), ∑ i ∈ fs, w i = 1 ∧
        p₁ = fs.affineCombination 𝕜 Subtype.val w := by
  simpa [Subtype.range_val] using
    (mem_affineSpan_iff_eq_affineCombination (k := 𝕜) (V := V) (p1 := p₁) (p := Subtype.val))

/-- Primitive intrinsic membership bridge: without `[Nontrivial 𝕜]`, membership follows from
nonempty support data rather than ambient set nonemptiness. -/
theorem affineCombination_mem_aff_of_nonempty_support {s : Set P} {fs : Finset s} {w : s → 𝕜}
    (hfs : fs.Nonempty) (h : ∑ i ∈ fs, w i = 1) :
    fs.affineCombination 𝕜 Subtype.val w ∈ aff[𝕜] s := by
  letI : Nonempty s := ⟨hfs.choose⟩
  simpa [Subtype.range_val] using
    (affineCombination_mem_affineSpan_of_nonempty (k := 𝕜) (s := fs) (w := w)
      (h := h) (p := Subtype.val))

/-- Intrinsic set-level form of `affineCombination_mem_affineSpan`.
Under `[Nontrivial 𝕜]`, any finite affine combination over `s` belongs to `aff[𝕜] s`. -/
theorem affineCombination_mem_aff [Nontrivial 𝕜] {s : Set P} {fs : Finset s} {w : s → 𝕜}
    (h : ∑ i ∈ fs, w i = 1) :
    fs.affineCombination 𝕜 Subtype.val w ∈ aff[𝕜] s := by
  have hfs : fs.Nonempty := by
    by_contra hfs
    have h01 : (0 : 𝕜) = 1 := by
      have h' := h
      rw [Finset.not_nonempty_iff_eq_empty.mp hfs] at h'
      exact h'
    exact zero_ne_one h01
  exact affineCombination_mem_aff_of_nonempty_support (s := s) (fs := fs) (w := w) hfs h

/-- Intrinsic set-level form of `affineCombination_mem_affineSpan` without `[Nontrivial 𝕜]`.
A finite affine combination over a nonempty generating set belongs to `aff[𝕜] s`. -/
theorem affineCombination_mem_aff_of_nonempty {s : Set P} (hs : s.Nonempty)
    {fs : Finset s} {w : s → 𝕜}
    (h : ∑ i ∈ fs, w i = 1) :
    fs.affineCombination 𝕜 Subtype.val w ∈ aff[𝕜] s := by
  letI : Nonempty s := hs.to_subtype
  simpa [Subtype.range_val] using
    (affineCombination_mem_affineSpan_of_nonempty (k := 𝕜) (s := fs) (w := w)
      (h := h) (p := Subtype.val))

/-- Intrinsic set-level iff form of Text 1.8.1 without `[Nontrivial 𝕜]`, assuming `s.Nonempty`. -/
theorem mem_aff_iff_exists_affineCombination_of_nonempty {s : Set P} (hs : s.Nonempty) {p₁ : P} :
    (p₁ ∈ aff[𝕜] s) ↔
      ∃ (fs : Finset s) (w : s → 𝕜), ∑ i ∈ fs, w i = 1 ∧
        p₁ = fs.affineCombination 𝕜 Subtype.val w := by
  constructor
  · exact eq_affineCombination_of_mem_aff
  · rintro ⟨fs, w, hw, rfl⟩
    exact affineCombination_mem_aff_of_nonempty hs (h := hw)

end Set

end
