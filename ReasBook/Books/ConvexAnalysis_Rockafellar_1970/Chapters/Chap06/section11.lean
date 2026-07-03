

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_11 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [Ring 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {P : Type*} [TopologicalSpace P] [AddTorsor V P]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.11 introduces the textbook adjective "relatively open" for a subset of
  an affine space, specialized in the source to `ℝ^n`, but the defining content is scalar-generic.
- `core/canonical`: the owner abstraction is mathlib's `intrinsicInterior 𝕜 C`.
- `bridge/view`: the public bridge is the source-facing predicate `IsRelativelyOpen`, whose
  defining content is the owner equality `intrinsicInterior 𝕜 C = C`; ambient openness gives a
  thin bridge to that adjective.
- Primitive data vs derived API: the primitive datum is the canonical owner-side equality
  `intrinsicInterior 𝕜 C = C`; ambient openness and the affine-span-subtype picture are derived
  bridge lemmas.
- Domain-style sampling used here: `intrinsicInterior`, `intrinsicInterior_subset`,
  `interior_subset_intrinsicInterior`, and `IsOpen.interior_eq`.
- Allowed-abbrev justification: unlike a one-off compatibility alias, `IsRelativelyOpen` is kept
  as the short chapter-wide source-facing vocabulary for a notion that is used extensively
  downstream; the owner-side equality remains its defining content.
- Layer target: the main labeled entry is `source-facing`.
-/

variable (𝕜)

/-- Text 6.11: a subset of an affine space is relatively open when its relative interior,
formalized by the canonical owner `intrinsicInterior 𝕜 C`, is the whole set. -/
abbrev IsRelativelyOpen (C : Set P) : Prop :=
  ri[𝕜](C) = C

variable {𝕜}

/-- Primitive intrinsic-topology owner form of relative openness: `IsRelativelyOpen 𝕜 C` is
equivalent to ordinary openness of `C` inside its affine hull subtype. -/
theorem isRelativelyOpen_iff_isOpen_preimage_affineSpan {C : Set P} :
    IsRelativelyOpen 𝕜 C ↔ IsOpen ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
  constructor
  · intro hC
    have hinterior :
        interior ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) = ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
      ext x
      constructor
      · intro hx
        have hxri : (x : P) ∈ ri[𝕜](C) := by
          exact ⟨x, hx, rfl⟩
        simpa [IsRelativelyOpen, hC] using hxri
      · intro hx
        have hxri : (x : P) ∈ ri[𝕜](C) := by
          simpa [IsRelativelyOpen, hC] using hx
        rcases (mem_intrinsicInterior (𝕜 := 𝕜) (s := C) (x := (x : P))).1 hxri with
          ⟨y, hy, hyx⟩
        have hyx' : y = x := Subtype.ext hyx
        simpa [hyx'] using hy
    exact interior_eq_iff_isOpen.mp hinterior
  · intro hC
    have hinterior :
        interior ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) = ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) :=
      hC.interior_eq
    ext x
    constructor
    · intro hx
      rcases (mem_intrinsicInterior (𝕜 := 𝕜) (s := C) (x := x)).1 hx with ⟨y, hy, hyx⟩
      have hyC : (y : P) ∈ C := by
        have hy' : y ∈ ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
          simpa [hinterior] using hy
        exact hy'
      exact hyx ▸ hyC
    · intro hx
      let y : affineSpan 𝕜 C := ⟨x, subset_affineSpan 𝕜 C hx⟩
      have hy : y ∈ ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := hx
      have hyi : y ∈ interior ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
        simpa [hinterior] using hy
      exact ⟨y, hyi, rfl⟩

/-- Primitive bridge: if the ambient interior of a set is already the set, then it is relatively
open. This is the owner-level data used by Text 6.11. -/
theorem isRelativelyOpen_of_interior_eq {C : Set P} (hC : interior C = C) :
    IsRelativelyOpen 𝕜 C := by
  refine intrinsicInterior_subset.antisymm ?_
  simpa [IsRelativelyOpen, hC] using
    (interior_subset_intrinsicInterior : interior C ⊆ intrinsicInterior 𝕜 C)

/-- Any open subset of the ambient affine space is relatively open. -/
theorem IsOpen.isRelativelyOpen {C : Set P} (hC : IsOpen C) :
    IsRelativelyOpen 𝕜 C := by
  exact isRelativelyOpen_of_interior_eq hC.interior_eq

end
