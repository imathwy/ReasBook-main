import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_18_0_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Set

variable {𝕜 : Type v} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
variable {C F : Set E}
local notation "E⋆" => StrongDual 𝕜 E

/-!
Source/core/bridge triage:
- `source-facing`: the item identifies nonempty exposed faces of a convex set with supporting
  level-set slices, and then records the proper-face refinement by nontrivial supporting
  hyperplanes.
- `core/canonical`: the owner abstraction for exposed faces is `IsExposed 𝕜 C F`, and the
  supporting slice is most economically represented by a continuous linear functional together with
  one of its supporting level sets; properness is what upgrades this to a nonzero hyperplane
  description.
- `bridge/view`: this item is a bridge theorem relating the canonical exposed-face predicate to the
  supporting-functional description of the same hyperplane cut.

Domain-style sampling used here:
- `IsExposed 𝕜 C F`;
- `E⋆`;
- canonical maximizer owner surfaces `C.maximizers l`;
- preorder-level supporting slices `{x ∈ C | a ≤ l x}` and supporting half-spaces
  `{x | l x ≤ a}`.

Primitive data vs derived API:
- the primitive mathematical inputs are the ambient set `C`, the candidate subset `F`, and
  nonemptiness of `F`;
- properness of `F` is only needed for the nontrivial-hyperplane refinement, not for the core
  supporting-level-set characterization;
- the containment `F ⊆ C` is derived on both sides of the bridge statement, so it should not
  remain a primitive binder;
- the supporting-hyperplane description is theorem-level bridge API from `IsExposed`, written
  directly as existence data rather than stored in a second wrapper predicate;
- ambient minimization: the statement can stay on the ordered-semiring preorder layer by avoiding
  order antisymmetry (`l x = a`) on theorem surfaces and keeping only the primitive half-space/slice
  inequalities, so it should not be specialized to `ℝ`.

Layer target: `bridge/view`.
-/

namespace IsExposed

/-- Primitive constructor bridge on the canonical owner surface. -/
theorem of_eq_maximizers
    (l : E⋆) (hF_eq : F = C.maximizers l) :
    IsExposed 𝕜 C F := by
  intro _
  refine ⟨l, ?_⟩
  simpa [Set.maximizers, IsMaxOn] using hF_eq

/-- Primitive elimination bridge on the canonical owner surface. -/
theorem exists_eq_maximizers
    (hF : IsExposed 𝕜 C F) (hF_ne : F.Nonempty) :
    ∃ l : E⋆, F = C.maximizers l := by
  rcases hF hF_ne with ⟨l, hF_eq⟩
  refine ⟨l, ?_⟩
  simpa [Set.maximizers, IsMaxOn] using hF_eq

/-- Core bridge: for nonempty `F`, exposedness is equivalent to one maximizer-set equation. -/
theorem iff_exists_eq_maximizers (hF_ne : F.Nonempty) :
    IsExposed 𝕜 C F ↔ ∃ l : E⋆, F = C.maximizers l := by
  constructor
  · intro hF
    exact hF.exists_eq_maximizers hF_ne
  · rintro ⟨l, hF_eq⟩
    exact of_eq_maximizers l hF_eq

/-- Proper-face refinement on the canonical owner surface: for nonempty proper `F`, the exposing
functional can be chosen nonzero. -/
theorem iff_exists_nonzero_eq_maximizers (hF_ne : F.Nonempty) (hproper : F ≠ C) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, l ≠ 0 ∧ F = C.maximizers l := by
  rw [iff_exists_eq_maximizers hF_ne]
  constructor
  · rintro ⟨l, hF_eq⟩
    refine ⟨l, ?_, hF_eq⟩
    intro hl
    apply hproper
    calc
      F = C.maximizers l := hF_eq
      _ = C := by
        ext x
        simp [Set.maximizers, isMaxOn_iff, hl]
  · rintro ⟨l, _, hF_eq⟩
    exact ⟨l, hF_eq⟩

/-- Derived constructor bridge: a supporting threshold-slice description yields exposedness. -/
theorem of_supporting_levelSet
    (l : E⋆) (a : 𝕜) (hC : C ⊆ {x : E | l x ≤ a})
    (hF_eq : F = {x ∈ C | a ≤ l x}) :
    IsExposed 𝕜 C F := by
  intro hF_ne
  refine ⟨l, ?_⟩
  ext x
  constructor
  · intro hxF
    rw [hF_eq] at hxF
    refine ⟨hxF.1, ?_⟩
    intro y hyC
    exact (hC hyC).trans hxF.2
  · intro hx
    rcases hF_ne with ⟨x₀, hx₀F⟩
    have hx₀ : x₀ ∈ {x ∈ C | a ≤ l x} := by
      simpa [hF_eq] using hx₀F
    have ha_le : a ≤ l x := (hx₀.2).trans (hx.2 x₀ hx₀.1)
    rw [hF_eq]
    exact ⟨hx.1, ha_le⟩

/-- Derived constructor bridge: existentially packaged supporting threshold-slice data yields
exposedness. -/
theorem of_exists_supporting_levelSet :
    (∃ l : E⋆, ∃ a : 𝕜,
      C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x}) →
      IsExposed 𝕜 C F := by
  rintro ⟨l, a, hC, hF_eq⟩
  exact of_supporting_levelSet l a hC hF_eq

/-- Forward bridge: a nonempty exposed subset admits one supporting threshold-slice
representation. -/
theorem exists_supporting_levelSet
    (hF : IsExposed 𝕜 C F) (hF_ne : F.Nonempty) :
    ∃ l : E⋆, ∃ a : 𝕜,
      C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  rcases hF_ne with ⟨x₀, hx₀F⟩
  rcases hF.exists_eq_maximizers ⟨x₀, hx₀F⟩ with ⟨l, hF_eq_max⟩
  refine ⟨l, l x₀, ?_, ?_⟩
  · intro x hxC
    have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
      simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
    exact hx₀Max.2 x hxC
  · ext x
    constructor
    · intro hxF
      have hxMax : x ∈ C ∧ ∀ y ∈ C, l y ≤ l x := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hxF
      have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
      refine ⟨hxMax.1, ?_⟩
      exact hxMax.2 x₀ hx₀Max.1
    · intro hx
      have hx₀Max : x₀ ∈ C ∧ ∀ y ∈ C, l y ≤ l x₀ := by
        simpa [Set.maximizers, isMaxOn_iff, hF_eq_max] using hx₀F
      have hxMax : x ∈ C ∧ ∀ y ∈ C, l y ≤ l x := by
        refine ⟨hx.1, ?_⟩
        intro y hyC
        exact (hx₀Max.2 y hyC).trans hx.2
      have hxMax' : x ∈ C.maximizers l := by
        simpa [Set.maximizers, isMaxOn_iff] using hxMax
      simpa [hF_eq_max] using hxMax'

/-- Text 18.0.7, core bridge: for a nonempty subset `F` of `C`, being exposed is equivalent to
having one supporting threshold-slice description. -/
theorem iff_exists_supporting_levelSet (hF_ne : F.Nonempty) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, ∃ a : 𝕜,
        C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  constructor
  · intro hF
    exact hF.exists_supporting_levelSet hF_ne
  · rintro ⟨l, a, hC, hF_eq⟩
    exact of_supporting_levelSet l a hC hF_eq

/-- Text 18.0.7, proper-face refinement: for a nonempty proper subset `F` of `C`, the supporting
functional in the level-set characterization can be chosen nonzero, so the supporting hyperplane is
nontrivial. -/
theorem iff_exists_nonzero_supporting_levelSet (hF_ne : F.Nonempty) (hproper : F ≠ C) :
    IsExposed 𝕜 C F ↔
      ∃ l : E⋆, ∃ a : 𝕜,
        l ≠ 0 ∧ C ⊆ {x : E | l x ≤ a} ∧ F = {x ∈ C | a ≤ l x} := by
  rw [iff_exists_supporting_levelSet hF_ne]
  constructor
  · rintro ⟨l, a, hC, hF_eq⟩
    refine ⟨l, a, ?_, hC, hF_eq⟩
    intro hl
    apply hproper
    ext x
    constructor
    · intro hxF
      rw [hF_eq] at hxF
      exact hxF.1
    · intro hxC
      rw [hF_eq]
      rcases hF_ne with ⟨x₀, hx₀F⟩
      have hx₀ : x₀ ∈ {x ∈ C | a ≤ l x} := by
        simpa [hF_eq] using hx₀F
      have ha_le_zero : a ≤ (0 : 𝕜) := by
        simpa [hl] using hx₀.2
      exact ⟨hxC, by simpa [hl] using ha_le_zero⟩
  · rintro ⟨l, a, _, hC, hF_eq⟩
    exact ⟨l, a, hC, hF_eq⟩

end IsExposed

end
