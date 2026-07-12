import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Source/core/bridge triage:
-- `source-facing`: Definition 34.7.1 is the Stacks notion of a family of flat, locally finitely
-- presented morphisms whose images cover a fixed target scheme `T`;
-- `core/canonical`: the canonical fppf precoverage `Scheme.fppfPrecoverage`;
-- `bridge/view`: the companion theorems `mem_fppf_precoverage`, `source_spec`, and
-- `mem_flat_precoverage`.
--
-- The source keeps the explicit covering family as the main object, so this file reuses the
-- existing `Scheme.fppfPrecoverage` owner and exposes source-facing accessors rather than a second
-- local structure.

-- Semantic recall: `lean_leansearch` was attempted for the fppf-cover owner/API but was
-- unavailable due to HTTP 429 rate limiting. Chapter 34 already treats
-- `Scheme.fppfPrecoverage` as the canonical fppf-cover owner, so the source-facing API here is a
-- thin accessor layer over that existing owner rather than a duplicate local structure.

section

variable (T : Scheme.{u})

/-- Definition 34.7.1: an fppf covering of `T` is a family of morphisms `Uᵢ ⟶ T` whose members are
flat, locally of finite presentation, and whose images cover all points of `T`. -/
abbrev FppfCover (T : Scheme.{u}) :=
  T.Cover Scheme.fppfPrecoverage

namespace FppfCover

/-- An fppf covering can be used as its underlying family of morphisms to `T`. -/
instance : CoeFun (FppfCover T) (fun 𝒰 ↦ (i : 𝒰.I₀) → 𝒰.X i ⟶ T) where
  coe 𝒰 := 𝒰.f

/-- Companion bridge for Definition 34.7.1: the arrows of an fppf covering form a covering family
for the canonical fppf precoverage on schemes. -/
theorem mem_fppf_precoverage (𝒰 : FppfCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fppfPrecoverage.coverings T := by
  simpa using 𝒰.mem₀

/-- Each morphism in an fppf covering family is flat. -/
theorem flat (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    Flat (𝒰.f i) :=
  (𝒰.map_prop i).1

/-- Each morphism in an fppf covering family is locally of finite presentation. -/
theorem locallyOfFinitePresentation (𝒰 : FppfCover T) (i : 𝒰.I₀) :
    LocallyOfFinitePresentation (𝒰.f i) :=
  (𝒰.map_prop i).2

/-- The images of the morphisms in an fppf covering family cover all points of `T`. -/
theorem cover (𝒰 : FppfCover T) (t : T) :
    ∃ i, t ∈ Set.range (𝒰.f i) := by
  have hmem :
      (∀ x : T, ∃ i, x ∈ Set.range (𝒰.f i)) ∧
        (∀ i, Flat (𝒰.f i) ∧ LocallyOfFinitePresentation (𝒰.f i)) := by
    simpa [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] using
      𝒰.mem_fppf_precoverage
  exact hmem.1 t

/-- Source-facing specification for Definition 34.7.1: an fppf cover supplies flatness,
local finite presentation, and a jointly covering family of images. This is the downstream-facing
entry point for using all defining conditions without unfolding the structure. -/
theorem source_spec (𝒰 : FppfCover T) :
    (∀ i, Flat (𝒰.f i)) ∧
      (∀ i, LocallyOfFinitePresentation (𝒰.f i)) ∧
        (∀ t : T, ∃ i, t ∈ Set.range (𝒰.f i)) := by
  exact ⟨𝒰.flat, 𝒰.locallyOfFinitePresentation, 𝒰.cover⟩

/-- Companion bridge for Definition 34.7.1: forgetting local finite presentation, an fppf covering
is a covering family for the flat precoverage on schemes. -/
theorem mem_flat_precoverage (𝒰 : FppfCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := by
  rw [Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨𝒰.cover, 𝒰.flat⟩

end FppfCover

end

end AlgebraicGeometry
