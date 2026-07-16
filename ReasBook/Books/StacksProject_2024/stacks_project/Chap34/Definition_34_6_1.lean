import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_30_3
import StacksProject_2024.stacks_project.Chap29.Lemma_29_30_4
import StacksProject_2024.stacks_project.Chap29.Lemma_29_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

section

variable (T : Scheme.{u})

-- Source/core/bridge triage:
-- `source-facing`: Definition 34.6.1 is the Stacks notion of a family of syntomic morphisms whose
-- images cover `T`;
-- `core/canonical`: the canonical syntomic precoverage `Scheme.precoverage
-- (@Syntomic)`;
-- `bridge/view`: the companion theorem `mem_syntomic_precoverage`.
--
-- Mathlib already supplies the `MorphismProperty` closure instances for `@Syntomic`, so the
-- source-facing owner here is just the fixed-target cover API built from the canonical
-- precoverage.

/-- Definition 34.6.1: a syntomic covering of `T` is a family of morphisms `Tᵢ ⟶ T` such that each
member of the family is syntomic and the images of the family cover all points of `T`. -/
@[stacks 0225]
abbrev SyntomicCover (T : Scheme.{u}) :=
  T.Cover (Scheme.precoverage (@Syntomic))

namespace SyntomicCover

/-- Source-facing specification for Definition 34.6.1: a syntomic cover supplies memberwise
syntomicity and a jointly covering family of images. -/
theorem source_spec (𝒰 : SyntomicCover T) :
    (∀ i : 𝒰.I₀, Syntomic (𝒰.f i)) ∧
      (∀ t : T, ∃ i : 𝒰.I₀, t ∈ Set.range (𝒰.f i)) := by
  exact ⟨𝒰.map_prop, fun t ↦ ⟨𝒰.idx t, 𝒰.covers t⟩⟩

/-- Each morphism in a syntomic covering family is syntomic. -/
theorem syntomic (𝒰 : SyntomicCover T) (i : 𝒰.I₀) :
    Syntomic (𝒰.f i) := by
  exact 𝒰.map_prop i

/-- The images of the morphisms in a syntomic covering family cover all points of `T`. -/
theorem cover (𝒰 : SyntomicCover T) (t : T) :
    ∃ i : 𝒰.I₀, t ∈ Set.range (𝒰.f i) := by
  exact ⟨𝒰.idx t, 𝒰.covers t⟩

/-- Companion bridge for Definition 34.6.1: the arrows of a syntomic covering form a covering
family for the canonical syntomic precoverage on schemes. -/
theorem mem_syntomic_precoverage (𝒰 : SyntomicCover T) :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ (Scheme.precoverage (@Syntomic)).coverings T :=
  𝒰.mem₀

end SyntomicCover

end

end AlgebraicGeometry
