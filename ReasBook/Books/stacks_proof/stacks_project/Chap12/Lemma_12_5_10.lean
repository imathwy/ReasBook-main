import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe v u

namespace CategoryTheory
namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {S : ShortComplex C}

/- Domain-style sampling for Lemma 12.5.10:
- primary domain: splittings of exact short complexes in a preadditive balanced category;
- sampled owner API:
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.ext_r`,
  `ShortComplex.Splitting.ext_s`,
  `ShortComplex.Splitting.ofExactOfSection`,
  `ShortComplex.Splitting.ofExactOfRetraction`;
- source/core/bridge triage:
  `source-facing`: the two complementary existence-and-uniqueness statements from the source;
  `core/canonical`: the owner structure `S.Splitting`;
  `bridge/view`: extracting the complementary retraction or section from a chosen splitting.

Primitive data already live in the owner `S.Splitting`: a retraction, a section, and the splitting
identity. The local uniqueness package for splittings is therefore derived API, so this file
should state only the source-facing complementary-map lemmas and prove them directly from the
canonical owner constructors and extensionality lemmas.
-/

open Splitting

/-- Lemma 12.5.10 (1): in a short exact sequence, a chosen section of the quotient map determines
uniquely the complementary retraction on the subobject map making the sequence split. -/
@[stacks 010G]
theorem existsUnique_retraction_of_shortExact_of_section
    (hS : S.Exact) [Mono S.f] (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    ∃! r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  let σ : S.Splitting := ofExactOfSection S hS s hs inferInstance
  refine ⟨σ.r, ⟨σ.f_r, by simpa [σ] using σ.id⟩, ?_⟩
  intro r hr
  let τ : S.Splitting := { r := r, s := s, f_r := hr.1, s_g := hs, id := hr.2 }
  have hτ : τ = σ := ext_s τ σ rfl
  simpa [τ, σ] using congrArg Splitting.r hτ

/-- Lemma 12.5.10 (2): in a short exact sequence, a chosen retraction of the subobject map
determines uniquely the complementary section of the quotient map making the sequence split. -/
@[stacks 010G]
theorem existsUnique_section_of_shortExact_of_retraction
    (hS : S.Exact) [Epi S.g] (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 S.X₁) :
    ∃! s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  let σ : S.Splitting := ofExactOfRetraction S hS r hr inferInstance
  refine ⟨σ.s, ⟨σ.s_g, by simpa [σ] using σ.id⟩, ?_⟩
  intro s hs
  let τ : S.Splitting := { r := r, s := s, f_r := hr, s_g := hs.1, id := hs.2 }
  have hτ : τ = σ := ext_r τ σ rfl
  simpa [τ, σ] using congrArg Splitting.s hτ

end ShortComplex
end CategoryTheory
