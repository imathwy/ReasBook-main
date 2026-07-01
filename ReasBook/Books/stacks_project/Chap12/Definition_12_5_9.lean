import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory
namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex C)

/- Domain-style sampling for Definition 12.5.9:
- primary domain: split short complexes in a preadditive category;
- sampled owner API:
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.splitMono_f`,
  `ShortComplex.Splitting.splitEpi_g`,
  `ShortComplex.Splitting.isoBinaryBiproduct`;
- source/core/bridge triage:
  `source-facing`: the textbook proposition that a short complex is split, formalized as
    `Nonempty S.Splitting`;
  `core/canonical`: the owner structure `S.Splitting`;
  `bridge/view`: the existence-style reformulation below in terms of a retraction and a section.

Primitive data are exactly the retraction `r`, the section `s`, and the direct-sum identity on
`S.X₂`. The split monomorphism/epimorphism consequences and biproduct comparison are derived API
already provided upstream by the owner structure, so this file should not introduce a parallel
wrapper for that data.
-/

/- Definition 12.5.9: a short complex is split in the textbook sense exactly when the proposition
`Nonempty S.Splitting` holds. -/
#check (Nonempty S.Splitting)

/- Companion recall: `S.Splitting` is the canonical owner for chosen splitting data. Its primitive
data are a retraction of `S.f`, a section of `S.g`, and the direct-sum identity on `S.X₂`. -/
recall Splitting

/-- Source-facing bridge for the textbook formulation of a split short complex. -/
theorem nonempty_splitting_iff :
    Nonempty S.Splitting ↔
      ∃ (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂),
        S.f ≫ r = 𝟙 S.X₁ ∧ s ≫ S.g = 𝟙 S.X₃ ∧ r ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  constructor
  · rintro ⟨σ⟩
    exact ⟨σ.r, σ.s, σ.f_r, σ.s_g, σ.id⟩
  · rintro ⟨r, s, hr, hs, hid⟩
    exact ⟨⟨r, s, hr, hs, hid⟩⟩

end ShortComplex
end CategoryTheory
