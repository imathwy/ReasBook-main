import Mathlib.AlgebraicGeometry.Sites.Fpqc
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.SemiRepresentableFamily.Over

namespace AlgebraicGeometry

section

variable (R : Type u) [CommRing R] [Nontrivial R]

local notation "SpecR" => Scheme.Spec.obj (Opposite.op (CommRingCat.of R))
local notation "FpqcCover" => Scheme.Cover Scheme.fpqcPrecoverage SpecR

/-- The underlying fixed-target family of an fpqc cover of `Spec R`, viewed in the Chapter 7
owner `SemiRepresentableFamily.Over SpecR`. -/
private noncomputable abbrev coverFamily
    {R : Type u} [CommRing R]
    (𝒰 : Scheme.Cover Scheme.fpqcPrecoverage
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of R)))) :
    SemiRepresentableFamily.Over
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of R))) :=
  ofArrows 𝒰.X 𝒰.f

/-- Lemma 34.9.15: if `R` is a nonzero ring, then there is no set-indexed family of fpqc covers of
`Spec R` such that every fpqc cover of `Spec R` is refined by a member of that family. Here the
set-theoretic size obstruction is expressed by requiring the collection of candidate covers to live
in universe `v` and testing it against fpqc covers with indexing universe `max u v + 1`. -/
theorem no_small_fpqc_refinement_family_of_spec :
    ¬ ∃ (α : Type v) (A : α → FpqcCover),
        ∀ 𝒰 : FpqcCover,
          ∃ a : α,
            Refines (coverFamily (A a)) (coverFamily 𝒰) := by
  have hmissing :
      ∀ (α : Type v) (A : α → FpqcCover),
        ∃ 𝒰 : FpqcCover,
          ∀ a : α,
            ¬ Refines (coverFamily (A a)) (coverFamily 𝒰) := by
    intro α A
    sorry
  rintro ⟨α, A, hA⟩
  rcases hmissing α A with ⟨𝒰, h𝒰⟩
  rcases hA 𝒰 with ⟨a, ha⟩
  exact h𝒰 a ha

end

end AlgebraicGeometry
