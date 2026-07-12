import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_9_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

/- Semantic recall hits:
- `Scheme.fpqcPrecoverage`, `StandardFpqcCover`, and the Chapter 7 fixed-target-family refinement
  relation `Refines`;
- in this chapter, the source-facing fpqc owner is the site cover `T.Cover Scheme.fpqcPrecoverage`,
  while the finite affine refinement owner is `StandardFpqcCover`.
-/

/-- Lemma 34.9.9: for an affine scheme `T`, every fpqc covering of `T` admits a finite affine
refinement whose components remain fpqc over `T`, and this refinement can be chosen so that each
affine component is an open affine subscheme of one member of the original covering family. -/
@[stacks 022E]
theorem existsFiniteAffineOpenRefinementOfFpqcCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.Cover Scheme.fpqcPrecoverage) :
    ∃ 𝒱 : StandardFpqcCover T,
      ∃ φ : 𝒱.toOverFamily ⟶ ofArrows 𝒰.X 𝒰.f,
        ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f j).left) := sorry

/-- Companion source-facing form of Lemma 34.9.9: each component of the finite affine fpqc
refinement is an open affine subscheme of one member of the original covering family. -/
theorem existsFiniteAffineOpenRefinementOfFpqcCover_spec
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.Cover Scheme.fpqcPrecoverage) :
    ∃ 𝒱 : StandardFpqcCover T,
      Refines 𝒱.toOverFamily (ofArrows 𝒰.X 𝒰.f) ∧
        ∀ j : Fin 𝒱.n, ∃ i : 𝒰.I₀, ∃ g : 𝒱.U j ⟶ 𝒰.X i,
          IsOpenImmersion g ∧ g ≫ 𝒰.f i = 𝒱.map j := by
  rcases existsFiniteAffineOpenRefinementOfFpqcCover 𝒰 with ⟨𝒱, φ, hφ⟩
  refine ⟨𝒱, ⟨φ⟩, ?_⟩
  intro j
  refine ⟨φ.α j, (φ.f j).left, hφ j, ?_⟩
  simpa using Over.w (φ.f j)

end AlgebraicGeometry
