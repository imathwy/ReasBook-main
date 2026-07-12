import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_6_1
import StacksProject_2024.Chap34.Definition_34_6_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall / analogue check:
-- `lean_leansearch` recalled the canonical `Scheme.AffineCover` refinement surface.
-- Local Chapter 34 precedents `Lemma_34_4_4` and `Lemma_34_9_9` confirm that the source's
-- "moreover, open affine in one of the original members" clause should be recorded through the
-- component morphisms of an explicit refinement being open immersions.

variable {T : Scheme.{u}}

/-- Lemma 34.6.4: an affine scheme with a syntomic covering admits a finite refinement by affine
standard syntomic charts, and each refining affine chart may be chosen as an open affine subscheme
of one member of the original covering family. -/
@[stacks 0228]
theorem exists_standardSyntomicRefinement_of_syntomicCover_of_isAffine
    [IsAffine T] (𝒰 : SyntomicCover.{v, u} T) :
    ∃ 𝒱 : StandardSyntomicCovering T,
      let 𝒲 : SemiRepresentableFamily.Over T :=
        SemiRepresentableFamily.Over.ofArrows
          (fun j : ULift.{v} (Fin 𝒱.n) ↦ 𝒱.U j.down) (fun j ↦ 𝒱.map j.down)
      let 𝒲₀ : SemiRepresentableFamily.Over T :=
        SemiRepresentableFamily.Over.ofArrows
          (fun i : 𝒰.I₀ ↦ 𝒰.X i) (fun i ↦ 𝒰.f i)
      ∃ φ : 𝒲 ⟶ 𝒲₀, ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f (ULift.up j)).left) := sorry

end AlgebraicGeometry
