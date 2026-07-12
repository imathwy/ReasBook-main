import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap34.Definition_34_5_1
import StacksProject_2024.Chap34.Definition_34_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/- Semantic recall / owner check:
- `lean_leansearch` surfaced `AlgebraicGeometry.IsSmooth.exists_isStandardSmooth` as the canonical
  local standard-smooth chart criterion for smooth morphisms.
- The local Chapter 34 source-facing owners are `Scheme.SmoothCovering` for arbitrary indexed
  smooth coverings and `StandardSmoothCovering` for finite affine standard smooth coverings.
- The refinement and "open affine in one of the `T_i`" clause are therefore expressed by an
  explicit morphism of fixed-target families in `SemiRepresentableFamily.Over T`, whose component
  arrows are required to be open immersions.
-/

variable {T : Scheme.{u}} {ι : Type v}

/-- Lemma 34.5.4: a smooth covering of an affine scheme admits a finite affine refinement by
standard smooth morphisms, and the refining affine schemes may be chosen as open affines of the
original covering schemes. -/
@[stacks 0222]
theorem exists_standardSmoothCovering_refining_smoothCovering_of_isAffine
    [IsAffine T] (family : ι → Over T) (hfamily : Scheme.SmoothCovering family) :
    ∃ 𝒱 : StandardSmoothCovering T,
      (∀ j : Fin 𝒱.n, Smooth (𝒱.map j)) ∧
        let 𝒲 : SemiRepresentableFamily.Over T :=
          SemiRepresentableFamily.Over.ofArrows
            (fun j : ULift.{v} (Fin 𝒱.n) ↦ (𝒱.toOverFamily.obj j.down).left)
            (fun j ↦ (𝒱.toOverFamily.obj j.down).hom)
        let 𝒲₀ : SemiRepresentableFamily.Over T :=
          SemiRepresentableFamily.Over.ofArrows
            (fun i : ι ↦ (family i).left) (fun i ↦ (family i).hom)
        ∃ φ : 𝒲 ⟶ 𝒲₀, ∀ j : Fin 𝒱.n, IsOpenImmersion ((φ.f (ULift.up j)).left) := sorry

end AlgebraicGeometry
