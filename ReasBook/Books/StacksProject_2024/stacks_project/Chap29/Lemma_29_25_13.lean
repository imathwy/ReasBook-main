import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: Chapter 29 already exposes the source-facing scheme owners
-- `Scheme.Hom.flatAt`, `Scheme.Modules.flatOverAt`, and `Scheme.Modules.flatOver`.

open Scheme.Hom

section

variable {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]

/-- Lemma 29.25.13 (1): let `h : X ⟶ Y` be a morphism of schemes over `S`, let `𝒢` be a
quasi-coherent `\mathcal O_Y`-module, and let `x : X`. If `h` is flat at `x`, then `𝒢` is flat
over `S` at `h(x)` if and only if `h^*𝒢` is flat over `S` at `x`. -/
@[stacks 02JZ]
theorem flatOverAt_iff_pullback_flatOverAt_of_flatAt
    (x : X) (hh : flatAt h x) :
    flatOverAt 𝒢 f (h.base x) ↔
      flatOverAt ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f) x := sorry

/-- Lemma 29.25.13 (2): if `h : X ⟶ Y` is surjective and flat, then a quasi-coherent
`\mathcal O_Y`-module `𝒢` is flat over `S` if and only if `h^*𝒢` is flat over `S`. -/
@[stacks 02JZ]
theorem flatOver_iff_pullback_flatOver_of_surjective_of_flat
    [Flat h] [Surjective h] :
    flatOver 𝒢 f ↔
      flatOver ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f) := sorry

end

end AlgebraicGeometry.Scheme.Modules

namespace Scheme.Hom

section

variable {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)

/-- Lemma 29.25.13 (3): if `h : X ⟶ Y` is surjective and flat and `X` is flat over `S`, then
`Y` is flat over `S`. -/
@[stacks 02JZ]
theorem flat_of_comp_of_surjective_of_flat
    [Flat h] [Surjective h] [Flat (h ≫ f)] :
    Flat f := sorry

/-- Companion to Lemma 29.25.13 (3): under the same hypotheses, `f` is flat at every point of
`Y`. This exposes the pointwise flatness owner used by later source-facing statements. -/
theorem flatAt_of_comp_of_surjective_of_flat
    [Flat h] [Surjective h] [Flat (h ≫ f)] (y : Y) :
    flatAt f y := sorry

end

end Scheme.Hom
