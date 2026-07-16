import Mathlib
import StacksProject_2024.stacks_project.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced mathlib's smoothness owner `AlgebraicGeometry.IsSmooth` together with
  the instance `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsSmooth`;
- local Chapter 29 precedent packages smoothness locality in
  `Scheme.Hom.smooth_iff_exists_affineOpenCover`;
- local Chapter 32 precedent for inverse-system descent/existence statements is
  `exists_compactOpen_stage_preimage_eq`.
-/

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 : I)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
variable [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
variable [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]

/-- Lemma 32.8.9: in the notation and assumptions of Situation `32.8.1`, if the limit base change
of `f₀` to `S = c.pt` is smooth and `f₀` is locally of finite presentation, then there exists a
stage `i ≥ i₀` such that the stagewise base change of `f₀` to `Sᵢ` is smooth. -/
@[stacks 0C0C]
theorem exists_ge_smooth_stage_of_smooth_limit
    [LocallyOfFinitePresentation f0]
    (hlimit : Smooth (pullback.snd f0 (pullback.fst y0 (c.π.app i0)))) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Smooth (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
