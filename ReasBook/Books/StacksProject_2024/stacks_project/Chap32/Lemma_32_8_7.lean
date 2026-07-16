import Mathlib
import StacksProject_2024.stacks_project.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 : I)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
variable [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
variable [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]

-- Semantic recall: `lean_leansearch` confirmed the canonical owner `AlgebraicGeometry.Flat`.
-- The local Chapter 32 situation file fixes the stagewise and limit base changes via
-- `pullback.snd f0 (pullback.fst y0 ...)`, so the source-facing statement is recorded directly on
-- those morphisms rather than through an auxiliary wrapper.

/-- Lemma 32.8.7: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is flat and `f_0` is locally of finite presentation, then some stagewise base change
`f_i` is flat for a stage `i >= i0`. -/
@[stacks 04AI]
theorem exists_flat_stageBaseChange_of_flat_limitBaseChange_of_locallyOfFinitePresentation
    (hflat :
      Flat (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Flat (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
