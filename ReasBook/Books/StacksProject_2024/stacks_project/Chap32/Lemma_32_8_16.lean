import Mathlib
import StacksProject_2024.Chap29.Definition_29_30_1
import StacksProject_2024.Chap32.Situation_32_8_1

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

-- Semantic recall: `lean_leansearch` did not surface a scheme-level syntomic limit-descent theorem,
-- so the owner choice was verified against the local Chapter 32 flat analogue
-- `exists_flat_stageBaseChange_of_flat_limitBaseChange_of_locallyOfFinitePresentation`, together
-- with the project definition `Syntomic f := LocallyOfType RingHom.Syntomic f`.

/-- Lemma 32.8.16: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is syntomic and `f_0` is locally of finite presentation, then some stagewise base
change `f_i` is syntomic for a stage `i >= i0`. -/
@[stacks 0C3L]
theorem exists_syntomic_stageBaseChange_of_syntomic_limitBaseChange_of_locallyOfFinitePresentation
    (hsyntomic :
      Syntomic (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Syntomic (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
