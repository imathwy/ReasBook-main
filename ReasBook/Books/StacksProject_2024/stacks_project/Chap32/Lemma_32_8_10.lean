import Mathlib
import StacksProject_2024.Chap32.Situation_32_8_1

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

-- Semantic recall: the dedicated `lean_leansearch` tool was unavailable in this environment.
-- The owner/API choice was verified against local Chapter 29/32 precedent, in particular the
-- canonical scheme-side owner `Etale` and the direct stagewise/limit base-change surface used in
-- the nearby descent lemmas for `Flat`, `Smooth`, and `Syntomic`.

/-- Lemma 32.8.10: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is étale and `f_0` is locally of finite presentation, then some stagewise base change
`f_i` is étale for a stage `i >= i0`. -/
@[stacks 07RP]
theorem exists_etale_stageBaseChange_of_etale_limitBaseChange_of_locallyOfFinitePresentation
    (hetale :
      Etale (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Etale (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
