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

-- Semantic recall: `lean_leansearch` confirmed `AlgebraicGeometry.IsFinite` as the canonical
-- scheme-side owner for finite morphisms. Local Chapter 32 precedent represents the Situation
-- 32.8.1 limit and stagewise base changes by the morphisms `pullback.snd f0
-- (pullback.fst y0 ...)`.

/-- Lemma 32.8.3: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is finite and `f_0` is locally of finite type, then some stagewise base change `f_i`
is finite for a stage `i >= i0`. -/
@[stacks 01ZO]
theorem exists_isFinite_stageBaseChange_of_isFinite_limitBaseChange_of_locallyOfFiniteType
    (hfinite :
      IsFinite (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hft : LocallyOfFiniteType f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsFinite (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
