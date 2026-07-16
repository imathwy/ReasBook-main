import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1
import StacksProject_2024.stacks_project.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recovered the canonical scheme-side owner
-- `LocallyQuasiFinite`; local Chapter 29 adds the Stacks-facing global owner
-- `Scheme.Hom.QuasiFinite`, and Situation 32.8.1 fixes the stagewise and limit base changes as
-- `pullback.snd f0 (pullback.fst y0 ...)`.

/-- Lemma 32.18.2: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is quasi-finite and `f_0` is locally of finite type, then some stagewise base change
`f_i` is quasi-finite for a stage `i >= i0`. -/
@[stacks 094M]
theorem exists_quasiFinite_stageBaseChange_of_quasiFinite_limitBaseChange_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i0 : I)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
    (hf0 : f0 ≫ y0 = x0)
    [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
    [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
    [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]
    (hqf : Scheme.Hom.QuasiFinite (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hft : LocallyOfFiniteType f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.QuasiFinite (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end AlgebraicGeometry
