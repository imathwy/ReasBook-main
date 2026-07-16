import Mathlib
import StacksProject_2024.stacks_project.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed the canonical scheme-morphism owner
-- `AlgebraicGeometry.Surjective`. Local Chapter 32 precedent represents the Situation 32.8.1
-- stagewise and limit base changes as `pullback.snd f0 (pullback.fst y0 ...)`.

/-- Lemma 32.8.15: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f_0` is surjective and `f_0` is locally of finite presentation, then there exists
a stage `i >= i0` such that the stagewise base change `f_i` is surjective. -/
@[stacks 07RR]
theorem exists_surjective_stageBaseChange_of_surjective_limitBaseChange_of_locallyOfFinitePresentation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i0 : I)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
    (hf0 : f0 ≫ y0 = x0)
    [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
    [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
    [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]
    (hsurj : Surjective (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Surjective (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end AlgebraicGeometry
