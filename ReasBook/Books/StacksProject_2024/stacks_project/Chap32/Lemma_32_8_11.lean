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

-- Semantic recall: `lean_leansearch` confirmed `CategoryTheory.IsIso` as the canonical owner for
-- isomorphisms of scheme morphisms. Local Chapter 32 precedent represents Situation 32.8.1
-- stagewise and limit base changes by the morphisms `pullback.snd f0 (pullback.fst y0 ...)`.

/-- Lemma 32.8.11: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f_0` is an isomorphism and `f_0` is locally of finite presentation, then there
exists a stage `i >= i0` such that the stagewise base change `f_i` is an isomorphism. -/
@[stacks 081E]
theorem exists_isIso_stageBaseChange_of_isIso_limitBaseChange_of_locallyOfFinitePresentation
    (hiso :
      IsIso (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsIso (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
