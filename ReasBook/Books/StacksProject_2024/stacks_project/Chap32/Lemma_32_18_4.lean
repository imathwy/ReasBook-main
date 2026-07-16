import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_29_1
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

-- Semantic recall: `lean_leansearch` found the mathlib owner
-- `LocallyOfFinitePresentation`; local Chapter 29 precedent supplies
-- `Scheme.Hom.RelativeDimension`, and local Chapter 32 precedent represents Situation 32.8.1
-- stage and limit base changes by the canonical `pullback.snd` morphisms.

/-- Lemma 32.18.4: in the notation and assumptions of Situation 32.8.1, if the limit base change
`f` of `f_0` has relative dimension `d`, and `f_0` is locally of finite presentation, then some
stagewise base change `f_i` has relative dimension `d`. -/
@[stacks 0EY2]
theorem exists_relativeDimension_stageBaseChange_of_relativeDimension_limitBaseChange_of_locallyOfFinitePresentation
    (d : ℕ)
    (hrel :
      Scheme.Hom.RelativeDimension (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) d)
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.RelativeDimension
        (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) d := sorry

end

end AlgebraicGeometry
