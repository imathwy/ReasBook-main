import Mathlib
import StacksProject_2024.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed `AlgebraicGeometry.IsImmersion` and its
-- `LocallyOfFiniteType` instance as the canonical scheme-morphism owners. Local Chapter 32
-- precedent represents the Situation 32.8.1 limit and stage base changes by the corresponding
-- `pullback.snd f0 (pullback.fst y0 ...)` morphisms.

/-- Lemma 32.8.13: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f_0` is an immersion and `f_0` is locally of finite type, then there exists
a stage `i >= i0` such that the stagewise base change `f_i` is an immersion. -/
@[stacks 0GTB]
theorem exists_isImmersion_stageBaseChange_of_isImmersion_limitBaseChange_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i0 : I)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
    (hf0 : f0 ≫ y0 = x0)
    [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
    [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
    [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]
    (himm :
      IsImmersion (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hft : LocallyOfFiniteType f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsImmersion (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end AlgebraicGeometry
