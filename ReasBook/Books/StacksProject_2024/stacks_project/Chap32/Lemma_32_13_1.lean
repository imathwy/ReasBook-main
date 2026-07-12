import StacksProject_2024.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed `IsProper` as the canonical scheme-morphism
-- owner for properness, with `LocallyOfFiniteType` as the source side condition. Local
-- Chapter 32 precedent represents Situation 32.8.1 stage and limit base changes by
-- `pullback.snd f0 (pullback.fst y0 ...)`.

/-- Lemma 32.13.1: in the notation and assumptions of Situation 32.8.1, if the limit base
change `f` of `f_0` is proper and `f_0` is locally of finite type, then some stagewise base
change `f_i` is proper for a stage `i >= i0`. -/
@[stacks 081F]
theorem exists_isProper_stageBaseChange_of_isProper_limitBaseChange_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i0 : I)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
    (hf0 : f0 ≫ y0 = x0)
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    (hproper : IsProper (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hft : LocallyOfFiniteType f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsProper (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end AlgebraicGeometry
