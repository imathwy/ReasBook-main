import Mathlib
import StacksProject_2024.Chap29.Definition_29_48_1
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

-- Semantic recall: `lean_leansearch` surfaced the scheme-side finite morphism owner
-- `AlgebraicGeometry.IsFinite`; local Chapter 29 precedent supplies the source-facing
-- finite-locally-free owners `IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfRank`.

/-- Lemma 32.8.8 (1): in the notation and assumptions of Situation 32.8.1, if the limit base
change of `f_0` is finite locally free and `f_0` is locally of finite presentation, then some
stagewise base change `f_i` is finite locally free for a stage `i >= i0`. -/
@[stacks 06AC]
theorem exists_isFiniteLocallyFree_stageBaseChange_of_isFiniteLocallyFree_limitBaseChange_of_locallyOfFinitePresentation
    (hfiniteLocallyFree :
      IsFiniteLocallyFree (pullback.snd f0 (pullback.fst y0 (c.π.app i0))))
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsFiniteLocallyFree (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

/-- Lemma 32.8.8 (2): in the notation and assumptions of Situation 32.8.1, if the limit base
change of `f_0` is finite locally free of degree `d` and `f_0` is locally of finite presentation,
then some stagewise base change `f_i` is finite locally free of degree `d` for a stage `i >= i0`.
-/
@[stacks 06AC]
theorem exists_isFiniteLocallyFreeOfRank_stageBaseChange_of_isFiniteLocallyFreeOfRank_limitBaseChange_of_locallyOfFinitePresentation
    (d : ℕ)
    (hfiniteLocallyFreeOfRank :
      IsFiniteLocallyFreeOfRank (pullback.snd f0 (pullback.fst y0 (c.π.app i0))) d)
    (hfp : LocallyOfFinitePresentation f0) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsFiniteLocallyFreeOfRank
        (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) d := sorry

end

end AlgebraicGeometry
