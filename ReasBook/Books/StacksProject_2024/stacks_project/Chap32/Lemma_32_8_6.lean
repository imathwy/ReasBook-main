import Mathlib
import StacksProject_2024.stacks_project.Chap32.Situation_32_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
variable (i0 : I)
variable (X0 Y0 : Scheme.{u}) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)

-- Semantic recall: `lean_leansearch` confirmed `AlgebraicGeometry.IsSeparated` as the canonical
-- scheme-morphism owner, together with the diagonal closed-immersion characterization. Local
-- Chapter 32 precedent represents the Situation 32.8.1 limit and stage base changes by
-- `pullback.snd f0 (pullback.fst y0 ...)`. The Stacks source tag evidence is consistent with
-- tag `01ZQ`.

/-- Lemma 32.8.6: in the notation and assumptions of Situation 32.8.1, if the limit base change
of `f_0` is separated, then some stagewise base change `f_i` is separated for a stage `i >= i0`.
-/
@[stacks 01ZQ]
theorem exists_isSeparated_stageBaseChange_of_isSeparated_limitBaseChange
    [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (hc : IsLimit c) (x0 : X0 ⟶ D.obj i0) (hf0 : f0 ≫ y0 = x0)
    [CompactSpace ↥(D.obj i0)] [QuasiSeparatedSpace ↥(D.obj i0)]
    [CompactSpace ↥X0] [QuasiSeparatedSpace ↥X0]
    [CompactSpace ↥Y0] [QuasiSeparatedSpace ↥Y0]
    (hsep :
      IsSeparated (pullback.snd f0 (pullback.fst y0 (c.π.app i0)))) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      IsSeparated (pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end

end AlgebraicGeometry
