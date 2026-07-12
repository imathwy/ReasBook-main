import StacksProject_2024.Chap32.«32_22_2_1»
import StacksProject_2024.Chap32.Situation_32_22_1
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open FiniteTypeApproximationDiagram

-- Semantic recall: `lean_leansearch` confirmed the canonical owners `IsClosedImmersion` and
-- scheme finite-type morphisms; local Chapter 32 precedent uses explicit cone data for
-- `S = lim_i S_i` and `FiniteTypeApproximationDiagram` for the displayed square.

/-- Lemma 32.22.2: in Situation 32.22.1, if `X ⟶ S` is quasi-separated and of finite
type, then after some stage `i` there is a diagram `X ⟶ W` over `S ⟶ S_i` with
`W ⟶ S_i` of finite type, and the induced morphism
`X ⟶ S ×_{S_i} W` is a closed immersion. -/
@[stacks 0CNN]
theorem exists_finiteTypeApproximationDiagram_closedImmersion
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {X : Scheme.{u}} (f : X ⟶ c.pt) [QuasiSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
      Scheme.Hom.FiniteType diagram.toSi ∧
        IsClosedImmersion (pullback.lift f diagram.toW (w diagram).symm) := sorry

end AlgebraicGeometry
