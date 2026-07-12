import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical `pullback.mapDesc` immersion and
closed-immersion instances used in Lemma 26.21.9. This item states the corresponding graph map
`X ⟶ X ×_S Y` directly as a `pullback.lift`. -/

/-- The graph morphism associated to a morphism of schemes over a base. -/
@[stacks 01KS]
def graphOverBase {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
    (hg : g ≫ y = x) : X ⟶ pullback x y :=
  pullback.lift (𝟙 X) g ((Category.id_comp x).trans hg.symm)

variable {X Y S : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (g : X ⟶ Y)
  (hg : g ≫ y = x)

/-- Lemma 26.21.10 (1): for a morphism `g : X ⟶ Y` of schemes over `S`, the graph morphism
`X ⟶ X ×_S Y` is an immersion. -/
@[stacks 01KS]
theorem isImmersion_graphOverBase :
    IsImmersion (graphOverBase x y g hg) := sorry

/-- Lemma 26.21.10 (2): if `Y` is separated over `S`, then the graph morphism
`X ⟶ X ×_S Y` is a closed immersion. -/
@[stacks 01KS]
theorem isClosedImmersion_graphOverBase_of_isSeparated [IsSeparated y] :
    IsClosedImmersion (graphOverBase x y g hg) := sorry

/-- Lemma 26.21.10 (3): if `Y` is quasi-separated over `S`, then the graph morphism
`X ⟶ X ×_S Y` is quasi-compact. -/
@[stacks 01KS]
theorem quasiCompact_graphOverBase_of_quasiSeparated [QuasiSeparated y] :
    QuasiCompact (graphOverBase x y g hg) := sorry

end AlgebraicGeometry
