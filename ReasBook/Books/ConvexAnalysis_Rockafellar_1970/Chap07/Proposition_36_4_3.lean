import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_15
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_5

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]
variable [HasPairing U UStar α] [HasPairing X XStar α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 36.4.3 says that the inverse operation `F ↦ F_*` commutes with the
  adjoint operation, producing the common bifunction denoted in the text by `F_*^*`.
- `core/canonical`: the built layer already provides the inverse notation `F _*` together with
  `Bifunction.adjoint`, and Definition 6.30.15 now supplies the source-facing owner
  `Bifunction.concaveAdjoint` as the matching concave-side bridge owner.
- `bridge/view`: this file records the commutation law directly as equalities between those owner
  operations, split into the convex-side and concave-side clauses because the two adjoint
  operations live on different source layers.

Domain-style sampling used here:
- notation `F _*` from `Definition_36_4_1`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`, available through the built
  Chapter 7 bridge import `Definition_36_4_5`;
- `Bifunction.concaveAdjoint` from `Chap06.Definition_6_30_15`;
- `Bifunction.inverse_adjoint` from `Definition_36_4_5`, which already owns the common
  `⨆ x, ⨆ u` formula for `(F⋆) _*`;
- the owner-level inverse involution from `Definition_36_4_1`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → WithBotTop α`;
- primitive owner expressions: `concaveAdjoint UStar XStar (F _*)` and `(F⋆) _*`;
- derived API: the commutation equalities showing that these two source constructions coincide.

Layer target: `bridge/view`.
-/

section ConvexClause

variable [Neg UStar] [HasPairingNegRight U UStar α]

-- Proof sketch: rewrite `concaveAdjoint` of `F _*` by the Chapter 6 textbook `⨆ x, ⨆ u`
-- formula, then reuse the Chapter 7 owner theorem `inverse_adjoint_apply`, which gives
-- the same formula for `(F⋆) _*`.
/-- Proposition 36.4.3 (1): taking the inverse first and then the concave adjoint agrees with
taking the convex adjoint first and then the inverse. -/
theorem concaveAdjoint_inverse_eq_inverse_adjoint
    (F : U → X → WithBotTop α) :
    concaveAdjoint UStar XStar (F _*) = (F⋆) _* := by
  funext uStar xStar
  rw [concaveAdjoint_eq_iSup_iSup (XStar := UStar) (UStar := XStar)]
  simpa [add_left_comm, add_comm] using
    (inverse_adjoint_apply (F := F) uStar xStar).symm

end ConvexClause

section ConcaveClause

variable [Neg XStar] [HasPairingNegRight X XStar α]

-- Proof sketch: expand the same three owners in the opposite order. The convex adjoint of
-- `G _*` is definitionally the same sign-swapped formula as the inverse of the concave
-- adjoint of `G`.
/-- Proposition 36.4.3 (2): taking the inverse first and then the convex adjoint agrees with
taking the concave adjoint first and then the inverse. -/
theorem adjoint_inverse_eq_inverse_concaveAdjoint
    (G : U → X → WithBotTop α) :
    (G _*)⋆ =
      (concaveAdjoint XStar UStar G) _* := by
  simpa [inverse_inverse] using
    congrArg (fun H => H _*)
      (concaveAdjoint_inverse_eq_inverse_adjoint (G _*)).symm

end ConcaveClause

end Bifunction
