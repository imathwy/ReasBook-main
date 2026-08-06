import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped Pointwise

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The stabilizer of a fiber point under fiber translation is the subgroup transported from the
corresponding vertex group upstairs. -/
theorem fiberPoint_stabilizer_eq_mapVertexGroup_range (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) :
    by
      letI : Functor.IsCovering p := hp
      exact MulAction.stabilizer (b ⟶ b) e =
        e.2 ▸ (Functor.mapVertexGroup p e.1).range := by
  rcases e with ⟨e, rfl⟩
  -- Reduce to the distinguished basepoint of the fiber, where Lemma 3.4.11 gives the exact
  -- stabilizer computation.
  simpa using fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e

/-- Proposition 3.3.6: every conjugate of the subgroup `p(π(E,e))` attached to a chosen fiber
point `e` is the corresponding subgroup for another point of the same fiber. -/
-- Proof sketch: equip the fiber with the canonical owner action
-- `Functor.vertexGroupAction (fiberTranslationFunctor hp) b`. The
-- translated point has
-- stabilizer `MulAut.conj g • MulAction.stabilizer _ e` by
-- `MulAction.stabilizer_smul_eq_stabilizer_map_conj`, and the basepoint isotropy theorem
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range` identifies these stabilizers
-- with
-- the source-facing transported image subgroups.
theorem exists_fiberPoint_mapVertexGroup_range_eq_conjugate (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) (g : b ⟶ b) :
    ∃ e' : p.Fiber b,
      e'.2 ▸ (Functor.mapVertexGroup p e'.1).range =
        MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
  -- Follow the source proof: translate the chosen fiber point by the loop `g`.
  refine ⟨g • e, ?_⟩
  calc
    (g • e).2 ▸ (Functor.mapVertexGroup p (g • e).1).range
        = MulAction.stabilizer (b ⟶ b) (g • e) := by
          -- Rewrite the subgroup attached to the translated point as its stabilizer.
          simpa using (fiberPoint_stabilizer_eq_mapVertexGroup_range hp (g • e)).symm
    _ = (MulAction.stabilizer (b ⟶ b) e).map (MulAut.conj g).toMonoidHom := by
          -- Translating a point conjugates its stabilizer inside the loop group.
          simpa using MulAction.stabilizer_smul_eq_stabilizer_map_conj g e
    _ = MulAut.conj g • MulAction.stabilizer (b ⟶ b) e := by
          rfl
    _ = MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
          -- Rewrite the original subgroup back from the stabilizer description.
          rw [(fiberPoint_stabilizer_eq_mapVertexGroup_range hp e).symm]

end CategoryTheory.Functor.IsCovering
