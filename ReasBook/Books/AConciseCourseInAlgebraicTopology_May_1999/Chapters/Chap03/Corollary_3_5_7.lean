import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B} {e : E}
variable [IsConnected E]

private theorem endSubgroup_transport_bot {b b' : B} (h : b = b') :
    h ▸ (⊥ : Subgroup (b ⟶ b)) = (⊥ : Subgroup (b' ⟶ b')) := by
  cases h
  rfl

/-- Corollary 3.5.7 (1): a connected universal covering functor over the base object `p.obj e`
maps uniquely to every covering functor over `B` once a point of the target fiber over `p.obj e`
is chosen. -/
-- Proof sketch: apply `existsUnique_map_iff_mapVertexGroup_range_le` with
-- `(Functor.mapVertexGroup p e).range = ⊥`; the needed subgroup inclusion is `⊥ ≤ H` for any
-- target subgroup `H`.
theorem universalCovering_existsUnique_map_to_covering
    (hp : Functor.IsUniversalCovering p e) (hp' : Functor.IsCovering p')
    (e' : p'.Fiber (p.obj e)) :
    ∃! h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom,
      let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1 := by
  simpa using
    (existsUnique_map_iff_mapVertexGroup_range_le
      hp' (p.obj e) ⟨e, rfl⟩ e').2 <|
      by
        rw [hp.mapVertexGroup_range_eq_bot]
        exact bot_le

/- Corollary 3.5.7 (2): if the target covering is also universal at the chosen fiber point, then
every point-preserving map of coverings over `B` is an isomorphism of coverings, provided the
target total groupoid is preconnected. -/
-- Proof sketch: specialize `isIso_map_iff_mapVertexGroup_range_eq` to the chosen points
-- `⟨e, rfl⟩` and `e'`. Universality of `p` at `e` and of `p'` at `e'.1` identifies both image
-- subgroups with `⊥`, so the subgroup equality criterion yields that any point-preserving map of
-- coverings is an isomorphism.
theorem universalCovering_map_isIso_of_target_isUniversal
    [IsPreconnected E']
    (hp : Functor.IsUniversalCovering p e)
    (e' : p'.Fiber (p.obj e)) (hp'univ : Functor.IsUniversalCovering p' e'.1)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom)
    (hh : let g : E ⥤ E' := h.left.toFunctor
      g.obj e = e'.1) :
    IsIso h := by
  refine
    (isIso_map_iff_mapVertexGroup_range_eq
      hp.isCovering hp'univ.isCovering (p.obj e) ⟨e, rfl⟩ e' h hh).2 ?_
  rw [hp.mapVertexGroup_range_eq_bot, hp'univ.mapVertexGroup_range_eq_bot]
  simpa using (endSubgroup_transport_bot e'.2).symm

end CategoryTheory.Functor.IsCovering
