import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]

/-- Definition 3.3.11 (1): a covering functor of groupoids is regular at `e` if the image of the
induced map on the vertex group at `e` is a normal subgroup of the vertex group at `p.obj e`. -/
class IsRegularCovering (p : E ⥤ B) (e : E) : Prop where
  /-- A regular covering functor is, in particular, a covering functor. -/
  isCovering : Functor.IsCovering p
  /-- The image of the induced map on the vertex group at `e` is normal in the vertex group at
  `p.obj e`. -/
  normal_mapVertexGroup_range : (Functor.mapVertexGroup p e).range.Normal

namespace IsRegularCovering

variable {p : E ⥤ B} {e : E}

instance (hp : IsRegularCovering p e) : Functor.IsCovering p :=
  hp.isCovering

instance [hp : IsRegularCovering p e] : (Functor.mapVertexGroup p e).range.Normal :=
  hp.normal_mapVertexGroup_range

end IsRegularCovering

/-- Definition 3.3.11 (2): a covering functor of groupoids is universal at `e` if the image of
the induced map on the vertex group at `e` is the trivial subgroup of the vertex group at
`p.obj e`. -/
class IsUniversalCovering (p : E ⥤ B) (e : E) : Prop where
  /-- A universal covering functor is, in particular, a covering functor. -/
  isCovering : Functor.IsCovering p
  /-- The image of the induced map on the vertex group at `e` is trivial. -/
  mapVertexGroup_range_eq_bot : (Functor.mapVertexGroup p e).range = ⊥

namespace IsUniversalCovering

variable {p : E ⥤ B} {e : E}

instance (hp : IsUniversalCovering p e) : Functor.IsCovering p :=
  hp.isCovering

/-- A universal covering functor is regular at the chosen base object. -/
-- Proof sketch: the trivial subgroup is normal, so the triviality condition on the image of the
-- induced vertex-group map implies the normality condition required for regularity.
theorem isRegularCovering (hp : IsUniversalCovering p e) : IsRegularCovering p e := by
  refine ⟨hp.isCovering, ?_⟩
  rw [hp.mapVertexGroup_range_eq_bot]
  exact (Subgroup.normal_bot : (⊥ : Subgroup (p.obj e ⟶ p.obj e)).Normal)

instance [hp : IsUniversalCovering p e] : IsRegularCovering p e :=
  hp.isRegularCovering

instance [hp : IsUniversalCovering p e] : (Functor.mapVertexGroup p e).range.Normal :=
  hp.isRegularCovering.normal_mapVertexGroup_range

end IsUniversalCovering

end CategoryTheory.Functor
