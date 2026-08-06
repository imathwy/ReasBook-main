import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1

open scoped Manifold Topology

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced linear-orientation primitives but no existing
-- orientation-cover owner in the current environment, and local search verified that Chapter 20
-- records pointwise orientation data through `localTopHomologyGroup`.

/-- A local orientation at `x` is a choice of identification of the local top homology group at
`x` with the repository's constant coefficient module over `ℤ`. -/
abbrev LocalOrientation (n : ℕ) {M : Type} [TopologicalSpace M] (x : M) : Type :=
  localTopHomologyGroup ℤ n M x ≅ constantCoefficientModule ℤ

/-- Construction 20.6.1: the orientation cover of `M` consists of pairs `(x, α)` where `x : M`
and `α` is a choice of local orientation at `x`. -/
abbrev OrientationCover (n : ℕ) (M : Type) [TopologicalSpace M] : Type :=
  Σ x : M, LocalOrientation n x

namespace OrientationCover

variable {n M} [TopologicalSpace M]

/-- The basepoint component of an element of the orientation cover. -/
abbrev point (x : OrientationCover n M) : M :=
  x.1

/-- The local orientation chosen over the basepoint of an element of the orientation cover. -/
abbrev orientation (x : OrientationCover n M) : LocalOrientation n (point x) :=
  x.2

@[simp] theorem point_mk (x : M) (α : LocalOrientation n x) :
    point ⟨x, α⟩ = x :=
  rfl

@[simp] theorem orientation_mk (x : M) (α : LocalOrientation n x) :
    orientation ⟨x, α⟩ = α :=
  rfl

@[simp] theorem mk_point_orientation (x : OrientationCover n M) :
    ⟨point x, orientation x⟩ = x := by
  cases x
  rfl

/-- An element of the orientation cover canonically projects to its base point in `M`. -/
instance : CoeTC (OrientationCover n M) M where
  coe := point

end OrientationCover
