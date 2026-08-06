import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Topology.Connected.PathConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1

open scoped Topology

universe u w

-- Semantic recall: `lean_leansearch` surfaced `ZerothHomotopy`, `Abelianization`, and
-- `HomotopyGroup.Pi` as the canonical owners for the three source branches, while Chapter 10
-- supplies the source-facing connectivity owner `NConnectedSpace` on the underlying space.

/-- The source connectivity hypothesis for `H'_n(X)`: degree `0` carries no extra condition,
while degree `m + 1` requires the underlying space of `X` to be `m`-connected. -/
abbrev provisionalReducedGroupConnectivity
    (n : ℕ) (X : PointedCompactlyGenerated.{u, w}) : Prop :=
  match n with
  | 0 => True
  | m + 1 => NConnectedSpace m X.toCompactlyGenerated

/-- In degree `0`, the source connectivity hypothesis for `H'_0(X)` is vacuous. -/
@[simp] theorem provisionalReducedGroupConnectivity_zero
    (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroupConnectivity 0 X ↔ True :=
  Iff.rfl

/-- In positive degree, the source connectivity hypothesis for `H'_n(X)` is `NConnectedSpace` on
the underlying space. -/
@[simp] theorem provisionalReducedGroupConnectivity_succ_iff
    (m : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroupConnectivity (m + 1) X ↔
      NConnectedSpace m X.toCompactlyGenerated :=
  Iff.rfl

/-- Definition 13.2.6. For an `(n - 1)`-connected based compactly generated space `X`, the
provisional reduced group `H'_n(X)` is given by cases: path components in degree `0`,
the abelianization of `π_ 1` in degree `1`, and `π_ n` in degrees `n ≥ 2`.
The source connectivity hypothesis is tracked separately by
`provisionalReducedGroupConnectivity n X`. -/
abbrev provisionalReducedGroup
    (n : ℕ) (X : PointedCompactlyGenerated.{u, w}) : Type _ :=
  match n with
  | 0 => ZerothHomotopy X.toCompactlyGenerated
  | 1 => Abelianization (π_ 1 X.toCompactlyGenerated X.point)
  | m + 2 => π_ (m + 2) X.toCompactlyGenerated X.point

/-- The degree-zero provisional reduced group is the path-component quotient. -/
@[simp] theorem provisionalReducedGroup_zero (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroup 0 X = ZerothHomotopy X.toCompactlyGenerated :=
  rfl

/-- The degree-one provisional reduced group is the abelianization of `π_ 1`. -/
@[simp] theorem provisionalReducedGroup_one (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroup 1 X =
      Abelianization (π_ 1 X.toCompactlyGenerated X.point) :=
  rfl

/-- In degrees `m + 2`, the provisional reduced group is the corresponding higher homotopy group. -/
@[simp] theorem provisionalReducedGroup_succ_succ (m : ℕ) (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroup (m + 2) X =
      π_ (m + 2) X.toCompactlyGenerated X.point :=
  rfl

/-- The degree-zero branch identifies canonically with `π_ 0` of the underlying based space. -/
noncomputable def provisionalReducedGroupZeroEquivPi0
    (X : PointedCompactlyGenerated.{u, w}) :
    provisionalReducedGroup 0 X ≃ π_ 0 X.toCompactlyGenerated X.point :=
  HomotopyGroup.pi0EquivZerothHomotopy.symm
