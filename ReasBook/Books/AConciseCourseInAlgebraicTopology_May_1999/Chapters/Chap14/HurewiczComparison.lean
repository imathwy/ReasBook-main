import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10

open CategoryTheory
open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

/-- The canonical based `n`-sphere, with distinguished point `sphereBasepoint n`. -/
abbrev basedSphere (n : ℕ) : Under (⊤_ TopCat.{u}) :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (sphereBasepoint n)))

/-- The chosen basepoint of `basedSphere n` is `sphereBasepoint n`. -/
@[simp] theorem underTopBasepoint_basedSphere (n : ℕ) :
    underTopBasepoint (basedSphere n) = sphereBasepoint n := sorry

/-- A Chapter 14.3.3 comparison identifies based homotopy classes of maps `S^n ⟶ X` with the
canonical homotopy group `π_ n(X)` based at `underTopBasepoint X`. -/
abbrev HurewiczComparison (n : ℕ) (X : Under (⊤_ TopCat.{u})) :=
  basedHomotopyClasses (basedSphere n) X ≃ π_ n X.right (underTopBasepoint X)

/-- Apply a Chapter 14.3.3 comparison to a based homotopy class of maps `S^n ⟶ X`. -/
abbrev HurewiczComparison.ofSphereClass {n : ℕ} {X : Under (⊤_ TopCat.{u})}
    (comparison : HurewiczComparison n X) :
    basedHomotopyClasses (basedSphere n) X → π_ n X.right (underTopBasepoint X) :=
  comparison

/-- Regard an element of `π_ n(X)` as a based homotopy class of maps `S^n ⟶ X` via the inverse
Chapter 14.3.3 comparison. -/
abbrev HurewiczComparison.toSphereClass {n : ℕ} {X : Under (⊤_ TopCat.{u})}
    (comparison : HurewiczComparison n X) :
    π_ n X.right (underTopBasepoint X) → basedHomotopyClasses (basedSphere n) X :=
  comparison.symm

/-- A named repo owner for the chosen Chapter 14.3.3 comparison attached to `X` in degree `n`. -/
class HasHurewiczComparison (n : ℕ) (X : Under (⊤_ TopCat.{u})) where
  /-- The chosen comparison between based sphere classes and `π_ n(X)`. -/
  comparison : HurewiczComparison n X

/-- The chosen Chapter 14.3.3 comparison attached to `X` in degree `n`. -/
abbrev hurewiczComparison (n : ℕ) (X : Under (⊤_ TopCat.{u})) [HasHurewiczComparison n X] :
    HurewiczComparison n X :=
  HasHurewiczComparison.comparison
