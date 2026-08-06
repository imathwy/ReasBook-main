import Mathlib.Algebra.Module.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-- Definition 19.1.2. For a based space `X`, modeled as an object of `BasedSpace`, the
reduced cohomology `Ẽ^q(X)` is the relative cohomology `E q X.right ({underTopBasepoint X} : Set
X.right)` of `X` relative to its chosen basepoint. -/
abbrev reducedCohomology
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    (q : ℤ) (X : BasedSpace) : Type v :=
  E q X.right ({underTopBasepoint X} : Set X.right)

/-- Unfolding `reducedCohomology` identifies it with the ambient relative cohomology theory
evaluated on the singleton basepoint subset. -/
@[simp] theorem reducedCohomology_def
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    (q : ℤ) (X : BasedSpace) :
    reducedCohomology E q X = E q X.right ({underTopBasepoint X} : Set X.right) :=
  rfl

/-- Reduced cohomology inherits its additive-group structure from the underlying relative
cohomology group at the singleton basepoint. -/
instance reducedCohomologyAddCommGroup
    (E : ℤ → (Y : TopCat.{u}) → Set Y → Type v)
    [∀ q (Y : TopCat.{u}) (A : Set Y), AddCommGroup (E q Y A)]
    (q : ℤ) (X : BasedSpace.{u}) :
    AddCommGroup (reducedCohomology E q X) :=
  inferInstanceAs (AddCommGroup (E q X.right ({underTopBasepoint X} : Set X.right)))

/-- Reduced cohomology inherits its module structure from the underlying relative cohomology
group at the singleton basepoint. -/
instance reducedCohomologyModule
    (R : Type w) [Semiring R]
    (E : ℤ → (Y : TopCat.{u}) → Set Y → Type v)
    [∀ q (Y : TopCat.{u}) (A : Set Y), AddCommMonoid (E q Y A)]
    [∀ q (Y : TopCat.{u}) (A : Set Y), Module R (E q Y A)]
    (q : ℤ) (X : BasedSpace.{u}) :
    Module R (reducedCohomology E q X) :=
  inferInstanceAs (Module R (E q X.right ({underTopBasepoint X} : Set X.right)))
