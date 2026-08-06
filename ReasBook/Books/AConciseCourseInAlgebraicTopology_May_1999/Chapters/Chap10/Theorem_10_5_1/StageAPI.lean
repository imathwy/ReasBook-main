import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison

open CategoryTheory Limits
open scoped TopCat Topology Topology.Homotopy unitInterval

noncomputable section

universe u

namespace CWApproximationStageApi

-- Route correction: Theorem 10.5.1 cannot import the later Chapter 10 construction files
-- directly, so this support module owns the dependency-closed stage interfaces needed for the
-- stagewise CW-approximation route.

/-- Helper for Theorem 10.5.1: a chosen family of homotopy-group generators of a based space. -/
structure SelectedPiGenerators (X : BasedSpace.{u}) where
  /-- Indexing type for the chosen generators. -/
  generator : Type u
  /-- The degree attached to each chosen generator. -/
  degree : generator → ℕ
  /-- The chosen homotopy-group element in the recorded degree. -/
  piElement :
    ∀ i : generator, π_ (degree i) X.right (underTopBasepoint X)

/-- Helper for Theorem 10.5.1: the predicate that a homotopy-group element is one of the chosen
generators. -/
def SelectedPiGenerators.isPiGenerator {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (q : ℕ)
    (a : π_ q X.right (underTopBasepoint X)) : Prop :=
  ∃ i : {i : chosenGenerators.generator // chosenGenerators.degree i = q},
    (i.property ▸ chosenGenerators.piElement i.1) = a

/-- Helper for Theorem 10.5.1: `isPiGenerator` is exactly the explicit membership predicate in the
chosen indexed family. -/
theorem SelectedPiGenerators.isPiGenerator_iff {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (q : ℕ)
    (a : π_ q X.right (underTopBasepoint X)) :
    chosenGenerators.isPiGenerator q a ↔
      ∃ i : {i : chosenGenerators.generator // chosenGenerators.degree i = q},
        (i.property ▸ chosenGenerators.piElement i.1) = a :=
  Iff.rfl

/-- Helper for Theorem 10.5.1: each indexed generator is a chosen generator in its own degree. -/
theorem SelectedPiGenerators.piElement_isPiGenerator {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (i : chosenGenerators.generator) :
    chosenGenerators.isPiGenerator
      (chosenGenerators.degree i)
      (chosenGenerators.piElement i) := by
  -- Unpack the defining membership predicate with the canonical index.
  rw [chosenGenerators.isPiGenerator_iff]
  exact ⟨⟨i, rfl⟩, rfl⟩

/-- Helper for Theorem 10.5.1: a based sphere map represents a chosen homotopy-group element when
the fixed comparison sends its based homotopy class to that element. -/
def sphereMapRepresentsPiElement {X : BasedSpace.{u}} {q : ℕ}
    (comparison : HurewiczComparison q X)
    (a : π_ q X.right (underTopBasepoint X)) (f : basedSphere q ⟶ X) : Prop :=
  comparison.ofSphereClass
      ((Quotient.mk (basedHomotopySetoid (basedSphere q) X) f) :
        basedHomotopyClasses (basedSphere q) X) =
    a

/-- Helper for Theorem 10.5.1: the first stage of the stagewise CW approximation, namely a wedge
of generator spheres equipped with chosen maps to the target. -/
structure CWApproximationFirstStage (X : BasedSpace.{u}) (chosenGenerators : SelectedPiGenerators X)
    where
  /-- The chosen map from the sphere summand indexed by `i` to the target. -/
  representingMap :
    ∀ i : chosenGenerators.generator, basedSphere (chosenGenerators.degree i) ⟶ X

/-- Helper for Theorem 10.5.1: the chosen sphere maps realize the selected homotopy-group
generators relative to a fixed comparison family. -/
def CWApproximationFirstStage.representsChosenGenerators {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators)
    (comparison : ∀ i : chosenGenerators.generator,
      HurewiczComparison (chosenGenerators.degree i) X) : Prop :=
  ∀ i : chosenGenerators.generator,
    sphereMapRepresentsPiElement
      (comparison i)
      (chosenGenerators.piElement i)
      (X₁.representingMap i)

/-- Helper for Theorem 10.5.1: the underlying first-stage based space is the wedge of the chosen
sphere summands. -/
abbrev CWApproximationFirstStage.firstStage {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (_ : CWApproximationFirstStage X chosenGenerators) : BasedSpace.{u} :=
  ∐ fun i : chosenGenerators.generator ↦ basedSphere (chosenGenerators.degree i)

/-- Helper for Theorem 10.5.1: a first stage canonically coerces to its underlying wedge of
spheres. -/
instance CWApproximationFirstStage.instCoeToBasedSpace
    {X : BasedSpace.{u}} {chosenGenerators : SelectedPiGenerators X} :
    CoeTC (CWApproximationFirstStage X chosenGenerators) BasedSpace.{u} where
  coe X₁ := X₁.firstStage

/-- Helper for Theorem 10.5.1: the map from the first stage to the target descends the chosen
summand maps. -/
abbrev CWApproximationFirstStage.toTarget {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators) : X₁.firstStage ⟶ X :=
  Sigma.desc X₁.representingMap

/-- Helper for Theorem 10.5.1: restricting `toTarget` to one summand recovers the chosen
representing map of that summand. -/
@[simp] theorem CWApproximationFirstStage.sigma_ι_toTarget {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators)
    (i : chosenGenerators.generator) :
    Sigma.ι
        (fun j : chosenGenerators.generator ↦ basedSphere (chosenGenerators.degree j)) i ≫
      X₁.toTarget =
      X₁.representingMap i := by
  -- Descending from the coproduct immediately identifies the `i`th summand map.
  simpa [CWApproximationFirstStage.toTarget] using
    (Limits.Sigma.ι_desc X₁.representingMap i)

/-- Helper for Theorem 10.5.1: once the whole first stage realizes the chosen generators, each
individual summand does as well. -/
theorem CWApproximationFirstStage.representsGenerator {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators)
    (comparison : ∀ i : chosenGenerators.generator,
      HurewiczComparison (chosenGenerators.degree i) X)
    (hX₁ : X₁.representsChosenGenerators comparison)
    (i : chosenGenerators.generator) :
    sphereMapRepresentsPiElement
      (comparison i)
      (chosenGenerators.piElement i)
      (X₁.representingMap i) :=
  hX₁ i

/-- Helper for Theorem 10.5.1: the successor stage data records one next space, its inclusion of
the current stage, its map to the target, and the reduced-cylinder lifting property used to kill
kernels in one degree. -/
structure CWApproximationNextStage
    (n : ℕ) (X_n X : TopCat.{u}) (x_n : X_n) (x : X)
    (f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x) where
  /-- The next stage `X_(n+1)`. -/
  X_next : TopCat.{u}
  /-- The chosen basepoint of the next stage. -/
  x_next : X_next
  /-- The inclusion of the current stage into the next stage. -/
  inclusion : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X_next x_next
  /-- The next-stage map to the target. -/
  toTarget : basedSpaceAtPoint X_next x_next ⟶ basedSpaceAtPoint X x
  /-- The old stage map factors through the inclusion into the next stage. -/
  fac : inclusion ≫ toTarget = f_n
  /-- Reduced-cylinder homotopies in the target lift to the chosen next stage. -/
  lift (a b : basedSphere n ⟶ basedSpaceAtPoint X_n x_n)
      (K : reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X x)
      (hK₀ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 0) = (a ≫ f_n).right.hom s)
      (hK₁ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 1) = (b ≫ f_n).right.hom s) :
      ∃ H :
        reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X_next x_next,
        (∀ s : (basedSphere n).right,
          reducedCylinderToBasedHomotopy H (s, 0) = (a ≫ inclusion).right.hom s) ∧
        (∀ s : (basedSphere n).right,
          reducedCylinderToBasedHomotopy H (s, 1) = (b ≫ inclusion).right.hom s) ∧
        H ≫ toTarget = K

/-- Helper for Theorem 10.5.1: a next stage canonically coerces to its underlying based space. -/
instance CWApproximationNextStage.instCoeToBasedSpace
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x} :
    CoeTC (CWApproximationNextStage n X_n X x_n x f_n) (BasedSpace.{u}) where
  coe X_nextStage := basedSpaceAtPoint X_nextStage.X_next X_nextStage.x_next

/-- Helper for Theorem 10.5.1: the basepoint of the coerced based space is the recorded
`x_next`. -/
theorem CWApproximationNextStage.underTopBasepoint_coe
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n) :
    underTopBasepoint (X_nextStage : BasedSpace.{u}) = X_nextStage.x_next :=
  rfl

/-- Helper for Theorem 10.5.1: the stage map factors through the chosen next-stage inclusion. -/
@[simp] theorem CWApproximationNextStage.inclusion_comp_toTarget
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n) :
    X_nextStage.inclusion ≫ X_nextStage.toTarget = f_n := by
  -- Reuse the stored factorization field directly.
  exact X_nextStage.fac

/-- Helper for Theorem 10.5.1: the stored reduced-cylinder lifting datum can be read back without
unfolding the structure fields in later proofs. -/
theorem CWApproximationNextStage.lift_spec
    {n : ℕ} {X_n X : TopCat.{u}} {x_n : X_n} {x : X}
    {f_n : basedSpaceAtPoint X_n x_n ⟶ basedSpaceAtPoint X x}
    (X_nextStage : CWApproximationNextStage n X_n X x_n x f_n)
    (a b : basedSphere n ⟶ basedSpaceAtPoint X_n x_n)
    (K : reducedCylinder (basedSphere n) ⟶ basedSpaceAtPoint X x)
    (hK₀ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 0) = (a ≫ f_n).right.hom s)
    (hK₁ : ∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy K (s, 1) = (b ≫ f_n).right.hom s) :
    ∃ H :
      reducedCylinder (basedSphere n) ⟶ X_nextStage,
      (∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy H (s, 0) = (a ≫ X_nextStage.inclusion).right.hom s) ∧
      (∀ s : (basedSphere n).right,
        reducedCylinderToBasedHomotopy H (s, 1) = (b ≫ X_nextStage.inclusion).right.hom s) ∧
      H ≫ X_nextStage.toTarget = K := by
  -- Unpack the stored lifting field once and return it in the coerced next-stage spelling.
  exact X_nextStage.lift a b K hK₀ hK₁

end CWApproximationStageApi
