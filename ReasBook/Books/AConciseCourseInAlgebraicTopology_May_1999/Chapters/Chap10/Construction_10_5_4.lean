import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped Topology

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no existing mathlib owner surfaced for the first stage of
-- a CW approximation, while local precedent already uses the canonical homotopy-group surface
-- `π_ q X.right (underTopBasepoint X)` for selected generators, the based-space model
-- `Under (⊤_ TopCat)`, the based sphere `basedSphere q`, and the wedge coproduct `∐` with
-- coproduct descents `Sigma.desc`.

/-- A `SelectedPiGenerators X` packages the previously chosen generators of the homotopy groups of
`X`, recorded by their degrees and by the corresponding canonical elements of
`π_ q X.right (underTopBasepoint X)`. The degreewise predicate saying that a canonical
homotopy-group element is one of these chosen generators is exposed as derived companion API. -/
structure SelectedPiGenerators (X : BasedSpace.{u}) where
  /-- Indexing type for the previously chosen generators of the homotopy groups of `X`. -/
  generator : Type u
  /-- The dimension `q` of the sphere corresponding to the chosen generator indexed by `i`. -/
  degree : generator → ℕ
  /-- The chosen generator of `π_q(X)` indexed by `i`, on the canonical homotopy-group owner. -/
  piElement :
    ∀ i : generator, π_ (degree i) X.right (underTopBasepoint X)

/-- A degree-`q` element of `π_q(X)` is a chosen generator exactly when it appears in the indexed
family `chosenGenerators`. -/
def SelectedPiGenerators.isPiGenerator {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (q : ℕ)
    (a : π_ q X.right (underTopBasepoint X)) : Prop :=
  ∃ i : {i : chosenGenerators.generator // chosenGenerators.degree i = q},
    (i.property ▸ chosenGenerators.piElement i.1) = a

/-- The chosen-generator predicate for `SelectedPiGenerators X` is exactly membership in the
indexed family of chosen homotopy-group elements. -/
theorem SelectedPiGenerators.isPiGenerator_iff {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (q : ℕ)
    (a : π_ q X.right (underTopBasepoint X)) :
    chosenGenerators.isPiGenerator q a ↔
      ∃ i : {i : chosenGenerators.generator // chosenGenerators.degree i = q},
        (i.property ▸ chosenGenerators.piElement i.1) = a :=
  Iff.rfl

/-- Each packaged element in `SelectedPiGenerators X` is one of the selected generators in its own
degree on the canonical `π_q(X)` surface. -/
theorem SelectedPiGenerators.piElement_isPiGenerator {X : BasedSpace.{u}}
    (chosenGenerators : SelectedPiGenerators X) (i : chosenGenerators.generator) :
    chosenGenerators.isPiGenerator
      (chosenGenerators.degree i)
      (chosenGenerators.piElement i) := by
  rw [chosenGenerators.isPiGenerator_iff]
  exact ⟨⟨i, rfl⟩, rfl⟩

/-- A based sphere map `f : basedSphere q ⟶ X` represents `a : π_q(X)` relative to a fixed
Chapter 14.3.3 comparison when that comparison sends the based homotopy class of `f` to `a` on
the canonical `π_q(X)` surface. -/
def sphereMapRepresentsPiElement {X : BasedSpace.{u}} {q : ℕ}
    (comparison : HurewiczComparison q X)
    (a : π_ q X.right (underTopBasepoint X)) (f : basedSphere q ⟶ X) : Prop :=
  comparison.ofSphereClass
      ((Quotient.mk (basedHomotopySetoid (basedSphere q) X) f) :
        basedHomotopyClasses (basedSphere q) X) =
    a

/-- Construction 10.5.4. For a based space `X` and a previously chosen family
`chosenGenerators : SelectedPiGenerators X`, `CWApproximationFirstStage X chosenGenerators`
packages the first-stage wedge of spheres `S^q`, one summand for each selected generator of
`π_q(X)`, together with chosen based maps from those sphere summands into `X`. The auxiliary
statement that these maps realize the prescribed homotopy-group generators relative to a fixed
Chapter 14.3.3 comparison is exposed separately as bridge API. -/
structure CWApproximationFirstStage (X : BasedSpace.{u}) (chosenGenerators : SelectedPiGenerators X)
    where
  /-- A chosen based sphere map on the summand indexed by `i`. -/
  representingMap :
    ∀ i : chosenGenerators.generator, basedSphere (chosenGenerators.degree i) ⟶ X

/-- Relative to a fixed Chapter 14.3.3 comparison family in the relevant degrees, the chosen
sphere maps in `X₁` realize the prescribed selected generators. -/
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

/-- The first stage `X₁` of `CWApproximationFirstStage X chosenGenerators` is the wedge of the
selected sphere summands. -/
abbrev CWApproximationFirstStage.firstStage {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (_ : CWApproximationFirstStage X chosenGenerators) : BasedSpace.{u} :=
  ∐ fun i : chosenGenerators.generator ↦ basedSphere (chosenGenerators.degree i)

/-- A `CWApproximationFirstStage X chosenGenerators` canonically coerces to its underlying
first-stage based space. -/
instance CWApproximationFirstStage.instCoeToBasedSpace
    {X : BasedSpace.{u}} {chosenGenerators : SelectedPiGenerators X} :
    CoeTC (CWApproximationFirstStage X chosenGenerators) BasedSpace.{u} where
  coe X₁ := X₁.firstStage

/-- The map `X₁ ⟶ X` is obtained by descending the chosen representing maps from the sphere
summands of the wedge. -/
abbrev CWApproximationFirstStage.toTarget {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators) : X₁.firstStage ⟶ X :=
  Sigma.desc X₁.representingMap

/-- The map `CWApproximationFirstStage.toTarget` restricts on each sphere summand to the chosen
representing map. -/
@[simp] theorem CWApproximationFirstStage.sigma_ι_toTarget {X : BasedSpace.{u}}
    {chosenGenerators : SelectedPiGenerators X}
    (X₁ : CWApproximationFirstStage X chosenGenerators)
    (i : chosenGenerators.generator) :
    Sigma.ι
        (fun j : chosenGenerators.generator ↦ basedSphere (chosenGenerators.degree j)) i ≫
      X₁.toTarget =
      X₁.representingMap i := by
  simpa [CWApproximationFirstStage.toTarget] using
    (Limits.Sigma.ι_desc X₁.representingMap i)

/-- If the chosen summand maps of `X₁` realize the prescribed generators relative to `comparison`,
then the summand indexed by `i` represents the chosen generator indexed by `i`. -/
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
