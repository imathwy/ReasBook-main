import Mathlib.Topology.Homotopy.Lifting
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

universe u v w

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

-- Semantic recall: mathlib provides `IsCoveringMap.liftHomotopy` for covering maps, but no
-- general topological `HasCoveringHomotopyProperty` or `IsFibration` owner was found in the
-- current environment.

/-- The covering homotopy property for a continuous map `p : C(E, B)`. -/
class HasCoveringHomotopyProperty (p : C(E, B)) : Prop where
  /-- Every compatible lift at time `0` of a homotopy in `B` extends to a lifted homotopy in `E`.
  -/
  homotopyLift {A : Type w} [TopologicalSpace A]
      [CompactlyGeneratedWeakHausdorffSpace.{w, w} A]
      {f₀ f₁ : C(A, B)} (H : f₀.Homotopy f₁)
      {g₀ : C(A, E)} (hg₀ : p.comp g₀ = f₀) :
      ∃ g₁ : C(A, E), ∃ G : g₀.Homotopy g₁, p.comp G.toContinuousMap = H.toContinuousMap

/-- Definition 7.1.2: a continuous map `p : C(E, B)` is a fibration if it is surjective and
has the covering homotopy property. -/
class IsFibration (p : C(E, B)) : Prop extends HasCoveringHomotopyProperty p where
  /-- A fibration is surjective. -/
  surjective : Function.Surjective p

namespace HasCoveringHomotopyProperty

variable {p : C(E, B)}

/-- Helper for Definition 7.1.2: a map with the covering homotopy property admits lifted
homotopies for every compatible initial lift. -/
theorem exists_homotopyLift [hp : HasCoveringHomotopyProperty.{u, v, w} p]
    ⦃A : Type w⦄ [TopologicalSpace A] [CompactlyGeneratedWeakHausdorffSpace.{w, w} A]
    ⦃f₀ f₁ : C(A, B)⦄ (H : f₀.Homotopy f₁) ⦃g₀ : C(A, E)⦄ (hg₀ : p.comp g₀ = f₀) :
    ∃ g₁ : C(A, E), ∃ G : g₀.Homotopy g₁, p.comp G.toContinuousMap = H.toContinuousMap := by
  -- Route correction: eliminate the structure first so the lifting field becomes an ordinary
  -- theorem surface with the test-space universe fixed explicitly in the statement.
  -- Apply the covering homotopy property directly to the given initial lift.
  exact HasCoveringHomotopyProperty.homotopyLift.{u, v, w}
    (self := hp) (A := A) (f₀ := f₀) (f₁ := f₁) (g₀ := g₀) H hg₀

end HasCoveringHomotopyProperty

namespace IsFibration

variable {p : C(E, B)}

/-- An `IsFibration` map is surjective. -/
instance instSurjective [hp : IsFibration p] : Function.Surjective p := hp.surjective

/-- A fibration admits lifted homotopies for every compatible initial lift. -/
theorem exists_homotopyLift [hp : IsFibration.{u, v, w} p] ⦃A : Type w⦄ [TopologicalSpace A]
    [CompactlyGeneratedWeakHausdorffSpace.{w, w} A]
    ⦃f₀ f₁ : C(A, B)⦄ (H : f₀.Homotopy f₁) ⦃g₀ : C(A, E)⦄ (hg₀ : p.comp g₀ = f₀) :
    ∃ g₁ : C(A, E), ∃ G : g₀.Homotopy g₁, p.comp G.toContinuousMap = H.toContinuousMap := by
  -- Forward to the inherited covering homotopy property.
  exact HasCoveringHomotopyProperty.exists_homotopyLift H hg₀

end IsFibration
