import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.PathToSet

open Topology
open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The homotopy fiber of the inclusion `A ↪ X` over the basepoint `x : A`, modeled as a point of
`A` together with a path in `X` from `x.1` to that point. -/
def inclusionHomotopyFiber (A : Set X) (x : A) : Type u :=
  { z : A × C(I, X) // z.2 0 = x.1 ∧ z.2 1 = z.1.1 }

namespace inclusionHomotopyFiber

variable {A : Set X} {x : A}

/-- `inclusionHomotopyFiber A x` carries the subtype topology inherited from `A × C(I, X)`. -/
instance instTopologicalSpace : TopologicalSpace (inclusionHomotopyFiber A x) :=
  inferInstanceAs
    (TopologicalSpace { z : A × C(I, X) // z.2 0 = x.1 ∧ z.2 1 = z.1.1 })

/-- The endpoint in `A` underlying a modeled inclusion homotopy fiber point. -/
def endpoint (z : inclusionHomotopyFiber A x) : A :=
  z.1.1

/-- The path in `X` underlying a modeled inclusion homotopy fiber point. -/
def path (z : inclusionHomotopyFiber A x) : Path x.1 z.endpoint.1 where
  toContinuousMap := z.1.2
  source' := z.2.1
  target' := z.2.2

/-- Construct a modeled inclusion homotopy fiber point from an endpoint in `A` and a path from
`x.1` to that endpoint. -/
def mk (y : A) (γ : Path x.1 y.1) : inclusionHomotopyFiber A x :=
  ⟨(y, γ.toContinuousMap), ⟨γ.source', γ.target'⟩⟩

end inclusionHomotopyFiber

/-- Turn a point of the modeled homotopy fiber into a path beginning at `x.1` and ending in `A`.
-/
def inclusionHomotopyFiberToPathToSet (A : Set X) (x : A) :
    inclusionHomotopyFiber A x → PathToSet A x.1
  | z =>
      { endpoint := inclusionHomotopyFiber.endpoint z
        path := inclusionHomotopyFiber.path z }

/-- Turn a path from `x.1` to `A` into a point of the modeled homotopy fiber of `A ↪ X`. -/
def pathToSetToInclusionHomotopyFiber (A : Set X) (x : A) :
    PathToSet A x.1 → inclusionHomotopyFiber A x
  | γ =>
      inclusionHomotopyFiber.mk γ.endpoint γ.path

/-- The map from the inclusion homotopy fiber to `PathToSet` has the expected inverse. -/
theorem inclusionHomotopyFiberToPathToSet_leftInverse (A : Set X) (x : A) :
    Function.LeftInverse (pathToSetToInclusionHomotopyFiber A x)
      (inclusionHomotopyFiberToPathToSet A x) := by
  intro z
  -- Unpack the modeled fiber point; the round-trip only repackages the same endpoint and path.
  rcases z with ⟨⟨y, γ⟩, hγ₀, hγ₁⟩
  rfl

/-- The map from `PathToSet` to the inclusion homotopy fiber has the expected inverse. -/
theorem inclusionHomotopyFiberToPathToSet_rightInverse (A : Set X) (x : A) :
    Function.RightInverse (pathToSetToInclusionHomotopyFiber A x)
      (inclusionHomotopyFiberToPathToSet A x) := by
  intro γ
  -- Unpack the endpoint-plus-path data; the round-trip is definitionally unchanged.
  rcases γ with ⟨y, γ⟩
  rfl

/-- The canonical map from `PathToSet A x.1` into the modeled inclusion homotopy fiber is an
embedding. -/
theorem pathToSetToInclusionHomotopyFiber_isEmbedding (A : Set X) (x : A) :
    IsEmbedding (pathToSetToInclusionHomotopyFiber A x) := by
  have hcomp : IsEmbedding
      ((Subtype.val : inclusionHomotopyFiber A x → A × C(I, X)) ∘
        pathToSetToInclusionHomotopyFiber A x) := by
    change IsEmbedding (PathToSet.endpointAndPath A x)
    exact (PathToSet.endpointAndPath_injective (A := A) (x := x)).isEmbedding_induced
  exact
    (IsEmbedding.of_comp_iff
      (g := (Subtype.val : inclusionHomotopyFiber A x → A × C(I, X)))
      IsEmbedding.subtypeVal).mp hcomp

/-- Definition 9.1.4. For `x : A`, the homotopy fiber of the inclusion `A ↪ X` over `x.1` is
homeomorphic to `PathToSet A x.1`, the paths in `X` beginning at the basepoint and ending in
`A`. -/
noncomputable def inclusionHomotopyFiberHomeomorphPathToSet (A : Set X) (x : A) :
    inclusionHomotopyFiber A x ≃ₜ PathToSet A x.1 :=
  (pathToSetToInclusionHomotopyFiber_isEmbedding A x).toHomeomorphOfSurjective
    (inclusionHomotopyFiberToPathToSet_leftInverse A x).surjective |>.symm

/-- `inclusionHomotopyFiberHomeomorphPathToSet` acts by sending a point of the modeled inclusion
homotopy fiber to its associated path ending in `A`. -/
@[simp] theorem inclusionHomotopyFiberHomeomorphPathToSet_apply (A : Set X) (x : A)
    (z : inclusionHomotopyFiber A x) :
    inclusionHomotopyFiberHomeomorphPathToSet A x z = inclusionHomotopyFiberToPathToSet A x z :=
  by
    let e : PathToSet A x.1 ≃ₜ inclusionHomotopyFiber A x :=
      (pathToSetToInclusionHomotopyFiber_isEmbedding A x).toHomeomorphOfSurjective
        (inclusionHomotopyFiberToPathToSet_leftInverse A x).surjective
    -- Compare both sides after applying the forward homeomorphism `e`.
    apply e.injective
    change e (e.symm z) =
      pathToSetToInclusionHomotopyFiber A x (inclusionHomotopyFiberToPathToSet A x z)
    -- The left side cancels by the homeomorphism laws, and the right side is the left-inverse map.
    simpa [e] using inclusionHomotopyFiberToPathToSet_leftInverse A x z
