module

public import Topology_Munkres_2000.Book.Exercise_48_10.UniformBoundedness
import Mathlib.Topology.Baire.CompleteMetrizable

public section

universe u

/-- Exercise 48.10. The uniform boundedness principle for a pointwise bounded set of
continuous real-valued functions on a nonempty complete metric space. -/
theorem uniformBoundednessPrinciple {X : Type u} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] (𝓕 : Set (ContinuousMap X ℝ))
    (h𝓕 : 𝓕.PointwiseBounded) :
    ∃ U : Set X, U.Nonempty ∧ IsOpen U ∧
      ∃ M : ℝ, ∀ x ∈ U, ∀ f ∈ 𝓕, |f x| ≤ M := by
  -- Apply the Baire-space theorem to the family indexed by the subtype `𝓕`.
  obtain ⟨U, hU, hUopen, M, hM⟩ :=
    PointwiseBounded.existsOpenUniformBound
      (fun f : 𝓕 ↦ (f : ContinuousMap X ℝ)) h𝓕
  refine ⟨U, hU, hUopen, M, ?_⟩
  -- Package ambient functions with their membership proofs to use the indexed bound.
  intro x hx f hf
  exact hM x hx ⟨f, hf⟩
