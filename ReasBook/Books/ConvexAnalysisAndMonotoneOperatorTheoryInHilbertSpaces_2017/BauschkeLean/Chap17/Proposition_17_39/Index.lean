import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap16.Proposition_16_27

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 17 39: an interior effective-domain point is a continuity point on the
effective domain. -/
lemma continuousAtOnEffectiveDomain_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ContinuousAtOnEffectiveDomain f x := by
  -- Proposition 16.27 first turns interior-domain membership into the source continuity
  -- predicate `ContinuousPoint f x`.
  have hxcont : ContinuousPoint f x :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  -- The Chapter 16 bridge then upgrades the source continuity predicate to the owner predicate.
  exact ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain hxcont

/-- Helper for Proposition 17 39: an interior effective-domain point lies in the domain of the
subdifferential. -/
lemma mem_subdifferentialDomain_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    x ∈ SetValuedOperator.dom (∂ f) := by
  -- Proposition 16.27 sends the source continuity predicate `ContinuousPoint f x` into
  -- `dom (∂ f)`.
  have hxcont : ContinuousPoint f x :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  exact continuitySet_subset_subdifferentialDomain_of_mem_gammaZero hf hxcont

/-- Helper for Proposition 17 39: short rays from an interior effective-domain point remain in the
domain of the subdifferential. -/
lemma small_segment_subset_subdifferentialDom
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∀ y : H, ∃ α : ℝ, 0 < α ∧
      ∀ t ∈ Set.Icc (0 : ℝ) α, x + t • y ∈ SetValuedOperator.dom (∂ f) := by
  intro y
  have hsegments :
      HasRadialSegmentsAt (interior (effectiveDomain f)) x :=
    HasRadialSegmentsAt.of_mem_nhds (by
      simpa [mem_interior_iff_mem_nhds] using hx)
  rcases hsegments y with ⟨α, hαpos, hαmem⟩
  refine ⟨α, hαpos, ?_⟩
  intro t ht
  -- Nearby interior-domain points first become source continuity points, then subdifferentiable.
  exact mem_subdifferentialDomain_of_mem_interior_effectiveDomain hf (hαmem t ht)

end DifferentiabilityOfConvexFunctions

end ERealFunction
