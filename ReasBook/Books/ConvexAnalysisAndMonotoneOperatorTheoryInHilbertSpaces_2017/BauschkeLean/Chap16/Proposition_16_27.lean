import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall: `lean_leansearch` only returned generic convex-continuity facts, while verified
-- Chapter 16 precedent packages the source continuity set `cont f` as `ContinuousPoint f x`; the
-- reusable helper predicate `ContinuousAtOnEffectiveDomain f x` remains available separately.
-- Proof sketch: apply Corollary 8.39 to a member of `Γ₀(H)` to identify interior-domain points
-- with the source continuity-point predicate `ContinuousPoint f x`.
/-- Proposition 16.27 (1): for `f ∈ Γ₀(H)`, the interior of the effective domain is exactly the
set `{x : H | ContinuousPoint f x}` of source continuity points of `f`. -/
theorem interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    interior (effectiveDomain f) = {x : H | ContinuousPoint f x} := by
  -- Route correction: keep `hf` in the packed `Γ₀(H)` form expected by the Chapter 12 theorem.
  -- Corollary 8.39 identifies the source continuity set with the interior effective domain.
  simpa [ContinuousPoint] using
    (continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous f hf).symm

/-- Helper for Proposition 16.27: an interior effective-domain point of a `Γ₀(H)` function is a
source continuity point. -/
lemma continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ContinuousPoint f x := by
  -- Read the Chapter 12 set equality pointwise to recover the source continuity predicate.
  have hcontset : {y : H | ContinuousPoint f y} = interior (effectiveDomain f) := by
    simpa [ContinuousPoint] using
      continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous f hf
  have hxcont : x ∈ {y : H | ContinuousPoint f y} := by
    rwa [hcontset]
  simpa using hxcont

/-- Interior points of the effective domain of a `Γ₀(H)` function are continuity points on the
effective domain. -/
theorem interior_effectiveDomain_subset_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    interior (effectiveDomain f) ⊆ {x : H | ContinuousAtOnEffectiveDomain f x} := by
  intro x hx
  -- First recover the source continuity predicate directly from the Chapter 12 interior equality.
  have hxcont : ContinuousPoint f x :=
    continuousPoint_of_mem_interior_effectiveDomain_of_mem_gammaZero hf hx
  -- The Chapter 16 bridge turns source continuity into continuity on the effective domain.
  exact ContinuousAtOnEffectiveDomain.of_continuousAtInEffectiveDomain hxcont

-- Proof sketch: Proposition 16.17 (2) gives a nonempty subdifferential at each source continuity
-- point.
/-- Proposition 16.27 (2): every source continuity point of a `Γ₀(H)` function is a
subdifferentiability point. -/
theorem continuitySet_subset_subdifferentialDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {x : H | ContinuousPoint f x} ⊆ SetValuedOperator.dom (∂ f) := by
  have hγ := mem_gammaZero_iff.mp hf
  intro x hxcont
  -- Proposition 16.17 (2) gives a nonempty subdifferential at every source continuity point.
  rw [SetValuedOperator.mem_dom_iff]
  exact (subdifferential_nonempty_and_weaklyCompact_of_continuousPoint f hγ.2 hxcont).1

-- Proof sketch: Proposition 16.4 already supplies the canonical inclusion from the
-- subdifferential domain to the effective domain for functions with nonempty effective domain; a
-- `Γ₀(H)` function has that nonempty effective domain by convexity.
omit [CompleteSpace H] in
/-- Proposition 16.27 (3): if `f ∈ Γ₀(H)`, then the domain of `∂ f` is contained in the
effective domain of `f`. -/
theorem subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.dom (∂ f) ⊆ effectiveDomain f := by
  have hγ := mem_gammaZero_iff.mp hf
  -- Proposition 16.4 (1) applies because convexity supplies a point in the effective domain.
  exact subdifferential_domain_subset_effectiveDomain f hγ.2.nonempty

end SubdifferentialContinuity

end ERealFunction
