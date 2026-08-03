import BauschkeLean.Chap27.Proposition_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open ContinuousLinearMap
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u v

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Remark 26.29 records the `zero_mem_sri` specialization of the composite
  primal/dual optimality picture.
- `core/canonical`: the owner objects are `compositePrimalObjective`, `compositeDualObjective`,
  `CompositePrimalObjectiveRegularity`, and
  `primal_dual_solution_tfae_for_composite_objective`.
- `bridge/view`: Chapter 27 supplies both the primal argmin/zero-set identification and the
  `zero_mem_sri` dual-certificate whose value component recovers the strong-duality identity.

Primitive data: the functions `f`, `g`, the operator `L`, and the `zero_mem_sri` hypothesis.
Derived API: the argmin/zero-set identification and the primal-dual optimality equivalence below.
-/

section CompositeDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

section

variable {f : H → Set.Ioi (⊥ : EReal)}
variable {g : K → Set.Ioi (⊥ : EReal)}

/-- Remark 26.29 (1): under `0 ∈ sri (dom g - L (dom f))`, the primal operator-inclusion zero set
coincides with the minimizer set of the composite primal objective. This is the
`CompositePrimalObjectiveRegularity.zero_mem_sri` specialization of the Chapter 27 owner theorem
`argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular`. -/
theorem argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_zero_mem_sri
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    Argmin (compositePrimalObjective f g L) =
      ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L g).zeros := by
  simpa using
    argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular
      hf hg L (.zero_mem_sri hsri)

/-- Remark 26.29 (2): under the same `zero_mem_sri` regularity hypothesis, the paired
operator-duality relations are exactly simultaneous primal and dual optimality for
`compositePrimalObjective f g L` and `compositeDualObjective f g L`, expressed as membership of
`(x, v)` in the product of the primal and dual argmin sets. -/
theorem subgradient_pair_iff_composite_primal_dual_optimality_of_zero_mem_sri
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f))
    (x : H) (v : K) :
    (-L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x)) ↔
      (x, v) ∈ Argmin (compositePrimalObjective f g L) ×ˢ
        Argmin (compositeDualObjective f g L) := by
  have hregular : CompositePrimalObjectiveRegularity f g L := .zero_mem_sri hsri
  have hstrong :
      compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L :=
    by
      rcases
          exists_mem_argmin_compositeDualObjective_and_strongDuality_of_regular
            hf hg L hregular with
        ⟨_, _, hstrong⟩
      exact hstrong
  have htfae := primal_dual_solution_tfae_for_composite_objective hf hg L x v
  have hiff := List.TFAE.out htfae 1 0
  constructor
  · intro hsub
    rcases hiff.1 hsub with ⟨hx, hv, _⟩
    exact Set.mem_prod.mpr ⟨hx, hv⟩
  · intro hopt
    rcases Set.mem_prod.mp hopt with ⟨hx, hv⟩
    exact hiff.2 ⟨hx, hv, hstrong⟩

/-- Companion form of Remark 26.29 (2): the same subgradient relations are equivalent to the
simultaneous primal and dual minimizer conditions, unpacked from the product-set formulation. -/
theorem subgradient_pair_iff_mem_argmin_compositePrimal_and_dual_of_zero_mem_sri
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f))
    (x : H) (v : K) :
    (-L.adjoint v ∈ (∂ f) x ∧ v ∈ (∂ g) (L x)) ↔
      x ∈ Argmin (compositePrimalObjective f g L) ∧
        v ∈ Argmin (compositeDualObjective f g L) := by
  simpa [Set.mem_prod] using
    subgradient_pair_iff_composite_primal_dual_optimality_of_zero_mem_sri
      hf hg L hsri x v

/-- Remark 26.29 (3): the same `zero_mem_sri` hypothesis gives the strong-duality identity for
the composite primal and dual objectives. This is the value component of the Chapter 27
dual-certificate theorem specialized to `zero_mem_sri`. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_of_zero_mem_sri
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  have hregular : CompositePrimalObjectiveRegularity f g L := .zero_mem_sri hsri
  rcases
      exists_mem_argmin_compositeDualObjective_and_strongDuality_of_regular
        hf hg L hregular with
    ⟨_, _, hstrong⟩
  exact hstrong

end

end CompositeDuality

end ERealFunction
