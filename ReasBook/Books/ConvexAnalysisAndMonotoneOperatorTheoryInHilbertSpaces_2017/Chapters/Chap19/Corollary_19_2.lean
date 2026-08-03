import BauschkeLean.Chap19.Theorem_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 19.2 identifies the primal minimizer set after fixing a dual
  solution.
- `core/canonical`: Theorem 19.1 is the owner TFAE for composite primal-dual optimality.
- `bridge/view`: the proof uses the clause `(i) ↔ (iii)` specialization of that TFAE, written
  with the canonical packaged conjugates `f∗[hf]` and `g∗[hg]`.
-/

-- Semantic search note: `lean_leansearch` did not surface a better direct owner than the local
-- Chapter 19 composite-duality API, so this item keeps the source-faithful argmin identity.

/-- Companion to Corollary 19.2: for a fixed dual solution `v`, membership in
`Argmin (compositePrimalObjective f g L)` is equivalent to membership in the source-facing set
`∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, represented by the canonical `Γ₀` conjugates `f∗[hf]`
and `g∗[hg]`. -/
theorem
    mem_argmin_compositePrimalObjective_iff_of_dual_solution
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (x : H) :
    x ∈ Argmin (compositePrimalObjective f g L) ↔
      x ∈ (∂ (f∗[hf])) (-L.adjoint v) ∩
        L ⁻¹' ((∂ (g∗[hg])) v) := by
  let htfae := primal_dual_solution_tfae_for_composite_objective hf hg L x v
  have hiff := List.TFAE.out htfae 0 2
  constructor
  · intro hx
    exact hiff.1 ⟨hx, hv, hstrong⟩
  · intro hx
    exact (hiff.2 hx).1

/-- Corollary 19.2: if `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, if the primal infimum of `x ↦ f x + g (L x)`
is the negative of the minimum of the dual objective `v ↦ f^*(-L^* v) + g^*(v)`, and if `v` is a
dual solution, then the primal solution set is `∂ f^*(-L^* v) ∩ L⁻¹(∂ g^*(v))`, represented by
the canonical `Γ₀` conjugates `f∗[hf]` and `g∗[hg]`. -/
theorem argmin_compositePrimalObjective_eq_conjugateSubdifferential_inter_preimage_of_dual_solution
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L)) :
    Argmin (compositePrimalObjective f g L) =
      (∂ (f∗[hf])) (-L.adjoint v) ∩
        L ⁻¹' ((∂ (g∗[hg])) v) := by
  ext x
  exact
    mem_argmin_compositePrimalObjective_iff_of_dual_solution
      hf hg L v hstrong hv x

end PrimalSolutionsViaDualSolutions

end ERealFunction
