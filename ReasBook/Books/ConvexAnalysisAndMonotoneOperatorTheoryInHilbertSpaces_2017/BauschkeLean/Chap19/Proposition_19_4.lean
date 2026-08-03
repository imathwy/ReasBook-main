import BauschkeLean.Chap19.Corollary_19_2
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.4 is the textbook uniqueness consequence for primal solutions of
  the composite Fenchel dual pair.
- `core/canonical`: the owner result already in Chapter 19 is
  `argmin_compositePrimalObjective_eq_conjugateSubdifferential_inter_preimage_of_dual_solution`.
- `bridge/view`: Proposition 19.4 keeps the source-facing `Argmin` surface and records the
  resulting empty-or-singleton conclusion together with the pointwise uniqueness consequence. -/

-- Semantic search note: `lean_leansearch` did not surface a useful direct owner for this
-- composite-duality uniqueness statement, so the file follows the local Chapter 19 owner API
-- from Corollary 19.2 and leaves the Chapter 17 singleton-subdifferential bridge implicit in the
-- statement skeleton.

/-- Helper for Proposition 19.4: any primal minimizer produces a point in the domain of the
conjugate subdifferential, hence `-L.adjoint v` lies in the effective domain of `f∗[hf]`. -/
lemma dual_argument_mem_effectiveDomain_gammaZeroConjugate_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (_hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDualMap ℝ H xstar) (-L.adjoint v))
    (x : H) (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    -L.adjoint v ∈ effectiveDomain (f∗[hf]) := by
  let hconj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hx_sub :
      x ∈ (∂ (f∗[hf])) (-L.adjoint v) := by
    -- Corollary 19.2 rewrites primal optimality into the source subdifferential intersection.
    exact
      (mem_argmin_compositePrimalObjective_iff_of_dual_solution
        hf hg L v hstrong hv x).1 hx |>.1
  have hdom :
      -L.adjoint v ∈ SetValuedOperator.dom (∂ (f∗[hf])) := by
    -- A concrete subgradient witness puts `-L.adjoint v` in the subdifferential domain.
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨x, hx_sub⟩
  -- The Chapter 16 domain inclusion upgrades domain membership to effective-domain membership.
  exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hconj hdom

/-- Helper for Proposition 19.4: once a primal minimizer exists, the conjugate subdifferential at
`-L.adjoint v` collapses to the singleton `{xstar}`. -/
lemma conjugate_subdifferential_eq_singleton_at_neg_adjoint_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDualMap ℝ H xstar) (-L.adjoint v))
    (x : H) (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    (∂ (f∗[hf])) (-L.adjoint v) = ({xstar} : Set H) := by
  let hconj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hdom :
      -L.adjoint v ∈ effectiveDomain (f∗[hf]) :=
    dual_argument_mem_effectiveDomain_gammaZeroConjugate_of_mem_argmin
      hf hg L v xstar hstrong hv hgrad x hx
  -- Proposition 17.31 collapses the conjugate subdifferential fiber to the Gâteaux gradient.
  simpa using
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt
      (f := f∗[hf]) hdom xstar hgrad

/-- Companion to Proposition 19.4: every primal minimizer equals the Gâteaux gradient `xstar` of
`fun y : H ↦ ((f∗[hf]) y : EReal).toReal` at `-L.adjoint v`. -/
theorem
    eq_of_mem_argmin_compositePrimalObjective_of_dual_solution_and_hasGateauxDerivativeAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDualMap ℝ H xstar) (-L.adjoint v))
    (x : H) (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    x = xstar := by
  have hx_sub :
      x ∈ (∂ (f∗[hf])) (-L.adjoint v) := by
    -- Corollary 19.2 supplies the inclusion `Argmin ... ⊆ ∂ f^*(-L^* v)`.
    exact
      (mem_argmin_compositePrimalObjective_iff_of_dual_solution
        hf hg L v hstrong hv x).1 hx |>.1
  have hsingleton :
      (∂ (f∗[hf])) (-L.adjoint v) = ({xstar} : Set H) :=
    conjugate_subdifferential_eq_singleton_at_neg_adjoint_of_mem_argmin
      hf hg L v xstar hstrong hv hgrad x hx
  -- Rewriting by the singleton identity identifies every primal minimizer with `xstar`.
  rw [hsingleton, Set.mem_singleton_iff] at hx_sub
  exact hx_sub

/-- Proposition 19.4. If `f ∈ Γ₀(ℋ)` and `g ∈ Γ₀(𝒦)`, if the primal infimum of
`x ↦ f x + g (L x)` equals the negative minimum of the dual objective
`v ↦ (f∗[hf]) (-L.adjoint v) + (g∗[hg]) v`, and if `v` is a dual solution at which
`fun y : H ↦ ((f∗[hf]) y : EReal).toReal` has Gâteaux gradient `xstar` at `-L.adjoint v`, then
`Argmin (compositePrimalObjective f g L)` is either empty or `{xstar}`. This is the source
equation `(19.7)` packaged on the canonical `Argmin` surface. -/
theorem argmin_eq_empty_or_singleton_of_dual_solution_and_hasGateauxDerivativeAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (v : K) (xstar : H)
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    (hv : v ∈ Argmin (compositeDualObjective f g L))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f∗[hf] y : EReal).toReal)
        (toDualMap ℝ H xstar) (-L.adjoint v))
    :
    Argmin (compositePrimalObjective f g L) = (∅ : Set H) ∨
      Argmin (compositePrimalObjective f g L) = ({xstar} : Set H) := by
  classical
  by_cases harg : (Argmin (compositePrimalObjective f g L)).Nonempty
  · rcases harg with ⟨x, hx⟩
    have hx_eq : x = xstar :=
      eq_of_mem_argmin_compositePrimalObjective_of_dual_solution_and_hasGateauxDerivativeAt
        hf hg L v xstar hstrong hv hgrad x hx
    have hxstar_mem : xstar ∈ Argmin (compositePrimalObjective f g L) := by
      -- Rewriting the chosen primal minimizer along uniqueness produces the singleton witness.
      simpa [hx_eq] using hx
    -- The pointwise uniqueness theorem upgrades the nonempty argmin set to `{xstar}`.
    exact Or.inr <|
      Set.eq_singleton_iff_unique_mem.2 ⟨hxstar_mem, by
        intro y hy
        exact
          eq_of_mem_argmin_compositePrimalObjective_of_dual_solution_and_hasGateauxDerivativeAt
            hf hg L v xstar hstrong hv hgrad y hy⟩
  · -- If no minimizer exists, the `Argmin` set is definitionally empty.
    exact Or.inl <|
      Set.eq_empty_iff_forall_notMem.2 <| by
        intro x hx
        exact harg ⟨x, hx⟩

end PrimalSolutionsViaDualSolutions

end ERealFunction
