import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.List.TFAE
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Proposition_16_16

open scoped InnerProductSpace Pointwise Set
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

-- Proof sketch: Proposition 16.16 gives the equivalence of clauses `(i)`, `(ii)`, and `(iii)`.
-- Corollary 16.30 identifies clause `(iv)` with clause `(i)` by rewriting `(∂ f)⁻¹` as the
-- subdifferential of the canonical packaged conjugate `gammaZeroConjugate f hf`.
/-- Theorem 16.29: for `f ∈ Γ₀(H)`, membership of `(x, u)` in the graph of `∂ f`,
membership of `(u, -1)` in the normal cone to `epi f` at `(x, f x)`, equality in the
Fenchel--Young identity, and membership of `(u, x)` in the graph of `∂ f^*` are equivalent.
In Lean, clauses (i) and (iv) are written as the corresponding subdifferential-membership
statements, and clause (ii) uses the real-height epigraph point
`(x, (f x : EReal).toReal)`. -/
theorem subdifferential_normalCone_fenchelYoung_conjugate_tfae
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x u : H) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal),
        x ∈ (∂ (gammaZeroConjugate f hf)) u] := by
  have hinv := inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf
  have h14 :
      u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u := by
    rw [← hinv]
    exact (SetValuedOperator.mem_inverse_iff (∂ f.asEReal) u x).symm
  by_cases hx : x ∈ effectiveDomain f
  · have htfae :=
      subdifferential_normalCone_fenchelYoung_tfae
        f (hf.2 : ConvexOn f (effectiveDomain f)) hf.2.nonempty x u hx
    have h12 :
        u ∈ (∂ f) x ↔
          (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
      simpa using (List.TFAE.out htfae 0 1)
    have h13 :
        u ∈ (∂ f) x ↔
          (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      simpa using (List.TFAE.out htfae 0 2)
    tfae_have 1 ↔ 2 := by
      change u ∈ (∂ f) x ↔
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
      exact h12
    tfae_have 1 ↔ 3 := by
      change u ∈ (∂ f) x ↔
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
      exact h13
    tfae_have 1 ↔ 4 := by
      change u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u
      exact h14
    tfae_finish
  · have hx_top : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have hx_not_epi : (x, (f x : EReal).toReal) ∉ epigraph f.asEReal := by
      intro hx_epi
      have hfx_lt_top : (f x : EReal) < ⊤ := by
        exact lt_of_le_of_lt ((mem_epigraph_iff f.asEReal x _).1 hx_epi) (EReal.coe_lt_top _)
      exact hx (mem_effectiveDomain_iff.2 hfx_lt_top)
    have h1false : ¬ u ∈ (∂ f) x := by
      intro hu
      have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨u, hu⟩
      exact hx (subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hx_subdom)
    have h2false :
        ¬ (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
      simp [Set.normalCone_of_not_mem hx_not_epi]
    have h3false :
        ¬ ((f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
      have hconj_ne_bot : f.asEReal∗ u ≠ ⊥ :=
        conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty u
      rw [hx_top, EReal.top_add_of_ne_bot hconj_ne_bot]
      simp
    tfae_have 1 ↔ 2 := by
      change u ∈ (∂ f) x ↔
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
      constructor
      · intro hu
        exact False.elim (h1false hu)
      · intro hu
        exact False.elim (h2false hu)
    tfae_have 1 ↔ 3 := by
      change u ∈ (∂ f) x ↔
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
      constructor
      · intro hu
        exact False.elim (h1false hu)
      · intro hu
        exact False.elim (h3false hu)
    tfae_have 1 ↔ 4 := by
      change u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u
      exact h14
    tfae_finish

end SubdifferentialConjugation

end

end ERealFunction
