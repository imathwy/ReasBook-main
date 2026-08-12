import Mathlib
import ProbabilityTheory_Klenke_2020.Chap05.Lemma_5_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v} [Finite E₁] [Finite E₂]

-- Proof sketch: compare the joint law `p` with the product of its two marginal laws and apply the
-- nonnegativity of relative entropy (equivalently, the cross-entropy bound) to obtain
-- `H(p) ≤ H(p.map Prod.fst) + H(p.map Prod.snd)`.
/-- Exercise 5.3.4: the entropy of a joint probability mass function on a finite product is at
most the sum of the entropies of its two marginal probability mass functions. -/
theorem entropy_le_entropy_map_fst_add_entropy_map_snd
    (p : PMF (E₁ × E₂)) :
    entropy p ≤ entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
  let b : LogBase := ⟨Real.exp 1, Real.exp_pos 1, ne_of_gt (Real.one_lt_exp_iff.2 zero_lt_one)⟩
  let p₁ : PMF E₁ := p.map Prod.fst
  let p₂ : PMF E₂ := p.map Prod.snd
  let q : E₁ × E₂ → ENNReal := fun x ↦ p₁ x.1 * p₂ x.2
  have hq : (∑' x : E₁ × E₂, q x) ≤ 1 := by
    sorry
  have hcross : crossEntropyInBase b p q = entropy p₁ + entropy p₂ := by
    sorry
  calc
    entropy p = entropyInBase b p := by
      simp [b]
    _ ≤ crossEntropyInBase b p q :=
      entropyInBase_le_crossEntropyInBase b (by
        change 1 < Real.exp 1
        exact Real.one_lt_exp_iff.2 zero_lt_one) p q hq
    _ = entropy p₁ + entropy p₂ := hcross
