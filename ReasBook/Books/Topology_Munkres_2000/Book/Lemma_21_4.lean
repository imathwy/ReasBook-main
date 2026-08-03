module

import Mathlib.Topology.Algebra.Ring.Real

/- Lemma 21.4 (1) -/
#check (continuous_add : Continuous (fun p : ℝ × ℝ ↦ p.1 + p.2))

/- Lemma 21.4 (2) -/
#check (continuous_sub : Continuous (fun p : ℝ × ℝ ↦ p.1 - p.2))

/- Lemma 21.4 (3) -/
#check (continuous_mul : Continuous (fun p : ℝ × ℝ ↦ p.1 * p.2))

/- Lemma 21.4 (4) -/
#check (continuous_fst.div (continuous_subtype_val.comp continuous_snd)
  (fun p : ℝ × {y : ℝ // y ≠ 0} ↦ p.2.property) :
    Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} ↦ p.1 / p.2))
