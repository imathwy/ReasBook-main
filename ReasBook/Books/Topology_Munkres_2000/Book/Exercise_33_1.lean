module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

universe u

/-- Helper for Exercise 33.1: equality `f x = r` determines the upper-membership and
lower-nonmembership rational cuts of `x`. -/
lemma rationalCutConditionsOfEq {X : Type u} [TopologicalSpace X]
    (U : ℚ → Set X) (f : X → ℝ)
    (h_le : ∀ q x, x ∈ closure (U q) → f x ≤ q)
    (h_ge : ∀ q x, x ∉ U q → q ≤ f x) {x : X} {r : ℝ} (hxr : f x = r) :
    (∀ p : ℚ, r < p → x ∈ U p) ∧ (∀ q : ℚ, q < r → x ∉ U q) := by
  -- A missing upper-cut membership would force the rational endpoint below `f x = r`.
  constructor
  · intro p hrp
    by_contra hxp
    have hpr : (p : ℝ) ≤ r := by
      rw [← hxr]
      exact h_ge p x hxp
    exact (not_le_of_gt hrp) hpr
  -- Lower-cut membership passes to the closure and contradicts the upper estimate.
  · intro q hqr hxq
    have hrq : r ≤ (q : ℝ) := by
      rw [← hxr]
      exact h_le q x (subset_closure hxq)
    exact (not_le_of_gt hqr) hrq

/-- Helper for Exercise 33.1: the upper-membership and lower-nonmembership rational cuts
determine the value `f x = r`. -/
lemma eqOfRationalCutConditions {X : Type u} [TopologicalSpace X]
    (U : ℚ → Set X) (f : X → ℝ)
    (h_le : ∀ q x, x ∈ closure (U q) → f x ≤ q)
    (h_ge : ∀ q x, x ∉ U q → q ≤ f x) {x : X} {r : ℝ}
    (h_upper : ∀ p : ℚ, r < p → x ∈ U p)
    (h_lower : ∀ q : ℚ, q < r → x ∉ U q) : f x = r := by
  -- Density rules out `r < f x`: an intermediate rational would also bound `f x` above.
  have hfr : f x ≤ r := by
    by_contra hnot
    obtain ⟨p, hrp, hpf⟩ := exists_rat_btwn (lt_of_not_ge hnot)
    have hfp : f x ≤ (p : ℝ) := h_le p x (subset_closure (h_upper p hrp))
    exact (not_le_of_gt hpf) hfp
  -- Symmetrically, an intermediate rational rules out `f x < r`.
  have hrf : r ≤ f x := by
    by_contra hnot
    obtain ⟨q, hfq, hqr⟩ := exists_rat_btwn (lt_of_not_ge hnot)
    have hqf : (q : ℝ) ≤ f x := h_ge q x (h_lower q hqr)
    exact (not_le_of_gt hfq) hqf
  exact le_antisymm hfr hrf

/-- Exercise 33.1: For the rationally indexed sets `U p` and function `f` in the proof
of Urysohn's lemma, the fiber over `r` is the intersection of the `U p` for `r < p`,
minus the union of the `U q` for `q < r`. -/
theorem fiber_eq_iInter_diff_iUnion_rat {X : Type u} [TopologicalSpace X]
    (U : ℚ → Set X) (f : X → ℝ)
    (h_le : ∀ q x, x ∈ closure (U q) → f x ≤ q)
    (h_ge : ∀ q x, x ∉ U q → q ≤ f x) (r : ℝ) :
    f ⁻¹' {r} = (⋂ (p : ℚ) (_ : r < p), U p) \ ⋃ (q : ℚ) (_ : q < r), U q := by
  -- Extensionality reduces the set identity to the two rational cut conditions at each point.
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_iInter,
    Set.mem_iUnion]
  constructor
  · intro hxr
    obtain ⟨h_upper, h_lower⟩ := rationalCutConditionsOfEq U f h_le h_ge hxr
    refine ⟨h_upper, ?_⟩
    rintro ⟨q, hqr, hxq⟩
    exact h_lower q hqr hxq
  · rintro ⟨h_upper, h_lower_union⟩
    have h_lower : ∀ q : ℚ, q < r → x ∉ U q := by
      intro q hqr hxq
      exact h_lower_union ⟨q, hqr, hxq⟩
    exact eqOfRationalCutConditions U f h_le h_ge h_upper h_lower

end
