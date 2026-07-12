import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Lemma_2_26

open scoped ContDiff Manifold

/- Exercise 2.27 is source-facing: it rules out a real-valued supported smooth extension of the
constant function `1` on `(0, ∞)`, showing the closedness hypothesis in Lemma 2.26 is necessary. -/

/-- The counterexample domain `(0, ∞) ⊆ ℝ` is not closed. -/
theorem not_isClosed_Ioi_zero : ¬ IsClosed (Set.Ioi (0 : ℝ)) := by
  intro h
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    simp
  have : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    rw [h.closure_eq] at h0
    exact h0
  have : False := by
    simp at this
  exact this

/-- Any function agreeing with a nonzero constant on `(0, ∞)` has `0` in its topological support. -/
theorem zero_mem_tsupport_of_eqOn_const_Ioi_zero {α : Type*} [Zero α] {F : ℝ → α} {c : α}
    (hc : c ≠ 0) (hF : Set.EqOn F (fun _ : ℝ ↦ c) (Set.Ioi (0 : ℝ))) :
    (0 : ℝ) ∈ tsupport F := by
  have hIoi : Set.Ioi (0 : ℝ) ⊆ tsupport F := by
    intro x hx
    apply subset_tsupport
    simpa [hF hx] using hc
  have hclosure : closure (Set.Ioi (0 : ℝ)) ⊆ tsupport F :=
    closure_minimal hIoi (isClosed_tsupport F)
  exact hclosure (by simp [closure_Ioi])

/-- Exercise 2.27 in the chapter's canonical smooth-function owner `C^∞⟮𝓘(ℝ), ℝ; ℝ⟯`: the
nonclosed set `(0, ∞)` admits no supported smooth extension of the constant function `1`. -/
theorem not_exists_supported_contMDiffMap_extension_Ioi_zero :
    ¬ ∃ F : C^∞⟮𝓘(ℝ), ℝ; ℝ⟯,
      Set.EqOn F 1 (Set.Ioi (0 : ℝ)) ∧
        tsupport F ⊆ Set.Ioi (0 : ℝ) := by
  rintro ⟨F, hF, hsupport⟩
  have h0 : (0 : ℝ) ∈ tsupport F :=
    zero_mem_tsupport_of_eqOn_const_Ioi_zero one_ne_zero (by simpa using hF)
  have : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := hsupport h0
  have : False := by
    simp at this
  exact this
