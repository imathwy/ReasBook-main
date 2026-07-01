import cartan.III.section08.«0002_Theorem_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

variable {f : ℂ → ℂ} {D S T : Set ℂ} {M : ℝ}

namespace HasMeanValuePropertyOn

/-- Helper for Corollary III.2-extra-2: restricting the domain preserves the mean value property. -/
lemma mono (hf : HasMeanValuePropertyOn f T) (hST : S ⊆ T) :
    HasMeanValuePropertyOn f S where
  continuousOn := hf.continuousOn.mono hST
  circleAverage_eq hclosed := hf.circleAverage_eq (Subset.trans hclosed hST)

end HasMeanValuePropertyOn

/-- Helper for Corollary III.2-extra-2: the frontier of a connected component inside an open set
stays on the frontier of the ambient set. -/
lemma frontier_connectedComponentIn_subset_frontier
    (hD_open : IsOpen D) {z : ℂ} (hz : z ∈ D) :
    frontier (connectedComponentIn D z) ⊆ frontier D := by
  let C : Set ℂ := connectedComponentIn D z
  have hC_subset : C ⊆ D := connectedComponentIn_subset D z
  have hC_open : IsOpen C := hD_open.connectedComponentIn
  have hcomp_closed : IsClosed (connectedComponent (⟨z, hz⟩ : D)) := isClosed_connectedComponent
  obtain ⟨t, ht_closed, ht_image⟩ :=
    hcomp_closed.image_val
  have hC_eq : C = t ∩ D := by
    simpa [C, connectedComponentIn_eq_image hz] using ht_image
  have hclosureC_subset_t : closure C ⊆ t := by
    rw [hC_eq]
    exact closure_minimal inter_subset_left ht_closed
  intro x hx
  have hxC : x ∈ frontier C := by
    simpa [C] using hx
  have hx' : x ∈ closure C ∧ x ∉ C := by
    rw [hC_open.frontier_eq] at hxC
    simpa using hxC
  have hx_not_memD : x ∉ D := by
    intro hxD
    have hxt : x ∈ t := hclosureC_subset_t hx'.1
    have hxC : x ∈ C := by
      rw [hC_eq]
      exact ⟨hxt, hxD⟩
    exact hx'.2 hxC
  refine ⟨closure_mono hC_subset hx'.1, ?_⟩
  simpa [hD_open.interior_eq] using hx_not_memD

/-- Helper for Corollary III.2-extra-2: a global norm bound on `S` makes every point of the
equality fiber into a local maximum of `‖f‖` on `S`. -/
lemma global_norm_bound_gives_local_max_on_fiber
    {a x : ℂ} (_hx : x ∈ S) (hfx : f x = f a)
    (hbound : ∀ z ∈ S, ‖f z‖ ≤ ‖f a‖) :
    IsLocalMaxOn (norm ∘ f) S x := by
  -- The global bound already gives the needed neighborhood bound on `𝓝[S] x`.
  rw [IsLocalMaxOn, IsMaxFilter, eventually_nhdsWithin_iff]
  exact Filter.Eventually.of_forall fun y hyS => by
    calc
      ‖f y‖ ≤ ‖f a‖ := hbound y hyS
      _ = ‖f x‖ := by simp [hfx]

/-- Helper for Corollary III.2-extra-2: under a global norm bound, the equality fiber
`{x ∈ S | f x = f a}` is clopen in the subtype `S`. -/
lemma isClopen_subtype_fiber_of_global_norm_max
    (hS_open : IsOpen S) (hf_contS : ContinuousOn f (closure S))
    (hfS : HasMeanValuePropertyOn f S) {a : ℂ} (_ha : a ∈ S)
    (hbound : ∀ z ∈ S, ‖f z‖ ≤ ‖f a‖) :
    IsClopen {x : S | f x = f a} := by
  refine ⟨?_, ?_⟩
  · -- Closedness is the preimage of a closed singleton under the restricted continuous map.
    have hcont_restrict : Continuous (S.restrict f) :=
      (hf_contS.mono subset_closure).restrict
    simpa using isClosed_singleton.preimage hcont_restrict
  · -- Openness comes from the local constancy furnished by the maximum-modulus principle.
    refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    have hxS : (x : ℂ) ∈ S := x.2
    have hlocal_max : IsLocalMaxOn (norm ∘ f) S (x : ℂ) :=
      global_norm_bound_gives_local_max_on_fiber (f := f) hxS hx hbound
    have hconst :
        f =ᶠ[𝓝[S] (x : ℂ)] Function.const ℂ (f x) :=
      maximum_modulus_principle hS_open hfS hxS hlocal_max
    have hconst_a : ∀ᶠ y in 𝓝[S] (x : ℂ), f y = f a := by
      filter_upwards [hconst] with y hy
      exact hy.trans hx
    change ((↑) : S → ℂ) ⁻¹' {y : ℂ | f y = f a} ∈ 𝓝 x
    exact (preimage_coe_mem_nhds_subtype).2 hconst_a

-- Proof sketch: let `M'` be the maximum of `‖f‖` on the compact set `closure D`,
-- using continuity on
-- `closure D` and boundedness of `D`. If `‖f‖` exceeded `M` somewhere in `D`, then a point of
-- `closure D` where `‖f‖ = M'` could not lie on `frontier D`, so it would lie in `D`; applying the
-- local maximum-modulus theorem there would force `f` to be locally constant, hence constant on the
-- corresponding connected component, contradicting the boundary bound.
/-- Corollary III.2-extra-2 (1): if a complex-valued function is continuous on `closure D`, has the
mean value property on the bounded open set `D`, and `M` bounds its norm on `frontier D`, then
`‖f z‖ ≤ M` for every `z ∈ D`. -/
theorem norm_le_boundary_bound_of_hasMeanValuePropertyOn
    (hD_open : IsOpen D) (hD_bdd : Bornology.IsBounded D)
    (hf_cont : ContinuousOn f (closure D)) (hf : HasMeanValuePropertyOn f D)
    (hM : ∀ z ∈ frontier D, ‖f z‖ ≤ M) :
    ∀ z ∈ D, ‖f z‖ ≤ M := by
  intro z hz
  let C : Set ℂ := connectedComponentIn D z
  have hC_subset : C ⊆ D := connectedComponentIn_subset D z
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hC_open : IsOpen C := hD_open.connectedComponentIn
  have hC_preconnected : IsPreconnected C := isPreconnected_connectedComponentIn
  have hC_bdd : Bornology.IsBounded C := hD_bdd.subset hC_subset
  have hf_contC : ContinuousOn f (closure C) := hf_cont.mono (closure_mono hC_subset)
  have hfC : HasMeanValuePropertyOn f C := hf.mono hC_subset
  by_contra hzM
  have hzM' : M < ‖f z‖ := lt_of_not_ge hzM
  -- Restrict to the connected component of `z` and maximize `‖f‖` on its compact closure.
  obtain ⟨a, haC, ha_max⟩ :=
    hC_bdd.isCompact_closure.exists_isMaxOn ⟨z, subset_closure hzC⟩ hf_contC.norm
  rw [isMaxOn_iff] at ha_max
  have ha_not_frontier : a ∉ frontier C := by
    intro ha_frontier
    have ha_bound : ‖f a‖ ≤ M := by
      exact hM a (frontier_connectedComponentIn_subset_frontier hD_open hz ha_frontier)
    have hz_le : ‖f z‖ ≤ ‖f a‖ := ha_max z (subset_closure hzC)
    exact hzM'.not_ge (le_trans hz_le ha_bound)
  have ha : a ∈ C := by
    -- The maximizer lies in the interior of the component, not on its frontier.
    rw [closure_eq_self_union_frontier, mem_union] at haC
    rcases haC with ha | ha_frontier
    · exact ha
    · exact False.elim (ha_not_frontier ha_frontier)
  have hboundC : ∀ w ∈ C, ‖f w‖ ≤ ‖f a‖ := fun w hw ↦ ha_max w (subset_closure hw)
  have hfiber_clopen : IsClopen {x : C | f x = f a} :=
    isClopen_subtype_fiber_of_global_norm_max (f := f) hC_open hf_contC hfC ha hboundC
  have hfiber_eq_univ : {x : C | f x = f a} = univ := by
    -- A nonempty clopen subset of the preconnected subtype `C` must be everything.
    letI : PreconnectedSpace C := Subtype.preconnectedSpace hC_preconnected
    refine IsClopen.eq_univ hfiber_clopen ?_
    exact ⟨⟨a, ha⟩, by simp⟩
  have hEqC : EqOn f (Function.const ℂ (f a)) C := by
    -- The clopen fiber equality says that `f` is constant on the whole component.
    intro w hw
    have hmem : (⟨w, hw⟩ : C) ∈ {x : C | f x = f a} := by
      rw [hfiber_eq_univ]
      trivial
    simpa using hmem
  have hEqClosureC : EqOn f (Function.const ℂ (f a)) (closure C) :=
    Set.EqOn.of_subset_closure hEqC hf_contC continuousOn_const subset_closure Subset.rfl
  have hC_ne_univ : C ≠ univ := by
    intro hC_univ
    exact (NormedSpace.unbounded_univ (𝕜 := ℂ) (E := ℂ)) (hC_univ ▸ hC_bdd)
  have hfrontierC_nonempty : (frontier C).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨z, hzC⟩, hC_ne_univ⟩
  obtain ⟨b, hb_frontier⟩ := hfrontierC_nonempty
  have hb_closure : b ∈ closure C := by
    have hb' : b ∈ closure C \ C := by
      simpa [hC_open.frontier_eq] using hb_frontier
    exact hb'.1
  have hb_bound : ‖f b‖ ≤ M := by
    exact hM b (frontier_connectedComponentIn_subset_frontier hD_open hz hb_frontier)
  have hz_eq : f z = f a := hEqC hzC
  have hb_eq : f b = f a := hEqClosureC hb_closure
  -- The constant value on `closure C` reaches the frontier, contradicting the strict interior bound.
  have hz_bound : ‖f z‖ ≤ M := by
    calc
      ‖f z‖ = ‖f a‖ := by simp [hz_eq]
      _ = ‖f b‖ := by simp [hb_eq]
      _ ≤ M := hb_bound
  exact hzM'.not_ge hz_bound

-- Proof sketch: first apply `norm_le_boundary_bound_of_hasMeanValuePropertyOn` to see that
-- `‖f a‖ = M` is a global maximum of `‖f‖` on `D`. The local maximum-modulus theorem then shows
-- that `f` is locally constant at `a`; the locus where `f = f a` is nonempty, open in `D`, and
-- closed in `D` by continuity, so preconnectedness gives constancy on `D`, and continuity extends
-- this equality to `closure D`.
/-- Corollary III.2-extra-2 (2): if, under the same hypotheses, `‖f a‖ = M` at some interior point
`a ∈ D`, then `f` is constant on `closure D`. -/
theorem eqOn_closure_of_hasMeanValuePropertyOn_of_norm_eq_boundary_bound
    {a : ℂ}
    (hD_open : IsOpen D) (hD_preconnected : IsPreconnected D) (hD_bdd : Bornology.IsBounded D)
    (hf_cont : ContinuousOn f (closure D)) (hf : HasMeanValuePropertyOn f D)
    (hM : ∀ z ∈ frontier D, ‖f z‖ ≤ M) (ha : a ∈ D) (haM : ‖f a‖ = M) :
    EqOn f (Function.const ℂ (f a)) (closure D) := by
  -- First promote the boundary estimate to the whole domain, with `a` realizing the bound.
  have hboundD : ∀ z ∈ D, ‖f z‖ ≤ ‖f a‖ := by
    intro z hz
    have hz_bound :=
      norm_le_boundary_bound_of_hasMeanValuePropertyOn hD_open hD_bdd hf_cont hf hM z hz
    simpa [haM] using hz_bound
  have hfiber_clopen : IsClopen {x : D | f x = f a} :=
    isClopen_subtype_fiber_of_global_norm_max (f := f) hD_open hf_cont hf ha hboundD
  have hfiber_eq_univ : {x : D | f x = f a} = univ := by
    -- The equality fiber is nonempty and clopen in the preconnected subtype `D`.
    letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_preconnected
    refine IsClopen.eq_univ hfiber_clopen ?_
    exact ⟨⟨a, ha⟩, by simp⟩
  have hEqD : EqOn f (Function.const ℂ (f a)) D := by
    -- The clopen-fiber argument gives constancy on all of `D`.
    intro z hz
    have hmem : (⟨z, hz⟩ : D) ∈ {x : D | f x = f a} := by
      rw [hfiber_eq_univ]
      trivial
    simpa using hmem
  -- Continuity extends the interior constancy to the closure.
  exact Set.EqOn.of_subset_closure hEqD hf_cont continuousOn_const subset_closure Subset.rfl
