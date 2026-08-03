import BauschkeLean.Chap10.Proposition_10_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 10.17: `⊤` is an admissible `]-∞,+∞]` value. -/
private theorem ereal_bot_lt_top : (⊥ : EReal) < (⊤ : EReal) := by
  simp

/-- Helper for Proposition 10.17: localize an `]-∞,+∞]`-valued function to a set by keeping the
original value on the set and sending the complement to `⊤`. -/
private noncomputable def restrictToSet
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    @ite (Set.Ioi (⊥ : EReal)) (x ∈ C) (Classical.propDecidable _) (f x)
      ⟨⊤, ereal_bot_lt_top⟩

/-- Helper for Proposition 10.17: the localized function agrees with the original function on the
localizing set. -/
private theorem restrictToSet_apply_of_mem
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) {x : H} (hx : x ∈ C) :
    (restrictToSet f C x : EReal) = (f x : EReal) := by
  -- Evaluate the defining `if` on the in-set branch.
  unfold restrictToSet
  rw [if_pos hx]

/-- Helper for Proposition 10.17: the localized function is `⊤` off the localizing set. -/
private theorem restrictToSet_apply_of_not_mem
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) {x : H} (hx : x ∉ C) :
    (restrictToSet f C x : EReal) = ⊤ := by
  -- Evaluate the defining `if` on the out-of-set branch.
  unfold restrictToSet
  rw [if_neg hx]

/-- Helper for Proposition 10.17: the effective domain of the localized function is exactly the
localizing set. -/
private theorem effectiveDomain_restrictToSet_eq
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) (hC_dom : C ⊆ effectiveDomain f) :
    effectiveDomain (restrictToSet f C) = C := by
  ext x
  constructor
  · intro hx
    by_contra hxC
    -- Off `C`, the localized function is `⊤`, so the effective-domain test fails.
    have htop : ((restrictToSet f C x : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ :=
      restrictToSet_apply_of_not_mem f C hxC
    have hlt : (((restrictToSet f C x : Set.Ioi (⊥ : EReal)) : EReal) < ⊤) :=
      mem_effectiveDomain_iff.mp hx
    exact (not_lt_of_ge le_top) (htop ▸ hlt)
  · intro hxC
    -- On `C`, the localized function keeps the original finite value.
    rw [mem_effectiveDomain_iff]
    simpa [restrictToSet_apply_of_mem f C hxC] using
      (mem_effectiveDomain_iff.mp (hC_dom hxC))

/-- Helper for Proposition 10.17: a source-facing strictly convex-on function is convex on the
same set. -/
private theorem StrictlyConvexOn.convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hf : StrictlyConvexOn f C) :
    ConvexOn f C := by
  refine ⟨hf.nonempty, hf.subset_effectiveDomain, ?_⟩
  intro x hx y hy α hα0 hα1
  by_cases hxy : x = y
  · subst hxy
    -- Collapse the diagonal convex combination to a single point.
    have hsum : α + (1 - α) = (1 : ℝ) := by ring
    have hdiag : α • x + (1 - α) • x = x := by
      calc
        α • x + (1 - α) • x = (α + (1 - α)) • x := by rw [← add_smul]
        _ = (1 : ℝ) • x := by simpa [hsum]
        _ = x := by simp
    have hx_dom : x ∈ effectiveDomain f := hf.subset_effectiveDomain hx
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
    have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    rw [hdiag, ← EReal.coe_toReal hx_top hx_bot]
    have hcoeff :
        (((α * (f x : EReal).toReal + (1 - α) * (f x : EReal).toReal : ℝ)) : EReal) =
          ((((f x : EReal).toReal : ℝ)) : EReal) := by
      congr 1
      ring_nf
    simpa [EReal.coe_add, EReal.coe_mul] using hcoeff.ge
  · -- Away from the diagonal, strict Jensen implies the weak Jensen inequality.
    exact (hf.ineq hx hy hxy hα0 hα1).le

/-- Helper for Proposition 10.17: the real midpoint-gap observable attached to an
`]-∞,+∞]`-valued function. -/
private noncomputable def midpointGapReal
    (f : H → Set.Ioi (⊥ : EReal)) : H × H → ℝ :=
  fun p ↦
    (((f p.1 : EReal).toReal + (f p.2 : EReal).toReal) / 2) -
      (f ((1 / 2 : ℝ) • p.1 + (1 - (1 / 2 : ℝ)) • p.2) : EReal).toReal

/-- Helper for Proposition 10.17: the weighted endpoint sum in a midpoint Jensen gap is finite at
effective-domain points. -/
private theorem midpointWeightedSum_neTop
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    (((1 / 2 : ℝ) : EReal)) * (f x : EReal) + (1 - ((1 / 2 : ℝ) : EReal)) * (f y : EReal) ≠ ⊤ :=
  by
  -- Effective-domain values are finite, so both weighted endpoint terms stay away from `⊤`.
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hhalf_nonneg : (0 : EReal) ≤ (((1 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hhalf'_nonneg : (0 : EReal) ≤ (1 - ((1 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 ≤ (1 - (1 / 2 : ℝ)) by norm_num)
  have hhalf_mul_ne_top : (((1 / 2 : ℝ) : EReal)) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inl hhalf_nonneg,
      Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)), Or.inr hfx_top⟩
  have hhalf'_mul_ne_top : (1 - ((1 / 2 : ℝ) : EReal)) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl ?_, Or.inl hhalf'_nonneg, Or.inl ?_, Or.inr hfy_top⟩
    · exact EReal.coe_ne_bot (1 - (1 / 2 : ℝ))
    · exact EReal.coe_ne_top (1 - (1 / 2 : ℝ))
  exact EReal.add_ne_top hhalf_mul_ne_top hhalf'_mul_ne_top

/-- Helper for Proposition 10.17: on effective-domain midpoint triples, the real midpoint gap
coerces back to the source-facing midpoint Jensen gap. -/
private theorem midpointGapReal_eq_coe
    {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    (hm : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ effectiveDomain f) :
    (((midpointGapReal f (x, y) : ℝ)) : EReal) = jensenGap f (1 / 2 : ℝ) x y := by
  -- Rewrite every finite value through `EReal.toReal`, then normalize the midpoint arithmetic.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hm_top : (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hm)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hm_bot : (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (f _).2
  rw [midpointGapReal, jensenGap, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_toReal hm_top hm_bot]
  change
    (((((f x : EReal).toReal + (f y : EReal).toReal) / 2 -
        (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal).toReal : ℝ)) : EReal) =
      ((((1 / 2 : ℝ) * (f x : EReal).toReal +
          (1 - (1 / 2 : ℝ)) * (f y : EReal).toReal -
          (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal).toReal : ℝ)) : EReal)
  congr 1
  ring

/-- Helper for Proposition 10.17: the fixed-distance shell inside `C ×ˢ C`. -/
private def distanceShell (C : Set H) (t : NNReal) : Set (H × H) :=
  {p | p.1 ∈ C ∧ p.2 ∈ C ∧ ‖p.1 - p.2‖₊ = t}

/-- Helper for Proposition 10.17: the real midpoint-gap observable is continuous on `C ×ˢ C`. -/
private theorem midpointGapRealContinuousOn
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) (hC_convex : Convex ℝ C)
    (hcont : ContinuousOn (fun x : H ↦ (f x : EReal).toReal) C) :
    ContinuousOn (midpointGapReal f) (C ×ˢ C) := by
  -- Compose the coordinate restrictions with the product projections.
  let fstTerm : H × H → ℝ := fun p ↦ (f p.1 : EReal).toReal
  let sndTerm : H × H → ℝ := fun p ↦ (f p.2 : EReal).toReal
  let midpointMap : H × H → H := fun p ↦ ((2 : ℝ)⁻¹) • p.1 + (1 - ((2 : ℝ)⁻¹)) • p.2
  let midpointTerm : H × H → ℝ := fun p ↦ (f (midpointMap p) : EReal).toReal
  have hfst : ContinuousOn fstTerm (C ×ˢ C) := by
    refine ContinuousOn.comp hcont continuous_fst.continuousOn ?_
    intro p hp
    exact hp.1
  have hsnd : ContinuousOn sndTerm (C ×ˢ C) := by
    refine ContinuousOn.comp hcont continuous_snd.continuousOn ?_
    intro p hp
    exact hp.2
  have hmid_map : Set.MapsTo midpointMap (C ×ˢ C) C := by
    intro p hp
    exact hC_convex hp.1 hp.2 (by norm_num) (by norm_num) (by norm_num)
  have hmidpointMap : Continuous midpointMap := by
    simpa [midpointMap] using
      (continuous_fst.const_smul (1 / 2 : ℝ)).add
        (continuous_snd.const_smul (1 - (1 / 2 : ℝ)))
  have hmid : ContinuousOn midpointTerm (C ×ˢ C) := by
    refine ContinuousOn.comp hcont hmidpointMap.continuousOn hmid_map
  -- Reassemble the midpoint gap from the three continuous-on pieces.
  have havg : ContinuousOn (fun p ↦ (fstTerm p + sndTerm p) / 2) (C ×ˢ C) :=
    (hfst.add hsnd).div_const (2 : ℝ)
  have hgapCont :
      ContinuousOn
        (fun p ↦ ((f p.1 : EReal).toReal + (f p.2 : EReal).toReal) / 2 -
          (f (midpointMap p) : EReal).toReal)
        (C ×ˢ C) := by
    simpa [fstTerm, sndTerm, midpointTerm] using havg.sub hmid
  refine hgapCont.congr ?_
  intro p hp
  simp [midpointGapReal, midpointMap, one_div]

/-- Helper for Proposition 10.17: the fixed-distance shell in `C ×ˢ C` is compact. -/
private theorem distanceShellIsCompact
    (C : Set H) (hC_compact : IsCompact C) (t : NNReal) :
    IsCompact (distanceShell C t) := by
  -- Intersect the compact product `C ×ˢ C` with the closed distance fiber.
  let distMap : H × H → NNReal := fun p ↦ ‖p.1 - p.2‖₊
  have hdist_cont : Continuous distMap := by
    continuity
  have hfiber_closed : IsClosed {p : H × H | distMap p = t} :=
    isClosed_eq hdist_cont continuous_const
  have hprod_compact : IsCompact (C ×ˢ C) :=
    hC_compact.prod hC_compact
  have hshell_eq :
      distanceShell C t = (C ×ˢ C) ∩ {p : H × H | distMap p = t} := by
    ext p
    simp [distanceShell, distMap, and_assoc]
  rw [hshell_eq]
  exact hprod_compact.inter_right hfiber_closed

/-- Helper for Proposition 10.17: if the localized midpoint modulus vanishes, then the
corresponding fixed-distance shell is nonempty. -/
private theorem midpointModulus_eq_zero_implies_shellNonempty
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) (hC_dom : C ⊆ effectiveDomain f)
    {t : NNReal} (hzero : midpointModulusOfConvexity (restrictToSet f C) t = 0) :
    (distanceShell C t).Nonempty := by
  -- If the shell were empty, the defining witness set of the midpoint modulus would also be empty.
  by_contra hshell
  have hshell_empty : distanceShell C t = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hshell
  let g := restrictToSet f C
  have hdomEq : effectiveDomain g = C :=
    effectiveDomain_restrictToSet_eq f C hC_dom
  let witnessSet : Set EReal :=
    {δ : EReal |
      ∃ x ∈ effectiveDomain g, ∃ y ∈ effectiveDomain g,
        ‖x - y‖₊ = t ∧ δ = jensenGap g (1 / 2 : ℝ) x y}
  have hwitness_empty : witnessSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro δ hδ
    rcases hδ with ⟨x, hx, y, hy, hxy, _⟩
    have hxC : x ∈ C := by simpa [g, hdomEq] using hx
    have hyC : y ∈ C := by simpa [g, hdomEq] using hy
    have hp : (x, y) ∈ distanceShell C t := ⟨hxC, hyC, hxy⟩
    simpa [hshell_empty] using hp
  have htop : midpointModulusOfConvexity g t = ⊤ := by
    -- The infimum over an empty witness set is `⊤`.
    rw [midpointModulusOfConvexity]
    change sInf witnessSet = ⊤
    rw [hwitness_empty, sInf_empty]
  exact EReal.top_ne_zero (htop.symm.trans hzero)

/-- Helper for Proposition 10.17: midpoint Jensen gaps are nonnegative on a convex-on set. -/
private theorem midpointJensenGap_nonneg_of_convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hconv : ConvexOn f C)
    {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    0 ≤ jensenGap f (1 / 2 : ℝ) x y := by
  -- Rewrite the convex midpoint inequality into the Jensen-gap form.
  have hx_dom : x ∈ effectiveDomain f := hconv.subset_effectiveDomain hx
  have hy_dom : y ∈ effectiveDomain f := hconv.subset_effectiveDomain hy
  have hmid_bot : (f ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (f _).2
  have hsum_ne_top :
      (((1 / 2 : ℝ) : EReal)) * (f x : EReal) +
          (1 - ((1 / 2 : ℝ) : EReal)) * (f y : EReal) ≠ ⊤ :=
    midpointWeightedSum_neTop hx_dom hy_dom
  rw [jensenGap, EReal.sub_nonneg (Or.inl hsum_ne_top) (Or.inr hmid_bot)]
  simpa using hconv.ineq hx hy (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)

/-- Helper for Proposition 10.17: the real midpoint gap is nonnegative on `C`. -/
private theorem midpointGapReal_nonneg
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hconv : ConvexOn f C)
    (hC_convex : Convex ℝ C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    0 ≤ midpointGapReal f (x, y) := by
  -- Cast the source-facing midpoint Jensen gap down to `ℝ`.
  have hmidC : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ C :=
    hC_convex hx hy (by norm_num) (by norm_num) (by norm_num)
  have hgap_nonneg : 0 ≤ jensenGap f (1 / 2 : ℝ) x y :=
    midpointJensenGap_nonneg_of_convexOn hconv hx hy
  have hgap_eq :
      (((midpointGapReal f (x, y) : ℝ)) : EReal) = jensenGap f (1 / 2 : ℝ) x y :=
    midpointGapReal_eq_coe (hconv.subset_effectiveDomain hx) (hconv.subset_effectiveDomain hy)
      (hconv.subset_effectiveDomain hmidC)
  have hgap_real_nonneg : (0 : EReal) ≤ ((midpointGapReal f (x, y) : ℝ) : EReal) := by
    simpa [hgap_eq] using hgap_nonneg
  exact_mod_cast hgap_real_nonneg

/-- Helper for Proposition 10.17: strict convexity makes the real midpoint gap positive for
distinct points of `C`. -/
private theorem midpointGapReal_pos_of_ne
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hstrict : StrictlyConvexOn f C)
    (hC_convex : Convex ℝ C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    0 < midpointGapReal f (x, y) := by
  -- Convert the strict midpoint Jensen inequality to the real midpoint-gap observable.
  have hmidC : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ C :=
    hC_convex hx hy (by norm_num) (by norm_num) (by norm_num)
  have hgap_pos : 0 < jensenGap f (1 / 2 : ℝ) x y := by
    simpa [jensenGap] using
      (EReal.sub_pos.mpr (hstrict.ineq hx hy hxy (by norm_num) (by norm_num)))
  have hgap_eq :
      (((midpointGapReal f (x, y) : ℝ)) : EReal) = jensenGap f (1 / 2 : ℝ) x y :=
    midpointGapReal_eq_coe (hstrict.subset_effectiveDomain hx) (hstrict.subset_effectiveDomain hy)
      (hstrict.subset_effectiveDomain hmidC)
  have hgap_real_pos : (0 : EReal) < ((midpointGapReal f (x, y) : ℝ) : EReal) := by
    simpa [hgap_eq] using hgap_pos
  simpa using hgap_real_pos

/-- Helper for Proposition 10.17: for the localized function `restrictToSet f C`, vanishing of
the midpoint modulus forces the radius to be `0` on a compact convex set. -/
private theorem midpointModulus_eq_zero_implies_radius_eq_zero_of_isCompact
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H)
    (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (hstrict : StrictlyConvexOn f C)
    (hcont : ContinuousOn (fun x : H ↦ (f x : EReal).toReal) C)
    {t : NNReal} (hzero : midpointModulusOfConvexity (restrictToSet f C) t = 0) :
    t = 0 := by
  let g := restrictToSet f C
  let shell := distanceShell C t
  have hdomEq : effectiveDomain g = C :=
    effectiveDomain_restrictToSet_eq f C hstrict.subset_effectiveDomain
  have hcont_g : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) C := by
    -- On `C`, the localized function agrees with `f`.
    refine hcont.congr ?_
    intro x hx
    simp [g, restrictToSet_apply_of_mem, hx]
  have hshell_compact : IsCompact shell :=
    distanceShellIsCompact C hC_compact t
  have hshell_nonempty : shell.Nonempty :=
    midpointModulus_eq_zero_implies_shellNonempty f C hstrict.subset_effectiveDomain hzero
  have hgap_cont_shell : ContinuousOn (midpointGapReal g) shell := by
    -- Restrict the product continuity lemma to the fixed-distance shell.
    refine (midpointGapRealContinuousOn g C hC_convex hcont_g).mono ?_
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  obtain ⟨p, hpShell, hpMin⟩ :=
    hshell_compact.exists_isMinOn hshell_nonempty hgap_cont_shell
  rcases hpShell with ⟨hp1, hp2, hpDist⟩
  have hp1_dom : p.1 ∈ effectiveDomain g := by
    simpa [g, hdomEq] using hp1
  have hp2_dom : p.2 ∈ effectiveDomain g := by
    simpa [g, hdomEq] using hp2
  have hmidC : (1 / 2 : ℝ) • p.1 + (1 - (1 / 2 : ℝ)) • p.2 ∈ C :=
    hC_convex hp1 hp2 (by norm_num) (by norm_num) (by norm_num)
  have hmid_dom : (1 / 2 : ℝ) • p.1 + (1 - (1 / 2 : ℝ)) • p.2 ∈ effectiveDomain g := by
    simpa [g, hdomEq] using hmidC
  have hmin_eq :
      (((midpointGapReal g p : ℝ)) : EReal) = midpointModulusOfConvexity g t := by
    apply le_antisymm
    · -- The minimizer value is bounded below by every witness in the defining infimum.
      rw [midpointModulusOfConvexity]
      refine le_sInf ?_
      intro δ hδ
      rcases hδ with ⟨x, hx, y, hy, hxy, rfl⟩
      have hxC : x ∈ C := by simpa [g, hdomEq] using hx
      have hyC : y ∈ C := by simpa [g, hdomEq] using hy
      have hmidxyC : (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ C :=
        hC_convex hxC hyC (by norm_num) (by norm_num) (by norm_num)
      have hmidxy_dom :
          (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ effectiveDomain g := by
        simpa [g, hdomEq] using hmidxyC
      have hp_le : midpointGapReal g p ≤ midpointGapReal g (x, y) :=
        hpMin ⟨hxC, hyC, hxy⟩
      have hpair_eq :
          (((midpointGapReal g (x, y) : ℝ)) : EReal) = jensenGap g (1 / 2 : ℝ) x y :=
        midpointGapReal_eq_coe hx hy hmidxy_dom
      calc
        (((midpointGapReal g p : ℝ)) : EReal) ≤ (((midpointGapReal g (x, y) : ℝ)) : EReal) := by
          exact_mod_cast hp_le
        _ = jensenGap g (1 / 2 : ℝ) x y := hpair_eq
    · -- The midpoint modulus is bounded above by the minimizing witness.
      have hpair_eq :
          (((midpointGapReal g p : ℝ)) : EReal) = jensenGap g (1 / 2 : ℝ) p.1 p.2 :=
        midpointGapReal_eq_coe hp1_dom hp2_dom hmid_dom
      calc
        midpointModulusOfConvexity g t ≤ jensenGap g (1 / 2 : ℝ) p.1 p.2 :=
          midpointModulusOfConvexity_le_gap g hp1_dom hp2_dom hpDist
        _ = (((midpointGapReal g p : ℝ)) : EReal) := hpair_eq.symm
  have hgap_zeroE : (((midpointGapReal g p : ℝ)) : EReal) = 0 := by
    calc
      (((midpointGapReal g p : ℝ)) : EReal) = midpointModulusOfConvexity g t := hmin_eq
      _ = 0 := hzero
  have hgap_zero : midpointGapReal g p = 0 := by
    exact_mod_cast hgap_zeroE
  have hgap_eq_original : midpointGapReal g p = midpointGapReal f p := by
    -- On the shell, all localized values reduce back to the original function.
    rw [midpointGapReal, midpointGapReal]
    rw [restrictToSet_apply_of_mem _ _ hp1, restrictToSet_apply_of_mem _ _ hp2,
      restrictToSet_apply_of_mem _ _ hmidC]
  have hpDiag : p.1 = p.2 := by
    -- Strict convexity forbids a zero midpoint gap away from the diagonal.
    by_contra hpNe
    have hpos : 0 < midpointGapReal f p :=
      midpointGapReal_pos_of_ne hstrict hC_convex hp1 hp2 hpNe
    have hpos_g : 0 < midpointGapReal g p := by
      simpa [hgap_eq_original] using hpos
    simpa [hgap_zero] using hpos_g
  calc
    t = ‖p.1 - p.2‖₊ := hpDist.symm
    _ = 0 := by simpa [hpDiag]

/-- Helper for Proposition 10.17: strict convexity of a real-valued function upgrades to the
source-facing `]-∞,+∞]` strict convexity owner after applying `Function.toEReal`. -/
private theorem strictConvexOn_toEReal
    {f : H → ℝ} {C : Set H} (hC_nonempty : C.Nonempty) (hstrict : StrictConvexOn ℝ C f) :
    ERealFunction.StrictlyConvexOn f.toEReal C := by
  refine ⟨hC_nonempty, ?_, ?_⟩
  · intro x hx
    simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy hxy α hα0 hα1
    have hineq :
        f (α • x + (1 - α) • y) < α * f x + (1 - α) * f y := by
      simpa [smul_eq_mul] using hstrict.2 hx hy hxy hα0 (by linarith) (by ring)
    have hineqE :
        (((f (α • x + (1 - α) • y) : ℝ) : EReal)) <
          (((α * f x + (1 - α) * f y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm] using hineqE

-- Semantic recall: `lean_leansearch` surfaced mathlib's real-valued owner
-- `Mathlib.Analysis.Convex.Strong.UniformConvexOn`; the labeled source item is more naturally
-- expressed in the repo's `ERealFunction.UniformlyConvexOn` owner API, with a thin real-valued
-- companion bridge kept for downstream reuse.
/-- Proposition 10.17: on a compact convex set `C`, strict convexity of
`f : H → ]-∞,+∞]` on `C` together with continuity of `x ↦ (f x : EReal).toReal` on `C`
implies uniform convexity of `f` on `C`. The textbook's ambient properness and global convexity
assumptions are redundant for this local conclusion, so the source-facing owner here keeps only
the hypotheses used by the conclusion itself. -/
theorem exists_uniformlyConvexOn_of_isCompact_of_strictlyConvexOn_of_continuousOn
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H)
    (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (hstrict : StrictlyConvexOn f C)
    (hcont : ContinuousOn (fun x : H ↦ (f x : EReal).toReal) C) :
    ∃ φ : NNReal → EReal, UniformlyConvexOn f C φ := by
  let g := restrictToSet f C
  have hdomEq : effectiveDomain g = C :=
    effectiveDomain_restrictToSet_eq f C hstrict.subset_effectiveDomain
  have hconv_g : ConvexOn g (effectiveDomain g) := by
    -- The localized function is convex on its effective domain because it agrees with `f` on `C`.
    refine ⟨by simpa [g, hdomEq] using hstrict.nonempty, subset_rfl, ?_⟩
    intro x hx y hy α hα0 hα1
    have hxC : x ∈ C := by simpa [g, hdomEq] using hx
    have hyC : y ∈ C := by simpa [g, hdomEq] using hy
    have hmidC : α • x + (1 - α) • y ∈ C :=
      hC_convex hxC hyC hα0.le (by linarith) (by ring)
    have hineq := (hstrict.convexOn).ineq hxC hyC hα0 hα1
    simpa [g, restrictToSet_apply_of_mem, hxC, hyC, hmidC] using hineq
  have hzero_iff : ∀ t : NNReal, midpointModulusOfConvexity g t = 0 ↔ t = 0 := by
    intro t
    constructor
    · intro hzero
      -- The compact-shell lemma gives the hard direction.
      exact
        midpointModulus_eq_zero_implies_radius_eq_zero_of_isCompact
          f C hC_compact hC_convex hstrict hcont hzero
    · intro ht
      subst ht
      -- A diagonal witness forces the radius-zero midpoint modulus to vanish.
      have hnonneg : 0 ≤ midpointModulusOfConvexity g 0 :=
        midpointModulusOfConvexity_nonneg (f := g) hconv_g 0
      rcases hstrict.nonempty with ⟨x, hx⟩
      have hxg : x ∈ effectiveDomain g := by
        simpa [g, hdomEq] using hx
      have hdiag_gap : midpointGapReal g (x, x) = 0 := by
        -- The midpoint of a diagonal pair is the point itself.
        simp [midpointGapReal]
      have hgap_eq :
          jensenGap g (1 / 2 : ℝ) x x = 0 := by
        simpa [hdiag_gap] using
          (midpointGapReal_eq_coe (f := g) hxg hxg (by simpa using hxg)).symm
      have hle_zero : midpointModulusOfConvexity g 0 ≤ 0 := by
        calc
          midpointModulusOfConvexity g 0 ≤ jensenGap g (1 / 2 : ℝ) x x :=
            midpointModulusOfConvexity_le_gap g hxg hxg (by simp)
          _ = 0 := hgap_eq
      exact le_antisymm hle_zero hnonneg
  obtain ⟨φ, hUniform_g⟩ :=
    (uniformlyConvex_exists_iff_midpointModulusOfConvexity_eq_zero_iff (f := g) hconv_g).2
      hzero_iff
  have hUniform_g_on : UniformlyConvexOn g C φ := by
    simpa [UniformlyConvex, g, hdomEq] using hUniform_g
  rcases hUniform_g_on with ⟨hC_nonempty, _hsubset_g, hφ_mono, hφ_zero, hφ_gap⟩
  refine ⟨φ, ?_⟩
  refine ⟨hC_nonempty, hstrict.subset_effectiveDomain, hφ_mono, hφ_zero, ?_⟩
  intro x hx y hy α hα0 hα1
  -- Transport the localized Jensen inequality back to `f` on `C`.
  have hmidC : α • x + (1 - α) • y ∈ C :=
    hC_convex hx hy hα0.le (by linarith) (by ring)
  simpa [g, jensenGap, restrictToSet_apply_of_mem, hx, hy, hmidC] using
    hφ_gap hx hy hα0 hα1

/-- Helper for Proposition 10.17: in the real-valued setting, the source-facing modulus is finite
at every realized radius. -/
private theorem realizedRadiusModulus_neTop
    {f : H → ℝ} {C : Set H} {φ : NNReal → EReal}
    (hφ : UniformlyConvexOn f.toEReal C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    φ ‖x - y‖₊ ≠ ⊤ := by
  -- Evaluate the source-facing gap inequality at the midpoint coefficient `1 / 2`.
  have hgap :=
    hφ.gap_le hx hy (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hcoeff_pos : (0 : EReal) < (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) := by
    exact_mod_cast (show 0 < (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) by norm_num)
  have hgap_finite :
      jensenGap f.toEReal (1 / 2 : ℝ) x y ≠ ⊤ := by
    -- For real-valued data, the midpoint Jensen gap is the coercion of a real number.
    have hx_dom : x ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hy_dom : y ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hmid_dom :
        (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y ∈ effectiveDomain f.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hcoe :
        (((midpointGapReal f.toEReal (x, y) : ℝ)) : EReal) =
          jensenGap f.toEReal (1 / 2 : ℝ) x y :=
      midpointGapReal_eq_coe hx_dom hy_dom hmid_dom
    exact fun htop ↦ EReal.coe_ne_top _ (hcoe.trans htop)
  intro htop
  have hleft_top :
      (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊ = ⊤ := by
    rw [htop, EReal.mul_top_of_pos hcoeff_pos]
  have htop_le : (⊤ : EReal) ≤ jensenGap f.toEReal (1 / 2 : ℝ) x y := by
    calc
      (⊤ : EReal) =
          (((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) : ℝ) : EReal) * φ ‖x - y‖₊ := hleft_top.symm
      _ ≤ jensenGap f.toEReal (1 / 2 : ℝ) x y := hgap
  exact hgap_finite (top_le_iff.mp htop_le)

/-- Canonical real-valued bridge for Proposition 10.17: on a compact set, strict convexity and
continuity yield a mathlib `UniformConvexOn` modulus positive away from `0`. -/
theorem exists_uniformConvexOn_of_isCompact_of_strictConvexOn_of_continuousOn
    (f : H → ℝ) (C : Set H)
    (hC_compact : IsCompact C)
    (hstrict : StrictConvexOn ℝ C f) (hcont : ContinuousOn f C) :
    ∃ ψ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ f := by
  by_cases hC_nonempty : C.Nonempty
  · -- Route correction: the real-valued proof is easiest through the source-facing `EReal`
    -- theorem, followed by a local `toReal` conversion only at realized radii.
    obtain ⟨φ, hφ⟩ :=
      exists_uniformlyConvexOn_of_isCompact_of_strictlyConvexOn_of_continuousOn
        f.toEReal C hC_compact hstrict.1
        (strictConvexOn_toEReal hC_nonempty hstrict)
        (by simpa [Function.toEReal_apply] using hcont)
    let ψ : ℝ → ℝ := fun r ↦
      if hr : 0 ≤ r then
        if htop : φ ⟨r, hr⟩ = ⊤ then 1 else (φ ⟨r, hr⟩).toReal
      else
        1
    refine ⟨ψ, ?_, ?_⟩
    · intro r hr_ne
      by_cases hr : 0 ≤ r
      · by_cases htop : φ ⟨r, hr⟩ = ⊤
        · -- The fallback branch is the positive constant `1`.
          simp [ψ, hr, htop]
        · -- Away from `⊤`, positivity follows from the source-facing zero-set criterion.
          have hφ_nonneg : 0 ≤ φ ⟨r, hr⟩ := by
            rw [← (hφ.modulus_eq_zero_iff 0).2 rfl]
            exact hφ.monotone bot_le
          have hφ_ne_zero : φ ⟨r, hr⟩ ≠ 0 := by
            intro hzero
            have hradius_zero : (⟨r, hr⟩ : NNReal) = 0 :=
              (hφ.modulus_eq_zero_iff ⟨r, hr⟩).1 hzero
            have : r = 0 := by
              exact congrArg (fun s : NNReal => (s : ℝ)) hradius_zero
            exact hr_ne this
          have hφ_pos : (0 : EReal) < φ ⟨r, hr⟩ :=
            lt_of_le_of_ne hφ_nonneg (Ne.symm hφ_ne_zero)
          have htoReal_pos : 0 < (φ ⟨r, hr⟩).toReal :=
            EReal.toReal_pos hφ_pos htop
          simpa [ψ, hr, htop] using htoReal_pos
      · -- Negative radii also fall into the positive constant branch.
        simp [ψ, hr]
    · refine ⟨hstrict.1, ?_⟩
      intro x hx y hy a b ha hb hab
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [ha0, hb1]
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simp [hb0, ha1]
      have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have ha_lt_one : a < 1 := by
        nlinarith
      have hb_eq : b = 1 - a := by
        linarith
      have hradius_ne_top : φ ‖x - y‖₊ ≠ ⊤ :=
        realizedRadiusModulus_neTop hφ hx hy
      have hradius_nonneg : 0 ≤ φ ‖x - y‖₊ := by
        rw [← (hφ.modulus_eq_zero_iff 0).2 rfl]
        exact hφ.monotone bot_le
      have hradius_ne_bot : φ ‖x - y‖₊ ≠ ⊥ := by
        exact ne_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) hradius_nonneg)
      have hnorm_nn : (⟨‖x - y‖, norm_nonneg (x - y)⟩ : NNReal) = ‖x - y‖₊ := by
        ext
        simp
      have hψ_radius :
          (((ψ ‖x - y‖ : ℝ) : EReal)) = φ ‖x - y‖₊ := by
        rw [show ψ ‖x - y‖ = (φ ‖x - y‖₊).toReal by
          simp [ψ, norm_nonneg, hradius_ne_top, hnorm_nn]]
        rw [EReal.coe_toReal hradius_ne_top hradius_ne_bot]
      have hgapE :
          (((a * (1 - a) * ψ ‖x - y‖ : ℝ)) : EReal) ≤
            (((a * f x + (1 - a) * f y - f (a • x + (1 - a) • y) : ℝ)) : EReal) := by
        simpa [hψ_radius, Function.toEReal_apply, jensenGap, EReal.coe_add, EReal.coe_mul,
          mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
          hφ.gap_le hx hy ha_pos ha_lt_one
      have hgap :
          a * (1 - a) * ψ ‖x - y‖ ≤
            a * f x + (1 - a) * f y - f (a • x + (1 - a) • y) := by
        exact_mod_cast hgapE
      have hineq :
          f (a • x + (1 - a) • y) + a * (1 - a) * ψ ‖x - y‖ ≤
            a * f x + (1 - a) * f y := by
        linarith
      rw [le_sub_iff_add_le]
      simpa [hb_eq, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using
        hineq
  · -- On the empty set, any positive-away-from-zero modulus works because the inequality is
    -- vacuous.
    have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    refine ⟨fun _ ↦ 1, ?_, ?_⟩
    · intro r _hr
      norm_num
    · subst hC_empty
      refine ⟨convex_empty, ?_⟩
      intro x hx
      simpa using hx

end ERealFunction
