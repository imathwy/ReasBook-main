import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

local notation "SmoothRealFunctionRing" => C^∞⟮𝓘(ℝ), ℝ; ℝ⟯

/-- The ideal of smooth real-valued functions vanishing at the origin. -/
def smoothRealFunctionsVanishingAtZeroIdeal : Ideal SmoothRealFunctionRing :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℝ))

/-- The ideal of smooth real-valued functions that vanish on a neighborhood of the origin. -/
def smoothRealFunctionsVanishingNearZeroIdeal : Ideal SmoothRealFunctionRing where
  carrier := { f | ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0 }
  zero_mem' := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    rfl
  add_mem' := by
    rintro f g ⟨εf, hεf, hf⟩ ⟨εg, hεg, hg⟩
    refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    intro x hx
    have hxf : |x| < εf := lt_of_lt_of_le hx (min_le_left _ _)
    have hxg : |x| < εg := lt_of_lt_of_le hx (min_le_right _ _)
    simp [hf x hxf, hg x hxg]
  smul_mem' := by
    rintro f g ⟨ε, hε, hg⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    simp [hg x hx]

-- Proof sketch: a smooth function that vanishes on some neighborhood of `0` in particular vanishes
-- at `0`, so it lies in the kernel of evaluation at the origin.
/-- Any smooth function vanishing near the origin also vanishes at the origin. -/
theorem smoothRealFunctionsVanishingNearZeroIdeal_le_vanishingAtZeroIdeal :
    smoothRealFunctionsVanishingNearZeroIdeal ≤ smoothRealFunctionsVanishingAtZeroIdeal := by
  -- Evaluating at `0` turns a neighborhood-vanishing hypothesis into an actual zero.
  intro f hf
  rcases hf with ⟨ε, hε, hvanish⟩
  rw [smoothRealFunctionsVanishingAtZeroIdeal, RingHom.mem_ker]
  exact hvanish 0 (by simpa using hε)

/-- The ideal of functions vanishing at the origin is maximal. -/
theorem smoothRealFunctionsVanishingAtZeroIdeal_isMaximal :
    smoothRealFunctionsVanishingAtZeroIdeal.IsMaximal := by
  -- Evaluation at `0` is onto `ℝ`, so its kernel is maximal.
  rw [smoothRealFunctionsVanishingAtZeroIdeal]
  refine RingHom.ker_isMaximal_of_surjective (ContMDiffMap.evalRingHom (0 : ℝ)) ?_
  intro r
  refine ⟨ContMDiffMap.const r, ?_⟩
  simp [ContMDiffMap.evalRingHom, ContMDiffMap.const]

attribute [instance] smoothRealFunctionsVanishingAtZeroIdeal_isMaximal

instance smoothRealFunctionsVanishingAtZeroIdeal_isPrime :
    smoothRealFunctionsVanishingAtZeroIdeal.IsPrime :=
  smoothRealFunctionsVanishingAtZeroIdeal_isMaximal.isPrime

/-- The source-facing module `M = R_𝔪` from Remark 10.78.4, where `𝔪` is the maximal ideal of
smooth functions vanishing at the origin. -/
abbrev smoothRealFunctionLocalizationAtZero :=
  Localization.AtPrime smoothRealFunctionsVanishingAtZeroIdeal

/-- The quotient model `R / I` from Remark 10.78.4, where `I` consists of smooth functions
vanishing on a neighborhood of the origin. -/
abbrev smoothRealFunctionQuotientAtZero :=
  SmoothRealFunctionRing ⧸ smoothRealFunctionsVanishingNearZeroIdeal

/-- Helper for Remark 10.78.4: bundle the standard smooth cutoff theorem on `ℝ` into the smooth
function ring. -/
lemma smooth_cutoff_support_eq_eq_one {s t : Set ℝ} (hs : IsOpen s) (ht : IsClosed t)
    (h : t ⊆ s) :
    ∃ φ : SmoothRealFunctionRing,
      Function.support (φ : ℝ → ℝ) = s ∧
      Set.range (φ : ℝ → ℝ) ⊆ Set.Icc 0 1 ∧
      ∀ x, x ∈ t ↔ φ x = 1 := by
  -- Repackage the unbundled cutoff theorem as an element of `SmoothRealFunctionRing`.
  rcases exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ)) hs ht h with
    ⟨φ, hφdiff, hφrange, hφsupp, hφone⟩
  refine ⟨⟨φ, hφdiff⟩, ?_, ?_, ?_⟩
  · simpa using hφsupp
  · simpa using hφrange
  · simpa using hφone

/-- Helper for Remark 10.78.4: a smooth function nonzero at the origin stays nonzero on a small
interval around `0`. -/
lemma exists_abs_lt_nonzero_of_eval_ne_zero (f : SmoothRealFunctionRing) (hf0 : f 0 ≠ 0) :
    ∃ ε > 0, ∀ x : ℝ, |x| < ε → f x ≠ 0 := by
  -- Continuity turns the open condition `f x ≠ 0` into a neighborhood of `0`.
  have hpre : {x : ℝ | f x ≠ 0} ∈ nhds (0 : ℝ) := by
    exact f.contMDiff.continuous.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hf0)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hεsub (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hx)

/-- Helper for Remark 10.78.4: if the support of a smooth numerator has closure inside the
nonvanishing locus of the denominator, then the pointwise quotient extends to a smooth function on
all of `ℝ`. -/
lemma contMDiff_div_of_support_closure_subset (c f : SmoothRealFunctionRing) {s : Set ℝ}
    (hsupp : Function.support (c : ℝ → ℝ) = s) (hcl : closure s ⊆ {x : ℝ | f x ≠ 0}) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun x : ℝ ↦ c x / f x) := by
  -- On the closure of the support, the denominator is nonzero; away from that closure, the
  -- numerator vanishes on a neighborhood, so the quotient is locally constant zero.
  intro x
  by_cases hx : x ∈ closure s
  · exact ContMDiffAt.div₀ (c.contMDiff x) (f.contMDiff x) (hcl hx)
  · refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun _ : ℝ ↦ (0 : ℝ))
      (contMDiffAt_const : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun _ : ℝ ↦ (0 : ℝ)) x) ?_
    filter_upwards [IsOpen.mem_nhds isClosed_closure.isOpen_compl hx] with y hy
    have hy_support : y ∉ Function.support (c : ℝ → ℝ) := by
      rw [hsupp]
      intro hy'
      exact hy (subset_closure hy')
    have hcy : c y = 0 := by
      rwa [Function.notMem_support] at hy_support
    simpa [hcy]

/-- Helper for Remark 10.78.4: any smooth function vanishing near `0` is killed by some element of
the complement of the maximal ideal of functions vanishing at `0`. -/
lemma exists_primeCompl_multiplier_eq_zero_of_mem_vanishingNearZeroIdeal
    (h : SmoothRealFunctionRing)
    (hh : h ∈ smoothRealFunctionsVanishingNearZeroIdeal) :
    ∃ c : smoothRealFunctionsVanishingAtZeroIdeal.primeCompl, (c : SmoothRealFunctionRing) * h = 0 := by
  rcases hh with ⟨ε, hε, hvanish⟩
  let s : Set ℝ := Set.Ioo (-(ε / 2)) (ε / 2)
  let t : Set ℝ := Set.Icc (-(ε / 4)) (ε / 4)
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  refine ⟨⟨c, ?_⟩, ?_⟩
  · -- The cutoff is equal to `1` near the origin, so it does not vanish at `0`.
    intro hc
    have hc0' : c 0 = 0 := by
      simpa [smoothRealFunctionsVanishingAtZeroIdeal] using hc
    have hc0 : c 0 = 1 := (hcone 0).1 (by
      constructor <;> linarith [hε])
    have : (1 : ℝ) = 0 := by rw [← hc0, hc0']
    exact one_ne_zero this
  · -- Inside the support of the cutoff, `h` vanishes; outside the support, the cutoff vanishes.
    ext x
    by_cases hx : x ∈ Function.support (c : ℝ → ℝ)
    · have hx' : x ∈ Set.Ioo (-(ε / 2)) (ε / 2) := by simpa [hcsupp] using hx
      have hxε : |x| < ε := by
        have hxabs : |x| < ε / 2 := abs_lt.mpr ⟨by linarith [hx'.1], hx'.2⟩
        linarith
      simp [hvanish x hxε]
    · have hcx : c x = 0 := by
        rwa [Function.notMem_support] at hx
      simp [hcx]

/-- Helper for Remark 10.78.4: a smooth function nonzero at `0` becomes a unit in the quotient by
functions vanishing near `0`. -/
lemma quotient_mk_isUnit_of_eval_ne_zero (f : SmoothRealFunctionRing) (hf0 : f 0 ≠ 0) :
    IsUnit (Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f) := by
  rcases exists_abs_lt_nonzero_of_eval_ne_zero f hf0 with ⟨ε, hε, hnonzero⟩
  let s : Set ℝ := Set.Ioo (-(ε / 2)) (ε / 2)
  let t : Set ℝ := Set.Icc (-(ε / 4)) (ε / 4)
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  have hcl : closure s ⊆ {x : ℝ | f x ≠ 0} := by
    -- The closure of the cutoff support still lies in the small interval where `f` is nonzero.
    intro x hx
    have hclosure : closure s = Set.Icc (-(ε / 2)) (ε / 2) := by
      have hab : -(ε / 2) ≠ ε / 2 := by linarith
      simpa [s] using (closure_Ioo hab)
    rw [hclosure] at hx
    have hxabs : |x| ≤ ε / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    exact hnonzero x (lt_of_le_of_lt hxabs (by linarith))
  let g : SmoothRealFunctionRing :=
    ⟨fun x : ℝ ↦ c x / f x, contMDiff_div_of_support_closure_subset c f hcsupp hcl⟩
  have hmul : f * g = c := by
    -- Pointwise, the quotient is exact where `f` is nonzero, and the cutoff vanishes elsewhere.
    ext x
    by_cases hfx : f x = 0
    · have hx_support : x ∉ Function.support (c : ℝ → ℝ) := by
        rw [hcsupp]
        intro hx'
        exact (hcl (subset_closure hx')) hfx
      have hcx : c x = 0 := by
        rwa [Function.notMem_support] at hx_support
      simp [g, hfx, hcx]
    · change f x * (c x / f x) = c x
      field_simp [hfx]
  have hc_one : Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal c = 1 := by
    -- The cutoff equals `1` on a neighborhood of `0`, so it is `1` in the quotient.
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal (c - 1) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨ε / 4, by linarith, ?_⟩
    intro x hx
    have hxt : x ∈ t := by
      change x ∈ Set.Icc (-(ε / 4)) (ε / 4)
      have hx' := abs_lt.mp hx
      constructor <;> linarith
    have hcx : c x = 1 := (hcone x).1 hxt
    simp [hcx]
  have hmulq :
      Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f *
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal g = 1 := by
    calc
      Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal f *
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal g
          = Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal (f * g) := by
            simp
      _ = Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal c := by
            simpa using congrArg (Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal) hmul
      _ = 1 := hc_one
  refine ⟨Units.mkOfMulEqOne _ _ hmulq, ?_⟩
  simpa using Units.val_mkOfMulEqOne hmulq

/-- The quotient model `R / I` is a localization of `R` at the maximal ideal of functions
vanishing at `0`. -/
instance smoothRealFunctionQuotientAtZero_isLocalizationAtVanishingAtZeroIdeal :
    IsLocalization smoothRealFunctionsVanishingAtZeroIdeal.primeCompl
      smoothRealFunctionQuotientAtZero := by
  rw [isLocalization_iff]
  constructor
  · intro y
    refine quotient_mk_isUnit_of_eval_ne_zero y ?_
    intro hy0
    exact y.2 (by simpa [smoothRealFunctionsVanishingAtZeroIdeal] using hy0)
  constructor
  · intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨x, 1⟩, ?_⟩
    simp
  · intro x y hxy
    have hxy' :
        Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal x =
          Ideal.Quotient.mk smoothRealFunctionsVanishingNearZeroIdeal y := by
      simpa using hxy
    have hmem : x - y ∈ smoothRealFunctionsVanishingNearZeroIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hxy', sub_self]
    rcases exists_primeCompl_multiplier_eq_zero_of_mem_vanishingNearZeroIdeal (x - y) hmem with
      ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [mul_sub, sub_eq_zero] using hc

/-- The source-facing localization `R_𝔪` and the quotient model `R / I` are canonically
equivalent. -/
noncomputable abbrev smoothRealFunctionLocalizationAtZeroEquivQuotient :
    smoothRealFunctionLocalizationAtZero ≃ₐ[SmoothRealFunctionRing]
      smoothRealFunctionQuotientAtZero :=
  IsLocalization.algEquiv smoothRealFunctionsVanishingAtZeroIdeal.primeCompl _ _

/-- The module `M = R_𝔪` is finite over `R`. -/
instance smoothRealFunctionLocalizationAtZero_finite :
    Module.Finite SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  Module.Finite.equiv smoothRealFunctionLocalizationAtZeroEquivQuotient.symm.toLinearEquiv

/-- The source-facing localization `M = R_𝔪` is flat over `R = C^\infty(\mathbf R, \mathbf R)`. -/
instance smoothRealFunctionLocalizationAtZero_flat :
    Module.Flat SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  inferInstance

/-- Helper for Remark 10.78.4: a projective quotient ring comes from an idempotent generator of
the kernel ideal. -/
lemma exists_idempotent_generator_of_projective_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (hproj : Module.Projective R (R ⧸ I)) :
    ∃ e : R, IsIdempotentElem e ∧ e ∈ I ∧ I = Ideal.span {e} := by
  let _ : Module.Projective R (R ⧸ I) := hproj
  obtain ⟨σ, hσ⟩ :=
    (Module.Projective.iff_split_of_projective (R := R)
      ((Ideal.Quotient.mkₐ R I).toLinearMap) Ideal.Quotient.mk_surjective).mp hproj
  let e : R := 1 - σ 1
  -- The section sends `1` to a lift of `1`, so `e = 1 - σ(1)` lands in the kernel ideal.
  have hσ1 : Ideal.Quotient.mk I (σ 1) = 1 := by
    simpa using DFunLike.congr_fun hσ (1 : R ⧸ I)
  have he_mem : e ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp [e, hσ1]
  have hmul_right : ∀ {x : R}, x ∈ I → x = x * e := by
    -- Every kernel element is fixed by right multiplication with `e`.
    intro x hx
    have hxq : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hσx : σ (Ideal.Quotient.mk I x) = x * σ 1 := by
      calc
        σ (Ideal.Quotient.mk I x) = σ (x • (1 : R ⧸ I)) := by simp [Algebra.smul_def]
        _ = x • σ 1 := by rw [map_smul]
        _ = x * σ 1 := by simp [smul_eq_mul]
    have hxσ0 : x * σ 1 = 0 := by
      simpa [hσx] using congrArg σ hxq
    calc
      x = x * 1 := by simp
      _ = x * (e + σ 1) := by simp [e, sub_eq_add_neg, add_comm, add_left_comm]
      _ = x * e + x * σ 1 := by ring
      _ = x * e := by simp [hxσ0]
  have hspan_le : Ideal.span {e} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 he_mem
  have hle : I ≤ Ideal.span {e} := by
    -- Conversely, every kernel element is a multiple of `e`.
    intro x hx
    rw [hmul_right hx]
    exact Ideal.mem_span_singleton'.mpr ⟨x, by simp⟩
  have he_idem : IsIdempotentElem e := by
    simpa [IsIdempotentElem] using (hmul_right he_mem).symm
  exact ⟨e, he_idem, he_mem, le_antisymm hle hspan_le⟩

/-- Helper for Remark 10.78.4: a smooth idempotent that vanishes on a neighborhood of `0` must be
the zero function. -/
lemma smooth_idempotent_eq_zero_of_vanishes_near_zero (f : SmoothRealFunctionRing)
    (hf : IsIdempotentElem f) (hvanish : f ∈ smoothRealFunctionsVanishingNearZeroIdeal) :
    f = 0 := by
  rcases hvanish with ⟨ε, hε, hzero⟩
  -- A nonzero value would have to be `1`, but connectedness forces the intermediate value `1/2`.
  ext x
  have hval : f x = 0 ∨ f x = 1 := by
    have hidx : IsIdempotentElem (f x) := by
      simpa [IsIdempotentElem] using congrArg (fun g : SmoothRealFunctionRing ↦ g x) hf
    exact IsIdempotentElem.iff_eq_zero_or_one.mp hidx
  rcases hval with hfx | hfx
  · exact hfx
  · have h0 : f 0 = 0 := hzero 0 (by simpa using hε)
    have hhalf : (1 / 2 : ℝ) ∈ Set.range (f : ℝ → ℝ) := by
      have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (f 0) (f x) := by
        rw [h0, hfx]
        norm_num
      exact intermediate_value_univ (0 : ℝ) x f.contMDiff.continuous hhalf_mem
    rcases hhalf with ⟨y, hy⟩
    have hy_idem : IsIdempotentElem (f y) := by
      simpa [IsIdempotentElem] using congrArg (fun g : SmoothRealFunctionRing ↦ g y) hf
    have : (1 / 2 : ℝ) = 0 ∨ (1 / 2 : ℝ) = 1 := by
      simpa [hy] using (IsIdempotentElem.iff_eq_zero_or_one.mp hy_idem)
    norm_num at this

/-- Helper for Remark 10.78.4: the near-zero ideal is nontrivial, witnessed by a bump function
supported away from the origin. -/
lemma smoothRealFunctionsVanishingNearZeroIdeal_ne_bot :
    smoothRealFunctionsVanishingNearZeroIdeal ≠ ⊥ := by
  let s : Set ℝ := Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)
  let t : Set ℝ := Set.Icc (1 : ℝ) 1
  rcases smooth_cutoff_support_eq_eq_one (s := s) (t := t) isOpen_Ioo isClosed_Icc
      (by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) with
    ⟨c, hcsupp, -, hcone⟩
  have hc_mem : c ∈ smoothRealFunctionsVanishingNearZeroIdeal := by
    -- The support is disjoint from a neighborhood of `0`, so the cutoff vanishes there.
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro x hx
    have hx_support : x ∉ Function.support (c : ℝ → ℝ) := by
      rw [hcsupp]
      intro hx'
      have hx'' : x ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) := hx'
      have hxpos : (1 / 2 : ℝ) < x := hx''.1
      have hxabs' : x ≤ |x| := by exact le_abs_self x
      linarith
    rwa [Function.notMem_support] at hx_support
  intro hbot
  have hc_zero : c = 0 := by simpa [hbot] using hc_mem
  have hc1 : c 1 = 1 := (hcone 1).1 (by simp [t])
  have : (1 : ℝ) = 0 := by simpa [hc_zero] using hc1
  exact one_ne_zero this

-- Proof sketch: use the standard smooth-function counterexample: the localization `R_𝔪`,
-- equivalently the quotient `R / I`, is finite and flat but not projective.
/-- Remark 10.78.4: for `R = C^\infty(\mathbf R, \mathbf R)` and
`M = R_𝔪 = R / I`, where `𝔪` is the maximal ideal of functions vanishing at `0` and `I` consists
of smooth functions vanishing on a neighborhood of `0`, the module `M` is not projective.
Together with the companion instances asserting that `M` is finite and flat, this gives the stated
counterexample to the implication "finite flat implies projective". -/
@[stacks 00NY]
theorem smoothRealFunctionLocalizationAtZero_not_projective :
    ¬ Module.Projective SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero := by
  -- Route correction: pass to the quotient model `R / I`, then force the kernel ideal to be
  -- idempotent-generated and use connectedness of `ℝ` to show that idempotent must vanish.
  intro hproj
  let _ : Module.Projective SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero := hproj
  have hquot :
      Module.Projective SmoothRealFunctionRing smoothRealFunctionQuotientAtZero :=
    Module.Projective.of_equiv' smoothRealFunctionLocalizationAtZeroEquivQuotient.toLinearEquiv
  obtain ⟨e, he_idem, he_mem, hI⟩ :=
    exists_idempotent_generator_of_projective_quotient
      smoothRealFunctionsVanishingNearZeroIdeal hquot
  have he_zero : e = 0 := smooth_idempotent_eq_zero_of_vanishes_near_zero e he_idem he_mem
  have hbot : smoothRealFunctionsVanishingNearZeroIdeal = ⊥ := by
    rw [hI, he_zero]
    simp
  exact smoothRealFunctionsVanishingNearZeroIdeal_ne_bot hbot
