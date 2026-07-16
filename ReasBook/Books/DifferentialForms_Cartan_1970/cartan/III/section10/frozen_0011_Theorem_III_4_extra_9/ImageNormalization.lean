import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0010_Remark_III_4_extra_8»

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a subset of `ℂ` whose
complement has at most one point is either all of `ℂ` or the complement of a singleton. -/
lemma eq_univ_or_compl_singleton_of_compl_subsingleton {s : Set ℂ}
    (hcompl : ∀ ⦃a b : ℂ⦄, a ∉ s → b ∉ s → a = b) :
    s = univ ∨ ∃ a : ℂ, s = ({a} : Set ℂ)ᶜ := by
  classical
  by_cases hs : s = univ
  · exact Or.inl hs
  · right
    -- Pick the unique omitted value once the set is known not to be all of `ℂ`.
    obtain ⟨a, ha⟩ : ∃ a : ℂ, a ∉ s := by
      by_contra hnone
      apply hs
      ext z
      simp only [mem_univ, iff_true]
      by_contra hz
      exact hnone ⟨z, hz⟩
    refine ⟨a, ?_⟩
    ext z
    constructor
    · intro hz
      -- Any point already in `s` cannot be the unique omitted value.
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hza
      exact ha (hza ▸ hz)
    · intro hz
      -- Any other omitted point must coincide with the chosen one, contradicting `z ≠ a`.
      simp only [mem_compl_iff, mem_singleton_iff] at hz
      by_contra hz'
      exact hz (hcompl hz' ha)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: translating the punctured ball
centered at `o` to the origin preserves punctured-ball analyticity. -/
lemma analyticOnNhd_puncturedBall_translate_iff {f : ℂ → ℂ} {o : ℂ} {ε : ℝ} :
    AnalyticOnNhd ℂ f (ball o ε \ ({o} : Set ℂ)) ↔
      AnalyticOnNhd ℂ (fun z ↦ f (z + o)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  constructor
  · intro hf z hz
    -- Compose the local analyticity at `z + o` with the translation `w ↦ w + o`.
    have hz' : z + o ∈ ball o ε \ ({o} : Set ℂ) := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hz.1
      · simp only [mem_singleton_iff] at hz ⊢
        intro hzo
        apply hz.2
        have hz0 : z = 0 := by
          have hsub := congrArg (fun w : ℂ ↦ w - o) hzo
          simpa [sub_eq_add_neg, add_assoc] using hsub
        exact hz0
    have htranslate : AnalyticAt ℂ (fun w : ℂ ↦ w + o) z := by
      fun_prop
    have hanalytic : AnalyticAt ℂ f (z + o) := hf (z + o) hz'
    have hcomp :
        AnalyticAt ℂ ((fun w : ℂ ↦ f w) ∘ (fun w : ℂ ↦ w + o)) z :=
      AnalyticAt.comp (g := f) (f := fun w : ℂ ↦ w + o) hanalytic htranslate
    simpa [Function.comp] using hcomp
  · intro hf z hz
    -- Compose the translated analyticity with the inverse translation `w ↦ w - o`.
    have hz' : z - o ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hz.1
      · simp only [mem_singleton_iff] at hz ⊢
        exact sub_ne_zero.mpr hz.2
    have htranslate : AnalyticAt ℂ (fun w : ℂ ↦ w - o) z := by
      fun_prop
    have hanalytic : AnalyticAt ℂ (fun z ↦ f (z + o)) (z - o) := hf (z - o) hz'
    have hcomp :
        AnalyticAt ℂ ((fun w : ℂ ↦ f (w + o)) ∘ (fun w : ℂ ↦ w - o)) z :=
      AnalyticAt.comp (g := fun w : ℂ ↦ f (w + o)) (f := fun w : ℂ ↦ w - o) hanalytic htranslate
    have hfun : ((fun w : ℂ ↦ f (w + o)) ∘ fun w : ℂ ↦ w - o) = f := by
      ext w
      simp [Function.comp, sub_eq_add_neg, add_assoc]
    simpa [hfun] using hcomp

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: translating the punctured ball
to the origin does not change the image set, only its parameterization. -/
lemma image_puncturedBall_translate_eq {f : ℂ → ℂ} {o : ℂ} {ε : ℝ} :
    (fun z ↦ f (z + o)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) =
      f '' (ball o ε \ ({o} : Set ℂ)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + o, ?_, rfl⟩
    constructor
    · -- The translated parameter still lies in the radius-`ε` ball around `o`.
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hz.1
    · -- The puncture at `0` becomes the puncture at `o`.
      simp only [mem_singleton_iff] at hz ⊢
      intro hzo
      apply hz.2
      have hz0 : z = 0 := by
        have hsub := congrArg (fun w : ℂ ↦ w - o) hzo
        simpa [sub_eq_add_neg, add_assoc] using hsub
      exact hz0
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - o, ?_, ?_⟩
    · constructor
      · -- Subtracting the center identifies the original punctured ball with the centered one.
        simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hz.1
      · -- The puncture at `o` becomes the puncture at `0`.
        simp only [mem_singleton_iff] at hz ⊢
        exact sub_ne_zero.mpr hz.2
    · simp [sub_eq_add_neg, add_assoc]

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if `f` omits `b` on the
punctured ball, then the normalized ratio `(f - a) / (f - b)` stays analytic there. -/
lemma normalizedOmittedRatio_analyticOnNhd
    {f : ℂ → ℂ} {ε : ℝ} {a b : ℂ}
    (h_analytic : AnalyticOnNhd ℂ f (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hb : b ∉ f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    AnalyticOnNhd ℂ (fun z ↦ (f z - a) / (f z - b)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  -- The only analytic bookkeeping is that the denominator never vanishes on the punctured ball.
  have hdenom_ne :
      ∀ z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ), f z - b ≠ 0 := by
    intro z hz hzb
    apply hb
    exact ⟨z, hz, sub_eq_zero.mp hzb⟩
  have hnum_analytic : AnalyticOnNhd ℂ (fun z ↦ f z - a) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    simpa using h_analytic.sub analyticOnNhd_const
  have hdenom_analytic : AnalyticOnNhd ℂ (fun z ↦ f z - b) (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
    simpa using h_analytic.sub analyticOnNhd_const
  exact hnum_analytic.div hdenom_analytic hdenom_ne

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: after normalizing by
`(f - a) / (f - b)`, the omitted values `a` and `b` become the omitted values `0` and `1`. -/
lemma normalizedOmittedRatio_avoids_zero_one
    {f : ℂ → ℂ} {ε : ℝ} {a b : ℂ}
    (hab : a ≠ b)
    (ha : a ∉ f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hb : b ∉ f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    0 ∉ (fun z ↦ (f z - a) / (f z - b)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) ∧
      1 ∉ (fun z ↦ (f z - a) / (f z - b)) '' (ball (0 : ℂ) ε \ ({0} : Set ℂ)) := by
  constructor
  · -- A zero of the normalized ratio would force `f z = a`, contradicting the omitted-value
    -- hypothesis for `a`.
    rintro ⟨z, hz, hz0⟩
    have hdenom_ne : f z - b ≠ 0 := by
      intro hzb
      apply hb
      exact ⟨z, hz, sub_eq_zero.mp hzb⟩
    have hnum_zero : f z - a = 0 := by
      exact (div_eq_zero_iff.mp hz0).resolve_right hdenom_ne
    apply ha
    exact ⟨z, hz, sub_eq_zero.mp hnum_zero⟩
  · -- Hitting the value `1` would force `f z - a = f z - b`, hence `a = b`.
    rintro ⟨z, hz, hz1⟩
    have hdenom_ne : f z - b ≠ 0 := by
      intro hzb
      apply hb
      exact ⟨z, hz, sub_eq_zero.mp hzb⟩
    have hsame : f z - a = f z - b := (div_eq_one_iff_eq hdenom_ne).mp hz1
    have hab' : a = b := by
      have hsub : f z - f z = a - b := (sub_eq_sub_iff_sub_eq_sub.mp hsame)
      exact sub_eq_zero.mp <| by simpa using hsub.symm
    exact hab hab'

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: reconstruct `f` from the
normalized ratio `(f - a) / (f - b)` away from the omitted value `b`. -/
lemma normalizedOmittedRatio_reconstruct
    {f : ℂ → ℂ} {ε : ℝ} {a b z : ℂ}
    (hab : a ≠ b)
    (hz : z ∈ ball (0 : ℂ) ε \ ({0} : Set ℂ))
    (hb : b ∉ f '' (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    f z = (b * ((f z - a) / (f z - b)) - a) / (((f z - a) / (f z - b)) - 1) := by
  -- Clearing denominators gives the textbook rational inversion formula.
  have hdenom_ne : f z - b ≠ 0 := by
    intro hzb
    apply hb
    exact ⟨z, hz, sub_eq_zero.mp hzb⟩
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr fun hba ↦ hab hba.symm
  field_simp [hdenom_ne, hba_ne]
  ring

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: analyticity on a punctured ball
already packages the owner-level isolated-singularity hypothesis at the center. -/
lemma hasIsolatedSingularityAt_of_analyticOnNhd_puncturedBall
    {g : ℂ → ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    HasIsolatedSingularityAt g 0 := by
  -- Repackage the punctured-ball analyticity data using the owner equivalence for isolated
  -- singularities.
  exact (HasIsolatedSingularityAt.iff_exists_analyticOnNhd_punctured_ball).2 ⟨ε, hε, hg_analytic⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the quarter ball centered at
`1 / 2` lies inside the Exercise 16 lens domain. -/
lemma quarterBall_half_subset_exercise16Domain :
    Metric.ball ((1 : ℂ) / 2) (1 / 4 : ℝ) ⊆ exercise16Domain := by
  intro w hw
  constructor
  · -- The first lens inequality follows by the triangle inequality around `1 / 2`.
    have hw_half : ‖w - (1 : ℂ) / 2‖ < 1 / 4 := by
      simpa [Metric.mem_ball, Complex.dist_eq] using hw
    have hrepr : (w - (1 : ℂ) / 2) + (1 : ℂ) / 2 = w := by ring
    have hnorm : ‖w‖ ≤ ‖w - (1 : ℂ) / 2‖ + ‖(1 : ℂ) / 2‖ := by
      have hnorm' : ‖(w - (1 : ℂ) / 2) + (1 : ℂ) / 2‖ ≤
          ‖w - (1 : ℂ) / 2‖ + ‖(1 : ℂ) / 2‖ :=
        norm_add_le _ _
      simpa [hrepr] using hnorm'
    have hhalf : ‖(1 : ℂ) / 2‖ = (1 : ℝ) / 2 := by norm_num
    have hlt : ‖w‖ < 1 := by
      rw [hhalf] at hnorm
      linarith
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hlt
  · -- The second lens inequality is the same estimate after shifting by `1`.
    have hw_half : ‖w - (1 : ℂ) / 2‖ < 1 / 4 := by
      simpa [Metric.mem_ball, Complex.dist_eq] using hw
    have hnorm' : ‖w - 1‖ ≤ ‖w - (1 : ℂ) / 2‖ + ‖-(1 : ℂ) / 2‖ := by
      -- Rewrite `w - 1` as `(w - 1 / 2) + (-1 / 2)` and apply the triangle inequality once.
      convert (norm_add_le (w - (1 : ℂ) / 2) (-(1 : ℂ) / 2)) using 1
      ring_nf
    have hnorm : ‖w - 1‖ ≤ ‖w - (1 : ℂ) / 2‖ + ‖(1 : ℂ) / 2‖ := by
      simpa using hnorm'
    have hhalf : ‖(1 : ℂ) / 2‖ = (1 : ℝ) / 2 := by norm_num
    have hlt : ‖w - 1‖ < 1 := by
      rw [hhalf] at hnorm
      linarith
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using hlt

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: the Exercise 16 lens domain is
stable under the involution `w ↦ 1 - w`. -/
lemma exercise16Domain_one_sub_mem {w : ℂ} (hw : w ∈ exercise16Domain) :
    1 - w ∈ exercise16Domain := by
  rcases hw with ⟨hw0, hw1⟩
  constructor
  · -- Swap the two unit-ball conditions using `‖1 - w‖ = ‖w - 1‖`.
    have hw1' : ‖w - 1‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw1
    have hnormEq : ‖1 - w‖ = ‖w - 1‖ := by
      simpa [sub_eq_add_neg] using norm_sub_rev (1 : ℂ) w
    have hnorm : ‖1 - w‖ < 1 := by
      rw [hnormEq]
      exact hw1'
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  · -- The second condition is just the first one rewritten as `‖(1 - w) - 1‖ = ‖w‖`.
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_neg] using hw0

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: mapping into
`exercise16Domain` automatically keeps `1 - g` inside the same lens domain. -/
lemma mapsTo_one_sub_exercise16Domain {g : ℂ → ℂ} {E : Set ℂ}
    (hgE : MapsTo g E exercise16Domain) :
    MapsTo (fun z ↦ 1 - g z) E exercise16Domain := by
  intro z hz
  -- Apply the involution symmetry of the lens domain pointwise.
  exact exercise16Domain_one_sub_mem (hgE hz)

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: a dense punctured-ball image
already hits the Exercise 16 lens domain. -/
lemma exists_preimage_in_exercise16Domain_of_dense_image
    {g : ℂ → ℂ} {ρ : ℝ}
    (hdense : Dense (g '' (ball (0 : ℂ) ρ \ ({0} : Set ℂ)))) :
    ∃ z ∈ ball (0 : ℂ) ρ \ ({0} : Set ℂ), g z ∈ exercise16Domain := by
  -- Use density to hit the fixed nonempty open ball inside `exercise16Domain`.
  have hnonempty :
      (Metric.ball ((1 : ℂ) / 2) (1 / 4 : ℝ) ∩
        g '' (ball (0 : ℂ) ρ \ ({0} : Set ℂ))).Nonempty := by
    exact (Metric.dense_iff.1 hdense) ((1 : ℂ) / 2) (1 / 4 : ℝ) (by norm_num)
  rcases hnonempty with ⟨w, hwball, hwimage⟩
  rcases hwimage with ⟨z, hz, rfl⟩
  exact ⟨z, hz, quarterBall_half_subset_exercise16Domain hwball⟩

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: by reapplying Weierstrass
density on every smaller punctured ball, the preimage of `exercise16Domain` accumulates at `0`. -/
lemma exercise16Domain_preimage_accumulates_at_zero
    {g : ℂ → ℂ} {ε δ : ℝ}
    (hess : HasEssentialSingularityAt g 0) (hε : 0 < ε) (hδ : 0 < δ)
    (hg_analytic : AnalyticOnNhd ℂ g (ball (0 : ℂ) ε \ ({0} : Set ℂ))) :
    ∃ z ∈ ball (0 : ℂ) (min δ ε) \ ({0} : Set ℂ), g z ∈ exercise16Domain := by
  let ρ : ℝ := min δ ε
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hδ hε
  have hg_small : AnalyticOnNhd ℂ g (ball (0 : ℂ) ρ \ ({0} : Set ℂ)) := by
    -- Restrict the punctured-ball analyticity to the smaller punctured ball.
    refine hg_analytic.mono ?_
    intro z hz
    constructor
    · dsimp [ρ] at hz
      simpa [Metric.mem_ball] using
        (lt_of_lt_of_le (by simpa [Metric.mem_ball] using hz.1) (min_le_right δ ε))
    · exact hz.2
  have hdense_small :
      Dense (g '' (ball (0 : ℂ) ρ \ ({0} : Set ℂ))) :=
    weierstrass_dense_image_of_isolated_essential_singularity hess hρ hg_small
  -- Once the smaller image is dense, it must hit the fixed open lens domain.
  exact exists_preimage_in_exercise16Domain_of_dense_image (g := g) (ρ := ρ) hdense_small

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: on a preconnected source
domain, two continuous functions with the same exponential differ by one fixed integral multiple
of `2π i`. -/
lemma eqOn_add_two_pi_I_mul_int_of_exp_eq_on_preconnected
    {E : Set ℂ} {F₁ F₂ : ℂ → ℂ}
    (hE : IsPreconnected E)
    (hF₁ : ContinuousOn F₁ E)
    (hF₂ : ContinuousOn F₂ E)
    (hexp : Set.EqOn (fun z ↦ Complex.exp (F₁ z)) (fun z ↦ Complex.exp (F₂ z)) E) :
    ∃ k : ℤ, Set.EqOn F₂ (fun z ↦ F₁ z + k * (2 * (Real.pi : ℂ) * Complex.I)) E := by
  by_cases hE_empty : E = ∅
  · -- The empty domain carries no monodromy, so the zero period works immediately.
    refine ⟨0, ?_⟩
    intro z hz
    exact (hE_empty ▸ hz).elim
  let η : ℂ → ℝ := fun z ↦ (F₂ z - F₁ z).im / (2 * Real.pi : ℝ)
  have hη_cont : ContinuousOn η E := by
    -- The normalized imaginary part of the difference is continuous on the source domain.
    simpa [η] using
      (Complex.continuous_im.comp_continuousOn (hF₂.sub hF₁)).div_const (2 * Real.pi : ℝ)
  have hη_image_subset : η '' E ⊆ Set.range (fun k : ℤ ↦ (k : ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    -- Pointwise equality of exponentials forces the difference to be an integer period.
    have hExp : Complex.exp (F₂ z) = Complex.exp (F₁ z) := by
      simpa using (hexp hz).symm
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hExp
    refine ⟨k, ?_⟩
    have hsub : F₂ z - F₁ z = k * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hk, add_sub_cancel_left]
    have hk_im : (F₂ z - F₁ z).im = (k : ℝ) * (2 * Real.pi) := by
      calc
        (F₂ z - F₁ z).im = (k * (2 * (Real.pi : ℂ) * Complex.I)).im := by rw [hsub]
        _ = (((k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I)).im) := by rw [zsmul_eq_mul]
        _ = (k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I).im := by rw [Complex.im_zsmul]
        _ = (k : ℝ) * (2 * Real.pi) := by simp
    have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact ((div_eq_iff htwo_pi_ne).2 hk_im).symm
  have hη_image_subsingleton : (η '' E).Subsingleton := by
    -- A preconnected subset of the integer lattice in `ℝ` must be a singleton.
    have hcount : (Set.range (fun k : ℤ ↦ (k : ℝ))).Countable := Set.countable_range _
    exact hcount.isTotallyDisconnected (η '' E) hη_image_subset (hE.image η hη_cont)
  have hη_const : ∀ ⦃z w : ℂ⦄, z ∈ E → w ∈ E → η z = η w := by
    intro z w hz hw
    exact hη_image_subsingleton ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
  obtain ⟨z₀, hz₀⟩ : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
  have hExp₀ : Complex.exp (F₂ z₀) = Complex.exp (F₁ z₀) := by
    simpa using (hexp hz₀).symm
  obtain ⟨k₀, hk₀⟩ := Complex.exp_eq_exp_iff_exists_int.mp hExp₀
  have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hη_eq_int :
      ∀ ⦃z : ℂ⦄ ⦃k : ℤ⦄,
        F₂ z = F₁ z + k * (2 * (Real.pi : ℂ) * Complex.I) → η z = k := by
    intro z k hk
    have hsub : F₂ z - F₁ z = k * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hk, add_sub_cancel_left]
    have hk_im : (F₂ z - F₁ z).im = (k : ℝ) * (2 * Real.pi) := by
      calc
        (F₂ z - F₁ z).im = (k * (2 * (Real.pi : ℂ) * Complex.I)).im := by rw [hsub]
        _ = (((k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I)).im) := by rw [zsmul_eq_mul]
        _ = (k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I).im := by rw [Complex.im_zsmul]
        _ = (k : ℝ) * (2 * Real.pi) := by simp
    dsimp [η]
    exact (div_eq_iff htwo_pi_ne).2 hk_im
  refine ⟨k₀, ?_⟩
  intro z hz
  -- Compare the pointwise period at `z` with the one fixed at the base point `z₀`.
  have hExp : Complex.exp (F₂ z) = Complex.exp (F₁ z) := by
    simpa using (hexp hz).symm
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hExp
  have hk_cast : (k : ℝ) = (k₀ : ℝ) := by
    calc
      (k : ℝ) = η z := (hη_eq_int hk).symm
      _ = η z₀ := hη_const hz hz₀
      _ = (k₀ : ℝ) := hη_eq_int hk₀
  have hk_eq : k = k₀ := Int.cast_injective (α := ℝ) hk_cast
  simpa [hk_eq] using hk

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: composing the Exercise 16
reflection identity with a map into the lens domain gives a constant identity on the source. -/
lemma exercise16ReflectionConstant_comp
    {a : ℂ} (ha : Exercise16ReflectionConstant a)
    {g : ℂ → ℂ} {E : Set ℂ} (hgE : MapsTo g E exercise16Domain) :
    EqOn
      (fun z ↦
        Complex.dilogarithmPowerSeries (g z) + Complex.dilogarithmPowerSeries (1 - g z) +
          Complex.log (g z) * Complex.log (1 - g z))
      (fun _ ↦ a) E := by
  intro z hz
  -- Evaluate the reflected dilogarithm identity at the image point `g z`.
  have hz_reflect := ha (g z) (hgE hz)
  calc
    Complex.dilogarithmPowerSeries (g z) + Complex.dilogarithmPowerSeries (1 - g z) +
        Complex.log (g z) * Complex.log (1 - g z)
      = (a - Complex.log (g z) * Complex.log (1 - g z)) +
          Complex.log (g z) * Complex.log (1 - g z) := by
            rw [hz_reflect]
    _ = a := by ring
