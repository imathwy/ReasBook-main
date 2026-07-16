import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2»
import DifferentialForms_Cartan_1970.cartan.V.section19.«0010_Definition_V_2_extra_5»
import DifferentialForms_Cartan_1970.cartan.V.section19.«0011_Proposition_5_2»
import DifferentialForms_Cartan_1970.cartan.V.section21.«0018_Exercise_9»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open MeromorphicOn

namespace PeriodPair

-- Semantic recall note: the source-facing owner for the chosen domain is
-- `PeriodPair.periodParallelogram`, the divisor data is carried by `MeromorphicOn.divisor`, and
-- the period-lattice class lives in `ℂ ⧸ L.lattice.toAddSubgroup`.

/-- Helper for Exercise 10: the affine linear combination `℘' - α ℘ - β` is meromorphic and
periodic for the period lattice `L.lattice`. -/
lemma weierstrass_linear_form_has_period_lattice
    (L : PeriodPair) (α β : ℂ) :
    Meromorphic (fun z ↦ ℘'[L] z - α * ℘[L] z - β) ∧
      HasPeriodLattice L (fun z ↦ ℘'[L] z - α * ℘[L] z - β) := by
  constructor
  · have hscale : Meromorphic (fun z ↦ α * ℘[L] z) := by
      -- Meromorphicity is preserved by multiplying `℘` by a complex scalar.
      simpa using (Meromorphic.const α).mul L.meromorphic_weierstrassP
    have hsub : Meromorphic (fun z ↦ ℘'[L] z - α * ℘[L] z) :=
      L.meromorphic_derivWeierstrassP.sub hscale
    -- Subtracting the constant term keeps the function meromorphic.
    exact hsub.sub (Meromorphic.const β)
  · intro ω hω z
    let l : L.lattice := ⟨ω, hω⟩
    -- The lattice-periodicity of `℘` and `℘'` transports directly to the affine linear form.
    simp [l, L.weierstrassP_add_coe z l, L.derivWeierstrassP_add_coe z l]

/-- Helper for Exercise 10: away from the period lattice, the affine linear combination
`℘' - α ℘ - β` is analytic. -/
lemma analyticAt_weierstrass_linear_form_of_not_mem_lattice
    (L : PeriodPair) {α β z : ℂ} (hz : z ∉ L.lattice) :
    AnalyticAt ℂ (fun w ↦ ℘'[L] w - α * ℘[L] w - β) z := by
  -- Off the lattice, both `℘` and `℘'` are analytic, so the affine combination is analytic too.
  have hderiv : AnalyticAt ℂ ℘'[L] z := L.analyticOnNhd_derivWeierstrassP z hz
  have hweier : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
  have hscale : AnalyticAt ℂ (fun w ↦ (α : ℂ) * ℘[L] w) z := analyticAt_const.mul hweier
  exact (hderiv.sub hscale).sub analyticAt_const

/-- Helper for Exercise 10: at the origin, the affine linear combination `℘' - α ℘ - β`
regularizes after multiplication by `z^3`, and the resulting analytic germ is nonzero. -/
lemma analyticAt_regularized_weierstrass_linear_form
    (L : PeriodPair) (α β : ℂ) :
    let g : ℂ → ℂ := fun z ↦
      (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) -
        α * z * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) - β * z ^ 3
    AnalyticAt ℂ g 0 ∧ g 0 = -2 := by
  let g : ℂ → ℂ := fun z ↦
    (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) -
      α * z * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) - β * z ^ 3
  constructor
  · -- Each regularized Weierstrass term is analytic at `0`, so the whole affine combination is.
    have hderiv : AnalyticAt ℂ (fun z ↦ ℘'[L - (0 : ℂ)] z * z ^ 3 - 2) 0 := by
      fun_prop
    have hweier : AnalyticAt ℂ (fun z ↦ α * z * (℘[L - (0 : ℂ)] z * z ^ 2 + 1)) 0 := by
      fun_prop
    have hpoly : AnalyticAt ℂ (fun z ↦ β * z ^ 3) 0 := by
      fun_prop
    convert (hderiv.sub hweier).sub hpoly using 1
  · -- At the origin, the regularized Weierstrass terms collapse to their Exercise 9 values.
    simp [g]

/-- Helper for Exercise 10: at the origin, the affine linear combination `℘' - α ℘ - β`
has the same triple pole as `℘'`. -/
lemma meromorphicOrderAt_weierstrass_linear_form_at_zero
    (L : PeriodPair) (α β : ℂ) :
    meromorphicOrderAt (fun z ↦ ℘'[L] z - α * ℘[L] z - β) 0 = (-3 : WithTop ℤ) := by
  let f : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  let g : ℂ → ℂ := fun z ↦
    (℘'[L - (0 : ℂ)] z * z ^ 3 - 2) -
      α * z * (℘[L - (0 : ℂ)] z * z ^ 2 + 1) - β * z ^ 3
  have hf : MeromorphicAt f 0 := by
    -- Meromorphicity comes from the global meromorphic linear-form package already proved above.
    simpa [f] using (L.weierstrass_linear_form_has_period_lattice α β).1 0
  change meromorphicOrderAt f 0 = (-3 : ℤ)
  rw [meromorphicOrderAt_eq_int_iff hf]
  have hg := L.analyticAt_regularized_weierstrass_linear_form α β
  refine ⟨g, ?_, ?_, ?_⟩
  · -- The chosen regularized factor is analytic at the origin.
    simpa [g] using hg.1
  · -- Its value is the nonzero principal coefficient `-2`.
    simpa [g] using hg.2
  · -- Route correction: instead of comparing orders term-by-term, rewrite the punctured germ
    -- directly to the regularized source expression used in Exercise 9.
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hregularized :
        g z = z ^ 3 * f z := by
      simp only [g, f, L.derivWeierstrassPExcept_def, L.weierstrassPExcept_def,
        ← ZeroMemClass.coe_zero L.lattice]
      simp [hz0]
      field_simp
      ring
    have hfactor :
        (z : ℂ) ^ (-3 : ℤ) * (z ^ 3 * f z) = f z := by
      calc
        (z : ℂ) ^ (-3 : ℤ) * (z ^ 3 * f z) =
            ((z : ℂ) ^ (-3 : ℤ) * z ^ 3) * f z := by
              rw [mul_assoc]
        _ = f z := by
          calc
            ((z : ℂ) ^ (-3 : ℤ) * z ^ 3) * f z = (1 : ℂ) * f z := by
              simpa [mul_assoc] using
                congrArg (fun w : ℂ ↦ w * f z) (zpow_neg_mul_zpow_self 3 hz0)
            _ = f z := by simp
    calc
      f z = (z : ℂ) ^ (-3 : ℤ) * g z := by
        rw [hregularized]
        exact hfactor.symm
      _ = (z - 0) ^ (-3 : ℤ) • g z := by simp [smul_eq_mul]

/-- Helper for Exercise 10: off the lattice, the affine linear combination `℘' - α ℘ - β`
cannot vanish on a whole neighborhood. -/
lemma analyticOrderAt_weierstrass_linear_form_ne_top_of_not_mem_lattice
    (L : PeriodPair) {α β z : ℂ} (hz : z ∉ L.lattice) :
    analyticOrderAt (fun w ↦ ℘'[L] w - α * ℘[L] w - β) z ≠ ⊤ := by
  let g : ℂ → ℂ := fun w ↦ ℘'[L] w - α * ℘[L] w - β
  have hg : AnalyticOnNhd ℂ g (L.latticeᶜ : Set ℂ) := by
    intro w hw
    simpa [g] using L.analyticAt_weierstrass_linear_form_of_not_mem_lattice (α := α) (β := β) hw
  have hconnected : IsPreconnected (L.latticeᶜ : Set ℂ) := L.isPreconnected_compl_lattice
  intro htop
  have hzero_local : g =ᶠ[𝓝 z] 0 := by
    simpa [g] using analyticOrderAt_eq_top.mp htop
  have hzero_global : Set.EqOn g 0 (L.latticeᶜ : Set ℂ) :=
    hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconnected hz hzero_local
  have hnear_lattice :
      ((↑L.lattice \ ({(0 : ℂ)} : Set ℂ))ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_diff_singleton_mem_nhds 0)
  have hzero_punctured : ∀ᶠ w in 𝓝[≠] (0 : ℂ), g w = 0 := by
    -- The punctured neighborhood of the origin lies in the connected complement of the lattice.
    filter_upwards [self_mem_nhdsWithin, hnear_lattice] with w hw0 hwnear
    have hw_not_lattice : w ∉ L.lattice := by
      intro hwL
      have hw_mem_diff : w ∈ (↑L.lattice \ ({(0 : ℂ)} : Set ℂ) : Set ℂ) := by
        refine ⟨hwL, ?_⟩
        simpa [Set.mem_compl_iff] using hw0
      exact hwnear hw_mem_diff
    exact hzero_global hw_not_lattice
  have horder_top : meromorphicOrderAt g (0 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    exact hzero_punctured
  have horder_zero := L.meromorphicOrderAt_weierstrass_linear_form_at_zero α β
  rw [horder_zero] at horder_top
  simp at horder_top

/-- Helper for Exercise 10: away from the lattice, positivity of the divisor of
`℘' - α ℘ - β` is equivalent to vanishing of the affine linear combination itself. -/
lemma divisor_linear_form_pos_iff_of_not_mem_lattice
    (L : PeriodPair) {P : Set ℂ} {α β z : ℂ} (hzP : z ∈ P) (hz : z ∉ L.lattice) :
    0 < divisor (fun w ↦ ℘'[L] w - α * ℘[L] w - β) P z ↔
      ℘'[L] z - α * ℘[L] z - β = 0 := by
  let g : ℂ → ℂ := fun w ↦ ℘'[L] w - α * ℘[L] w - β
  have hg : Meromorphic g := (L.weierstrass_linear_form_has_period_lattice α β).1
  have hanalytic : AnalyticAt ℂ g z := by
    simpa [g] using L.analyticAt_weierstrass_linear_form_of_not_mem_lattice (α := α) (β := β) hz
  have hnot_top : analyticOrderAt g z ≠ ⊤ :=
    L.analyticOrderAt_weierstrass_linear_form_ne_top_of_not_mem_lattice (α := α) (β := β) hz
  constructor
  · intro hzdiv
    by_contra hgz
    have horder_zero : analyticOrderAt g z = 0 := by
      rw [hanalytic.analyticOrderAt_eq_zero]
      simpa [g, sub_eq_zero] using hgz
    have hdiv_zero : divisor g P z = 0 := by
      rw [divisor_apply hg.meromorphicOn hzP, hanalytic.meromorphicOrderAt_eq, horder_zero]
      simp
    exact (ne_of_gt hzdiv) hdiv_zero
  · intro hgz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnot_top
    have horder_ne_zero : analyticOrderAt g z ≠ 0 := by
      exact (hanalytic.analyticOrderAt_ne_zero).2 (by simpa [g] using hgz)
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact horder_ne_zero (by simpa [hn0] using hn.symm)
    have hdiv_eq : divisor g P z = (n : ℤ) := by
      rw [divisor_apply hg.meromorphicOn hzP, hanalytic.meromorphicOrderAt_eq, ← hn]
      simp
    have hdiv_ne_zero : divisor g P z ≠ 0 := by
      rw [hdiv_eq]
      exact_mod_cast hn_ne_zero
    have hnonneg : 0 ≤ divisor g P z := by
      rw [hdiv_eq]
      exact Int.ofNat_nonneg n
    exact lt_of_le_of_ne hnonneg (Ne.symm hdiv_ne_zero)

/-- Helper for Exercise 10: any divisor-weighted lattice representative is trivial in the quotient
by the period lattice. -/
lemma divisor_weighted_class_eq_zero_of_mem_lattice
    (L : PeriodPair) {n : ℤ} {z : ℂ} (hz : z ∈ L.lattice) :
    ((((n • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) = 0 := by
  -- Quotient triviality is exactly membership in the period lattice subgroup.
  change (((n • z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
    ((0 : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa using L.lattice.smul_mem n hz

/-- Helper for Exercise 10: the unique pole representative of `℘' - α ℘ - β` lies in the period
lattice. -/
lemma pole_representative_mem_lattice_of_linear_form
    (L : PeriodPair) (z₀ α β pole : ℂ)
    (hpoles :
      IsPoleRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        ({pole} : Finset ℂ)) :
    pole ∈ L.lattice := by
  by_contra hpole
  let f : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hf : Meromorphic f := (L.weierstrass_linear_form_has_period_lattice α β).1
  have hpole_mem :
      pole ∈ L.periodParallelogram z₀ := by
    exact (hpoles.mem_iff pole).1 (by simp) |>.1
  have hpole_neg :
      divisor f (L.periodParallelogram z₀) pole < 0 := by
    exact (hpoles.mem_iff pole).1 (by simp) |>.2
  have hanalytic : AnalyticAt ℂ f pole := by
    -- Route correction: instead of chasing the divisor support directly, rule out off-lattice poles
    -- by analyticity of both Weierstrass building blocks away from the lattice.
    simpa [f] using
      L.analyticAt_weierstrass_linear_form_of_not_mem_lattice (α := α) (β := β) hpole
  have horder_nonneg : 0 ≤ meromorphicOrderAt f pole := hanalytic.meromorphicOrderAt_nonneg
  have hdiv_nonneg : 0 ≤ divisor f (L.periodParallelogram z₀) pole := by
    rw [hf.meromorphicOn.divisor_apply hpole_mem]
    exact WithTop.untop₀_nonneg.2 horder_nonneg
  exact not_lt_of_ge hdiv_nonneg hpole_neg

/-- Helper for Exercise 10: the half-open period parallelogram keeps the left and bottom edges and
removes the opposite edges, so it gives one representative per lattice class. -/
def periodParallelogramHalfOpenSection (L : PeriodPair) (z₀ : ℂ) : Set ℂ :=
  {z | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
      z = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂}

/-- A point lies in the half-open period section exactly when it has the defining affine
coordinates with both basis parameters in `[0,1)`. -/
@[simp]
theorem mem_periodParallelogramHalfOpenSection_iff (L : PeriodPair) (z₀ z : ℂ) :
    z ∈ L.periodParallelogramHalfOpenSection z₀ ↔
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
        z = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ :=
  Iff.rfl

/-- Helper for Exercise 10: the half-open section sits inside the closed period parallelogram. -/
lemma periodParallelogramHalfOpenSection_subset
    (L : PeriodPair) (z₀ : ℂ) :
    L.periodParallelogramHalfOpenSection z₀ ⊆ L.periodParallelogram z₀ := by
  intro z hz
  rcases hz with ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
  exact ⟨t₁, t₂, ht₁0, le_of_lt ht₁1, ht₂0, le_of_lt ht₂1, rfl⟩

/-- Helper for Exercise 10: the explicit `Int.fract` representative lands in the half-open period
section and differs from the original point by a lattice vector. -/
lemma exists_mem_periodParallelogramHalfOpenSection_sub_lattice
    (L : PeriodPair) (z z₀ : ℂ) :
    ∃ w : ℂ, w ∈ L.periodParallelogramHalfOpenSection z₀ ∧ w - z ∈ L.lattice := by
  let c : Fin 2 → ℝ := L.basis.equivFun (z - z₀)
  let w : ℂ := z₀ + Int.fract (c 0) • L.ω₁ + Int.fract (c 1) • L.ω₂
  refine ⟨w, ?_, ?_⟩
  · -- The fractional coordinates lie in `[0,1)`, so they define a section representative.
    refine ⟨Int.fract (c 0), Int.fract (c 1), Int.fract_nonneg _, Int.fract_lt_one _,
      Int.fract_nonneg _, Int.fract_lt_one _, rfl⟩
  · -- Subtracting the integer parts of the basis coordinates produces the lattice translation.
    have hcoords : z - z₀ = c 0 * L.ω₁ + c 1 * L.ω₂ := by
      simpa [c, smul_eq_mul] using (L.basis.sum_equivFun (z - z₀)).symm
    have hz' : z = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by
      calc
        z = z₀ + (z - z₀) := by ring
        _ = z₀ + (c 0 * L.ω₁ + c 1 * L.ω₂) := by rw [hcoords]
    have hwz :
        w - z = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
      calc
        w - z =
            (Int.fract (c 0) - c 0) * L.ω₁ + (Int.fract (c 1) - c 1) * L.ω₂ := by
              rw [hz']
              simp [w]
              ring
        _ = (((-⌊c 0⌋ : ℤ) : ℂ) * L.ω₁ + (((-⌊c 1⌋ : ℤ) : ℂ)) * L.ω₂) := by
              have h0 :
                  ((↑(Int.fract (c 0)) : ℂ) - ↑(c 0)) = (((-⌊c 0⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h0r : (c 0 - (⌊c 0⌋ : ℝ)) - c 0 = (-((⌊c 0⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h0r
              have h1 :
                  ((↑(Int.fract (c 1)) : ℂ) - ↑(c 1)) = (((-⌊c 1⌋ : ℤ) : ℂ)) := by
                rw [Int.fract]
                have h1r : (c 1 - (⌊c 1⌋ : ℝ)) - c 1 = (-((⌊c 1⌋ : ℤ) : ℝ)) := by
                  ring
                exact_mod_cast h1r
              rw [h0, h1]
    exact L.mem_lattice.mpr ⟨-⌊c 0⌋, -⌊c 1⌋, hwz.symm⟩

/-- Helper for Exercise 10: a point on the top or right edge of the closed period parallelogram
lies on its frontier. -/
lemma mem_frontier_periodParallelogram_of_coord_eq_one
    (L : PeriodPair) {z₀ : ℂ} {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hedge : u = 1 ∨ v = 1) :
    z₀ + u • L.ω₁ + v • L.ω₂ ∈ frontier (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ ≃ₜ ℂ :=
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀)
  let square : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  have himage : e '' square = L.periodParallelogram z₀ := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hp₁, hp₂⟩
      refine ⟨p.1, p.2, hp₁.1, hp₁.2, hp₂.1, hp₂.2, ?_⟩
      -- Read the image point in period-basis coordinates.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
          z₀ + p.1 • L.ω₁ + p.2 • L.ω₂
      rw [L.basis_pair_homeomorph_apply]
      simp [add_assoc]
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      refine ⟨(t₁, t₂), ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, ?_⟩
      -- The converse direction is the same affine-coordinate expansion.
      change
        z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (t₁, t₂) : ℂ) =
          z₀ + t₁ • L.ω₁ + t₂ • L.ω₂
      rw [L.basis_pair_homeomorph_apply]
      simp [add_assoc]
  have hpfrontier : (u, v) ∈ frontier square := by
    rw [frontier_prod_eq]
    rcases hedge with rfl | rfl
    · -- On the right edge, the first square coordinate is in the frontier of the interval.
      right
      refine ⟨?_, subset_closure ?_⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hu0]
      · exact ⟨hv0, hv1⟩
    · -- On the top edge, the second square coordinate is in the frontier of the interval.
      left
      refine ⟨subset_closure ?_, ?_⟩
      · exact ⟨hu0, hu1⟩
      · rw [frontier_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
        simp [hv0]
  have himage_frontier :
      z₀ + u • L.ω₁ + v • L.ω₂ ∈ e '' frontier square := by
    refine ⟨(u, v), hpfrontier, ?_⟩
    -- Translate the square edge point through the basis homeomorphism.
    change
      z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
        (u, v) : ℂ) =
        z₀ + u • L.ω₁ + v • L.ω₂
    rw [L.basis_pair_homeomorph_apply]
    simp [add_assoc]
  -- The homeomorphism sends the square frontier to the parallelogram frontier.
  have hfrontier_image :
      z₀ + u • L.ω₁ + v • L.ω₂ ∈ frontier (e '' square) := by
    simpa [e.image_frontier] using himage_frontier
  simpa [himage] using hfrontier_image

/-- Helper for Exercise 10: any point of the closed period parallelogram that avoids the frontier
already lies in the half-open section. -/
lemma mem_periodParallelogramHalfOpenSection_of_not_frontier
    (L : PeriodPair) {z₀ z : ℂ}
    (hzP : z ∈ L.periodParallelogram z₀)
    (hzfrontier : z ∉ frontier (L.periodParallelogram z₀)) :
    z ∈ L.periodParallelogramHalfOpenSection z₀ := by
  rcases hzP with ⟨u, v, hu0, hu1, hv0, hv1, hz_eq⟩
  have hu_lt : u < 1 := by
    -- A point with first coordinate `1` would lie on the omitted right edge.
    by_contra hu_not_lt
    have hu_eq : u = 1 := le_antisymm hu1 (le_of_not_gt hu_not_lt)
    exact hzfrontier <|
      by simpa [hz_eq] using
        (L.mem_frontier_periodParallelogram_of_coord_eq_one
          (z₀ := z₀) hu0 hu1 hv0 hv1 (Or.inl hu_eq))
  have hv_lt : v < 1 := by
    -- The same argument excludes the omitted top edge.
    by_contra hv_not_lt
    have hv_eq : v = 1 := le_antisymm hv1 (le_of_not_gt hv_not_lt)
    exact hzfrontier <|
      by simpa [hz_eq] using
        (L.mem_frontier_periodParallelogram_of_coord_eq_one
          (z₀ := z₀) hu0 hu1 hv0 hv1 (Or.inr hv_eq))
  exact ⟨u, v, hu0, hu_lt, hv0, hv_lt, hz_eq⟩

/-- Helper for Exercise 10: the half-open period section is a genuine quotient section for
`ℂ ⧸ L.lattice.toAddSubgroup`. -/
lemma periodParallelogram_half_open_section_bijOn
    (L : PeriodPair) (z₀ : ℂ) :
    Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup)
      (L.periodParallelogramHalfOpenSection z₀) Set.univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Every section point maps to some quotient class.
    intro z hz
    simp
  · intro z hz w hw hzw
    rcases hz with ⟨u₁, v₁, hu₁0, hu₁1, hv₁0, hv₁1, rfl⟩
    rcases hw with ⟨u₂, v₂, hu₂0, hu₂1, hv₂0, hv₂1, rfl⟩
    rw [QuotientAddGroup.eq_iff_sub_mem] at hzw
    obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice hzw
    have hcoord0 :
        L.basis.equivFun
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)) 0 =
          u₁ - u₂ := by
      have hpair :
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) : ℂ) =
            ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
              (u₁ - u₂, v₁ - v₂)) : ℂ) := by
        rw [L.basis_pair_homeomorph_apply]
        calc
          (z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)
              = u₁ • L.ω₁ + v₁ • L.ω₂ - u₂ • L.ω₁ - v₂ • L.ω₂ := by ring
          _ = (u₁ • L.ω₁ - u₂ • L.ω₁) + (v₁ • L.ω₂ - v₂ • L.ω₂) := by abel
          _ = (u₁ - u₂) • L.ω₁ + (v₁ - v₂) • L.ω₂ := by rw [sub_smul, sub_smul]
      rw [hpair]
      change L.basis.equivFun (L.basis.equivFunL.symm ![u₁ - u₂, v₁ - v₂]) 0 = u₁ - u₂
      simpa using L.basis_equivFunL_symm_apply_zero (u₁ - u₂) (v₁ - v₂)
    have hcoord1 :
        L.basis.equivFun
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)) 1 =
          v₁ - v₂ := by
      have hpair :
          ((z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂) : ℂ) =
            ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
              (u₁ - u₂, v₁ - v₂)) : ℂ) := by
        rw [L.basis_pair_homeomorph_apply]
        calc
          (z₀ + u₁ • L.ω₁ + v₁ • L.ω₂) - (z₀ + u₂ • L.ω₁ + v₂ • L.ω₂)
              = u₁ • L.ω₁ + v₁ • L.ω₂ - u₂ • L.ω₁ - v₂ • L.ω₂ := by ring
          _ = (u₁ • L.ω₁ - u₂ • L.ω₁) + (v₁ • L.ω₂ - v₂ • L.ω₂) := by abel
          _ = (u₁ - u₂) • L.ω₁ + (v₁ - v₂) • L.ω₂ := by rw [sub_smul, sub_smul]
      rw [hpair]
      change L.basis.equivFun (L.basis.equivFunL.symm ![u₁ - u₂, v₁ - v₂]) 1 = v₁ - v₂
      simpa using L.basis_equivFunL_symm_apply_one (u₁ - u₂) (v₁ - v₂)
    have hm_eq : (m : ℝ) = u₁ - u₂ := by
      linarith [hm, hcoord0]
    have hn_eq : (n : ℝ) = v₁ - v₂ := by
      linarith [hn, hcoord1]
    have hm_bounds : (-1 : ℝ) < (m : ℝ) ∧ (m : ℝ) < 1 := by
      constructor <;> linarith [hu₁0, hu₁1, hu₂0, hu₂1, hm_eq]
    have hn_bounds : (-1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
      constructor <;> linarith [hv₁0, hv₁1, hv₂0, hv₂1, hn_eq]
    have hm_lower : -1 < m := by
      exact_mod_cast hm_bounds.1
    have hm_upper : m < 1 := by
      exact_mod_cast hm_bounds.2
    have hn_lower : -1 < n := by
      exact_mod_cast hn_bounds.1
    have hn_upper : n < 1 := by
      exact_mod_cast hn_bounds.2
    have hm_zero : m = 0 := by omega
    have hn_zero : n = 0 := by omega
    have hu_eq : u₁ = u₂ := by
      have hm_zero' : (m : ℝ) = 0 := by exact_mod_cast hm_zero
      linarith [hm_eq, hm_zero']
    have hv_eq : v₁ = v₂ := by
      have hn_zero' : (n : ℝ) = 0 := by exact_mod_cast hn_zero
      linarith [hn_eq, hn_zero']
    simp [hu_eq, hv_eq]
  · intro q hq
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q
    rcases L.exists_mem_periodParallelogramHalfOpenSection_sub_lattice z z₀ with ⟨w, hw, hwz⟩
    refine ⟨w, hw, ?_⟩
    -- The section representative differs from the original point by a lattice period.
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simpa using hwz

/-- Helper for Exercise 10: the same zero representative finset can be read on the half-open
section because boundary regularity excludes the omitted edges. -/
lemma closed_periodParallelogram_weighted_zero_sum_transport
    (L : PeriodPair) {g : ℂ → ℂ} (z₀ : ℂ)
    (hg : Meromorphic g)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt g z = (0 : WithTop ℤ))
    (roots : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g (L.periodParallelogram z₀) roots) :
    IsZeroRepresentativeSet g (L.periodParallelogramHalfOpenSection z₀) roots ∧
      (((roots.sum
          fun z ↦ divisor g (L.periodParallelogramHalfOpenSection z₀) z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((roots.sum
          fun z ↦ divisor g (L.periodParallelogram z₀) z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hroots_half : IsZeroRepresentativeSet g (L.periodParallelogramHalfOpenSection z₀) roots := by
    intro z
    constructor
    · intro hz
      obtain ⟨hzP, hzdiv⟩ := (hroots.mem_iff z).1 hz
      have hz_not_frontier : z ∉ frontier (L.periodParallelogram z₀) := by
        intro hzfrontier
        have hdiv_zero : divisor g (L.periodParallelogram z₀) z = 0 := by
          rw [hg.meromorphicOn.divisor_apply hzP, hboundary z hzfrontier, WithTop.untop₀_zero]
        have : ¬ 0 < divisor g (L.periodParallelogram z₀) z := by
          simpa [hdiv_zero]
        exact this hzdiv
      have hzhalf :
          z ∈ L.periodParallelogramHalfOpenSection z₀ :=
        L.mem_periodParallelogramHalfOpenSection_of_not_frontier hzP hz_not_frontier
      have hdiv_eq :
          divisor g (L.periodParallelogramHalfOpenSection z₀) z =
            divisor g (L.periodParallelogram z₀) z := by
        rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
      exact ⟨hzhalf, by simpa [hdiv_eq] using hzdiv⟩
    · intro hz
      have hzhalf : z ∈ L.periodParallelogramHalfOpenSection z₀ := hz.1
      have hzdiv : 0 < divisor g (L.periodParallelogramHalfOpenSection z₀) z := hz.2
      have hzP : z ∈ L.periodParallelogram z₀ :=
        L.periodParallelogramHalfOpenSection_subset z₀ hzhalf
      have hdiv_eq :
          divisor g (L.periodParallelogramHalfOpenSection z₀) z =
            divisor g (L.periodParallelogram z₀) z := by
        rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
      exact (hroots.mem_iff z).2 ⟨hzP, by simpa [hdiv_eq] using hzdiv⟩
  have hdiv_eq_on_roots :
      ∀ z ∈ roots,
        divisor g (L.periodParallelogramHalfOpenSection z₀) z =
          divisor g (L.periodParallelogram z₀) z := by
    intro z hz
    have hzhalf : z ∈ L.periodParallelogramHalfOpenSection z₀ :=
      ((hroots_half.mem_iff z).1 hz).1
    have hzP : z ∈ L.periodParallelogram z₀ :=
      ((hroots.mem_iff z).1 hz).1
    -- On shared support points, both owners read the same meromorphic order.
    rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
  have hsum_eq :
      (roots.sum (fun z ↦ divisor g (L.periodParallelogramHalfOpenSection z₀) z • z) : ℂ) =
        roots.sum (fun z ↦ divisor g (L.periodParallelogram z₀) z • z) := by
    refine Finset.sum_congr rfl ?_
    intro z hz
    rw [hdiv_eq_on_roots z hz]
  refine ⟨hroots_half, ?_⟩
  -- The weighted zero sum is unchanged because every support point and divisor multiplicity agrees.
  exact congrArg (fun x : ℂ => ((x : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) hsum_eq

/-- Helper for Exercise 10: the same pole representative finset can be read on the half-open
section because boundary regularity excludes the omitted edges. -/
lemma closed_periodParallelogram_weighted_pole_sum_transport
    (L : PeriodPair) {g : ℂ → ℂ} (z₀ : ℂ)
    (hg : Meromorphic g)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt g z = (0 : WithTop ℤ))
    (poles : Finset ℂ)
    (hpoles : IsPoleRepresentativeSet g (L.periodParallelogram z₀) poles) :
    IsPoleRepresentativeSet g (L.periodParallelogramHalfOpenSection z₀) poles ∧
      (((poles.sum
          fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₀) z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum
          fun z ↦ (-divisor g (L.periodParallelogram z₀) z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hpoles_half : IsPoleRepresentativeSet g (L.periodParallelogramHalfOpenSection z₀) poles := by
    intro z
    constructor
    · intro hz
      obtain ⟨hzP, hzdiv⟩ := (hpoles.mem_iff z).1 hz
      have hz_not_frontier : z ∉ frontier (L.periodParallelogram z₀) := by
        intro hzfrontier
        have hdiv_zero : divisor g (L.periodParallelogram z₀) z = 0 := by
          rw [hg.meromorphicOn.divisor_apply hzP, hboundary z hzfrontier, WithTop.untop₀_zero]
        exact (not_lt_of_ge (by simpa [hdiv_zero])) hzdiv
      have hzhalf :
          z ∈ L.periodParallelogramHalfOpenSection z₀ :=
        L.mem_periodParallelogramHalfOpenSection_of_not_frontier hzP hz_not_frontier
      have hdiv_eq :
          divisor g (L.periodParallelogramHalfOpenSection z₀) z =
            divisor g (L.periodParallelogram z₀) z := by
        -- On shared support points, both owners read the same meromorphic order.
        rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
      exact ⟨hzhalf, by simpa [hdiv_eq] using hzdiv⟩
    · intro hz
      have hzhalf : z ∈ L.periodParallelogramHalfOpenSection z₀ := hz.1
      have hzdiv : divisor g (L.periodParallelogramHalfOpenSection z₀) z < 0 := hz.2
      have hzP : z ∈ L.periodParallelogram z₀ :=
        L.periodParallelogramHalfOpenSection_subset z₀ hzhalf
      have hdiv_eq :
          divisor g (L.periodParallelogramHalfOpenSection z₀) z =
            divisor g (L.periodParallelogram z₀) z := by
        -- Passing from the half-open owner back to the closed owner does not change local order.
        rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
      exact (hpoles.mem_iff z).2 ⟨hzP, by simpa [hdiv_eq] using hzdiv⟩
  have hdiv_eq_on_poles :
      ∀ z ∈ poles,
        divisor g (L.periodParallelogramHalfOpenSection z₀) z =
          divisor g (L.periodParallelogram z₀) z := by
    intro z hz
    have hzhalf : z ∈ L.periodParallelogramHalfOpenSection z₀ :=
      ((hpoles_half.mem_iff z).1 hz).1
    have hzP : z ∈ L.periodParallelogram z₀ :=
      ((hpoles.mem_iff z).1 hz).1
    -- The divisor multiplicity is owner-independent on a point shared by both sections.
    rw [hg.meromorphicOn.divisor_apply hzhalf, hg.meromorphicOn.divisor_apply hzP]
  have hsum_eq :
      (poles.sum
          (fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₀) z) • z) : ℂ) =
        poles.sum (fun z ↦ (-divisor g (L.periodParallelogram z₀) z) • z) := by
    refine Finset.sum_congr rfl ?_
    intro z hz
    rw [hdiv_eq_on_poles z hz]
  refine ⟨hpoles_half, ?_⟩
  -- The weighted pole sum is unchanged because every pole representative and multiplicity agrees.
  exact congrArg (fun x : ℂ => ((x : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) hsum_eq

/-- Helper for Exercise 10: the unique pole representative can also be read on the half-open
section, and its weighted pole term is unchanged. -/
lemma closed_periodParallelogram_singleton_pole_transport
    (L : PeriodPair) {g : ℂ → ℂ} (z₀ pole : ℂ)
    (hg : Meromorphic g)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt g z = (0 : WithTop ℤ))
    (hpoles :
      IsPoleRepresentativeSet g (L.periodParallelogram z₀) ({pole} : Finset ℂ)) :
    IsPoleRepresentativeSet g (L.periodParallelogramHalfOpenSection z₀) ({pole} : Finset ℂ) ∧
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₀) z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogram z₀) z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  -- Route correction: the singleton case is just the generic pole transport specialized to
  -- `poles = {pole}`.
  simpa using
    (L.closed_periodParallelogram_weighted_pole_sum_transport
      (z₀ := z₀) hg hboundary ({pole} : Finset ℂ) hpoles)

/-- Helper for Exercise 10: every meromorphic function on a compact period parallelogram has a
finite representative set for the support of the positive divisor. -/
lemma exists_zero_representatives_on_periodParallelogram
    (L : PeriodPair) {g : ℂ → ℂ} (z₀ : ℂ) (hg : Meromorphic g) :
    ∃ roots : Finset ℂ, IsZeroRepresentativeSet g (L.periodParallelogram z₀) roots := by
  let D := divisor g (L.periodParallelogram z₀)
  let hfin : Set.Finite (D⁺).support := (D⁺).finiteSupport (L.isCompact_periodParallelogram z₀)
  refine ⟨hfin.toFinset, ?_⟩
  intro z
  constructor
  · intro hz
    have hzsupport : z ∈ (D⁺).support := by
      simpa [hfin] using hz
    have hzP : z ∈ L.periodParallelogram z₀ := (D⁺).supportWithinDomain hzsupport
    have hzpos : 0 < D z := by
      have hzneq : (D z)⁺ ≠ 0 := by
        simpa [D, Function.locallyFinsuppWithin.posPart_apply] using hzsupport
      have hznot : ¬ D z ≤ 0 := by
        intro hzle
        exact hzneq (posPart_eq_zero.2 hzle)
      exact lt_of_not_ge hznot
    exact ⟨hzP, hzpos⟩
  · rintro ⟨hzP, hzpos⟩
    have hzsupport : z ∈ (D⁺).support := by
      change (D z)⁺ ≠ 0
      exact ne_of_gt (by
        simpa [D, Function.locallyFinsuppWithin.posPart_apply] using posPart_pos hzpos)
    simpa [hfin] using hzsupport

/-- Helper for Exercise 10: summing divisor multiplicities over a zero representative set recovers
the total positive divisor mass. -/
lemma IsZeroRepresentativeSet.sum_divisor_eq_finsum_posPart
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) :
    roots.sum (divisor f P) = ∑ᶠ z, (divisor f P)⁺ z := by
  have hsupp :
      Function.support (fun z ↦ (divisor f P z)⁺) ⊆ (↑roots : Set ℂ) := by
    intro z hz
    have hzsupport : z ∈ (divisor f P)⁺.support := by
      simpa [Function.support, Function.locallyFinsuppWithin.posPart_apply] using hz
    have hzP : z ∈ P := ((divisor f P)⁺).supportWithinDomain hzsupport
    have hzpos : 0 < divisor f P z := by
      have hzneq : (divisor f P z)⁺ ≠ 0 := by
        simpa [Function.locallyFinsuppWithin.posPart_apply] using hzsupport
      have hznot : ¬ divisor f P z ≤ 0 := by
        intro hzle
        exact hzneq (posPart_eq_zero.2 hzle)
      exact lt_of_not_ge hznot
    exact (hroots.mem_iff z).2 ⟨hzP, hzpos⟩
  calc
    roots.sum (divisor f P) = roots.sum (fun z ↦ (divisor f P z)⁺) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzpos : 0 < divisor f P z := (hroots.mem_iff z).1 hz |>.2
      exact (posPart_of_nonneg (le_of_lt hzpos)).symm
    _ = ∑ᶠ z, (divisor f P)⁺ z := by
      symm
      exact finsum_eq_sum_of_support_subset _ hsupp

/-- Helper for Exercise 10: if a meromorphic germ has order zero, then its normal-form
representative is analytic at the center. -/
lemma analyticAt_toMeromorphicNFAt_of_meromorphicOrderAt_eq_zero
    {g : ℂ → ℂ} {z : ℂ}
    (hg : MeromorphicAt g z) (horder : meromorphicOrderAt g z = (0 : ℤ)) :
    AnalyticAt ℂ (toMeromorphicNFAt g z) z := by
  have hnf : MeromorphicNFAt (toMeromorphicNFAt g z) z :=
    meromorphicNFAt_toMeromorphicNFAt
  have horder_nf :
      meromorphicOrderAt (toMeromorphicNFAt g z) z = (0 : WithTop ℤ) := by
    -- The normal-form replacement agrees with the original punctured germ, so it keeps the same
    -- meromorphic order.
    calc
      meromorphicOrderAt (toMeromorphicNFAt g z) z = meromorphicOrderAt g z := by
        symm
        exact meromorphicOrderAt_congr hg.eq_nhdsNE_toMeromorphicNFAt
      _ = (0 : WithTop ℤ) := by
        simpa using horder
  -- Once the order is nonnegative for the normal-form germ, normal-form analyticity applies.
  exact (hnf.meromorphicOrderAt_nonneg_iff_analyticAt).1 (by simpa [horder_nf])

/-- Helper for Exercise 10: an off-lattice zero of `℘' - α ℘ - β` forces the corresponding
Weierstrass value to be a root of the source cubic elimination polynomial. -/
lemma weierstrass_linear_form_root_mem_badValues
    (L : PeriodPair) {α β z : ℂ} (hz : z ∉ L.lattice)
    (hzero : ℘'[L] z - α * ℘[L] z - β = 0) :
    let q : Polynomial ℂ :=
      Polynomial.C (4 : ℂ) * Polynomial.X ^ 3 -
        Polynomial.C (α ^ 2) * Polynomial.X ^ 2 -
        Polynomial.C (2 * α * β + L.g₂) * Polynomial.X -
        Polynomial.C (β ^ 2 + L.g₃)
    ℘[L] z ∈ q.roots.toFinset := by
  classical
  let q : Polynomial ℂ :=
    Polynomial.C (4 : ℂ) * Polynomial.X ^ 3 -
      Polynomial.C (α ^ 2) * Polynomial.X ^ 2 -
      Polynomial.C (2 * α * β + L.g₂) * Polynomial.X -
      Polynomial.C (β ^ 2 + L.g₃)
  have hderiv : ℘'[L] z = α * ℘[L] z + β := by
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  have hcubic :
      4 * (℘[L] z) ^ 3 - α ^ 2 * (℘[L] z) ^ 2 -
        (2 * α * β + L.g₂) * ℘[L] z - (β ^ 2 + L.g₃) = 0 := by
    -- Eliminate `℘'` from the Weierstrass differential equation using the assumed zero.
    calc
      4 * (℘[L] z) ^ 3 - α ^ 2 * (℘[L] z) ^ 2 -
          (2 * α * β + L.g₂) * ℘[L] z - (β ^ 2 + L.g₃) =
        4 * (℘[L] z) ^ 3 - (α * ℘[L] z + β) ^ 2 - L.g₂ * ℘[L] z - L.g₃ := by
          ring
      _ = 0 := by
          rw [← hderiv, L.derivWeierstrassP_sq z hz]
          ring
  have hq_eval : q.eval (℘[L] z) = 0 := by
    simp [q, hcubic]
  have hq_ne : q ≠ 0 := by
    intro hq
    have hcoeffCX2 : (Polynomial.C (α ^ 2) * Polynomial.X ^ 2 : Polynomial ℂ).coeff 3 = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
    have hcoeff : q.coeff 3 = (4 : ℂ) := by
      calc
        q.coeff 3 =
            (Polynomial.C (4 : ℂ) * Polynomial.X ^ 3).coeff 3 -
              (Polynomial.C (α ^ 2) * Polynomial.X ^ 2).coeff 3 -
              (Polynomial.C (2 * α * β + L.g₂) * Polynomial.X).coeff 3 -
              (Polynomial.C (β ^ 2 + L.g₃)).coeff 3 := by
                simp [q]
        _ = (4 : ℂ) := by
            rw [Polynomial.coeff_C_mul_X_pow, hcoeffCX2, Polynomial.coeff_C_mul_X,
              Polynomial.coeff_C]
            simp
    have hcoeff_zero : q.coeff 3 = 0 := by
      simpa [hq]
    rw [hcoeff_zero] at hcoeff
    norm_num at hcoeff
  rw [Multiset.mem_toFinset]
  exact (Polynomial.mem_roots hq_ne).2 hq_eval

/-- Helper for Exercise 10: the slanted boundary parameters meeting one off-lattice Weierstrass
fiber already form a countable set. -/
lemma countable_slanted_parameters_of_weierstrass_fiber
    (L : PeriodPair) (x : ℂ) :
    Set.Countable
      {t : ℝ | ∃ z : ℂ,
        z ∉ L.lattice ∧ ℘[L] z = x ∧
          (t = -(L.basis.equivFun z 0) ∨
            t = 1 - L.basis.equivFun z 0 ∨
            t = -2 * L.basis.equivFun z 1 ∨
            t = 2 * (1 - L.basis.equivFun z 1))} := by
  -- Reuse the single-fiber bad-parameter theorem from Proposition 5.2 and drop the lattice branch.
  refine (L.countable_slanted_bad_parameters x).mono ?_
  intro t ht
  rcases ht with ⟨z, hznotL, hzx, hparam⟩
  exact ⟨z, Or.inr ⟨hznotL, hzx⟩, hparam⟩

/-- Helper for Exercise 10: the slanted boundary parameters meeting lattice points alone are
countable. -/
lemma countable_slanted_parameters_of_lattice
    (L : PeriodPair) :
    Set.Countable
      {t : ℝ | ∃ z : ℂ,
        z ∈ L.lattice ∧
          (t = -(L.basis.equivFun z 0) ∨
            t = 1 - L.basis.equivFun z 0 ∨
            t = -2 * L.basis.equivFun z 1 ∨
            t = 2 * (1 - L.basis.equivFun z 1))} := by
  -- This is the lattice-only subfamily of the same countable bad-parameter set.
  refine (L.countable_slanted_bad_parameters 0).mono ?_
  intro t ht
  rcases ht with ⟨z, hzL, hparam⟩
  exact ⟨z, Or.inl hzL, hparam⟩

/-- Helper for Exercise 10: the slanted boundary parameters meeting the lattice or any finite
family of forbidden Weierstrass values form a countable set. -/
lemma countable_slanted_bad_parameters_of_finite_weierstrass_values
    (L : PeriodPair) (S : Finset ℂ) :
    Set.Countable
      {t : ℝ | ∃ z : ℂ,
        (z ∈ L.lattice ∨ z ∉ L.lattice ∧ ℘[L] z ∈ S) ∧
          (t = -(L.basis.equivFun z 0) ∨
            t = 1 - L.basis.equivFun z 0 ∨
            t = -2 * L.basis.equivFun z 1 ∨
            t = 2 * (1 - L.basis.equivFun z 1))} := by
  classical
  -- Build the forbidden-parameter set as the lattice contribution plus one countable fiber set
  -- for each forbidden Weierstrass value.
  induction S using Finset.induction_on with
  | empty =>
      refine (L.countable_slanted_parameters_of_lattice).mono ?_
      intro t ht
      rcases ht with ⟨z, hz, hparam⟩
      rcases hz with hzL | ⟨_, hzmem⟩
      · exact ⟨z, hzL, hparam⟩
      · simpa using hzmem
  | @insert x S hx ih =>
      have hfiber := L.countable_slanted_parameters_of_weierstrass_fiber x
      refine (ih.union hfiber).mono ?_
      intro t ht
      rcases ht with ⟨z, hz, hparam⟩
      rcases hz with hzL | ⟨hznotL, hzmem⟩
      · exact Or.inl ⟨z, Or.inl hzL, hparam⟩
      · rw [Finset.mem_insert] at hzmem
        rcases hzmem with hzx | hzmem
        · exact Or.inr ⟨z, hznotL, hzx, hparam⟩
        · exact Or.inl ⟨z, Or.inr ⟨hznotL, hzmem⟩, hparam⟩

/-- Helper for Exercise 10: one can choose a slanted period parallelogram whose boundary avoids a
finite family of forbidden Weierstrass values, while the only lattice point inside remains `0`. -/
lemma exists_boundary_generic_periodParallelogram_avoiding_finite_weierstrass_values
    (L : PeriodPair) (S : Finset ℂ) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      let z₀ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
      0 ∈ L.periodParallelogram z₀ ∧
        (∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ∉ S) ∧
        (∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) := by
  let badSet : Set ℝ :=
    {t : ℝ | ∃ z : ℂ,
      (z ∈ L.lattice ∨ z ∉ L.lattice ∧ ℘[L] z ∈ S) ∧
        (t = -(L.basis.equivFun z 0) ∨
          t = 1 - L.basis.equivFun z 0 ∨
          t = -2 * L.basis.equivFun z 1 ∨
          t = 2 * (1 - L.basis.equivFun z 1))}
  have hbad : Set.Countable badSet := by
    -- The new source ingredient is only the finite-union countability wrapper.
    simpa [badSet] using L.countable_slanted_bad_parameters_of_finite_weierstrass_values S
  have hdense : Dense (badSetᶜ : Set ℝ) := by
    simpa using (Set.Countable.dense_compl (𝕜 := ℝ) hbad)
  have hunit_nonempty : (Set.Ioo (0 : ℝ) 1).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num
  have hchoice : (Set.Ioo (0 : ℝ) 1 ∩ (badSetᶜ : Set ℝ)).Nonempty :=
    hdense.inter_open_nonempty (Set.Ioo (0 : ℝ) 1) isOpen_Ioo hunit_nonempty
  rcases hchoice with ⟨t, htunit, htbad⟩
  have htbad_not : t ∉ badSet := by
    simpa [Set.mem_compl_iff] using htbad
  have ht0 : 0 < t := htunit.1
  have ht1 : t < 1 := htunit.2
  refine ⟨t, ht0, ht1, ?_⟩
  dsimp
  constructor
  · -- The slanted translate still contains the origin exactly as in Proposition 5.2.
    refine ⟨t, t / 2, le_of_lt ht0, le_of_lt ht1, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · change 0 = -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂ + t • L.ω₁ + (t / 2 : ℝ) • L.ω₂
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (neg_add_cancel ((t : ℝ) • L.ω₁)).symm
  constructor
  · intro z hzfront
    have hparam := L.parameter_eq_of_mem_frontier_slanted_periodParallelogram hzfront
    have hznotL : z ∉ L.lattice := by
      -- A boundary lattice point would put `t` into the forbidden countable set.
      intro hzL
      exact htbad_not ⟨z, ⟨Or.inl hzL, hparam⟩⟩
    refine ⟨hznotL, ?_⟩
    intro hzS
    -- The same excluded-parameter argument rules out the whole finite forbidden value set.
    exact htbad_not ⟨z, ⟨Or.inr ⟨hznotL, hzS⟩, hparam⟩⟩
  · intro z hzP hzL
    obtain ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩ :=
      L.basis_coords_of_mem_slanted_periodParallelogram hzP
    obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice hzL
    have hm_eq : (m : ℝ) = u - t := by
      -- Compare the integer lattice coordinate with the slanted-coordinate expression.
      calc
        (m : ℝ) = L.basis.equivFun z 0 := by simpa using hm.symm
        _ = u - t := hcoord0
    have hn_eq : (n : ℝ) = v - t / 2 := by
      calc
        (n : ℝ) = L.basis.equivFun z 1 := by simpa using hn.symm
        _ = v - t / 2 := hcoord1
    have hm_low : (-1 : ℝ) < (m : ℝ) := by
      linarith [hu0, ht1, hm_eq]
    have hm_high : (m : ℝ) < 1 := by
      linarith [hu1, ht0, hm_eq]
    have hn_low : (-1 : ℝ) < (n : ℝ) := by
      linarith [hv0, ht1, hn_eq]
    have hn_high : (n : ℝ) < 1 := by
      linarith [hv1, ht0, hn_eq]
    have hm_low_int : (-1 : ℤ) < m := by
      exact_mod_cast hm_low
    have hm_high_int : m < 1 := by
      exact_mod_cast hm_high
    have hn_low_int : (-1 : ℤ) < n := by
      exact_mod_cast hn_low
    have hn_high_int : n < 1 := by
      exact_mod_cast hn_high
    have hm_zero : m = 0 := by
      omega
    have hn_zero : n = 0 := by
      omega
    have hzcoord0 : L.basis.equivFun z 0 = 0 := by
      simpa [hm_zero] using hm
    have hzcoord1 : L.basis.equivFun z 1 = 0 := by
      simpa [hn_zero] using hn
    -- Vanishing of both basis coordinates forces the lattice point itself to be the origin.
    apply L.basis.equivFun.injective
    ext i
    fin_cases i
    · simpa [hzcoord0]
    · simpa [hzcoord1]

/-- Helper for Exercise 10: one can choose a slanted period parallelogram whose boundary contains
no zero of `℘' - α ℘ - β`, while the unique pole representative is the origin with multiplicity
`3`. -/
lemma linear_form_boundary_regular_and_singleton_triple_pole
    (L : PeriodPair) (α β : ℂ) :
    ∃ z₀ : ℂ,
      0 ∈ L.periodParallelogram z₀ ∧
      (∀ z ∈ frontier (L.periodParallelogram z₀),
        meromorphicOrderAt (fun z ↦ ℘'[L] z - α * ℘[L] z - β) z = (0 : WithTop ℤ)) ∧
      IsPoleRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        ({0} : Finset ℂ) ∧
      divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β) (L.periodParallelogram z₀) 0 = -3 := by
  classical
  let q : Polynomial ℂ :=
    Polynomial.C (4 : ℂ) * Polynomial.X ^ 3 -
      Polynomial.C (α ^ 2) * Polynomial.X ^ 2 -
      Polynomial.C (2 * α * β + L.g₂) * Polynomial.X -
      Polynomial.C (β ^ 2 + L.g₃)
  let S : Finset ℂ := q.roots.toFinset
  obtain ⟨t, ht0, ht1, hcell⟩ :=
    L.exists_boundary_generic_periodParallelogram_avoiding_finite_weierstrass_values S
  let z₀ : ℂ := -(t : ℝ) • L.ω₁ - (t / 2 : ℝ) • L.ω₂
  have hcell' :
      0 ∈ L.periodParallelogram z₀ ∧
        (∀ z ∈ frontier (L.periodParallelogram z₀), z ∉ L.lattice ∧ ℘[L] z ∉ S) ∧
        (∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) := by
    simpa [z₀] using hcell
  rcases hcell' with ⟨hzero, havoid, hlattice⟩
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hg : Meromorphic g := (L.weierstrass_linear_form_has_period_lattice α β).1
  have hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt g z = (0 : WithTop ℤ) := by
    intro z hzfront
    have hznotL : z ∉ L.lattice := (havoid z hzfront).1
    have hznotS : ℘[L] z ∉ S := (havoid z hzfront).2
    have hanalytic : AnalyticAt ℂ g z := by
      simpa [g] using
        L.analyticAt_weierstrass_linear_form_of_not_mem_lattice (α := α) (β := β) hznotL
    have hnonzero : g z ≠ 0 := by
      intro hgz
      have hroot : ℘[L] z ∈ S := by
        simpa [g, q, S] using
          (L.weierstrass_linear_form_root_mem_badValues (α := α) (β := β) hznotL hgz)
      exact hznotS hroot
    -- The slanted cell excludes the bad Weierstrass values, so the analytic boundary germ has
    -- order zero.
    have horder_zero : analyticOrderAt g z = 0 := by
      rw [hanalytic.analyticOrderAt_eq_zero]
      exact hnonzero
    rw [hanalytic.meromorphicOrderAt_eq, horder_zero]
    simp
  have htriple : divisor g (L.periodParallelogram z₀) 0 = -3 := by
    -- At the origin, the divisor is the source triple pole computed from the regularized germ.
    rw [hg.meromorphicOn.divisor_apply hzero,
      L.meromorphicOrderAt_weierstrass_linear_form_at_zero α β]
    norm_num
  have hpoles : IsPoleRepresentativeSet g (L.periodParallelogram z₀) ({0} : Finset ℂ) := by
    intro z
    constructor
    · intro hz
      simp at hz
      subst hz
      constructor
      · exact hzero
      · simpa [g, htriple]
    · intro hz
      rcases hz with ⟨hzP, hzneg⟩
      by_cases hzL : z ∈ L.lattice
      · -- Any lattice pole inside the cell is the distinguished origin.
        simpa [hlattice z hzP hzL] using hzP
      · -- Off the lattice, analyticity forces the divisor to be nonnegative.
        have hanalytic : AnalyticAt ℂ g z := by
          simpa [g] using
            L.analyticAt_weierstrass_linear_form_of_not_mem_lattice (α := α) (β := β) hzL
        have hnonneg : 0 ≤ divisor g (L.periodParallelogram z₀) z := by
          rw [hg.meromorphicOn.divisor_apply hzP]
          exact WithTop.untop₀_nonneg.2 hanalytic.meromorphicOrderAt_nonneg
        exact False.elim (not_lt_of_ge hnonneg hzneg)
  refine ⟨z₀, hzero, ?_, ?_, htriple⟩
  · intro z hzfront
    simpa [g] using hboundary z hzfront
  · simpa [g] using hpoles

/-- Exercise 10 (1): if the only pole representative of `℘' - α ℘ - β` in the chosen period
parallelogram is a triple pole, then the zero divisor in that parallelogram has total multiplicity
`3`. -/
theorem exercise10_zero_divisor_sum_eq_three
    (L : PeriodPair) (z₀ α β pole : ℂ)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀),
        meromorphicOrderAt (fun z ↦ ℘'[L] z - α * ℘[L] z - β) z = (0 : WithTop ℤ))
    (hpoles :
      IsPoleRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        ({pole} : Finset ℂ))
    (htriple :
      divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β) (L.periodParallelogram z₀) pole = -3) :
    ∑ᶠ z, (divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β) (L.periodParallelogram z₀))⁺ z = 3 := by
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hg : Meromorphic g ∧ HasPeriodLattice L g := by
    -- Proposition III.5.1 applies to the same periodic meromorphic linear form as in the source.
    simpa [g] using L.weierstrass_linear_form_has_period_lattice α β
  obtain ⟨roots, hroots⟩ := L.exists_zero_representatives_on_periodParallelogram z₀ hg.1
  have hsum :=
    zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram
      L z₀ hg.1 hg.2 hboundary roots ({pole} : Finset ℂ) hroots hpoles
  rw [IsZeroRepresentativeSet.sum_divisor_eq_finsum_posPart hroots] at hsum
  calc
    ∑ᶠ z, (divisor g (L.periodParallelogram z₀))⁺ z =
      ({pole} : Finset ℂ).sum (fun z ↦ -divisor g (L.periodParallelogram z₀) z) := by
        simpa [g] using hsum
    _ = 3 := by
        simp [g, htriple]

-- Route correction: keep the theorem-local Proposition III.5.2 copy isolated, and reuse the
-- canonical Chapter III owner for the public weighted Abel relation needed below.
namespace Exercise10Local

/-- Helper for Exercise 10: every finite subset of `ℝ` misses some point of the open unit
interval. -/
lemma exists_point_Ioo_not_mem_finset (s : Finset ℝ) :
    ∃ u : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∉ s := by
  have hs : Set.Countable (↑s : Set ℝ) := s.finite_toSet.countable
  have hdense : Dense ((↑s : Set ℝ)ᶜ) := by
    simpa using (Set.Countable.dense_compl (𝕜 := ℝ) hs)
  have hnonempty : (Set.Ioo (0 : ℝ) 1).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num
  rcases hdense.inter_open_nonempty (Set.Ioo (0 : ℝ) 1) isOpen_Ioo hnonempty with ⟨u, hu, hus⟩
  refine ⟨u, hu, ?_⟩
  simpa [Set.mem_compl_iff] using hus

/-- Helper for Exercise 10: if a translated-boundary point is represented by `w` in the base
period parallelogram, then one of the representative coordinates must equal the chosen shift. -/
lemma representative_coord_eq_shift_of_translated_frontier
    (L : PeriodPair) {u v : ℝ} {z₀ z z₁ w : ℂ}
    (hz₁ : z₁ = z₀ + u • L.ω₁ + v • L.ω₂)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (hz : z ∈ frontier (L.periodParallelogram z₁))
    (hw : w ∈ L.periodParallelogram z₀)
    (hsub : w - z ∈ L.lattice) :
    L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v := by
  obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice hsub
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hcoord0, hcoord1⟩ :=
    L.basis_coords_sub_of_mem_periodParallelogram (z₀ := z₀) hw
  obtain ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, hz_eq, hedge⟩ :=
    L.frontier_periodParallelogram_coord_eq_zero_or_one hz
  have hz_sub_eq : z - z₁ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
    -- The frontier coordinates are the basis coordinates after subtracting the translated basepoint.
    calc
      z - z₁ = t₁ • L.ω₁ + t₂ • L.ω₂ := by
        calc
          z - z₁ = (z₁ + t₁ • L.ω₁ + t₂ • L.ω₂) - z₁ := by rw [hz_eq]
          _ = t₁ • L.ω₁ + t₂ • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![t₁, t₂] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (L.basis_pair_homeomorph_apply (t₁, t₂))
  have hz_coord0 : L.basis.equivFun (z - z₁) 0 = t₁ := by
    -- Read the first frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using L.basis_equivFunL_symm_apply_zero t₁ t₂
  have hz_coord1 : L.basis.equivFun (z - z₁) 1 = t₂ := by
    -- Read the second frontier coordinate from the inverse basis map.
    rw [hz_sub_eq]
    simpa using L.basis_equivFunL_symm_apply_one t₁ t₂
  have hz₁_sub_eq : z₁ - z₀ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
    -- The chosen translation vector has basis coordinates `(u, v)`.
    calc
      z₁ - z₀ = u • L.ω₁ + v • L.ω₂ := by
        calc
          z₁ - z₀ = (z₀ + u • L.ω₁ + v • L.ω₂) - z₀ := by rw [hz₁]
          _ = u • L.ω₁ + v • L.ω₂ := by ring
      _ = (L.basis.equivFunL.symm ![u, v] : ℂ) := by
        symm
        simpa [smul_eq_mul] using (L.basis_pair_homeomorph_apply (u, v))
  have hz₁_coord0 : L.basis.equivFun (z₁ - z₀) 0 = u := by
    -- Read the first coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using L.basis_equivFunL_symm_apply_zero u v
  have hz₁_coord1 : L.basis.equivFun (z₁ - z₀) 1 = v := by
    -- Read the second coordinate of the translation vector.
    rw [hz₁_sub_eq]
    simpa using L.basis_equivFunL_symm_apply_one u v
  have hsum0 : a = m + t₁ + u := by
    -- The first representative coordinate splits into lattice, frontier, and translation parts.
    calc
      a = L.basis.equivFun (w - z₀) 0 := hcoord0.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 0 := by
            congr 1
            ring
      _ =
          L.basis.equivFun (w - z) 0 +
            (L.basis.equivFun (z - z₁) 0 + L.basis.equivFun (z₁ - z₀) 0) := by
            simp
      _ = m + t₁ + u := by
            rw [hm, hz_coord0, hz₁_coord0]
            ring
  have hsum1 : b = n + t₂ + v := by
    -- The second representative coordinate splits in the same way.
    calc
      b = L.basis.equivFun (w - z₀) 1 := hcoord1.symm
      _ = L.basis.equivFun ((w - z) + ((z - z₁) + (z₁ - z₀))) 1 := by
            congr 1
            ring
      _ =
          L.basis.equivFun (w - z) 1 +
            (L.basis.equivFun (z - z₁) 1 + L.basis.equivFun (z₁ - z₀) 1) := by
            simp
      _ = n + t₂ + v := by
            rw [hn, hz_coord1, hz₁_coord1]
            ring
  rcases hedge with ht₁ | ht₁ | ht₂ | ht₂
  · -- On the `t₁ = 0` edge, the first representative coordinate must be the chosen shift `u`.
    left
    have hm_gt_neg_one : (-1 : ℝ) < m := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hm_lt_one : (m : ℝ) < 1 := by
      have hsum0' : a = m + u := by simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hm_gt_neg_one' : (-1 : ℤ) < m := by exact_mod_cast hm_gt_neg_one
    have hm_lt_one' : m < 1 := by exact_mod_cast hm_lt_one
    have hm_zero : m = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + m := by
            have hsum0' : a = m + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hm_zero]
  · -- On the `t₁ = 1` edge, integrality forces the lattice correction to be `-1`.
    left
    have hk_gt_neg_one : (-1 : ℝ) < (m + 1 : ℤ) := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.2, ha0, hsum0']
    have hk_lt_one : (((m + 1 : ℤ) : ℝ)) < 1 := by
      have hsum0' : a = (m + 1 : ℤ) + u := by
        simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
      linarith [hu.1, ha1, hsum0']
    have hk_gt_neg_one' : (-1 : ℤ) < m + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : m + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : m + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 0 = a := hcoord0
      _ = u + ((m + 1 : ℤ) : ℝ) := by
            have hsum0' : a = (m + 1 : ℤ) + u := by
              simpa [ht₁, add_assoc, add_left_comm, add_comm] using hsum0
            linarith
      _ = u := by simp [hk_zero]
  · -- On the `t₂ = 0` edge, the second representative coordinate must be the chosen shift `v`.
    right
    have hn_gt_neg_one : (-1 : ℝ) < n := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hn_lt_one : (n : ℝ) < 1 := by
      have hsum1' : b = n + v := by simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hn_gt_neg_one' : (-1 : ℤ) < n := by exact_mod_cast hn_gt_neg_one
    have hn_lt_one' : n < 1 := by exact_mod_cast hn_lt_one
    have hn_zero : n = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + n := by
            have hsum1' : b = n + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hn_zero]
  · -- On the `t₂ = 1` edge, integrality forces the second lattice correction to be `-1`.
    right
    have hk_gt_neg_one : (-1 : ℝ) < (n + 1 : ℤ) := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.2, hb0, hsum1']
    have hk_lt_one : (((n + 1 : ℤ) : ℝ)) < 1 := by
      have hsum1' : b = (n + 1 : ℤ) + v := by
        simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
      linarith [hv.1, hb1, hsum1']
    have hk_gt_neg_one' : (-1 : ℤ) < n + 1 := by exact_mod_cast hk_gt_neg_one
    have hk_lt_one' : n + 1 < 1 := by exact_mod_cast hk_lt_one
    have hk_zero : n + 1 = 0 := by omega
    calc
      L.basis.equivFun (w - z₀) 1 = b := hcoord1
      _ = v + ((n + 1 : ℤ) : ℝ) := by
            have hsum1' : b = (n + 1 : ℤ) + v := by
              simpa [ht₂, add_assoc, add_left_comm, add_comm] using hsum1
            linarith
      _ = v := by simp [hk_zero]

/-- Helper for Exercise 10: one can choose a translate of the period parallelogram whose two
shift coordinates avoid the finitely many coordinates of a prescribed finite support. -/
lemma period_parallelogram_shift_avoids_finite_boundary_coordinates
    (L : PeriodPair) {z₀ : ℂ} {S : Finset ℂ}
    (hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀) :
    ∃ u v : ℝ, u ∈ Set.Ioo (0 : ℝ) 1 ∧ v ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ s ∈ S, L.basis.equivFun (s - z₀) 0 ≠ u ∧ L.basis.equivFun (s - z₀) 1 ≠ v := by
  classical
  let firstCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 0
  let secondCoords : Finset ℝ := S.image fun s ↦ L.basis.equivFun (s - z₀) 1
  obtain ⟨u, hu, hu_not_mem⟩ := exists_point_Ioo_not_mem_finset firstCoords
  obtain ⟨v, hv, hv_not_mem⟩ := exists_point_Ioo_not_mem_finset secondCoords
  refine ⟨u, v, hu, hv, ?_⟩
  intro s hs
  constructor
  · -- The first shift coordinate was chosen outside the first-coordinate image of `S`.
    intro hs_eq
    exact hu_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩
  · -- The second shift coordinate was chosen outside the second-coordinate image of `S`.
    intro hs_eq
    exact hv_not_mem <| Finset.mem_image.mpr ⟨s, hs, hs_eq⟩

/-- Helper for Exercise 10: a quotient-section bijection supplies a representative in `P` for each
class modulo the period lattice. -/
lemma exists_section_representative_sub_mem_lattice
    (L : PeriodPair) {P : Set ℂ}
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (z : ℂ) :
    ∃ w : ℂ, w ∈ P ∧ w - z ∈ L.lattice := by
  rcases hπ.surjOn (show ((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) ∈ Set.univ by simp) with
    ⟨w, hwP, hwz⟩
  refine ⟨w, hwP, ?_⟩
  -- Equality in the quotient is exactly congruence modulo the period lattice.
  rw [QuotientAddGroup.eq_iff_sub_mem] at hwz
  simpa using hwz

/-- Helper for Exercise 10: translating by a lattice period preserves meromorphic order. -/
lemma meromorphicOrderAt_add_period_eq
    (L : PeriodPair) {g : ℂ → ℂ} (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    meromorphicOrderAt g (z + ω) = meromorphicOrderAt g z := by
  have hcomp :
      meromorphicOrderAt (fun w : ℂ ↦ g (w + ω)) z =
        meromorphicOrderAt g (z + ω) := by
    -- Compose with the translation map `w ↦ w + ω`, whose derivative is `1`.
    simpa [Function.comp] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := g) (g := fun w : ℂ ↦ w + ω) (x := z)
        (show AnalyticAt ℂ (fun w : ℂ ↦ w + ω) z by fun_prop)
        (by simpa using (one_ne_zero : (1 : ℂ) ≠ 0)))
  have hcongr :
      meromorphicOrderAt (fun w : ℂ ↦ g (w + ω)) z = meromorphicOrderAt g z := by
    -- On every punctured neighborhood, periodicity identifies the translated germ with `g`.
    apply meromorphicOrderAt_congr
    filter_upwards [Filter.Eventually.of_forall (fun w : ℂ ↦ hperiods ω hω w)] with w hw
    simpa using hw
  exact hcomp.symm.trans hcongr

/-- Helper for Exercise 10: divisor values agree for points differing by a lattice period, even
when they are read on different representative sections. -/
lemma divisor_eq_of_sub_mem_period_lattice
    (L : PeriodPair) {P Q : Set ℂ} {g : ℂ → ℂ} {z z' : ℂ}
    (hg : Meromorphic g) (hperiods : HasPeriodLattice L g)
    (hzP : z ∈ P) (hz'Q : z' ∈ Q) (hsub : z' - z ∈ L.lattice) :
    divisor g Q z' = divisor g P z := by
  -- Read both divisor values as local orders, then translate the germ by the period `z' - z`.
  rw [hg.meromorphicOn.divisor_apply hz'Q, hg.meromorphicOn.divisor_apply hzP]
  exact congrArg (fun w : WithTop ℤ ↦ w.untop₀) <| by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (meromorphicOrderAt_add_period_eq L hperiods (z := z) (ω := z' - z) hsub)

/-- Helper for Exercise 10: if two section representatives differ by a lattice period, then their
weighted divisor classes agree modulo the period lattice. -/
lemma divisor_weighted_eq_mod_period_lattice_of_sub_mem
    (L : PeriodPair) {P Q : Set ℂ} {g : ℂ → ℂ} {z z' : ℂ}
    (hg : Meromorphic g) (hperiods : HasPeriodLattice L g)
    (hzP : z ∈ P) (hz'Q : z' ∈ Q) (hsub : z' - z ∈ L.lattice) :
    (((divisor g Q z' • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
      (((divisor g P z • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hdiv :
      divisor g Q z' = divisor g P z :=
    divisor_eq_of_sub_mem_period_lattice L (P := P) (Q := Q) (g := g)
      hg hperiods hzP hz'Q hsub
  -- First align the multiplicity, then transport the point itself through the quotient section.
  calc
    (((divisor g Q z' • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
      (((divisor g P z • z' : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
        simp [hdiv]
    _ = (((divisor g P z • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa [sub_eq_add_neg, smul_sub] using L.lattice.smul_mem (divisor g P z) hsub

/-- Helper for Exercise 10: if one point has infinite meromorphic order, then every divisor value
on a quotient section vanishes and the weighted Abel relation is trivial. -/
lemma periodic_meromorphic_order_top_trivializes_weighted_divisor_sum
    (L : PeriodPair) {P : Set ℂ} {g : ℂ → ℂ}
    (hg : Meromorphic g)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (htop : ∃ z, meromorphicOrderAt g z = ⊤) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  have hnone_finite : ¬ ∃ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ := by
    intro hfinite
    have hforall_top :
        ∀ u : Set.univ, meromorphicOrderAt g u.1 ≠ ⊤ :=
      (hg.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1 hfinite
    rcases htop with ⟨z, hz⟩
    exact hforall_top ⟨z, by simp⟩ hz
  have htop_all : ∀ z : ℂ, meromorphicOrderAt g z = ⊤ := by
    intro z
    by_contra hz
    exact hnone_finite ⟨⟨z, by simp⟩, hz⟩
  have hroots_empty : roots = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hroots.mem_iff z).1 hz with ⟨hzP, hzpos⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ 0 < divisor g P z by simpa [hdiv]) hzpos
  have hpoles_empty : poles = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro z hz
    rcases (hpoles.mem_iff z).1 hz with ⟨hzP, hzneg⟩
    have hdiv : divisor g P z = 0 := by
      rw [hg.meromorphicOn.divisor_apply hzP, htop_all z]
      simp
    exact (show ¬ divisor g P z < 0 by simpa [hdiv]) hzneg
  -- Once both representative finsets are empty, the quotient-valued sums are both zero.
  simp [hroots_empty, hpoles_empty]

/-- Helper for Exercise 10: in the finite-order branch, one can translate the period
parallelogram so that its boundary avoids every zero and pole represented by the fixed section
`P`. -/
lemma exists_boundary_regular_translate_for_finite_order_support
    (L : PeriodPair) {P : Set ℂ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    ∃ z₁ : ℂ, ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ) := by
  -- Route correction: choose the translated period cell before any contour argument, so the
  -- eventual weighted identity sees no divisor support on the boundary.
  let S : Finset ℂ := roots ∪ poles
  have hS : (↑S : Set ℂ) ⊆ L.periodParallelogram z₀ := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hP ((hroots.mem_iff z).1 hz).1
    · exact hP ((hpoles.mem_iff z).1 hz).1
  obtain ⟨u, v, hu, hv, havoid⟩ :=
    period_parallelogram_shift_avoids_finite_boundary_coordinates L (z₀ := z₀) hS
  let z₁ : ℂ := z₀ + u • L.ω₁ + v • L.ω₂
  refine ⟨z₁, ?_⟩
  intro z hz
  by_contra hz_ne_zero
  obtain ⟨w, hwP, hwsub⟩ :=
    exists_section_representative_sub_mem_lattice L (P := P) hπ z
  have hwPar : w ∈ L.periodParallelogram z₀ := hP hwP
  have hcoord :
      L.basis.equivFun (w - z₀) 0 = u ∨ L.basis.equivFun (w - z₀) 1 = v :=
    representative_coord_eq_shift_of_translated_frontier L
      (z₀ := z₀) (z₁ := z₁) (z := z) (w := w) rfl hu hv hz hwPar hwsub
  have horder_w :
      meromorphicOrderAt g w = meromorphicOrderAt g z := by
    -- Transport the boundary order back to the chosen section representative.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (meromorphicOrderAt_add_period_eq L hperiods (z := z) (ω := w - z) hwsub)
  have hdiv_ne_zero : divisor g P w ≠ 0 := by
    intro hdiv_zero
    have horder_zero_or_top :
        meromorphicOrderAt g w = (0 : WithTop ℤ) ∨ meromorphicOrderAt g w = ⊤ := by
      have horder_untop_zero : (meromorphicOrderAt g w).untop₀ = 0 := by
        simpa [hg.meromorphicOn.divisor_apply hwP] using hdiv_zero
      exact WithTop.untop₀_eq_zero.mp horder_untop_zero
    rcases horder_zero_or_top with horder_zero | horder_top
    · exact hz_ne_zero (by simpa [horder_w] using horder_zero)
    · exact hfinite w horder_top
  have hw_mem_support : w ∈ S := by
    -- A nonzero finite divisor at the section representative forces membership in `roots ∪ poles`.
    rcases lt_or_gt_of_ne hdiv_ne_zero with hdiv_neg | hdiv_pos
    · exact Finset.mem_union.mpr <| Or.inr ((hpoles.mem_iff w).2 ⟨hwP, hdiv_neg⟩)
    · exact Finset.mem_union.mpr <| Or.inl ((hroots.mem_iff w).2 ⟨hwP, hdiv_pos⟩)
  have havoid_w := havoid w hw_mem_support
  rcases hcoord with hcoord0 | hcoord1
  · exact havoid_w.1 hcoord0
  · exact havoid_w.2 hcoord1

/-- Helper for Exercise 10: transporting zero representatives between two quotient sections
preserves the weighted divisor sum modulo the period lattice. -/
lemma exists_zero_representatives_on_section_with_same_weighted_sum
    (L : PeriodPair) {P Q : Set ℂ} {g : ℂ → ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hπP : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (hπQ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) Q Set.univ)
    (rootsP : Finset ℂ)
    (hrootsP : IsZeroRepresentativeSet g P rootsP) :
    ∃ rootsQ : Finset ℂ,
      IsZeroRepresentativeSet g Q rootsQ ∧
        (((rootsQ.sum fun z ↦ divisor g Q z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        (((rootsP.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := by
  classical
  let repQ : ℂ → ℂ := fun z ↦
    Classical.choose (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)
  have hrepQ_mem : ∀ z : ℂ, repQ z ∈ Q := by
    intro z
    exact (Classical.choose_spec
      (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)).1
  have hrepQ_sub : ∀ z : ℂ, repQ z - z ∈ L.lattice := by
    intro z
    exact (Classical.choose_spec
      (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)).2
  have hrepQ_inj : Set.InjOn repQ (↑rootsP : Set ℂ) := by
    intro z hz w hw hEq
    have hzP : z ∈ P := (hrootsP.mem_iff z).1 hz |>.1
    have hwP : w ∈ P := (hrootsP.mem_iff w).1 hw |>.1
    have hzClass :
        (((repQ z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      simpa using hrepQ_sub z
    have hwClass :
        (((repQ w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      simpa using hrepQ_sub w
    have hrepEq :
        (((repQ z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((repQ w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      simpa [hEq]
    have hclass :
        (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      exact hzClass.symm.trans (hrepEq.trans hwClass)
    exact hπP.injOn hzP hwP hclass
  let rootsQ : Finset ℂ := rootsP.image repQ
  have hrootsQ : IsZeroRepresentativeSet g Q rootsQ := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
      have hrP : r ∈ P := (hrootsP.mem_iff r).1 hr |>.1
      have hrdiv : 0 < divisor g P r := (hrootsP.mem_iff r).1 hr |>.2
      have hdiv :
          divisor g Q (repQ r) = divisor g P r :=
        divisor_eq_of_sub_mem_period_lattice (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hrP (hrepQ_mem r) (hrepQ_sub r)
      -- The transported representative stays in `Q`, and periodicity preserves its divisor sign.
      exact ⟨hrepQ_mem r, by simpa [hdiv] using hrdiv⟩
    · rintro ⟨hzQ, hzdiv⟩
      obtain ⟨r, hrP, hrsub⟩ :=
        exists_section_representative_sub_mem_lattice L (P := P) hπP z
      have hzsub : z - r ∈ L.lattice := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using neg_mem hrsub
      have hdiv :
          divisor g Q z = divisor g P r :=
        divisor_eq_of_sub_mem_period_lattice (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hrP hzQ hzsub
      have hr : r ∈ rootsP := by
        exact (hrootsP.mem_iff r).2 ⟨hrP, by simpa [hdiv] using hzdiv⟩
      have hrepClass :
          (((repQ r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrepQ_sub r
      have hrClass :
          (((r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrsub
      have hrepEq : repQ r = z := hπQ.injOn (hrepQ_mem r) hzQ (hrepClass.trans hrClass)
      -- Surjectivity of the section map recovers the transported zero representative.
      exact Finset.mem_image.mpr ⟨r, hr, hrepEq⟩
  have hsumImage :
      (rootsQ.sum fun z ↦
        ((((divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
        rootsP.sum fun z ↦
          ((((divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
    simpa [rootsQ] using
      (Finset.sum_image
        (s := rootsP)
        (g := repQ)
        (f := fun z ↦
          ((((divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup))
        hrepQ_inj)
  have hterm :
      ∀ z ∈ rootsP,
        ((((divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        ((((divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
    intro z hz
    have hzP : z ∈ P := (hrootsP.mem_iff z).1 hz |>.1
    -- The weighted divisor class only depends on the lattice class of the representative.
    exact divisor_weighted_eq_mod_period_lattice_of_sub_mem (L := L)
      (P := P) (Q := Q) (g := g) hg hperiods hzP (hrepQ_mem z) (hrepQ_sub z)
  refine ⟨rootsQ, hrootsQ, ?_⟩
  -- Route correction: transport the theorem first through quotient-section bijections, so the
  -- remaining analytic work stays entirely on the canonical translated section.
  calc
    (((rootsQ.sum fun z ↦ divisor g Q z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      rootsQ.sum fun z ↦
        ((((divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp
    _ =
      rootsP.sum fun z ↦
        ((((divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := hsumImage
    _ =
      rootsP.sum fun z ↦
        ((((divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          exact hterm z hz
    _ =
      (((rootsP.sum fun z ↦ divisor g P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp

/-- Helper for Exercise 10: transporting pole representatives between two quotient sections
preserves the weighted pole sum modulo the period lattice. -/
lemma exists_pole_representatives_on_section_with_same_weighted_sum
    (L : PeriodPair) {P Q : Set ℂ} {g : ℂ → ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hπP : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (hπQ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) Q Set.univ)
    (polesP : Finset ℂ)
    (hpolesP : IsPoleRepresentativeSet g P polesP) :
    ∃ polesQ : Finset ℂ,
      IsPoleRepresentativeSet g Q polesQ ∧
        (((polesQ.sum fun z ↦ (-divisor g Q z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        (((polesP.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := by
  classical
  let repQ : ℂ → ℂ := fun z ↦
    Classical.choose (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)
  have hrepQ_mem : ∀ z : ℂ, repQ z ∈ Q := by
    intro z
    exact (Classical.choose_spec
      (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)).1
  have hrepQ_sub : ∀ z : ℂ, repQ z - z ∈ L.lattice := by
    intro z
    exact (Classical.choose_spec
      (exists_section_representative_sub_mem_lattice L (P := Q) hπQ z)).2
  have hrepQ_inj : Set.InjOn repQ (↑polesP : Set ℂ) := by
    intro z hz w hw hEq
    have hzP : z ∈ P := (hpolesP.mem_iff z).1 hz |>.1
    have hwP : w ∈ P := (hpolesP.mem_iff w).1 hw |>.1
    have hzClass :
        (((repQ z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      simpa using hrepQ_sub z
    have hwClass :
        (((repQ w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      rw [QuotientAddGroup.eq_iff_sub_mem]
      simpa using hrepQ_sub w
    have hrepEq :
        (((repQ z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((repQ w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      simpa [hEq]
    have hclass :
        (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
      exact hzClass.symm.trans (hrepEq.trans hwClass)
    exact hπP.injOn hzP hwP hclass
  let polesQ : Finset ℂ := polesP.image repQ
  have hpolesQ : IsPoleRepresentativeSet g Q polesQ := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
      have hrP : r ∈ P := (hpolesP.mem_iff r).1 hr |>.1
      have hrdiv : divisor g P r < 0 := (hpolesP.mem_iff r).1 hr |>.2
      have hdiv :
          divisor g Q (repQ r) = divisor g P r :=
        divisor_eq_of_sub_mem_period_lattice (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hrP (hrepQ_mem r) (hrepQ_sub r)
      -- Pole multiplicities transport through the chosen quotient representative.
      exact ⟨hrepQ_mem r, by simpa [hdiv] using hrdiv⟩
    · rintro ⟨hzQ, hzdiv⟩
      obtain ⟨r, hrP, hrsub⟩ :=
        exists_section_representative_sub_mem_lattice L (P := P) hπP z
      have hzsub : z - r ∈ L.lattice := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using neg_mem hrsub
      have hdiv :
          divisor g Q z = divisor g P r :=
        divisor_eq_of_sub_mem_period_lattice (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hrP hzQ hzsub
      have hr : r ∈ polesP := by
        exact (hpolesP.mem_iff r).2 ⟨hrP, by simpa [hdiv] using hzdiv⟩
      have hrepClass :
          (((repQ r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrepQ_sub r
      have hrClass :
          (((r : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrsub
      have hrepEq : repQ r = z := hπQ.injOn (hrepQ_mem r) hzQ (hrepClass.trans hrClass)
      -- Surjectivity of the target section recovers the transported pole representative.
      exact Finset.mem_image.mpr ⟨r, hr, hrepEq⟩
  have hsumImage :
      (polesQ.sum fun z ↦
        ((((-divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
        polesP.sum fun z ↦
          ((((-divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
            ℂ ⧸ L.lattice.toAddSubgroup) := by
    simpa [polesQ] using
      (Finset.sum_image
        (s := polesP)
        (g := repQ)
        (f := fun z ↦
          ((((-divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup))
        hrepQ_inj)
  have hterm :
      ∀ z ∈ polesP,
        ((((-divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        ((((-divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
    intro z hz
    have hzP : z ∈ P := (hpolesP.mem_iff z).1 hz |>.1
    -- The same quotient transport works for the pole-weighted classes.
    exact by
      simpa [neg_smul] using
        (divisor_weighted_eq_mod_period_lattice_of_sub_mem (L := L)
          (P := P) (Q := Q) (g := g) hg hperiods hzP (hrepQ_mem z) (hrepQ_sub z))
  refine ⟨polesQ, hpolesQ, ?_⟩
  -- Transport the weighted pole sum to the canonical section before the contour computation.
  calc
    (((polesQ.sum fun z ↦ (-divisor g Q z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      polesQ.sum fun z ↦
        ((((-divisor g Q z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp
    _ =
      polesP.sum fun z ↦
        ((((-divisor g Q (repQ z)) • repQ z : ℂ) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := hsumImage
    _ =
      polesP.sum fun z ↦
        ((((-divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          exact hterm z hz
    _ =
      (((polesP.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp

/-- Helper for Exercise 10: boundary regularity lets the same zero representative finset be read
on the closed translated period parallelogram. -/
lemma zero_representatives_half_open_to_closed_periodParallelogram
    (L : PeriodPair) {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ))
    (roots : Finset ℂ)
    (hroots :
      IsZeroRepresentativeSet g (L.periodParallelogramHalfOpenSection z₁) roots) :
    IsZeroRepresentativeSet g (L.periodParallelogram z₁) roots := by
  intro z
  constructor
  · intro hz
    obtain ⟨hzhalf, hzdiv⟩ := (hroots.mem_iff z).1 hz
    have hzclosed : z ∈ L.periodParallelogram z₁ :=
      L.periodParallelogramHalfOpenSection_subset z₁ hzhalf
    have hdiv_eq :
        divisor g (L.periodParallelogram z₁) z =
          divisor g (L.periodParallelogramHalfOpenSection z₁) z := by
      -- On points shared by both owners, the divisor is the same local meromorphic order.
      rw [hg.meromorphicOn.divisor_apply hzclosed, hg.meromorphicOn.divisor_apply hzhalf]
    exact ⟨hzclosed, by simpa [hdiv_eq] using hzdiv⟩
  · rintro ⟨hzclosed, hzdiv⟩
    have hz_not_frontier : z ∉ frontier (L.periodParallelogram z₁) := by
      intro hzfrontier
      have hdiv_zero : divisor g (L.periodParallelogram z₁) z = 0 := by
        rw [hg.meromorphicOn.divisor_apply hzclosed, hboundary z hzfrontier, WithTop.untop₀_zero]
      exact (show ¬ 0 < divisor g (L.periodParallelogram z₁) z by simpa [hdiv_zero]) hzdiv
    have hzhalf :
        z ∈ L.periodParallelogramHalfOpenSection z₁ :=
      L.mem_periodParallelogramHalfOpenSection_of_not_frontier hzclosed hz_not_frontier
    have hdiv_eq :
        divisor g (L.periodParallelogram z₁) z =
          divisor g (L.periodParallelogramHalfOpenSection z₁) z := by
      -- Boundary regularity excludes the omitted edges, so the half-open owner sees the same germ.
      rw [hg.meromorphicOn.divisor_apply hzclosed, hg.meromorphicOn.divisor_apply hzhalf]
    exact (hroots.mem_iff z).2 ⟨hzhalf, by simpa [← hdiv_eq] using hzdiv⟩

/-- Helper for Exercise 10: boundary regularity lets the same pole representative finset be read
on the closed translated period parallelogram. -/
lemma pole_representatives_half_open_to_closed_periodParallelogram
    (L : PeriodPair) {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ))
    (poles : Finset ℂ)
    (hpoles :
      IsPoleRepresentativeSet g (L.periodParallelogramHalfOpenSection z₁) poles) :
    IsPoleRepresentativeSet g (L.periodParallelogram z₁) poles := by
  intro z
  constructor
  · intro hz
    obtain ⟨hzhalf, hzdiv⟩ := (hpoles.mem_iff z).1 hz
    have hzclosed : z ∈ L.periodParallelogram z₁ :=
      L.periodParallelogramHalfOpenSection_subset z₁ hzhalf
    have hdiv_eq :
        divisor g (L.periodParallelogram z₁) z =
          divisor g (L.periodParallelogramHalfOpenSection z₁) z := by
      -- On points shared by both owners, the divisor is the same local meromorphic order.
      rw [hg.meromorphicOn.divisor_apply hzclosed, hg.meromorphicOn.divisor_apply hzhalf]
    exact ⟨hzclosed, by simpa [hdiv_eq] using hzdiv⟩
  · rintro ⟨hzclosed, hzdiv⟩
    have hz_not_frontier : z ∉ frontier (L.periodParallelogram z₁) := by
      intro hzfrontier
      have hdiv_zero : divisor g (L.periodParallelogram z₁) z = 0 := by
        rw [hg.meromorphicOn.divisor_apply hzclosed, hboundary z hzfrontier, WithTop.untop₀_zero]
      exact (show ¬ divisor g (L.periodParallelogram z₁) z < 0 by simpa [hdiv_zero]) hzdiv
    have hzhalf :
        z ∈ L.periodParallelogramHalfOpenSection z₁ :=
      L.mem_periodParallelogramHalfOpenSection_of_not_frontier hzclosed hz_not_frontier
    have hdiv_eq :
        divisor g (L.periodParallelogram z₁) z =
          divisor g (L.periodParallelogramHalfOpenSection z₁) z := by
      -- Boundary regularity excludes the omitted edges, so the half-open owner sees the same germ.
      rw [hg.meromorphicOn.divisor_apply hzclosed, hg.meromorphicOn.divisor_apply hzhalf]
    exact (hpoles.mem_iff z).2 ⟨hzhalf, by simpa [← hdiv_eq] using hzdiv⟩

/-- Helper for Exercise 10: the only remaining source-faithful analytic input is the weighted
Abel relation on the canonical translated half-open section. -/
lemma weighted_divisor_sum_mod_period_lattice_eq_zero_on_translated_half_open_section
    (L : PeriodPair) {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (roots poles : Finset ℂ)
    (hroots :
      IsZeroRepresentativeSet g (L.periodParallelogramHalfOpenSection z₁) roots)
    (hpoles :
      IsPoleRepresentativeSet g (L.periodParallelogramHalfOpenSection z₁) poles)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    (((roots.sum fun z ↦ divisor g (L.periodParallelogramHalfOpenSection z₁) z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₁) z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  -- Route correction: this local theorem now delegates to the canonical Chapter III Abel
  -- relation on the genuine quotient section, so the unfinished local contour clone is bypassed.
  simpa using
    (sum_divisor_weighted_mod_period_lattice_eq_zero
      (L := L)
      (P := L.periodParallelogramHalfOpenSection z₁) (g := g) (z₀ := z₁)
      hg hperiods
      (L.periodParallelogramHalfOpenSection_subset z₁)
      (L.periodParallelogram_half_open_section_bijOn z₁)
      roots poles hroots hpoles)

/-- Helper for Exercise 10: on a boundary-generic translated period parallelogram, the source
four-edge contour computation yields the weighted divisor identity modulo the period lattice. -/
lemma weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate
    (L : PeriodPair) {P : Set ℂ} {g : ℂ → ℂ} {z₀ z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  let H := L.periodParallelogramHalfOpenSection z₁
  obtain ⟨rootsH, hrootsH, hrootsTransport⟩ :=
    exists_zero_representatives_on_section_with_same_weighted_sum L
      (P := P) (Q := H) hg hperiods hπ (L.periodParallelogram_half_open_section_bijOn z₁)
      roots hroots
  obtain ⟨polesH, hpolesH, hpolesTransport⟩ :=
    exists_pole_representatives_on_section_with_same_weighted_sum L
      (P := P) (Q := H) hg hperiods hπ (L.periodParallelogram_half_open_section_bijOn z₁)
      poles hpoles
  -- Route correction: move all quotient-section transport out of the contour argument, so the
  -- only analytic blocker is the canonical translated half-open section.
  calc
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((rootsH.sum fun z ↦ divisor g H z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simpa [H] using hrootsTransport.symm
    _ =
      (((polesH.sum fun z ↦ (-divisor g H z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simpa [H] using
            (weighted_divisor_sum_mod_period_lattice_eq_zero_on_translated_half_open_section L
              (g := g) (z₁ := z₁) hg hperiods rootsH polesH hrootsH hpolesH hboundary)
    _ =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simpa [H] using hpolesTransport

/-- Helper for Exercise 10: on any quotient section inside a period parallelogram, Proposition
III.5.2 should identify the weighted zero sum of a periodic meromorphic function with the weighted
pole sum. -/
lemma sum_divisor_weighted_mod_period_lattice_eq_zero
    (L : PeriodPair) {P : Set ℂ} {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hP : P ⊆ L.periodParallelogram z₀)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles) :
    (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  by_cases htop : ∃ z, meromorphicOrderAt g z = ⊤
  · -- The degenerate branch already collapses to the trivial empty-divisor identity.
    exact periodic_meromorphic_order_top_trivializes_weighted_divisor_sum L
      (P := P) hg roots poles hroots hpoles htop
  · -- Route correction: after removing the `⊤` branch, the remaining source-faithful proof is the
    -- translated boundary-generic contour computation.
    have hfinite : ∀ z, meromorphicOrderAt g z ≠ ⊤ := by
      intro z hz
      exact htop ⟨z, hz⟩
    obtain ⟨z₁, hboundary⟩ :=
      exists_boundary_regular_translate_for_finite_order_support L
        (P := P) hg hperiods hfinite hP hπ roots poles hroots hpoles
    exact weighted_divisor_sum_mod_period_lattice_eq_zero_of_boundary_generic_translate L
      (P := P) (z₀ := z₀) (z₁ := z₁) hg hperiods hP hπ roots poles hroots hpoles hboundary

end Exercise10Local

/-- Helper for Exercise 10: on the half-open quotient section, Proposition III.5.2 directly
identifies the weighted zero sum of `℘' - α ℘ - β` with the weighted pole sum. -/
lemma linear_form_weighted_zero_sum_eq_pole_sum_on_half_open_section
    (L : PeriodPair) (z₀ α β pole : ℂ)
    (roots : Finset ℂ)
    (hroots :
      IsZeroRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogramHalfOpenSection z₀)
        roots)
    (hpoles :
      IsPoleRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogramHalfOpenSection z₀)
        ({pole} : Finset ℂ)) :
    (((roots.sum
        fun z ↦ divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
          (L.periodParallelogramHalfOpenSection z₀) z • z) :
      ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
            (L.periodParallelogramHalfOpenSection z₀) z) • z : ℂ) :
        ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hg : Meromorphic g ∧ HasPeriodLattice L g := by
    -- The linear form inherits both meromorphicity and lattice-periodicity from `℘` and `℘'`.
    simpa [g] using L.weierstrass_linear_form_has_period_lattice α β
  -- Route correction: downstream Exercise 10 should specialize the canonical Chapter III Abel
  -- relation directly on the half-open section, rather than depending on the local contour clone.
  simpa [g] using
    (sum_divisor_weighted_mod_period_lattice_eq_zero
      (L := L)
      (P := L.periodParallelogramHalfOpenSection z₀) (g := g) (z₀ := z₀)
      hg.1 hg.2
      (L.periodParallelogramHalfOpenSection_subset z₀)
      (L.periodParallelogram_half_open_section_bijOn z₀)
      roots ({pole} : Finset ℂ) hroots hpoles)

/-- Exercise 10 (2): under the same pole hypothesis, every chosen representative set of zeros of
`℘' - α ℘ - β` has divisor-weighted sum congruent to `0` modulo the period lattice, so that sum
is a period. -/
theorem exercise10_zero_weighted_sum_eq_zero_mod_period_lattice
    (L : PeriodPair) (z₀ α β pole : ℂ)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀),
        meromorphicOrderAt (fun z ↦ ℘'[L] z - α * ℘[L] z - β) z = (0 : WithTop ℤ))
    (hpoles :
      IsPoleRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        ({pole} : Finset ℂ))
    (htriple :
      divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β) (L.periodParallelogram z₀) pole = -3)
    (roots : Finset ℂ)
    (hroots :
      IsZeroRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        roots) :
    (((roots.sum
        fun z ↦ divisor (fun z ↦ ℘'[L] z - α * ℘[L] z - β) (L.periodParallelogram z₀) z • z) :
      ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hg : Meromorphic g ∧ HasPeriodLattice L g := by
    -- The affine linear form is the meromorphic periodic function to which Proposition III.5.2
    -- should be applied on a genuine quotient section.
    simpa [g] using L.weierstrass_linear_form_has_period_lattice α β
  have hroots_transport :=
    L.closed_periodParallelogram_weighted_zero_sum_transport z₀ hg.1 hboundary roots hroots
  have hpoles_transport :=
    L.closed_periodParallelogram_singleton_pole_transport z₀ pole hg.1 hboundary hpoles
  have hpole_mem : pole ∈ L.lattice :=
    L.pole_representative_mem_lattice_of_linear_form z₀ α β pole hpoles
  have hpole_class :
      (((((-divisor g (L.periodParallelogram z₀) pole) • pole : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup)) = 0 := by
    -- Once the pole representative is a lattice point, its weighted class already vanishes.
    simpa using
      (L.divisor_weighted_class_eq_zero_of_mem_lattice
        (n := -divisor g (L.periodParallelogram z₀) pole) hpole_mem)
  have hpole_sum_class :
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogram z₀) z) • z : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    -- The singleton pole finset contributes exactly that same weighted lattice class.
    simpa using hpole_class
  have hhalf_section :
      (((roots.sum
          fun z ↦ divisor g (L.periodParallelogramHalfOpenSection z₀) z • z) :
        ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₀) z) • z : ℂ) :
        ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
    -- The half-open section is the genuine quotient section where Proposition III.5.2 applies.
    simpa [g] using
      L.linear_form_weighted_zero_sum_eq_pole_sum_on_half_open_section
        z₀ α β pole roots hroots_transport.1 hpoles_transport.1
  -- The source route now closes by transporting the closed-owner sums to the quotient section,
  -- applying the Abel relation there, and transporting the singleton pole back.
  calc
    (((roots.sum fun z ↦ divisor g (L.periodParallelogram z₀) z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((roots.sum fun z ↦ divisor g (L.periodParallelogramHalfOpenSection z₀) z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          exact hroots_transport.2.symm
    _ =
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogramHalfOpenSection z₀) z) • z : ℂ) :
        ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := hhalf_section
    _ =
      (((({pole} : Finset ℂ).sum
          fun z ↦ (-divisor g (L.periodParallelogram z₀) z) • z : ℂ) :
        ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := hpoles_transport.2
    _ = 0 := hpole_sum_class

-- Exercise 10 (3): if `u`, `v`, and `-u-v` avoid the period lattice and `u` is not congruent to
-- `±v` modulo the lattice, then one can choose `α` and `β` so that `℘' - α ℘ - β` vanishes at
-- `u`, `v`, and `-u-v`.
/-- Helper for Exercise 10: if two non-lattice points are neither congruent nor opposite modulo
the period lattice, then their Weierstrass `℘`-values are distinct. -/
lemma weierstrassP_ne_of_not_congr_or_neg_congr
    (L : PeriodPair) {u v : ℂ}
    (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (hu_add_v : u + v ∉ L.lattice)
    (hu_sub_v : u - v ∉ L.lattice) :
    ℘[L] u ≠ ℘[L] v := by
  intro huv
  rcases L.weierstrassP_fiber_mod_lattice with ⟨_, hfiber, _⟩
  rcases hfiber hu hv huv.symm with hdiff | hsum
  · exact hu_sub_v (by simpa [sub_eq_add_neg, add_comm] using neg_mem hdiff)
  · exact hu_add_v (by simpa [add_comm] using hsum)

/-- Helper for Exercise 10: distinct Weierstrass `℘`-values determine secant-line coefficients
forcing the affine linear form `℘' - α ℘ - β` to vanish at the chosen two points. -/
lemma exists_linear_form_coeffs_vanishing_at_two_points
    (L : PeriodPair) {u v : ℂ}
    (hneq : ℘[L] u ≠ ℘[L] v) :
    ∃ α β : ℂ,
      (℘'[L] u - α * ℘[L] u - β = 0) ∧
      (℘'[L] v - α * ℘[L] v - β = 0) := by
  let α : ℂ := (℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)
  let β : ℂ := ℘'[L] u - α * ℘[L] u
  refine ⟨α, β, ?_, ?_⟩
  · -- By construction, `β` makes the affine linear form vanish at `u`.
    simp [β]
  · -- The secant-slope formula for `α` then forces the same vanishing at `v`.
    have hdenom : ℘[L] u - ℘[L] v ≠ 0 := sub_ne_zero.mpr hneq
    have halpha :
        α * (℘[L] u - ℘[L] v) = ℘'[L] u - ℘'[L] v := by
      calc
        α * (℘[L] u - ℘[L] v) =
            ((℘'[L] u - ℘'[L] v) / (℘[L] u - ℘[L] v)) * (℘[L] u - ℘[L] v) := by
              simp [α]
        _ = ℘'[L] u - ℘'[L] v := by
              field_simp [hdenom]
    have hrewrite :
        α * ℘[L] u - α * ℘[L] v = ℘'[L] u - ℘'[L] v := by
      simpa [sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, mul_assoc] using halpha
    have hvanishing :
        ℘'[L] v - α * ℘[L] v = ℘'[L] u - α * ℘[L] u := by
      calc
        ℘'[L] v - α * ℘[L] v
            = ℘'[L] u - (℘'[L] u - ℘'[L] v) - α * ℘[L] v := by ring
        _ = ℘'[L] u - (α * ℘[L] u - α * ℘[L] v) - α * ℘[L] v := by rw [hrewrite]
        _ = ℘'[L] u - α * ℘[L] u := by ring
    simpa [β] using sub_eq_zero.mpr hvanishing

/-- Helper for Exercise 10: once the zero divisor of `g` has total multiplicity `3` and weighted
sum `0` modulo the period lattice, some root represents the lattice class of `-u-v`. -/
lemma exists_zero_representative_in_neg_sum_class_of_total_multiplicity_three
    (L : PeriodPair) {P : Set ℂ} {g : ℂ → ℂ} {roots : Finset ℂ} {u v u₀ v₀ : ℂ}
    (hroots : IsZeroRepresentativeSet g P roots)
    (hsum : roots.sum (divisor g P) = 3)
    (hweighted :
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0)
    (hu₀ : u₀ ∈ roots)
    (hv₀ : v₀ ∈ roots)
    (huv₀ : u₀ ≠ v₀)
    (huclass : u₀ - u ∈ L.lattice)
    (hvclass : v₀ - v ∈ L.lattice) :
    ∃ r ∈ roots, r - (-u - v) ∈ L.lattice := by
  classical
  let d : ℂ → ℤ := divisor g P
  have hroot_pos : ∀ z ∈ roots, 0 < d z := by
    intro z hz
    simpa [d] using (hroots.mem_iff z).1 hz |>.2
  have hroot_ge_one : ∀ z ∈ roots, 1 ≤ d z := by
    intro z hz
    have hzpos : 0 < d z := hroot_pos z hz
    omega
  have hweighted_mem : roots.sum (fun z ↦ d z • z) ∈ L.lattice := by
    have hweighted' := hweighted
    -- Read the quotient equality as lattice membership of the weighted divisor sum.
    change
      ((((roots.sum fun z ↦ d z • z) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) =
        ((0 : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) at hweighted'
    rw [QuotientAddGroup.eq_iff_sub_mem] at hweighted'
    simpa using hweighted'
  by_cases hthird : ∃ w ∈ roots, w ≠ u₀ ∧ w ≠ v₀
  · rcases hthird with ⟨w, hw₀, hwu₀, hwv₀⟩
    let T : Finset ℂ := (roots.erase u₀).erase v₀
    have hv₀_erase : v₀ ∈ roots.erase u₀ := by
      exact Finset.mem_erase.mpr ⟨fun h ↦ huv₀ h.symm, hv₀⟩
    have hwT : w ∈ T := by
      simp [T, hw₀, hwu₀, hwv₀]
    have hu₀_ge_one : 1 ≤ d u₀ := hroot_ge_one u₀ hu₀
    have hv₀_ge_one : 1 ≤ d v₀ := hroot_ge_one v₀ hv₀
    have hw_ge_one : 1 ≤ d w := hroot_ge_one w hw₀
    have hsum_split : d u₀ + d v₀ + T.sum d = 3 := by
      -- Split off the two prescribed roots from the total multiplicity-three divisor.
      have hsplit_v : d v₀ + T.sum d = (roots.erase u₀).sum d := by
        simpa [T, add_comm] using (roots.erase u₀).sum_erase_add d hv₀_erase
      have hsplit_u : d u₀ + (roots.erase u₀).sum d = roots.sum d := by
        simpa [add_comm] using (roots.sum_erase_add d hu₀)
      calc
        d u₀ + d v₀ + T.sum d = d u₀ + (roots.erase u₀).sum d := by
          rw [← hsplit_v]
          ring
        _ = roots.sum d := hsplit_u
        _ = 3 := hsum
    have hw_le : d w ≤ T.sum d := by
      exact Finset.single_le_sum
        (fun z hz ↦
          le_of_lt <| hroot_pos z <| Finset.mem_of_mem_erase <| Finset.mem_of_mem_erase hz)
        hwT
    have hT_eq_one : T.sum d = 1 := by
      omega
    have hdu₀ : d u₀ = 1 := by
      omega
    have hdv₀ : d v₀ = 1 := by
      omega
    have hdw : d w = 1 := by
      omega
    have hT_erase_w_sum_zero : (T.erase w).sum d = 0 := by
      -- The third-root remainder has total mass `1`, so removing `w` leaves no multiplicity.
      have hsplit_w : (T.erase w).sum d + d w = T.sum d := by
        simpa [add_comm] using T.sum_erase_add d hwT
      omega
    have hT_singleton : T = ({w} : Finset ℂ) := by
      ext z
      constructor
      · intro hzT
        by_cases hzw : z = w
        · simp [hzw]
        · exfalso
          have hzTw : z ∈ T.erase w := by
            simp [hzT, hzw]
          have hzroot : z ∈ roots := by
            exact Finset.mem_of_mem_erase <| Finset.mem_of_mem_erase hzT
          have hz_ge_one : 1 ≤ d z := hroot_ge_one z hzroot
          have hz_le : d z ≤ (T.erase w).sum d := by
            exact Finset.single_le_sum
              (fun y hy ↦
                le_of_lt <|
                  hroot_pos y <|
                    Finset.mem_of_mem_erase <|
                      Finset.mem_of_mem_erase <|
                        Finset.mem_of_mem_erase hy)
              hzTw
          omega
      · intro hz
        simp at hz
        subst z
        exact hwT
    have hsum_weighted :
        roots.sum (fun z ↦ d z • z) = u₀ + v₀ + w := by
      -- With total multiplicity `3`, the weighted divisor sum is exactly the sum of the three
      -- root representatives.
      have hsplit_u :
          d u₀ • u₀ + (roots.erase u₀).sum (fun z ↦ d z • z) =
            roots.sum (fun z ↦ d z • z) := by
        simpa [add_comm] using
          (roots.sum_erase_add (fun z ↦ d z • z) hu₀)
      have hsplit_v :
          d v₀ • v₀ + T.sum (fun z ↦ d z • z) =
            (roots.erase u₀).sum (fun z ↦ d z • z) := by
        simpa [T, add_comm] using
          ((roots.erase u₀).sum_erase_add (fun z ↦ d z • z) hv₀_erase)
      calc
        roots.sum (fun z ↦ d z • z)
            = d u₀ • u₀ + (roots.erase u₀).sum (fun z ↦ d z • z) := hsplit_u.symm
        _ = d u₀ • u₀ + (d v₀ • v₀ + T.sum (fun z ↦ d z • z)) := by
                rw [← hsplit_v]
        _ = u₀ + v₀ + w := by
                simp [hdu₀, hdv₀, hdw, hT_singleton, add_assoc, add_left_comm, add_comm]
    have hw_class : w - (-u - v) ∈ L.lattice := by
      -- Subtract the two known lattice-class corrections from the weighted lattice relation.
      have hsum_mem : u₀ + v₀ + w ∈ L.lattice := by
        rw [hsum_weighted] at hweighted_mem
        exact hweighted_mem
      have hsub_u : (u₀ + v₀ + w) - (u₀ - u) ∈ L.lattice := sub_mem hsum_mem huclass
      have hsub_v : ((u₀ + v₀ + w) - (u₀ - u)) - (v₀ - v) ∈ L.lattice := by
        exact sub_mem hsub_u hvclass
      convert hsub_v using 1 <;> ring
    exact ⟨w, hw₀, hw_class⟩
  · have hroots_erase : roots.erase u₀ = ({v₀} : Finset ℂ) := by
      ext z
      constructor
      · intro hz
        have hzroot : z ∈ roots := Finset.mem_of_mem_erase hz
        have hz_ne_u₀ : z ≠ u₀ := (Finset.mem_erase.mp hz).1
        by_cases hzv₀ : z = v₀
        · simp [hzv₀]
        · exfalso
          exact hthird ⟨z, hzroot, hz_ne_u₀, hzv₀⟩
      · intro hz
        simp at hz
        subst z
        exact Finset.mem_erase.mpr ⟨fun h ↦ huv₀ h.symm, hv₀⟩
    have hu₀_ge_one : 1 ≤ d u₀ := hroot_ge_one u₀ hu₀
    have hv₀_ge_one : 1 ≤ d v₀ := hroot_ge_one v₀ hv₀
    have hsum_split : d u₀ + d v₀ = 3 := by
      -- If there is no third root support point, the total mass is concentrated at `u₀` and `v₀`.
      have hsplit_u : d u₀ + (roots.erase u₀).sum d = roots.sum d := by
        simpa [add_comm] using (roots.sum_erase_add d hu₀)
      calc
        d u₀ + d v₀ = d u₀ + (roots.erase u₀).sum d := by
          simp [hroots_erase]
        _ = roots.sum d := hsplit_u
        _ = 3 := hsum
    have hsum_weighted :
        roots.sum (fun z ↦ d z • z) = d u₀ • u₀ + d v₀ • v₀ := by
      -- In the two-support case, the weighted sum has only these two contributions.
      have hsplit_u :
          d u₀ • u₀ + (roots.erase u₀).sum (fun z ↦ d z • z) =
            roots.sum (fun z ↦ d z • z) := by
        simpa [add_comm] using
          (roots.sum_erase_add (fun z ↦ d z • z) hu₀)
      calc
        roots.sum (fun z ↦ d z • z)
            = d u₀ • u₀ + (roots.erase u₀).sum (fun z ↦ d z • z) := hsplit_u.symm
        _ = d u₀ • u₀ + d v₀ • v₀ := by
                simp [hroots_erase]
    have hmult_cases :
        (d u₀ = 2 ∧ d v₀ = 1) ∨ (d u₀ = 1 ∧ d v₀ = 2) := by
      omega
    rcases hmult_cases with ⟨hdu₀, hdv₀⟩ | ⟨hdu₀, hdv₀⟩
    · refine ⟨u₀, hu₀, ?_⟩
      -- If `u₀` carries multiplicity `2`, the weighted lattice relation identifies its class with
      -- the missing third root class.
      have hsum_mem : u₀ + u₀ + v₀ ∈ L.lattice := by
        rw [hsum_weighted, hdu₀, hdv₀] at hweighted_mem
        convert hweighted_mem using 1 <;> ring
      have hsub_u : (u₀ + u₀ + v₀) - (u₀ - u) ∈ L.lattice := sub_mem hsum_mem huclass
      have hsub_v : ((u₀ + u₀ + v₀) - (u₀ - u)) - (v₀ - v) ∈ L.lattice := by
        exact sub_mem hsub_u hvclass
      convert hsub_v using 1 <;> ring
    · refine ⟨v₀, hv₀, ?_⟩
      -- The symmetric multiplicity-two case gives the same conclusion with `v₀` as the third
      -- representative.
      have hsum_mem : u₀ + v₀ + v₀ ∈ L.lattice := by
        rw [hsum_weighted, hdu₀, hdv₀] at hweighted_mem
        convert hweighted_mem using 1 <;> ring
      have hsub_u : (u₀ + v₀ + v₀) - (u₀ - u) ∈ L.lattice := sub_mem hsum_mem huclass
      have hsub_v : ((u₀ + v₀ + v₀) - (u₀ - u)) - (v₀ - v) ∈ L.lattice := by
        exact sub_mem hsub_u hvclass
      convert hsub_v using 1 <;> ring

/-- Helper for Exercise 10: a chosen representative of a prescribed zero class belongs to the zero
representative finset for the affine linear form `℘' - α ℘ - β`. -/
lemma linear_form_root_representative_mem_zero_set
    (L : PeriodPair) {z₀ α β u u₀ : ℂ} {roots : Finset ℂ}
    (hu₀P : u₀ ∈ L.periodParallelogram z₀)
    (hu₀ : u₀ ∉ L.lattice)
    (huclass : u₀ - u ∈ L.lattice)
    (hzero : ℘'[L] u - α * ℘[L] u - β = 0)
    (hroots :
      IsZeroRepresentativeSet
        (fun z ↦ ℘'[L] z - α * ℘[L] z - β)
        (L.periodParallelogram z₀)
        roots) :
    u₀ ∈ roots := by
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hu₀_zero : g u₀ = 0 := by
    let l : L.lattice := ⟨u₀ - u, huclass⟩
    have hperiod := (L.weierstrass_linear_form_has_period_lattice α β).2 (u₀ - u) huclass u
    have hu_eq : u + l = u₀ := by
      change u + (u₀ - u) = u₀
      ring
    -- Periodicity transports the prescribed zero from `u` to its chosen representative `u₀`.
    calc
      g u₀ = g (u + l) := by rw [hu_eq.symm]
      _ = g u := by simpa [g] using hperiod
      _ = 0 := hzero
  have hu₀_div_pos :
      0 < divisor g (L.periodParallelogram z₀) u₀ := by
    -- Off the lattice, vanishing is equivalent to positivity of the local divisor.
    exact (L.divisor_linear_form_pos_iff_of_not_mem_lattice
      (P := L.periodParallelogram z₀) (α := α) (β := β) hu₀P hu₀).2 hu₀_zero
  exact (hroots.mem_iff u₀).2 ⟨hu₀P, hu₀_div_pos⟩

theorem exercise10_exists_coeffs_of_three_prescribed_zeros
    (L : PeriodPair) {u v : ℂ}
    (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (hu_add_v : u + v ∉ L.lattice)
    (hu_sub_v : u - v ∉ L.lattice) :
    ∃ α β : ℂ,
      ∀ z ∈ ({u, v, -u - v} : Finset ℂ),
        ℘'[L] z - α * ℘[L] z - β = 0 :=
by
  classical
  have huv_ne : ℘[L] u ≠ ℘[L] v :=
    L.weierstrassP_ne_of_not_congr_or_neg_congr hu hv hu_add_v hu_sub_v
  obtain ⟨α, β, huzero, hvzero⟩ :=
    L.exists_linear_form_coeffs_vanishing_at_two_points huv_ne
  obtain ⟨z₀, hz₀P, hboundary, hpoles, htriple⟩ :=
    L.linear_form_boundary_regular_and_singleton_triple_pole α β
  let g : ℂ → ℂ := fun z ↦ ℘'[L] z - α * ℘[L] z - β
  have hg : Meromorphic g := (L.weierstrass_linear_form_has_period_lattice α β).1
  obtain ⟨roots, hroots⟩ := L.exists_zero_representatives_on_periodParallelogram z₀ hg
  obtain ⟨u₀, hu₀P, hu₀, huclass⟩ :=
    L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := u) (z₀ := z₀) hu
  obtain ⟨v₀, hv₀P, hv₀, hvclass⟩ :=
    L.exists_nonlattice_mem_periodParallelogram_sub_lattice (z := v) (z₀ := z₀) hv
  have hu₀roots : u₀ ∈ roots :=
    L.linear_form_root_representative_mem_zero_set hu₀P hu₀ huclass huzero hroots
  have hv₀roots : v₀ ∈ roots :=
    L.linear_form_root_representative_mem_zero_set hv₀P hv₀ hvclass hvzero hroots
  have hu₀v₀ : u₀ ≠ v₀ := by
    intro huv₀
    have hdiff : u - v ∈ L.lattice := by
      have hsum : (v₀ - v) - (u₀ - u) ∈ L.lattice := sub_mem hvclass huclass
      simpa [huv₀, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
    exact hu_sub_v hdiff
  have hsum_zero :
      roots.sum (divisor g (L.periodParallelogram z₀)) = 3 := by
    -- The total zero multiplicity is exactly the positive divisor mass computed in part (1).
    rw [IsZeroRepresentativeSet.sum_divisor_eq_finsum_posPart hroots]
    simpa [g] using
      L.exercise10_zero_divisor_sum_eq_three z₀ α β 0 hboundary hpoles htriple
  have hweighted_zero :
      (((roots.sum fun z ↦ divisor g (L.periodParallelogram z₀) z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
    -- Part (2) supplies the weighted Abel relation for this same representative finset.
    simpa [g] using
      L.exercise10_zero_weighted_sum_eq_zero_mod_period_lattice
        z₀ α β 0 hboundary hpoles htriple roots hroots
  obtain ⟨r, hrroots, hrclass⟩ :=
    L.exists_zero_representative_in_neg_sum_class_of_total_multiplicity_three
      (P := L.periodParallelogram z₀) (g := g) (roots := roots)
      hroots hsum_zero hweighted_zero hu₀roots hv₀roots hu₀v₀ huclass hvclass
  have hrP : r ∈ L.periodParallelogram z₀ := (hroots.mem_iff r).1 hrroots |>.1
  have hrpos : 0 < divisor g (L.periodParallelogram z₀) r := (hroots.mem_iff r).1 hrroots |>.2
  have hrnot : r ∉ L.lattice := by
    intro hrL
    have htarget : -u - v ∈ L.lattice := by
      have hsub : r - (r - (-u - v)) ∈ L.lattice := sub_mem hrL hrclass
      convert hsub using 1 <;> ring
    have huvL : u + v ∈ L.lattice := by
      simpa [add_comm] using neg_mem htarget
    exact hu_add_v huvL
  have hrzero : g r = 0 := by
    exact (L.divisor_linear_form_pos_iff_of_not_mem_lattice
      (P := L.periodParallelogram z₀) (α := α) (β := β) hrP hrnot).1 hrpos
  have hthird_zero : g (-u - v) = 0 := by
    let l : L.lattice := ⟨r - (-u - v), hrclass⟩
    have hperiod :=
      (L.weierstrass_linear_form_has_period_lattice α β).2 (r - (-u - v)) hrclass (-u - v)
    have hr_eq : (-u - v) + l = r := by
      change (-u - v) + (r - (-u - v)) = r
      ring
    have hrg : g r = g (-u - v) := by
      calc
        g r = g ((-u - v) + l) := by rw [hr_eq.symm]
        _ = g (-u - v) := by simpa [g] using hperiod
    rwa [hrg] at hrzero
  refine ⟨α, β, ?_⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · -- The secant-line construction already gives the zero at `u`.
    exact huzero
  rcases Finset.mem_insert.mp hz with rfl | hz
  · -- The same coefficients make the affine linear form vanish at `v`.
    exact hvzero
  rcases Finset.mem_singleton.mp hz with rfl
  -- The third zero comes from the multiplicity-three divisor and weighted Abel relation.
  exact hthird_zero

-- Exercise 10 (4): if `u + v + w = 0`, then the three row vectors
-- `(℘(u), ℘'(u), 1)`, `(℘(v), ℘'(v), 1)`, and `(℘(w), ℘'(w), 1)` are linearly dependent.
/-- Helper for Exercise 10: a nonzero right-kernel vector forces the rows of a square matrix over
`ℂ` to be linearly dependent. -/
lemma row_matrix_not_linearIndependent_of_nonzero_right_kernel
    (A : Matrix (Fin 3) (Fin 3) ℂ) (c : Fin 3 → ℂ)
    (hc : c ≠ 0) (hAc : A.mulVec c = 0) :
    ¬ LinearIndependent ℂ A := by
  intro hA
  have hunit : IsUnit A := by
    simpa [Matrix.row] using (Matrix.linearIndependent_rows_iff_isUnit (A := A)).1 hA
  have hinj : Function.Injective A.mulVec :=
    (Matrix.mulVec_injective_iff_isUnit (A := A)).2 hunit
  have hc_zero : c = 0 := hinj (by simpa using hAc)
  exact hc hc_zero

theorem exercise10_row_vectors_not_linearIndependent_of_sum_eq_zero
    (L : PeriodPair) {u v w : ℂ}
    (hu : u ∉ L.lattice)
    (hv : v ∉ L.lattice)
    (hw : w ∉ L.lattice)
    (huvw : u + v + w = 0) :
    ¬ LinearIndependent ℂ
      ![![℘[L] u, ℘'[L] u, (1 : ℂ)],
        ![℘[L] v, ℘'[L] v, (1 : ℂ)],
        ![℘[L] w, ℘'[L] w, (1 : ℂ)]] :=
by
  classical
  let A : Matrix (Fin 3) (Fin 3) ℂ :=
    ![![℘[L] u, ℘'[L] u, (1 : ℂ)],
      ![℘[L] v, ℘'[L] v, (1 : ℂ)],
      ![℘[L] w, ℘'[L] w, (1 : ℂ)]]
  by_cases hu_sub_v : u - v ∈ L.lattice
  · intro hA
    have hA' : LinearIndependent ℂ A := by
      simpa [A] using hA
    let l : L.lattice := ⟨u - v, hu_sub_v⟩
    have hu_eq : v + l = u := by
      change v + (u - v) = u
      ring
    have hweier : ℘[L] v = ℘[L] u := by
      simpa [hu_eq] using (L.weierstrassP_add_coe v l).symm
    have hderiv : ℘'[L] v = ℘'[L] u := by
      simpa [hu_eq] using (L.derivWeierstrassP_add_coe v l).symm
    have hrow_eq : A 1 = A 0 := by
      -- Congruent points give identical rows because both `℘` and `℘'` are lattice-periodic.
      ext i
      fin_cases i <;> simp [A, hweier, hderiv]
    have hinj := hA'.injective
    have hidx : (1 : Fin 3) = 0 := hinj hrow_eq
    have hval : (1 : Nat) = 0 := congrArg Fin.val hidx
    norm_num at hval
  · have hu_add_v : u + v ∉ L.lattice := by
      intro huvL
      have huv_eq : u + v = -w := by
        have hsum : (u + v) + w = 0 := by
          simpa [add_assoc] using huvw
        have hsub := congrArg (fun z : ℂ ↦ z - w) hsum
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
      have hw_neg : -w ∈ L.lattice := by
        simpa [huv_eq] using huvL
      have hwL : w ∈ L.lattice := by
        simpa using neg_mem hw_neg
      exact hw hwL
    obtain ⟨α, β, hzeros⟩ :=
      L.exercise10_exists_coeffs_of_three_prescribed_zeros hu hv hu_add_v hu_sub_v
    let c : Fin 3 → ℂ := ![-α, 1, -β]
    have hc : c ≠ 0 := by
      intro hc0
      have hcoord := congrArg (fun x : Fin 3 → ℂ ↦ x 1) hc0
      simpa [c] using hcoord
    have hw_eq : w = -u - v := by
      have hsum : w + (u + v) = 0 := by
        calc
          w + (u + v) = u + (v + w) := by ring
          _ = 0 := by simpa [add_assoc] using huvw
      simpa [neg_add, add_comm] using eq_neg_of_add_eq_zero_left hsum
    have hAc : A.mulVec c = 0 := by
      ext i
      fin_cases i
      · -- The first row kills `c` because the linear form vanishes at `u`.
        simpa [A, c, Matrix.mulVec, dotProduct, Fin.sum_univ_three, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
          hzeros u (by simp)
      · -- The second row kills `c` because the linear form vanishes at `v`.
        simpa [A, c, Matrix.mulVec, dotProduct, Fin.sum_univ_three, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
          hzeros v (by simp)
      · -- The third row kills `c` because `w = -u - v` is the forced third zero.
        simpa [A, c, hw_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_three, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
          hzeros (-u - v) (by simp)
    simpa [A] using row_matrix_not_linearIndependent_of_nonzero_right_kernel A c hc hAc

end PeriodPair
