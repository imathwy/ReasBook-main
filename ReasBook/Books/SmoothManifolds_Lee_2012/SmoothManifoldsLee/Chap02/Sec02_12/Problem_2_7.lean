import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.LinearAlgebra.Dimension.Finite

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Manifold ContDiff
open TopologicalSpace

universe uι uX uE uH uM

/-- Real-valued functions with pairwise disjoint nonempty supports are linearly independent over
`ℝ`. -/
theorem functions_linearIndependent_of_pairwise_disjoint_support
    {ι : Type uι} {X : Type uX} {f : ι → X → ℝ}
    (hdisj : Pairwise fun i j ↦ Disjoint (Function.support (f i)) (Function.support (f j)))
    (hsupp : ∀ i, (Function.support (f i)).Nonempty) :
    LinearIndependent ℝ f := by
  refine linearIndependent_iff'.2 fun s g hsum i hi ↦ ?_
  obtain ⟨x, hx⟩ := hsupp i
  have hx' : f i x ≠ 0 := by
    simpa [Function.mem_support] using hx
  have hsumx : s.sum (fun j ↦ g j • (f j x)) = 0 := by
    simpa using congr_fun hsum x
  rw [Finset.sum_eq_single i] at hsumx
  · exact (smul_eq_zero.mp hsumx).resolve_right hx'
  · intro j hj hji
    have hxj : x ∉ Function.support (f j) := by
      exact Set.disjoint_left.mp (hdisj hji.symm) hx
    have hfjx : f j x = 0 := by
      simpa [Function.mem_support] using hxj
    simp [hfjx]
  · intro hii
    exact (hii hi).elim

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Helper for Problem 2-7: distinct natural-number indices have real distance at least `1`. -/
lemma one_le_abs_sub_of_ne_natCast {i j : ℕ} (hij : i ≠ j) :
    (1 : ℝ) ≤ |(i : ℝ) - j| := by
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · have hcast : (i : ℝ) + 1 ≤ j := by
      exact_mod_cast Nat.succ_le_of_lt hij'
    have habs : |(i : ℝ) - j| = (j : ℝ) - i := by
      rw [abs_of_nonpos]
      · ring
      nlinarith
    rw [habs]
    nlinarith
  · have hcast : (j : ℝ) + 1 ≤ i := by
      exact_mod_cast Nat.succ_le_of_lt hij'
    have habs : |(i : ℝ) - j| = (i : ℝ) - j := by
      rw [abs_of_nonneg]
      nlinarith
    rw [habs]
    nlinarith

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Helper for Problem 2-7: a positive-dimensional normed ball contains any prescribed finite
family of pairwise disjoint smaller open balls. -/
lemma exists_pairwise_disjoint_balls_in_ball (n : ℕ) (hn : 0 < n) (y : E) {r : ℝ}
    (hr : 0 < r) (hpos : 0 < Module.finrank ℝ E) :
    ∃ c : Fin n → E, ∃ ρ > 0,
      (∀ i, Metric.ball (c i) ρ ⊆ Metric.ball y r) ∧
      Pairwise fun i j ↦ Disjoint (Metric.ball (c i) ρ) (Metric.ball (c j) ρ) := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  let u : E := (‖v‖)⁻¹ • v
  let ρ : ℝ := r / (4 * n)
  let dir : E := (3 * ρ) • u
  let c : Fin n → E := fun i ↦ y + (i : ℝ) • dir
  have hn' : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    simpa using norm_smul_inv_norm (𝕜 := ℝ) hv
  have hdir : ‖dir‖ = 3 * ρ := by
    dsimp [dir]
    simpa [hu] using norm_smul_of_nonneg (E := E) (x := u) (show 0 ≤ 3 * ρ by positivity)
  refine ⟨c, ρ, hρ, ?_, ?_⟩
  · intro i x hx
    have hxy : dist x y < r := by
      have hxci : dist x (c i) < ρ := hx
      have hciy : dist (c i) y = (i : ℝ) * (3 * ρ) := by
        calc
          dist (c i) y = ‖c i - y‖ := by rw [dist_eq_norm]
          _ = ‖(i : ℝ) • dir‖ := by
            simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          _ = |(i : ℝ)| * ‖dir‖ := norm_smul _ _
          _ = (i : ℝ) * ‖dir‖ := by
            have habs : |(i : ℝ)| = i := by
              rw [abs_of_nonneg]
              exact_mod_cast Nat.zero_le i
            rw [habs]
          _ = (i : ℝ) * (3 * ρ) := by rw [hdir]
      have hi : (i : ℝ) < n := by
        exact_mod_cast i.is_lt
      have hbound : ρ + (i : ℝ) * (3 * ρ) < r := by
        have hrho : (4 * n : ℝ) * ρ = r := by
          dsimp [ρ]
          field_simp
        have haux : ρ + (i : ℝ) * (3 * ρ) < ρ + n * (3 * ρ) := by
          gcongr
        have hstrict : ρ + n * (3 * ρ) ≤ (4 * n : ℝ) * ρ := by
          have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast hn
          nlinarith [hn1, hρ]
        exact lt_of_lt_of_le haux <| hstrict.trans_eq hrho
      have hsum : dist x (c i) + dist (c i) y < r := by
        rw [hciy]
        nlinarith [hxci, hbound]
      exact lt_of_le_of_lt (dist_triangle x (c i) y) <| by
        exact hsum
    simpa [Metric.mem_ball] using hxy
  · intro i j hij
    have hsub : c i - c j = ((i : ℝ) - j) • dir := by
      calc
        c i - c j = ((i : ℝ) • dir) - ((j : ℝ) • dir) := by
          simp [c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = ((i : ℝ) - j) • dir := by rw [sub_smul]
    have hdist : dist (c i) (c j) = |(i : ℝ) - j| * (3 * ρ) := by
      calc
        dist (c i) (c j) = ‖c i - c j‖ := by rw [dist_eq_norm]
        _ = ‖((i : ℝ) - j) • dir‖ := by rw [hsub]
        _ = |(i : ℝ) - j| * ‖dir‖ := norm_smul _ _
        _ = |(i : ℝ) - j| * (3 * ρ) := by rw [hdir]
    have hgap : ρ + ρ ≤ dist (c i) (c j) := by
      rw [hdist]
      have hsep : (1 : ℝ) ≤ |(i : ℝ) - j| :=
        one_le_abs_sub_of_ne_natCast fun h => hij (Fin.ext h)
      nlinarith [hsep, hρ]
    exact Metric.ball_disjoint_ball hgap

/-- Helper for Problem 2-7: one chart contains arbitrarily large finite families of pairwise
disjoint open balls. -/
lemma exists_pairwise_disjoint_chart_balls [T2Space M] (p : M) (n : ℕ) (hn : 0 < n)
    (hpos : 0 < Module.finrank ℝ E) :
    ∃ c : Fin n → E, ∃ ρ > 0,
      (∀ i, c i ∈ (extChartAt I p).target) ∧
      (∀ i, Metric.ball (c i) ρ ⊆ (extChartAt I p).target) ∧
      Pairwise fun i j ↦ Disjoint (Metric.ball (c i) ρ) (Metric.ball (c j) ρ) := by
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty (I := I) p
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp <| isOpen_interior.mem_nhds hy
  obtain ⟨c, ρ, hρ, hsub, hdisj⟩ :=
    exists_pairwise_disjoint_balls_in_ball (n := n) hn y hr hpos
  refine ⟨c, ρ, hρ, ?_, ?_, hdisj⟩
  · intro i
    have hci : c i ∈ Metric.ball y r := hsub i <| by simpa [Metric.mem_ball, hρ]
    exact interior_subset (hrsub hci)
  · intro i
    exact (hsub i).trans (hrsub.trans interior_subset)

/-- Helper for Problem 2-7: every nonempty positive-dimensional smooth manifold admits finite
linearly independent families of smooth real-valued functions. -/
lemma exists_linearlyIndependent_smooth_family [T2Space M] (p : M) (n : ℕ) (hn : 0 < n)
    (hpos : 0 < Module.finrank ℝ E) :
    ∃ f : Fin n → C^∞⟮I, M; ℝ⟯, LinearIndependent ℝ f := by
  classical
  obtain ⟨c, ρ, hρ, hc, hball, hdisj⟩ :=
    exists_pairwise_disjoint_chart_balls (I := I) p n hn hpos
  let q : Fin n → M := fun i ↦ (extChartAt I p).symm (c i)
  let U : Fin n → Set M := fun i ↦ (chartAt H p).source ∩ (extChartAt I p) ⁻¹' Metric.ball (c i) ρ
  have hU_mem : ∀ i, U i ∈ nhds (q i) := by
    intro i
    have hq_source : q i ∈ (extChartAt I p).source := (extChartAt I p).map_target (hc i)
    have hq_mem : q i ∈ U i := by
      refine ⟨?_, ?_⟩
      · simpa [q, extChartAt_source] using hq_source
      · change extChartAt I p ((extChartAt I p).symm (c i)) ∈ Metric.ball (c i) ρ
        rw [(extChartAt I p).right_inv (hc i)]
        exact Metric.mem_ball_self hρ
    exact (isOpen_extChartAt_preimage (I := I) p Metric.isOpen_ball).mem_nhds hq_mem
  have hbump : ∀ i, ∃ b : SmoothBumpFunction I (q i), Function.support b ⊆ U i := by
    intro i
    have hbasis :=
      SmoothBumpFunction.nhds_basis_support (I := I) (c := q i) (s := U i) (hU_mem i)
    obtain ⟨b, -, hbsub⟩ := hbasis.mem_iff.mp (hU_mem i)
    exact ⟨b, hbsub⟩
  choose b hbsub using hbump
  let f : Fin n → C^∞⟮I, M; ℝ⟯ := fun i ↦ ⟨b i, (b i).contMDiff⟩
  have hsupport_disjoint : Pairwise fun i j ↦
      Disjoint (Function.support (b i)) (Function.support (b j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hix hjx ↦ ?_
    have hix' : extChartAt I p x ∈ Metric.ball (c i) ρ := (hbsub i hix).2
    have hjx' : extChartAt I p x ∈ Metric.ball (c j) ρ := (hbsub j hjx).2
    exact (hdisj hij).le_bot ⟨hix', hjx'⟩
  have hsupport_nonempty : ∀ i, (Function.support (f i)).Nonempty := by
    intro i
    simpa [f] using (b i).nonempty_support
  refine ⟨f, ?_⟩
  -- Route correction: linear independence is proved from disjoint supports exactly as the problem
  -- hint suggests, after the manifold work is reduced to choosing the bump functions.
  have hfun :
      LinearIndependent ℝ (fun i : Fin n ↦ (f i : M → ℝ)) :=
    functions_linearIndependent_of_pairwise_disjoint_support
      (f := fun i x ↦ f i x) (by simpa [f] using hsupport_disjoint) hsupport_nonempty
  exact LinearIndependent.of_comp (ContMDiffMap.coeFnLinearMap (𝕜 := ℝ) (I := I) (N := M)
    (V := ℝ)) (by simpa using hfun)

end FiniteDimensional

-- Proof sketch: choose a point `p : M`, use `SmoothBumpFunction.nhds_basis_support` in a single
-- positive-dimensional chart around `p` to obtain arbitrarily large finite families of smooth bump
-- functions with pairwise disjoint supports inside that chart neighborhood. Viewing these bump
-- functions in the ambient function space and applying
-- `functions_linearIndependent_of_pairwise_disjoint_support` gives linearly independent families of
-- every finite cardinality in `C^∞⟮I, M; ℝ⟯`, so the smooth-function space cannot be
-- finite-dimensional.
/-- Problem 2-7: if `M` is a nonempty smooth manifold with or without boundary and the model space
has positive finite dimension, then the vector space of smooth real-valued functions on `M` is not
finite-dimensional over `ℝ`. -/
theorem smooth_functions_not_finiteDimensional
    [FiniteDimensional ℝ E] [T2Space M] [Nonempty M] (hpos : 0 < Module.finrank ℝ E) :
    ¬ FiniteDimensional ℝ C^∞⟮I, M; ℝ⟯ := by
  intro hfd
  letI := hfd
  let n := Module.finrank ℝ C^∞⟮I, M; ℝ⟯ + 1
  have hn : 0 < n := Nat.succ_pos _
  obtain ⟨p⟩ := ‹Nonempty M›
  -- Build a family with one more element than the claimed dimension.
  obtain ⟨f, hf⟩ := exists_linearlyIndependent_smooth_family (I := I) p n hn hpos
  have hcard :
      Fintype.card (Fin n) ≤ Module.finrank ℝ C^∞⟮I, M; ℝ⟯ :=
    LinearIndependent.fintype_card_le_finrank hf
  -- This contradicts the finite-dimensional cardinality bound.
  simpa [n] using hcard
