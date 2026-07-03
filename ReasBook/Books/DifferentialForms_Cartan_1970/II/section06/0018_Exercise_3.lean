import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

namespace Path

@[simp] theorem map'_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {a b : X} {γ : Path a b} {f : X → Y} (h : ContinuousOn f (Set.range γ))
    (t : Set.Icc (0 : ℝ) 1) :
    γ.map' h t = f (γ t) :=
  rfl

/-- Helper for Exercise 3: each closed subdivision piece stays inside the unit interval. -/
private lemma subdivision_piece_subset_unitInterval
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1) :
    ∀ i : Fin (n + 1), Set.Icc (subdiv i.castSucc) (subdiv i.succ) ⊆ I := by
  intro i t ht
  constructor
  · -- The left endpoint of every piece lies to the right of `0`.
    calc
      0 = subdiv 0 := by symm; exact h0
      _ ≤ subdiv i.castSucc := hsubdiv.monotone (Fin.zero_le _)
      _ ≤ t := ht.1
  · -- The right endpoint of every piece lies to the left of `1`.
    calc
      t ≤ subdiv i.succ := ht.2
      _ ≤ subdiv (Fin.last (n + 1)) := hsubdiv.monotone i.succ.le_last
      _ = 1 := h1

/-- Helper for Exercise 3: on each closed smooth piece, the extension of the mapped path agrees
with the composition `φ ∘ γ.extend`. -/
private lemma map'_extend_eqOn_piece
    {a b : ℂ} {γ : Path a b} {D : Set ℂ} {φ : ℂ → ℂ}
    (hγD : Set.range γ ⊆ D) (hφ : DifferentiableOn ℂ φ D)
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1) (i : Fin (n + 1)) :
    Set.EqOn (γ.map' ((hφ.continuousOn).mono hγD)).extend
      (fun t ↦ φ (γ.extend t))
      (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
  intro t ht
  -- Both extensions can be replaced by ordinary path values because the piece lies in `[0,1]`.
  have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
  simp [Path.extend_apply, htI]

/-- Helper for Exercise 3: the same subdivision witnessing piecewise differentiability of `γ`
also witnesses `C¹` regularity of the mapped path `φ ∘ γ` on each closed piece. -/
private lemma mapped_path_contDiffOn_piece
    {a b : ℂ} {γ : Path a b} {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hγD : Set.range γ ⊆ D) (hφ : DifferentiableOn ℂ φ D)
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1)
    (hpieces : ∀ i : Fin (n + 1),
      ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)))
    (i : Fin (n + 1)) :
    ContDiffOn ℝ 1 (γ.map' ((hφ.continuousOn).mono hγD)).extend
      (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
  have hmapsToD :
      Set.MapsTo γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) D := by
    intro t ht
    -- Points on the subdivision piece come from the original path inside `D`.
    have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
    simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
  have hcomp :
      ContDiffOn ℝ 1 (fun t ↦ φ (γ.extend t))
        (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    -- Compose the `C¹` path piece with the real-scalar restriction of the holomorphic map.
    exact (((hφ.contDiffOn hD).restrict_scalars ℝ).comp (hpieces i) hmapsToD)
  -- Replace the composed extension by the actual extension of the mapped path on this piece.
  refine hcomp.congr ?_
  intro t ht
  symm
  exact map'_extend_eqOn_piece hγD hφ hsubdiv h0 h1 i ht

/-- Helper for Exercise 3: a continuous scalar coefficient pulled back along a `C¹` path piece is
interval integrable on that piece. -/
private lemma pullback_scalar_intervalIntegrable_on_piece {z₀ z₁ : ℂ} {γ : Path z₀ z₁}
    {l u : ℝ} (hlt : l < u) (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc l u)) {ψ : ℂ → ℂ}
    (hψ : ContinuousOn ψ (γ.extend '' Set.Icc l u)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * ψ (γ.extend t)) MeasureTheory.volume l u := by
  -- First replace the ordinary derivative by the continuous within-derivative on the closed piece.
  have hDerivWithin :
      ContinuousOn (fun t ↦ derivWithin γ.extend (Set.Icc l u) t) (Set.Icc l u) := by
    exact (hγ.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
  have hCoeff : ContinuousOn (fun t ↦ ψ (γ.extend t)) (Set.Icc l u) := by
    refine hψ.comp (by fun_prop) ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIntWithin :
      IntervalIntegrable
        (fun t ↦ derivWithin γ.extend (Set.Icc l u) t * ψ (γ.extend t))
        MeasureTheory.volume l u :=
    (hDerivWithin.mul hCoeff).intervalIntegrable_of_Icc hlt.le
  -- On the interior of the piece, the within-derivative equals the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact by simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/- Helper for Exercise 3: on each open smooth piece, the pullback integrand for the mapped path
coincides with the chain-rule pullback integrand on the original path. -/
private lemma mapped_curve_integrand_eqOn_piece
    {a b : ℂ} {γ : Path a b} {D : Set ℂ} (hD : IsOpen D) {φ f : ℂ → ℂ}
    (hγD : Set.range γ ⊆ D) (hφ : DifferentiableOn ℂ φ D)
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1)
    (hpieces : ∀ i : Fin (n + 1),
      ContDiffOn ℝ 1 γ.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)))
    (i : Fin (n + 1)) :
    Set.EqOn
      (fun t ↦
        deriv (γ.map' ((hφ.continuousOn).mono hγD)).extend t *
          f ((γ.map' ((hφ.continuousOn).mono hγD)).extend t))
      (fun t ↦ deriv γ.extend t * (f (φ (γ.extend t)) * deriv φ (γ.extend t)))
      (Set.Ioo (subdiv i.castSucc) (subdiv i.succ)) := by
  intro t ht
  have hEqOpen :
      Set.EqOn (γ.map' ((hφ.continuousOn).mono hγD)).extend
        (fun s ↦ φ (γ.extend s))
        (Set.Ioo (subdiv i.castSucc) (subdiv i.succ)) := by
    intro s hs
    exact map'_extend_eqOn_piece hγD hφ hsubdiv h0 h1 i ⟨hs.1.le, hs.2.le⟩
  have hDerivEq :
      deriv (γ.map' ((hφ.continuousOn).mono hγD)).extend t =
        deriv (fun s ↦ φ (γ.extend s)) t := by
    exact (hEqOpen.deriv isOpen_Ioo) ht
  have htClosed : t ∈ Set.Icc (subdiv i.castSucc) (subdiv i.succ) := ⟨ht.1.le, ht.2.le⟩
  have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i htClosed
  have hzD : γ.extend t ∈ D := by
    -- The current point still lies on the original path inside `D`.
    simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
  have hγDiffWithin :
      DifferentiableWithinAt ℝ γ.extend
        (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) t :=
    (hpieces i t htClosed).differentiableWithinAt one_ne_zero
  have hγDiffAt : DifferentiableAt ℝ γ.extend t :=
    hγDiffWithin.differentiableAt (Icc_mem_nhds ht.1 ht.2)
  have hφDiffAt : DifferentiableAt ℂ φ (γ.extend t) :=
    (hφ (γ.extend t) hzD).differentiableAt (hD.mem_nhds hzD)
  have hChain :
      deriv (fun s ↦ φ (γ.extend s)) t = deriv φ (γ.extend t) * deriv γ.extend t := by
    -- Convert the complex derivative of `φ` into the real Fréchet derivative needed for the
    -- real-parameter chain rule along the path.
    have hOuter :
        HasFDerivAt φ (deriv φ (γ.extend t) • (1 : ℂ →L[ℝ] ℂ)) (γ.extend t) :=
      (hφDiffAt.hasDerivAt).complexToReal_fderiv
    have hComp :
        HasDerivAt (fun s ↦ φ (γ.extend s))
          ((deriv φ (γ.extend t) • (1 : ℂ →L[ℝ] ℂ)) (deriv γ.extend t)) t :=
      hOuter.comp_hasDerivAt t hγDiffAt.hasDerivAt
    simpa [ContinuousLinearMap.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hComp.deriv
  -- Replace the mapped-path derivative by the chain-rule expression and simplify the scalar form.
  calc
    deriv (γ.map' ((hφ.continuousOn).mono hγD)).extend t *
        f ((γ.map' ((hφ.continuousOn).mono hγD)).extend t) =
      deriv (fun s ↦ φ (γ.extend s)) t * f (φ (γ.extend t)) := by
        rw [hDerivEq, hEqOpen ht]
    _ = deriv γ.extend t * (f (φ (γ.extend t)) * deriv φ (γ.extend t)) := by
        rw [hChain]
        ring

-- Proof sketch: use the finite break set witnessing piecewise differentiability of `γ`; away from
-- those break points, `γ.extend` is differentiable and composition with `φ` preserves
-- differentiability because the path stays inside `D`.
/-- Helper for Exercise 3: composing a piecewise differentiable complex path with a holomorphic map
preserves piecewise differentiability. -/
lemma IsPiecewiseDifferentiable.map'_of_differentiableOn {a b : ℂ} {γ : Path a b}
    (hγ : γ.IsPiecewiseDifferentiable) {D : Set ℂ} (hD : IsOpen D) {φ : ℂ → ℂ}
    (hγD : Set.range γ ⊆ D) (hφ : DifferentiableOn ℂ φ D) :
    (γ.map' ((hφ.continuousOn).mono hγD)).IsPiecewiseDifferentiable := by
  rcases hγ with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  -- Reuse the original subdivision and transport `C¹` regularity through the holomorphic map.
  refine ⟨n, subdiv, hsubdiv, h0, h1, ?_⟩
  intro i
  exact mapped_path_contDiffOn_piece hD hγD hφ hsubdiv h0 h1 hpieces i

-- Proof sketch: subdivide `γ` at its finitely many break points; on each smooth subinterval,
-- apply the chain rule to `φ ∘ γ` and the one-variable change-of-variables formula for the curve
-- integral, using that `f` is continuous on the actual image `φ '' Set.range γ`, then sum the
-- resulting equalities over the subdivision.
/-- Exercise 3: if `γ` is a piecewise differentiable path contained in `D` and `φ` is holomorphic
on `D`, then the image path `φ ∘ γ` satisfies
`∫_{φ ∘ γ} f(w) dw = ∫_γ f(φ(z)) φ'(z) dz`; in particular, this remains valid without global
differentiability of `γ`, provided that `γ` is piecewise differentiable. -/
theorem curveIntegral_map'_eq_curveIntegral_mul_deriv
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseDifferentiable)
    {D : Set ℂ} (hD : IsOpen D) (hγD : Set.range γ ⊆ D)
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D)
    {f : ℂ → ℂ} (hf : ContinuousOn f (φ '' Set.range γ)) :
    ∫ᶜ w in γ.map' ((hφ.continuousOn).mono hγD), (1 : ℂ →L[ℂ] ℂ).smulRight (f w) =
      ∫ᶜ z in γ, (1 : ℂ →L[ℂ] ℂ).smulRight (f (φ z) * deriv φ z) := by
  let η : Path (φ a) (φ b) := γ.map' ((hφ.continuousOn).mono hγD)
  rcases hγ with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  let a' : ℕ → ℝ := fun k ↦
    if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  let gL : ℝ → ℂ := fun t ↦ deriv η.extend t * f (η.extend t)
  let gR : ℝ → ℂ := fun t ↦ deriv γ.extend t * (f (φ (γ.extend t)) * deriv φ (γ.extend t))
  have ha0 : a' 0 = 0 := by
    simp [a', h0]
  have ha1 : a' (n + 1) = 1 := by
    simpa [a'] using h1
  have hIntL :
      ∀ k < n + 1, IntervalIntegrable gL MeasureTheory.volume (a' k) (a' (k + 1)) := by
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    have hηpiece :
        ContDiffOn ℝ 1 η.extend (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
      -- The mapped path is `C¹` on the same subdivision pieces as the original path.
      simpa [η] using mapped_path_contDiffOn_piece hD hγD hφ hsubdiv h0 h1 hpieces i
    have hf_piece :
        ContinuousOn f (η.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
      refine hf.mono ?_
      rintro z ⟨t, ht, rfl⟩
      have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
      -- Every point on the mapped piece comes from applying `φ` to a point of the original path.
      refine ⟨γ ⟨t, htI⟩, ⟨⟨t, htI⟩, rfl⟩, ?_⟩
      simpa [η, Path.extend_apply γ htI] using
        (map'_extend_eqOn_piece hγD hφ hsubdiv h0 h1 i ht).symm
    have hInt :
        IntervalIntegrable
          (fun t ↦ deriv η.extend t * f (η.extend t))
          MeasureTheory.volume (subdiv i.castSucc) (subdiv i.succ) := by
      exact pullback_scalar_intervalIntegrable_on_piece hlt hηpiece hf_piece
    simpa [a', gL, i, hk0, hk1] using hInt
  have hIntR :
      ∀ k < n + 1, IntervalIntegrable gR MeasureTheory.volume (a' k) (a' (k + 1)) := by
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    have hpiece_image_subset_D :
        γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ) ⊆ D := by
      rintro z ⟨t, ht, rfl⟩
      have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
      simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
    have hφ_piece :
        ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) :=
      (hφ.continuousOn).mono hpiece_image_subset_D
    have hderiv_piece :
        ContinuousOn (deriv φ) (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) :=
      ((hφ.deriv hD).continuousOn).mono hpiece_image_subset_D
    have hf_comp_piece :
        ContinuousOn (fun z ↦ f (φ z))
          (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
      refine hf.comp hφ_piece ?_
      intro z hz
      rcases hz with ⟨t, ht, rfl⟩
      have htI : t ∈ I := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
      exact ⟨γ ⟨t, htI⟩, ⟨⟨t, htI⟩, rfl⟩, by simp [Path.extend_apply γ htI]⟩
    have hCoeff_piece :
        ContinuousOn (fun z ↦ f (φ z) * deriv φ z)
          (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) :=
      hf_comp_piece.mul hderiv_piece
    have hInt :
        IntervalIntegrable
          (fun t ↦ deriv γ.extend t * (f (φ (γ.extend t)) * deriv φ (γ.extend t)))
          MeasureTheory.volume (subdiv i.castSucc) (subdiv i.succ) := by
      exact pullback_scalar_intervalIntegrable_on_piece hlt (hpieces i) hCoeff_piece
    simpa [a', gR, i, hk0, hk1] using hInt
  have hPieceEq :
      ∀ k < n + 1,
        ∫ t in a' k..a' (k + 1), gL t = ∫ t in a' k..a' (k + 1), gR t := by
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    have hEqAe :
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.uIoc (subdiv i.castSucc) (subdiv i.succ))),
          gL t = gR t := by
      -- Equality holds on the open smooth piece; the endpoints are negligible for the interval
      -- integral.
      rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      simpa [gL, gR, η] using
        mapped_curve_integrand_eqOn_piece (f := f) hD hγD hφ hsubdiv h0 h1 hpieces i ht
    have hEqInt :
        ∫ t in subdiv i.castSucc..subdiv i.succ, gL t =
          ∫ t in subdiv i.castSucc..subdiv i.succ, gR t :=
      intervalIntegral.integral_congr_ae_restrict hEqAe
    simpa [a', i, hk0, hk1] using hEqInt
  have hsumL :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), gL t) =
        ∫ t in a' 0..a' (n + 1), gL t :=
    by
      simpa using intervalIntegral.sum_integral_adjacent_intervals (f := gL) hIntL
  have hsumR :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), gR t) =
        ∫ t in a' 0..a' (n + 1), gR t :=
    by
      simpa using intervalIntegral.sum_integral_adjacent_intervals (f := gR) hIntR
  -- Rewrite both contour integrals as interval integrals and compare the adjacent subdivision
  -- pieces one by one.
  calc
    ∫ᶜ w in γ.map' ((hφ.continuousOn).mono hγD), (1 : ℂ →L[ℂ] ℂ).smulRight (f w) =
        ∫ t in 0..1, gL t := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      simp [gL, η]
    _ = Finset.sum (Finset.range (n + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), gL t) := by
      symm
      simpa [ha0, ha1] using hsumL
    _ = Finset.sum (Finset.range (n + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), gR t) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact hPieceEq k (Finset.mem_range.mp hk)
    _ = ∫ t in 0..1, gR t := by
      simpa [ha0, ha1] using hsumR
    _ = ∫ᶜ z in γ, (1 : ℂ →L[ℂ] ℂ).smulRight (f (φ z) * deriv φ z) := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      simp [gR]

end Path
