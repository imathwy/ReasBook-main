import DifferentialForms_Cartan_1970.cartan.IV.section17.«0002_Theorem_IV_5_extra_2».BoundaryCauchySeries

/-- Helper for Theorem IV.5-extra-2: updating two distinct coordinates of a fixed finite vector
is analytic in the two inserted scalar variables. -/
lemma analyticAt_update_twoCoordinates
    {n : ℕ} {x : Fin n → ℂ} {i j : Fin n} (hij : i ≠ j) (q : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ ↦ Function.update (Function.update x j q.1) i q.2) q := by
  refine AnalyticAt.pi fun k ↦ ?_
  by_cases hk_i : k = i
  · subst hk_i
    simpa [Function.update, hij] using
      (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.2) q)
  by_cases hk_j : k = j
  · subst hk_j
    simpa [Function.update, hij, hk_i] using
      (analyticAt_fst : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.1) q)
  simpa [Function.update, hk_i, hk_j] using
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ ↦ x k) q)

/-- Helper for Theorem IV.5-extra-2: the coordinate-order swap `(ζ, u) ↦ ![u, ζ]` is jointly
analytic on every subset of `ℂ × ℂ`. -/
lemma analyticOnNhd_fin2Swap
    {s : Set (ℂ × ℂ)} :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ ![p.2, p.1]) s := by
  refine (analyticOnNhd_pi_iff :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ fun i : Fin 2 ↦ (![p.2, p.1] : Fin 2 → ℂ) i) s ↔
      ∀ i : Fin 2, AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ (![p.2, p.1] : Fin 2 → ℂ) i) s).2 ?_
  intro i
  fin_cases i
  · simpa using (analyticOnNhd_snd (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := s))
  · simpa using (analyticOnNhd_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ) (t := s))

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the product-coordinate packing map
`(z₁, z₂) ↦ ![z₁, z₂]` is jointly analytic. -/
lemma analyticAt_fin2Pack (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ ↦ ![q.1, q.2]) p := by
  -- Prove analyticity coordinatewise: the packed `Fin 2` coordinates are exactly `fst` and `snd`.
  refine AnalyticAt.pi fun i ↦ ?_
  fin_cases i
  · simpa using (analyticAt_fst : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.1) p)
  · simpa using (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.2) p)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: translating the product-coordinate pack
map by a fixed `Fin 2` point stays jointly analytic. -/
lemma analyticAt_fin2TranslatePack (z : Fin 2 → ℂ) (p : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ ↦ ![z 0 + q.1, z 1 + q.2]) p := by
  -- The translated packing map is still coordinatewise affine in the two product variables.
  refine AnalyticAt.pi fun i ↦ ?_
  fin_cases i
  · simpa using
      (analyticAt_const.add (analyticAt_fst : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.1) p))
  · simpa using
      (analyticAt_const.add (analyticAt_snd : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.2) p))

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: every open subset of `Fin 2 → ℂ`
contains a translated product bidisc around each of its points. This is the geometric owner needed
to localize the direct `Fin 2` Hartogs argument to a bidisc without invoking the recursive product
theorem. -/
lemma fin2_exists_localBidisc_subset_domain
    {D2 : Set (Fin 2 → ℂ)} (hD2 : IsOpen D2) {z : Fin 2 → ℂ} (hz : z ∈ D2) :
    ∃ r : ℝ, 0 < r ∧
      ∀ q : ℂ × ℂ, ‖q.1‖ < r → ‖q.2‖ < r → ![z 0 + q.1, z 1 + q.2] ∈ D2 := by
  let φ : ℂ × ℂ → Fin 2 → ℂ := fun q ↦ ![z 0 + q.1, z 1 + q.2]
  have hφcont : Continuous φ := by
    -- The translated packing map is coordinatewise continuous, so its preimage preserves openness.
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · simpa [φ] using
        (continuous_const.add (continuous_fst : Continuous fun q : ℂ × ℂ ↦ q.1))
    · simpa [φ] using
        (continuous_const.add (continuous_snd : Continuous fun q : ℂ × ℂ ↦ q.2))
  have hpreOpen : IsOpen (φ ⁻¹' D2) := hD2.preimage hφcont
  have hzero : (0 : ℂ × ℂ) ∈ φ ⁻¹' D2 := by
    have hφzero : φ (0, 0) = z := by
      ext i
      fin_cases i <;> simp [φ]
    change φ (0, 0) ∈ D2
    rw [hφzero]
    exact hz
  rcases Metric.isOpen_iff.mp hpreOpen (0 : ℂ × ℂ) hzero with ⟨r, hrpos, hrball⟩
  refine ⟨r, hrpos, ?_⟩
  intro q hq1 hq2
  have hqBall : q ∈ Metric.ball (0 : ℂ × ℂ) r := by
    have hqDist : dist q (0 : ℂ × ℂ) < r := by
      rw [Prod.dist_eq, max_lt_iff]
      simpa [dist_eq_norm] using And.intro hq1 hq2
    simpa [Metric.mem_ball] using hqDist
  exact hrball hqBall

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: the coordinate-unpacking map
`z ↦ (z 0, z 1)` from `Fin 2 → ℂ` to `ℂ × ℂ` is jointly analytic. -/
lemma analyticAt_fin2Unpack (z : Fin 2 → ℂ) :
    AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ (w 0, w 1)) z := by
  -- The unpacking map is a continuous linear projection pair.
  simpa using
    (ContinuousLinearMap.analyticAt
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).prod
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1)) z)

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: after transporting a `Fin 2`-indexed
family to product coordinates, the separate analyticity hypotheses become analyticity in the two
product variables with no remaining `Function.update` noise. -/
lemma fin2SeparateAnalyticity_prodCoordinates
    {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ}
    (hsep2 :
      ∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) :
    let pack : ℂ × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1, p.2]
    let G : ℂ × ℂ → ℂ := F ∘ pack
    let D : Set (ℂ × ℂ) := pack ⁻¹' D2
    ∀ p ∈ D,
      AnalyticAt ℂ (fun w ↦ G (w, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2 := by
  dsimp
  intro p hp
  have hp' : ![p.1, p.2] ∈ D2 := hp
  constructor
  · -- The first product-coordinate slice is exactly the first `Fin 2` coordinate slice.
    convert hsep2 ![p.1, p.2] hp' 0 using 1
    funext w
    congr 1
    ext i <;> fin_cases i <;> simp [Function.update]
  · -- The second product-coordinate slice is exactly the second `Fin 2` coordinate slice.
    convert hsep2 ![p.1, p.2] hp' 1 using 1
    funext w
    congr 1
    ext i <;> fin_cases i <;> simp [Function.update]

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the transported product pullback
is analytic at the unpacked point, composing back with the analytic unpacking map returns the
original `Fin 2` germ. -/
lemma analyticAt_of_fin2ProdPullback
    {F : (Fin 2 → ℂ) → ℂ} {G : ℂ × ℂ → ℂ} {z : Fin 2 → ℂ}
    (hGAt : AnalyticAt ℂ G (z 0, z 1))
    (hEq : (fun w : Fin 2 → ℂ ↦ G (w 0, w 1)) = F) :
    AnalyticAt ℂ F z := by
  have hFGerm :
      AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ G (w 0, w 1)) z := by
    -- Compose the product germ with the analytic unpacking map once in the exact target shape.
    simpa using hGAt.comp (f := fun w : Fin 2 → ℂ ↦ (w 0, w 1)) (x := z) (analyticAt_fin2Unpack z)
  -- Compose the transported product germ back with the analytic unpacking map.
  simpa [hEq] using hFGerm

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: fixing the second translated
product coordinate inside the half-radius disc leaves an analytic first-coordinate slice on the
corresponding closed half-radius disc. -/
lemma translatedBidiscFirstSlice_analyticOnNhd_closedHalfBall_local
    {F : (Fin 2 → ℂ) → ℂ} {z : Fin 2 → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hsep :
      ∀ q : ℂ × ℂ, ‖q.1‖ < r → ‖q.2‖ < r →
        AnalyticAt ℂ (fun u ↦ F ![z 0 + u, z 1 + q.2]) q.1 ∧
          AnalyticAt ℂ (fun u ↦ F ![z 0 + q.1, z 1 + u]) q.2) :
    ∀ w ∈ Metric.ball (0 : ℂ) (r / 2),
      AnalyticOnNhd ℂ (fun u ↦ F ![z 0 + u, z 1 + w]) (Metric.closedBall (0 : ℂ) (r / 2)) := by
  intro w hw u hu
  have hw_half : ‖w‖ < r / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hw_lt : ‖w‖ < r := by
    linarith
  have hu_le : ‖u‖ ≤ r / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hu_lt : ‖u‖ < r := by
    linarith
  -- Evaluate the first-coordinate slice package at the chosen point of the smaller closed disc.
  simpa using (hsep (u, w) hu_lt hw_lt).1

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: fixing the first translated
product coordinate inside the half-radius disc leaves an analytic second-coordinate slice on the
corresponding closed half-radius disc. -/
lemma translatedBidiscSecondSlice_analyticOnNhd_closedHalfBall_local
    {F : (Fin 2 → ℂ) → ℂ} {z : Fin 2 → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hsep :
      ∀ q : ℂ × ℂ, ‖q.1‖ < r → ‖q.2‖ < r →
        AnalyticAt ℂ (fun u ↦ F ![z 0 + u, z 1 + q.2]) q.1 ∧
          AnalyticAt ℂ (fun u ↦ F ![z 0 + q.1, z 1 + u]) q.2) :
    ∀ w ∈ Metric.ball (0 : ℂ) (r / 2),
      AnalyticOnNhd ℂ (fun u ↦ F ![z 0 + w, z 1 + u]) (Metric.closedBall (0 : ℂ) (r / 2)) := by
  intro w hw u hu
  have hw_half : ‖w‖ < r / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hw_lt : ‖w‖ < r := by
    linarith
  have hu_le : ‖u‖ ≤ r / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hu_lt : ‖u‖ < r := by
    linarith
  -- Evaluate the second-coordinate slice package at the chosen point of the smaller closed disc.
  simpa using (hsep (w, u) hw_lt hu_lt).2

 /-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: every interior point of the translated
bidisc carries a smaller centered bidisc that still stays inside the original radius-`r` bidisc in
both coordinates. -/
lemma translatedBidisc_shrinkAroundPoint_local
    {r : ℝ} {p : ℂ × ℂ}
    (hp : p ∈ Metric.ball (0 : ℂ) r ×ˢ Metric.ball (0 : ℂ) r) :
    ∃ s : ℝ, 0 < s ∧
      ∀ q : ℂ × ℂ, ‖q.1‖ < s → ‖q.2‖ < s →
        ‖p.1 + q.1‖ < r ∧ ‖p.2 + q.2‖ < r := by
  have hp1 : ‖p.1‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp.1
  have hp2 : ‖p.2‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hp.2
  let s : ℝ := min (r - ‖p.1‖) (r - ‖p.2‖) / 2
  have hs_pos : 0 < s := by
    have hs1 : 0 < r - ‖p.1‖ := sub_pos.mpr hp1
    have hs2 : 0 < r - ‖p.2‖ := sub_pos.mpr hp2
    have hmin : 0 < min (r - ‖p.1‖) (r - ‖p.2‖) := lt_min hs1 hs2
    dsimp [s]
    linarith
  refine ⟨s, hs_pos, ?_⟩
  intro q hq1 hq2
  have hs_lt1 : s < r - ‖p.1‖ := by
    dsimp [s]
    have hs1 : 0 < r - ‖p.1‖ := sub_pos.mpr hp1
    have hs2 : 0 < r - ‖p.2‖ := sub_pos.mpr hp2
    linarith [min_le_left (r - ‖p.1‖) (r - ‖p.2‖)]
  have hs_lt2 : s < r - ‖p.2‖ := by
    dsimp [s]
    have hs1 : 0 < r - ‖p.1‖ := sub_pos.mpr hp1
    have hs2 : 0 < r - ‖p.2‖ := sub_pos.mpr hp2
    linarith [min_le_right (r - ‖p.1‖) (r - ‖p.2‖)]
  constructor
  · -- The first coordinate stays in the original radius-`r` disc by the triangle inequality.
    calc
      ‖p.1 + q.1‖ ≤ ‖p.1‖ + ‖q.1‖ := norm_add_le _ _
      _ < r := by
        linarith
  · -- The second coordinate obeys the same centered-bidisc estimate.
    calc
      ‖p.2 + q.2‖ ≤ ‖p.2‖ + ‖q.2‖ := norm_add_le _ _
      _ < r := by
        linarith

/-- Helper for Cartan section17 0002_Theorem_IV_5_extra_2: once the `Fin 1 × ℂ` product Hartogs
owner is supplied explicitly, the `Fin 2` case is only the coordinate pack/unpack transport. -/
lemma separatelyHolomorphicFin2_analyticOnNhd_ofProdHartogs_local
    (prodHartogs :
      ∀ {D : Set ((Fin 1 → ℂ) × ℂ)} {G : ((Fin 1 → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ G (w, p.2)) p.1 ∧
            AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) →
        AnalyticOnNhd ℂ G D)
    {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ}
    (hD2 : IsOpen D2)
    (hsep2 :
      ∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ F D2 := by
  intro z hz
  let pack : (Fin 1 → ℂ) × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1 0, p.2]
  let unpack : (Fin 2 → ℂ) → (Fin 1 → ℂ) × ℂ := fun w ↦ ((fun _ : Fin 1 ↦ w 0), w 1)
  let G : ((Fin 1 → ℂ) × ℂ) → ℂ := F ∘ pack
  let D : Set ((Fin 1 → ℂ) × ℂ) := pack ⁻¹' D2
  have hPackCont : Continuous pack := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · simpa [pack] using
        (continuous_apply 0).comp
          (continuous_fst : Continuous fun p : (Fin 1 → ℂ) × ℂ ↦ p.1)
    · simpa [pack] using (continuous_snd : Continuous fun p : (Fin 1 → ℂ) × ℂ ↦ p.2)
  have hD : IsOpen D := hD2.preimage hPackCont
  have hPackUnpack : ∀ w : Fin 2 → ℂ, pack (unpack w) = w := by
    intro w
    ext i <;> fin_cases i <;> simp [pack, unpack]
  have hzD : unpack z ∈ D := by
    change pack (unpack z) ∈ D2
    simpa [hPackUnpack z] using hz
  have hsepProd :
      ∀ p ∈ D,
        AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ G (w, p.2)) p.1 ∧
          AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2 := by
    intro p hp
    have hp' : pack p ∈ D2 := hp
    constructor
    · have hslice :
          AnalyticAt ℂ (fun w ↦ F (Function.update (pack p) 0 w)) ((pack p) 0) :=
        hsep2 (pack p) hp' 0
      have hEval : AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ w 0) p.1 := by
        simpa using
          (ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0) p.1)
      have hComp :
          AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ F (Function.update (pack p) 0 (w 0))) p.1 := by
        simpa [pack] using hslice.comp (f := fun w : Fin 1 → ℂ ↦ w 0) (x := p.1) hEval
      have hArgEq :
          ∀ w : Fin 1 → ℂ, pack (w, p.2) = Function.update (pack p) 0 (w 0) := by
        intro w
        ext i <;> fin_cases i <;> simp [pack, Function.update]
      have hEq :
          (fun w : Fin 1 → ℂ ↦ G (w, p.2)) =
            (fun w : Fin 1 → ℂ ↦ F (Function.update (pack p) 0 (w 0))) := by
        funext w
        simp [G, Function.comp, hArgEq w]
      simpa [hEq] using hComp
    · have hslice :
          AnalyticAt ℂ (fun w ↦ F (Function.update (pack p) 1 w)) ((pack p) 1) :=
        hsep2 (pack p) hp' 1
      have hArgEq : ∀ w : ℂ, pack (p.1, w) = Function.update (pack p) 1 w := by
        intro w
        ext i <;> fin_cases i <;> simp [pack, Function.update]
      have hEq :
          (fun w : ℂ ↦ G (p.1, w)) = (fun w : ℂ ↦ F (Function.update (pack p) 1 w)) := by
        funext w
        simp [G, Function.comp, hArgEq w]
      simpa [hEq] using hslice
  have hGOn : AnalyticOnNhd ℂ G D := prodHartogs hD hsepProd
  have hGAt : AnalyticAt ℂ G (unpack z) := hGOn (unpack z) hzD
  have hUnpackAt : AnalyticAt ℂ unpack z := by
    have hFirst :
        AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ fun _ : Fin 1 ↦ w 0) z := by
      refine AnalyticAt.pi fun i ↦ ?_
      fin_cases i
      simpa using
        (ContinuousLinearMap.analyticAt
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0) z)
    have hSecond : AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ w 1) z := by
      simpa using
        (ContinuousLinearMap.analyticAt
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) z)
    simpa [unpack] using hFirst.prod hSecond
  have hEq : (fun w : Fin 2 → ℂ ↦ G (unpack w)) = F := by
    funext w
    simpa [G, unpack, hPackUnpack w]
  have hFGerm : AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ G (unpack w)) z := by
    simpa using hGAt.comp (f := unpack) (x := z) hUnpackAt
  simpa [hEq] using hFGerm
