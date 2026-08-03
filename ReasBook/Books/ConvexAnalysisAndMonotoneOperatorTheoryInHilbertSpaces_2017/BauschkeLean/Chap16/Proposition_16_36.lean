import Mathlib
import BauschkeLean.Chap02.Lemma_2_51
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Theorem_9_1
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

section SubdifferentialGraphClosedness

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 16.36: for a `Γ₀(H)` function, subdifferential membership is exactly
Fenchel--Young equality. -/
private theorem mem_subdifferential_iff_fenchel_young_eq_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- Proposition 16.10 already proves the contact equivalence once the effective domain is known
  -- to be nonempty.
  simpa using mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty x u

/-- Helper for Proposition 16.36: members of `Γ₀(H)` are weakly sequentially lower
semicontinuous. -/
private theorem gammaZero_seq_lsc_weak
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {xSeq : ℕ → H} {x : H}
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x))) :
    (f x : EReal) ≤ Filter.liminf (fun n ↦ (f (xSeq n) : EReal)) atTop := by
  -- Read the weak sequential clause directly from Theorem 9.1.
  have htfae :
      List.TFAE
        [ (∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (toWeakSpace ℝ H y)) →
                f.asEReal y ≤ Filter.liminf (f.asEReal ∘ u) atTop),
          (∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
              Tendsto u atTop (𝓝 y) →
                f.asEReal y ≤ Filter.liminf (f.asEReal ∘ u) atTop),
          LowerSemicontinuous f.asEReal,
          WeaklyLowerSemicontinuous f.asEReal ] := by
    exact convex_lowerSemicontinuity_tfae
      (convex_epigraph_asEReal_of_mem_gammaZero hf)
  have hweak_seq :
      ∀ ⦃u : ℕ → H⦄ ⦃y : H⦄,
        Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop (𝓝 (toWeakSpace ℝ H y)) →
          f.asEReal y ≤ Filter.liminf (f.asEReal ∘ u) atTop := by
    exact (List.TFAE.out htfae 0 2).2 hf.1
  simpa [Function.comp] using hweak_seq hx

/-- Helper for Proposition 16.36: the epigraph of a convex extended-real-valued function is
convex. -/
private theorem convex_epigraph_of_isConvex
    {g : H → EReal} (hg : IsConvex g) :
    Convex ℝ (epigraph g) := by
  -- The Jensen form of convexity is exactly the epigraph convexity criterion.
  refine (convex_epigraph_iff_jensen_on_dom g).2 ?_
  intro x y hx hy a ha0 ha1
  exact hg ha0.le ha1.le

/-- Helper for Proposition 16.36: the Fenchel conjugate is strongly sequentially lower
semicontinuous. -/
private theorem conjugate_seq_lsc_strong
    (f : H → Set.Ioi (⊥ : EReal)) {uSeq : ℕ → H} {u : H}
    (hu : Tendsto uSeq atTop (𝓝 u)) :
    f.asEReal∗ u ≤ Filter.liminf (fun n ↦ f.asEReal∗ (uSeq n)) atTop := by
  -- Proposition 13.13 places the raw conjugate in `Γ(H)`, and the sequential characterization of
  -- `Γ(H)` then gives the required liminf inequality.
  have hgamma : f.asEReal∗ ∈ Γ(H) := conjugate_mem_gamma f.asEReal
  exact ((mem_gamma_iff_seq_tendsto_le_liminf (H := H) f.asEReal∗).1 hgamma).2 hu

/-- Helper for Proposition 16.36: the Fenchel conjugate is weakly sequentially lower
semicontinuous. -/
private theorem conjugate_seq_lsc_weak
    (f : H → Set.Ioi (⊥ : EReal)) {uSeq : ℕ → H} {u : H}
    (hu :
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H u))) :
    f.asEReal∗ u ≤ Filter.liminf (fun n ↦ f.asEReal∗ (uSeq n)) atTop := by
  -- Theorem 9.1 upgrades strong lower semicontinuity of the raw conjugate to weak sequential
  -- lower semicontinuity because its epigraph is convex.
  have hgamma : f.asEReal∗ ∈ Γ(H) := conjugate_mem_gamma f.asEReal
  have hgamma_data : IsConvex f.asEReal∗ ∧ LowerSemicontinuous f.asEReal∗ :=
    (mem_gamma_iff (H := H) f.asEReal∗).1 hgamma
  have htfae :
      List.TFAE
        [ (∀ ⦃v : ℕ → H⦄ ⦃y : H⦄,
              Tendsto (fun n ↦ toWeakSpace ℝ H (v n)) atTop (𝓝 (toWeakSpace ℝ H y)) →
                f.asEReal∗ y ≤ Filter.liminf (f.asEReal∗ ∘ v) atTop),
          (∀ ⦃v : ℕ → H⦄ ⦃y : H⦄,
              Tendsto v atTop (𝓝 y) →
                f.asEReal∗ y ≤ Filter.liminf (f.asEReal∗ ∘ v) atTop),
          LowerSemicontinuous f.asEReal∗,
          WeaklyLowerSemicontinuous f.asEReal∗ ] := by
    exact convex_lowerSemicontinuity_tfae
      (convex_epigraph_of_isConvex hgamma_data.1)
  have hweak_seq :
      ∀ ⦃v : ℕ → H⦄ ⦃y : H⦄,
        Tendsto (fun n ↦ toWeakSpace ℝ H (v n)) atTop (𝓝 (toWeakSpace ℝ H y)) →
          f.asEReal∗ y ≤ Filter.liminf (f.asEReal∗ ∘ v) atTop := by
    exact (List.TFAE.out htfae 0 2).2 hgamma_data.2
  simpa [Function.comp] using hweak_seq hu

/-- Helper for Proposition 16.36: weak convergence in a pre-Hilbert space still forces a
norm-bounded range, by passing to the weak-star bidual and pulling the norm bound back through the
canonical isometric embedding. -/
private theorem bounded_range_of_tendsto_toWeakSpace_prehilbert
    {xSeq : ℕ → H} {x : H}
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x))) :
    Bornology.IsBounded (Set.range xSeq) := by
  let ySeq : ℕ → WeakDual ℝ (StrongDual ℝ H) := fun n ↦
    NormedSpace.inclusionInDoubleDualWeak ℝ H (toWeakSpace ℝ H (xSeq n))
  -- The weakly convergent sequence becomes weak-star convergent in the bidual.
  have hy :
      Tendsto ySeq atTop
        (𝓝 (NormedSpace.inclusionInDoubleDualWeak ℝ H (toWeakSpace ℝ H x))) := by
    simpa [ySeq] using
      ((NormedSpace.inclusionInDoubleDualWeak ℝ H).continuous.tendsto
        (toWeakSpace ℝ H x)).comp hx
  have hy_vN : Bornology.IsVonNBounded ℝ (Set.range ySeq) :=
    hy.isVonNBounded_range ℝ
  have hy_bounded : Bornology.IsBounded (Set.range ySeq) := by
    rw [WeakDual.isBounded_iff_isVonNBounded]
    exact hy_vN
  have hbidual_bounded :
      Bornology.IsBounded
        (Set.range fun n ↦ WeakDual.toStrongDual (ySeq n)) := by
    rw [← WeakDual.isBounded_toStrongDual_preimage_iff_isBounded]
    exact hy_bounded.subset <| by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
  -- Pull the bidual norm bound back through the canonical linear isometry.
  refine
    ((NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := H)).antilipschitz.isBounded_preimage
      hbidual_bounded).subset ?_
  rintro z ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  ext l
  change StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ H (xSeq n)) l = l (xSeq n)
  simp [NormedSpace.dual_def]

/-- Helper for Proposition 16.36: weak convergence gives convergence of every fixed inner-product
coordinate, without any completeness hypothesis. -/
private theorem tendsto_inner_right_of_tendsto_toWeakSpace
    {xSeq : ℕ → H} {x v : H}
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x))) :
    Tendsto (fun n ↦ ⟪xSeq n, v⟫_ℝ) atTop (𝓝 ⟪x, v⟫_ℝ) := by
  -- Evaluate weak convergence against the fixed weak-dual functional induced by `innerSL ℝ v`.
  have hcont_id : Continuous (fun z : WeakSpace ℝ H ↦ z) := continuous_id
  have hweak_eval :
      Continuous fun z : WeakSpace ℝ H ↦
        StrongDual.toWeakDual (innerSL ℝ v) ((toWeakSpace ℝ H).symm z) :=
    (continuous_iff_forall_weakDual_apply (f := fun z : WeakSpace ℝ H ↦ z)).1 hcont_id
      (StrongDual.toWeakDual (innerSL ℝ v))
  have hEval := (hweak_eval.tendsto (toWeakSpace ℝ H x)).comp hx
  simpa [StrongDual.toWeakDual_apply, innerSL_apply_apply, real_inner_comm] using hEval

/-- Helper for Proposition 16.36: weak convergence in the first slot, strong convergence in the
second slot, and a bounded first range imply convergence of the pairing. -/
private theorem tendsto_inner_of_tendsto_toWeakSpace_of_tendsto_of_bounded_range
    {xSeq uSeq : ℕ → H} {x u : H}
    (hx_bounded : Bornology.IsBounded (Set.range xSeq))
    (hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H x)))
    (hu : Tendsto uSeq atTop (𝓝 u)) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  rcases isBounded_iff_forall_norm_le.mp hx_bounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC : ∀ n, ‖xSeq n‖ ≤ C := by
    intro n
    calc
      ‖xSeq n‖ ≤ C₀ := hC₀ _ (Set.mem_range_self n)
      _ ≤ max C₀ 0 := le_max_left _ _
      _ = C := rfl
  -- The fixed-vector pairing converges by weak continuity.
  have hfixed : Tendsto (fun n ↦ ⟪xSeq n, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
    exact tendsto_inner_right_of_tendsto_toWeakSpace hx
  have hdiff : Tendsto (fun n ↦ uSeq n - u) atTop (𝓝 (0 : H)) := by
    simpa using hu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ u) atTop (𝓝 u))
  have hnorm_diff : Tendsto (fun n ↦ ‖uSeq n - u‖) atTop (𝓝 0) := by
    simpa using hdiff.norm
  have hmul : Tendsto (fun n ↦ C * ‖uSeq n - u‖) atTop (𝓝 0) := by
    simpa using hnorm_diff.const_mul C
  -- The perturbation term is controlled by Cauchy-Schwarz and the bounded first range.
  have hpert_abs :
      Tendsto (fun n ↦ |⟪xSeq n, uSeq n - u⟫_ℝ|) atTop (𝓝 0) := by
    refine
      squeeze_zero' (f := fun n ↦ |⟪xSeq n, uSeq n - u⟫_ℝ|)
        (g := fun n ↦ C * ‖uSeq n - u‖)
        (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hmul
  have hpert : Tendsto (fun n ↦ ⟪xSeq n, uSeq n - u⟫_ℝ) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp] using hpert_abs
  have hsplit :
      (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) =
        fun n ↦ ⟪xSeq n, uSeq n - u⟫_ℝ + ⟪xSeq n, u⟫_ℝ := by
    funext n
    calc
      ⟪xSeq n, uSeq n⟫_ℝ = ⟪xSeq n, (uSeq n - u) + u⟫_ℝ := by
        congr 2
        abel
      _ = ⟪xSeq n, uSeq n - u⟫_ℝ + ⟪xSeq n, u⟫_ℝ := by
        rw [inner_add_right]
  rw [hsplit]
  simpa using hpert.add hfixed

/-- Helper for Proposition 16.36: the symmetric mixed-convergence pairing limit, obtained by
swapping the two inner-product slots. -/
private theorem tendsto_inner_of_tendsto_of_tendsto_toWeakSpace_of_bounded_range
    {xSeq uSeq : ℕ → H} {x u : H}
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hu_bounded : Bornology.IsBounded (Set.range uSeq))
    (hu :
      Tendsto (fun n ↦ toWeakSpace ℝ H (uSeq n)) atTop
        (𝓝 (toWeakSpace ℝ H u))) :
    Tendsto (fun n ↦ ⟪xSeq n, uSeq n⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  -- Swap the pairing slots and reuse the previous weak-strong lemma.
  have hswap :
      Tendsto (fun n ↦ ⟪uSeq n, xSeq n⟫_ℝ) atTop (𝓝 ⟪u, x⟫_ℝ) :=
    tendsto_inner_of_tendsto_toWeakSpace_of_tendsto_of_bounded_range hu_bounded hu hx
  simpa [real_inner_comm] using hswap

/-- Proposition 16.36 (1): if `f ∈ Γ₀(H)`, then the graph of the subdifferential is sequentially
closed in `H^weak × H^strong`, encoded as sequential closedness of its image in
`WeakSpace ℝ H × H`. -/
theorem graph_subdifferential_isSeqClosed_weakStrong_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    IsSeqClosed ((Prod.map (toWeakSpace ℝ H) id) '' (∂ f).graph) := by
  intro pₙ p hpₙ hp
  let x : H := (toWeakSpace ℝ H).symm p.1
  let u : H := p.2
  have hgraph : ∀ n, ((toWeakSpace ℝ H).symm (pₙ n).1, (pₙ n).2) ∈ (∂ f).graph := by
    intro n
    rcases hpₙ n with ⟨⟨xₙ, uₙ⟩, hxuₙ, hpₙ_eq⟩
    rw [← hpₙ_eq]
    simpa using hxuₙ
  have hx :
      Tendsto (fun n ↦ toWeakSpace ℝ H ((toWeakSpace ℝ H).symm (pₙ n).1)) atTop
        (𝓝 (toWeakSpace ℝ H x)) := by
    simpa [x] using (continuous_fst.tendsto p).comp hp
  have hu : Tendsto (fun n ↦ (pₙ n).2) atTop (𝓝 u) := by
    simpa [u] using (continuous_snd.tendsto p).comp hp
  have hx_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (toWeakSpace ℝ H).symm (pₙ n).1) :=
    bounded_range_of_tendsto_toWeakSpace_prehilbert hx
  have hinner :
      Tendsto (fun n ↦ ⟪(toWeakSpace ℝ H).symm (pₙ n).1, (pₙ n).2⟫_ℝ) atTop
        (𝓝 ⟪x, u⟫_ℝ) :=
    tendsto_inner_of_tendsto_toWeakSpace_of_tendsto_of_bounded_range hx_bounded hx hu
  have hinner_ereal :
      Tendsto
        (fun n ↦ (((⟪(toWeakSpace ℝ H).symm (pₙ n).1, (pₙ n).2⟫_ℝ : ℝ) : EReal)))
        atTop (𝓝 (((⟪x, u⟫_ℝ : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hinner
  have hcontact :
      ∀ n,
        (f ((toWeakSpace ℝ H).symm (pₙ n).1) : EReal) + f.asEReal∗ ((pₙ n).2) =
          (((⟪(toWeakSpace ℝ H).symm (pₙ n).1, (pₙ n).2⟫_ℝ : ℝ) : EReal)) := by
    intro n
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_mem_gammaZero hf
        ((toWeakSpace ℝ H).symm (pₙ n).1) ((pₙ n).2)).1 <| by
          simpa [SetValuedOperator.mem_graph] using hgraph n
  -- The source Fenchel-Young chain now closes directly.
  have hsum_le :
      (f x : EReal) + f.asEReal∗ u ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
    calc
      (f x : EReal) + f.asEReal∗ u
          ≤ Filter.liminf (fun n ↦ (f ((toWeakSpace ℝ H).symm (pₙ n).1) : EReal)) atTop +
              Filter.liminf (fun n ↦ f.asEReal∗ ((pₙ n).2)) atTop := by
                exact add_le_add (gammaZero_seq_lsc_weak hf hx) (conjugate_seq_lsc_strong f hu)
      _ ≤ Filter.liminf
            (fun n ↦
              (f ((toWeakSpace ℝ H).symm (pₙ n).1) : EReal) + f.asEReal∗ ((pₙ n).2)) atTop := by
            simpa using
              (EReal.le_liminf_add :
                Filter.liminf (fun n ↦ (f ((toWeakSpace ℝ H).symm (pₙ n).1) : EReal)) atTop +
                  Filter.liminf (fun n ↦ f.asEReal∗ ((pₙ n).2)) atTop ≤
                    Filter.liminf
                      (fun n ↦
                        (f ((toWeakSpace ℝ H).symm (pₙ n).1) : EReal) + f.asEReal∗ ((pₙ n).2))
                      atTop)
      _ = Filter.liminf
            (fun n ↦ (((⟪(toWeakSpace ℝ H).symm (pₙ n).1, (pₙ n).2⟫_ℝ : ℝ) : EReal))) atTop := by
            exact Filter.liminf_congr (Eventually.of_forall hcontact)
      _ = (((⟪x, u⟫_ℝ : ℝ) : EReal)) := hinner_ereal.liminf_eq
  have hfy :
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ (f x : EReal) + f.asEReal∗ u := by
    -- The ambient Fenchel-Young inequality provides the reverse inequality at the limit point.
    simpa using
      fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) x u
  have hmem : u ∈ (∂ f) x :=
    (mem_subdifferential_iff_fenchel_young_eq_of_mem_gammaZero hf x u).2 <|
      le_antisymm hsum_le hfy
  refine ⟨(x, u), ?_, ?_⟩
  · simpa [SetValuedOperator.mem_graph] using hmem
  · simp [x, u]

/-- Proposition 16.36 (2): if `f ∈ Γ₀(H)`, then the graph of the subdifferential is sequentially
closed in `H^strong × H^weak`, encoded as sequential closedness of its image in
`H × WeakSpace ℝ H`. -/
theorem graph_subdifferential_isSeqClosed_strongWeak_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    IsSeqClosed ((Prod.map id (toWeakSpace ℝ H)) '' (∂ f).graph) := by
  intro pₙ p hpₙ hp
  let x : H := p.1
  let u : H := (toWeakSpace ℝ H).symm p.2
  have hgraph : ∀ n, ((pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2) ∈ (∂ f).graph := by
    intro n
    rcases hpₙ n with ⟨⟨xₙ, uₙ⟩, hxuₙ, hpₙ_eq⟩
    rw [← hpₙ_eq]
    simpa using hxuₙ
  have hx : Tendsto (fun n ↦ (pₙ n).1) atTop (𝓝 x) := by
    simpa [x] using (continuous_fst.tendsto p).comp hp
  have hu :
      Tendsto (fun n ↦ toWeakSpace ℝ H ((toWeakSpace ℝ H).symm (pₙ n).2)) atTop
        (𝓝 (toWeakSpace ℝ H u)) := by
    simpa [u] using (continuous_snd.tendsto p).comp hp
  have hu_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (toWeakSpace ℝ H).symm (pₙ n).2) :=
    bounded_range_of_tendsto_toWeakSpace_prehilbert hu
  have hinner :
      Tendsto (fun n ↦ ⟪(pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2⟫_ℝ) atTop
        (𝓝 ⟪x, u⟫_ℝ) :=
    tendsto_inner_of_tendsto_of_tendsto_toWeakSpace_of_bounded_range hx hu_bounded hu
  have hinner_ereal :
      Tendsto
        (fun n ↦ (((⟪(pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2⟫_ℝ : ℝ) : EReal)))
        atTop (𝓝 (((⟪x, u⟫_ℝ : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hinner
  have hcontact :
      ∀ n,
        (f ((pₙ n).1) : EReal) + f.asEReal∗ ((toWeakSpace ℝ H).symm (pₙ n).2) =
          (((⟪(pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2⟫_ℝ : ℝ) : EReal)) := by
    intro n
    exact
      (mem_subdifferential_iff_fenchel_young_eq_of_mem_gammaZero hf
        ((pₙ n).1) ((toWeakSpace ℝ H).symm (pₙ n).2)).1 <| by
          simpa [SetValuedOperator.mem_graph] using hgraph n
  have hx_lsc :
      (f x : EReal) ≤ Filter.liminf (fun n ↦ (f ((pₙ n).1) : EReal)) atTop := by
    -- The primal variable converges strongly, so the standard `Γ(H)` sequential liminf estimate
    -- applies to `f.asEReal`.
    simpa [Function.comp, x] using
      ((mem_gamma_iff_seq_tendsto_le_liminf (H := H) f.asEReal).1
        (asEReal_mem_gamma_of_mem_gammaZero hf)).2 hx
  have hsum_le :
      (f x : EReal) + f.asEReal∗ u ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
    calc
      (f x : EReal) + f.asEReal∗ u
          ≤ Filter.liminf (fun n ↦ (f ((pₙ n).1) : EReal)) atTop +
              Filter.liminf
                (fun n ↦ f.asEReal∗ ((toWeakSpace ℝ H).symm (pₙ n).2)) atTop := by
                  exact add_le_add hx_lsc (conjugate_seq_lsc_weak f hu)
      _ ≤ Filter.liminf
            (fun n ↦
              (f ((pₙ n).1) : EReal) + f.asEReal∗ ((toWeakSpace ℝ H).symm (pₙ n).2)) atTop := by
            simpa using
              (EReal.le_liminf_add :
                Filter.liminf (fun n ↦ (f ((pₙ n).1) : EReal)) atTop +
                  Filter.liminf
                    (fun n ↦ f.asEReal∗ ((toWeakSpace ℝ H).symm (pₙ n).2)) atTop ≤
                    Filter.liminf
                      (fun n ↦
                        (f ((pₙ n).1) : EReal) +
                          f.asEReal∗ ((toWeakSpace ℝ H).symm (pₙ n).2))
                      atTop)
      _ = Filter.liminf
            (fun n ↦ (((⟪(pₙ n).1, (toWeakSpace ℝ H).symm (pₙ n).2⟫_ℝ : ℝ) : EReal))) atTop := by
            exact Filter.liminf_congr (Eventually.of_forall hcontact)
      _ = (((⟪x, u⟫_ℝ : ℝ) : EReal)) := hinner_ereal.liminf_eq
  have hfy :
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) ≤ (f x : EReal) + f.asEReal∗ u := by
    -- The same Fenchel-Young inequality closes the reverse direction at the limit point.
    simpa using
      fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) x u
  have hmem : u ∈ (∂ f) x :=
    (mem_subdifferential_iff_fenchel_young_eq_of_mem_gammaZero hf x u).2 <|
      le_antisymm hsum_le hfy
  refine ⟨(x, u), ?_, ?_⟩
  · simpa [SetValuedOperator.mem_graph] using hmem
  · simp [x, u]

end SubdifferentialGraphClosedness

end ERealFunction
