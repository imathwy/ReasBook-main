import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0004_Definition_II_1_extra_4»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

namespace Path

/-- Helper for Cartan section05 0005_Proposition_2_1: every subdivision piece of a piecewise
differentiable path stays inside the unit interval. -/
lemma subdivision_piece_subset_unitInterval
    {n : ℕ} {subdiv : Fin (n + 2) → ℝ} (hsubdiv : StrictMono subdiv)
    (h0 : subdiv 0 = 0) (h1 : subdiv (Fin.last (n + 1)) = 1) :
    ∀ i : Fin (n + 1), Set.Icc (subdiv i.castSucc) (subdiv i.succ) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro i t ht
  constructor
  · -- The left endpoint of each subdivision piece stays to the right of `0`.
    calc
      0 = subdiv 0 := by symm; exact h0
      _ ≤ subdiv i.castSucc := hsubdiv.monotone (Fin.zero_le _)
      _ ≤ t := ht.1
  · -- The right endpoint of each subdivision piece stays to the left of `1`.
    calc
      t ≤ subdiv i.succ := ht.2
      _ ≤ subdiv (Fin.last (n + 1)) := hsubdiv.monotone i.succ.le_last
      _ = 1 := h1

/-- Helper for Cartan section05 0005_Proposition_2_1: on one `C¹` subdivision piece, a continuous
`G`-valued `1`-form yields an interval-integrable pullback integrand. -/
lemma curveIntegral_intervalIntegrable_on_piece
    {x y : E} {γ : Path x y} {l u : ℝ} (hlt : l < u)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc l u)) {ω : E → E →L[ℝ] G}
    (hω : ContinuousOn ω (γ.extend '' Set.Icc l u)) :
    IntervalIntegrable (fun t ↦ ω (γ.extend t) (deriv γ.extend t)) MeasureTheory.volume l u := by
  have hDerivWithin :
      ContinuousOn (fun t ↦ derivWithin γ.extend (Set.Icc l u) t) (Set.Icc l u) := by
    -- Replace the ordinary derivative by the continuous within-derivative on the closed piece.
    exact (hγ.derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
  have hωAlong : ContinuousOn (fun t ↦ ω (γ.extend t)) (Set.Icc l u) := by
    -- Pull the coefficient field back along the path extension.
    refine hω.comp (by fun_prop) ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIntWithin :
      IntervalIntegrable (fun t ↦ ω (γ.extend t) (derivWithin γ.extend (Set.Icc l u) t))
        MeasureTheory.volume l u :=
    (hωAlong.clm_apply hDerivWithin).intervalIntegrable_of_Icc hlt.le
  -- On the interior of the piece, the within-derivative agrees with the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  rw [Set.uIoc_of_le hlt.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  exact by simp [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Cartan section05 0005_Proposition_2_1: a continuous `G`-valued differential form is
curve-integrable along every piecewise differentiable path whose image stays in the domain. -/
lemma curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
    {D : Set E} {ω : E → E →L[ℝ] G} {x y : E} {γ : Path x y}
    (hω : ContinuousOn ω D) (hγ : γ.IsPiecewiseDifferentiable) (hγD : Set.range γ ⊆ D) :
    CurveIntegrable ω γ := by
  rcases hγ with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hCoeff :
      ∀ i : Fin (n + 1), ContinuousOn ω (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    -- Restrict the ambient continuity hypothesis to the image of the current subdivision piece.
    refine hω.mono ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
    simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
  let a : ℕ → ℝ := fun k ↦
    if hk : k ≤ n + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
  have hInt :
      IntervalIntegrable (fun t ↦ ω (γ.extend t) (deriv γ.extend t)) MeasureTheory.volume
        (a 0) (a (n + 1)) := by
    -- Reassemble the interval-integrable pullback from the finitely many `C¹` pieces.
    refine IntervalIntegrable.trans_iterate ?_
    intro k hk
    let i : Fin (n + 1) := ⟨k, hk⟩
    have hk0 : k ≤ n + 1 := Nat.le_of_lt hk
    have hk1 : k + 1 ≤ n + 1 := Nat.succ_le_of_lt hk
    have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
    simpa [a, i, hk0, hk1] using
      curveIntegral_intervalIntegrable_on_piece (γ := γ) hlt (hpieces i) (hCoeff i)
  have h0' : a 0 = 0 := by simp [a, h0]
  have h1' : a (n + 1) = 1 := by simpa [a] using h1
  rw [CurveIntegrable]
  have hInt' :
      IntervalIntegrable (fun t ↦ ω (γ.extend t) (deriv γ.extend t)) MeasureTheory.volume 0 1 := by
    simpa [h0', h1'] using hInt
  -- Replace the ordinary derivative by the within-derivative used in `curveIntegralFun`.
  refine hInt'.congr_ae ?_
  rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  simp [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Cartan section05 0005_Proposition_2_1: reversing a piecewise differentiable path
preserves piecewise differentiability. -/
lemma IsPiecewiseDifferentiable.symm {x y : E} {γ : Path x y}
    (hγ : γ.IsPiecewiseDifferentiable) :
    γ.symm.IsPiecewiseDifferentiable := by
  rcases hγ with ⟨n, subdiv, hsubdiv, h0, h1, hpieces⟩
  let subdiv' : Fin (n + 2) → ℝ := fun i ↦ 1 - subdiv (Fin.rev i)
  have hsubdiv' : StrictMono subdiv' := by
    -- Reverse the subdivision order and use the affine reparametrization `t ↦ 1 - t`.
    intro i j hij
    dsimp [subdiv']
    have hrev : Fin.rev j < Fin.rev i := (Fin.rev_lt_rev).2 hij
    have hlt : subdiv (Fin.rev j) < subdiv (Fin.rev i) := hsubdiv hrev
    linarith
  refine ⟨n, subdiv', hsubdiv', ?_, ?_, ?_⟩
  · -- The reversed subdivision still starts at `0`.
    simp [subdiv', h1]
  · -- The reversed subdivision still ends at `1`.
    simp [subdiv', h0]
  · intro i
    -- On each reversed piece, compose the original `C¹` witness with `t ↦ 1 - t`.
    have hparam :
        ContDiffOn ℝ 1 (fun t : ℝ ↦ 1 - t)
          (Set.Icc (subdiv' i.castSucc) (subdiv' i.succ)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        contDiffOn_affine_reparam (-1) 1
          (Set.Icc (subdiv' i.castSucc) (subdiv' i.succ))
    have hmaps :
        Set.MapsTo (fun t : ℝ ↦ 1 - t)
          (Set.Icc (subdiv' i.castSucc) (subdiv' i.succ))
          (Set.Icc (subdiv i.rev.castSucc) (subdiv i.rev.succ)) := by
      intro t ht
      rcases ht with ⟨htlo, hthi⟩
      constructor <;> linarith
        [show subdiv' i.castSucc = 1 - subdiv i.rev.succ by
            simp [subdiv', Fin.rev_castSucc]
        , show subdiv' i.succ = 1 - subdiv i.rev.castSucc by
            simp [subdiv', Fin.rev_succ]]
    have hpiece :
        ContDiffOn ℝ 1 (fun t ↦ γ.extend (1 - t))
          (Set.Icc (subdiv' i.castSucc) (subdiv' i.succ)) :=
      (hpieces (Fin.rev i)).comp hparam hmaps
    have heq :
        Set.EqOn γ.symm.extend (fun t ↦ γ.extend (1 - t))
          (Set.Icc (subdiv' i.castSucc) (subdiv' i.succ)) := by
      intro t _ht
      simp [Path.extend_symm]
    simpa [subdiv'] using hpiece.congr heq

/-- Helper for Cartan section05 0005_Proposition_2_1: concatenating two piecewise differentiable
paths preserves piecewise differentiability. -/
lemma IsPiecewiseDifferentiable.trans {x y z : E} {γ₁ : Path x y} {γ₂ : Path y z}
    (hγ₁ : γ₁.IsPiecewiseDifferentiable) (hγ₂ : γ₂.IsPiecewiseDifferentiable) :
    (γ₁.trans γ₂).IsPiecewiseDifferentiable := by
  rcases hγ₁ with ⟨n, subdiv₁, hsubdiv₁, h0₁, h1₁, hpieces₁⟩
  rcases hγ₂ with ⟨m, subdiv₂, hsubdiv₂, h0₂, h1₂, hpieces₂⟩
  let left : Fin (n + 1) → ℝ := fun i ↦ subdiv₁ i.castSucc / 2
  let right : Fin (m + 2) → ℝ := fun i ↦ (1 + subdiv₂ i) / 2
  let subdiv : Fin (((n + 1) + m) + 2) → ℝ := @Fin.append (n + 1) (m + 2) _ left right
  refine ⟨(n + 1) + m, subdiv, ?_, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    change subdiv j.castSucc < subdiv j.succ
    refine @Fin.addCases (n + 1) (m + 1) (fun k ↦ subdiv k.castSucc < subdiv k.succ) ?_ ?_ j
    · intro i
      cases i using Fin.lastCases with
      | cast i =>
          -- On the left part, the new subdivision is just the rescaled subdivision of `γ₁`.
          have hlt' : subdiv₁ i.castSucc.castSucc < subdiv₁ i.succ.castSucc := by
            apply hsubdiv₁
            simp
          have hlt : subdiv₁ i.castSucc.castSucc < subdiv₁ i.castSucc.succ := by
            simpa only [Fin.succ_castSucc] using hlt'
          have hs :
              (Fin.castAdd (m + 2) i.succ : Fin (n + 1 + m + 2)) =
                (Fin.castAdd (m + 1) i.castSucc).succ := by
            ext
            simp [Fin.succ_castAdd]
          rw [← hs]
          simp [subdiv, Fin.castSucc_castAdd, Fin.append_left]
          dsimp [left, right] at *
          linarith
      | last =>
          -- The boundary node `1/2` is shared between the two rescaled subdivisions.
          have hs :
              (Fin.natAdd (n + 1) (0 : Fin (m + 2)) : Fin (n + 1 + m + 2)) =
                (Fin.castAdd (m + 1) (Fin.last n)).succ := by
            ext
            simp [Fin.succ_castAdd]
          rw [← hs]
          simp [subdiv, Fin.castSucc_castAdd, Fin.append_left, Fin.append_right, h0₂]
          have hlt : subdiv₁ (Fin.last n).castSucc < subdiv₁ (Fin.last n).succ :=
            hsubdiv₁ (Fin.last n).castSucc_lt_succ
          have hlt' : subdiv₁ (Fin.last n).castSucc < 1 := by
            simpa [Fin.succ_last, h1₁] using hlt
          dsimp [left, right] at *
          linarith
    · intro i
      -- On the right part, the new subdivision is the shifted subdivision of `γ₂`.
      rw [Fin.castSucc_natAdd, Fin.succ_natAdd]
      simp [subdiv, Fin.append_right]
      have hlt : subdiv₂ i.castSucc < subdiv₂ i.succ := hsubdiv₂ i.castSucc_lt_succ
      dsimp [left, right] at *
      linarith
  · -- The rescaled concatenation still starts at `0`.
    have hzero :
        (0 : Fin (((n + 1) + m) + 2)) = Fin.castAdd (m + 2) (0 : Fin (n + 1)) := by
      ext
      simp
    simpa [subdiv, left, h0₁, hzero] using (Fin.append_left left right (0 : Fin (n + 1)))
  · -- The shifted subdivision still ends at `1`.
    have hlast :
        (Fin.last (((n + 1) + m) + 1) : Fin (((n + 1) + m) + 2)) =
          Fin.natAdd (n + 1) (Fin.last (m + 1)) := by
      ext
      simp [Nat.add_assoc]
    simpa [subdiv, right, h1₂, hlast] using
      (Fin.append_right left right (Fin.last (m + 1)))
  · intro j
    change
      ContDiffOn ℝ 1 (⇑(γ₁.trans γ₂).extend) (Set.Icc (subdiv j.castSucc) (subdiv j.succ))
    refine @Fin.addCases (n + 1) (m + 1)
      (fun k ↦ ContDiffOn ℝ 1 (⇑(γ₁.trans γ₂).extend) (Set.Icc (subdiv k.castSucc) (subdiv k.succ)))
      ?_ ?_ j
    · intro i
      cases i using Fin.lastCases with
      | cast i =>
          -- The left interior pieces come from the reparametrized `C¹` pieces of `γ₁`.
          have hs :
              (Fin.castAdd (m + 2) i.succ : Fin (n + 1 + m + 2)) =
                (Fin.castAdd (m + 1) i.castSucc).succ := by
            ext
            simp [Fin.succ_castAdd]
          rw [← hs]
          have hparam :
              ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t)
                (Set.Icc (subdiv₁ i.castSucc.castSucc / 2) (subdiv₁ i.succ.castSucc / 2)) := by
            simpa using contDiffOn_affine_reparam 2 0
              (Set.Icc (subdiv₁ i.castSucc.castSucc / 2) (subdiv₁ i.succ.castSucc / 2))
          have hmaps :
              Set.MapsTo (fun t : ℝ ↦ 2 * t)
                (Set.Icc (subdiv₁ i.castSucc.castSucc / 2) (subdiv₁ i.succ.castSucc / 2))
                (Set.Icc (subdiv₁ i.castSucc.castSucc) (subdiv₁ i.succ.castSucc)) := by
            intro t ht
            constructor <;> nlinarith [ht.1, ht.2]
          have hpiece :
              ContDiffOn ℝ 1 (fun t ↦ γ₁.extend (2 * t))
                (Set.Icc (subdiv₁ i.castSucc.castSucc / 2) (subdiv₁ i.succ.castSucc / 2)) :=
            (hpieces₁ i.castSucc).comp hparam hmaps
          have heq :
              Set.EqOn (γ₁.trans γ₂).extend (fun t ↦ γ₁.extend (2 * t))
                (Set.Icc (subdiv₁ i.castSucc.castSucc / 2) (subdiv₁ i.succ.castSucc / 2)) := by
            intro t ht
            have hupper : subdiv₁ i.succ.castSucc ≤ 1 := by
              calc
                subdiv₁ i.succ.castSucc ≤ subdiv₁ (Fin.last (n + 1)) :=
                  hsubdiv₁.monotone i.succ.castSucc.le_last
                _ = 1 := h1₁
            exact Path.extend_trans_of_le_half γ₁ γ₂ (by nlinarith [ht.2, hupper])
          simpa [subdiv, Fin.castSucc_castAdd, Fin.append_left] using hpiece.congr heq
      | last =>
          -- The last left piece ends at the shared midpoint `1/2`.
          have hs :
              (Fin.natAdd (n + 1) (0 : Fin (m + 2)) : Fin (n + 1 + m + 2)) =
                (Fin.castAdd (m + 1) (Fin.last n)).succ := by
            ext
            simp [Fin.succ_castAdd]
          rw [← hs]
          have hparam :
              ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t)
                (Set.Icc (subdiv₁ (Fin.last n).castSucc / 2) (1 / 2 : ℝ)) := by
            simpa [h1₁] using contDiffOn_affine_reparam 2 0
              (Set.Icc (subdiv₁ (Fin.last n).castSucc / 2) (1 / 2 : ℝ))
          have hmaps :
              Set.MapsTo (fun t : ℝ ↦ 2 * t)
                (Set.Icc (subdiv₁ (Fin.last n).castSucc / 2) (1 / 2 : ℝ))
                (Set.Icc (subdiv₁ (Fin.last n).castSucc) (subdiv₁ (Fin.last n).succ)) := by
            intro t ht
            constructor
            · nlinarith [ht.1]
            · have htop : subdiv₁ (Fin.last n).succ = 1 := by
                simpa [Fin.succ_last] using h1₁
              nlinarith [ht.2, htop]
          have hpiece :
              ContDiffOn ℝ 1 (fun t ↦ γ₁.extend (2 * t))
                (Set.Icc (subdiv₁ (Fin.last n).castSucc / 2) (1 / 2 : ℝ)) :=
            (hpieces₁ (Fin.last n)).comp hparam hmaps
          have heq :
              Set.EqOn (γ₁.trans γ₂).extend (fun t ↦ γ₁.extend (2 * t))
                (Set.Icc (subdiv₁ (Fin.last n).castSucc / 2) (1 / 2 : ℝ)) := by
            intro t ht
            exact Path.extend_trans_of_le_half γ₁ γ₂ (by nlinarith [ht.2])
          simpa [subdiv, left, right, Fin.castSucc_castAdd, Fin.append_left, Fin.append_right, h0₂] using
            hpiece.congr heq
    · intro i
      rw [Fin.castSucc_natAdd, Fin.succ_natAdd]
      -- The right pieces come from the shifted `C¹` pieces of `γ₂`.
      have hparam :
          ContDiffOn ℝ 1 (fun t : ℝ ↦ 2 * t - 1)
            (Set.Icc ((1 + subdiv₂ i.castSucc) / 2) ((1 + subdiv₂ i.succ) / 2)) := by
        simpa [sub_eq_add_neg] using contDiffOn_affine_reparam 2 (-1)
          (Set.Icc ((1 + subdiv₂ i.castSucc) / 2) ((1 + subdiv₂ i.succ) / 2))
      have hmaps :
          Set.MapsTo (fun t : ℝ ↦ 2 * t - 1)
            (Set.Icc ((1 + subdiv₂ i.castSucc) / 2) ((1 + subdiv₂ i.succ) / 2))
            (Set.Icc (subdiv₂ i.castSucc) (subdiv₂ i.succ)) := by
        intro t ht
        constructor <;> nlinarith [ht.1, ht.2]
      have hpiece :
          ContDiffOn ℝ 1 (fun t ↦ γ₂.extend (2 * t - 1))
            (Set.Icc ((1 + subdiv₂ i.castSucc) / 2) ((1 + subdiv₂ i.succ) / 2)) :=
        (hpieces₂ i).comp hparam hmaps
      have heq :
          Set.EqOn (γ₁.trans γ₂).extend (fun t ↦ γ₂.extend (2 * t - 1))
            (Set.Icc ((1 + subdiv₂ i.castSucc) / 2) ((1 + subdiv₂ i.succ) / 2)) := by
        intro t ht
        have hsub : 0 ≤ subdiv₂ i.castSucc := by
          calc
            0 = subdiv₂ 0 := by symm; exact h0₂
            _ ≤ subdiv₂ i.castSucc := hsubdiv₂.monotone (Fin.zero_le _)
        have hhalf : (1 / 2 : ℝ) ≤ t := by
          nlinarith [ht.1, hsub]
        exact Path.extend_trans_of_half_le γ₁ γ₂ hhalf
      simpa [subdiv, Fin.append_right] using hpiece.congr heq

/-- Helper for Cartan section05 0005_Proposition_2_1: comparing a path with the reverse of a
second path produces a piecewise differentiable loop. -/
lemma IsPiecewiseDifferentiable.trans_symm {x y : E} {γ η : Path x y}
    (hγ : γ.IsPiecewiseDifferentiable) (hη : η.IsPiecewiseDifferentiable) :
    (γ.trans η.symm).IsPiecewiseDifferentiable :=
  hγ.trans hη.symm

/-- Helper for Cartan section05 0005_Proposition_2_1: reversing a path does not change its image. -/
lemma range_symm {x y : E} (γ : Path x y) : Set.range γ.symm = Set.range γ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨unitInterval.symm t, ?_⟩
    simp
  · rintro ⟨t, rfl⟩
    refine ⟨unitInterval.symm t, ?_⟩
    simp

/-- Helper for Cartan section05 0005_Proposition_2_1: if every piecewise differentiable loop in
`D` has zero integral, then the curve integral depends only on the endpoints. -/
lemma curveIntegral_eq_of_sameEndpoints_of_loopZero
    {D : Set E} {ω : E → E →L[ℝ] G} (hω : ContinuousOn ω D)
    (hloopZero :
      ∀ {z₀ : E} (γ : Path z₀ z₀), γ.IsPiecewiseDifferentiable → Set.range γ ⊆ D →
        ∫ᶜ z in γ, ω z = 0)
    {x y : E} {γ η : Path x y}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable) (hη_piecewise : η.IsPiecewiseDifferentiable)
    (hγD : Set.range γ ⊆ D) (hηD : Set.range η ⊆ D) :
    ∫ᶜ z in γ, ω z = ∫ᶜ z in η, ω z := by
  have hγ_int :
      CurveIntegrable ω γ :=
    curveIntegrable_of_piecewiseDifferentiable_of_continuousOn hω hγ_piecewise hγD
  have hη_int :
      CurveIntegrable ω η :=
    curveIntegrable_of_piecewiseDifferentiable_of_continuousOn hω hη_piecewise hηD
  have hloop_piecewise : (γ.trans η.symm).IsPiecewiseDifferentiable :=
    hγ_piecewise.trans_symm hη_piecewise
  have hloopD : Set.range (γ.trans η.symm) ⊆ D := by
    rw [Path.trans_range]
    exact Set.union_subset hγD <| by simpa [range_symm η] using hηD
  have hsum : ∫ᶜ z in γ, ω z + ∫ᶜ z in η.symm, ω z = 0 := by
    calc
      ∫ᶜ z in γ, ω z + ∫ᶜ z in η.symm, ω z = ∫ᶜ z in γ.trans η.symm, ω z := by
        symm
        exact curveIntegral_trans hγ_int hη_int.symm
      _ = 0 := hloopZero (γ.trans η.symm) hloop_piecewise hloopD
  have hneg : -(∫ᶜ z in η.symm, ω z) = ∫ᶜ z in γ, ω z :=
    neg_eq_of_add_eq_zero_left hsum
  calc
    ∫ᶜ z in γ, ω z = -(∫ᶜ z in η.symm, ω z) := hneg.symm
    _ = ∫ᶜ z in η, ω z := by
      rw [curveIntegral_symm]
      simp

end Path

/-- Helper for Cartan section05 0005_Proposition_2_1: on an open connected set, vanishing
piecewise-differentiable loop integrals produces a primitive. -/
lemma hasPrimitiveOn_of_curveIntegral_eq_zero_loops_of_isOpen_isConnected
    {U : Set E} (hU_open : IsOpen U) (hU_connected : IsConnected U)
    {ω : E → E →L[ℝ] G} (hω : ContinuousOn ω U)
    (hloopZero :
      ∀ {z₀ : E} (γ : Path z₀ z₀), γ.IsPiecewiseDifferentiable → Set.range γ ⊆ U →
        ∫ᶜ z in γ, ω z = 0) :
    HasPrimitiveOn U ω := by
  classical
  rcases hU_connected.nonempty with ⟨a, ha⟩
  have hpath :
      ∀ x : U, ∃ γ : Path a x.1, γ.IsPiecewiseDifferentiable ∧ ∀ t, γ t ∈ U := by
    intro x
    simpa using
      exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
        hU_open hU_connected ha x.property
  choose ρ hρ_piece hρ_mem using hpath
  let F : E → G := fun x ↦ if hx : x ∈ U then ∫ᶜ z in ρ ⟨x, hx⟩, ω z else 0
  refine ⟨F, ?_⟩
  intro z hz
  have hF_eq :
      F =ᶠ[nhds z] fun x ↦ F z + ∫ᶜ u in Path.segment z x, ω u := by
    obtain ⟨r, hr_pos, hrU⟩ := Metric.isOpen_iff.mp hU_open z hz
    filter_upwards [Metric.ball_mem_nhds z hr_pos] with x hxball
    have hxU : x ∈ U := hrU hxball
    have hρz_range : Set.range (ρ ⟨z, hz⟩) ⊆ U := by
      rintro y ⟨t, rfl⟩
      exact hρ_mem ⟨z, hz⟩ t
    have hρx_range : Set.range (ρ ⟨x, hxU⟩) ⊆ U := by
      rintro y ⟨t, rfl⟩
      exact hρ_mem ⟨x, hxU⟩ t
    have hseg_ball : Set.range (Path.segment z x) ⊆ Metric.ball z r := by
      rw [Path.range_segment]
      exact (convex_ball z r).segment_subset (Metric.mem_ball_self hr_pos) hxball
    have hsegU : Set.range (Path.segment z x) ⊆ U :=
      Set.Subset.trans hseg_ball hrU
    have htrans_piece :
        ((ρ ⟨z, hz⟩).trans (Path.segment z x)).IsPiecewiseDifferentiable :=
      (hρ_piece ⟨z, hz⟩).trans_of_isDifferentiable (Path.segment_isDifferentiable z x)
    have htrans_range : Set.range ((ρ ⟨z, hz⟩).trans (Path.segment z x)) ⊆ U := by
      rw [Path.trans_range]
      exact Set.union_subset hρz_range hsegU
    have hρz_integrable :
        CurveIntegrable ω (ρ ⟨z, hz⟩) :=
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hω (hρ_piece ⟨z, hz⟩) hρz_range
    have hseg_integrable :
        CurveIntegrable ω (Path.segment z x) :=
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hω (Path.segment_isPiecewiseDifferentiable z x) hsegU
    have hsame :
        ∫ᶜ u in ρ ⟨x, hxU⟩, ω u =
          ∫ᶜ u in (ρ ⟨z, hz⟩).trans (Path.segment z x), ω u :=
      Path.curveIntegral_eq_of_sameEndpoints_of_loopZero hω hloopZero
        (hρ_piece ⟨x, hxU⟩) htrans_piece hρx_range htrans_range
    -- Compare the chosen path to `x` with the chosen path to `z` followed by the short segment.
    calc
      F x = ∫ᶜ u in ρ ⟨x, hxU⟩, ω u := by simp [F, hxU]
      _ = ∫ᶜ u in (ρ ⟨z, hz⟩).trans (Path.segment z x), ω u := hsame
      _ = ∫ᶜ u in ρ ⟨z, hz⟩, ω u + ∫ᶜ u in Path.segment z x, ω u := by
        exact curveIntegral_trans hρz_integrable hseg_integrable
      _ = F z + ∫ᶜ u in Path.segment z x, ω u := by simp [F, hz]
  have hω_eventually : ∀ᶠ x in nhds z, ContinuousAt ω x := by
    filter_upwards [hU_open.mem_nhds hz] with x hxU
    exact hω.continuousAt (hU_open.mem_nhds hxU)
  have hsegment_deriv :
      HasFDerivAt (fun x ↦ ∫ᶜ u in Path.segment z x, ω u) (ω z) z :=
    HasFDerivAt.curveIntegral_segment_source' hω_eventually
  have hlocal_deriv :
      HasFDerivAt (fun x ↦ F z + ∫ᶜ u in Path.segment z x, ω u) (ω z) z := by
    simpa using hsegment_deriv.const_add (F z)
  -- The local segment formula identifies `F` with a standard primitive model near `z`.
  exact hlocal_deriv.congr_of_eventuallyEq hF_eq

/-- Helper for Cartan section05 0005_Proposition_2_1: the component-keyed global primitive agrees
near `z` with the primitive chosen for `connectedComponentIn D z`. -/
lemma globalPrimitive_eq_componentPrimitive_nhds
    {D : Set E} [DecidablePred (· ∈ D)]
    (hD_open : IsOpen D) (componentPrimitive : Set E → E → G) {z : E} (hz : z ∈ D) :
    (fun x ↦ if x ∈ D then componentPrimitive (connectedComponentIn D x) x else 0)
      =ᶠ[nhds z] componentPrimitive (connectedComponentIn D z) := by
  have hcomponent_nhds :
      connectedComponentIn D z ∈ nhds z :=
    connectedComponentIn_mem_nhds (hD_open.mem_nhds hz)
  filter_upwards [hcomponent_nhds] with x hxC
  have hxD : x ∈ D := connectedComponentIn_subset D z hxC
  have hcomponent_eq : connectedComponentIn D x = connectedComponentIn D z :=
    (connectedComponentIn_eq hxC).symm
  -- Inside the component neighborhood, both the domain test and the component key are fixed.
  simp [hxD, hcomponent_eq]

-- Proof sketch: if `ω = dF` on `D`, then the curve integral along any closed path is the endpoint
-- difference `F (γ 1) - F (γ 0)`, hence vanishes. Conversely, on each connected component of the
-- open set `D`, fix a base point, define the componentwise primitive by integrating `ω` along a
-- piecewise differentiable path from that base point, use loop-vanishing to show
-- path-independence, and then glue these componentwise primitives across the clopen connected
-- components of `D`.
/-- Cartan section05 0005_Proposition_2_1: Proposition 2.1 states that for a continuous
`G`-valued differential form on an open set `D`, the form has a primitive on `D` if and only if
its integral along every piecewise differentiable closed path contained in `D` is zero. -/
theorem hasPrimitiveOn_iff_curveIntegral_eq_zero_loops_of_isOpen
    {D : Set E} (hD_open : IsOpen D)
    {ω : E → E →L[ℝ] G} (hω : ContinuousOn ω D) :
    HasPrimitiveOn D ω ↔
      ∀ {z₀ : E} (γ : Path z₀ z₀) (hγ_piecewise : γ.IsPiecewiseDifferentiable)
        (hγD : Set.range γ ⊆ D),
        ∫ᶜ z in γ, ω z = 0 := by
  constructor
  · intro hprimitive z₀ γ hγ_piecewise hγD
    rcases hprimitive with ⟨primitive, hprimitive⟩
    -- First show the loop is curve-integrable so the endpoint-difference formula applies.
    have hγ_integrable : CurveIntegrable ω γ :=
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hω hγ_piecewise hγD
    calc
      ∫ᶜ z in γ, ω z = hprimitive.alongPath γ hγD 1 - hprimitive.alongPath γ hγD 0 := by
        -- Convert the global primitive on `D` into a primitive along `γ`.
        simpa using
          (hprimitive.isPrimitiveAlongPath hD_open γ hγD).curveIntegral_eq_endpoint_sub
            hγ_piecewise hγ_integrable
      _ = primitive z₀ - primitive z₀ := by
        -- A closed loop has identical initial and terminal values.
        simp [IsPrimitiveOn.alongPath_apply]
      _ = 0 := sub_self _
  · intro hloopZero
    classical
    have hcomponentPrimitive :
        ∀ C : Set E, (∃ z ∈ D, C = connectedComponentIn D z) → ∃ f : E → G, IsPrimitiveOn C ω f := by
      intro C hC
      rcases hC with ⟨z, hz, rfl⟩
      -- Route correction: choose one primitive per connected component, not per point.
      exact hasPrimitiveOn_of_curveIntegral_eq_zero_loops_of_isOpen_isConnected
        (hD_open.connectedComponentIn)
        ((isConnected_connectedComponentIn_iff).2 hz)
        (hω.mono (connectedComponentIn_subset D z))
        (fun γ hγ_piecewise hγC ↦
          hloopZero γ hγ_piecewise
            (Set.Subset.trans hγC (connectedComponentIn_subset D z)))
    let componentPrimitive : Set E → E → G := fun C ↦
      if hC : ∃ z ∈ D, C = connectedComponentIn D z then
        Classical.choose (hcomponentPrimitive C hC)
      else 0
    have hcomponentPrimitive_spec :
        ∀ {z : E} (hz : z ∈ D),
          IsPrimitiveOn (connectedComponentIn D z) ω
            (componentPrimitive (connectedComponentIn D z)) := by
      intro z hz
      have hC : ∃ y ∈ D, connectedComponentIn D z = connectedComponentIn D y := ⟨z, hz, rfl⟩
      -- The component witness is read back from the component-keyed choice.
      simpa [componentPrimitive, hC] using
        (Classical.choose_spec (hcomponentPrimitive (connectedComponentIn D z) hC))
    let F : E → G := fun x ↦
      if hx : x ∈ D then componentPrimitive (connectedComponentIn D x) x else 0
    refine ⟨F, ?_⟩
    intro z hz
    have hz_component : z ∈ connectedComponentIn D z := mem_connectedComponentIn hz
    have hF_eq :
        F =ᶠ[nhds z] componentPrimitive (connectedComponentIn D z) :=
      globalPrimitive_eq_componentPrimitive_nhds hD_open componentPrimitive hz
    -- Near `z`, the global ambient extension is literally the primitive on its component.
    exact (hcomponentPrimitive_spec hz z hz_component).congr_of_eventuallyEq hF_eq

end
