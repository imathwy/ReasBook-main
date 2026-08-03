import Mathlib
import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap09.Remark_9_37

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal InnerProductSpace

namespace ERealFunction

noncomputable section

/-- Helper for Example 13 31: on `ℝ`, the conjugate body rewrites to the scalar supremum
`sup_x (ux - f x)`. -/
@[simp] private theorem conjugate_apply_real (f : ℝ → EReal) (u : ℝ) :
    f∗ u = sSup (Set.range fun x : ℝ ↦ ((u * x : ℝ) : EReal) - f x) := by
  -- Rewrite the defining indexed supremum as an `sSup` over the scalar range.
  rw [conjugate_apply, ← sSup_range]
  congr with x

/-- Helper for Example 13 31: an `sSup` equals `a` when every value is bounded above by `a` and
every strict lower bound of `a` is exceeded somewhere in the range. -/
private theorem supremum_eq_of_pointwise_le_and_dense_lower_bounds
    (g : ℝ → EReal) (a : EReal) (h_upper : ∀ x, g x ≤ a)
    (h_lower : ∀ z, z < a → ∃ x, z < g x) :
    sSup (Set.range g) = a := by
  -- Apply the standard `sSup` characterization directly to the range of `g`.
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h_upper x
  · intro z hz
    rcases h_lower z hz with ⟨x, hx⟩
    exact ⟨g x, ⟨x, rfl⟩, hx⟩

/-- Helper for Example 13 31: the Young-extremizing point
`sign(u) * |u|^(Real.conjExponent p - 1)` attains the value `|u|^(Real.conjExponent p) /
Real.conjExponent p`. -/
private theorem power_conjugate_maximizer_value
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    let q := Real.conjExponent p
    let x0 := Real.sign u * |u| ^ (q - 1)
    u * x0 - |x0| ^ p / p = |u| ^ q / q := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  have hp_ne : p ≠ 0 := hpq.ne_zero
  have hq_ne : q ≠ 0 := hpq.symm.ne_zero
  have hcoeff : 1 - 1 / p = 1 / q := by
    simpa [one_div] using hpq.one_sub_inv
  have hqp : (q - 1) * p = q := by
    calc
      (q - 1) * p = (q / p) * p := by rw [hpq.symm.div_conj_eq_sub_one]
      _ = q := by field_simp [hp_ne]
  rcases eq_or_ne u 0 with rfl | hu0
  · have hq_sub_ne : q - 1 ≠ 0 := ne_of_gt hpq.symm.sub_one_pos
    -- At the origin both the maximizer and the optimal value are zero.
    simp [q, hp_ne, hq_ne, hq_sub_ne]
  · rcases lt_or_gt_of_ne hu0 with hu_neg | hu_pos
    · have hu_abs : |u| = -u := abs_of_neg hu_neg
      have hu_pos' : 0 < -u := by linarith
      have hu_nonneg' : 0 ≤ -u := hu_pos'.le
      have hu_mul_pow : u * (-((-u) ^ (q - 1))) = (-u) ^ q := by
        -- On the negative branch the maximizing point has the opposite sign.
        calc
          u * (-((-u) ^ (q - 1))) = (-u) * (-u) ^ (q - 1) := by ring
          _ = (-u) ^ (1 : ℝ) * (-u) ^ (q - 1) := by rw [Real.rpow_one]
          _ = (-u) ^ q := by
            calc
              (-u) ^ (1 : ℝ) * (-u) ^ (q - 1) = (-u) ^ ((1 : ℝ) + (q - 1)) := by
                exact (Real.rpow_add hu_pos' (1 : ℝ) (q - 1)).symm
              _ = (-u) ^ q := by congr 1; ring
      have hpow : ((-u) ^ (q - 1)) ^ p = (-u) ^ q := by
        rw [← Real.rpow_mul hu_nonneg' (q - 1) p, hqp]
      -- Substitute the negative-branch maximizer and simplify the Holder coefficient.
      calc
        u * x0 - |x0| ^ p / p = u * (-((-u) ^ (q - 1))) - ((-u) ^ (q - 1)) ^ p / p := by
          simp [x0, hu_abs, Real.sign_of_neg hu_neg,
            abs_of_nonneg (Real.rpow_nonneg hu_nonneg' _)]
        _ = (-u) ^ q - (-u) ^ q / p := by rw [hu_mul_pow, hpow]
        _ = (-u) ^ q * (1 - 1 / p) := by ring
        _ = (-u) ^ q * (1 / q) := by rw [hcoeff]
        _ = (-u) ^ q / q := by ring
        _ = |u| ^ q / q := by simp [hu_abs]
    · have hu_abs : |u| = u := abs_of_pos hu_pos
      have hu_nonneg : 0 ≤ u := hu_pos.le
      have hu_mul_pow : u * u ^ (q - 1) = u ^ q := by
        -- On the positive branch the maximizing point is the usual positive power.
        calc
          u * u ^ (q - 1) = u ^ (1 : ℝ) * u ^ (q - 1) := by rw [Real.rpow_one]
          _ = u ^ q := by
            calc
              u ^ (1 : ℝ) * u ^ (q - 1) = u ^ ((1 : ℝ) + (q - 1)) := by
                exact (Real.rpow_add hu_pos (1 : ℝ) (q - 1)).symm
              _ = u ^ q := by congr 1; ring
      have hpow : (u ^ (q - 1)) ^ p = u ^ q := by
        rw [← Real.rpow_mul hu_nonneg (q - 1) p, hqp]
      -- Substitute the positive-branch maximizer and simplify the Holder coefficient.
      calc
        u * x0 - |x0| ^ p / p = u * u ^ (q - 1) - (u ^ (q - 1)) ^ p / p := by
          simp [x0, hu_abs, Real.sign_of_pos hu_pos,
            abs_of_nonneg (Real.rpow_nonneg hu_nonneg _)]
        _ = u ^ q - u ^ q / p := by rw [hu_mul_pow, hpow]
        _ = u ^ q * (1 - 1 / p) := by ring
        _ = u ^ q * (1 / q) := by rw [hcoeff]
        _ = u ^ q / q := by ring
        _ = |u| ^ q / q := by simp [hu_abs]

/-- Helper for Example 13 31: the scalar conjugate of `x ↦ |x|^p / p` is
`u ↦ |u|^(p*) / p*`. -/
private theorem conjugate_absRpowDivided
    (p : ℝ) (hp : 1 < p) (u : ℝ) :
    ((fun x : ℝ ↦ |x| ^ p / p).toEReal.asEReal)∗ u =
      ((fun x : ℝ ↦ |x| ^ Real.conjExponent p / Real.conjExponent p).toEReal.asEReal) u := by
  let q := Real.conjExponent p
  let x0 := Real.sign u * |u| ^ (q - 1)
  have hpq : p.HolderConjugate q := by
    simpa [q] using Real.HolderConjugate.conjExponent hp
  rw [conjugate_apply_real]
  simp only [Function.asEReal_apply, Function.toEReal_apply]
  -- Bound the scalar defect above by Young's inequality and attain the bound at the extremizer.
  refine supremum_eq_of_pointwise_le_and_dense_lower_bounds
      (fun x : ℝ ↦ ((u * x : ℝ) : EReal) - ((|x| ^ p / p : ℝ) : EReal))
      ((|u| ^ q / q : ℝ) : EReal) ?_ ?_
  · intro x
    have hmul : u * x ≤ |x| * |u| := by
      calc
        u * x ≤ |u * x| := le_abs_self (u * x)
        _ = |u| * |x| := by rw [abs_mul]
        _ = |x| * |u| := by ring
    have hyoung :
        |x| * |u| ≤ |x| ^ p / p + |u| ^ q / q := by
      simpa [q, abs_abs] using
        Real.young_inequality_of_nonneg (abs_nonneg x) (abs_nonneg u) hpq
    have hreal : u * x - |x| ^ p / p ≤ |u| ^ q / q := by
      linarith
    have hEReal :
        ((u * x - |x| ^ p / p : ℝ) : EReal) ≤ ((|u| ^ q / q : ℝ) : EReal) :=
      EReal.coe_le_coe hreal
    simpa [sub_eq_add_neg, ← EReal.coe_sub] using hEReal
  · intro z hz
    have hvalue_real : u * x0 - |x0| ^ p / p = |u| ^ q / q := by
      simpa [q, x0] using power_conjugate_maximizer_value p hp u
    have hvalue :
        (((u * x0 : ℝ) : EReal) - ((|x0| ^ p / p : ℝ) : EReal)) =
          ((|u| ^ q / q : ℝ) : EReal) := by
      simpa [sub_eq_add_neg, ← EReal.coe_sub] using
        congrArg (fun t : ℝ ↦ (t : EReal)) hvalue_real
    exact ⟨x0, hz.trans_eq hvalue.symm⟩

/-- Helper for Example 13 31: casting a finite real sum to `EReal` agrees with summing the casted
summands. -/
lemma finset_sum_coe_real_local {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    ((s.sum r : ℝ) : EReal) = s.sum (fun i ↦ ((r i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is preserved by the real-to-`EReal` coercion.
      simp
  | @insert i s hi ih =>
      -- Peel off the distinguished term and combine it with the induction hypothesis.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

/-- Helper for Example 13 31: precomposing an `EReal`-valued function on the finite `lp` owner by
the canonical `lpPiLpₗᵢ` identification transports its Fenchel conjugate along the same
identification. -/
lemma conjugate_precompose_lpPiLp_symm
    (N : ℕ) (F : lp (fun _ : Fin N ↦ ℝ) 2 → EReal) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦ F ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x))∗ =
      fun u : EuclideanSpace ℝ (Fin N) ↦ F∗ ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm u) := by
  let e : lp (fun _ : Fin N ↦ ℝ) 2 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ
  ext u
  -- Reindex the defining supremum through the linear isometry equivalence `e`.
  rw [conjugate_apply, conjugate_apply]
  calc
    ⨆ x : EuclideanSpace ℝ (Fin N), (((⟪x, u⟫_ℝ : ℝ) : EReal) - F (e.symm x)) =
        ⨆ z : lp (fun _ : Fin N ↦ ℝ) 2, (((⟪e z, u⟫_ℝ : ℝ) : EReal) - F z) := by
          exact (e.symm.iSup_congr fun x => by simp [e])
    _ = ⨆ z : lp (fun _ : Fin N ↦ ℝ) 2, (((⟪z, e.symm u⟫_ℝ : ℝ) : EReal) - F z) := by
          -- Move the `lpPiLpₗᵢ` map across the inner product.
          refine iSup_congr fun z => ?_
          have hpair : ⟪e z, u⟫_ℝ = ⟪z, e.symm u⟫_ℝ := by
            simpa using LinearIsometryEquiv.inner_map_eq_flip e z u
          rw [hpair]

/-- Helper for Example 13 31: the pulled-back finite direct sum of the scalar map
`t ↦ |t|^r / r` is exactly the coordinate `ℓ^r` power expression on `EuclideanSpace ℝ (Fin N)`. -/
lemma directSum_abs_power_divided_eq_lpNorm_power_divided
    (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦
      (directSumFunction (fun _ : Fin N ↦ (fun t : ℝ ↦ |t| ^ r / r).toEReal)
        ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) : EReal)) =
      fun x : EuclideanSpace ℝ (Fin N) ↦
        ((‖x‖_[ENNReal.ofReal r] ^ r / r : ℝ) : EReal) := by
  ext x
  let e : lp (fun _ : Fin N ↦ ℝ) 2 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ
  have hcoords : (((e.symm x : lp (fun _ : Fin N ↦ ℝ) 2) : Fin N → ℝ)) = x := by
    simpa [e] using
      (coe_lpPiLpₗᵢ_symm (𝕜 := ℝ) (E := fun _ : Fin N ↦ ℝ) (p := (2 : ℝ≥0∞)) x)
  have hnorm :
      ‖x‖_[ENNReal.ofReal r] ^ r = ∑ i : Fin N, |x i| ^ r := by
    have hnorm_eq :
        ‖x‖_[ENNReal.ofReal r] =
          (∑ i : Fin N, |x i| ^ r) ^ (1 / r) := by
      -- Rewrite the coordinate `ℓ^r` norm through the `WithLp` owner formula.
      rw [EuclideanSpace.lpNorm_apply]
      simpa [ENNReal.toReal_ofReal hr.le, Real.norm_eq_abs] using
        (PiLp.norm_eq_sum
          (p := ENNReal.ofReal r) (β := fun _ : Fin N ↦ ℝ)
          (by simpa [ENNReal.toReal_ofReal hr.le] using hr)
          (WithLp.toLp (ENNReal.ofReal r) ((EuclideanSpace.equiv (Fin N) ℝ) x)))
    have hsum_nonneg : 0 ≤ ∑ i : Fin N, |x i| ^ r := by
      exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (x i)) r
    calc
      ‖x‖_[ENNReal.ofReal r] ^ r = ((∑ i : Fin N, |x i| ^ r) ^ (1 / r)) ^ r := by
        rw [hnorm_eq]
      _ = (∑ i : Fin N, |x i| ^ r) ^ ((1 / r) * r) := by
        rw [← Real.rpow_mul hsum_nonneg (1 / r) r]
      _ = (∑ i : Fin N, |x i| ^ r) ^ (1 : ℝ) := by
        congr 1
        field_simp [hr.ne']
      _ = ∑ i : Fin N, |x i| ^ r := by
        rw [Real.rpow_one]
  -- Rewrite the direct sum as a casted finite real sum, then close with the `lpNorm` identity.
  calc
    (directSumFunction (fun _ : Fin N ↦ (fun t : ℝ ↦ |t| ^ r / r).toEReal) (e.symm x) : EReal)
        = (((∑ i : Fin N, |(e.symm x : lp (fun _ : Fin N ↦ ℝ) 2) i| ^ r / r : ℝ)) : EReal) := by
            rw [directSumFunction_apply]
            symm
            exact finset_sum_coe_real_local (s := Finset.univ)
              (r := fun i : Fin N ↦ |(e.symm x : lp (fun _ : Fin N ↦ ℝ) 2) i| ^ r / r)
    _ = (((∑ i : Fin N, |x i| ^ r / r : ℝ)) : EReal) := by
          simp [hcoords]
    _ = ((((∑ i : Fin N, |x i| ^ r) / r : ℝ)) : EReal) := by
          congr 1
          rw [Finset.sum_div]
    _ = ((‖x‖_[ENNReal.ofReal r] ^ r / r : ℝ) : EReal) := by
          congr 1
          rw [← hnorm]

/-- Helper for Example 13 31: the defect contributed by one coordinate in the finite direct-sum
conjugate body. -/
private def coordinateDefect
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → EReal)
    (u : lp (fun _ : Fin N ↦ ℝ) 2) (i : Fin N) (z : ℝ) : EReal :=
  (((⟪z, u i⟫_ℝ : ℝ) : EReal) - f i z)

/-- Helper for Example 13 31: the partial finite-coordinate conjugate defect over a finite active
set. -/
private def partialCoordinateDefect
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → EReal)
    (u : lp (fun _ : Fin N ↦ ℝ) 2) (s : Finset (Fin N))
    (x : lp (fun _ : Fin N ↦ ℝ) 2) : EReal :=
  s.sum (fun j ↦ coordinateDefect N f u j (x j))

/-- Helper for Example 13 31: the supremum of all pairwise sums in `EReal` is the sum of the two
individual suprema. -/
private theorem sSup_image2_add_eq (A B : Set EReal) :
    sSup (Set.image2 (· + ·) A B) = sSup A + sSup B := by
  apply le_antisymm
  · -- Bound every pairwise sum above by the sum of the two individual suprema.
    refine sSup_le ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (le_sSup ha) (le_sSup hb)
  · -- Approximate each supremum from below and combine the two approximants.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_sSup_iff.mp ha with ⟨a', ha', haa'⟩
    rcases lt_sSup_iff.mp hb with ⟨b', hb', hbb'⟩
    have hab' : a + b < a' + b' := EReal.add_lt_add haa' hbb'
    exact hab'.le.trans <| le_sSup <| Set.mem_image2.mpr ⟨a', ha', b', hb', rfl⟩

/-- Helper for Example 13 31: a finite sum of `EReal` values that are never `-∞` is itself never
`-∞`. -/
private theorem finset_sum_ne_bot_of_forall_ne_bot
    {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hbot : ∀ i ∈ s, g i ≠ ⊥) :
    s.sum g ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine (EReal.add_ne_bot_iff.2 ?_ )
      constructor
      · exact hbot i (by simp)
      · exact ih (fun j hj ↦ hbot j (by simp [hj]))

/-- Helper for Example 13 31: summing coordinatewise negatives in `EReal` is the negation of the
finite sum as soon as no summand is `-∞`. -/
private theorem finset_sum_neg_ereal
    {ι : Type*} (s : Finset ι) (g : ι → EReal)
    (hbot : ∀ i ∈ s, g i ≠ ⊥) :
    s.sum (fun i ↦ -g i) = -s.sum g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is fixed by negation.
      simp
  | @insert i s hi ih =>
      -- Peel off one term and rewrite the negation of the finite sum explicitly.
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        ih (fun j hj ↦ hbot j (by simp [hj]))]
      have hi_ne_bot : g i ≠ ⊥ := hbot i (by simp)
      have hs_ne_bot : s.sum g ≠ ⊥ :=
        finset_sum_ne_bot_of_forall_ne_bot (s := s) (g := g) (fun j hj ↦ hbot j (by simp [hj]))
      simpa using (EReal.neg_add (.inl hi_ne_bot) (.inr hs_ne_bot)).symm

/-- Helper for Example 13 31: the finite partial coordinate defect is the casted sum of the active
inner products minus the sum of the active coordinate function values. -/
private theorem partial_coordinate_defect_eq_sum_sub
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → EReal)
    (u : lp (fun _ : Fin N ↦ ℝ) 2) (s : Finset (Fin N))
    (x : lp (fun _ : Fin N ↦ ℝ) 2)
    (hbot : ∀ j ∈ s, f j (x j) ≠ ⊥) :
    partialCoordinateDefect N f u s x =
      (((s.sum fun j ↦ ⟪x j, u j⟫_ℝ) : EReal) - s.sum (fun j ↦ f j (x j))) := by
  -- Normalize each coordinate defect to `a + (-b)` and then regroup the finite sums.
  simp_rw [partialCoordinateDefect, coordinateDefect, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, ← finset_sum_coe_real_local]
  congr 1
  simpa using finset_sum_neg_ereal (s := s) (g := fun j ↦ f j (x j)) hbot

/-- Helper for Example 13 31: activating one more coordinate splits the partial-defect range as
pairwise sums of the new coordinate defect and the previous partial defect. -/
private theorem partial_coordinate_defect_range_insert_eq_image2
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → EReal)
    (u : lp (fun _ : Fin N ↦ ℝ) 2) (s : Finset (Fin N)) (i : Fin N) (hi : i ∉ s) :
    Set.range (partialCoordinateDefect N f u (insert i s)) =
      Set.image2 (· + ·) (Set.range (coordinateDefect N f u i))
        (Set.range (partialCoordinateDefect N f u s)) := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, rfl⟩
    -- Split the inserted finite sum into the new coordinate and the old tail.
    refine Set.mem_image2.mpr ?_
    refine ⟨coordinateDefect N f u i (x i), ⟨x i, rfl⟩,
      partialCoordinateDefect N f u s x, ⟨x, rfl⟩, ?_⟩
    simp [partialCoordinateDefect, hi, Finset.sum_insert]
  · intro hr
    rcases Set.mem_image2.mp hr with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨z, rfl⟩
    rcases hb with ⟨x, rfl⟩
    refine ⟨coordinateSlice x i z, ?_⟩
    have htail :
        partialCoordinateDefect N f u s (coordinateSlice x i z) =
          partialCoordinateDefect N f u s x := by
      -- Away from `i`, the slice agrees with the base point coordinatewise.
      unfold partialCoordinateDefect
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hji : j ≠ i := ne_of_mem_of_not_mem hj hi
      simp [coordinateDefect, coordinateSlice_apply_of_ne, hji]
    -- Route correction: first separate the inserted coordinate, then rewrite the frozen tail by
    -- the slice invariance lemma.
    rw [show
        partialCoordinateDefect N f u (insert i s) (coordinateSlice x i z) =
          coordinateDefect N f u i ((coordinateSlice x i z) i) +
            partialCoordinateDefect N f u s (coordinateSlice x i z) by
        simp [partialCoordinateDefect, hi, Finset.sum_insert]]
    simp only [coordinateSlice_apply_self]
    rw [htail]
    simpa [coordinateDefect] using hab

/-- Helper for Example 13 31: the supremum of the partial coordinate defects over a finite active
set is the sum of the corresponding coordinate conjugates. -/
private theorem sSup_partial_coordinate_defect_eq_sum_conjugate_fin
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → EReal)
    (u : lp (fun _ : Fin N ↦ ℝ) 2) :
    ∀ s : Finset (Fin N),
      sSup (Set.range (partialCoordinateDefect N f u s)) = s.sum (fun j ↦ (f j)∗ (u j)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- The empty partial defect is constantly zero.
      have hconst :
          partialCoordinateDefect N f u ∅ = fun _ : lp (fun _ : Fin N ↦ ℝ) 2 ↦ (0 : EReal) := by
        funext x
        simp [partialCoordinateDefect]
      have hzero : Set.range (partialCoordinateDefect N f u ∅) = ({0} : Set EReal) := by
        rw [hconst, Set.range_const]
      rw [hzero]
      simp
  | @insert i s hi ih =>
      -- Separate the new coordinate and use the induction hypothesis on the remaining coordinates.
      rw [partial_coordinate_defect_range_insert_eq_image2 (N := N) (f := f) (u := u)
        (s := s) (i := i) hi, sSup_image2_add_eq, ih, Finset.sum_insert hi]
      have hcoord :
          sSup (Set.range (coordinateDefect N f u i)) = (f i)∗ (u i) := by
        -- The one-coordinate defect supremum is exactly the coordinate Fenchel conjugate.
        rw [conjugate_apply, ← sSup_range]
        rfl
      rw [hcoord]

/-- Helper for Example 13 31: after expanding the `lp` inner product and the direct-sum owner, the
global conjugate body is exactly the full finite-coordinate defect. -/
private theorem directSum_conjugate_body_eq_univ_partial_coordinate_defect
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → Set.Ioi (⊥ : EReal))
    (u x : lp (fun _ : Fin N ↦ ℝ) 2) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (directSumFunction f x : EReal)) =
      partialCoordinateDefect N (fun i z ↦ (f i z : EReal)) u Finset.univ x := by
  -- Rewrite the global body as the finite real inner-product sum minus the coordinate sum.
  have hinner_sum : ∑ j, ⟪x j, u j⟫_ℝ = ⟪x, u⟫_ℝ := by
    calc
      ∑ j, ⟪x j, u j⟫_ℝ
          = ∑ j, ⟪(lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ x) j,
              (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ u) j⟫_ℝ := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [coe_lpPiLpₗᵢ]
      _ = ⟪lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ x, lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ u⟫_ℝ := by
            symm
            rw [PiLp.inner_apply]
      _ = ⟪x, u⟫_ℝ := by
            exact (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).inner_map_map x u
  have hinner_cast :
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) = ∑ j, ((⟪x j, u j⟫_ℝ : ℝ) : EReal) := by
    calc
      (((⟪x, u⟫_ℝ : ℝ) : EReal)) = (((∑ j, ⟪x j, u j⟫_ℝ : ℝ) : ℝ) : EReal) := by
        rw [← hinner_sum]
      _ = ∑ j, ((⟪x j, u j⟫_ℝ : ℝ) : EReal) := by
        exact finset_sum_coe_real_local (s := Finset.univ) (r := fun j ↦ ⟪x j, u j⟫_ℝ)
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (directSumFunction f x : EReal))
        = (((∑ j, ⟪x j, u j⟫_ℝ) : EReal) - ∑ j, (f j (x j) : EReal)) := by
            rw [hinner_cast, directSumFunction_apply]
    _ = partialCoordinateDefect N (fun i z ↦ (f i z : EReal)) u Finset.univ x := by
          symm
          exact partial_coordinate_defect_eq_sum_sub (N := N)
            (f := fun i z ↦ (f i z : EReal)) (u := u) (s := Finset.univ) (x := x)
            (hbot := fun j hj ↦ ne_of_gt (f j (x j)).2)

/-- Helper for Example 13 31: the Fenchel conjugate of a finite scalar direct sum is the finite
sum of the coordinate Fenchel conjugates. -/
private theorem conjugate_directSumFunction_eq_sum_conjugate_fin
    (N : ℕ) (f : ∀ _ : Fin N, ℝ → Set.Ioi (⊥ : EReal)) :
    (directSumFunction f).asEReal∗ =
      fun u : lp (fun _ : Fin N ↦ ℝ) 2 ↦ ∑ i, (f i).asEReal∗ (u i) := by
  ext u
  -- Rewrite the conjugate as the supremum of the full finite-coordinate defect.
  rw [conjugate_apply, ← sSup_range]
  have hbody :
      (fun x : lp (fun _ : Fin N ↦ ℝ) 2 ↦
        (((⟪x, u⟫_ℝ : ℝ) : EReal) - (directSumFunction f x : EReal))) =
        partialCoordinateDefect N (fun i z ↦ (f i z : EReal)) u Finset.univ := by
    -- Route correction: normalize the global body first, then apply the finite-set `sSup` lemma.
    funext x
    simpa using
      directSum_conjugate_body_eq_univ_partial_coordinate_defect
        (N := N) (f := f) (u := u) (x := x)
  rw [hbody]
  simpa using
    sSup_partial_coordinate_defect_eq_sum_conjugate_fin (N := N)
      (f := fun i z ↦ (f i z : EReal)) (u := u) (s := Finset.univ)

/-- Helper for Example 13 31: the Fenchel conjugate of the finite direct sum of the scalar map
`t ↦ |t|^p / p` is the corresponding direct sum with exponent `Real.conjExponent p`. -/
lemma conjugate_directSum_abs_power_divided_eq_conjExponent
    (N : ℕ) (p : ℝ) (hp : 1 < p) :
    (directSumFunction (fun _ : Fin N ↦ (fun t : ℝ ↦ |t| ^ p / p).toEReal)).asEReal∗ =
      fun u : lp (fun _ : Fin N ↦ ℝ) 2 ↦
        (directSumFunction
          (fun _ : Fin N ↦
            (fun t : ℝ ↦ |t| ^ Real.conjExponent p / Real.conjExponent p).toEReal)
          u : EReal) := by
  ext u
  -- Apply the local finite-coordinate direct-sum splitting theorem, then rewrite each coordinate
  -- conjugate with Example 13.2 and fold the sum back into the direct-sum owner.
  rw [conjugate_directSumFunction_eq_sum_conjugate_fin]
  calc
    ∑ i, ((fun x : ℝ ↦ |x| ^ p / p).toEReal.asEReal)∗ (u i)
        = ∑ i,
            ((fun x : ℝ ↦
              |x| ^ Real.conjExponent p / Real.conjExponent p).toEReal.asEReal) (u i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using conjugate_absRpowDivided p hp (u i)
    _ = (directSumFunction
          (fun _ : Fin N ↦
            (fun t : ℝ ↦ |t| ^ Real.conjExponent p / Real.conjExponent p).toEReal)
          u : EReal) := by
            simp [directSumFunction_apply, Function.asEReal_apply]

-- Proof sketch: identify `ℝ^N` with the finite Hilbert direct sum of `N` copies of `ℝ`, apply
-- Example 13.2 coordinatewise to the scalar summand `t ↦ |t|^p / p`, and then use Proposition
-- 13.30 to pass the Fenchel conjugate through the finite direct sum. The coordinate `ℓ^p` norm is
-- the Chapter 7 owner `EuclideanSpace.lpNorm`, written `‖x‖_[p]`, so no separate local wrapper is
-- needed.
/-- Example 13 31: on `ℝ^N`, for `p ∈ ]1,+∞[`, the Fenchel conjugate of `x ↦ ‖x‖_p^p / p` is
`u ↦ ‖u‖_{p*}^{p*} / p*`, where `p* = Real.conjExponent p = p / (p - 1)`. -/
theorem fenchelConjugate_lpNormPowerDivided_eq_lpNormPowerDivided_conjExponent
    (N : ℕ) (p : ℝ) (hp : 1 < p) :
    (fun x : EuclideanSpace ℝ (Fin N) ↦
      ((‖x‖_[ENNReal.ofReal p] ^ p / p : ℝ) : EReal))∗ =
      fun u : EuclideanSpace ℝ (Fin N) ↦
        ((‖u‖_[ENNReal.ofReal (Real.conjExponent p)] ^ Real.conjExponent p /
          Real.conjExponent p : ℝ) : EReal) := by
  let f : ∀ i : Fin N, ℝ → Set.Ioi (⊥ : EReal) :=
    fun _ ↦ (fun t : ℝ ↦ |t| ^ p / p).toEReal
  let g : ∀ i : Fin N, ℝ → Set.Ioi (⊥ : EReal) :=
    fun _ ↦ (fun t : ℝ ↦ |t| ^ Real.conjExponent p / Real.conjExponent p).toEReal
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (Real.conjExponent p) := by
    simpa using Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < Real.conjExponent p := hpq.symm.pos
  -- Normalize the Euclidean-space function to the finite direct-sum owner, transport conjugation
  -- through `lpPiLpₗᵢ`, insert the coordinatewise scalar conjugate formula, and rewrite back.
  calc
    (fun x : EuclideanSpace ℝ (Fin N) ↦
      ((‖x‖_[ENNReal.ofReal p] ^ p / p : ℝ) : EReal))∗ =
        (fun x : EuclideanSpace ℝ (Fin N) ↦
          (directSumFunction f ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) : EReal))∗ := by
            congr 1
            simpa [f] using
              (directSum_abs_power_divided_eq_lpNorm_power_divided (N := N) (r := p) hp_pos).symm
    _ = fun u : EuclideanSpace ℝ (Fin N) ↦
          (directSumFunction f).asEReal∗ ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm u) := by
            simpa using
              conjugate_precompose_lpPiLp_symm (N := N) (F := (directSumFunction f).asEReal)
    _ = fun u : EuclideanSpace ℝ (Fin N) ↦
          (directSumFunction g ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm u) : EReal) := by
            funext u
            simpa [f, g] using
              congrFun
                (conjugate_directSum_abs_power_divided_eq_conjExponent (N := N) (p := p) hp)
                ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm u)
    _ = fun u : EuclideanSpace ℝ (Fin N) ↦
          ((‖u‖_[ENNReal.ofReal (Real.conjExponent p)] ^ Real.conjExponent p /
            Real.conjExponent p : ℝ) : EReal) := by
            simpa [g] using
              directSum_abs_power_divided_eq_lpNorm_power_divided
                (N := N) (r := Real.conjExponent p) hq_pos

end

end ERealFunction
