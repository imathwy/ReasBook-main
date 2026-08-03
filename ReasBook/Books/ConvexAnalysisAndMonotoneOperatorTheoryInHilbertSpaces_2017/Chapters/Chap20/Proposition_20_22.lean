import Mathlib
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_21
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: swap the coordinates of the graph. This transports monotonicity to `A⁻¹`,
-- and graph inclusion between monotone extensions is preserved by taking inverses, so maximality
-- transfers as well.
/-- Proposition 20.22 (1): the inverse of a maximally monotone set-valued operator is maximally
monotone. -/
theorem Maximal.inverse {A : SetValuedOperator H H}
    (hA : Maximal IsMonotone A) :
    Maximal IsMonotone A⁻¹ := by
  -- Transport the Minty criterion by swapping the graph coordinates.
  rw [maximal_iff_mem_iff]
  intro u x
  rw [mem_inverse_iff]
  constructor
  · intro hxu y v hyv
    -- Reinterpret a graph point of `A⁻¹` as a swapped graph point of `A`.
    have hyv' : y ∈ A v := by
      simpa [mem_inverse_iff] using hyv
    have hsource : 0 ≤ ⟪x - v, u - y⟫_ℝ :=
      (Maximal.mem_iff hA x u).1 hxu hyv'
    simpa [real_inner_comm] using hsource
  · intro hxu
    -- Test the inverse Minty relation against swapped graph points of `A`.
    exact (Maximal.mem_iff hA x u).2 fun {y v} hv ↦ by
      have hswapped : 0 ≤ ⟪u - v, x - y⟫_ℝ :=
        hxu (y := v) (v := y) (by simpa [mem_inverse_iff] using hv)
      simpa [real_inner_comm] using hswapped

/-- Helper for Proposition 20.22: membership in the affine perturbation is equivalent to
membership of the normalized output difference in the translated source fiber. -/
private theorem mem_const_add_smul_translate_iff
    {A : SetValuedOperator H H} (x w z u : H) (γ : Set.Ioi (0 : ℝ)) :
    w ∈ (((fun _ : H ↦ u).toSetValuedOperator) + (γ : ℝ) • A.translate (-z)) x ↔
      (γ : ℝ)⁻¹ • (w - u) ∈ A (x + z) := by
  have hγ : 0 < (γ : ℝ) := by
    exact γ.2
  constructor
  · intro hw
    -- Unpack the affine sum and normalize the scaled graph point back to `A`.
    rcases Set.mem_add.mp hw with ⟨a, ha, b, hb, habw⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at ha
    subst a
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne',
      SetValuedOperator.mem_translate_iff] at hb
    have hb_eq : b = w - u := by
      calc
        b = (u + b) - u := by abel_nf
        _ = w - u := by rw [habw]
    simpa [hb_eq, sub_eq_add_neg] using hb
  · intro hw
    -- Rebuild the affine graph point from the normalized source point.
    refine Set.mem_add.2 ⟨u, ?_, w - u, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne',
        SetValuedOperator.mem_translate_iff]
      simpa only [sub_neg_eq_add] using hw
    · abel_nf

/-- Helper for Proposition 20.22: the affine graph transform rescales the monotonicity pairing by
the positive factor `γ`. -/
private theorem affine_pairing_eq_smul_source_pairing
    (a b x y u z : H) (γ : Set.Ioi (0 : ℝ)) :
    ⟪x - y, (u + (γ : ℝ) • a) - (u + (γ : ℝ) • b)⟫_ℝ =
      (γ : ℝ) * ⟪(x + z) - (y + z), a - b⟫_ℝ := by
  -- Output translation cancels, input translation preserves differences, and the scaling factors
  -- out of the real inner product.
  calc
    ⟪x - y, (u + (γ : ℝ) • a) - (u + (γ : ℝ) • b)⟫_ℝ
        = ⟪x - y, (γ : ℝ) • a - (γ : ℝ) • b⟫_ℝ := by
          abel_nf
    _ = ⟪x - y, (γ : ℝ) • (a - b)⟫_ℝ := by
      rw [smul_sub]
    _ = (γ : ℝ) * ⟪x - y, a - b⟫_ℝ := by
      rw [inner_smul_right]
    _ = (γ : ℝ) * ⟪(x + z) - (y + z), a - b⟫_ℝ := by
      congr 1
      abel_nf

-- Proof sketch: view `x ↦ {u} + γ • A (x + z)` as the image of `A.graph` under the affine
-- automorphism `(x, a) ↦ (x - z, u + γ • a)` of `H × H`. Positive scaling and translations
-- preserve monotonicity, and the bijective transport of graph inclusion preserves maximality.
/-- Proposition 20.22 (2): for `z, u : H` and `γ ∈ ℝ_{++}`, the affine perturbation
`x ↦ {u} + γ • A (x + z)` of a maximally monotone operator is maximally monotone. -/
theorem Maximal.output_translation_smul_input_translation
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (z u : H) (γ : Set.Ioi (0 : ℝ)) :
    Maximal IsMonotone (((fun _ : H ↦ u).toSetValuedOperator) + (γ : ℝ) • A.translate (-z)) :=
  by
  have hγ : 0 < (γ : ℝ) := by
    exact γ.2
  -- Transport the Minty criterion through the affine graph normalization.
  rw [maximal_iff_mem_iff]
  intro x w
  constructor
  · intro hw y v hv
    -- Normalize both affine graph points back to graph points of `A`.
    let a : H := (γ : ℝ)⁻¹ • (w - u)
    let b : H := (γ : ℝ)⁻¹ • (v - u)
    have ha : a ∈ A (x + z) := by
      simpa [a] using
        (mem_const_add_smul_translate_iff (A := A) (x := x) (w := w) (z := z) (u := u)
          (γ := γ)).1 hw
    have hb : b ∈ A (y + z) := by
      simpa [b] using
        (mem_const_add_smul_translate_iff (A := A) (x := y) (w := v) (z := z) (u := u)
          (γ := γ)).1 hv
    have hsource : 0 ≤ ⟪(x + z) - (y + z), a - b⟫_ℝ :=
      (isMonotone_iff A).1 (Maximal.isMonotone hA) ha hb
    have hw_eq : w = u + (γ : ℝ) • a := by
      calc
        w = u + (w - u) := by
          abel_nf
        _ = u + (γ : ℝ) • a := by
          simp [a, smul_inv_smul₀ hγ.ne']
    have hv_eq : v = u + (γ : ℝ) • b := by
      calc
        v = u + (v - u) := by
          abel_nf
        _ = u + (γ : ℝ) • b := by
          simp [b, smul_inv_smul₀ hγ.ne']
    -- Rewrite the target pairing as the positive scalar `γ` times the source pairing.
    have hpairing :
        ⟪x - y, w - v⟫_ℝ =
          (γ : ℝ) * ⟪(x + z) - (y + z), a - b⟫_ℝ := by
      calc
        ⟪x - y, w - v⟫_ℝ
            = ⟪x - y, (u + (γ : ℝ) • a) - (u + (γ : ℝ) • b)⟫_ℝ := by
                rw [hw_eq, hv_eq]
        _ = (γ : ℝ) * ⟪(x + z) - (y + z), a - b⟫_ℝ := by
          simpa using affine_pairing_eq_smul_source_pairing a b x y u z γ
    rw [hpairing]
    exact mul_nonneg hγ.le hsource
  · intro hw
    -- Normalize the candidate affine graph point and apply maximality of `A`.
    let a : H := (γ : ℝ)⁻¹ • (w - u)
    have hw_eq : w = u + (γ : ℝ) • a := by
      calc
        w = u + (w - u) := by
          abel_nf
        _ = u + (γ : ℝ) • a := by
          simp [a, smul_inv_smul₀ hγ.ne']
    have hsource_rel : ∀ ⦃y b : H⦄, b ∈ A y → 0 ≤ ⟪(x + z) - y, a - b⟫_ℝ := by
      intro y b hb
      -- Test the affine Minty hypothesis on the graph point corresponding to `(y, b) ∈ gra A`.
      have htest :
          u + (γ : ℝ) • b ∈
            (((fun _ : H ↦ u).toSetValuedOperator) + (γ : ℝ) • A.translate (-z)) (y - z) := by
        rw [mem_const_add_smul_translate_iff (A := A) (x := y - z) (w := u + (γ : ℝ) • b)
          (z := z) (u := u) (γ := γ)]
        simpa [sub_eq_add_neg, inv_smul_smul₀ hγ.ne'] using hb
      have htransport : 0 ≤ ⟪x - (y - z), w - (u + (γ : ℝ) • b)⟫_ℝ :=
        hw (y := y - z) (v := u + (γ : ℝ) • b) htest
      -- Rewrite the affine pairing back to the source pairing and remove the positive factor.
      have hpairing :
          ⟪x - (y - z), w - (u + (γ : ℝ) • b)⟫_ℝ =
            (γ : ℝ) * ⟪(x + z) - y, a - b⟫_ℝ := by
        calc
          ⟪x - (y - z), w - (u + (γ : ℝ) • b)⟫_ℝ
              = ⟪x - (y - z), (u + (γ : ℝ) • a) - (u + (γ : ℝ) • b)⟫_ℝ := by
                  rw [hw_eq]
          _ = (γ : ℝ) * ⟪(x + z) - ((y - z) + z), a - b⟫_ℝ := by
            simpa using affine_pairing_eq_smul_source_pairing a b x (y - z) u z γ
          _ = (γ : ℝ) * ⟪(x + z) - y, a - b⟫_ℝ := by
            congr 1
            abel_nf
      rw [hpairing] at htransport
      exact nonneg_of_mul_nonneg_right htransport hγ
    have ha : a ∈ A (x + z) :=
      (Maximal.mem_iff hA (x + z) a).2 fun {y b} hb ↦ hsource_rel hb
    rw [mem_const_add_smul_translate_iff (A := A) (x := x) (w := w) (z := z) (u := u) (γ := γ)]
    simpa [a] using ha

end SetValuedOperator
