import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap15.Corollary_15_17
import BauschkeLean.Chap20.Proposition_20_22
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap20.Proposition_20_58

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 21.1 is Minty's range characterization for a monotone operator.
- `core/canonical`: the public owner notion is `Maximal IsMonotone A`.
- `bridge/view`: the range formula for `Id + A` is the source-facing characterization theorem,
  not a second owner abstraction. -/

/-- Helper for Theorem 21.1: on `H × H`, `halfSquaredNorm` splits as the sum of the coordinate
quadratics. -/
private theorem pair_halfSquaredNorm_eq_add (x u : H) :
    (halfSquaredNorm ((x, u) : H × H) : EReal) =
      (halfSquaredNorm x : EReal) + (halfSquaredNorm u : EReal) := by
  -- Rewrite the product norm through the canonical `ℓ²` model and simplify the resulting real
  -- identity.
  rw [halfSquaredNorm_apply, halfSquaredNorm_apply, halfSquaredNorm_apply]
  have hnorm :
      ‖((x, u) : H × H)‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) + ‖u‖ ^ (2 : ℕ) := by
    simpa using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 ((x, u) : H × H)))
  have hreal : ‖((x, u) : H × H)‖ ^ (2 : ℕ) / 2 = ‖x‖ ^ (2 : ℕ) / 2 + ‖u‖ ^ (2 : ℕ) / 2 := by
    nlinarith
  exact_mod_cast hreal

/-- Helper for Theorem 21.1: surjectivity of `Id + A` forces maximal monotonicity by the Minty
membership test. -/
private theorem maximal_of_range_id_add_eq_univ_aux
    (A : SetValuedOperator H H) (hA : A.IsMonotone)
    (hrange : ((id : H → H).toSetValuedOperator + A).range = Set.univ) :
    Maximal IsMonotone A := by
  -- Rewrite maximality into the graph-membership criterion and close the backward implication
  -- with the range witness at `x + u`.
  rw [maximal_iff_mem_iff]
  intro x u
  constructor
  · intro hxu y v hv
    exact (isMonotone_iff A).1 hA hxu hv
  · intro hMinty
    have hxu_range : x + u ∈ (((id : H → H).toSetValuedOperator + A).range) := by
      simpa [hrange]
    rcases
        (SetValuedOperator.mem_range_iff (((id : H → H).toSetValuedOperator + A)) (x + u)).1
          hxu_range with
      ⟨y, hy⟩
    change x + u ∈ ((id : H → H).toSetValuedOperator y + A y) at hy
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hy
    rcases hy with ⟨z, hz, v, hv, hzv⟩
    have hz' : z = y := by
      simpa using hz
    subst z
    have hzv' : y + v = x + u := by
      simpa [hz'] using hzv
    have hrel : 0 ≤ ⟪x - y, u - v⟫_ℝ := hMinty hv
    have hresid : u - v = y - x := by
      have hzero : u - v + (x - y) = 0 := by
        have : x + u - (y + v) = 0 := by
          rw [hzv']
          abel_nf
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hzero' : (u - v) - (y - x) = 0 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
      exact sub_eq_zero.mp hzero'
    have hsq_nonpos : ‖x - y‖ ^ (2 : ℕ) ≤ 0 := by
      have hnonneg : 0 ≤ -‖x - y‖ ^ (2 : ℕ) := by
        calc
          0 ≤ ⟪x - y, u - v⟫_ℝ := hrel
          _ = ⟪x - y, y - x⟫_ℝ := by
            rw [hresid]
          _ = -⟪x - y, x - y⟫_ℝ := by
            have hyx : y - x = -(x - y) := by
              abel_nf
            rw [hyx, inner_neg_right]
          _ = -‖x - y‖ ^ (2 : ℕ) := by
            rw [real_inner_self_eq_norm_sq]
      linarith
    have hsq_zero : ‖x - y‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hsq_nonpos (sq_nonneg ‖x - y‖)
    have hxy : x = y := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero))
    have huv : u = v := by
      calc
        u = x + u - x := by
          abel_nf
        _ = y + v - x := by
          rw [← hzv']
        _ = v := by
          rw [hxy]
          abel_nf
    subst y
    simpa [huv] using hv

/-- Helper for Theorem 21.1: a quadratic minorant of `F[A] + ½‖·‖²` on `H × H` yields the
affine lower bound used in the Fitzpatrick part of Minty's argument. -/
private theorem fitzpatrickAffineLowerBoundFromQuadraticWitness
    {A : SetValuedOperator H H} {v y : H}
    (hminor : ∀ p : H × H,
      (halfSquaredNorm (p + (v, y)) : EReal) ≤ F[A] p + (halfSquaredNorm p : EReal))
    (x u : H) :
    (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
      (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) := by
  -- Expand the translated quadratic once, then cancel the common `½‖(x, u)‖²` term on both sides.
  have hquad :
      (halfSquaredNorm (((x, u) : H × H) + (v, y)) : EReal) =
        ((halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
            (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal))) +
          (halfSquaredNorm ((x, u) : H × H) : EReal) := by
    rw [show (((x, u) : H × H) + (v, y)) = (x + v, u + y) by rfl]
    rw [pair_halfSquaredNorm_eq_add, pair_halfSquaredNorm_eq_add]
    have hx :
        (halfSquaredNorm x : EReal) = (((‖x‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply x)
    have hu :
        (halfSquaredNorm u : EReal) = (((‖u‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply u)
    have hv :
        (halfSquaredNorm v : EReal) = (((‖v‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply v)
    have hy :
        (halfSquaredNorm y : EReal) = (((‖y‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply y)
    have hxv0 :
        (halfSquaredNorm (x + v) : EReal) =
          (((‖x + v‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply (x + v))
    have huy0 :
        (halfSquaredNorm (u + y) : EReal) =
          (((‖u + y‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
      simpa using (halfSquaredNorm_apply (u + y))
    rw [hxv0, huy0, hv, hy, hx, hu]
    have hxv := norm_add_sq_real x v
    have huy := norm_add_sq_real u y
    have hreal :
        ‖x + v‖ ^ (2 : ℕ) / 2 + ‖u + y‖ ^ (2 : ℕ) / 2 =
          (‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + (⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ)) +
            (‖x‖ ^ (2 : ℕ) / 2 + ‖u‖ ^ (2 : ℕ) / 2) := by
      nlinarith [hxv, huy, real_inner_comm y u]
    exact_mod_cast hreal
  have hshift :
      ((halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
          (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal))) +
        (halfSquaredNorm ((x, u) : H × H) : EReal)
        ≤ F[A] (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) := by
    have hshift0 :
        (halfSquaredNorm (((x, u) : H × H) + (v, y)) : EReal)
          ≤ F[A] (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) :=
      hminor (x, u)
    rw [hquad] at hshift0
    exact hshift0
  have hbase :
      (halfSquaredNorm ((x, u) : H × H) : EReal) =
        (((‖((x, u) : H × H)‖ ^ (2 : ℕ)) / 2 : ℝ) : EReal) := by
    simpa using (halfSquaredNorm_apply ((x, u) : H × H))
  rw [hbase] at hshift
  have hcancel :
      (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
        (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) :=
    (EReal.addLECancellable_coe (((‖((x, u) : H × H)‖ ^ (2 : ℕ)) / 2 : ℝ))).add_le_add_iff_right.mp
      hshift
  simpa [add_assoc, add_left_comm, add_comm] using hcancel

/-- Helper for Theorem 21.1: a maximally monotone operator has nonempty domain. -/
private theorem dom_nonempty_of_maximal_local
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom.Nonempty := by
  -- If the domain were empty, the Minty membership test would force `(0, 0)` into the graph.
  by_contra hdom
  have hdom_empty : A.dom = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hdom ⟨x, hx⟩
  have hzero_mem : (0 : H) ∈ A (0 : H) := by
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := (mem_dom_iff A y).2 ⟨v, hv⟩
    simp [hdom_empty] at hy_dom
  have hzero_dom : (0 : H) ∈ A.dom := (mem_dom_iff A 0).2 ⟨0, hzero_mem⟩
  exact hdom ⟨0, hzero_dom⟩

/-- Helper for Theorem 21.1: a maximally monotone operator has `0` in the range of `Id + A`. -/
private theorem zero_mem_range_id_add_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    (0 : H) ∈ (((id : H → H).toSetValuedOperator + A).range) := by
  let hA_mono : A.IsMonotone := Maximal.isMonotone hA
  let hA_graph : (gra A).Nonempty := by
    rcases dom_nonempty_of_maximal_local A hA with ⟨x, hx⟩
    rcases hx with ⟨u, hu⟩
    exact ⟨(x, u), by simpa [SetValuedOperator.mem_graph] using hu⟩
  let hFA_proper : IsProper F[A] :=
    fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono
  let FA : H × H → Set.Ioi (⊥ : EReal) := properIoi (F[A]) hFA_proper
  have hFA_gamma : FA ∈ Γ₀(H × H) := by
    -- Package the Fitzpatrick function through `properIoi` so Corollary 15.17 applies directly.
    simpa [FA, hFA_proper] using fitzpatrickFunction_mem_gammaZero A hA_graph hA_mono
  have pair_halfSquaredNorm_nonneg :
      ∀ a b : H, (0 : EReal) ≤ pairing (a, b) + (halfSquaredNorm ((a, b) : H × H) : EReal) := by
    intro a b
    -- The product-space inequality is the square identity `0 ≤ ‖a + b‖²`.
    rw [pairing_apply, halfSquaredNorm_apply]
    have hnorm := norm_add_sq_real a b
    have hsplit :
        ‖((a, b) : H × H)‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + ‖b‖ ^ (2 : ℕ) := by
      simpa using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 ((a, b) : H × H)))
    exact_mod_cast by
      nlinarith [hnorm, hsplit]
  have hnonneg :
      ∀ p : H × H, (0 : EReal) ≤ (FA p : EReal) + (halfSquaredNorm p : EReal) := by
    rintro ⟨x, u⟩
    have hpair_half :
        (0 : EReal) ≤ pairing (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) :=
      pair_halfSquaredNorm_nonneg x u
    have hsum_le :
        pairing (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal)
          ≤ F[A] (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) := by
      exact add_le_add (Maximal.inner_le_fitzpatrickFunction hA x u) le_rfl
    calc
      (0 : EReal) ≤ pairing (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) := hpair_half
      _ ≤ F[A] (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) := hsum_le
      _ = (FA (x, u) : EReal) + (halfSquaredNorm ((x, u) : H × H) : EReal) := by
        simp [FA]
  obtain ⟨w, hw⟩ :=
    ERealFunction.exists_halfSquaredNorm_sub_le_pointwiseAdd (H := H × H) FA hFA_gamma hnonneg
  let v : H := -w.1
  let y : H := -w.2
  have hminor :
      ∀ p : H × H,
        (halfSquaredNorm (p + (v, y)) : EReal) ≤ F[A] p + (halfSquaredNorm p : EReal) := by
    intro p
    -- Rewrite the translated quadratic witness from Corollary 15.17 into the source coordinates.
    simpa [FA, v, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw p
  have hpair_nonneg_real :
      0 ≤ ‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + ⟪y, v⟫_ℝ := by
    have hnorm := norm_add_sq_real y v
    nlinarith
  have hyv : v ∈ A y := by
    -- The affine lower bound turns every graph point of `A` into a Minty test against `(y, v)`.
    refine (Maximal.mem_iff hA y v).2 ?_
    intro x u hxu
    have hbound :
        (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
          (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal))
          ≤ pairing (x, u) := by
      calc
        (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
            (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal))
            ≤ F[A] (x, u) :=
          fitzpatrickAffineLowerBoundFromQuadraticWitness hminor x u
        _ = pairing (x, u) := by
          rw [fitzpatrickFunction_eq_inner_of_mem_graph (A := A) hA_mono]
          simpa [SetValuedOperator.mem_graph] using hxu
    have hbound_real :
        ‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + (⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ) ≤ ⟪x, u⟫_ℝ := by
      rw [halfSquaredNorm_apply, halfSquaredNorm_apply, pairing_apply] at hbound
      exact_mod_cast hbound
    have hmono_real : 0 ≤ ⟪x - y, u - v⟫_ℝ := by
      have hineq :
          ⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
        nlinarith [hbound_real, hpair_nonneg_real]
      have hform :
          ⟪x - y, u - v⟫_ℝ =
            ⟪x, u⟫_ℝ - (⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ - ⟪y, v⟫_ℝ) := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right]
        ring
      nlinarith [hineq, hform]
    have hswap : ⟪y - x, v - u⟫_ℝ = ⟪x - y, u - v⟫_ℝ := by
      have hyx : y - x = -(x - y) := by
        abel_nf
      have hvu : v - u = -(u - v) := by
        abel_nf
      calc
        ⟪y - x, v - u⟫_ℝ = ⟪-(x - y), -(u - v)⟫_ℝ := by
          rw [hyx, hvu]
        _ = ⟪x - y, u - v⟫_ℝ := by
          rw [inner_neg_left, inner_neg_right]
          simp
    rwa [hswap]
  have hself :
      (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
        (((⟪y, v⟫_ℝ + ⟪y, v⟫_ℝ : ℝ) : EReal))
        ≤ pairing (y, v) := by
    -- Reuse the same affine lower bound at the graph point `(y, v)`.
    calc
      (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
          (((⟪y, v⟫_ℝ + ⟪y, v⟫_ℝ : ℝ) : EReal))
          ≤ F[A] (y, v) :=
        fitzpatrickAffineLowerBoundFromQuadraticWitness hminor y v
      _ = pairing (y, v) := by
        rw [fitzpatrickFunction_eq_inner_of_mem_graph (A := A) hA_mono]
        simpa [SetValuedOperator.mem_graph] using hyv
  have hself_real :
      ‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + (⟪y, v⟫_ℝ + ⟪y, v⟫_ℝ) ≤ ⟪y, v⟫_ℝ := by
    rw [halfSquaredNorm_apply, halfSquaredNorm_apply, pairing_apply] at hself
    exact_mod_cast hself
  have hsum_nonpos : ‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + ⟪y, v⟫_ℝ ≤ 0 := by
    nlinarith
  have hsum_zero : ‖v‖ ^ (2 : ℕ) / 2 + ‖y‖ ^ (2 : ℕ) / 2 + ⟪y, v⟫_ℝ = 0 := by
    exact le_antisymm hsum_nonpos hpair_nonneg_real
  have hsq_zero : ‖y + v‖ ^ (2 : ℕ) = 0 := by
    have hnorm := norm_add_sq_real y v
    nlinarith [hsum_zero, hnorm]
  have hyv_eq_zero : y + v = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero)
  -- Convert the recovered graph point `(y, v)` with `y + v = 0` into the desired range witness.
  exact
    (SetValuedOperator.mem_range_iff (((id : H → H).toSetValuedOperator + A)) 0).2
      ⟨y, by
        change 0 ∈ ((id : H → H).toSetValuedOperator y + A y)
        rw [Function.toSetValuedOperator_apply, Set.mem_add]
        refine ⟨y, by simp, v, hyv, ?_⟩
        simpa [add_comm] using hyv_eq_zero⟩

/- Source/core/bridge triage:
- `source-facing`: Theorem 21.1 is Minty's range characterization for a monotone operator.
- `core/canonical`: the owner abstraction is maximal monotonicity `Maximal IsMonotone A`.
- `bridge/view`: the theorem states that this owner is equivalent to the surjectivity of
  `Id + A`. -/
/-- Theorem 21.1 (Minty): let `A : H → 2^H` be monotone. Then `A` is maximally monotone if and
only if `ran (Id + A) = H`, formalized as
`((id : H → H).toSetValuedOperator + A).range = Set.univ`. -/
theorem maximal_iff_range_id_add_eq_univ
    (A : SetValuedOperator H H) (hA : A.IsMonotone) :
    Maximal IsMonotone A ↔
      ((id : H → H).toSetValuedOperator + A).range = Set.univ := by
  constructor
  · intro hAmax
    ext w
    constructor
    · intro _
      simp
    · intro _
      -- Route correction: reduce the surjectivity statement to the zero-case by translating the
      -- operator output by `-w`, then pull the resulting witness back to `Id + A`.
      have hshift :
          Maximal IsMonotone (((fun _ : H ↦ -w).toSetValuedOperator) + A) := by
        have hshift0 :
            Maximal IsMonotone
              (((fun _ : H ↦ -w).toSetValuedOperator) + (1 : ℝ) • A.translate (-0)) :=
          Maximal.output_translation_smul_input_translation
            (A := A) hAmax 0 (-w) (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))
        have htranslate0 :
            (((fun _ : H ↦ -w).toSetValuedOperator) + (1 : ℝ) • A.translate (-0)) =
              (((fun _ : H ↦ -w).toSetValuedOperator) + A) := by
          ext x u
          simp [SetValuedOperator.translate]
        exact htranslate0 ▸ hshift0
      have hzero :
          (0 : H) ∈
            (((id : H → H).toSetValuedOperator + (((fun _ : H ↦ -w).toSetValuedOperator) + A)).range) :=
        zero_mem_range_id_add_of_maximal (((fun _ : H ↦ -w).toSetValuedOperator) + A) hshift
      rcases
          (SetValuedOperator.mem_range_iff
            (((id : H → H).toSetValuedOperator + (((fun _ : H ↦ -w).toSetValuedOperator) + A))) 0).1
            hzero with
        ⟨y, hy⟩
      change 0 ∈ ((id : H → H).toSetValuedOperator y + ((((fun _ : H ↦ -w).toSetValuedOperator) + A) y)) at hy
      rw [Function.toSetValuedOperator_apply, Set.mem_add] at hy
      rcases hy with ⟨a, ha, b, hb, hab0⟩
      have ha' : a = y := by
        simpa using ha
      subst a
      change b ∈ ((fun _ : H ↦ -w).toSetValuedOperator y + A y) at hb
      rw [Function.toSetValuedOperator_apply, Set.mem_add] at hb
      rcases hb with ⟨c, hc, v, hv, hcvb⟩
      have hc' : c = -w := by
        simpa using hc
      subst c
      have hywv : y + (-w + v) = 0 := by
        calc
          y + (-w + v) = y + b := by
            rw [← hcvb]
          _ = 0 := hab0
      have hw_eq : w = y + v := by
        have hsum : y + (-w + v) + w = y + v := by
          abel_nf
        rw [hywv] at hsum
        simpa using hsum
      exact
        (SetValuedOperator.mem_range_iff (((id : H → H).toSetValuedOperator + A)) w).2
          ⟨y, by
            change w ∈ ((id : H → H).toSetValuedOperator y + A y)
            rw [Function.toSetValuedOperator_apply, Set.mem_add]
            exact ⟨y, by simp, v, hv, hw_eq.symm⟩⟩
  · intro hrange
    -- The reverse implication is the direct Minty argument at the range witness for `x + u`.
    exact maximal_of_range_id_add_eq_univ_aux A hA hrange

end SetValuedOperator
