import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap02.Lemma_2_45
import BauschkeLean.Chap03.Proposition_3_45
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Definition_20_51
import BauschkeLean.Chap20.Proposition_20_38
import BauschkeLean.Chap20.Proposition_20_56
import BauschkeLean.Chap20.Proposition_20_58
import BauschkeLean.Chap15.Corollary_15_17
import BauschkeLean.Chap21.Proposition_21_11

open ERealFunction
open Filter
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
- `source-facing`: Proposition 21.12 compares `A.dom` with the first-coordinate projection
  `Q₁ (dom F_A)` from the textbook.
- `core/canonical`: the chapter owners are `F[A]` and, for the closure/interior identities,
  `Maximal IsMonotone A`.
- `bridge/view`: the projected Fitzpatrick-domain sets are the thin views
  `A.fstImageDomFitzpatrick` and `A.sndImageDomFitzpatrick`; they are not second root owners.

Primitive data: `A` and its Fitzpatrick owner `F[A]`.
Derived API: the interior, closure, and inclusion relations between `A.dom` and
`A.fstImageDomFitzpatrick`, together with the inverse bridge identifying
`A.sndImageDomFitzpatrick` with `(A⁻¹).fstImageDomFitzpatrick`. -/

-- Semantic recall: `lean_leansearch` returned only generic closure/interior facts, so the
-- Chapter 21 Fitzpatrick-domain bridges remain project-local owners.

/-- The first-coordinate projection `Q₁ (dom F_A)` of the domain of the Fitzpatrick function of
`A`, formalized as the image of `dom (F[A])` under `Prod.fst`. This is a thin bridge/view on top
of the core owner `F[A]`. -/
abbrev fstImageDomFitzpatrick (A : SetValuedOperator H H) : Set H :=
  Prod.fst '' ERealFunction.dom (F[A])

/-- The second-coordinate projection `Q₂ (dom F_A)` of the domain of the Fitzpatrick function of
`A`, formalized as the image of `dom (F[A])` under `Prod.snd`. This is the direct thin bridge/view
on top of the core owner `F[A]` used for the range-side clauses of Corollary 21.14. -/
abbrev sndImageDomFitzpatrick (A : SetValuedOperator H H) : Set H :=
  Prod.snd '' ERealFunction.dom (F[A])

omit [CompleteSpace H] in
/-- The second textbook projection `Q₂ (dom F_A)` is exactly the first projection of the inverse
Fitzpatrick domain `Q₁ (dom F_{A⁻¹})`. -/
theorem sndImageDomFitzpatrick_eq_fstImageDomFitzpatrick_inverse
    (A : SetValuedOperator H H) :
    A.sndImageDomFitzpatrick = (A⁻¹).fstImageDomFitzpatrick := by
  ext u
  constructor
  · rintro ⟨⟨x, u⟩, hu, rfl⟩
    refine ⟨(u, x), ?_, rfl⟩
    exact (mem_dom_iff_ne_top _ _).2 <|
      by simpa [fitzpatrickFunction_inverse_eq_transpose, transpose_apply] using
        (mem_dom_iff_ne_top (F[A]) (x, u)).1 hu
  · rintro ⟨⟨u, x⟩, hu, rfl⟩
    refine ⟨(x, u), ?_, rfl⟩
    exact (mem_dom_iff_ne_top _ _).2 <|
      by simpa [fitzpatrickFunction_inverse_eq_transpose, transpose_apply] using
        (mem_dom_iff_ne_top (F[A⁻¹]) (u, x)).1 hu

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: a maximally monotone operator has a nonempty graph. -/
private theorem dom_nonempty_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom.Nonempty := by
  by_contra hdom
  have hdom_empty : A.dom = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hdom ⟨x, hx⟩
  have hzero_mem : (0 : H) ∈ A (0 : H) := by
    -- The Minty test is vacuous if the domain is empty.
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := (SetValuedOperator.mem_dom_iff A y).2 ⟨v, hv⟩
    simp [hdom_empty] at hy_dom
  have hzero_dom : (0 : H) ∈ A.dom := (SetValuedOperator.mem_dom_iff A 0).2 ⟨0, hzero_mem⟩
  exact hdom ⟨0, hzero_dom⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: a maximally monotone operator has a nonempty graph. -/
private theorem graph_nonempty_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    (gra A).Nonempty := by
  rcases dom_nonempty_of_maximal A hA with ⟨x, hx⟩
  rcases (SetValuedOperator.mem_dom_iff A x).1 hx with ⟨u, hu⟩
  exact ⟨(x, u), hu⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 21.12: on `H × H`, `halfSquaredNorm` splits into the sum of the two
coordinate quadratics. -/
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

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: a quadratic minorant of `F[A] + ½‖·‖²` on `H × H` produces the
affine Fitzpatrick lower bound used in Minty's argument. -/
private theorem fitzpatrickAffineLowerBoundFromQuadraticWitness
    {A : SetValuedOperator H H} {v y : H}
    (hminor : ∀ p : H × H,
      (halfSquaredNorm (p + (v, y)) : EReal) ≤ F[A] p + (halfSquaredNorm p : EReal))
    (x u : H) :
    (halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
      (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) := by
  have hquad :
      (halfSquaredNorm (((x, u) : H × H) + (v, y)) : EReal) =
        ((halfSquaredNorm v : EReal) + (halfSquaredNorm y : EReal) +
            (((⟪x, v⟫_ℝ + ⟪y, u⟫_ℝ : ℝ) : EReal))) +
          (halfSquaredNorm ((x, u) : H × H) : EReal) := by
    -- Expand the translated quadratic once and collect the affine term.
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

/-- Helper for Proposition 21.12: a maximally monotone operator has `0` in the range of `Id + A`.
-/
private theorem zero_mem_range_id_add_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    (0 : H) ∈ (((id : H → H).toSetValuedOperator + A).range) := by
  let hA_mono : A.IsMonotone := Maximal.isMonotone hA
  let hA_graph : (gra A).Nonempty := graph_nonempty_of_maximal A hA
  let hFA_proper : IsProper F[A] :=
    fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone A hA_graph hA_mono
  let FA : H × H → Set.Ioi (⊥ : EReal) := properIoi (F[A]) hFA_proper
  have hFA_gamma : FA ∈ Γ₀(H × H) := by
    simpa [FA, hFA_proper] using fitzpatrickFunction_mem_gammaZero A hA_graph hA_mono
  have hnonneg :
      ∀ p : H × H, (0 : EReal) ≤ (FA p : EReal) + (halfSquaredNorm p : EReal) := by
    rintro ⟨x, u⟩
    have hpair_half :
        (0 : EReal) ≤ pairing (x, u) + (halfSquaredNorm ((x, u) : H × H) : EReal) := by
      rw [pairing_apply, halfSquaredNorm_apply]
      have hnorm := norm_add_sq_real x u
      have hsplit :
          ‖((x, u) : H × H)‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) + ‖u‖ ^ (2 : ℕ) := by
        simpa using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 ((x, u) : H × H)))
      exact_mod_cast by
        nlinarith [hnorm, hsplit]
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

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: every graph point of a monotone operator gives a first-coordinate
Fitzpatrick-domain witness. -/
private theorem mem_fstImageDomFitzpatrick_of_mem_dom
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) {x : H} (hx : x ∈ A.dom) :
    x ∈ A.fstImageDomFitzpatrick := by
  rcases (SetValuedOperator.mem_dom_iff A x).1 hx with ⟨u, hu⟩
  refine ⟨(x, u), ?_, rfl⟩
  refine (mem_dom_iff_ne_top _ _).2 ?_
  rw [fitzpatrickFunction_eq_inner_of_mem_graph A hA_mono hu]
  exact EReal.coe_ne_top _

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: the first inclusion in `(21.34)` follows from monotonicity,
which keeps graph witnesses finite in the Fitzpatrick domain. -/
theorem interior_dom_subset_interior_fst_image_dom_fitzpatrick
    (A : SetValuedOperator H H) (hA_mono : A.IsMonotone) :
    interior A.dom ⊆ interior A.fstImageDomFitzpatrick := by
  have hsubset : A.dom ⊆ A.fstImageDomFitzpatrick := by
    intro x hx
    exact mem_fstImageDomFitzpatrick_of_mem_dom A hA_mono hx
  -- The inclusion on interiors is the topological upgrade of the pointwise graph-witness bridge.
  exact interior_mono hsubset

omit [CompleteSpace H] in
/-- First clause of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`interior A.dom ⊆ interior (A.fstImageDomFitzpatrick)`. -/
theorem interior_dom_subset_interior_fst_image_dom_fitzpatrick_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    interior A.dom ⊆ interior A.fstImageDomFitzpatrick := by
  -- The helper only needs monotonicity, which comes for free from maximality.
  exact interior_dom_subset_interior_fst_image_dom_fitzpatrick A (Maximal.isMonotone hA)

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: the first-coordinate projection of `dom (F[A])` is convex for a
maximally monotone operator. -/
private theorem convex_fstImageDomFitzpatrick_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    Convex ℝ A.fstImageDomFitzpatrick := by
  let FA : H × H → Set.Ioi (⊥ : EReal) :=
    properIoi (F[A])
      (fitzpatrickFunction_isProper_of_graph_nonempty_of_monotone
        A (graph_nonempty_of_maximal A hA) (Maximal.isMonotone hA))
  have hFA : FA ∈ Γ₀(H × H) := by
    -- Package the Fitzpatrick function into the canonical `Γ₀` interface.
    simpa [FA] using
      fitzpatrickFunction_mem_gammaZero
        A (graph_nonempty_of_maximal A hA) (Maximal.isMonotone hA)
  -- Project the convex effective domain to the first coordinate.
  simpa [fstImageDomFitzpatrick, FA, ERealFunction.effectiveDomain, ERealFunction.dom] using
    hFA.2.convex_effectiveDomain.linear_image (ContinuousLinearMap.fst ℝ H H).toLinearMap

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: a zero of `Id + γ • A.translate (-x)` yields a graph point
`a ∈ A y` whose displacement from `x` is `-(γ • a)`. -/
private theorem scaledRangeWitnessToGraphWitness
    {A : SetValuedOperator H H} {x : H} (γ : Set.Ioi (0 : ℝ))
    (hzero :
      (0 : H) ∈ (((id : H → H).toSetValuedOperator + (γ : ℝ) • A.translate (-x)).range)) :
    ∃ y a, a ∈ A y ∧ y - x = -((γ : ℝ) • a) := by
  have hγ : 0 < (γ : ℝ) := γ.2
  rcases
      (SetValuedOperator.mem_range_iff
        (((id : H → H).toSetValuedOperator + (γ : ℝ) • A.translate (-x))) 0).1 hzero with
    ⟨z, hz⟩
  change 0 ∈ ((id : H → H).toSetValuedOperator z + ((γ : ℝ) • A.translate (-x)) z) at hz
  rw [Function.toSetValuedOperator_apply, Set.mem_add] at hz
  rcases hz with ⟨b, hb, c, hc, hbc⟩
  have hbz : b = z := by
    simpa using hb
  subst b
  rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne', SetValuedOperator.mem_translate_iff]
    at hc
  let a : H := (γ : ℝ)⁻¹ • c
  let y : H := z + x
  have ha : a ∈ A y := by
    -- Normalize the translated/scaled witness back to the original graph of `A`.
    simpa [a, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hc
  have hz_eq : z = -c := by
    have hbc0 : z + c = 0 := by
      simpa using hbc
    calc
      z = z + c - c := by
        abel_nf
      _ = 0 - c := by rw [hbc0]
      _ = -c := by simp
  have hc_eq : c = (γ : ℝ) • a := by
    -- Undo the normalization used to define `a`.
    dsimp [a]
    simp [smul_inv_smul₀ hγ.ne']
  refine ⟨y, a, ha, ?_⟩
  -- Translate the recovered zero of `Id + γ • A.translate (-x)` into the source displacement.
  calc
    y - x = z := by
      dsimp [y]
      abel_nf
    _ = -c := hz_eq
    _ = -((γ : ℝ) • a) := by rw [hc_eq]

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: any graph witness `(y, a) ∈ gra A` bounds the displacement
expression `-⟪y - x, a⟫ + ⟪y - x, u⟫` by the finite Fitzpatrick value at `(x, u)`. -/
private theorem fitzpatrickApproximationInequality
    {A : SetValuedOperator H H} {x u y a : H} {β : ℝ}
    (ha : a ∈ A y) (hFA_top : F[A] (x, u) ≠ ⊤)
    (hβ_fitz : (F[A] (x, u)).toReal ≤ β) (hβ_xu : ‖x‖ * ‖u‖ ≤ β) :
    -⟪y - x, a⟫_ℝ + ⟪y - x, u⟫_ℝ ≤ 2 * β := by
  let p : gra A := ⟨(y, a), ha⟩
  have hfitz :
      (((⟪y, u⟫_ℝ + ⟪x, a⟫_ℝ - ⟪y, a⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) := by
    -- Evaluate the Fitzpatrick supremum at the concrete graph point `(y, a)`.
    exact le_iSup
      (fun q : gra A ↦
        (((⟪q.1.1, u⟫_ℝ + ⟪x, q.1.2⟫_ℝ - ⟪q.1.1, q.1.2⟫_ℝ : ℝ) : EReal))) p
  have hfitz_real :
      ⟪y, u⟫_ℝ + ⟪x, a⟫_ℝ - ⟪y, a⟫_ℝ ≤ (F[A] (x, u)).toReal := by
    -- Convert the finite Fitzpatrick upper bound from `EReal` to `ℝ`.
    exact EReal.toReal_le_toReal hfitz (EReal.coe_ne_bot _) hFA_top
  have hinner :
      -⟪x, u⟫_ℝ ≤ β := by
    -- The remaining source term is controlled by Cauchy-Schwarz and the `β` definition.
    have hcs : |⟪x, u⟫_ℝ| ≤ ‖x‖ * ‖u‖ := by
      simpa using abs_real_inner_le_norm x u
    have hneg : -⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := by
      have habs := abs_le.mp hcs
      nlinarith
    exact le_trans hneg hβ_xu
  have hsplit :
      -⟪y - x, a⟫_ℝ + ⟪y - x, u⟫_ℝ =
        (⟪y, u⟫_ℝ + ⟪x, a⟫_ℝ - ⟪y, a⟫_ℝ) - ⟪x, u⟫_ℝ := by
    -- Expand both displacement inner products once and collect the source terms.
    rw [inner_sub_left, inner_sub_left]
    ring
  rw [hsplit]
  nlinarith

omit [CompleteSpace H] in
/-- Helper for Proposition 21.12: the displacement identity `y - x = -(γ • a)` turns the
Fitzpatrick bound into the quadratic norm inequality used in the approximation argument. -/
private theorem quadraticDistanceBoundOfScaledGraphWitness
    {x y u a : H} {β : ℝ} (γ : Set.Ioi (0 : ℝ))
    (hyx : y - x = -((γ : ℝ) • a))
    (hfitz : -⟪y - x, a⟫_ℝ + ⟪y - x, u⟫_ℝ ≤ 2 * β)
    (hβ_u : ‖u‖ ≤ β) :
    ‖y - x‖ ^ (2 : ℕ) - ((γ : ℝ) * β) * ‖y - x‖ - 2 * ((γ : ℝ) * β) ≤ 0 := by
  have hγ : 0 < (γ : ℝ) := γ.2
  have hsq :
      ‖y - x‖ ^ (2 : ℕ) = -((γ : ℝ) * ⟪y - x, a⟫_ℝ) := by
    -- Rewrite the norm square through the displacement identity `y - x = -(γ • a)`.
    calc
      ‖y - x‖ ^ (2 : ℕ) = ⟪y - x, y - x⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ⟪y - x, -((γ : ℝ) • a)⟫_ℝ := by rw [hyx]
      _ = -((γ : ℝ) * ⟪y - x, a⟫_ℝ) := by
        rw [inner_neg_right, inner_smul_right]
  have hscaled :
      (γ : ℝ) * (-⟪y - x, a⟫_ℝ + ⟪y - x, u⟫_ℝ) ≤ (γ : ℝ) * (2 * β) := by
    -- Multiply the Fitzpatrick inequality by the positive scalar `γ`.
    exact mul_le_mul_of_nonneg_left hfitz hγ.le
  have hcs : |⟪y - x, u⟫_ℝ| ≤ ‖y - x‖ * ‖u‖ := by
    simpa using abs_real_inner_le_norm (y - x) u
  have hinner_lower : -(‖y - x‖ * ‖u‖) ≤ ⟪y - x, u⟫_ℝ := by
    exact (abs_le.mp hcs).1
  have hinner_beta : -(‖y - x‖ * β) ≤ ⟪y - x, u⟫_ℝ := by
    -- Replace `‖u‖` by the larger bound `β`.
    have hmul : ‖y - x‖ * ‖u‖ ≤ ‖y - x‖ * β := by
      gcongr
    nlinarith
  have hgamma_inner :
      -((γ : ℝ) * β) * ‖y - x‖ ≤ (γ : ℝ) * ⟪y - x, u⟫_ℝ := by
    -- Scale the lower bound on the mixed inner product by `γ`.
    have hscaled_inner := mul_le_mul_of_nonneg_left hinner_beta hγ.le
    nlinarith [hscaled_inner]
  -- Combine the squared-norm identity with the scaled mixed-term lower bound.
  nlinarith [hscaled, hgamma_inner, hsq]

/-- Helper for Proposition 21.12: the quadratic inequality from the Minty approximation forces the
norm variable to lie strictly below `η`. -/
private theorem quadraticBoundForcesSmallNorm
    {η r : ℝ} (hη : 0 < η) (hη_one : η ≤ 1)
    (hquad : r ^ (2 : ℕ) - (η ^ (2 : ℕ) / 4) * r - 2 * (η ^ (2 : ℕ) / 4) ≤ 0) :
    r < η := by
  by_contra hrη
  have hηr : η ≤ r := le_of_not_gt hrη
  -- Once `r` reaches `η`, the quadratic left-hand side is strictly positive because `η ≤ 1`.
  have hlower :
      η ^ (2 : ℕ) * (2 - η) / 4 ≤
        r ^ (2 : ℕ) - (η ^ (2 : ℕ) / 4) * r - 2 * (η ^ (2 : ℕ) / 4) := by
    have hprod_nonneg : 0 ≤ (r - η) * (4 * r + 4 * η - η ^ (2 : ℕ)) := by
      have hleft : 0 ≤ r - η := sub_nonneg.mpr hηr
      have hright : 0 ≤ 4 * r + 4 * η - η ^ (2 : ℕ) := by
        nlinarith [hηr, hη_one]
      exact mul_nonneg hleft hright
    have hfac :
        4 *
            (r ^ (2 : ℕ) - (η ^ (2 : ℕ) / 4) * r - 2 * (η ^ (2 : ℕ) / 4)) -
          η ^ (2 : ℕ) * (2 - η) =
            (r - η) * (4 * r + 4 * η - η ^ (2 : ℕ)) := by
      ring
    nlinarith [hprod_nonneg, hfac]
  have hpos : 0 < η ^ (2 : ℕ) * (2 - η) / 4 := by
    nlinarith
  have hnonpos : η ^ (2 : ℕ) * (2 - η) / 4 ≤ 0 := le_trans hlower hquad
  exact (not_le_of_gt hpos) hnonpos

/-- Helper for Proposition 21.12: every point in `Q₁ (dom F_A)` can be approximated arbitrarily
closely by points of `dom A`. -/
private theorem exists_mem_dom_dist_lt_of_mem_fstImageDomFitzpatrick
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) {x : H}
    (hx : x ∈ A.fstImageDomFitzpatrick) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ A.dom, dist x y < ε := by
  -- Route correction: isolate the affine transport, the Fitzpatrick-to-real inequality, and the
  -- final quadratic estimate instead of mixing them in one large proof term.
  rcases hx with ⟨⟨x, u⟩, hxu, rfl⟩
  let η : ℝ := min ε 1
  let β₀ : ℝ := max (F[A] (x, u)).toReal (max ‖u‖ (‖x‖ * ‖u‖))
  let β : ℝ := max 1 β₀
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hε zero_lt_one
  have hη_le_ε : η ≤ ε := by
    dsimp [η]
    exact min_le_left _ _
  have hη_one : η ≤ 1 := by
    dsimp [η]
    exact min_le_right _ _
  have hFA_top : F[A] (x, u) ≠ ⊤ := by
    exact (mem_dom_iff_ne_top _ _).1 hxu
  have hβ_one : 1 ≤ β := by
    dsimp [β]
    exact le_max_left _ _
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_one
  have hβ_fitz : (F[A] (x, u)).toReal ≤ β := by
    dsimp [β, β₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hβ_u : ‖u‖ ≤ β := by
    dsimp [β, β₀]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hβ_xu : ‖x‖ * ‖u‖ ≤ β := by
    dsimp [β, β₀]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  let γ : Set.Ioi (0 : ℝ) := ⟨η ^ (2 : ℕ) / (4 * β), by
    have hfourβ : 0 < 4 * β := by
      positivity
    exact div_pos (pow_pos hη_pos 2) hfourβ⟩
  have hshift0 :
      Maximal IsMonotone
        (((fun _ : H ↦ 0).toSetValuedOperator) + (γ : ℝ) • A.translate (-x)) :=
    Maximal.output_translation_smul_input_translation (A := A) hA x 0 γ
  have hzero_shift :
      (((fun _ : H ↦ 0).toSetValuedOperator) + (γ : ℝ) • A.translate (-x)) =
        (γ : ℝ) • A.translate (-x) := by
    ext z c
    constructor
    · intro hzc
      rcases Set.mem_add.mp hzc with ⟨b, hb, d, hd, hbd⟩
      have hb0 : b = 0 := by
        simpa [Function.toSetValuedOperator_apply] using hb
      subst b
      have hdc : d = c := by
        simpa using hbd
      exact hdc.symm ▸ hd
    · intro hc
      exact Set.mem_add.2 ⟨0, by simp [Function.toSetValuedOperator_apply], c, hc, by simp⟩
  have hscaled_max : Maximal IsMonotone ((γ : ℝ) • A.translate (-x)) := by
    -- Remove the harmless output translation by `0` from the maximality statement.
    exact hzero_shift ▸ hshift0
  have hzero :
      (0 : H) ∈ (((id : H → H).toSetValuedOperator + (γ : ℝ) • A.translate (-x)).range) :=
    zero_mem_range_id_add_of_maximal ((γ : ℝ) • A.translate (-x)) hscaled_max
  rcases scaledRangeWitnessToGraphWitness (A := A) (x := x) γ hzero with ⟨y, a, ha, hyx⟩
  have hyDom : y ∈ A.dom := by
    exact (SetValuedOperator.mem_dom_iff A y).2 ⟨a, ha⟩
  have hfitz :
      -⟪y - x, a⟫_ℝ + ⟪y - x, u⟫_ℝ ≤ 2 * β :=
    fitzpatrickApproximationInequality (A := A) ha hFA_top hβ_fitz hβ_xu
  have hquad :
      ‖y - x‖ ^ (2 : ℕ) - ((γ : ℝ) * β) * ‖y - x‖ - 2 * ((γ : ℝ) * β) ≤ 0 :=
    quadraticDistanceBoundOfScaledGraphWitness γ hyx hfitz hβ_u
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hγβ : ((γ : ℝ) * β) = η ^ (2 : ℕ) / 4 := by
    -- The specific scaling choice turns the quadratic coefficient into `η² / 4`.
    dsimp [γ]
    field_simp [hβ_ne]
  have hquad_eta :
      ‖y - x‖ ^ (2 : ℕ) - (η ^ (2 : ℕ) / 4) * ‖y - x‖ - 2 * (η ^ (2 : ℕ) / 4) ≤ 0 := by
    simpa [hγβ] using hquad
  have hnorm_lt : ‖y - x‖ < η :=
    quadraticBoundForcesSmallNorm hη_pos hη_one hquad_eta
  refine ⟨y, hyDom, ?_⟩
  -- Convert the norm estimate back to a metric estimate and compare `η` with `ε`.
  simpa [dist_eq_norm, norm_sub_rev] using lt_of_lt_of_le hnorm_lt hη_le_ε

/-- Second clause of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`interior (A.fstImageDomFitzpatrick) ⊆ A.dom`. -/
theorem interior_fst_image_dom_fitzpatrick_subset_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    interior A.fstImageDomFitzpatrick ⊆ A.dom := by
  classical
  intro x hx
  have hx_closure : x ∈ closure A.dom := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases exists_mem_dom_dist_lt_of_mem_fstImageDomFitzpatrick A hA (interior_subset hx) hε with
      ⟨y, hyDom, hxy⟩
    exact ⟨y, hyDom, hxy⟩
  rcases
      isLocallyBoundedAt_of_mem_interior_fst_image_dom_fitzpatrick
        A (Maximal.isMonotone hA) hx with
    ⟨ρ, hρ, hbounded⟩
  have happrox :
      ∀ n : ℕ, ∃ y ∈ A.dom, dist x y < min ρ (1 / (n + 1 : ℝ)) := by
    intro n
    have hδ : 0 < min ρ (1 / (n + 1 : ℝ)) := by
      refine lt_min hρ ?_
      positivity
    rcases (Metric.mem_closure_iff.1 hx_closure) (min ρ (1 / (n + 1 : ℝ))) hδ with
      ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  choose y hyDom hyDist using happrox
  choose u hu using fun n ↦ (SetValuedOperator.mem_dom_iff A (y n)).1 (hyDom n)
  have hu_bounded : Bornology.IsBounded (Set.range u) := by
    refine hbounded.subset ?_
    rintro _ ⟨n, rfl⟩
    refine (SetValuedOperator.mem_image A (Metric.ball x ρ) (u n)).2 ?_
    refine ⟨y n, ?_, hu n⟩
    have hy_ball : dist x (y n) < ρ := lt_of_lt_of_le (hyDist n) (min_le_left _ _)
    simpa [Metric.mem_ball, dist_comm] using hy_ball
  rcases bounded_sequence_has_weakly_convergent_subsequence u hu_bounded with
    ⟨v, φ, hφ, hφweak⟩
  have hy_tendsto : Tendsto (fun n ↦ y (φ n)) atTop (nhds x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hφn : N ≤ φ n := by
      exact le_trans hn (StrictMono.id_le hφ n)
    have hy_lt :
        dist (y (φ n)) x < 1 / (φ n + 1 : ℝ) := by
      have hy_lt' : dist x (y (φ n)) < 1 / (φ n + 1 : ℝ) :=
        (lt_of_lt_of_le (hyDist (φ n)) (min_le_right _ _))
      simpa [dist_comm] using hy_lt'
    have hcast : (N + 1 : ℝ) ≤ φ n + 1 := by
      exact_mod_cast Nat.succ_le_succ hφn
    have hdiv : 1 / (φ n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hcast
    exact lt_trans (lt_of_lt_of_le hy_lt hdiv) hN
  have hu_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ u (φ n)) := by
    refine hu_bounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨φ n, rfl⟩
  have hy_sub_bounded : Bornology.IsBounded (Set.range fun n ↦ y (φ n)) :=
    Metric.isBounded_range_of_tendsto _ hy_tendsto
  have hgraph_bounded :
      Bornology.IsBounded (Set.range fun n ↦ (y (φ n), u (φ n))) := by
    refine (hy_sub_bounded.prod hu_sub_bounded).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩
  have hmem :
      (x, v) ∈ gra A :=
    SetValuedOperator.Maximal.mem_graph_of_tendsto_of_tendsto_weakly hA
      (fun n ↦ hu (φ n)) hgraph_bounded hy_tendsto hφweak
  exact (SetValuedOperator.mem_dom_iff A x).2 ⟨v, hmem⟩

omit [CompleteSpace H] in
/-- Third clause of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`A.dom ⊆ A.fstImageDomFitzpatrick`. -/
theorem dom_subset_fst_image_dom_fitzpatrick
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom ⊆ A.fstImageDomFitzpatrick := by
  -- Every domain point comes from a graph witness, and maximality supplies monotonicity.
  intro x hx
  exact mem_fstImageDomFitzpatrick_of_mem_dom A (Maximal.isMonotone hA) hx

/-- Fourth clause of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`A.fstImageDomFitzpatrick ⊆ closure A.dom`. -/
theorem fst_image_dom_fitzpatrick_subset_closure_dom
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.fstImageDomFitzpatrick ⊆ closure A.dom := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  rcases exists_mem_dom_dist_lt_of_mem_fstImageDomFitzpatrick A hA hx hε with
    ⟨y, hyDom, hxy⟩
  exact ⟨y, hyDom, hxy⟩

/-- First consequence of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`interior A.dom = interior (A.fstImageDomFitzpatrick)`. -/
theorem interior_dom_eq_interior_fst_image_dom_fitzpatrick
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    interior A.dom = interior A.fstImageDomFitzpatrick := by
  refine Set.Subset.antisymm
    (interior_dom_subset_interior_fst_image_dom_fitzpatrick_of_maximal A hA) ?_
  -- The reverse inclusion lands in `A.dom`, hence in its interior because the source is open.
  exact (IsOpen.subset_interior_iff isOpen_interior).2
    (interior_fst_image_dom_fitzpatrick_subset_dom A hA)

/-- Second consequence of Proposition 21.12: if `A : H → 2^H` is maximally monotone, then
`closure A.dom = closure (A.fstImageDomFitzpatrick)`. -/
theorem closure_dom_eq_closure_fst_image_dom_fitzpatrick
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    closure A.dom = closure A.fstImageDomFitzpatrick := by
  refine le_antisymm ?_ ?_
  · exact closure_mono (dom_subset_fst_image_dom_fitzpatrick A hA)
  · exact closure_minimal (fst_image_dom_fitzpatrick_subset_closure_dom A hA) isClosed_closure

/-- Final consequence of Proposition 21.12: if `A : H → 2^H` is maximally monotone and
`interior A.dom` is
nonempty, then `closure (interior A.dom) = closure A.dom`. -/
theorem closure_interior_dom_eq_closure_dom_of_interior_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hinter : (interior A.dom).Nonempty) :
    closure (interior A.dom) = closure A.dom := by
  have hconv : Convex ℝ A.fstImageDomFitzpatrick :=
    convex_fstImageDomFitzpatrick_of_maximal A hA
  have hfst_inter_nonempty : (interior A.fstImageDomFitzpatrick).Nonempty := by
    simpa [interior_dom_eq_interior_fst_image_dom_fitzpatrick A hA] using hinter
  -- Rewrite the closure-of-interior statement through the convex Fitzpatrick-domain projection.
  calc
    closure (interior A.dom) = closure (interior A.fstImageDomFitzpatrick) := by
      rw [interior_dom_eq_interior_fst_image_dom_fitzpatrick A hA]
    _ = closure A.fstImageDomFitzpatrick := by
      exact closure_interior_eq_closure_of_convex_nonempty_interior hconv hfst_inter_nonempty
    _ = closure A.dom := by
      rw [← closure_dom_eq_closure_fst_image_dom_fitzpatrick A hA]

/-- Proposition 21.12. If `A : H → 2^H` is maximally monotone, then `A.dom` and the
first-coordinate Fitzpatrick-domain projection satisfy the inclusion chain from `(21.34)`, the
induced interior and closure identities, and the closure-of-interior identity when
`interior A.dom` is nonempty. -/
theorem dom_fstImageDomFitzpatrick_relations_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    interior A.dom ⊆ interior A.fstImageDomFitzpatrick ∧
      interior A.fstImageDomFitzpatrick ⊆ A.dom ∧
      A.dom ⊆ A.fstImageDomFitzpatrick ∧
      A.fstImageDomFitzpatrick ⊆ closure A.dom ∧
      interior A.dom = interior A.fstImageDomFitzpatrick ∧
      closure A.dom = closure A.fstImageDomFitzpatrick ∧
      ((interior A.dom).Nonempty → closure (interior A.dom) = closure A.dom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact interior_dom_subset_interior_fst_image_dom_fitzpatrick_of_maximal A hA
  · exact interior_fst_image_dom_fitzpatrick_subset_dom A hA
  · exact dom_subset_fst_image_dom_fitzpatrick A hA
  · exact fst_image_dom_fitzpatrick_subset_closure_dom A hA
  · exact interior_dom_eq_interior_fst_image_dom_fitzpatrick A hA
  · exact closure_dom_eq_closure_fst_image_dom_fitzpatrick A hA
  · intro hinter
    -- The nonempty-interior clause is exactly the final derived statement above.
    exact closure_interior_dom_eq_closure_dom_of_interior_nonempty A hA hinter

end SetValuedOperator
