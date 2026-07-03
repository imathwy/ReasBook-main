import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_7 (from Chap03) -/
open scoped BigOperators
open WithLp

noncomputable section

namespace EuclideanSpace

/-- The admissible exponents for finite-dimensional `ℓ_p` geometry, namely `1 ≤ p < ∞`. -/
abbrev LpExponent := {q : ENNReal // 1 ≤ q ∧ q ≠ ⊤}

instance (p : LpExponent) : Fact (1 ≤ (p : ENNReal)) :=
  ⟨p.2.1⟩

namespace LpExponent

/-- The real exponent attached to an admissible `ℓ_p` exponent. -/
abbrev toReal (p : EuclideanSpace.LpExponent) : ℝ :=
  ((p : ENNReal).toReal)

theorem toReal_pos (p : EuclideanSpace.LpExponent) : 0 < p.toReal :=
  ENNReal.toReal_pos_iff.mpr
    ⟨lt_of_lt_of_le zero_lt_one p.2.1, lt_of_le_of_ne le_top p.2.2⟩

end LpExponent

private abbrev coordinateLpEquiv (n : ℕ) (p : LpExponent) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] WithLp (p : ENNReal) (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.trans
    (WithLp.linearEquiv (p : ENNReal) ℝ (Fin n → ℝ)).symm

instance : One LpExponent where
  one := ⟨(1 : ENNReal), by constructor <;> simp⟩

namespace LpExponent

@[simp] theorem one_toReal : (1 : EuclideanSpace.LpExponent).toReal = 1 := by
  change (1 : ENNReal).toReal = 1
  exact ENNReal.toReal_one

end LpExponent

/- Definition 3.7 is source-facing in the chapter's finite-dimensional `ℓ_p`-geometry domain.

Sampled owner-style declarations:
- `EuclideanSpace.l1Seminorm`
- `EuclideanSpace.linftyNorm`
- `PiLp.norm_eq_sum`
- `Seminorm.closedBall`

Best owner abstraction:
- the coordinate pullback seminorm
  `EuclideanSpace.lpSeminorm n p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))`

Primitive data:
- the ambient dimension `n : ℕ`
- the exponent `p : LpExponent`

Derived API:
- the textbook evaluation notation `‖x‖_[p]`
- the raw coordinate formula `lpSeminorm_apply`
- the notation-facing coordinate formula `lpNorm_eq_sum`
- the induced normed-seminorm instance `lpSeminorm_isNorm`
- the `p = 1` bridge `lpSeminorm_one_eq_l1Seminorm`
- the `p = 1` coordinate specialization `lpSeminorm_one_apply`
- the downstream textbook `ℓ_p` ball `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`, obtained
  directly from
  `Seminorm.closedBall`

Source/core/bridge triage:
- source-facing: `EuclideanSpace.lpSeminorm n p`
- core/canonical: `Seminorm.comp (normSeminorm ℝ (WithLp (p : ENNReal) (Fin n → ℝ)))
  (coordinateLpEquiv n p).toLinearMap`
- bridge/view: the notation `‖x‖_[p]`, `lpSeminorm_isNorm`, `lpSeminorm_apply`,
  `lpNorm_eq_sum`, `lpSeminorm_one_eq_l1Seminorm`, `lpSeminorm_one_apply`

The former `lpNorm`/`lpBall` API duplicated owner declarations that are already canonical at the
seminorm layer, so this file keeps only the ambient owner `EuclideanSpace.lpSeminorm`, aligns its
public surface with the existing `EuclideanSpace.l1Seminorm` and `EuclideanSpace.linftyNorm`
owners, bridges its `p = 1` specialization to `EuclideanSpace.l1Seminorm`, records the
source-facing zero-detection fact via `lpSeminorm_isNorm`, and uses `Seminorm.closedBall`
directly for the textbook ball while exposing the recurring pointwise surface through `‖x‖_[p]`.
-/

/-- Definition 3.7: the coordinate `ℓ_p` seminorm on `ℝ^n`, obtained by pulling back the owner
`L^p` norm on `WithLp (p : ENNReal) (Fin n → ℝ)` along the Euclidean coordinate map. The induced
`Seminorm.IsNorm` instance recovers the textbook norm property, its value on a vector is written
`‖x‖_[p]` below, and its closed balls are the textbook `ℓ_p` balls. -/
def lpSeminorm (n : ℕ) (p : LpExponent) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  Seminorm.comp
    (normSeminorm ℝ (WithLp (p : ENNReal) (Fin n → ℝ)))
    (coordinateLpEquiv n p).toLinearMap

end EuclideanSpace

namespace EuclideanSpaceLp

scoped notation:max "‖" x "‖_[" p "]" => EuclideanSpace.lpSeminorm _ p x

end EuclideanSpaceLp

open scoped EuclideanSpaceLp

namespace EuclideanSpace

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem lpSeminorm_toLp (x : E) (p : LpExponent) :
    lpSeminorm n p x = ‖toLp (p : ENNReal) (fun i ↦ x i)‖ := by
  change ‖coordinateLpEquiv n p x‖ = _
  rfl

/-- The canonical coordinate `ℓ_p` seminorm is a norm on `ℝⁿ`. -/
-- Proof sketch: `lpSeminorm` is the pullback of the owner norm on
-- `WithLp (p : ENNReal) (Fin n → ℝ)`
-- along the coordinate linear equivalence defining `lpSeminorm`, so vanishing forces the vector
-- itself to vanish.
instance lpSeminorm_isNorm (p : LpExponent) : Seminorm.IsNorm (lpSeminorm n p : Seminorm ℝ E) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    exact (coordinateLpEquiv n p).map_eq_zero_iff.mp <|
      norm_eq_zero.mp <| by
        simpa [lpSeminorm, coordinateLpEquiv] using hx

/-- Applying the canonical coordinate `ℓ_p` seminorm to a vector gives the usual coordinate
formula. -/
-- Proof sketch: rewrite `lpSeminorm p x` as the owner `WithLp` norm on the coordinate function
-- `fun i ↦ x i` and apply `PiLp.norm_eq_sum`.
theorem lpSeminorm_apply (x : E) (p : LpExponent) :
    lpSeminorm n p x = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal : ℝ) := by
  rw [lpSeminorm_toLp x p]
  simpa [Real.norm_eq_abs] using PiLp.norm_eq_sum p.toReal_pos (toLp (p : ENNReal) fun i ↦ x i)

/-- The textbook `ℓ_p` notation on `EuclideanSpace ℝ (Fin n)` is given by the coordinate formula
for the owner seminorm `EuclideanSpace.lpSeminorm`. -/
theorem lpNorm_eq_sum (x : E) (p : LpExponent) :
    ‖x‖_[p] = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal : ℝ) := by
  simpa using lpSeminorm_apply x p

/-- The `p = 1` specialization of `lpSeminorm_apply` recovers the earlier project coordinate
formula for `l1Seminorm`. -/
theorem lpSeminorm_one_apply (x : E) :
    ‖x‖_[(1 : LpExponent)] = ∑ i, ‖x i‖ := by
  rw [lpNorm_eq_sum x (1 : LpExponent), LpExponent.one_toReal]
  norm_num

/-- The `p = 1` specialization of `lpSeminorm` coincides with the earlier project owner
`l1Seminorm`. -/
theorem lpSeminorm_one_eq_l1Seminorm :
    lpSeminorm n (1 : LpExponent) = l1Seminorm n := by
  ext x
  rw [l1Seminorm_apply]
  simpa using lpSeminorm_one_apply x

end

end EuclideanSpace

/-! ### Lemma_3_7 (from Chap03) -/
/- Lemma 3.7 lies in the chapter's extended-valued convex-analysis / subdifferential-calculus
domain.

Sampled owner-style declarations:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite-value representative;
- `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `subdifferential_eq_singleton_gradient` in `Lemma_3_1_7`, already stated on those owner
  abstractions.

Best owner abstraction:
- `subdifferential_eq_singleton_gradient` from `Lemma_3_1_7`.

Primitive data:
- none in this file; the theorem already lives upstream on the canonical owner surface.

Derived API:
- this recall-only source-facing entry point.

Source/core/bridge triage:
- source-facing: Lemma 3.7's singleton-subdifferential statement;
- core/canonical: `dom`, `withTopRealPart`, and `subdifferential`;
- bridge/view: this recall surface.

The previous file duplicated the effective-domain, finite-real-part, convexity, subgradient, and
subdifferential owners even though the exact theorem already exists in `Lemma_3_1_7`. This
refinement removes that parallel local API and reuses the canonical chapter theorem directly.
-/

recall subdifferential_eq_singleton_gradient

/-! ### Proposition_3_7 (from Chap03) -/
noncomputable section

open scoped BigOperators

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Proposition 3.7 lies in the chapter's finite-dimensional `ℓ₁`-geometry / convex-hull domain.

Sampled owner-style declarations:
- `EuclideanSpace.l1Seminorm`
- `lpSeminorm_one_eq_l1Seminorm`
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`

Best owner abstraction:
- `(EuclideanSpace.l1Seminorm n).closedBall x₀ r`

Primitive data:
- the ambient dimension `n : ℕ`
- the center `x₀ : E`
- the radius `r : ℝ`

Derived API:
- the coordinate membership view from `Seminorm.mem_closedBall` together with
  `EuclideanSpace.l1Seminorm_apply`
- the convex-hull description by the signed standard-basis vertices

Source/core/bridge triage:
- source-facing: the `ℓ₁`-ball / signed-vertex convex-hull equality
- core/canonical: `Seminorm.closedBall` for `EuclideanSpace.l1Seminorm n`
- bridge/view: the coordinate inequality
  `x ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ r ↔ ∑ i, ‖(x - x₀) i‖ ≤ r`

The previous statement exposed the coordinate set-builder as the main owner. In this file that
coordinate formula is only a bridge view, so the proposition is refined to the canonical
`l1Seminorm.closedBall` surface directly. -/

/- Proposition 3.7: for `0 < n` and `r ≥ 0`, the closed `ℓ₁`-ball centered at `x₀` in `ℝⁿ` is
the convex hull of the signed standard-basis vertices `x₀ ± r eᵢ`. -/
-- Proof sketch: prove both inclusions. For the convex-hull inclusion, show that every signed
-- basis vertex has `ℓ₁`-distance `r` from `x₀` and use convexity of the `ℓ₁` closed ball. For the
-- reverse inclusion, decompose each coordinate of `x - x₀` into positive and negative parts,
-- normalize by `r`, and read off a convex-combination formula in the listed vertices.
/-- Helper for Proposition 3.7: membership in the owner `ℓ₁` closed ball is equivalent to the
coordinate `ℓ₁` inequality. -/
lemma mem_l1_closedBall_iff_sum_norm_sub_le (x₀ x : E) (r : ℝ) :
    x ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ r ↔
      ∑ i, ‖(x - x₀) i‖ ≤ r := by
  -- Switch from the owner seminorm surface to the coordinate formula from `l1Seminorm_apply`.
  rw [(EuclideanSpace.l1Seminorm n).mem_closedBall, EuclideanSpace.l1Seminorm_apply]

/-- Helper for Proposition 3.7: each signed standard-basis vertex lies on the boundary of the
owner `ℓ₁` closed ball of radius `r`. -/
lemma signed_standard_basis_vertex_mem_l1_closedBall
    (x₀ : E) (r : ℝ) (hr : 0 ≤ r) (i : Fin n) :
    x₀ + r • e[i] ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ r ∧
      x₀ - r • e[i] ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ r := by
  constructor
  · -- For the `+` vertex, only the `i`th coordinate contributes to the `ℓ₁` sum.
    rw [(EuclideanSpace.l1Seminorm n).mem_closedBall]
    calc
      EuclideanSpace.l1Seminorm n ((x₀ + r • e[i]) - x₀)
          = EuclideanSpace.l1Seminorm n (r • e[i]) := by simp
      _ = r := by
        rw [EuclideanSpace.l1Seminorm_apply]
        rw [Finset.sum_eq_single i]
        · simp [hr]
        · intro j _ hji
          simp [hji]
        · simp
      _ ≤ r := le_rfl
  · -- The `-` vertex has the same `ℓ₁` distance because the coordinate formula uses absolute
    -- values.
    rw [(EuclideanSpace.l1Seminorm n).mem_closedBall]
    calc
      EuclideanSpace.l1Seminorm n ((x₀ - r • e[i]) - x₀)
          = EuclideanSpace.l1Seminorm n ((-r) • e[i]) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm]
      _ = r := by
        rw [EuclideanSpace.l1Seminorm_apply]
        rw [Finset.sum_eq_single i]
        · simp [hr]
        · intro j _ hji
          simp [hji]
        · simp
      _ ≤ r := le_rfl

/-- Helper for Proposition 3.7: the zero-radius owner `ℓ₁` closed ball is the singleton `{x₀}`. -/
lemma mem_l1_closedBall_zero_radius_iff (x₀ x : E) :
    x ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ 0 ↔ x = x₀ := by
  constructor
  · intro hx
    -- Radius zero forces the seminorm of `x - x₀` to vanish, hence the vector itself vanishes.
    have hzero : EuclideanSpace.l1Seminorm n (x - x₀) = 0 := by
      have hnonneg : 0 ≤ EuclideanSpace.l1Seminorm n (x - x₀) := by positivity
      exact le_antisymm ((EuclideanSpace.l1Seminorm n).mem_closedBall.mp hx)
        hnonneg
    have hsub : x - x₀ = 0 :=
      (inferInstance : Seminorm.IsNorm (EuclideanSpace.l1Seminorm n)).eq_zero_of_map_eq_zero hzero
    exact sub_eq_zero.mp hsub
  · intro hx
    -- Conversely, the center belongs to every nonnegative-radius closed ball.
    exact by
      simpa [hx] using (EuclideanSpace.l1Seminorm n).mem_closedBall_self (x := x₀) (r := 0) le_rfl

/-- Helper for Proposition 3.7: a point in the positive-radius owner `ℓ₁` closed ball admits an
explicit convex combination of the signed standard-basis vertices. -/
lemma exists_signed_standard_basis_weights_of_mem_l1_closedBall
    (hn : 0 < n) (x₀ : E) (r : ℝ) {x : E} (hr_pos : 0 < r)
    (hx : x ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ r) :
    ∃ w : (Fin n ⊕ Fin n) → ℝ,
      (∀ s, 0 ≤ w s) ∧
      (∑ s, w s = 1) ∧
      (∀ s,
        Sum.elim (fun i ↦ x₀ + r • e[i]) (fun i ↦ x₀ - r • e[i]) s ∈
          Set.range (fun i : Fin n ↦ x₀ + r • e[i]) ∪
            Set.range (fun i : Fin n ↦ x₀ - r • e[i])) ∧
      (∑ s, w s • Sum.elim (fun i ↦ x₀ + r • e[i]) (fun i ↦ x₀ - r • e[i]) s = x) := by
  let z : E := x - x₀
  let αPlus : Fin n → ℝ := fun i ↦ max (z i) 0 / r
  let αMinus : Fin n → ℝ := fun i ↦ max (-z i) 0 / r
  let beta : ℝ := 1 - ∑ i, (αPlus i + αMinus i)
  let i₀ : Fin n := ⟨0, hn⟩
  let vertex : Fin n ⊕ Fin n → E :=
    Sum.elim (fun i ↦ x₀ + r • e[i]) (fun i ↦ x₀ - r • e[i])
  let w : (Fin n ⊕ Fin n) → ℝ := fun s ↦
    Sum.elim
      (fun i ↦ αPlus i + if i = i₀ then beta / 2 else 0)
      (fun i ↦ αMinus i + if i = i₀ then beta / 2 else 0)
      s
  have hx_sum : ∑ i, ‖z i‖ ≤ r := by
    -- This is the coordinate form of the closed-ball assumption.
    simpa [z] using (mem_l1_closedBall_iff_sum_norm_sub_le (x₀ := x₀) (x := x) (r := r)).mp hx
  have hαPlus_nonneg : ∀ i : Fin n, 0 ≤ αPlus i := by
    intro i
    dsimp [αPlus]
    exact div_nonneg (le_max_right _ _) hr_pos.le
  have hαMinus_nonneg : ∀ i : Fin n, 0 ≤ αMinus i := by
    intro i
    dsimp [αMinus]
    exact div_nonneg (le_max_right _ _) hr_pos.le
  have hmass_eq : ∑ i, (αPlus i + αMinus i) = (∑ i, ‖z i‖) / r := by
    -- The positive and negative parts sum to the absolute value in each coordinate.
    calc
      ∑ i, (αPlus i + αMinus i)
          = ∑ i, (‖z i‖ / r) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              dsimp [αPlus, αMinus]
              rw [← add_div, max_zero_add_max_neg_zero_eq_abs_self]
      _ = (∑ i, ‖z i‖) / r := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]
  have hmass_le_one : ∑ i, (αPlus i + αMinus i) ≤ 1 := by
    rw [hmass_eq]
    exact (div_le_iff₀ hr_pos).2 <| by simpa using hx_sum
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    exact sub_nonneg.mpr hmass_le_one
  have hindicator : ∀ a : ℝ, ∑ i : Fin n, (if i = i₀ then a else 0) = a := by
    intro a
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hw_nonneg : ∀ s, 0 ≤ w s := by
    intro s
    cases s with
    | inl i =>
        by_cases hi : i = i₀
        · subst hi
          simpa [w] using add_nonneg (hαPlus_nonneg i₀) (by positivity : 0 ≤ beta / 2)
        · simpa [w, hi] using hαPlus_nonneg i
    | inr i =>
        by_cases hi : i = i₀
        · subst hi
          simpa [w] using add_nonneg (hαMinus_nonneg i₀) (by positivity : 0 ≤ beta / 2)
        · simpa [w, hi] using hαMinus_nonneg i
  have hw_sum_inl : ∑ i : Fin n, w (Sum.inl i) = (∑ i, αPlus i) + beta / 2 := by
    simp_rw [w, Sum.elim_inl]
    rw [Finset.sum_add_distrib, hindicator]
  have hw_sum_inr : ∑ i : Fin n, w (Sum.inr i) = (∑ i, αMinus i) + beta / 2 := by
    simp_rw [w, Sum.elim_inr]
    rw [Finset.sum_add_distrib, hindicator]
  have hw_sum : ∑ s, w s = 1 := by
    -- The added `beta / 2` mass on the distinguished `±i₀` vertices repairs the slack to total mass `1`.
    rw [Fintype.sum_sum_type]
    rw [hw_sum_inl, hw_sum_inr]
    have hsplit :
        (∑ i, αPlus i) + ∑ i, αMinus i = ∑ i, (αPlus i + αMinus i) := by
      rw [← Finset.sum_add_distrib]
    calc
      ((∑ i, αPlus i) + beta / 2) + ((∑ i, αMinus i) + beta / 2)
          = ((∑ i, αPlus i) + ∑ i, αMinus i) + beta := by ring
      _ = (∑ i, (αPlus i + αMinus i)) + beta := by rw [hsplit]
      _ = 1 := by
            dsimp [beta]
            ring
  have hvertex_mem :
      ∀ s,
        vertex s ∈
          Set.range (fun i : Fin n ↦ x₀ + r • e[i]) ∪
            Set.range (fun i : Fin n ↦ x₀ - r • e[i]) := by
    intro s
    cases s with
    | inl i =>
        exact Or.inl ⟨i, rfl⟩
    | inr i =>
        exact Or.inr ⟨i, rfl⟩
  have hw_diff : ∀ j : Fin n, w (Sum.inl j) - w (Sum.inr j) = αPlus j - αMinus j := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp [w]
    · simp [w, hj]
  have hweight_sum_split :
      (∑ i : Fin n, w (Sum.inl i)) + ∑ i : Fin n, w (Sum.inr i) = 1 := by
    simpa [Fintype.sum_sum_type] using hw_sum
  have hplus_basis :
      ∀ j : Fin n, ∑ i : Fin n, w (Sum.inl i) * ((r • e[i] : E) j) = w (Sum.inl j) * r := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hminus_basis :
      ∀ j : Fin n, ∑ i : Fin n, w (Sum.inr i) * ((r • e[i] : E) j) = w (Sum.inr j) * r := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hplus_basis_if :
      ∀ j : Fin n, ∑ i : Fin n, (if j = i then w (Sum.inl i) * r else 0) = w (Sum.inl j) * r := by
    intro j
    exact by
      simpa [Pi.smul_apply, Pi.single_apply, mul_ite, mul_one, mul_zero] using hplus_basis j
  have hminus_basis_if :
      ∀ j : Fin n, ∑ i : Fin n, w (Sum.inr i) * (if j = i then r else 0) = w (Sum.inr j) * r := by
    intro j
    exact by
      simpa [Pi.smul_apply, Pi.single_apply, mul_ite, mul_one, mul_zero] using hminus_basis j
  have hz_coord : ∀ j : Fin n, r * (αPlus j - αMinus j) = z j := by
    intro j
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    -- Clearing the common denominator recovers the coordinate decomposition `z = z⁺ - z⁻`.
    calc
      r * (αPlus j - αMinus j)
          = r * (max (z j) 0 / r) - r * (max (-z j) 0 / r) := by
              dsimp [αPlus, αMinus]
              ring
      _ = max (z j) 0 - max (-z j) 0 := by
            field_simp [hr_ne]
      _ = z j := by
            rw [max_zero_sub_max_neg_zero_eq_self]
  have hw_center_mass :
      ∑ s, w s • vertex s = x := by
    -- Coordinatewise, the `x₀` mass sums to `1`, and the signed basis terms reconstruct `z = x - x₀`.
    ext j
    calc
      (∑ s, w s • vertex s) j
          = (∑ i : Fin n, (w (Sum.inl i) * x₀ j + if j = i then w (Sum.inl i) * r else 0)) +
              ∑ i : Fin n, w (Sum.inr i) * (x₀ j - if j = i then r else 0) := by
                rw [Fintype.sum_sum_type]
                simp [vertex, Pi.add_apply, Pi.smul_apply, Pi.single_apply, mul_ite, mul_one,
                  mul_zero]
      _ = (((∑ i : Fin n, w (Sum.inl i)) + ∑ i : Fin n, w (Sum.inr i)) * x₀ j +
            (w (Sum.inl j) * r - w (Sum.inr j) * r)) := by
              simp_rw [mul_sub]
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
                ← Finset.sum_mul, hplus_basis_if j, hminus_basis_if j]
              ring
      _ = 1 * x₀ j + r * (αPlus j - αMinus j) := by
            rw [hweight_sum_split]
            calc
              1 * x₀ j + (w (Sum.inl j) * r - w (Sum.inr j) * r)
                  = 1 * x₀ j + r * (w (Sum.inl j) - w (Sum.inr j)) := by ring
              _ = 1 * x₀ j + r * (αPlus j - αMinus j) := by rw [hw_diff j]
      _ = x₀ j + r * (αPlus j - αMinus j) := by ring
      _ = x₀ j + z j := by
            rw [hz_coord j]
      _ = x j := by
            dsimp [z]
            ring
  exact ⟨w, hw_nonneg, hw_sum, hvertex_mem, hw_center_mass⟩

/-- Proposition 3.7: for `0 < n` and `r ≥ 0`, the closed `ℓ₁`-ball centered at `x₀` in `ℝⁿ` is
the convex hull of the signed standard-basis vertices `x₀ ± r eᵢ`. -/
theorem l1_ball_eq_convexHull_signed_standard_basis_prop
    (hn : 0 < n) (x₀ : E) (r : ℝ) (hr : 0 ≤ r) :
    (EuclideanSpace.l1Seminorm n).closedBall x₀ r =
      convexHull ℝ
        (Set.range (fun i : Fin n ↦ x₀ + r • e[i]) ∪
          Set.range (fun i : Fin n ↦ x₀ - r • e[i])) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hr_zero : r = 0
    · -- At radius zero the ball is `{x₀}`, and `hn` provides a listed vertex equal to `x₀`.
      have hx0 : x = x₀ := by
        have hx' : x ∈ (EuclideanSpace.l1Seminorm n).closedBall x₀ 0 := by
          simpa [hr_zero] using hx
        exact (mem_l1_closedBall_zero_radius_iff (x₀ := x₀) (x := x)).mp hx'
      subst hx0
      let i₀ : Fin n := ⟨0, hn⟩
      apply subset_convexHull ℝ
      exact Or.inl ⟨i₀, by simp [i₀, hr_zero]⟩
    · have hr_ne : 0 ≠ r := by simpa [eq_comm] using hr_zero
      have hr_pos : 0 < r := lt_of_le_of_ne hr hr_ne
      -- For positive radius, use the explicit signed-vertex convex combination from the source proof.
      rcases exists_signed_standard_basis_weights_of_mem_l1_closedBall
          (hn := hn) (x₀ := x₀) (r := r) hr_pos hx with
        ⟨w, hw_nonneg, hw_sum, hvertex_mem, hw_center_mass⟩
      exact mem_convexHull_of_exists_fintype w
        (Sum.elim (fun i ↦ x₀ + r • e[i]) (fun i ↦ x₀ - r • e[i]))
        hw_nonneg hw_sum hvertex_mem hw_center_mass
  · -- Every listed vertex is already in the closed ball, so convexity gives the whole hull.
    refine convexHull_min ?_ ((EuclideanSpace.l1Seminorm n).convex_closedBall (x := x₀) (r := r))
    intro x hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (signed_standard_basis_vertex_mem_l1_closedBall (x₀ := x₀) (r := r) hr i).1
    · exact (signed_standard_basis_vertex_mem_l1_closedBall (x₀ := x₀) (r := r) hr i).2

end

/-! ### Theorem_3_7 (from Chap03) -/
noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Theorem 3.7 is recall-only in the chapter's affine pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on Euclidean spaces and their affine pullbacks.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.comp_continuousAffineMap` from `Theorem_3_1_2_2`
- `ClosedConvexOn.comp_affineMap` from `Theorem_3_1_2_2`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the affine map `g : Eₙ →ᵃ[ℝ] Eₘ`

Derived API:
- `ClosedConvexOn.comp_affineMap`

Source/core/bridge triage:
- source-facing: the affine-preimage closed-convexity statement
- core/canonical: `ClosedConvexOn.comp_affineMap`
- bridge/view: the earlier continuous-affine owner theorem
  `ClosedConvexOn.comp_continuousAffineMap`

The earlier owner file already proves the exact Euclidean affine-map statement. The `Nonempty` and
bounded hypotheses previously carried here are mathematically redundant for this theorem and do not
belong in the public API. This file therefore recalls the canonical owner theorem directly instead
of keeping a parallel wrapper name.
-/

recall ClosedConvexOn.comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g)

end
