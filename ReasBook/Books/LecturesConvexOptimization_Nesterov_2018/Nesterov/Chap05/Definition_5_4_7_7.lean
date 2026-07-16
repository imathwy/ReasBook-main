import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_4_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped PowerCone

noncomputable section

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "LpLiftPointₙ" => ℝ × Eₙ × Eₙ

private abbrev liftedPowerConeCoord (τ : ℝ) (x z : Eₙ) (i : Fin n) : ((ℝ × ℝ) × ℝ) :=
  ((x i, τ), z i)

/- Definition 5.4.7.7 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-barrier
domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the source-facing symmetric power-cone owner for the
  coordinate triples `((x⁽ⁱ⁾, τ), z⁽ⁱ⁾)`;
* `power_cone_barrier` from `Theorem_5_4_7_3`, the chapter owner of the logarithmic power-cone
  barrier appearing in each summand of `Ψ_α`;
* `logarithmicBarrierDomain` / `LogarithmicBarrierPoint` from `Definition_5_4_5_7`, the chapter
  barrier-owner pattern "strict domain `Set` + subtype carrier + ambient bridge formula";
* `circumscribedEllipsoidBarrierDomain` / `CircumscribedEllipsoidBarrierPoint` from
  `Definition_5_4_5_5`, the same strict-domain pattern for a neighboring logarithmic barrier.

Source/core/bridge triage:
* source-facing: the strict lifted barrier domain `lpEpigraphConeBarrierLiftDomain α` and the
  barrier `lpEpigraphConeBarrierLifted α` on that domain;
* core/canonical: the coordinate owner `power_cone_barrier α` from the earlier power-cone files;
* bridge/view: the ambient finite-sum map `lpEpigraphConeBarrierLiftedAmbient α` and its
  coordinatewise textbook expansion.

Primitive data:
* coordinatewise strict membership in the canonical owner `interior K_[α]`;
* the shared positivity condition `τ > 0`, kept explicit because it is not recoverable from the
  coordinate owner when `n = 0`;
* the normalization equation `∑ i, x⁽ⁱ⁾ = τ`.

Derived API:
* the subtype carrier `LpEpigraphConeBarrierLiftPoint α`;
* the ambient barrier as a sum of the canonical coordinate barriers `power_cone_barrier α`;
* the companion theorem expanding that owner back to the raw textbook logarithmic formula.

This refinement keeps the barrier on its mathematically correct strict lifted domain rather than
on the closed witness set from the previous existence theorem, owns the coordinate strictness via
the earlier power-cone interior `interior K_[α]`, and reuses the chapter power-cone barrier owner
for each coordinate summand instead of duplicating that formula locally.
-/

/-- The lifted domain `𝓗_P` for the `ℓ_p` epigraph cone consists of triples `(τ, x, z)` such that
`x` is coordinatewise nonnegative, the inequalities
`(x^(i))^α τ^(1 - α) ≥ |z^(i)|` hold for every coordinate, and `∑ i, x^(i) = τ`. -/
def lpEpigraphConeLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ K_[α]) ∧
      ∑ i : Fin n, p.2.1 i = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeLiftDomain n α` exactly when it satisfies the
coordinatewise lifted `ℓ_p`-epigraph inequalities and the normalization equation
`∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeLiftDomain n α ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        (∀ i : Fin n, Real.rpow (x i) α * Real.rpow τ (1 - α) ≥ |z i|) ∧
          ∑ i : Fin n, x i = τ := by
  constructor
  · rintro ⟨hp, hsum⟩
    refine ⟨?_, ?_, hsum⟩
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨hxi, -, -⟩
      exact hxi
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨-, -, hzi⟩
      exact hzi
  · rintro ⟨hx, hz, hsum⟩
    refine ⟨?_, hsum⟩
    have hτ : 0 ≤ τ := by
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i :=
        Finset.sum_nonneg fun i _ ↦ hx i
      simpa [hsum] using hsum_nonneg
    intro i
    exact (mem_powerCone_iff α (x i) τ (z i)).2 ⟨hx i, hτ, hz i⟩

/-- The strict lifted domain `𝓗_P` on which the lifted `ℓ_p`-epigraph logarithmic barrier is
defined. Its primitive data are coordinatewise strict membership in the canonical power-cone owner
`interior K_[α]`, the shared positivity condition `τ > 0`, and the normalization
`∑ i, x^(i) = τ`. -/
def lpEpigraphConeBarrierLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ interior K_[α]) ∧
      0 < p.1 ∧
        (∑ i : Fin n, p.2.1 i) = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeBarrierLiftDomain n α` exactly when each
coordinate lies in `interior K_[α]`, with the shared strictness condition `τ > 0` and the
normalization `∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff_interior
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, liftedPowerConeCoord n τ x z i ∈ interior K_[α]) ∧
        0 < τ ∧
          (∑ i : Fin n, x i) = τ :=
  Iff.rfl

/-- Expanding the owner `interior K_[α]` rewrites strict lifted-domain membership back to the
coordinatewise positivity conditions from Definition 5.4.7.7. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, 0 < x i) ∧
        0 < τ ∧
          (∀ i : Fin n,
            0 < Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) ∧
            (∑ i : Fin n, x i) = τ := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff_interior]
  sorry

/-- The subtype of points in the strict lifted `ℓ_p`-epigraph barrier domain. This is the natural
owner carrier for Definition 5.4.7.7. -/
abbrev LpEpigraphConeBarrierLiftPoint (α : ℝ) :=
  {p : LpLiftPointₙ // p ∈ lpEpigraphConeBarrierLiftDomain n α}

/-- The ambient lifted barrier is the finite sum of the canonical Chapter 5 power-cone barriers on
the coordinate triples `((x^(i), τ), z^(i))`. The barrier itself is obtained by restricting this
ambient map to `LpEpigraphConeBarrierLiftPoint n α`. -/
def lpEpigraphConeBarrierLiftedAmbient (α : ℝ) : LpLiftPointₙ → ℝ
  | (τ, x, z) => ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)

/-- Definition 5.4.7.7: for `α ∈ (0, 1)`, the barrier `Ψ_α` on the strict lifted domain `𝓗_P`
is the restriction of the ambient coordinatewise power-cone barrier sum. -/
def lpEpigraphConeBarrierLifted (α : ℝ) : LpEpigraphConeBarrierLiftPoint n α → ℝ :=
  fun p ↦ lpEpigraphConeBarrierLiftedAmbient n α p.1

/-- Evaluating the ambient lifted `ℓ_p`-epigraph barrier at `(τ, x, z)` is exactly the sum of the
canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply
    (α τ : ℝ) (x z : Eₙ) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- Expanding the coordinate barrier owner `power_cone_barrier α` rewrites the ambient lifted
barrier back to the textbook logarithmic formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply_formula
    (α τ : ℝ) (x z : Eₙ) (hτ : 0 ≤ τ) (hx : ∀ i : Fin n, 0 ≤ x i) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  unfold lpEpigraphConeBarrierLiftedAmbient
  calc
    ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)
      = ∑ i : Fin n,
          (-(Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [power_cone_barrier_apply α (x i) τ (z i) (hx i) hτ]
          ring
    _ = -∑ i : Fin n,
          (Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ) := by
          rw [Finset.sum_neg_distrib]

/-- Evaluating `lpEpigraphConeBarrierLifted n α` on a strict-domain point agrees with the ambient
bridge formula. -/
@[simp] theorem lpEpigraphConeBarrierLifted_apply
    (α : ℝ) (p : LpEpigraphConeBarrierLiftPoint n α) :
    lpEpigraphConeBarrierLifted n α p =
      lpEpigraphConeBarrierLiftedAmbient n α p :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
is the sum of the canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLifted_apply_triple
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
recovers the textbook finite-sum formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLifted_apply_triple_formula
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff] at h
  have hx : ∀ i : Fin n, 0 ≤ x i := fun i ↦ (h.1 i).le
  have hτ : 0 ≤ τ := h.2.1.le
  simpa [lpEpigraphConeBarrierLifted] using
    lpEpigraphConeBarrierLiftedAmbient_apply_formula n α τ x z hτ hx

end
