import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_11

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Lemma 10.33 is `source-facing`: it is a scalar estimate for the FISTA momentum recursion.

Domain sampling:
- `fista_momentum_update` from Algorithm 10.13 is the chapter's canonical owner of the recursion
  `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- the FISTA momentum sequence `fista_t f g x0 L` from Algorithm 10.6 and the momentum sequence in
  `is_mfista_trajectory` from Algorithm 10.11 are downstream specializations of this same scalar
  recurrence.

Since the textbook statement is only about the scalar sequence defined by the recursion, the main
statement is kept at the sequence level and can later be specialized through the existing FISTA
and MFISTA recurrence lemmas without introducing a duplicate momentum-sequence owner.

Layer triage:
- `source-facing`: `fista_momentum_sequence_lower_bound`, the textbook scalar estimate for any
  sequence satisfying the FISTA momentum recursion;
- `core/canonical`: `fista_momentum_update` from Algorithm 10.13;
- `bridge/view`: the standing problem instance together with `fista_t f g x0 L` and
  `hproblem.IsMfistaTrajectory x y z t L`.

Primitive data:
- the initial value `t 0 = 1`;
- the recurrence `t (k + 1) = fista_momentum_update (t k)`.

Derived API:
- the owner-level scalar estimate `add_one_half_le_fista_momentum_update` from Algorithm 10.13;
- the bridge-level specializations in the namespace
  `IsFastProximalGradientProblem` below. -/

-- Proof sketch: argue by induction on `k`. The base case is `t 0 = 1 = (0 + 2) / 2`. For the
-- induction step, use `hsucc` together with the owner-level estimate
-- `add_one_half_le_fista_momentum_update` to get `t (k + 1) ≥ t k + 1 / 2`; combining this with
-- the induction hypothesis yields the claimed lower bound at `k + 1`.
/-- Lemma 10.33: if a real sequence starts at `t_0 = 1` and satisfies the FISTA momentum
recursion `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, then `t_k ≥ (k + 2) / 2` for every `k ≥ 0`. -/
theorem fista_momentum_sequence_lower_bound
    {t : ℕ → ℝ}
    (h0 : t 0 = 1)
    (hsucc : ∀ k : ℕ, t (k + 1) = fista_momentum_update (t k))
    (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ t k := by
  induction k with
  | zero =>
      simp [h0]
  | succ k hk =>
      rw [hsucc]
      have hstep : t k + 1 / 2 ≤ fista_momentum_update (t k) :=
        add_one_half_le_fista_momentum_update (t k)
      have hshift : (((k + 1 : ℕ) : ℝ) + 2) / 2 = (((k : ℝ) + 2) / 2) + 1 / 2 := by
        push_cast
        ring
      rw [hshift]
      linarith

end

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/-- The FISTA momentum sequence attached to a fast proximal-gradient problem satisfies the lower
bound from Lemma 10.33. This is an owner-level statement for the canonical sequence `fista_t`. -/
theorem fista_t_lower_bound
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ fista_t f g x0 L k := by
  exact fista_momentum_sequence_lower_bound
    (fista_t_zero f g x0 L)
    (fista_t_succ f g x0 L)
    k

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]
variable {x y z : ℕ → E} {t : ℕ → ℝ} {L : ℕ → PosReal}

/-- The momentum sequence of any MFISTA trajectory satisfies the lower bound from Lemma 10.33. -/
theorem is_mfista_trajectory_t_lower_bound
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ t k := by
  exact fista_momentum_sequence_lower_bound
    (is_mfista_trajectory_t_zero htraj)
    (is_mfista_trajectory_t_succ htraj)
    k

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable {x y z : ℕ → E} {t : ℕ → ℝ} {L : ℕ → PosReal}

namespace IsFastProximalGradientProblem

variable [hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf]

/-- Bridge/view specialization: the momentum sequence of any MFISTA trajectory owned by a fast
proximal-gradient problem satisfies the lower bound from Lemma 10.33. -/
theorem isMfistaTrajectory_t_lower_bound
    (htraj : hproblem.IsMfistaTrajectory x y z t L) (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ t k := by
  let _ : IsProperExtendedRealFunction g := hproblem.g_proper
  let _ : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  let _ : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  exact is_mfista_trajectory_t_lower_bound htraj k

end IsFastProximalGradientProblem

end
