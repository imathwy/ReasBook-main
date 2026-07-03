import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_6 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Corollary 10.6 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the local owner ecosystem:
- `composite_model_objective` from Definition 10.2 is the chapter owner for the composite value
  `F = f + g`;
- `prox_grad_operator` from Definition 10.9, with notation `T[...]`, is the canonical one-step
  prox-gradient update;
- `gradient_mapping` from Definition 10.5, with notation `G[...]`, is the canonical residual
  owner;
- `prox_grad_sufficient_decrease` from Lemma 10.4 is the upstream descent theorem this
  corollary specializes.

Primitive data are exactly the hypotheses already required by Lemma 10.4, with the positivity of
the smoothness constant carried canonically by `PosReal`. The displayed inequality is therefore
derived API obtained by specializing the owner theorem to the stepsize `L = L_f`, not a new local
descent owner. -/

variable (f g : E → EReal)
variable (Lf : PosReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

local notation "F" => composite_model_objective f g

-- Proof sketch: specialize `prox_grad_sufficient_decrease` to the stepsize `L = Lf`. The
-- coefficient `((L_f - L_f / 2) / L_f^2)` then simplifies to `1 / (2 L_f)`, and the residual
-- term is already expressed through the Chapter 10 owners `T_{L_f}` and `G_{L_f}` from
-- `Lemma_10_4`.
/-- Corollary 10.6: under the assumptions of Lemma 10.4, specializing the prox-gradient descent
estimate to the stepsize `L_f` gives
`F(x) - F(T_{L_f}^{f,g}(x)) ≥ (1 / (2 L_f)) ‖G_{L_f}^{f,g}(x)‖^2` for every
`x ∈ interior (effective_domain f)`. -/
theorem prox_grad_sufficient_decrease_at_smoothness_constant
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f))
        (PosReal.toNNReal Lf))
    (x : interior (effective_domain f)) :
    F (x : E) - F (T[Lf, f, g] x) ≥
      (((1 / (2 * (Lf : ℝ)) * ‖G[Lf, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  have hcoeff :
      (((Lf : ℝ) - (PosReal.toNNReal Lf : ℝ) / 2) / ((Lf : ℝ) ^ (2 : ℕ))) =
        (1 : ℝ) / (2 * (Lf : ℝ)) := by
    rw [PosReal.coe_toNNReal]
    have hLf_ne : (Lf : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos Lf)
    field_simp [hLf_ne]
    ring
  -- Specialize Lemma 10.4 at the smoothness constant `L = L_f`.
  simpa only [hcoeff] using
    prox_grad_sufficient_decrease
      (f := f)
      (g := g)
      (Lf := PosReal.toNNReal Lf)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (L := Lf)
      (x := x)

end
