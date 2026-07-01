import AchimKlenkeLean.Items.Chap14.Theorem_14_42
import AchimKlenkeLean.Items.Chap17.Definition_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

section

variable {E : Type u} [MeasurableSpace E] [StandardBorelSpace E]
variable (I : AddSubmonoid NNReal) (κt : I → Kernel E E) [IsMarkovSemigroup κt]
variable (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)

-- Proof sketch: use the ordered-difference closure of `I` to turn the semigroup `κt` into the
-- consistent two-time family `(s, t) ↦ κ_{t - s}` on the time set `I`, then apply the Chapter 14
-- path-kernel existence theorem to obtain a path-space kernel with the canonical
-- finite-dimensional marginals.
/-- Remark 17.4: if the additive time set `I ⊆ [0, ∞)` is closed under ordered differences, then
a time-homogeneous family of transition probabilities on `I` already determines a stochastic
kernel on the full path space `E^I`. Thus the kernel `κ` from Definition 17.3 is forced, at the
level of finite-dimensional marginals, by the transition kernels `κ_t`. -/
theorem exists_pathKernel_of_timeHomogeneousTransitionKernels
    :
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I), ∀ hj : StrictMono j,
          j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = 0 →
            (κ x).map (finiteCoordinateProjection j) =
              consistentFamilyFiniteDimensionalKernel
                (fun {s t : I} hst ↦
                  κt ⟨t.1 - s.1, hsub (le_of_lt hst)⟩)
                j hj x := sorry

-- Proof sketch: apply the finite-dimensional marginal statement to the two-time chain `(0, t)` and
-- rewrite the resulting pushforward identity in terms of `transitionKernel`.
/-- The one-time transition kernels are a derived consequence of the finite-dimensional path-kernel
realization from Remark 17.4. -/
theorem exists_pathKernel_with_transitionKernel_of_timeHomogeneousTransitionKernels
    :
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ t : I, transitionKernel κ t = κt t := sorry

end
