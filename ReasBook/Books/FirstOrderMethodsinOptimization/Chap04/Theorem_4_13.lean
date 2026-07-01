import FirstOrderMethodsinOptimization.Chap03.Theorem_3_4
import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

recall effective_domain
recall subdifferentialAt
recall conjugate_function
recall conjugate_function_apply

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 4.13 is `source-facing` in the chapter's convex Lipschitz/conjugacy interface.
Domain sampling identifies the owner abstractions upstream as Definition 2.1's
`effective_domain`, Theorem 3.4's strong-dual bridge `subdifferentialAt`, and Definition 4.1's
`conjugate_function`. The primitive data here are only the convex function `f` and the radius `L`;
the subgradient clause is expressed directly through `subdifferentialAt`, while the conjugate-domain
clause is the continuous-dual restriction of the owner `conjugate_function`. This file therefore
keeps only the textbook `TFAE` statement and no parallel local wrappers. -/

-- Proof sketch: identify clause (i) with clause (ii) using the global/full-domain specialization
-- of the Chapter 3 bounded-subdifferential characterization of Lipschitz continuity. For
-- `(iii) → (ii)`, use the conjugate-subgradient theorem: every `g ∈ subdifferentialAt f x` lies
-- in the effective domain of `f*`, hence in the dual closed ball. For `(i) → (iii)`, bound
-- `-f x` below by `-f 0 - L * ‖x‖` and then show that if `‖y‖ > L`, scaling along a unit vector
-- realizing `y` forces the supremum defining `f* y` to be `⊤`.
/-- Theorem 4.13: for a convex real-valued function, the following are equivalent for the given
Lipschitz bound `L`: (i) `f` is globally `L`-Lipschitz, (ii) every subgradient of `f` has norm at
most `L`, and (iii) the effective domain of the conjugate `f*` is contained in the closed dual
ball of radius `L`. -/
theorem convex_lipschitz_tfae_subdifferential_norm_le_conjugate_domain_subset_closedBall
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) (L : NNReal) :
    List.TFAE
      [LipschitzWith L f,
        ∀ x : E, ∀ g ∈ subdifferentialAt f x, ‖g‖ ≤ L,
        effective_domain (fun y : StrongDual ℝ E ↦ conjugate_function (fun x ↦ (f x : EReal)) y) ⊆
          closedBall (0 : StrongDual ℝ E) L] := sorry

end
