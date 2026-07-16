import Mathlib
import StacksProject_2024.stacks_project.Chap30.Lemma_30_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced mathlib's graded-module direct-sum API
-- `DirectSum.Gmodule` and ideal-power quotient API
-- `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`. The current project owner for
-- `Coh(X, I)` in this subsection is the affine inverse-system model from Lemma 30.23.1.

/-- The `n`-th piece `I^n / I^{n+1}` of the associated graded ring of an ideal, expressed as
the quotient of the ideal `I^n` by `I • I^n`. -/
abbrev associatedGradedIdealPiece (I : Ideal A) (n : ℕ) : Type u :=
  (I ^ n : Ideal A) ⧸ (I • (⊤ : Submodule A (I ^ n : Ideal A)))

/-- The `n`-th kernel piece `ker(F_{n+1} -> F_n)` of a sequential inverse system. -/
abbrev transitionKernelPiece (F : SequentialInverseSystem (FGModuleCat A)) (n : ℕ) : Type u :=
  (F.stepLinearMap n).ker

variable [IsNoetherianRing A]

/-- Lemma 30.23.8: in the affine model for coherent formal modules along an ideal `I`, the
direct sum of the transition kernels `ker(F_{n+1} -> F_n)` is finite over the associated graded
ring `⊕ n, I^n / I^{n+1}`. The graded ring and graded module structures in the hypotheses are the
canonical structures on these explicit degree pieces. -/
@[stacks 087Z]
theorem affineCoherentFormalModules_transitionKernelDirectSum_finite
    (I : Ideal A) (F : SequentialInverseSystem (FGModuleCat A))
    (hF : IsAffineCoherentFormalModuleSystem I F)
    [DirectSum.GSemiring (associatedGradedIdealPiece I)]
    [DirectSum.Gmodule (associatedGradedIdealPiece I) (transitionKernelPiece F)] :
    Module.Finite (DirectSum ℕ (associatedGradedIdealPiece I))
      (DirectSum ℕ (transitionKernelPiece F)) := sorry

end CategoryTheory.SequentialInverseSystem
