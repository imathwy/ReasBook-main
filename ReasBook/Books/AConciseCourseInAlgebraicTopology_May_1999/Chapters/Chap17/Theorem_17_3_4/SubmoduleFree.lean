import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section

open Module

universe u

namespace Submodule

/-- Helper for Theorem 17.3.4: over a PID, any submodule of a free module is free.

This support theorem isolates the repeated arbitrary-rank algebraic blocker away from the
cohomology theorem file. -/
theorem freeOfPidOfFree
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    (S : Submodule R M) :
    Module.Free R S := by
  -- Route correction: the finite-rank Smith-normal-form API is not enough here, so the remaining
  -- proof must build the arbitrary-rank PID submodule freeness theorem in support scope.
  -- TODO: prove this by the maximal-independent-family route from the replan, then recover
  -- `Module.Free R S` from the resulting basis.
  sorry

end Submodule
