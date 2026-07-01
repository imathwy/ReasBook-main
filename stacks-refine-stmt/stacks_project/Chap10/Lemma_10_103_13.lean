import Mathlib
import stacks_project.Chap10.Definition_10_103_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: argue by induction on the number of variables, reducing from
-- `MvPolynomial (Fin (n + 1)) R` to a one-variable polynomial extension over
-- `MvPolynomial (Fin n) R`. For each prime of the polynomial ring, localize and use flatness of
-- the polynomial extension together with the regular-sequence characterization of the
-- Cohen-Macaulay condition from the previous local lemmas. The owner abstraction for the source
-- hypothesis and target conclusion is `Module.LocallyCohenMacaulay`; the primewise depth/support
-- equalities are derived from that class rather than exposed as the main API.
namespace Module.LocallyCohenMacaulay

/-
Source/core/bridge triage:
* source-facing: local Cohen-Macaulayness of a finite module over a Noetherian ring;
* core/canonical: `Module.LocallyCohenMacaulay R M` from `Definition_10_103_12`;
* bridge/view: this polynomial-base-change closure theorem for that owner.

Primitive data are only the module `M` and the owner hypothesis
`Module.LocallyCohenMacaulay R M`. The primewise Cohen-Macaulay localizations of the polynomial
base change are derived API from the resulting owner instance, so the theorem should return
`Module.LocallyCohenMacaulay` directly instead of a parallel family of explicit equalities.
-/
/-- Lemma 10.103.13: if `M` is a locally Cohen-Macaulay module over a Noetherian ring `R`, then
its scalar extension to `R[x₁, …, xₙ]`, represented canonically by
`MvPolynomial (Fin n) R ⊗[R] M`, is again locally Cohen-Macaulay. -/
theorem mvPolynomial (hCM : Module.LocallyCohenMacaulay R M) (n : ℕ) :
    Module.LocallyCohenMacaulay (MvPolynomial (Fin n) R) ((MvPolynomial (Fin n) R) ⊗[R] M) :=
  sorry

end Module.LocallyCohenMacaulay

end
