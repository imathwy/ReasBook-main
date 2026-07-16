import stacks_proof.stacks_project.Chap15.Definition_15_28_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open Module

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: Koszul complexes in commutative algebra, specialized from a linear form on a
  finite free module to a finite family of ring elements;
- sampled owner declarations:
  `Module.piEquiv`,
  `Module.piEquiv_apply_apply`,
  `koszulComplex`,
  `ChainComplex.of`;
- best owner abstraction: the linear-map-level Koszul complex `koszulComplex`, together with the
  finite-family bridge from `Module.piEquiv`;
- primitive data: a finite family `f : Fin r → R`, viewed through the canonical linear form
  `koszulLinearForm f : (Fin r → R) →ₗ[R] R`;
- derived API: the tuple linear form `koszulLinearForm f` and the source-facing notations
  `K^•(f)` and `K^•[n](f)`;
- layer triage: `koszulComplex` and `Module.piEquiv` remain the `core/canonical` owners, while
  `koszulLinearForm` together with the notation layer are the public `bridge/view` API matching
  the textbook finite-family presentation. The basis-vector evaluation is already covered by
  `Module.piEquiv_apply_apply`, so it should not be restated here as a parallel public theorem.
-/

/-- Definition 15.28.2: the canonical linear form on the finite free module `Fin r → R`
determined by the tuple `f`. This is the family-level bridge to the owner Koszul complex
`koszulComplex`. -/
@[stacks 0623]
abbrev koszulLinearForm {r : ℕ} (f : Fin r → R) :
    (Fin r → R) →ₗ[R] R :=
  piEquiv (Fin r) R R f

namespace KoszulComplex

/- Definition 15.28.2: the source-facing notation `K^•(f)` denotes the family-level Koszul
complex obtained by applying the owner `koszulComplex` to the tuple linear form
`koszulLinearForm f`. -/
scoped notation:max "K^•(" f ")" => koszulComplex (koszulLinearForm f)

/- Textbook notation for the powered family-level Koszul complex
`K^•(f₁^(n+1), \ldots, fᵣ^(n+1))`. -/
scoped notation:max "K^•[" n "](" f ")" =>
  koszulComplex (koszulLinearForm (fun i ↦ f i ^ (n + 1)))

end KoszulComplex

end
