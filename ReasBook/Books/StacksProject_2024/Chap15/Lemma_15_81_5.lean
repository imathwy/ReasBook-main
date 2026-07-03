import Mathlib.RingTheory.FiniteStability
import stacks_project.Chap15.Lemma_15_81_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under scalar base change;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.overPolynomialPresentation`,
  `Module.FinitePresentation`,
  the tensor-base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of `A` over `R` together with finite
  presentation of `M` over that presentation ring;
- derived API: presentation-independent finite presentation over any chosen polynomial
  presentation of `A`, the tensor-base-change instance for `Module.FinitePresentation`, the
  canonical `R'`-algebra structure on `A ⊗[R] R'`, and the relative finite-presentation
  statement for the base-changed module.

Source/core/bridge triage:
- `source-facing`: the theorem below about relative finite presentation after the base change
  `R → R'`;
- `core/canonical`: `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: `MvPolynomial.algebraTensorAlgEquiv` and the standard tensor base-change
  equivalences identifying the presentation ring and module after scalar extension, together with
  the canonical right-action `R'`-algebra structure on `A ⊗[R] R'`.

The owner is already the correct source-facing predicate, so the main theorem should live on the
`Module` namespace and reuse the chapter owner API
`Module.FinitePresentationRelativeTo.overPolynomialPresentation` beneath that owner rather than
unpack one particular witness and duplicate that bridge locally. -/

variable {R : Type u} {A : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [AddCommGroup M] [Module A M]

-- Proof sketch: choose any polynomial presentation `P → A` coming from the finite-type algebra
-- structure implicit in `hM`, obtain `Module.FinitePresentation P M` from the canonical owner API
-- `hM.overPolynomialPresentation`, base-change `P` to `R'`, rewrite that base change as a
-- polynomial ring over `R'`, and then apply the standard tensor-base-change stability of
-- `Module.FinitePresentation` to the induced presentation of `((A ⊗[R] R') ⊗[A] M)`.
/-- Lemma 15.81.5: if `M` is finitely presented relative to `R`, then for any base change
`R → R'` the base-changed `(A ⊗[R] R')`-module `((A ⊗[R] R') ⊗[A] M)`, canonically identified
with `M ⊗[R] R'`, is finitely presented relative to `R'`; the needed `R'`-algebra structure on
`A ⊗[R] R'` is the canonical tensor-product one, and the finite-type hypothesis on `R → A` is
already implicit in `Module.FinitePresentationRelativeTo R A M`. -/
theorem Module.finitePresentationRelativeTo_baseChange
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R' (A ⊗[R] R') ((A ⊗[R] R') ⊗[A] M) := by
  sorry

end
