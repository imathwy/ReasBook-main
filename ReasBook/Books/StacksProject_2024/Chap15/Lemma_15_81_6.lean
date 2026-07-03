import stacks_project.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

section

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over finite type / finitely presented
  algebra maps;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`,
  `Module.FinitePresentation.trans`,
  the tensor-product base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a single surjective polynomial presentation of `A` over `R` over which `M` is
  finitely presented;
- derived API: finite type of `A` over `R`, ordinary finite-presentation consequences, the
  algebra finite-presentation restriction-of-scalars bridge, transitivity of module finite
  presentation, and tensor-product base change for finitely presented modules.

Source/core/bridge triage:
- `source-facing`: `Module.FinitePresentationRelativeTo R A M`;
- `core/canonical`: `Module.FinitePresentation`, `Algebra.FinitePresentation`, and the canonical
  base-change / scalar-restriction theorems for finitely presented modules;
- `bridge/view`: the theorem below, which upgrades the source-facing relative statement along a
  finitely presented algebra map using those canonical owners. -/

variable {R : Type u} {A : Type v} {A' : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing A']
variable [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
variable [AddCommGroup M] [Module A M]
variable [Algebra.FinitePresentation A A']

-- Proof sketch: start from the owner predicate
-- `Module.FinitePresentationRelativeTo R A M`, derive the finite-type `R`-algebra structure on
-- `A` from that witness, then compare the chosen polynomial presentation with a finitely
-- presented polynomial presentation of `A'` over `A`. The module-theoretic input should stay on
-- the canonical owners `Module.FinitePresentation` and `Algebra.FinitePresentation`, using the
-- standard tensor-product finite-presentation instance and the scalar-restriction/transitivity
-- bridges from Chapter 10 rather than any parallel local wrapper. The only new mathematical
-- content here is the source-facing relative reformulation over `R`, not a new owner for finite
-- presentation.
/-- Lemma 15.81.6: let `M` be an `A`-module finitely presented relative to `R`, and let
`A → A'` be a ring map of finite presentation. Then the base-changed `A'`-module `A' ⊗[A] M`,
canonically identified with the textbook module `M ⊗[A] A'`, is finitely presented relative to
`R`. -/
theorem Module.finitePresentationRelativeTo_baseChange_of_finitePresentation
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R A' (A' ⊗[A] M) := sorry

end
