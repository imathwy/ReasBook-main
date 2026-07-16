import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_2
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_3
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_89_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: the owner predicates `Module.MittagLeffler`, `Module.Projective`, and
  `Module.FinitePresentation` for modules over a commutative ring;
- sampled declarations of the same kind:
  `Module.MittagLeffler` and `Module.instMittagLefflerOfFinitePresentation` from
  `Definition_10_88_7`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective` from `Proposition_10_89_5`,
  the direct-sum owner API in `Lemma_10_89_10`,
  and mathlib's instance `Module.Projective.of_free`;
- best owner abstraction: `Module.MittagLeffler R M`;
- primitive data: the module `M` and owner hypotheses such as finite presentation, projectivity,
  or freeness;
- derived API: the finite-generation criterion below, the projective-to-Mittag-Leffler bridge, and
  the free case as a direct inferred consequence of `Module.Projective.of_free`;
- layer: clause (2) is a `bridge/view` from the projective owner to the Mittag-Leffler owner,
  while clause (3) is a recall/consequence item through the canonical owner instances.
-/

/- Example 10.91.1 (1): a finitely presented module is Mittag-Leffler. This is already the
canonical owner instance `Module.instMittagLefflerOfFinitePresentation` from
`Definition_10_88_7`, so this clause is a direct recall rather than a parallel local wrapper. -/
recall Module.instMittagLefflerOfFinitePresentation

-- Proof sketch: apply Proposition `10.89.2` to identify finite generation with surjectivity of the
-- canonical tensor-product-to-product maps, Proposition `10.89.3` to identify finite presentation
-- with bijectivity of the same maps, and Proposition `10.89.5` to rewrite the injectivity part as
-- the Mittag-Leffler condition.
/-- Example 10.91.1: for a finitely generated `R`-module `M`, being Mittag-Leffler is equivalent
to being finitely presented. -/
theorem mittagLeffler_iff_finitePresentation_of_finite [Module.Finite R M] :
    MittagLeffler R M ↔ Module.FinitePresentation R M := by
  have hsurj_iff :
      Module.Finite R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) :=
    show
      Module.Finite R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommMonoid Q] [Module R Q],
          Function.Surjective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q))
    from module_finite_tfae_tensorProduct_pi_surjective.out 0 2
  have hbij_iff :
      Module.FinitePresentation R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) :=
    show
      Module.FinitePresentation R M ↔
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Bijective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q))
    from module_finitePresentation_tfae_tensorProduct_pi_bijective.out 0 2
  constructor
  · intro hML
    have hsurj_all := hsurj_iff.1 (show Module.Finite R M from inferInstance)
    have hinj_pi :
        ∀ (A : Type (max u v)) (Q : A → Type u) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q) :=
      show
        ∀ (A : Type (max u v)) (Q : A → Type u) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q)
      from (Module.mittagLeffler_iff_tensorProduct_piRight_injective.1 hML)
    have hinj_all :
        ∀ (A : Type (max u v)) (Q : Type u) [AddCommGroup Q] [Module R Q],
          Function.Injective (TensorProduct.piRightHom R R M (fun _ : A ↦ Q)) := by
      intro A Q _ _
      exact hinj_pi A (fun _ : A ↦ Q)
    exact hbij_iff.2 (fun A Q ↦ ⟨hinj_all A Q, hsurj_all A Q⟩)
  · intro hfp
    letI : Module.FinitePresentation R M := hfp
    infer_instance

-- Proof sketch: a projective module is a direct summand of a free module. The previous theorem
-- makes the ambient free module Mittag-Leffler, and Lemma `10.89.10` identifies Mittag-Leffler
-- direct sums with stagewise Mittag-Leffler summands, so the projective summand is
-- Mittag-Leffler.
/-- A projective `R`-module is Mittag-Leffler. -/
instance instMittagLefflerOfProjective [Module.Projective R M] :
    MittagLeffler R M := by
  sorry

section

variable [Module.Free R M]

/- Example 10.91.1 (3): free modules are projective via mathlib's owner instance
`Module.Projective.of_free`, so the Mittag-Leffler conclusion is direct instance inference from
`instMittagLefflerOfProjective`. -/
#check (inferInstance : MittagLeffler R M)

end

end

end Module
