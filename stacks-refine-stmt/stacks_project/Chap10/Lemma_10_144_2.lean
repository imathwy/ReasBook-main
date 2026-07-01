import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

/- Domain triage:
* primary domain: standard étale morphisms of commutative rings;
* sampled declarations: `IsStandardEtale`, `StandardEtalePresentation`,
  `IsStandardEtale.of_isLocalizationAway`, and the tensor-product base-change instance
  `[IsStandardEtale R S] : IsStandardEtale R' (R' ⊗[R] S)`;
* source-facing layer: clause (4), which records the failure of composition stability;
* core/canonical owner: `IsStandardEtale`;
* bridge/view layer: `StandardEtalePresentation`;
* derived API: ordinary étaleness, base change, and principal-localization stability.

Primitive-vs-derived split:
* primitive data: only the `R`-algebra `S` equipped with the owner predicate
  `IsStandardEtale R S`;
* derived API: the induced `Etale R S` structure and its standard permanence properties.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/- Lemma 10.144.2 (1): a standard étale `R`-algebra is étale over `R`. This is exactly the
canonical instance `[IsStandardEtale R S] : Etale R S`. -/
#check (inferInstance : Etale R S)

/- Lemma 10.144.2 (2): the base change of a standard étale `R`-algebra along `R → R'` is
standard étale over `R'`. This is exactly the canonical tensor-product base-change instance. -/
variable (R' : Type w) [CommRing R'] [Algebra R R']

#check (inferInstance : IsStandardEtale R' (R' ⊗[R] S))

/- Lemma 10.144.2 (3): any principal localization of a standard étale `R`-algebra is again
standard étale over `R`. This is exactly `IsStandardEtale.of_isLocalizationAway`. -/
recall IsStandardEtale.of_isLocalizationAway

end

-- Proof sketch: use the finite-field counterexample from the source: `𝔽₂ → 𝔽₄` and
-- `𝔽₄ → 𝔽₄ × 𝔽₄ × 𝔽₄ × 𝔽₄` are standard étale, while the composite
-- `𝔽₂ → 𝔽₄ × 𝔽₄ × 𝔽₄ × 𝔽₄` is not standard étale.
/-- Lemma 10.144.2: there exists a tower `R → S → T` of standard étale maps whose composite
`R → T` is not standard étale. -/
theorem exists_standardEtale_tower_with_nonstandardEtale_composite :
    ∃ (R : Type u) (S : Type v) (T : Type w)
      (_ : CommRing R) (_ : CommRing S) (_ : CommRing T)
      (_ : Algebra R S) (_ : Algebra S T) (_ : Algebra R T) (_ : IsScalarTower R S T),
        IsStandardEtale R S ∧ IsStandardEtale S T ∧ ¬ IsStandardEtale R T := sorry

end Algebra
