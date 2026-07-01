import Mathlib
import stacks_project.Chap15.Lemma_15_91_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable {M : Type v} [AddCommMonoid M] [Module R M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: finite-generation descent for modules in the Beauville-Laszlo completion and
  localization setting;
- sampled owner declarations:
  `principalPowerIdealImageQuotientMap`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `LocalizedModule.equivTensorProduct`,
  `adicCompletion_quotientMap_bijective`;
- best owner abstraction: the finite-generation criterion naturally lives on the pair of canonical
  base-change objects `R' ⊗[R] M` and `Away f M`; the completion case is a source-faithful
  specialization through `principalAdicCompletion`;
- primitive data: the algebra map `R → R'`, the element `f : R`, the `R`-module `M`, and the
  principal-power quotient bijectivity hypothesis;
- derived API: the completion specialization;
- triage:
  - `source-facing`: the finite-generation descent criterion;
  - `core/canonical`: the owner objects `R' ⊗[R] M`, `Away f M`, and the chapter owner
    `principalPowerIdealImageQuotientMap`;
  - `bridge/view`: the specialization to `principalAdicCompletion f`.
-/

-- Proof sketch: the forward implication is preserved by extension of scalars and localization. For
-- the converse, choose a surjection from a finite free `R`-module onto `M` whose image generates
-- both `R' ⊗[R] M` and `M_f`; its cokernel becomes zero after tensoring with `R'` and after
-- localizing away from `f`, so Lemma `15.91.2` forces that cokernel to vanish, proving that `M`
-- is finitely generated over `R`.
/-- Lemma 15.91.4: if the quotient maps `R / (f)^n → R' / (f)^n R'` are bijective for all
positive integers `n`, then an `R`-module `M` is finitely generated if and only if both its base
change `R' ⊗[R] M` and its localization `Away f M` are finitely generated over
`R'` and `Localization.Away f`, respectively. -/
theorem moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective
    (f : R)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Module.Finite R M ↔
      Module.Finite R' (R' ⊗[R] M) ∧
        Module.Finite (Localization.Away f) (Away f M) := sorry

-- Proof sketch: apply
-- `moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, and use Lemma `15.91.1` to supply the
-- required quotient-map bijectivity for the `(f)`-adic completion.
/-- The completion-localization Beauville-Laszlo criterion for finite generation, in owner form. -/
theorem moduleFinite_of_finite_completion_and_localizedAway
    (f : R)
    (hfiniteCompletion :
      Module.Finite
        (principalAdicCompletion f)
        (principalAdicCompletion f ⊗[R] M))
    (hfiniteLocalization :
      Module.Finite (Localization.Away f) (Away f M)) :
    Module.Finite R M := sorry

end
