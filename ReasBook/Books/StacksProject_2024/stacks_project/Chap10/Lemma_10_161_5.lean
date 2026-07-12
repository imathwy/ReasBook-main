import Mathlib
import StacksProject_2024.Chap10.Definition_10_161_1
import StacksProject_2024.Chap10.Definition_10_122_3
import StacksProject_2024.Chap10.Lemma_10_123_14
import StacksProject_2024.Chap10.Lemma_10_161_3
import StacksProject_2024.Chap10.Lemma_10_161_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
* primary domain: quasi-finite finite-type extensions of Noetherian domains and permanence of the
  chapter owner `IsN2Ring`;
* sampled owner/bridge declarations:
  - `Algebra.FiniteType.QuasiFinite`, the chapter source-facing owner for a quasi-finite finite
    type extension from `Definition_10_122_3`;
  - `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`, the Zariski-main
    bridge from `Lemma_10_123_14`;
  - `isN2Ring_of_isLocalization`, the localization-stability bridge from `Lemma_10_161_3`;
  - `isN2Ring_of_finite_extension`, the finite-extension bridge from `Lemma_10_161_7`.
* best owner abstraction: the source-facing extension hypothesis is
  `Algebra.FiniteType.QuasiFinite R S`; the public conclusion is the owner `IsN2Ring S`.
* primitive data: the quasi-finite extension owner `hRSqf`, the injectivity hypothesis on
  `algebraMap R S`, and the ambient Noetherian/domain data.
* derived API: the separate finite-type and quasi-finite components, the finite intermediate
  subalgebra from Zariski's Main Theorem, and localization/finite-extension permanence of
  `IsN2Ring`.

Source/core/bridge triage:
* `source-facing`: the permanence theorem for a quasi-finite extension of domains;
* `core/canonical`: `IsN2Ring`;
* `bridge/view`: the Zariski-main finite subalgebra and the localization/finite-extension
  permanence theorems above.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [CommRing S] [IsDomain S] [Algebra R S]

-- Proof sketch: let `K = FractionRing R` and `L = FractionRing S`. Quasi-finiteness and
-- injectivity of `R → S` imply that `L / K` is finite. Applying the `N-2` hypothesis to `R`
-- shows that the integral closure of `R` in `L` is finite over `R`, hence so is the integral
-- closure of `R` in `S`. Zariski's Main Theorem gives a principal-open cover on which `S` agrees
-- with that finite integral closure, reducing to the finite-extension case; then one applies the
-- finite stability of `N-2` together with localization and transitivity of integral closure.
/-- Lemma 10.161.5: if `R` is a Noetherian `N-2` domain and `R ⊂ S` is a quasi-finite extension
of domains, then `S` is `N-2`. -/
theorem isN2Ring_of_quasiFinite_extension
    (hRSqf : Algebra.FiniteType.QuasiFinite R S)
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring R] :
    IsN2Ring S := sorry

end
