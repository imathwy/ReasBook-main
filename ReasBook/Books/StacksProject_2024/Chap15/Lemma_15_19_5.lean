import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal PrimeSpectrum
open scoped PrimeSpectrum

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable (I : Ideal R) (J : Ideal S)

local notation "K" => (I.map (algebraMap R S) + J : Ideal S)

/-
Domain triage:
- primary domain: flatness loci of finite modules over a Noetherian base, detected primewise on a
  closed subset of `Spec S` by the local criterion for flatness;
- sampled owner declarations:
  `StacksProject_2024.Chap10.Definition_10_17_1`'s closed-subset notation owner `V(-)`,
  `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers`,
  `localizedQuotientEquiv`,
  `Submodule.Quotient.module'`;
- best owner abstraction: the conclusion belongs on the chapter owner
  `Module.flatOverBaseLocus R S M`;
- primitive data: the ideals `I`, `J`, and the source-facing primewise flatness hypothesis on the
  quotient modules `M_q / I^n M_q`; the source wording `(M / I^n M)_q` is a bridge view, related
  to this owner-level local criterion input by `localizedQuotientEquiv`;
- derived API: the quotient `R ⧸ I^n`-module structure on
  `LocalizedModule.AtPrime q.asIdeal M ⧸ (I ^ n) • ⊤`, obtained canonically from
  `Submodule.Quotient.module'`, and the resulting closed-subset inclusion into
  `Module.flatOverBaseLocus`.

Source/core/bridge triage:
- `source-facing`: the hypothesis that for every `q ∈ V(I.map (algebraMap R S) + J)` and every
  `n ≥ 1`, the local quotient `M_q / I^n M_q` is flat over `R / I^n`;
- `core/canonical`: `Module.flatOverBaseLocus`, `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  and the local criterion
  `flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers`;
- `bridge/view`: the source presentation `(M / I^n M)_q`, which this file demotes in favor of the
  canonically equivalent quotient of the localized module `M_q / I^n M_q`.

The source hypothesis remains primewise because the ambient target ring for the quotient modules is
the localization of `S` at `q`, not a fixed global target ring, so the chapter owner
`Module.flatOverBaseLocus` does not apply to those hypotheses without adding an unnecessary
quotient-localization bridge layer.
-/

-- Proof sketch: fix `q ∈ V(J + IS)` and apply the local criterion for flatness from Lemma
-- `10.99.11` to the local homomorphism `R → S_q` and the finite `S_q`-module `M_q`. The
-- hypothesis supplies flatness of each quotient `M_q / I^n M_q` over `R / I^n`, so the criterion
-- yields flatness of `M_q` over `R`.
/-- Lemma 15.19.5: if `R` and `S` are Noetherian, `M` is finite over `S`, and for every `n ≥ 1`
and every prime `q ∈ V(J + IS)` the quotient `M_q / I^n M_q` is flat over `R / I^n`,
then for every `q ∈ V(J + IS)` the localization `M_q` is flat over `R`. -/
theorem localizedModule_flat_over_base_at_primes_of_zeroLocus_add_of_flat_quotient_powers
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (hquot : ∀ (q : PrimeSpectrum S) (_ : q ∈ V((K : Set S))) (n : ℕ) (_ : 1 ≤ n),
      Module.Flat (R ⧸ I ^ n)
        (LocalizedModule.AtPrime q.asIdeal M ⧸
          ((I ^ n) • (⊤ : Submodule R (LocalizedModule.AtPrime q.asIdeal M))))) :
    V((K : Set S)) ⊆
      Module.flatOverBaseLocus R S M := sorry

end
