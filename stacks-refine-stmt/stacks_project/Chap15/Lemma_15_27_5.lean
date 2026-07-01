import Mathlib
import stacks_project.Chap10.Lemma_10_97_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M]
variable [IsNoetherianRing (R ⧸ I)]

set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/- Domain triage:
* `source-facing`: Lemma `15.27.5` is the textbook adic-flatness criterion for a module `M`,
  keeping the hypotheses on `M / IM` and `Tor₁^R(M, R / I)` explicit.
* `core/canonical` owners: `AdicCompletion I R`, `AdicCompletion I M`, the Tor bifunctor
  `Tor₁[R](M, N)`, and the flatness owner `Module.Flat`.
* `bridge/view`: the inverse-system presentation of completion used in Lemma `15.27.4`.
* sampled declarations in the same domain:
  `Tor₁[R](M, N)`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `flat_of_residueField_tor_one_vanishing`,
  `AdicCompletion.isAdicComplete`,
  `adicCompletion_isNoetherian_and_isAdicComplete`,
  `flat_quotient_pow_of_flat_mod_ideal_and_tor_one_quotient_vanishes`,
  `inverseLimit_flat_of_surjective_and_quotientFlat`.
* primitive data: the finitely generated ideal `I`, the quotient-flat hypothesis on
  `M ⧸ (I • ⊤)`, and the vanishing of the owner `Tor₁[R](M, R ⧸ I)`.
* derived API: Noetherianity and flatness of the completed ring/module.

The public binder is kept on the chapter source-facing surface `Tor₁[R](M, N)` rather than on the
later general `Tor[R, p]` wrapper specialized to degree `1`. -/

-- Proof sketch: Lemma `10.99.8` gives flatness of each quotient `M ⧸ (I^n • ⊤)` over
-- `R ⧸ I^n`. Lemma `10.96.3` identifies `AdicCompletion I R` and `AdicCompletion I M` with the
-- corresponding inverse limits and their quotient stages, Lemma `10.97.5` makes the completed ring
-- Noetherian, and Lemma `15.27.4` then yields flatness of the completed module over the completed
-- ring.
/-- Lemma 15.27.5: if `I` is finitely generated, `R ⧸ I` is Noetherian,
`M ⧸ (I • ⊤)` is flat over `R ⧸ I`, and `Tor₁^R(M, R ⧸ I)` vanishes, then the `I`-adic
completion `AdicCompletion I R` is Noetherian and `AdicCompletion I M` is flat over
`AdicCompletion I R`. Lean records the Tor-vanishing hypothesis as
`IsZero (Tor₁[R](M, R ⧸ I))`. -/
theorem adicCompletion_isNoetherian_and_flat_of_flat_mod_ideal_and_tor_one_vanishing
    (hI : I.FG)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor : IsZero (Tor₁[R](M, R ⧸ I))) :
    IsNoetherianRing (AdicCompletion I R) ∧
      Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  have hnoeth : IsNoetherianRing (AdicCompletion I R) :=
    (adicCompletion_isNoetherian_and_isAdicComplete I hI).1
  refine ⟨hnoeth, ?_⟩
  sorry

end
