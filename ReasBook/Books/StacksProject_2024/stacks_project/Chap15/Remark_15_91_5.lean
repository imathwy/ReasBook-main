import StacksProject_2024.stacks_project.Chap15.Example_15_91_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: Beauville-Laszlo completion/localization counterexamples in commutative algebra;
* sampled owner declarations:
  `principalAdicCompletion`,
  `IsLocalization.flat`,
  `Localization.Away`,
  `firstBeauvilleLaszloCounterexample_completion_not_flat`;
* owner abstraction: the canonical completion-side owner is
  the direct flatness predicate on the canonical completion map
  `R → principalAdicCompletion f`; the localization side stays on the canonical map
  `R → Localization.Away f`, with flatness recorded by `RingHom.Flat`;
* primitive data: a commutative ring `R` and an element `f : R`;
* derived API: the explicit first Beauville-Laszlo counterexample together with the upstream
  completion nonflatness theorem from Example `15.91.9`.

Source/core/bridge triage:
* `source-facing`: the existential comparison in Remark `15.91.5`;
* `core/canonical`: `principalAdicCompletion`, `Localization.Away`, and `RingHom.Flat`;
* `bridge/view`: the explicit quotient-ring counterexample from Example `15.91.9`, especially its
  direct completion nonflatness theorem.
-/

/-- Remark 15.91.5: there exist a commutative ring `R` and an element `f : R` such that the
localization map `R → R_f` is flat, but the `f`-adic completion map
`R → principalAdicCompletion f` is not flat. Consequently, the Beauville-Laszlo cover
`R → R^∧ ⊕ R_f` cannot in general be treated by faithfully flat descent. -/
theorem exists_flat_localization_and_nonflat_principalAdicCompletion :
    ∃ (R : Type) (_ : CommRing R) (f : R),
      (algebraMap R (Localization.Away f)).Flat ∧
        ¬ (algebraMap R (principalAdicCompletion f)).Flat := by
  refine ⟨firstBeauvilleLaszloCounterexampleRing ℚ, inferInstance,
    firstBeauvilleLaszloCounterexample_f ℚ, ?_⟩
  exact ⟨RingHom.flat_algebraMap_iff.mpr <|
      IsLocalization.flat
        (Localization.Away (firstBeauvilleLaszloCounterexample_f ℚ))
        (Submonoid.powers (firstBeauvilleLaszloCounterexample_f ℚ)),
    firstBeauvilleLaszloCounterexample_completion_not_flat ℚ⟩
