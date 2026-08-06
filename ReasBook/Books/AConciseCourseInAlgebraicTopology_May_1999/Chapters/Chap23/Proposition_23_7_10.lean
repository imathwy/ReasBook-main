import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_6

noncomputable section

open CategoryTheory

-- Chapter 23 already owns the quotient-model classifying spaces `BU[n, EU]` and `BSO[n, ESO]`.
-- Proposition 23.7.10 identifies the universal Euler class on `BSO(2n)` with the pullback of
-- the top universal Chern class along a chosen restriction map `BSO(2n) → BU(n)`. This file
-- keeps the pullback construction explicit in a chosen universal Chern family and uses the
-- uniqueness theorem from `Theorem_23_7_6` to show that the resulting class is independent of
-- that choice.

section

variable {n : ℕ}
variable {ESO : Type} [TopologicalSpace ESO]
variable [MulAction (SO(2 * n)) ESO]
variable [ContinuousSMul (SO(2 * n)) ESO]
variable {EU : Type} [TopologicalSpace EU]
variable [MulAction (U n) EU] [ContinuousSMul (U n) EU]
variable {γBU : BU[n, EU] → Type}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
variable [∀ b, TopologicalSpace (γBU b)]
variable [FiberBundle (Fin n → ℂ) γBU]
variable [∀ b, AddCommGroup (γBU b)]
variable [∀ b, Module ℂ (γBU b)]
variable [VectorBundle ℂ (Fin n → ℂ) γBU]

/-- The universal Euler class on `BSO(2n)` attached to a chosen restriction map
`BSO(2n) → BU(n)` and a chosen family of universal Chern classes on `BU(n)` is the pullback of
the top class `c_n`. Theorem `universalEulerClass_eq_of_isUniversalChernClassFamily` shows that
this class is independent of the chosen universal Chern family. -/
abbrev universalEulerClass
    (restrictionMap : TopCat.of BSO[2 * n, ESO] ⟶ TopCat.of BU[n, EU])
    (universalChern : UniversalChernClassFamily n EU) :
    integralSingularCohomology (TopCat.of BSO[2 * n, ESO]) (2 * n) :=
  integralSingularCohomologyPullback restrictionMap (2 * n)
    (universalChern n)

/-- Unfolding `universalEulerClass` recovers the pullback of the top universal Chern class. -/
@[simp] theorem universalEulerClass_def
    (restrictionMap : TopCat.of BSO[2 * n, ESO] ⟶ TopCat.of BU[n, EU])
    (universalChern : UniversalChernClassFamily n EU) :
    universalEulerClass restrictionMap universalChern =
      integralSingularCohomologyPullback restrictionMap (2 * n) (universalChern n) :=
  rfl

/-- Proposition 23.7.10. The universal Euler class on `BSO(2n)` is the pullback of the top
universal Chern class along the chosen restriction map `BSO(2n) → BU(n)`, independently of which
universal Chern family on `BU(n)` is used to compute it. -/
theorem universalEulerClass_eq_pullback_topChernClass
    [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    (restrictionMap :
      TopCat.of BSO[2 * n, ESO] ⟶ TopCat.of BU[n, EU])
    (chosenUniversalChern : UniversalChernClassFamily n EU)
    (hChosenUniversalChern : IsUniversalChernClassFamily γBU chosenUniversalChern)
    (universalChern : UniversalChernClassFamily n EU)
    (hUniversalChern : IsUniversalChernClassFamily γBU universalChern) :
    universalEulerClass restrictionMap chosenUniversalChern =
      integralSingularCohomologyPullback restrictionMap (2 * n) (universalChern n) := by
  have hFamilies : chosenUniversalChern = universalChern := by
    have hChosen :
      (⟨chosenUniversalChern, hChosenUniversalChern⟩ :
        { u : UniversalChernClassFamily n EU //
          IsUniversalChernClassFamily γBU u }) =
      ⟨universalChern, hUniversalChern⟩ :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val hChosen
  simp [universalEulerClass, hFamilies]

/-- The pullback of the top universal Chern class along the chosen restriction map
`BSO(2n) → BU(n)` is independent of the chosen universal Chern family on `BU(n)`. -/
theorem universalEulerClass_eq_of_isUniversalChernClassFamily
    [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU]
    (restrictionMap :
      TopCat.of BSO[2 * n, ESO] ⟶ TopCat.of BU[n, EU])
    {u v : UniversalChernClassFamily n EU}
    (hu : IsUniversalChernClassFamily γBU u)
    (hv : IsUniversalChernClassFamily γBU v) :
    universalEulerClass restrictionMap u = universalEulerClass restrictionMap v := by
  simpa [universalEulerClass] using
    universalEulerClass_eq_pullback_topChernClass
      restrictionMap u hu v hv

end
