import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

-- Proof sketch: use the long exact sequence of `Tor` for multiplication by `f`, combine the
-- quotient-flatness hypothesis with the nilpotent-ideal criterion from Lemma `10.99.8` for
-- modules annihilated by `f`, and then detect vanishing of `Tor₁` after localizing away from `f`.
/-- Lemma 10.99.16 (1): if `f` is a nonzerodivisor on `A` and on `M`, the localization `M[1/f]`
is flat over `A[1/f]`, and the quotient `M / fM`, written as `QuotSMulTop f M`, is flat over
`A / fA`, then `M` is flat over `A`. -/
theorem flat_of_regular_of_flat_localizedModule_away_and_flat_quotient (f : A)
    (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hlocal : Module.Flat (Localization.Away f) (LocalizedModule.Away f M))
    (hquot : Module.Flat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.Flat A M := sorry

-- Proof sketch: first obtain flatness from the previous criterion, then use the faithful-flatness
-- criterion via exactness reflection or nontriviality reflection, applying the same localization
-- and quotient argument with “flat” replaced by “faithfully flat”.
/-- Lemma 10.99.16 (2): under the same regularity hypotheses, if `M[1/f]` is faithfully flat over
`A[1/f]` and the quotient `M / fM`, written as `QuotSMulTop f M`, is faithfully flat over
`A / fA`, then `M` is faithfully flat over `A`. -/
theorem faithfullyFlat_of_regular_of_faithfullyFlat_localizedModule_away_and_faithfullyFlat_quotient
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f)
    (hlocal : Module.FaithfullyFlat (Localization.Away f) (LocalizedModule.Away f M))
    (hquot : Module.FaithfullyFlat (A ⧸ Ideal.span {f}) (QuotSMulTop f M)) :
    Module.FaithfullyFlat A M := sorry

end
