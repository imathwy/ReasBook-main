import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap23.Definition_23_4_1

universe u

/- Source/core/bridge triage for Lemma 23.4.3:
- `source-facing`: the three source consequences relating sub-divided-power ideals to kernels,
  quotient divided powers, and generating sets.
- `core/canonical`: the mathlib owners `isSubDPIdeal_ker`, `Quotient.dividedPowers`,
  `Quotient.isDPMorphism`, `DividedPowers.extendsAlong`, and `span_isSubDPIdeal_iff`.
- `bridge/view`: part (1) is an exact recall of the canonical kernel theorem, part (2) is stated
  in terms of the Chapter 23 extension owner with an existential companion via
  `DividedPowers.extendsAlong_iff`, and part (3) remains a source-facing span criterion.
-/

namespace DividedPowers

section

variable {A : Type u} [CommRing A] {I : Ideal A}

/-
Lemma 23.4.3 (1): for a divided power morphism `φ : (A, I, γ) → (B, J, δ)`, the ideal
`RingHom.ker φ ⊓ I` is preserved by all positive divided powers of `γ`. This is exactly the
canonical theorem `DividedPowers.isSubDPIdeal_ker`.
-/
recall isSubDPIdeal_ker

/-- Lemma 23.4.3 (2): for an ideal `𝔞 ⊆ A`, the intersection `𝔞 ⊓ I` is a sub-divided-power
ideal of `(I, γ)` if and only if the divided powers `γ` extend along the quotient map
`A → A ⧸ 𝔞`. -/
@[stacks 07H2]
theorem isSubDPIdeal_inf_iff_extendsAlong_quotientMk
    (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      γ.extendsAlong (Ideal.Quotient.mk 𝔞) := by
  refine Iff.intro (fun h ↦ ⟨Quotient.dividedPowers γ h, Quotient.isDPMorphism γ h⟩) ?_
  rintro ⟨γq, hγq⟩
  simpa [Ideal.mk_ker] using isSubDPIdeal_ker γ γq hγq

/-- Companion expansion of Lemma 23.4.3 (2) using the defining existential form of
`DividedPowers.extendsAlong`. -/
theorem isSubDPIdeal_inf_iff_exists_quotientDividedPowers
    (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∃ γq : DividedPowers (I.map (Ideal.Quotient.mk 𝔞)),
        IsDPMorphism γ γq (Ideal.Quotient.mk 𝔞) := by
  simpa [DividedPowers.extendsAlong_iff] using
    isSubDPIdeal_inf_iff_extendsAlong_quotientMk γ 𝔞

/-- A generating set for `𝔞 ⊓ I` may be tested against the canonical span criterion for
sub-divided-power ideals. -/
theorem isSubDPIdeal_inf_iff_span_eq (γ : DividedPowers I) {𝔞 : Ideal A} {S : Set A}
    (hS : Ideal.span S = 𝔞 ⊓ I) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∀ n : ℕ, n ≠ 0 → ∀ s : A, s ∈ S → γ.dpow n s ∈ Ideal.span S := by
  have hSI : S ⊆ I := by
    intro s hs
    have hs' : s ∈ 𝔞 ⊓ I := by
      simpa [hS] using (Ideal.subset_span hs : s ∈ Ideal.span S)
    exact hs'.2
  rw [← hS]
  exact span_isSubDPIdeal_iff hSI

/-- Lemma 23.4.3 (3): for an ideal `𝔞 ⊆ A`, the intersection `𝔞 ⊓ I` is a sub-divided-power
ideal of `(I, γ)` if and only if it admits a generating set whose positive divided powers remain
in the ideal it generates. -/
@[stacks 07H2]
theorem isSubDPIdeal_inf_iff_exists_generatingSet (γ : DividedPowers I) (𝔞 : Ideal A) :
    IsSubDPIdeal γ (𝔞 ⊓ I) ↔
      ∃ S : Set A,
        Ideal.span S = 𝔞 ⊓ I ∧
          ∀ n : ℕ, n ≠ 0 → ∀ s : A, s ∈ S → γ.dpow n s ∈ Ideal.span S := by
  constructor
  · intro h
    have hS : Ideal.span ((𝔞 ⊓ I : Ideal A) : Set A) = 𝔞 ⊓ I := Ideal.span_eq _
    refine ⟨(𝔞 ⊓ I : Ideal A), hS, ?_⟩
    exact (isSubDPIdeal_inf_iff_span_eq γ hS).mp h
  · rintro ⟨S, hS, hγS⟩
    exact (isSubDPIdeal_inf_iff_span_eq γ hS).mpr hγS

end

end DividedPowers
