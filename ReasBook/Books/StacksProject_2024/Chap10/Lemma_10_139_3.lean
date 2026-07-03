import Mathlib
import stacks_project.Chap10.Lemma_10_134_6

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open Algebra.Extension
open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

section

variable {A C : Type u} (B : Type u)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
* primary domain: the surjective Jacobi-Zariski conormal sequence for a tower `A → B → C`,
  upgraded from right exactness to short exactness under formal smoothness of `A → B`;
* sampled owner declarations:
  - `surjective_algebra_h1Cotangent_equiv_cotangent`, the canonical bridge from the surjective
    `H¹` terms to the actual conormal modules `I / I²` and `J / J²`;
  - `Extension.h1Cotangentι` and `Extension.exact_hCotangentι_cotangentComplex`, the owner
    inclusion of `H¹(L_{C/A})` into the conormal module of a presentation and the resulting
    exactness with the conormal map;
  - `Extension.equivH1CotangentOfFormallySmooth`, which calculates `H¹(L_{C/A})` from any
    formally smooth surjective presentation `B → C`;
  - `Extension.exact_cotangentComplex_toKaehler`, the owner exactness of
    `J / J² → C ⊗[B] Ω[B⁄A] → Ω[C⁄A]`;
  - `ModuleCat.shortComplexOfCompEqZero`, the canonical `ShortComplex (ModuleCat C)` owner for a
    pair of `C`-linear maps with zero composite;
  - `ModuleCat.shortComplex_shortExact`, the canonical bridge from function-level
    injective/exact/surjective data to `ShortComplex.ShortExact`.
* best owner abstraction: the public source-facing statement should be the conormal
  `ShortComplex (ModuleCat C)` with terms `I / I²`, `J / J²`, and `Ω[B⁄A] ⊗[B] C`, together with
  its canonical owner predicate `.ShortExact`; the `H1Cotangent` sequence is only a bridge/view
  used to identify the left term with the kernel of the canonical conormal map.
* primitive data vs. derived API:
  - primitive data: the tower `A → B → C`, surjectivity of `A → C`, and formal smoothness of
    `A → B`;
  - derived API: the source-facing short exact conormal sequence and the smooth specialization.
* layer triage:
  - `source-facing`: the short exact conormal sequence
    `0 → I / I² → J / J² → Ω[B⁄A] ⊗[B] C → 0`;
  - `core/canonical`: `Extension.h1Cotangentι`,
    `Extension.exact_hCotangentι_cotangentComplex`,
    `Extension.equivH1CotangentOfFormallySmooth`,
    `Extension.exact_cotangentComplex_toKaehler`,
    `surjective_algebra_h1Cotangent_equiv_cotangent`,
    `ModuleCat.shortComplexOfCompEqZero`, and `ModuleCat.shortComplex_shortExact`;
  - `bridge/view`: the `H¹` Jacobi-Zariski sequence
    `H¹(L_{C/A}) → H¹(L_{C/B}) → Ω[B⁄A] ⊗[B] C`.
-/
private theorem surjective_algebraMap_tower
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap B C) := by
  intro x
  obtain ⟨a, rfl⟩ := hAC x
  refine ⟨algebraMap A B a, ?_⟩
  rw [IsScalarTower.algebraMap_eq A B C]
  rfl

private noncomputable abbrev surjectiveJacobiZariskiExtension
    (hAC : Function.Surjective (algebraMap A C)) :
    Extension A C :=
  Extension.ofSurjective (IsScalarTower.toAlgHom A B C) (surjective_algebraMap_tower B hAC)

private noncomputable abbrev surjectiveJacobiZariskiConormalH1Equiv
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    (surjectiveJacobiZariskiExtension B hAC).H1Cotangent ≃ₗ[C]
      (Extension.ofSurjective (Algebra.ofId A C) hAC).Cotangent :=
  let P := surjectiveJacobiZariskiExtension B hAC
  letI : Algebra.FormallySmooth A P.Ring := by
    change Algebra.FormallySmooth A B
    infer_instance
  P.equivH1CotangentOfFormallySmooth.trans
    (surjective_algebra_h1Cotangent_equiv_cotangent hAC)

private theorem surjectiveJacobiZariskiConormal_exact
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    let P := surjectiveJacobiZariskiExtension B hAC
    let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
    Function.Exact
      (P.h1Cotangentι ∘ₗ e.symm.toLinearMap)
      P.cotangentComplex := by
  let P := surjectiveJacobiZariskiExtension B hAC
  let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
  have h₁₂ :
      (P.h1Cotangentι ∘ₗ e.symm.toLinearMap) ∘ₗ e =
        (LinearEquiv.refl C P.Cotangent : P.Cotangent ≃ₗ[C] P.Cotangent) ∘ₗ P.h1Cotangentι := by
    ext x
    simpa only [e, surjectiveJacobiZariskiConormalH1Equiv] using
      congrArg Subtype.val (LinearEquiv.symm_apply_apply e x)
  have h₂₃ :
      P.cotangentComplex ∘ₗ (LinearEquiv.refl C P.Cotangent : P.Cotangent ≃ₗ[C] P.Cotangent) =
        (LinearEquiv.refl C P.CotangentSpace : P.CotangentSpace ≃ₗ[C] P.CotangentSpace) ∘ₗ
          P.cotangentComplex := by
    rfl
  exact Function.Exact.of_ladder_linearEquiv_of_exact h₁₂ h₂₃
    P.exact_hCotangentι_cotangentComplex

private theorem surjectiveJacobiZariskiConormalBridge_comp_eq_zero
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    let P := surjectiveJacobiZariskiExtension B hAC
    let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
    P.cotangentComplex.comp (P.h1Cotangentι ∘ₗ e.symm.toLinearMap) = 0 := by
  let P := surjectiveJacobiZariskiExtension B hAC
  let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
  calc
    P.cotangentComplex.comp (P.h1Cotangentι ∘ₗ e.symm.toLinearMap)
      = (P.cotangentComplex.comp P.h1Cotangentι) ∘ₗ e.symm.toLinearMap := by
          simp [LinearMap.comp_assoc]
    _ = 0 := by
      rw [Function.Exact.linearMap_comp_eq_zero P.exact_hCotangentι_cotangentComplex]
      simp

private theorem surjectiveJacobiZariskiConormal_injective
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    let P := surjectiveJacobiZariskiExtension B hAC
    let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
    Function.Injective (P.h1Cotangentι ∘ₗ e.symm.toLinearMap) := by
  let P := surjectiveJacobiZariskiExtension B hAC
  let e := surjectiveJacobiZariskiConormalH1Equiv B hAC
  exact P.h1Cotangentι_injective.comp e.symm.injective

private theorem surjectiveJacobiZariskiConormal_surjective
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (surjectiveJacobiZariskiExtension B hAC).cotangentComplex := by
  let P := surjectiveJacobiZariskiExtension B hAC
  letI : Subsingleton Ω[C⁄A] := KaehlerDifferential.subsingleton_of_surjective A C hAC
  have hzero : P.toKaehler = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hExact :
      Function.Exact P.cotangentComplex (0 : P.CotangentSpace →ₗ[C] Ω[C⁄A]) := by
    simpa [hzero] using P.exact_cotangentComplex_toKaehler
  exact (LinearMap.exact_zero_iff_surjective Ω[C⁄A] P.cotangentComplex).mp hExact

/-- The source-facing conormal short complex
`I / I² → J / J² → Ω[B⁄A] ⊗[B] C`
for a tower `A → B → C` with `A → C` surjective and `A → B` formally smooth, where
`I = ker(A → C)` and `J = ker(B → C)`. -/
noncomputable def surjectiveJacobiZariskiConormalSequence
    [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) :
    ShortComplex (ModuleCat C) :=
  let P : Extension A C := surjectiveJacobiZariskiExtension B hAC
  let e :
      P.H1Cotangent ≃ₗ[C] (Extension.ofSurjective (Algebra.ofId A C) hAC).Cotangent :=
    surjectiveJacobiZariskiConormalH1Equiv B hAC
  ModuleCat.shortComplexOfCompEqZero
    (P.h1Cotangentι ∘ₗ e.symm.toLinearMap)
    P.cotangentComplex
    (surjectiveJacobiZariskiConormalBridge_comp_eq_zero B hAC)

-- Proof sketch: transport the right-exact Jacobi-Zariski sequence from
-- `H¹(L_{C/A})` from the formally smooth presentation `B → C`, identify it with `I / I²` via the
-- canonical surjective bridge of Lemma `10.134.6`, and use the owner exact sequence
-- `H¹(L_{C/A}) → J / J² → C ⊗[B] Ω[B⁄A]` attached to that presentation. Since `A → C` is
-- surjective, `Ω[C⁄A] = 0`, so the conormal map `J / J² → C ⊗[B] Ω[B⁄A]` is surjective. This
-- yields the source-facing short exact conormal sequence directly on the canonical short-complex
-- expression `ModuleCat.shortComplexOfCompEqZero`.

/-- Lemma 10.139.3 in source-facing form: if `A → C` is surjective and `A → B` is formally
smooth, then the conormal sequence
`0 → I / I² → J / J² → Ω[B⁄A] ⊗[B] C → 0`
is short exact, where `I = ker(A → C)` and `J = ker(B → C)`. -/
theorem surjective_jacobi_zariski_conormal_sequence_shortExact_of_formallySmooth
    [Algebra.FormallySmooth A B] (hAC : Function.Surjective (algebraMap A C)) :
    (surjectiveJacobiZariskiConormalSequence B hAC).ShortExact := by
  let P : Extension A C := surjectiveJacobiZariskiExtension B hAC
  let e :
      P.H1Cotangent ≃ₗ[C] (Extension.ofSurjective (Algebra.ofId A C) hAC).Cotangent :=
    surjectiveJacobiZariskiConormalH1Equiv B hAC
  exact ModuleCat.shortComplex_shortExact
    (surjectiveJacobiZariskiConormalSequence B hAC)
    (by
      change Function.Exact
        (P.h1Cotangentι ∘ₗ e.symm.toLinearMap)
        P.cotangentComplex
      exact surjectiveJacobiZariskiConormal_exact B hAC)
    (by
      change Function.Injective (P.h1Cotangentι ∘ₗ e.symm.toLinearMap)
      exact surjectiveJacobiZariskiConormal_injective B hAC)
    (by
      change Function.Surjective P.cotangentComplex
      exact surjectiveJacobiZariskiConormal_surjective B hAC)

/-- Smoothness is a specialization of the formally-smooth short exact conormal sequence. -/
theorem surjective_jacobi_zariski_conormal_sequence_shortExact_of_smooth
    [Algebra.Smooth A B] (hAC : Function.Surjective (algebraMap A C)) :
    (surjectiveJacobiZariskiConormalSequence B hAC).ShortExact := by
  letI : Algebra.FormallySmooth A B := Algebra.Smooth.formallySmooth
  simpa using
    (surjective_jacobi_zariski_conormal_sequence_shortExact_of_formallySmooth B hAC)

end
