import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_139_1 (from Chap10) -/
open CategoryTheory

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
- primary domain: the transitivity short exact sequence for Kähler differentials over a tower
  `A → B → C` under smoothness of `B → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth`;
- best owner abstraction: the canonical `KaehlerDifferential` maps and the canonical
  `ShortComplex.moduleCatMkOfKerLERange` built from them;
- primitive data: the tower `A → B → C`;
- derived API: exactness, injectivity, and surjectivity of the two canonical maps;
- layer triage:
  - `source-facing`: the short exactness of the transitivity sequence
    `0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
  - `core/canonical`: `KaehlerDifferential.mapBaseChange`, `KaehlerDifferential.map`, and the
    standard `ShortComplex` owner in `ModuleCat`;
  - `bridge/view`: the theorem below upgrading the source-facing smoothness hypothesis to
    `ShortComplex.ShortExact`.

The previous file introduced a separate public definition
`kaehlerDifferential_transitivity_shortComplex` even though the canonical owner object is already
`ShortComplex.moduleCatMkOfKerLERange`. Since that wrapper was unused downstream and added no new
mathematics, the refined file states the result directly on the canonical short complex.
-/

-- Proof sketch: smoothness implies formal smoothness, so Lemma `10.138.9` gives injectivity of the
-- left map in the transitivity sequence. Mathlib already supplies exactness in the middle via
-- `KaehlerDifferential.exact_mapBaseChange_map` and surjectivity of the right map via
-- `KaehlerDifferential.map_surjective`. These are exactly the three ingredients for
-- `ModuleCat.shortComplex_shortExact`.
/-- Lemma 10.139.1: if `B → C` is smooth, then the transitivity sequence
`0 → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is short exact. -/
theorem kaehlerDifferential_transitivity_shortExact_of_smooth [Algebra.Smooth B C] :
    (ShortComplex.moduleCatMkOfKerLERange
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B C))
      (ModuleCat.ofHom (KaehlerDifferential.map A B C C))
      (LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map A B C)).ge).ShortExact := by
  let S : ShortComplex (ModuleCat C) :=
    ShortComplex.moduleCatMkOfKerLERange
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B C))
      (ModuleCat.ofHom (KaehlerDifferential.map A B C C))
      (LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map A B C)).ge
  refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
  · simpa [S] using KaehlerDifferential.exact_mapBaseChange_map A B C
  · simpa [S] using
      (show Function.Injective (KaehlerDifferential.mapBaseChange A B C) from
        (kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth).1)
  · simpa [S] using KaehlerDifferential.map_surjective A B C

end

/-! ### Lemma_10_139_2 (from Chap10) -/
open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.Smooth A C]

/- Domain triage:
- primary domain: the conormal exact sequence for a surjective map `B → C`, specialized from
  formal smoothness to smoothness of `A → C`;
- sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.mapBaseChange_surjective`,
  - `kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth`,
  - `Algebra.Smooth.formallySmooth`;
- best owner abstraction: the canonical `C`-linear map
  `KaehlerDifferential.mapBaseChange A B C`, with split exactness recorded by existence of a
  section;
- primitive data: the tower `A → B → C`, the surjectivity of `B → C`, and the smoothness of
  `A → C`;
- derived API: the actual splitting map `Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A]`;
- layer triage:
  - `source-facing`: Lemma `10.139.2`, the smooth case of the split conormal sequence;
  - `core/canonical`: `KaehlerDifferential.mapBaseChange A B C`;
  - `bridge/view`: Lemma `10.138.10`, which supplies the same section under the weaker
    `Algebra.FormallySmooth A C` hypothesis.

This file should therefore stay a thin smooth specialization of Lemma `10.138.10`, rather than
introducing any parallel wrapper around the owner map.
-/

-- Proof sketch: smoothness implies formal smoothness by `Algebra.Smooth.formallySmooth`, so this
-- reduces to the split exactness statement of Lemma `10.138.10`. Equivalently, the surjection
-- `KaehlerDifferential.mapBaseChange A B C` from the conormal sequence admits a `C`-linear
-- section.
/-- Lemma 10.139.2: if `A → C` is smooth and `B → C` is surjective with kernel `J`, then the exact
sequence
`0 → J/J² → Ω[B⁄A] ⊗[B] C → Ω[C⁄A] → 0`
of Lemma `10.131.9` is split exact. In canonical library form, the surjection
`KaehlerDifferential.mapBaseChange A B C : C ⊗[B] Ω[B⁄A] →ₗ[C] Ω[C⁄A]`
admits a `C`-linear section. -/
theorem kaehlerDifferential_mapBaseChange_has_section_of_smooth
    (hsurj : Function.Surjective (algebraMap B C)) :
    ∃ σ : Ω[C⁄A] →ₗ[C] C ⊗[B] Ω[B⁄A],
      (KaehlerDifferential.mapBaseChange A B C).comp σ = LinearMap.id :=
  kaehlerDifferential_mapBaseChange_has_section_of_formallySmooth hsurj

end

/-! ### Lemma_10_139_3 (from Chap10) -/
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
