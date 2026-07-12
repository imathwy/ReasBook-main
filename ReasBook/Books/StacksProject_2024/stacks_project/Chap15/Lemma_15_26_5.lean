import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap10.Lemma_10_24_5
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap10.Lemma_10_78_2
import StacksProject_2024.Chap10.Lemma_10_126_4
import StacksProject_2024.Chap15.Definition_15_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped AffineBlowupChart PrimeSpectrum

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable [Module.Finite R M]
variable {f : R} {r : ℕ}

/-- Helper for Lemma 15.26.5: a linear equivalence over the base ring should preserve finite local
freeness of fixed rank after localizing on each standard-open chart. -/
lemma finiteLocallyFreeOfRank_of_equiv
    {A : Type*} [CommRing A]
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    {n : ℕ}
    (e : N₁ ≃ₗ[A] N₂)
    [Module.FiniteLocallyFreeOfRank A N₂ n] :
    Module.FiniteLocallyFreeOfRank A N₁ n := by
  obtain ⟨s, hs_span, hs_triv⟩ :=
    Module.FiniteLocallyFreeOfRank.exists_standardOpen_cover (R := A) (M := N₂) (r := n)
  refine ⟨s, hs_span, ?_⟩
  intro g hg
  rcases hs_triv g hg with ⟨eg⟩
  -- Localizing the global equivalence on the same basic open preserves bijectivity.
  let eAway :
      LocalizedModule.Away g N₁ ≃ₗ[Localization.Away g]
        LocalizedModule.Away g N₂ :=
    LinearEquiv.ofBijective
      (LocalizedModule.map (Submonoid.powers g) e.toLinearMap)
      ⟨LocalizedModule.map_injective (Submonoid.powers g) e.toLinearMap e.injective,
        LocalizedModule.map_surjective (Submonoid.powers g) e.toLinearMap e.surjective⟩
  -- Compose the localized equivalence with the chosen trivialization for `N₂`.
  exact ⟨eAway.trans eg⟩

/-- Helper for Lemma 15.26.5: after inverting `f`, the module is finitely presented and hence
admits a finitely presented model over `R` with the same away-`f` localization. -/
lemma finitePresentation_model_away_f
    (hMf : Module.FiniteLocallyFreeOfRank (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ (M₁ : Type (max u v)) (_ : AddCommGroup M₁) (_ : Module R M₁)
      (_ : Module.FinitePresentation R M₁)
      (φ : M₁ →ₗ[R] M)
      (e : LocalizedModule.Away f M₁ ≃ₗ[Localization.Away f] LocalizedModule.Away f M),
      e.toLinearMap = LocalizedModule.map (Submonoid.powers f) φ ∧
        Module.FiniteLocallyFreeOfRank
          (Localization.Away f) (LocalizedModule.Away f M₁) r := by
  -- The away-`f` rank hypothesis first gives finite local freeness over `R_f`.
  letI : Module.FiniteLocallyFreeOfRank
      (Localization.Away f) (LocalizedModule.Away f M) r := hMf
  letI : Module.FiniteLocallyFree
      (Localization.Away f) (LocalizedModule.Away f M) :=
    Module.finiteLocallyFree_ofRank
      (R := Localization.Away f) (M := LocalizedModule.Away f M) r
  have hfpAway :
      Module.FinitePresentation
        (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.Flat
        (Localization.Away f) (LocalizedModule.Away f M) := by
    exact (module_finite_projective_tfae
      (R := Localization.Away f) (M := LocalizedModule.Away f M)).out 6 0 |>.mp
        (show Module.FiniteLocallyFree
            (Localization.Away f) (LocalizedModule.Away f M) from inferInstance)
  letI :
      Module.FinitePresentation
        (Localization.Away f) (LocalizedModule.Away f M) := hfpAway.1
  -- Then the approximation theorem supplies the finitely presented model over `R`.
  rcases exists_finitePresentation_module_with_localizedLinearEquiv
      (R := R) (S := Submonoid.powers f) (M := M) with
    ⟨M₁, _instAddCommGroupM₁, _instModuleM₁, _instFinitePresentationM₁, φ, e, he⟩
  -- Transport the away-`f` rank statement across the comparison equivalence.
  have hM₁f :
      Module.FiniteLocallyFreeOfRank
        (Localization.Away f) (LocalizedModule.Away f M₁) r := by
    letI : Module.FiniteLocallyFreeOfRank
        (Localization.Away f) (LocalizedModule.Away f M) r := hMf
    exact finiteLocallyFreeOfRank_of_equiv e
  exact ⟨M₁, inferInstance, inferInstance, inferInstance, φ, e, he, hM₁f⟩

/-- Helper for Lemma 15.26.5: any element of the scaled ideal `(f)J` factors as `f * b` with
`b ∈ J`. -/
lemma exists_factor_in_scaled_ideal
    (J : Ideal R)
    (a : Ideal.span ({f} : Set R) * J) :
    ∃ b : J, (a : R) = f * b := by
  -- Commute the product so the principal factor is the left scalar action on `J`.
  have ha : (a : R) ∈ Ideal.span ({f} : Set R) • J := by
    simpa [Ideal.mul_comm] using a.2
  rw [Submodule.ideal_span_singleton_smul] at ha
  rcases (Submodule.mem_smul_pointwise_iff_exists (a : R) f J).1 ha with ⟨b, hb, hab⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  simpa [smul_eq_mul] using hab.symm

/-- Helper for Lemma 15.26.5: in the finitely presented case, the source proof chooses a blowup
ideal whose charts make the strict transform finite locally free of rank `r`. -/
lemma finitelyPresented_case_blowupIdeal
    [Module.FinitePresentation R M]
    (hMf : Module.FiniteLocallyFreeOfRank (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
        (affineBlowupStrictTransform I a M) r := by
  -- TODO: follow the source route with `I = (f) * Fit_r(M)`, using the chart factorization
  -- `a = f * b`, Lemmas `10.70.7/8`, and the Fitting-ideal criterion on each chart.
  sorry

/-- Helper for Lemma 15.26.5: once two modules agree after inverting `f`, the same blowup ideal
works for both strict transforms on every chart whose center has the same zero locus as `(f)`. -/
lemma strictTransform_transfer_from_away_equiv
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    (I : Ideal R)
    (hV : V(({f} : Set R)) = V((I : Set R)))
    (φ : M₁ →ₗ[R] M)
    (e : LocalizedModule.Away f M₁ ≃ₗ[Localization.Away f] LocalizedModule.Away f M)
    (he : e.toLinearMap = LocalizedModule.map (Submonoid.powers f) φ)
    (hchart : ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
      (affineBlowupStrictTransform I a M₁) r) :
    ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
      (affineBlowupStrictTransform I a M) r := by
  -- TODO: compare strict transforms through the localized equivalence, then kill the kernel and
  -- cokernel using that on each chart the image of `f` is regular by Lemma `10.70.7`.
  sorry

/-
Domain-style sampling pass for Lemma 15.26.5.

Primary domain: commutative algebra of affine blowups, strict transforms, and finite locally free
modules.

Sampled owner declarations:
* `affineBlowupStrictTransform` from `Chap15/Definition_15_26_1.lean`;
* `fittingIdealAffineBlowupStrictTransform_finiteLocallyFreeOfRank` from
  `Chap15/Lemma_15_26_4.lean`;
* `Module.FiniteLocallyFreeOfRank` from `Chap10/Definition_10_78_1.lean`;
* `V(-)` from `Chap10/Definition_10_17_1.lean` as the source-facing closed-subset notation on
  `Spec R`.

Owner abstraction: the intrinsic owners are the ideal `I`, its closed subset
`V((I : Set R))`, the affine blowup charts `R[I / a]`, and the strict
transform `affineBlowupStrictTransform I a M`. The previous local structure in this file was only
a one-off package of three logical clauses and did not carry new mathematical data, so the public
statement should expose those clauses directly rather than through a parallel wrapper.

Primitive data: the ideal `I` and its chart elements `a : I`.
Derived API: finite generation of `I`, equality of closed loci with `(f)`, and the finite locally
free rank condition on each strict transform chart.

Source/core/bridge triage:
* `source-facing`: the existential blowup-ideal statement below;
* `core/canonical`: `V((I : Set R))`, `R[I / a]`, `affineBlowupStrictTransform I a M`, and
  `Module.FiniteLocallyFreeOfRank`;
* `bridge/view`: Lemma `15.26.4`, which supplies the chartwise finite-locally-free conclusion once
  the ideal choice is made.
-/

-- Proof sketch: replace `M` by a finitely presented module that agrees with it after inverting
-- `f`, choose the ideal `I = f * Fit_r(M)` in the finitely presented case, and apply the
-- Fitting-ideal criterion for finite locally free modules on each affine blowup chart after
-- quotienting by the `a`-power torsion.
/-- Lemma 15.26.5: if `M` becomes finite locally free of rank `r` after inverting `f`, then there
exists a finitely generated ideal `I` with `V(f) = V(I)` such that every affine blowup chart
`R[I/a]` makes the strict transform of `M` finite locally free of rank `r`. -/
theorem exists_blowupIdeal_with_strictTransform_finiteLocallyFreeOfRank
    (hMf : Module.FiniteLocallyFreeOfRank (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
        (affineBlowupStrictTransform I a M) r :=
  by
  -- Route correction: first descend to a finitely presented model with the same away-`f`
  -- localization, then transfer the resulting blowup ideal back along the localized equivalence.
  rcases finitePresentation_model_away_f (M := M) (f := f) (r := r) hMf with
    ⟨M₁, _instAddCommGroupM₁, _instModuleM₁, _instFinitePresentationM₁, φ, e, he, hM₁f⟩
  letI : Module.Finite R M₁ := by
    infer_instance
  rcases finitelyPresented_case_blowupIdeal (M := M₁) (f := f) (r := r) hM₁f with
    ⟨I, hIFG, hV, hchart⟩
  refine ⟨I, hIFG, hV, ?_⟩
  exact strictTransform_transfer_from_away_equiv
    (M := M) (f := f) (r := r) I hV φ e he hchart

end
