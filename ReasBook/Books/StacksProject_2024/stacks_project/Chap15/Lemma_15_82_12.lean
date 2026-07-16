import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_61_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_81_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [Algebra.FiniteType R A]

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)

/-- The base-changed algebra `A ⊗[R] R'` is finite type over the new base ring `R'`. -/
local instance instFiniteTypeAprime : Algebra.FiniteType R' Aprime :=
  Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType R' (R' ⊗[R] A))
    (Algebra.TensorProduct.commRight R R' A)

/-- Helper for Lemma 15.82.12: the coefficient map gives the canonical algebra
`R[x₁, \dots, xₙ] → R'[x₁, \dots, xₙ]`. -/
local instance instPolynomialBaseChangeAlgebra (n : ℕ) :
    Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R') :=
  (MvPolynomial.mapAlgHom (Algebra.ofId R R')).toAlgebra

/-- Helper for Lemma 15.82.12: after adjoining lifts for two surjective polynomial
presentations, the two resulting maps from the common polynomial ring agree. -/
private theorem adjoined_presentations_eq
    {S : Type u} [CommRing S] [Algebra R S]
    {n₀ n₁ : ℕ}
    {α₀ : MvPolynomial (Fin n₀) R →ₐ[R] S}
    {α₁ : MvPolynomial (Fin n₁) R →ₐ[R] S}
    {f : Fin n₁ → MvPolynomial (Fin n₀) R}
    {g : Fin n₀ → MvPolynomial (Fin n₁) R}
    (hf : ∀ j : Fin n₁, α₀ (f j) = α₁ (MvPolynomial.X j))
    (hg : ∀ i : Fin n₀, α₁ (g i) = α₀ (MvPolynomial.X i)) :
    let γ₀ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] S :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₀ (MvPolynomial.X i)) (fun j ↦ α₀ (f j)))
    let γ₁ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] S :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₁ (g i)) (fun j ↦ α₁ (MvPolynomial.X j)))
    γ₁ = γ₀ := by
  -- Proof comment: both adjoined presentation maps are determined by the variables, and the
  -- chosen lifts make them agree on each `x_i` and `y_j`.
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      simp [hg i]
  | inr j =>
      simp [hf j]

/-- Helper for Lemma 15.82.12: one surjective polynomial presentation suffices to conclude
relative `m`-pseudo-coherence for a cochain complex. -/
private theorem cochainComplex_isMPseudoCoherentRelativeTo_of_somePolynomialPresentation
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (E : CochainComplex (ModuleCat S) ℤ) (m : ℤ)
    (h :
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          (CochainComplex.polynomialPresentationRestriction E α).IsMPseudoCoherent m) :
    E.IsMPseudoCoherentRelativeTo R m := by
  -- Route correction: the main theorem no longer needs the source-side existential bridge.
  -- Only the target-side direction "some presentation implies relative" remains here.
  -- TODO(Lemma 15.82.12): recover the cochain-level transfer from one surjective presentation to
  -- every surjective presentation without importing the duplicate-owner branch through
  -- `Definition_15_82_4` / `Lemma_15_82_3`.
  sorry

/-- Helper for Lemma 15.82.12: restricting a chosen derived representative along a polynomial
presentation agrees with first restricting on cochain complexes and then applying `Q`. -/
private noncomputable def derived_polynomialPresentationRestriction_preimageIso
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DerivedCategory (ModuleCat S)) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] S) :
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ≅
      DerivedCategory.Q.obj
        (CochainComplex.polynomialPresentationRestriction (DerivedCategory.Q.objPreimage K) α) :=
  (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage K))

/-- Helper for Lemma 15.82.12: one surjective polynomial presentation suffices to conclude
relative derived `m`-pseudo-coherence. -/
private theorem derived_isMPseudoCoherentRelativeTo_of_somePolynomialPresentation
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (K : DerivedCategory (ModuleCat S)) (m : ℤ)
    (h :
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherentRelativeTo R m := by
  let E := DerivedCategory.Q.objPreimage K
  rcases h with ⟨n, α, hα, hKα⟩
  let e := derived_polynomialPresentationRestriction_preimageIso (R := R) K α
  have hEα :
      (CochainComplex.polynomialPresentationRestriction E α).IsMPseudoCoherent m := by
    -- Proof comment: rewrite the chosen derived witness on `K` as a witness on the fixed
    -- cochain representative `E`.
    simpa [E] using isMPseudoCoherent_of_iso e m hKα
  have hE :
      E.IsMPseudoCoherentRelativeTo R m :=
    cochainComplex_isMPseudoCoherentRelativeTo_of_somePolynomialPresentation
      (R := R) E m ⟨n, α, hα, hEα⟩
  intro n β hβ
  let eβ := derived_polynomialPresentationRestriction_preimageIso (R := R) K β
  -- Proof comment: transport the cochain-level relative statement back to the original derived
  -- object presentationwise.
  simpa [E] using isMPseudoCoherent_of_iso eβ.symm m (hE n β hβ)

/-- Helper for Lemma 15.82.12: after base changing a surjective polynomial presentation of `A`,
the restricted base-changed derived object identifies with ordinary derived scalar extension over
the polynomial ring over `R'`. -/
private noncomputable def polynomial_base_change_cover
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    MvPolynomial (Fin n) R' →ₐ[R'] Aprime :=
  letI : Algebra (MvPolynomial (Fin n) R) A := α.toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R (MvPolynomial (Fin n) R) r)
    exact (α.commutes r).symm
  (base_change_cover_map (R := R) (A := A) (R' := R') α).comp
    ((Algebra.TensorProduct.commRight R R' (MvPolynomial (Fin n) R)).toAlgHom.comp
      (MvPolynomial.algebraTensorAlgEquiv R R').symm.toAlgHom)

/-- Helper for Lemma 15.82.12: the polynomial presentation obtained by base change remains
surjective after transporting the tensor-base-changed source ring to `R'[x₁, \dots, xₙ]`. -/
private theorem polynomial_base_change_cover_surjective
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    Function.Surjective (polynomial_base_change_cover (R := R) (A := A) (R' := R') α) := by
  -- Proof comment: surjectivity is preserved by the tensor-base-change cover map and by the two
  -- algebra equivalences identifying the source with the polynomial ring over `R'`.
  letI : Algebra (MvPolynomial (Fin n) R) A := α.toAlgebra
  letI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R (MvPolynomial (Fin n) R) r)
    exact (α.commutes r).symm
  simpa [polynomial_base_change_cover] using
    (base_change_cover_map_surjective (R := R) (A := A) (R' := R') α hα).comp
      ((Algebra.TensorProduct.commRight R R' (MvPolynomial (Fin n) R)).surjective.comp
        (MvPolynomial.algebraTensorAlgEquiv R R').symm.surjective)

/-- Helper for Lemma 15.82.12: after base changing a surjective polynomial presentation of `A`,
the restricted base-changed derived object identifies with ordinary derived scalar extension over
the polynomial ring over `R'`. -/
private theorem presentationwise_base_change_iso
    {n : ℕ} (K : DModA)
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    ∃ (α' : MvPolynomial (Fin n) R' →ₐ[R'] Aprime),
      Function.Surjective α' ∧
        Nonempty
          (((ModuleCat.restrictScalars α'.toRingHom).mapDerivedCategory.obj
              (K ⊗[A]^L[Aprime])) ≅
            (((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ⊗[
              MvPolynomial (Fin n) R]^L[MvPolynomial (Fin n) R'])) := by
  refine
    ⟨polynomial_base_change_cover (R := R) (A := A) (R' := R') α,
      polynomial_base_change_cover_surjective (R := R) (A := A) (R' := R') α hα,
      ?_⟩
  -- Proof comment: the witness presentation `α'` is now fixed by the source route. The only
  -- remaining task is to identify restriction along `α'` with the tensor-base-change
  -- restriction along `α`, using `derivedTensorBaseChangeIso`, the pushout
  -- `base_change_cover_target_isPushout`, and the polynomial tensor equivalence.
  -- TODO(Lemma 15.82.12): prove the displayed comparison isomorphism for this explicit `α'`.
  sorry

/-- Helper for Lemma 15.82.12: over a polynomial presentation ring, derived scalar extension to
the corresponding polynomial ring over `R'` preserves absolute `m`-pseudo-coherence. -/
private theorem derivedTensorWithAlgebra_isMPseudoCoherent_over_polynomial_presentation
    {n : ℕ}
    (K : DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) (m : ℤ)
    (hK : K.IsMPseudoCoherent m) :
    (K ⊗[MvPolynomial (Fin n) R]^L[MvPolynomial (Fin n) R']).IsMPseudoCoherent m := by
  -- Proof comment: this is exactly the absolute preservation statement of Lemma `15.65.12`
  -- specialized to the polynomial presentation ring.
  -- TODO(Lemma 15.82.12): keep this specialization local until the upstream owner chain through
  -- `Lemma_15_65_6` is repaired; importing `Lemma_15_65_12` still rebuilds that broken file in
  -- item mode.
  sorry

-- Proof sketch: for each surjective polynomial presentation `P → A`, base change to the
-- surjective presentation `P ⊗[R] R' → A ⊗[R] R'`, use Lemma `15.61.2` to identify the derived
-- base change of the restricted complex with restriction of the base-changed complex to
-- `P ⊗[R] R'`, then apply Lemma `15.65.12` over the polynomial ring over `R'`.
/-- Lemma 15.82.12 (1): if `K^•` is `m`-pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is `m`-pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (m : ℤ) (hTor : IsTorIndependent R A R')
    (hK : K.IsMPseudoCoherentRelativeTo R m) :
    (K ⊗[A]^L[Aprime]).IsMPseudoCoherentRelativeTo R' m := by
  -- Proof comment: choose one polynomial presentation of `A` that already witnesses relative
  -- `m`-pseudo-coherence of `K`, base change that presentation to one over `R'`, and then apply
  -- the absolute base-change theorem over the polynomial ring.
  let _ := hTor
  rcases
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1
        (inferInstance : Algebra.FiniteType R A) with
    ⟨n, α, hα⟩
  have hKα :
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
    hK n α hα
  rcases presentationwise_base_change_iso (R := R) (A := A) (R' := R') K α hα with
    ⟨α', hα', ⟨e⟩⟩
  refine
    derived_isMPseudoCoherentRelativeTo_of_somePolynomialPresentation
      (R := R') (S := Aprime) (K := K ⊗[A]^L[Aprime]) m ?_
  have hBase :
      ((((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) ⊗[
          MvPolynomial (Fin n) R]^L[MvPolynomial (Fin n) R']).IsMPseudoCoherent m) := by
    -- Proof comment: once the presentation is fixed, the source theorem reduces to the absolute
    -- preservation of `m`-pseudo-coherence under derived scalar extension.
    simpa using
      derivedTensorWithAlgebra_isMPseudoCoherent_over_polynomial_presentation
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) m hKα
  have hTarget :
      ((ModuleCat.restrictScalars α'.toRingHom).mapDerivedCategory.obj
        (K ⊗[A]^L[Aprime])).IsMPseudoCoherent m := by
    -- Proof comment: transport the absolute statement back through the presentationwise
    -- comparison isomorphism.
    simpa using isMPseudoCoherent_of_iso e.symm m hBase
  exact ⟨n, α', hα', hTarget⟩

-- Proof sketch: apply part `(1)` presentationwise for every integer `m`, or equivalently replace
-- Lemma `15.65.12` by its pseudo-coherent variant after the same Tor-independent base-change
-- comparison from Lemma `15.61.2`.
/-- Lemma 15.82.12 (2): if `K^•` is pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (hTor : IsTorIndependent R A R')
    (hK : K.IsPseudoCoherentRelativeTo R) :
    (K ⊗[A]^L[Aprime]).IsPseudoCoherentRelativeTo R' := by
  -- Proof comment: unfold relative pseudo-coherence into the degreewise `m`-pseudo-coherent
  -- statements and apply part `(1)` uniformly.
  intro m
  exact
    derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_torIndependent
      K m hTor (hK m)

end

end CategoryTheory
