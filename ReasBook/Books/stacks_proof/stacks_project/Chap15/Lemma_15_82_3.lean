import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_5
import stacks_proof.stacks_project.Chap15.Lemma_15_65_8
import stacks_proof.stacks_project.Chap15.Lemma_15_65_12
import stacks_proof.stacks_project.Chap15.Lemma_15_82_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open Polynomial

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

/- Domain-style sampling for Lemma 15.82.3:
- primary domain: pseudo-coherence for cochain complexes after restriction along surjective
  polynomial presentations of an `R`-algebra `A`, with finite type only needed for the
  some-presentation/every-presentation equivalences;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `isMPseudoCoherent_iff_restrictScalars_evalAtZero`,
  `cochainComplex_pseudoCoherent_tfae`;
- best owner abstraction: the canonical owner is the restricted cochain complex over the
  presentation ring, together with the project-level cochain-complex predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; the “some/every
  presentation” formulations are source-facing quantifiers over that owner, not separate public
  data;
- primitive vs. derived:
  primitive data are a surjective polynomial presentation
  `α : MvPolynomial (Fin n) R →ₐ[R] A` and the associated restricted complex;
  derived API is the existential or universal quantification over all such presentations;
- source/core/bridge triage:
  `source-facing`: the two equivalences in Lemma 15.82.3;
  `core/canonical`: `CochainComplex.IsMPseudoCoherent` and
    `CochainComplex.IsPseudoCoherent`;
  `bridge/view`: restriction of scalars along a polynomial presentation.
- layer: this file stays source-facing and deletes redundant public wrappers around the bridge
  data. -/

namespace CochainComplex

/-- Restrict a cochain complex of `A`-modules along a polynomial presentation of `A` over `R`. -/
abbrev polynomialPresentationRestriction
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

end CochainComplex

/-- Helper for Lemma 15.82.3: passing a restricted cochain complex to the derived category is the
same as restricting the derived object along the presentation map. -/
private noncomputable def polynomialPresentationRestriction_Q_iso
    (K : CpxA) {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    DerivedCategory.Q.obj (K.polynomialPresentationRestriction α) ≅
      (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj (DerivedCategory.Q.obj K) :=
  ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategoryFactors.app K).symm

/-- Helper for Lemma 15.82.3: swapping the two blocks of variables identifies the two adjoined
polynomial presentations once the chosen lifts realize the original variables. -/
private theorem adjoined_presentations_comp_sumComm
    {n₀ n₁ : ℕ}
    {α₀ : MvPolynomial (Fin n₀) R →ₐ[R] A}
    {α₁ : MvPolynomial (Fin n₁) R →ₐ[R] A}
    {f : Fin n₁ → MvPolynomial (Fin n₀) R}
    {g : Fin n₀ → MvPolynomial (Fin n₁) R}
    (hf : ∀ j : Fin n₁, α₀ (f j) = α₁ (MvPolynomial.X j))
    (hg : ∀ i : Fin n₀, α₁ (g i) = α₀ (MvPolynomial.X i)) :
    let γ₀ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₀ (MvPolynomial.X i)) (fun j ↦ α₀ (f j)))
    let γ₁ : MvPolynomial (Fin n₁ ⊕ Fin n₀) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun j ↦ α₁ (MvPolynomial.X j)) (fun i ↦ α₁ (g i)))
    γ₁.comp (MvPolynomial.renameEquiv R (Equiv.sumComm (Fin n₀) (Fin n₁))).toAlgHom = γ₀ := by
  -- Proof comment: polynomial algebra maps are determined by the variables, and the two sets of
  -- chosen lifts match exactly after the block swap.
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      simp [hg i]
  | inr j =>
      simp [hf j]

/-- Helper for Lemma 15.82.3: the common adjoined presentation over `R[x_i, y_j]` is the same
whether one evaluates the `x_i` through chosen lifts in the `y`-presentation or evaluates the
`y_j` through chosen lifts in the `x`-presentation. -/
private theorem adjoined_presentations_eq
    {n₀ n₁ : ℕ}
    {α₀ : MvPolynomial (Fin n₀) R →ₐ[R] A}
    {α₁ : MvPolynomial (Fin n₁) R →ₐ[R] A}
    {f : Fin n₁ → MvPolynomial (Fin n₀) R}
    {g : Fin n₀ → MvPolynomial (Fin n₁) R}
    (hf : ∀ j : Fin n₁, α₀ (f j) = α₁ (MvPolynomial.X j))
    (hg : ∀ i : Fin n₀, α₁ (g i) = α₀ (MvPolynomial.X i)) :
    let γ₀ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₀ (MvPolynomial.X i)) (fun j ↦ α₀ (f j)))
    let γ₁ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₁ (g i)) (fun j ↦ α₁ (MvPolynomial.X j)))
    γ₁ = γ₀ := by
  -- Proof comment: on the common ring `R[x_i, y_j]`, both algebra maps agree on every variable by
  -- the chosen lift identities.
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
      simp [hg i]
  | inr j =>
      simp [hf j]

/-- Helper for Lemma 15.82.3: restricting the regular module along a ring equivalence preserves
pseudo-coherence. -/
private theorem restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv
    {S : Type u} {T : Type v} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  let eₗ :
      ModuleCat.of S S ≃ₗ[S]
        ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)) :=
    { __ := e.toAddEquiv
      map_smul' := fun r s ↦ e.map_mul r s }
  have hPerfect :
      ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPerfect := by
    -- Proof comment: the restricted regular module is linearly equivalent to the free rank-one
    -- `S`-module, so it is finite projective and hence perfect.
    rw [ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms]
    refine ⟨0, ?_⟩
    rw [ModuleCat.hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
    constructor
    · exact Module.Projective.of_equiv eₗ
    · exact Module.Finite.equiv eₗ
  exact
    (ModuleCat.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension _).1 hPerfect |>.1

/-- Helper for Lemma 15.82.3: evaluation at `f` is evaluation at `0` after translating the
polynomial variable by `f`. -/
private theorem polynomial_eval_at_eq_evalAtZero_after_translate
    {S : Type u} [CommRing S] (f : S) :
    Polynomial.evalRingHom f =
      (Polynomial.evalRingHom (0 : S)).comp
        (Polynomial.algEquivAevalXAddC f).toAlgHom.toRingHom := by
  -- Proof comment: both ring homomorphisms agree on coefficients and send `X` to `f`.
  ext p
  simp

/-- Helper for Lemma 15.82.3: multiplication by `X` in `S[X]` is injective. -/
private theorem polynomial_eq_zero_of_mul_X_eq_zero_local
    {S : Type u} [CommRing S] {p : S[X]} (h : p * X = 0) :
    p = 0 := by
  -- Proof comment: compare the coefficient of `X^(n + 1)` to recover every coefficient of `p`.
  ext n
  simpa [h] using (Polynomial.coeff_mul_X p n).symm

/-- Helper for Lemma 15.82.3: the map `p ↦ p * X` on `S[X]` is injective. -/
private theorem mul_X_injective_local
    {S : Type u} [CommRing S] :
    Function.Injective (LinearMap.mulRight (S[X]) (X : S[X])) := by
  intro p q hpq
  have hsub : (LinearMap.mulRight (S[X]) X) (p - q) = 0 := by
    rw [LinearMap.map_sub, hpq, sub_self]
  have hzero : p - q = 0 := by
    apply polynomial_eq_zero_of_mul_X_eq_zero_local
    simpa [LinearMap.mulRight_apply] using hsub
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 15.82.3: the underlying functions
`S[X] --(·X)--> S[X] --ev₀--> S` form an exact sequence. -/
private theorem evalAtZero_exact_mul_X_local
    {S : Type u} [CommRing S] :
    Function.Exact
      (fun p : S[X] ↦ p * X)
      (fun p : S[X] ↦ Polynomial.evalRingHom (0 : S) p) := by
  -- Proof comment: evaluation at `0` kills every multiple of `X`, and vanishing at `0` means
  -- divisibility by `X`.
  intro p
  constructor
  · intro hp
    have hroot : p.IsRoot 0 := (Polynomial.IsRoot.def).2 hp
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
    refine ⟨q, ?_⟩
    calc
      q * X = X * q := by rw [mul_comm]
      _ = p := by simpa using hq.symm
  · rintro ⟨q, rfl⟩
    simp [map_mul]

/-- Helper for Lemma 15.82.3: evaluation at zero is surjective on `S[X]`. -/
private theorem evalAtZero_surjective_local
    {S : Type u} [CommRing S] :
    Function.Surjective (fun p : S[X] ↦ Polynomial.evalRingHom (0 : S) p) := by
  -- Proof comment: constants already hit every element of `S`.
  intro s
  refine ⟨Polynomial.C s, ?_⟩
  simp

/-- Helper for Lemma 15.82.3: the reverse local evaluation-at-zero transfer descends from the
split derived tensor computation of Lemma `15.82.1`. -/
private theorem isMPseudoCoherent_of_restrictScalars_evalAtZero_local
    {S : Type u} [CommRing S]
    (L : DerivedCategory (ModuleCat S)) (m : ℤ) :
    ((ModuleCat.restrictScalars (Polynomial.evalRingHom (0 : S))).mapDerivedCategory.obj L)
        .IsMPseudoCoherent m →
      L.IsMPseudoCoherent m := by
  intro hL
  let _ : Algebra S[X] S := (Polynomial.evalRingHom (0 : S)).toAlgebra
  -- Proof comment: tensor back along `S[X] → S`, identify the result with `L ⊞ L⟦1⟧`, and then
  -- descend to the left summand using the split biproduct lemma.
  have hTensor :
      ((derivedTensorWithAlgebra (Polynomial.evalRingHom (0 : S))).obj
          ((ModuleCat.restrictScalars (Polynomial.evalRingHom (0 : S))).mapDerivedCategory.obj L))
        .IsMPseudoCoherent m := by
    exact derivedTensorWithAlgebra_isMPseudoCoherent
      (((ModuleCat.restrictScalars (Polynomial.evalRingHom (0 : S))).mapDerivedCategory.obj L))
      m hL
  rcases
      derivedTensor_restrictScalars_evalAtZero_isomorphic_biprod_shift (R := S) L with
    ⟨e⟩
  have hBiprod : (L ⊞ L⟦(1 : ℤ)⟧).IsMPseudoCoherent m := by
    exact isMPseudoCoherent_of_iso e m hTensor
  exact isMPseudoCoherent_left_of_biprod L (L⟦(1 : ℤ)⟧) m hBiprod

-- Proof sketch: compare a chosen surjective polynomial presentation with an arbitrary one by
-- adjoining both sets of variables and mapping the added variables to chosen lifts. After a change
-- of coordinates, the comparison maps are iterated evaluation-at-zero maps, so repeated
-- applications of Lemma `15.82.2` transfer `m`-pseudo-coherence from the chosen presentation to
-- every presentation, and the converse direction is immediate.
/-- Lemma 15.82.3: for a finite type ring map `R → A`, a cochain complex of `A`-modules is
`m`-pseudo-coherent over some surjective polynomial presentation of `A` over `R` if and only if it
is `m`-pseudo-coherent over every such presentation. -/
@[stacks 065H]
theorem cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) (m : ℤ) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := by
  constructor
  · rintro ⟨n₀, α₀, hα₀, hK₀⟩ n₁ α₁ hα₁
    classical
    -- Proof comment: choose lifts of each set of polynomial generators through the other
    -- surjective presentation so both restrictions can be compared on a common adjoined
    -- polynomial ring.
    let f : Fin n₁ → MvPolynomial (Fin n₀) R := fun j ↦
      Classical.choose (hα₀ (α₁ (MvPolynomial.X j)))
    let g : Fin n₀ → MvPolynomial (Fin n₁) R := fun i ↦
      Classical.choose (hα₁ (α₀ (MvPolynomial.X i)))
    have hf : ∀ j : Fin n₁, α₀ (f j) = α₁ (MvPolynomial.X j) := fun j ↦
      Classical.choose_spec (hα₀ (α₁ (MvPolynomial.X j)))
    have hg : ∀ i : Fin n₀, α₁ (g i) = α₀ (MvPolynomial.X i) := fun i ↦
      Classical.choose_spec (hα₁ (α₀ (MvPolynomial.X i)))
    let γ₀ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₀ (MvPolynomial.X i)) (fun j ↦ α₀ (f j)))
    let γ₁ : MvPolynomial (Fin n₀ ⊕ Fin n₁) R →ₐ[R] A :=
      MvPolynomial.aeval
        (Sum.elim (fun i ↦ α₁ (g i)) (fun j ↦ α₁ (MvPolynomial.X j)))
    have hγ :
        γ₁ = γ₀ := by
      -- Proof comment: the source proof compares both restrictions on the same adjoined
      -- polynomial ring, so the two adjoined presentation maps agree directly on variables.
      simpa [γ₀, γ₁] using
        (adjoined_presentations_eq (R := R) (A := A) (hf := hf) (hg := hg))
    -- Route correction: keep the source proof on the common adjoined presentation instead of
    -- switching to an unrelated finite-type argument. The remaining gap is now exactly the source
    -- induction: each adjoined presentation should be obtained from the original one by adjoining
    -- variables one at a time and reducing to evaluation at zero via Lemma `15.82.2`.
    -- TODO: prove `(K.polynomialPresentationRestriction γ₀).IsMPseudoCoherent m` from `hK₀` by
    -- iterating the one-variable adjoin/evaluate-at-zero step from `α₀` to `γ₀`; rewrite `γ₁` to
    -- `γ₀` using `hγ`; then run the symmetric induction from `γ₁` down to `α₁`.
    sorry
  · intro hEvery
    -- Proof comment: a finite type algebra admits at least one surjective polynomial presentation,
    -- and evaluating the universal hypothesis there supplies the existential witness.
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    exact ⟨n, α, hα, hEvery n α hα⟩

-- Proof sketch: use the previous equivalence for every integer `m`; then invoke Lemma `15.65.5`
-- on each presentation ring to pass between pseudo-coherence and `m`-pseudo-coherence for all
-- `m`.
/-- Pseudo-coherence relative to `R` can likewise be checked on one surjective polynomial
presentation of the finite type `R`-algebra `A`. -/
theorem cochainComplex_isPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
    [Algebra.FiniteType R A] (K : CpxA) :
    (∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsPseudoCoherent) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α → (K.polynomialPresentationRestriction α).IsPseudoCoherent := by
  constructor
  · rintro ⟨n₀, α₀, hα₀, hK₀⟩ n α hα
    -- Proof comment: convert the chosen pseudo-coherent witness into degreewise
    -- `m`-pseudo-coherence, apply the previous theorem in each degree, and package the result back
    -- into pseudo-coherence.
    have hAllM₀ : ∀ m : ℤ, (K.polynomialPresentationRestriction α₀).IsMPseudoCoherent m :=
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α₀)).out 0 1).mp hK₀
    have hAllM : ∀ m : ℤ, (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := by
      intro m
      have hSome :
          ∃ (n : ℕ) (β : MvPolynomial (Fin n) R →ₐ[R] A),
            Function.Surjective β ∧ (K.polynomialPresentationRestriction β).IsMPseudoCoherent m :=
        ⟨n₀, α₀, hα₀, hAllM₀ m⟩
      exact
        (cochainComplex_isMPseudoCoherentOverSomePolynomialPresentation_iff_overEveryPolynomialPresentation
          K m).mp hSome n α hα
    exact
      ((cochainComplex_pseudoCoherent_tfae (K.polynomialPresentationRestriction α)).out 1 0).mp
        hAllM
  · intro hEvery
    -- Proof comment: any surjective polynomial presentation from finite type gives the required
    -- existential witness.
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    exact ⟨n, α, hα, hEvery n α hα⟩

end
