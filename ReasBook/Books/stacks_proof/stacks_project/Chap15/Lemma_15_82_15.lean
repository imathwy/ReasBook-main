import Mathlib
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_5

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped TensorProduct

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A] [Algebra.FiniteType A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

local instance restrictScalars_preservesFiniteLimits {S T : Type u}
    [Ring S] [Ring T] (f : S →+* T) :
    CategoryTheory.Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) := by
  exact ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

namespace CochainComplex

/-- Helper for Lemma 15.82.15: restrict a cochain complex of modules along a polynomial
presentation. -/
abbrev polynomialPresentationRestriction
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (up ℤ)).obj K

/-- Helper for Lemma 15.82.15: relative `m`-pseudo-coherence for cochain complexes is the
presentationwise absolute condition. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A) (_ : Function.Surjective α),
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- Helper for Lemma 15.82.15: relative pseudo-coherence for cochain complexes is the universal
quantification of the relative `m`-pseudo-coherent conditions. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.15: relative `m`-pseudo-coherence can be checked on one surjective
polynomial presentation. -/
theorem isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧ (K.polynomialPresentationRestriction α).IsMPseudoCoherent m := by
  -- Route correction: keep the presentationwise bridge local so this file no longer depends on
  -- the broken upstream `Lemma_15_82_3` / `Definition_15_82_4` chain.
  sorry

end CochainComplex

/-- Helper for Lemma 15.82.15: relative `m`-pseudo-coherence for modules is computed on the
degree-zero complex. -/
abbrev ModuleCat.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) (m : ℤ) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.15: relative pseudo-coherence for modules is computed on the
degree-zero complex. -/
abbrev ModuleCat.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

omit [Algebra R B] [IsScalarTower R A B] [Algebra.FiniteType R A] [Algebra.FiniteType A B] in
/-- Helper for Lemma 15.82.15: adjoining polynomial variables to a surjective polynomial
presentation keeps the induced iterated cover surjective. -/
theorem iterated_polynomial_tensor_cover_surjective
    {n m : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin m) A →ₐ[A] B) (hβ : Function.Surjective β) :
    let P := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let _ : Algebra P B := ((algebraMap A B).comp α.toRingHom).toAlgebra
    let _ : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
    let Q := MvPolynomial (Fin m) P
    let qR : Q →ₐ[P] MvPolynomial (Fin m) A := MvPolynomial.mapAlgHom (Algebra.ofId P A)
    Function.Surjective ((β.restrictScalars P).comp qR) := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin m) P
  letI : Algebra P A := α.toAlgebra
  letI : Algebra P B := ((algebraMap A B).comp α.toRingHom).toAlgebra
  letI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' rfl
  let qR : Q →ₐ[P] MvPolynomial (Fin m) A := MvPolynomial.mapAlgHom (Algebra.ofId P A)
  change Function.Surjective ((β.restrictScalars P).comp qR)
  intro t
  rcases hβ t with ⟨y, rfl⟩
  rcases (show Function.Surjective qR by
      simpa [qR, Algebra.ofId] using
        MvPolynomial.map_surjective (Algebra.ofId P A).toRingHom hα) y with ⟨z, rfl⟩
  exact ⟨z, rfl⟩

/-- Helper for Lemma 15.82.15: module pseudo-coherence is preserved by module isomorphisms. -/
lemma moduleCat_isPseudoCoherent_of_iso
    {S : Type u} [CommRing S] {M N : ModuleCat S} (e : M ≅ N)
    (hM : M.IsPseudoCoherent) :
    N.IsPseudoCoherent := by
  sorry

/-- Helper for Lemma 15.82.15: the single complex on a finite free module is termwise finite
free. -/
lemma single_zero_complex_isTermwiseFiniteFree
    {S : Type u} [Ring S] (F : ModuleCat S) [Module.Free S F] [Module.Finite S F] :
    ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  sorry

/-- Helper for Lemma 15.82.15: a derived `A`-complex is `m`-pseudo-coherent relative to `R` if
it becomes `m`-pseudo-coherent after restriction along every surjective polynomial presentation of
`A` over `R`. -/
abbrev DerivedCategory.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m

/-- Helper for Lemma 15.82.15: a derived `A`-complex is pseudo-coherent relative to `R` if it is
`m`-pseudo-coherent relative to `R` for every integer `m`. -/
abbrev DerivedCategory.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.15: a module is pseudo-coherent exactly when it is `m`-pseudo-coherent
for every integer `m`. -/
lemma moduleCat_isPseudoCoherent_iff_forall_isMPseudoCoherent
    {S : Type u} [Ring S] (M : ModuleCat S) :
    M.IsPseudoCoherent ↔ ∀ m : ℤ, M.IsMPseudoCoherent m := by
  sorry

/-- Helper for Lemma 15.82.15: absolute `m`-pseudo-coherence is stable under restriction of
scalars along a pseudo-coherent ring map. This is the exact change-of-rings input used in the
source proof. -/
theorem isMPseudoCoherent_iff_restrictScalars_local
    {S T : Type u} [Ring S] [Ring T] (f : S →+* T)
    (K : DerivedCategory (ModuleCat T)) (m : ℤ)
    (hT : ((ModuleCat.restrictScalars f).obj (ModuleCat.of T T)).IsPseudoCoherent) :
    K.IsMPseudoCoherent m ↔
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  -- Route correction: keep this bridge local so the file no longer depends on the broken
  -- upstream owner module.
  sorry

/-- Helper for Lemma 15.82.15: flat scalar extension preserves pseudo-coherence of modules. -/
theorem isPseudoCoherent_extendScalars
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (hflat : (algebraMap S T).Flat) (M : ModuleCat S)
    (hM : M.IsPseudoCoherent) :
    ((ModuleCat.extendScalars (algebraMap S T)).obj M).IsPseudoCoherent := by
  -- Route correction: keep this bridge local so the file no longer depends on the broken
  -- upstream owner module.
  sorry

/-- Helper for Lemma 15.82.15: relative `m`-pseudo-coherence of a derived complex can be checked
on one surjective polynomial presentation of the base algebra. -/
lemma isMPseudoCoherentRelativeTo_iff_overSomePolynomialPresentation
    (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A),
        Function.Surjective α ∧
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m := by
  sorry

/-- Helper for Lemma 15.82.15: restricting the regular module along a ring equivalence preserves
pseudo-coherence. -/
lemma restrictScalars_regularModule_isPseudoCoherent_of_ringEquiv
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ((ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of T T)).IsPseudoCoherent := by
  sorry

/-- Helper for Lemma 15.82.15: a relative pseudo-coherence hypothesis on the regular `A`-module
gives absolute pseudo-coherence over one chosen polynomial presentation ring. -/
lemma regularModule_restrictScalars_isPseudoCoherent_of_relative
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R)
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)).IsPseudoCoherent := by
  sorry

/-- Helper for Lemma 15.82.15: adjoining polynomial variables to a pseudo-coherent polynomial
presentation preserves pseudo-coherence of the regular module over the enlarged presentation ring. -/
lemma polynomialBaseChange_regularModule_isPseudoCoherent
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R)
    {n l : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α) :
    ((ModuleCat.restrictScalars (MvPolynomial.map α.toRingHom)).obj
      (ModuleCat.of (MvPolynomial (Fin l) A) (MvPolynomial (Fin l) A))).IsPseudoCoherent := by
  sorry

/- Domain-style sampling for Lemma 15.82.15:
- primary domain: relative pseudo-coherence in derived categories over a tower `R → A → B` of
  finite type algebras;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherentRelativeTo_of_homology`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: the chapter owner predicates
  `DerivedCategory.IsMPseudoCoherentRelativeTo R K m` and
  `DerivedCategory.IsPseudoCoherentRelativeTo R K`, together with the thin module bridge
  `Module.IsPseudoCoherentRelativeTo R A A` for the intermediate algebra;
- primitive vs. derived:
  primitive data are the finite-type hypotheses on `R → A` and `A → B` together with the
  pseudo-coherence of `A` relative to `R`; the finite-type structure on `R → B` is derived by the
  canonical transitivity instance and should not remain on the public theorem surface;
- source/core/bridge triage:
  `source-facing`: the comparison lemmas below for relative pseudo-coherence across the
    intermediate algebra `A`;
  `core/canonical`: the owner predicates `DerivedCategory.IsMPseudoCoherentRelativeTo` and
    `DerivedCategory.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the internal passage from the tower hypotheses to the induced finite-type
    structure on `R → B`.
- layer: this refinement stays source-facing and keeps the induced `R → B` finite-type witness
  internal, without adding a public wrapper.
-/

-- Proof sketch: expand relative pseudo-coherence over `A` using a surjective polynomial
-- presentation `A[y₁, ..., yₙ] → B`. Choose a surjective polynomial presentation `R[x₁, ..., xₘ] → A`.
-- By the hypothesis on `A`, the algebra `A[y₁, ..., yₙ]` is pseudo-coherent over the polynomial
-- ring `R[x₁, ..., xₘ, y₁, ..., yₙ]` via flat base change, using Lemma `15.65.13`. Then apply
-- Lemma `15.65.11` to compare `m`-pseudo-coherence over these two presentation rings, and quantify
-- over all presentations.
/-- Lemma 15.82.15 (1): if `A → B` is a finite type map of finite type `R`-algebras and `A`,
viewed as an `A`-module, is pseudo-coherent relative to `R`, then a derived `B`-complex is
`m`-pseudo-coherent relative to `A` if and only if it is `m`-pseudo-coherent relative to `R`. -/
@[stacks 067D]
theorem isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB) (m : ℤ)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherentRelativeTo R m := by
        sorry

-- Proof sketch: apply part `(1)` for every integer `m`. Pseudo-coherence is equivalent to
-- `m`-pseudo-coherence for all `m`, so the relative pseudo-coherent statement follows by
-- unfolding the definition on both sides.
/-- Lemma 15.82.15 (2): under the same hypotheses, a derived `B`-complex is pseudo-coherent
relative to `A` if and only if it is pseudo-coherent relative to `R`. -/
@[stacks 067D]
theorem isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    (K : DModB)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherentRelativeTo R := by
        sorry

end

end CategoryTheory
