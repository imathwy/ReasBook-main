import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_65_10

noncomputable section

open CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAMinus" => boundedAboveDerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

namespace CochainComplex

/-- Helper for Lemma 15.82.10: restrict a cochain complex of `A`-modules along a surjective
polynomial presentation of `A` over `R`. -/
abbrev polynomialPresentationRestriction
    (K : CochainComplex (ModuleCat A) ℤ) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
  ((ModuleCat.restrictScalars α.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Helper for Lemma 15.82.10: relative `m`-pseudo-coherence for a cochain complex means
`m`-pseudo-coherence after restriction along every surjective polynomial presentation. -/
abbrev IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    (K.polynomialPresentationRestriction α).IsMPseudoCoherent m

/-- Helper for Lemma 15.82.10: relative pseudo-coherence is degreewise relative
`m`-pseudo-coherence. -/
abbrev IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (K : CochainComplex (ModuleCat A) ℤ) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

end CochainComplex

/-- Helper for Lemma 15.82.10: relative `m`-pseudo-coherence for modules is defined through the
degree-zero cochain complex. -/
abbrev ModuleCat.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) (m : ℤ) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsMPseudoCoherentRelativeTo R m

/-- Helper for Lemma 15.82.10: relative pseudo-coherence for modules is defined through the
degree-zero cochain complex. -/
abbrev ModuleCat.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (M : ModuleCat A) : Prop :=
  ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherentRelativeTo R

local instance restrictScalars_preservesFiniteLimits {S T : Type*}
    [CommRing S] [CommRing T] (f : S →+* T) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars f) := by
  let G : ModuleCat S ⥤ AddCommGrpCat := forget₂ _ AddCommGrpCat
  have hlim :
      CategoryTheory.Limits.PreservesFiniteLimits (ModuleCat.restrictScalars f ⋙ G) := by
    change CategoryTheory.Limits.PreservesFiniteLimits (forget₂ (ModuleCat T) AddCommGrpCat)
    infer_instance
  exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves
    (ModuleCat.restrictScalars f) G

private abbrev polynomialPresentationRestrictionDerived {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (K : DModA) :
    DerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) :=
  (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K

/-- A derived `A`-complex is `m`-pseudo-coherent relative to `R` if it becomes
`m`-pseudo-coherent after restriction along every surjective polynomial presentation of `A`
over `R`. -/
abbrev DerivedCategory.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
    (polynomialPresentationRestrictionDerived α K).IsMPseudoCoherent m

/-- A derived `A`-complex is pseudo-coherent relative to `R` if it is `m`-pseudo-coherent
relative to `R` for every integer `m`. -/
abbrev DerivedCategory.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] ⦃A : Type v⦄ [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ m : ℤ, K.IsMPseudoCoherentRelativeTo R m

/- Domain-style sampling for Lemma 15.82.10:
- primary domain: relative pseudo-coherence in `D(A)` for a finite type `R`-algebra `A`;
- sampled owner declarations:
  `CochainComplex.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `boundedAbove_isMPseudoCoherent_of_homology`;
- best owner abstraction: the canonical owner for the derived notion is
  `DerivedCategory.IsMPseudoCoherentRelativeTo`, with the ambient algebra inferred strictly from
  the derived object;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence predicates from Definition `15.82.4` together
  with the derived-category owner `DerivedCategory.IsMPseudoCoherentRelativeTo` introduced here;
  derived API is the bounded-above homology criterion proved here by applying the absolute lemma
  presentationwise after restriction of scalars;
- source/core/bridge triage:
  `source-facing`: the bounded-above homology criteria from Lemma `15.82.10`;
  `core/canonical`: the existing relative pseudo-coherence owners `IsMPseudoCoherentRelativeTo`
    and `IsPseudoCoherentRelativeTo`;
  `bridge/view`: passage to each surjective polynomial presentation and application of
    `boundedAbove_isMPseudoCoherent_of_homology`.
- layer: this file stays source-facing and reuses the existing canonical owners instead of keeping
  a parallel `...RelativeToBase` vocabulary.
-/

/-- Helper for Lemma 15.82.10: restricting scalars commutes with homology on derived categories of
modules. -/
private noncomputable def restrictScalars_homology_iso {S T : Type*}
    [CommRing S] [CommRing T] (f : S →+* T)
    (L : DerivedCategory (ModuleCat T)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        (((ModuleCat.restrictScalars f).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eT :
      (DerivedCategory.homologyFunctor (ModuleCat T) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K
  -- Proof comment: compute homology on a chosen cochain model of `L`, compare strict homology
  -- before and after restriction, then return to the derived category.
  exact
    (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
        ((((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
      (ModuleCat.restrictScalars f).mapIso eT.symm

/-- Helper for Lemma 15.82.10: module-level `m`-pseudo-coherence is preserved by module
isomorphisms. -/
private theorem moduleCat_isMPseudoCoherent_of_iso
    {S : Type*} [CommRing S] {M N : ModuleCat S} (e : M ≅ N) (a : ℤ)
    (hM : M.IsMPseudoCoherent a) :
    N.IsMPseudoCoherent a := by
  -- Proof comment: pass the module isomorphism through the degree-zero embedding into `D(S)`.
  rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
  exact
    isMPseudoCoherent_of_iso
      ((ModuleCat.single0Functor : ModuleCat S ⥤ DerivedCategory (ModuleCat S)).mapIso e) a hM

omit [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.10: restriction of scalars along a polynomial presentation preserves a
bounded-above cutoff in the derived category. -/
private theorem polynomial_presentation_restriction_derived_isLE {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) {K : DModA} {b : ℤ}
    (hK : K.IsLE b) :
    (polynomialPresentationRestrictionDerived α K).IsLE b := by
  -- Proof comment: the homology of the restricted complex is the restricted homology module.
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro i hi
  exact
    (restrictScalars_homology_iso (f := α.toRingHom) K i).isZero_iff.2 <|
      (ModuleCat.restrictScalars α.toRingHom).map_isZero (hK i hi)

/-- Helper for Lemma 15.82.10: evaluating the relative module condition on a fixed surjective
polynomial presentation produces the corresponding absolute pseudo-coherence statement after
restricting scalars. -/
private theorem module_restrictScalars_isMPseudoCoherent_of_relative {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    {M : ModuleCat A} {a : ℤ} (hM : M.IsMPseudoCoherentRelativeTo R a) :
    ((ModuleCat.restrictScalars α.toRingHom).obj M).IsMPseudoCoherent a := by
  -- Proof comment: evaluate the relative hypothesis at `α`, then identify the restricted single
  -- complex with the degree-zero derived object of the restricted module.
  have hPresentation :
      (CochainComplex.polynomialPresentationRestriction
        ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) α).IsMPseudoCoherent a := by
    exact hM n α hα
  let e :
      (ModuleCat.single0Functor.obj ((ModuleCat.restrictScalars α.toRingHom).obj M)) ≅
        DerivedCategory.Q.obj
          (CochainComplex.polynomialPresentationRestriction
            ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) α) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (MvPolynomial (Fin n) R)) (0 : ℤ)).app
      ((ModuleCat.restrictScalars α.toRingHom).obj M)) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars α.toRingHom)
          (0 : ℤ)).app M).symm
  simpa [ModuleCat.IsMPseudoCoherent, CochainComplex.polynomialPresentationRestriction] using
    isMPseudoCoherent_of_iso e.symm a hPresentation

/-- Helper for Lemma 15.82.10: after restricting a bounded-above complex along a fixed surjective
polynomial presentation, its homology modules satisfy the absolute `(m - i)`-pseudo-coherence
hypothesis needed for Lemma `15.65.10`. -/
private theorem restricted_homology_isMPseudoCoherent {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (K : DModAMinus) (m : ℤ)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsMPseudoCoherentRelativeTo R (m - i)) :
    ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (ModuleCat (MvPolynomial (Fin n) R)) i).obj
        (polynomialPresentationRestrictionDerived α K.obj)).IsMPseudoCoherent (m - i) := by
  intro i
  -- Proof comment: first evaluate the relative hypothesis on the chosen presentation, then move
  -- the result across the canonical homology comparison for restriction of scalars.
  have hRestricted :
      ((ModuleCat.restrictScalars α.toRingHom).obj ((H i).obj K.obj)).IsMPseudoCoherent
        (m - i) := by
    exact module_restrictScalars_isMPseudoCoherent_of_relative α hα (hH i)
  exact
    moduleCat_isMPseudoCoherent_of_iso
      (restrictScalars_homology_iso (f := α.toRingHom) K.obj i).symm (m - i) hRestricted

-- Proof sketch: fix a surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`. The
-- cohomology modules of the restricted complex are exactly the cohomology modules of `K` viewed as
-- modules over `R[x₁, ..., xₙ]`, so the hypothesis gives the `(m - i)`-pseudo-coherence needed to
-- apply Lemma `15.65.10` over the polynomial ring.
/-- Lemma 15.82.10 (1): if a bounded-above derived `A`-complex has cohomology modules that are
`(m - i)`-pseudo-coherent relative to `R` in every degree, then the complex is `m`-pseudo-coherent
relative to `R`. -/
@[stacks 0678]
theorem boundedAbove_isMPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus) (m : ℤ)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.obj.IsMPseudoCoherentRelativeTo R m := by
  intro n α hα
  obtain ⟨b, hb⟩ := (derivedCategory_t_minus_iff (K := K.obj)).1 K.property
  have hKb : K.obj.IsLE b := by
    -- Proof comment: rewrite the bounded-above witness from `D⁻` into the standard `IsLE` form.
    rw [DerivedCategory.isLE_iff]
    exact hb
  have hKαb : (polynomialPresentationRestrictionDerived α K.obj).IsLE b :=
    polynomial_presentation_restriction_derived_isLE α hKb
  let Kα : boundedAboveDerivedCategory (ModuleCat (MvPolynomial (Fin n) R)) :=
    ⟨polynomialPresentationRestrictionDerived α K.obj,
      (derivedCategory_t_minus_iff
        (K := polynomialPresentationRestrictionDerived α K.obj)).2
        (by
          refine ⟨b, ?_⟩
          rw [DerivedCategory.isLE_iff] at hKαb
          exact hKαb)⟩
  -- Proof comment: after restricting to the chosen polynomial presentation, the theorem becomes
  -- the absolute bounded-above homology criterion of Lemma `15.65.10`.
  exact
    boundedAbove_isMPseudoCoherent_of_homology Kα m
      (restricted_homology_isMPseudoCoherent α hα K m hH)

-- Proof sketch: for each surjective polynomial presentation of `A` over `R`, the restricted
-- cohomology modules are pseudo-coherent over that presentation ring by hypothesis. Apply the
-- pseudo-coherent variant of Lemma `15.65.10` presentationwise.
/-- Lemma 15.82.10 (2): if every cohomology module of a bounded-above derived `A`-complex is
pseudo-coherent relative to `R`, then the complex itself is pseudo-coherent relative to `R`. -/
@[stacks 0678]
theorem boundedAbove_isPseudoCoherentRelativeTo_of_homology
    (K : DModAMinus)
    (hH :
      ∀ i : ℤ,
        ((H i).obj K.obj).IsPseudoCoherentRelativeTo R) :
    K.obj.IsPseudoCoherentRelativeTo R := by
  intro m
  exact boundedAbove_isMPseudoCoherentRelativeTo_of_homology K m fun i ↦ hH i (m - i)

end

end CategoryTheory
