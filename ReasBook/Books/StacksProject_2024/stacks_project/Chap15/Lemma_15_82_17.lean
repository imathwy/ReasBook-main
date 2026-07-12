import Mathlib
import StacksProject_2024.Chap10.Lemma_10_90_5
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap15.Lemma_15_82_17.Index
import StacksProject_2024.Chap15.Lemma_15_65_10
import StacksProject_2024.Chap15.Lemma_15_65_18
import StacksProject_2024.Chap15.Lemma_15_82_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "BoundedAbove" => (t.minus : ObjectProperty DModA)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.17:
- primary domain: relative pseudo-coherence for derived `A`-complexes and `A`-modules over a
  finite type algebra `A` above a Noetherian base `R`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge`;
- best owner abstraction: the chapter owner predicates
  `DerivedCategory.IsMPseudoCoherentRelativeTo` and `DerivedCategory.IsPseudoCoherentRelativeTo`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners from `15.82.10` and the absolute
  Noetherian criterion from `15.65.17`;
  derived API is the finite-homology characterization in this file, obtained presentationwise over
  surjective polynomial presentations;
- source/core/bridge triage:
  `source-facing`: the three equivalences of Lemma `15.82.17`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
    `DerivedCategory.IsPseudoCoherentRelativeTo`, and `ModuleCat.IsPseudoCoherentRelativeTo`;
  `bridge/view`: restriction of scalars along a surjective polynomial presentation.

This file is source-facing. The later ring-map class `RingHom.IsPseudoCoherentRingMap` is a
downstream bridge from `15.83`, so it must not be used as the main route here. -/

/-- Helper for Lemma 15.82.17: restriction of scalars commutes with homology even when the source
and target rings live in different universes. -/
noncomputable def restrictScalars_homology_iso_univ
    {S : Type v} {T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (L : DerivedCategory (ModuleCat T)) (i : ℤ) :
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
  -- Proof comment: compute homology on a chosen cochain representative and compare strict
  -- homology before and after restriction of scalars.
  exact
    (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
        ((((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
      (ModuleCat.restrictScalars f).mapIso eT.symm

omit [IsNoetherianRing R] [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.17: restriction along a polynomial presentation preserves any chosen
bounded-above cutoff in the derived category. -/
lemma presentation_restriction_derived_isLE {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) {K : DModA} {b : ℤ}
    (hK : K.IsLE b) :
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsLE b := by
  -- Proof comment: after restricting scalars, homology is just the restricted homology module.
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro i hi
  exact
    (restrictScalars_homology_iso_univ α.toRingHom K i).isZero_iff.2 <|
      (ModuleCat.restrictScalars α.toRingHom).map_isZero (hK i hi)

omit [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.17: finite generation over `A` stays finite after restricting scalars
to a surjective polynomial presentation of `A` over `R`. -/
lemma presentation_restriction_homology_finite_of_finite {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (N : ModuleCat A) (hN : Module.Finite A N) :
    Module.Finite (MvPolynomial (Fin n) R)
      ((ModuleCat.restrictScalars α.toRingHom).obj N) := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P ↥N := Module.compHom (↥N) α.toRingHom
  letI : IsScalarTower P A ↥N := IsScalarTower.of_compHom P A ↥N
  letI : Module.Finite A ↥N := by
    simpa using hN
  letI : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hα
  -- Proof comment: `A` is finite over the polynomial presentation ring, so finite `A`-modules
  -- are finite after restriction of scalars.
  change Module.Finite P (↑N)
  letI : Module.Finite P (↑N) := Module.Finite.trans A (↑N)
  infer_instance

omit [IsNoetherianRing R] [Algebra.FiniteType R A] in
/-- Helper for Lemma 15.82.17: finite generation over a surjective polynomial presentation ring
descends to finite generation over the quotient algebra. -/
lemma module_finite_of_compHom_surjective
    {S : Type v} [CommRing S] [Algebra R S]
    (α : S →ₐ[R] A) (_hα : Function.Surjective α)
    (N : ModuleCat A)
    (hM :
      let _ : Module S N := Module.compHom N α.toRingHom
      Module.Finite S N) :
    Module.Finite A N := by
  letI : Algebra S A := α.toAlgebra
  letI : Module S N := Module.compHom N α.toRingHom
  letI : IsScalarTower S A N := IsScalarTower.of_compHom S A N
  letI : Module.Finite S N := by
    simpa using hM
  rcases (Module.Finite.iff_exists_surjective_free S N).1 (inferInstance : Module.Finite S N) with
    ⟨n, f, hf⟩
  let g : (Fin n → A) →ₗ[A] N :=
    Module.piEquiv (Fin n) A N (fun i ↦ f (Pi.single i (1 : S)))
  have hg : Function.Surjective g := by
    -- Proof comment: the chosen `S`-linear generators remain generators after composing with the
    -- surjection `S → A`.
    intro m
    rcases hf m with ⟨x, rfl⟩
    refine ⟨fun i ↦ α (x i), ?_⟩
    have hx : x = ∑ i, x i • (Pi.single i (1 : S) : Fin n → S) := by
      -- Proof comment: decompose the source tuple against the standard basis of `S^n`.
      ext i
      simp [Pi.single_apply]
    calc
      g (fun i ↦ α (x i)) =
          ∑ i, α (x i) • f (Pi.single i (1 : S)) := by
            simpa only [g] using
              (Module.piEquiv_apply_apply (Fin n) A N
                (fun i ↦ f (Pi.single i (1 : S))) (fun i ↦ α (x i)))
      _ = ∑ i, x i • f (Pi.single i (1 : S)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rfl
      _ = ∑ i, f (x i • (Pi.single i (1 : S) : Fin n → S)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact (f.map_smul (x i) (Pi.single i (1 : S) : Fin n → S)).symm
      _ = f (∑ i, x i • (Pi.single i (1 : S) : Fin n → S)) := by
            symm
            simp only [map_sum]
      _ = f x := by
            rw [← hx]
  exact Module.Finite.of_surjective g hg

/-- Helper for Lemma 15.82.17: a termwise finite free cochain complex has finite homology in
every degree. -/
lemma termwiseFiniteFree_homology_finite
    {S : Type v} [CommRing S] [IsNoetherianRing S] {E : CochainComplex (ModuleCat S) ℤ}
    [E.IsTermwiseFiniteFree] (i : ℤ) :
    Module.Finite S (E.homology i) := by
  have hcycles : Module.Finite S (E.cycles i) := by
    -- Proof comment: cycles form a submodule of the finite degree-`i` term.
    exact Module.Finite.of_injective
      (E.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let _ : Module.Finite S (E.cycles i) := hcycles
  -- Proof comment: homology is the quotient of cycles by boundaries.
  exact Module.Finite.of_surjective
    (E.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- Helper for Lemma 15.82.17: a zero module object is finite free. -/
lemma moduleCat_finite_free_of_isZero
    {S : Type v} [CommRing S] (N : ModuleCat S) (hN : IsZero N) :
    Module.Free S N ∧ Module.Finite S N := by
  -- Proof comment: a zero module is free by subsingleton, and finite because it is equivalent to
  -- the one-point free module.
  let _ : Subsingleton N := ModuleCat.subsingleton_of_isZero hN
  refine ⟨Module.Free.of_subsingleton (R := S) (N := N), ?_⟩
  let e : ModuleCat.of S PUnit ≅ N :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of S PUnit)).isoZero ≪≫ hN.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.82.17: the augmentation map of a projective-resolution cochain model is
an isomorphism in the derived category. -/
theorem projectiveResolution_cochain_map_isIso
    {S : Type v} [CommRing S] {N : ModuleCat S} (P : ProjectiveResolution N) :
    IsIso (DerivedCategory.Q.map P.π') := by
  -- Proof comment: projective-resolution augmentations are quasi-isomorphisms, so they become
  -- isomorphisms after applying `Q`.
  infer_instance

/-- Helper for Lemma 15.82.17: the cochain complex attached to a projective resolution of `N`
represents the degree-zero single object `N[0]`. -/
noncomputable def projectiveResolution_cochain_single0_iso
    {S : Type v} [CommRing S] {N : ModuleCat S} (P : ProjectiveResolution N) :
    DerivedCategory.Q.obj P.cochainComplex ≅ ModuleCat.single0Functor.obj N := by
  let _ : IsIso (DerivedCategory.Q.map P.π') :=
    projectiveResolution_cochain_map_isIso P
  exact
    asIso (DerivedCategory.Q.map P.π') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app N).symm

/-- Helper for Lemma 15.82.17: the cochain complex attached to a finite free resolution is
termwise finite free. -/
lemma projectiveResolution_cochain_isTermwiseFiniteFree
    {S : Type v} [CommRing S] {N : ModuleCat S} {F : ChainComplex (ModuleCat S) ℕ}
    (π : F ⟶ CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat S)) N)
    [hπ : ChainComplex.IsFiniteFreeResolution (R := S) (M := N) π] :
    (ChainComplex.IsFreeResolution.toProjectiveResolution (R := S) (M := N)
      (π := π)).cochainComplex.IsTermwiseFiniteFree := by
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := S) (M := N) (π := π)
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    let e : P.cochainComplex.X (-k) ≅ P.complex.X k :=
      P.cochainComplexXIso (-k) k rfl
    have hfree : Module.Free S (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFreeResolution.free (R := S) (M := N) π k
    have hfinite : Module.Finite S (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFiniteFreeResolution.finite (R := S) (M := N) π k
    let _ : Module.Free S (P.complex.X k) := hfree
    let _ : Module.Finite S (P.complex.X k) := hfinite
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · have hi' : 0 < i := by
      omega
    have hzero : IsZero (P.cochainComplex.X i) := P.cochainComplex.isZero_of_isStrictlyLE 0 i hi'
    exact moduleCat_finite_free_of_isZero (S := S) (P.cochainComplex.X i) hzero

/-- Helper for Lemma 15.82.17: over a Noetherian ring, a finite module is pseudo-coherent. -/
lemma moduleCat_isPseudoCoherent_of_finite
    {S : Type v} [CommRing S] [IsNoetherianRing S]
    (N : ModuleCat S) [Module.Finite S N] :
    N.IsPseudoCoherent := by
  -- Proof comment: choose a finite free resolution of `N`, pass to its cochain model, and use
  -- the canonical derived isomorphism from that model to `N[0]`.
  rcases module_exists_finite_free_resolution (R := S) (M := N) with ⟨F, π, hπ⟩
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := S) (M := N) (π := π)
  rw [ModuleCat.IsPseudoCoherent]
  refine ⟨P.cochainComplex, ?_, ?_, ?_⟩
  · exact ⟨0, inferInstance⟩
  · exact projectiveResolution_cochain_isTermwiseFiniteFree (S := S) (π := π)
  · refine ⟨(projectiveResolution_cochain_single0_iso P).hom, ?_⟩
    infer_instance

/-- Helper for Lemma 15.82.17: over a Noetherian ring, finite modules are `m`-pseudo-coherent in
every degree. -/
lemma module_isMPseudoCoherent_of_finite
    {S : Type v} [CommRing S] [IsNoetherianRing S]
    (N : ModuleCat S) [Module.Finite S N] (m : ℤ) :
    N.IsMPseudoCoherent m := by
  have hN : N.IsPseudoCoherent := moduleCat_isPseudoCoherent_of_finite (S := S) N
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent] at hN
  exact hN m

/-- Helper for Lemma 15.82.17: over a Noetherian ring, `m`-pseudo-coherent derived complexes are
exactly the bounded-above complexes whose cohomology modules are finite in degrees `≥ m`. -/
lemma noetherian_isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
    {S : Type u} [CommRing S] [IsNoetherianRing S]
    (K : DerivedCategory (ModuleCat S)) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat S))) K ∧
        ∀ i : ℤ,
          m ≤ i → Module.Finite S ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj K) := by
  let Hs := DerivedCategory.homologyFunctor (ModuleCat S)
  constructor
  · intro hK
    rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
    constructor
    · -- Proof comment: above the upper support bound of the model complex, the source homology
      -- vanishes and the comparison maps are isomorphisms.
      rw [derivedCategory_t_minus_iff]
      refine ⟨max m b, ?_⟩
      intro i hi
      have hib : b < i := by
        omega
      have him : m < i := by
        omega
      have hsource : Limits.IsZero ((Hs i).obj (DerivedCategory.Q.obj E)) := by
        have hQ : (DerivedCategory.Q.obj E).IsLE b := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          let _ : E.IsStrictlyLE b := hEb
          infer_instance
        let _ : (DerivedCategory.Q.obj E).IsLE b := hQ
        exact DerivedCategory.isZero_of_isLE _ b i hib
      let eH : ((Hs i).obj (DerivedCategory.Q.obj E)) ≅ ((Hs i).obj K) := by
        let _ : IsIso ((Hs i).map α) := hαgt i him
        exact asIso ((Hs i).map α)
      exact eH.isZero_iff.1 hsource
    · intro i hi
      by_cases him : m < i
      · -- Proof comment: in degrees above `m`, homology identifies with the homology of the
        -- finite-free model.
        have hEhomology : Module.Finite S (E.homology i) :=
          termwiseFiniteFree_homology_finite (S := S) i
        have hQhomology : Module.Finite S ((Hs i).obj (DerivedCategory.Q.obj E)) := by
          let eQ : ((Hs i).obj (DerivedCategory.Q.obj E)) ≅ E.homology i :=
            CochainComplex.derived_homology_iso (R := S) E i
          let _ : Module.Finite S (E.homology i) := hEhomology
          exact Module.Finite.of_surjective
            eQ.symm.toLinearEquiv.toLinearMap
            eQ.symm.toLinearEquiv.surjective
        let eH : ((Hs i).obj (DerivedCategory.Q.obj E)) ≅ ((Hs i).obj K) := by
          let _ : IsIso ((Hs i).map α) := hαgt i him
          exact asIso ((Hs i).map α)
        let _ : Module.Finite S ((Hs i).obj (DerivedCategory.Q.obj E)) := hQhomology
        exact Module.Finite.of_surjective
          eH.toLinearEquiv.toLinearMap
          eH.toLinearEquiv.surjective
      · have hieq : i = m := by
          omega
        subst i
        -- Proof comment: in degree `m`, the defining epimorphism still descends finiteness.
        have hEhomology : Module.Finite S (E.homology m) :=
          termwiseFiniteFree_homology_finite (S := S) m
        have hQhomology : Module.Finite S ((Hs m).obj (DerivedCategory.Q.obj E)) := by
          let eQ : ((Hs m).obj (DerivedCategory.Q.obj E)) ≅ E.homology m :=
            CochainComplex.derived_homology_iso (R := S) E m
          let _ : Module.Finite S (E.homology m) := hEhomology
          exact Module.Finite.of_surjective
            eQ.symm.toLinearEquiv.toLinearMap
            eQ.symm.toLinearEquiv.surjective
        let _ : Module.Finite S ((Hs m).obj (DerivedCategory.Q.obj E)) := hQhomology
        exact Module.Finite.of_surjective
          ((Hs m).map α).hom
          ((ModuleCat.epi_iff_surjective _).1 hαm)
  · rintro ⟨hminus, hfinite⟩
    let Kminus : boundedAboveDerivedCategory (ModuleCat S) := ⟨K, hminus⟩
    -- Proof comment: above degree `m`, the positive case is automatic and the nonpositive case
    -- comes from finite modules over a Noetherian ring.
    exact boundedAbove_isMPseudoCoherent_of_homology (R := S) Kminus m <| by
      intro i
      by_cases him : i < m
      · exact moduleCat_isMPseudoCoherent_of_pos (R := S) ((Hs i).obj K) (m - i) (by omega)
      · let _ : Module.Finite S ((Hs i).obj K) := hfinite i (by omega)
        simpa using module_isMPseudoCoherent_of_finite (S := S) ((Hs i).obj K) (m - i)

-- Proof sketch: fix a surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`. The ring
-- `MvPolynomial (Fin n) R` is Noetherian, so Lemma `15.65.17 (1)` applies to the restricted
-- complex. Its bounded-above condition and finite-homology condition are exactly the intrinsic
-- conditions on `K`, because restriction of scalars along `α` preserves the underlying cohomology
-- objects and finite generation ascends and descends across the surjection.
/-- Lemma 15.82.17 (1): for a finite type `R`-algebra `A` over a Noetherian ring `R`, a derived
`A`-complex is `m`-pseudo-coherent relative to `R` exactly when it lies in `D^-(A)` and its
cohomology modules `H^i` are finite `A`-modules for all `i ≥ m`. -/
theorem isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
    (K : DModA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      BoundedAbove K ∧
        ∀ i : ℤ, m ≤ i → Module.Finite A ((H i).obj K) := by
  constructor
  · intro hK
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin n) R
    letI : Algebra P A := α.toAlgebra
    have hRestricted :
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsMPseudoCoherent m :=
      hK n α hα
    have hCriterion :=
      (noetherian_isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
        (S := P) ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) m).1
        hRestricted
    rcases hCriterion with ⟨hminusRestricted, hfiniteRestricted⟩
    constructor
    · rcases
        (derivedCategory_t_minus_iff
          (K := (ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)).1
          hminusRestricted with
          ⟨b, hb⟩
      -- Proof comment: zero restricted homology reflects to zero original homology because
      -- restriction of scalars does not change the underlying additive group.
      rw [derivedCategory_t_minus_iff]
      refine ⟨b, ?_⟩
      intro i hi
      have hzeroRestricted :
          IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat P) i).obj
              ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)) :=
        hb i hi
      have hzeroRestrictedModule :
          Limits.IsZero ((ModuleCat.restrictScalars α.toRingHom).obj ((H i).obj K)) :=
        (restrictScalars_homology_iso_univ α.toRingHom K i).isZero_iff.1 hzeroRestricted
      exact
        isZero_of_restrictScalars_obj
          (f := α.toRingHom) ((H i).obj K) hzeroRestrictedModule
    · intro i hi
      have hfiniteRestrictedHi :
          Module.Finite P
            ((DerivedCategory.homologyFunctor (ModuleCat P) i).obj
              ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)) :=
        hfiniteRestricted i hi
      have hfiniteRestrictedModule :
          Module.Finite P ((ModuleCat.restrictScalars α.toRingHom).obj ((H i).obj K)) := by
        let e := restrictScalars_homology_iso_univ α.toRingHom K i
        let _ :
            Module.Finite P
              ((DerivedCategory.homologyFunctor (ModuleCat P) i).obj
                ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)) :=
          hfiniteRestrictedHi
        exact Module.Finite.equiv e.toLinearEquiv
      -- Proof comment: finite generation over the presentation ring descends back to `A` along
      -- the chosen surjective polynomial presentation.
      exact
        module_finite_of_compHom_surjective
          (R := R) (A := A) α hα ((H i).obj K) <| by
            simpa using hfiniteRestrictedModule
  · rintro ⟨hminus, hfinite⟩
    intro n α hα
    let P := MvPolynomial (Fin n) R
    letI : Algebra P A := α.toAlgebra
    rcases (derivedCategory_t_minus_iff (K := K)).1 hminus with ⟨b, hb⟩
    have hKb : K.IsLE b := by
      -- Proof comment: rewrite the bounded-above hypothesis into the standard `IsLE` form.
      rw [DerivedCategory.isLE_iff]
      exact hb
    have hRestrictedLE :
        ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K).IsLE b :=
      presentation_restriction_derived_isLE α hKb
    have hminusRestricted :
        (t.minus : ObjectProperty (DerivedCategory (ModuleCat P)))
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) := by
      -- Proof comment: the preserved `IsLE` cutoff gives the bounded-above witness after
      -- restriction to the presentation ring.
      rw [derivedCategory_t_minus_iff]
      refine ⟨b, ?_⟩
      rw [DerivedCategory.isLE_iff] at hRestrictedLE
      exact hRestrictedLE
    have hfiniteRestricted :
        ∀ i : ℤ,
          m ≤ i →
            Module.Finite P
              ((DerivedCategory.homologyFunctor (ModuleCat P) i).obj
                ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)) := by
      intro i hi
      have hfiniteA : Module.Finite A ((H i).obj K) := hfinite i hi
      have hfiniteRestrictedModule :
          Module.Finite P ((ModuleCat.restrictScalars α.toRingHom).obj ((H i).obj K)) :=
        presentation_restriction_homology_finite_of_finite α hα ((H i).obj K) hfiniteA
      let e := restrictScalars_homology_iso_univ α.toRingHom K i
      let _ : Module.Finite P ((ModuleCat.restrictScalars α.toRingHom).obj ((H i).obj K)) :=
        hfiniteRestrictedModule
      -- Proof comment: transport finite generation back across the canonical homology
      -- comparison isomorphism.
      exact Module.Finite.equiv e.symm.toLinearEquiv
    exact
      (noetherian_isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge
        (S := P) ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) m).2
        ⟨hminusRestricted, hfiniteRestricted⟩

-- Proof sketch: combine part `(1)` for all integers `m` with the definition of relative
-- pseudo-coherence as relative `m`-pseudo-coherence in every degree.
/-- Lemma 15.82.17 (2): for a finite type `R`-algebra `A` over a Noetherian ring `R`, a derived
`A`-complex is pseudo-coherent relative to `R` exactly when it lies in `D^-(A)` and all of its
cohomology modules are finite `A`-modules. -/
theorem isPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite
    (K : DModA) :
    K.IsPseudoCoherentRelativeTo R ↔
      BoundedAbove K ∧
        ∀ i : ℤ, Module.Finite A ((H i).obj K) := by
  constructor
  · intro hK
    have hzero :=
      (isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
        (R := R) (A := A) K 0).1 (hK 0)
    constructor
    · -- Proof comment: any one degree, for example `m = 0`, already yields bounded-above-ness.
      exact hzero.1
    · intro i
      -- Proof comment: specialize part `(1)` at `m = i` to read off finiteness in degree `i`.
      exact
        ((isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
          (R := R) (A := A) K i).1 (hK i)).2 i le_rfl
  · rintro ⟨hminus, hfinite⟩
    intro m
    -- Proof comment: part `(1)` closes every degree `m` using the common bounded-above witness
    -- and the finiteness hypothesis in all degrees.
    exact
      (isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
        (R := R) (A := A) K m).2
        ⟨hminus, fun i _ ↦ hfinite i⟩

end

section

variable {R A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 15.82.17: an `A`-module is relatively `m`-pseudo-coherent over `R` when
every surjective polynomial presentation of `A` sees the restricted module as absolutely
`m`-pseudo-coherent. -/
abbrev _root_.Module.IsMPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (M : Type u) [AddCommGroup M] [Module A M] (m : ℤ) : Prop :=
  ∀ n : ℕ,
    let P := MvPolynomial (Fin n) R
    ∀ (α : P →ₐ[R] A) (_ : Function.Surjective α),
      let _ : Module P M := Module.compHom M α.toRingHom
      (ModuleCat.of P M).IsMPseudoCoherent m

/-- Helper for Lemma 15.82.17: an `A`-module is relatively pseudo-coherent over `R` when its
restrictions to all surjective polynomial presentations are absolutely pseudo-coherent. -/
abbrev _root_.Module.IsPseudoCoherentRelativeTo
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (M : Type u) [AddCommGroup M] [Module A M] : Prop :=
  ∀ m : ℤ, Module.IsMPseudoCoherentRelativeTo R A M m

-- Proof sketch: choose one surjective polynomial presentation `P → A`. If `M` is relatively
-- pseudo-coherent, then in particular it is `0`-pseudo-coherent relative to `R`, hence finite by
-- Lemma `15.82.7 (1)`. Conversely, if `M` is finite over `A`, then for every surjective
-- polynomial presentation `P → A` the
-- restricted `P`-module is finite because `A` is finite over `P`; applying Lemma `15.65.17 (3)`
-- over `P` yields pseudo-coherence presentationwise.
/-- Lemma 15.82.17 (3): for a finite type `R`-algebra `A` over a Noetherian ring `R`, an
`A`-module is pseudo-coherent relative to `R` exactly when it is finite over `A`. -/
theorem _root_.Module.isPseudoCoherentRelativeTo_iff_finite
    : Module.IsPseudoCoherentRelativeTo R A M ↔ Module.Finite A M := by
  constructor
  · intro hM
    obtain ⟨n, α, hα⟩ :=
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin n) R
    let _ : IsCoherentRing P := noetherianRing_isCoherentRing (R := P)
    letI : Module P M := Module.compHom M α.toRingHom
    have hMP : (ModuleCat.of P M).IsMPseudoCoherent 0 := by
      -- Proof comment: evaluate the relative condition at one chosen surjective polynomial
      -- presentation of `A`.
      exact hM 0 n α hα
    have hfiniteP : Module.Finite P M :=
      (moduleCat_isZeroPseudoCoherent_iff_finite (R := P) (ModuleCat.of P M)).1 hMP
    -- Proof comment: finite generation descends along the chosen surjective presentation.
    exact module_finite_of_compHom_surjective (R := R) (A := A) α hα (ModuleCat.of A M) <| by
      simpa [P] using hfiniteP
  · intro hM m n
    dsimp
    intro α hα
    let P := MvPolynomial (Fin n) R
    let _ : IsCoherentRing P := noetherianRing_isCoherentRing (R := P)
    letI : Algebra P A := α.toAlgebra
    letI : Module P M := Module.compHom M α.toRingHom
    letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    letI : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hα
    letI : Module.Finite P M := Module.Finite.trans A M
    -- Proof comment: over the Noetherian presentation ring, finite modules are `m`-pseudo-
    -- coherent for every `m`.
    simpa using (module_isMPseudoCoherent_of_finite (S := P) (ModuleCat.of P M) m)

end

end CategoryTheory
