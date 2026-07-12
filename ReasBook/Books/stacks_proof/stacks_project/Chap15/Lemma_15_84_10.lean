import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksProject_2024.Chap15.Definition_15_84_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_59_3
import StacksProject_2024.Chap15.Lemma_15_67_3
import StacksProject_2024.Chap15.Lemma_15_67_6
import StacksProject_2024.Chap15.Lemma_15_67_8
import StacksProject_2024.Chap15.Lemma_15_67_19
import StacksProject_2024.Chap15.Lemma_15_78_3
import StacksProject_2024.Chap15.Lemma_15_78_5
import StacksProject_2024.Chap15.Lemma_15_82_17.RestrictionBridge
import StacksProject_2024.Chap15.Lemma_15_83_2
import StacksProject_2024.Chap15.Lemma_15_83_8

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.84.10:
- primary domain: relative perfectness in derived categories and residue-field fibers over primes
  of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  the scoped notation `K ⊗[R]^L[S]`,
  `DerivedCategory.IsGE`;
- best owner abstraction: this lemma is `source-facing` on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the fiber test should use the existing derived
  scalar-extension owner `derivedTensorWithAlgebra (algebraMap R p.asIdeal.ResidueField)` applied
  to the restricted object over `R`, rather than a local duplicate fiber functor;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K : D(A)`, its bounded-below condition in
  `D(A)`, and the bounded-below conditions on its residue-field fibers after restricting scalars
  to `R`;
  the derived-fiber construction itself is already owned upstream by `derivedTensorWithAlgebra`,
  so this file should not keep a parallel local abbreviation for it;
- source/core/bridge triage:
  `source-facing`: the iff criterion below;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and `K.IsGE`;
  `bridge/view`: the canonical restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`.
-/

-- Proof sketch: the forward implication should split into a lower-bound step for `K` itself and a
-- residue-field-fiber lower-bound step. The reverse implication should follow the source-faithful
-- polynomial-presentation reduction and the local closed-fiber perfectness criterion.
/-- Helper for Lemma 15.84.10: an `R`-perfect object is pseudo-coherent over `A` by definition. -/
lemma isPseudoCoherent_of_isPerfectOver
    (K : DModA) (hK : DerivedCategory.IsPerfectOver R K) :
    K.IsPseudoCoherent :=
  hK.1

/-- Helper for Lemma 15.84.10: an `R`-perfect object has finite Tor dimension over `R` by
definition. -/
lemma hasFiniteTorDimension_of_isPerfectOver
    (K : DModA) (hK : DerivedCategory.IsPerfectOver R K) :
    HasFiniteTorDimension ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) :=
  hK.2

/-- Helper for Lemma 15.84.10: flat scalar extension preserves a lower cohomological bound. -/
lemma isGE_derivedTensorWithAlgebra_of_isGE_local
    {R' : Type u} [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (L : DerivedCategory (ModuleCat R)) {n : ℤ} (hL : L.IsGE n) :
    ((derivedTensorWithAlgebra (algebraMap R R')).obj L).IsGE n := by
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).left_adjoint_additive
  letI : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R R' from inferInstance))
  -- Proof comment: transport the vanishing range through flat homology comparison for exact
  -- scalar extension, then rewrite exact extension as the derived tensor owner.
  rw [DerivedCategory.isGE_iff] at hL ⊢
  intro i hi
  have hzero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj L) :=
    hL i hi
  have hzeroExtended :
      IsZero (F.obj ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj L)) :=
    F.map_isZero hzero
  have hzeroMapDerived :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R') i).obj (F.mapDerivedCategory.obj L)) :=
    (extendScalars_homology_iso_of_flat (R := R) (R' := R') L i).isZero_iff.1
      hzeroExtended
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat R') i).mapIso
      ((extendScalars_mapDerivedCategory_iso_of_flat (R := R) (R' := R')).app L)).isZero_iff.1
      hzeroMapDerived

/-- Helper for Lemma 15.84.10: restriction of scalars preserves a lower cohomological bound. -/
lemma restrictScalars_isGE_of_isGE
    {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)
    (L : DerivedCategory (ModuleCat T)) {n : ℤ} (hL : L.IsGE n) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj L).IsGE n := by
  -- Proof comment: transport the lower bound degreewise through the canonical homology
  -- comparison for exact restriction of scalars.
  rw [DerivedCategory.isGE_iff] at hL ⊢
  intro i hi
  have hzero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj L) :=
    hL i hi
  have hzeroRestricted :
      IsZero
        ((ModuleCat.restrictScalars f).obj
          ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj L)) :=
    (ModuleCat.restrictScalars f).map_isZero hzero
  exact (restrictScalars_homology_iso (f := f) L i).isZero_iff.2 hzeroRestricted

/-- Helper for Lemma 15.84.10: the forward implication needs a bridge from relative perfectness to
an actual lower cohomological bound on `K`. -/
lemma exists_isGE_of_isPerfectOver
    (K : DModA) (hK : DerivedCategory.IsPerfectOver R K) :
    ∃ n : ℤ, K.IsGE n := by
  rcases hK.2 with ⟨n, b, hAmp⟩
  refine ⟨n, ?_⟩
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have hResZero :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)) :=
    homology_isZero_of_hasTorAmplitudeIn_below
      (R := R)
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)
      n b i hAmp hi
  have hRestricted :
      IsZero
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)) :=
    (restrictScalars_homology_iso (f := algebraMap R A) K i).isZero_iff.1 hResZero
  exact
    isZero_of_restrictScalars_obj (f := algebraMap R A)
      ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K) hRestricted

/-- Helper for Lemma 15.84.10: finite Tor dimension over `R` should make every residue-field
fiber bounded below. -/
lemma exists_isGE_primeResidueField_of_hasFiniteTorDimension
    (K : DModA)
    (hKtor :
      HasFiniteTorDimension ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K))
    (p : PrimeSpectrum R) :
    ∃ n : ℤ,
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⊗[R]^L[
        p.asIdeal.ResidueField]).IsGE n := by
  let KR := ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)
  rcases (hasFiniteTorDimension_iff KR).1 hKtor with ⟨a, b, hAmp⟩
  have hKRGE : KR.IsGE a := by
    -- Proof comment: testing tor-amplitude against the regular module already shows that `KR`
    -- itself has no homology below `a`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact homology_isZero_of_hasTorAmplitudeIn_below (R := R) KR a b i hAmp hi
  refine ⟨a, ?_⟩
  -- Proof comment: flat scalar extension to the residue field preserves this lower
  -- cohomological bound.
  simpa [KR] using
    isGE_derivedTensorWithAlgebra_of_isGE_local
      (R := R) (R' := p.asIdeal.ResidueField) KR hKRGE

/-- Helper for Lemma 15.84.10: restricting scalars along a surjective polynomial presentation does
not change relative perfectness over the base ring `R`. -/
lemma isPerfectOver_iff_restrictScalars_of_surjective_of_flat_of_finitePresentation
    {P : Type u} [CommRing P] [Algebra R P] [Algebra P A] [IsScalarTower R P A]
    [Module.Flat R P] [Algebra.FinitePresentation R P]
    (hφ : Function.Surjective (algebraMap P A)) (K : DModA) :
    DerivedCategory.IsPerfectOver R
        ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K) ↔
      DerivedCategory.IsPerfectOver R K := by
  let KP : DerivedCategory (ModuleCat P) :=
    ((ModuleCat.restrictScalars (algebraMap P A)).mapDerivedCategory.obj K)
  let hTFAE :=
    isPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
      (R := R) (B := P) (A := A) K hφ
  constructor
  · intro hKP
    -- Proof comment: pseudo-coherence crosses the surjective presentation by Lemma `15.83.8`,
    -- while finite tor dimension over `R` is unchanged because both restrictions to `R`
    -- coincide by scalar-tower associativity.
    refine ⟨?_, ?_⟩
    · exact (hTFAE.out 3 0).mp hKP.1
    · simpa [KP] using hKP.2
  · intro hK
    -- Proof comment: the same two owner components transport back to the presentation
    -- restriction.
    refine ⟨?_, ?_⟩
    · exact (hTFAE.out 0 3).mp hK.1
    · simpa [KP] using hK.2

/-- Helper for Lemma 15.84.10: absolute perfectness over `A` implies relative perfectness over
`R` for a flat finite-presentation `R`-algebra `A`. -/
lemma isPerfectOver_of_isPerfect
    (K : DModA) (hK : K.IsPerfect) :
    DerivedCategory.IsPerfectOver R K := by
  let Res :=
    (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)
  let ResDer := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory
  have hPc : K.IsPseudoCoherent :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (R := A) K).1 hK |>.1
  rcases hK with ⟨L, e, hL⟩
  have hResBounded :
      ∃ a b : ℤ, (Res.obj L).IsStrictlyGE a ∧ (Res.obj L).IsStrictlyLE b := by
    rcases hL.bounded with ⟨a, b, hGE, hLE⟩
    refine ⟨a, b, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff] at hGE ⊢
      intro i hi
      exact (ModuleCat.restrictScalars (algebraMap R A)).map_isZero (hGE i hi)
    · rw [CochainComplex.isStrictlyLE_iff] at hLE ⊢
      intro i hi
      exact (ModuleCat.restrictScalars (algebraMap R A)).map_isZero (hLE i hi)
  let LR : CochainComplex.bounded (ModuleCat R) := by
    refine ⟨Res.obj L, ?_⟩
    exact (CochainComplex.bounded_iff (ModuleCat R) (Res.obj L)).2 hResBounded
  have hTermTor :
      ∀ i : ℤ, ModuleHasFiniteTorDimension (LR.obj.X i) := by
    intro i
    let _ : Module.Projective A (L.X i) := hL.projective i
    let _ : Module.Flat A (L.X i) := Module.Flat.of_projective (R := A) (M := L.X i)
    have hFlatR : Module.Flat R ((Res.obj L).X i) := by
      simpa [Res] using (Module.Flat.trans R A (L.X i))
    have hTd0 : ModuleHasTorDimensionLE (R := R) (LR.obj.X i) 0 :=
      (ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R) (M := LR.obj.X i)).2 hFlatR
    exact hTd0.hasFiniteTorDimension
  have hResTor : HasFiniteTorDimension (DerivedCategory.Q.obj LR.obj) :=
    hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension (R := R) LR hTermTor
  have hRestrictedTor :
      HasFiniteTorDimension (ResDer.obj K) := by
    let eRes : ResDer.obj K ≅ DerivedCategory.Q.obj LR.obj :=
      (ResDer.mapIso e) ≪≫ Res.mapDerivedCategoryFactors.app L
    exact (hasFiniteTorDimension_of_iso (R := R) eRes).2 hResTor
  exact ⟨hPc, hRestrictedTor⟩

/-- Helper for Lemma 15.84.10: over the base ring itself, relative perfectness is equivalent to
ordinary perfectness. -/
lemma isPerfect_of_isPerfectOver_self
    {S : Type u} [CommRing S]
    (K : DerivedCategory (ModuleCat S)) (hK : DerivedCategory.IsPerfectOver S K) :
    K.IsPerfect := by
  simpa [DerivedCategory.IsPerfectOver] using
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (R := S) K).2 hK

/-- Helper for Lemma 15.84.10: pseudo-coherence is preserved by isomorphisms in the derived
category. -/
lemma isPseudoCoherent_of_iso_local
    {S : Type u} [CommRing S]
    {K L : DerivedCategory (ModuleCat S)} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free representative and compose its map to
  -- `K` with the chosen isomorphism to `L`.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.84.10: the fiber of a polynomial algebra is canonically the polynomial
algebra over the residue field. -/
noncomputable def fiber_mvPolynomial_algEquiv_residueField_local
    {S : Type u} [CommRing S]
    (n : ℕ) (p : PrimeSpectrum S) :
    p.asIdeal.Fiber (MvPolynomial (Fin n) S) ≃ₐ[p.asIdeal.ResidueField]
      MvPolynomial (Fin n) p.asIdeal.ResidueField :=
  (Algebra.fiber_baseChange_algEquiv
      (A := S) (B := S) (C := MvPolynomial (Fin n) S) (p := p)).symm.trans
    (MvPolynomial.algebraTensorAlgEquiv p.asIdeal.ResidueField S (Fin n))

/-- Helper for Lemma 15.84.10: a ring equivalence transports global-dimension bounds. -/
lemma hasGlobalDimensionLE_of_ringEquiv_local
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) (n : ℕ)
    [HasGlobalDimensionLE T n] :
    HasGlobalDimensionLE S n := by
  -- Proof comment: transport projective-dimension bounds through the module-category
  -- equivalence induced by `e`.
  refine ⟨fun M ↦ ?_⟩
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let N : ModuleCat T := E.inverse.obj M
  have hN : HasProjectiveDimensionLE N n := inferInstance
  let eRestrict : N ≃ₛₗ[e.symm.toRingHom] E.functor.obj N :=
    { __ := AddEquiv.refl N
      map_smul' := by
        intro s x
        change (show N from s • x) = (e (e.symm s)) • x
        simp }
  let eTotal : N ≃ₛₗ[e.symm.toRingHom] M :=
    eRestrict.trans (E.counitIso.app M).toLinearEquiv
  exact hasProjectiveDimensionLE_of_semiLinearEquiv (e := e.symm) eTotal n

/-- Helper for Lemma 15.84.10: every fiber of the polynomial presentation ring has global
dimension at most the number of variables. -/
lemma fiber_mvPolynomial_hasGlobalDimensionLE_local
    (n : ℕ) (p : PrimeSpectrum R) :
    HasGlobalDimensionLE (p.asIdeal.Fiber (MvPolynomial (Fin n) R)) n := by
  let κ := p.asIdeal.ResidueField
  have hpoly :
      HasGlobalDimensionLE (MvPolynomial (Fin n) κ) n := by
    -- Proof comment: Proposition `10.114.2` computes the global dimension of a polynomial ring
    -- over a field.
    simpa [globalDimension_mvPolynomial_eq (k := κ) (n := n)] using
      (hasGlobalDimensionLE_globalDimension (MvPolynomial (Fin n) κ))
  letI : HasGlobalDimensionLE (MvPolynomial (Fin n) κ) n := hpoly
  -- Proof comment: transport the bound back across the canonical fiber equivalence.
  exact
    hasGlobalDimensionLE_of_ringEquiv_local
      ((fiber_mvPolynomial_algEquiv_residueField_local n p).toRingEquiv) n

/-- Helper for Lemma 15.84.10: the canonical fiber object over `κ(𝔭) ⊗[R] P` agrees with the
honest `P`-linear derived base change of `L`. -/
lemma presentation_baseChange_to_fiber_obj_iso
    {d : ℕ}
    (L : DerivedCategory (ModuleCat (MvPolynomial (Fin d) R))) (p : PrimeSpectrum R) :
    let P := MvPolynomial (Fin d) R
    let KR : DerivedCategory (ModuleCat R) :=
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
    let C := p.asIdeal.Fiber P
    ((derivedTensorWithAlgebra (algebraMap R C)).obj KR) ≅
      ((derivedTensorWithAlgebra (algebraMap P C)).obj L) := by
  let P := MvPolynomial (Fin d) R
  let KR : DerivedCategory (ModuleCat R) :=
    ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
  let C := p.asIdeal.Fiber P
  have hcomp :
      (algebraMap P C).comp (algebraMap R P) = algebraMap R C := by
    ext x
    rfl
  -- Proof comment: first rewrite the iterated `R → P → C` base change to the direct `R → C`
  -- base change, then collapse the intermediate `R → P` extension back to `L`.
  exact
    ((derivedTensorWithAlgebraCompIso
        (algebraMap R P)
        (algebraMap P C)
        (algebraMap R C)
        hcomp).app KR).symm ≪≫
      (derivedTensorWithAlgebra (algebraMap P C)).mapIso
        (extend_restrict_counit_iso_of_flat (R := R) (S := P) L)

/-- Helper for Lemma 15.84.10: the canonical fiber object over `κ(𝔭) ⊗[R] P` is also the
iterated base change of the `κ(𝔭)`-fiber. -/
lemma base_prime_fiber_obj_iso_residue_field_baseChange
    {d : ℕ}
    (L : DerivedCategory (ModuleCat (MvPolynomial (Fin d) R))) (p : PrimeSpectrum R) :
    let P := MvPolynomial (Fin d) R
    let KR : DerivedCategory (ModuleCat R) :=
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
    let κ := p.asIdeal.ResidueField
    let C := p.asIdeal.Fiber P
    ((derivedTensorWithAlgebra (algebraMap κ C)).obj (KR ⊗[R]^L[κ])) ≅
      ((derivedTensorWithAlgebra (algebraMap R C)).obj KR) := by
  let P := MvPolynomial (Fin d) R
  let KR : DerivedCategory (ModuleCat R) :=
    ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
  let κ := p.asIdeal.ResidueField
  let C := p.asIdeal.Fiber P
  have hcomp :
      (algebraMap κ C).comp (algebraMap R κ) = algebraMap R C := by
    ext x
    rfl
  -- Proof comment: this is the standard iterated-vs-direct comparison for the scalar tower
  -- `R → κ(𝔭) → κ(𝔭) ⊗[R] P`.
  exact
    (derivedTensorWithAlgebraCompIso
      (algebraMap R κ)
      (algebraMap κ C)
      (algebraMap R C)
      hcomp).app KR

/-- Helper for Lemma 15.84.10: for the polynomial presentation ring, a lower bound on the
`κ(𝔭)`-fiber makes the canonical fiber object perfect. -/
lemma isPerfect_mvPolynomial_fiber_of_isPseudoCoherent_of_base_bound
    {d : ℕ}
    (L : DerivedCategory (ModuleCat (MvPolynomial (Fin d) R)))
    (hLpc : L.IsPseudoCoherent)
    (p : PrimeSpectrum R)
    {n : ℤ}
    (hκ :
      let P := MvPolynomial (Fin d) R
      (((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) ⊗[R]^L[
        p.asIdeal.ResidueField]).IsGE n) :
    let P := MvPolynomial (Fin d) R
    let C := p.asIdeal.Fiber P
    ((derivedTensorWithAlgebra (algebraMap R C)).obj
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)).IsPerfect := by
  let P := MvPolynomial (Fin d) R
  let KR : DerivedCategory (ModuleCat R) :=
    ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
  let κ := p.asIdeal.ResidueField
  let C := p.asIdeal.Fiber P
  let Kp : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap R C)).obj KR
  let KpPresentation : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap P C)).obj L
  have ePresentation : Kp ≅ KpPresentation :=
    presentation_baseChange_to_fiber_obj_iso (R := R) (d := d) L p
  have hKpPresentationPc : KpPresentation.IsPseudoCoherent := by
    -- Proof comment: pseudo-coherence is preserved by the honest `P → κ(𝔭) ⊗[R] P` base
    -- change.
    simpa [KpPresentation] using derivedTensorWithAlgebra_isPseudoCoherent L hLpc
  have hKpPc : Kp.IsPseudoCoherent := by
    -- Proof comment: move that pseudo-coherence statement back to the canonical fiber object.
    exact isPseudoCoherent_of_iso_local ePresentation.symm hKpPresentationPc
  rcases
      (isPseudoCoherent_iff_boundedAbove_and_homology_finite (R := C) Kp).1 hKpPc with
    ⟨hKpMinus, _⟩
  rcases (derivedCategory_t_minus_iff (K := Kp)).1 hKpMinus with ⟨b, hb⟩
  have hKpLE : Kp.IsLE b := by
    -- Proof comment: unwrap the bounded-above witness into the standard `IsLE` form.
    rw [DerivedCategory.isLE_iff]
    exact hb
  have hκ' : (KR ⊗[R]^L[κ]).IsGE n := by
    simpa [P, KR, κ] using hκ
  have hIterGE :
      ((derivedTensorWithAlgebra (algebraMap κ C)).obj (KR ⊗[R]^L[κ])).IsGE n := by
    -- Proof comment: the field extension `κ(𝔭) → κ(𝔭) ⊗[R] P` is flat, so it preserves the
    -- same lower cohomological bound.
    exact
      isGE_derivedTensorWithAlgebra_of_isGE_local
        (R := κ) (R' := C) (KR ⊗[R]^L[κ]) hκ'
  have hKpGE : Kp.IsGE n := by
    -- Proof comment: identify the canonical fiber object with that iterated base change and
    -- transport the lower bound across the comparison isomorphism.
    let _ :
        ((derivedTensorWithAlgebra (algebraMap κ C)).obj (KR ⊗[R]^L[κ])).IsGE n := hIterGE
    exact
      t.isGE_of_iso
        (base_prime_fiber_obj_iso_residue_field_baseChange (R := R) (d := d) L p).symm
        n
  letI : HasGlobalDimensionLE C d := by
    simpa [P, C] using fiber_mvPolynomial_hasGlobalDimensionLE_local (R := R) d p
  have hKpAmp : HasTorAmplitudeIn Kp n b := by
    -- Proof comment: finite global dimension of the polynomial fiber upgrades the cohomological
    -- interval `[n, b]` to finite tor-amplitude.
    simpa [Kp] using
      hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
        (R := C) d Kp n b hKpGE hKpLE
  -- Proof comment: combine pseudo-coherence with finite tor dimension to conclude perfectness of
  -- the canonical fiber object.
  exact
    isPerfect_of_isPerfectOver_self Kp ⟨hKpPc, hKpAmp.hasFiniteTorDimension⟩

/-- Helper for Lemma 15.84.10: in the polynomial case, the lower bounds on the `κ(𝔭)`-fibers
force eventual vanishing of every prime residue-field homology group. -/
lemma eventually_isZero_primeResidueFieldDerivedHomology_of_mvPolynomial_fiber_perfect
    {d : ℕ}
    (L : DerivedCategory (ModuleCat (MvPolynomial (Fin d) R)))
    (hLpc : L.IsPseudoCoherent)
    (hfibers :
      ∀ p : PrimeSpectrum R,
        ∃ n : ℤ,
          (((ModuleCat.restrictScalars
              (algebraMap R (MvPolynomial (Fin d) R))).mapDerivedCategory.obj L) ⊗[R]^L[
                p.asIdeal.ResidueField]).IsGE n) :
    ∀ q : PrimeSpectrum (MvPolynomial (Fin d) R),
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero (primeResidueFieldDerivedHomology q L i) := by
  let P := MvPolynomial (Fin d) R
  intro q
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R P) q
  let qbar : PrimeSpectrum (p.asIdeal.Fiber P) :=
    PrimeSpectrum.preimageEquivFiber R P p ⟨q, rfl⟩
  let Kp : DerivedCategory (ModuleCat (p.asIdeal.Fiber P)) :=
    (derivedTensorWithAlgebra (algebraMap R (p.asIdeal.Fiber P))).obj
      ((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L)
  rcases hfibers p with ⟨n, hn⟩
  have hKpPerfect : Kp.IsPerfect := by
    -- Proof comment: the previous helper turns the chosen lower bound on the `κ(𝔭)`-fiber into
    -- perfectness of the canonical fiber object over `κ(𝔭) ⊗[R] P`.
    simpa [P, p, Kp] using
      isPerfect_mvPolynomial_fiber_of_isPseudoCoherent_of_base_bound
        (R := R) (d := d) L hLpc p hn
  have hLocalizationPerfect :
      (Kp ⊗[p.asIdeal.Fiber P]^L[Localization.AtPrime qbar.asIdeal]).IsPerfect := by
    -- Proof comment: perfect complexes stay perfect after localizing at the prime `qbar`.
    exact isPerfect_localizationAtPrime_of_isPerfect (K := Kp) hKpPerfect qbar
  rcases
      eventually_isZero_primeResidueFieldDerivedHomology_of_isPerfect_localizationAtPrime
        (K := Kp) qbar hLocalizationPerfect with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro i hi
  have hqbarZero : IsZero (primeResidueFieldDerivedHomology qbar Kp i) := ha i hi
  -- Proof comment: the comparison from Lemma `15.78.5` transports vanishing at the fiber prime
  -- `qbar` back to the original prime `q`.
  exact
    (primeResidueFieldDerivedHomology_isZero_iff_fiber_residueFieldHomology_isZero
      (A := R) (B := P) L q i).2 <| by
        simpa [P, p, qbar, Kp, primeResidueFieldDerivedHomology] using hqbarZero

/-- Helper for Lemma 15.84.10: after passing to a surjective polynomial presentation, the
`R`-linear residue-field fiber bound is unchanged. -/
lemma presentation_primeResidueField_bound_of_isGE
    {d : ℕ} (α : MvPolynomial (Fin d) R →ₐ[R] A) (K : DModA)
    (p : PrimeSpectrum R) {n : ℤ}
    (hκ :
      (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⊗[R]^L[
        p.asIdeal.ResidueField]).IsGE n) :
    let P := MvPolynomial (Fin d) R
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' rfl
    let L : DerivedCategory (ModuleCat P) :=
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)
    (((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) ⊗[R]^L[
      p.asIdeal.ResidueField]).IsGE n := by
  let P := MvPolynomial (Fin d) R
  let _ : Algebra P A := α.toAlgebra
  let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' rfl
  let L : DerivedCategory (ModuleCat P) :=
    ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)
  -- Proof comment: after choosing the polynomial presentation, forgetting further to `R`
  -- still yields the original restricted `R`-complex underlying `K`.
  simpa [L, P] using hκ

/-- Lemma 15.84.10: let `R → A` be flat and of finite presentation, and let `K ∈ D(A)` be
pseudo-coherent. Then `K` is `R`-perfect if and only if `K` is bounded below and, for every prime
ideal `𝔭 ⊂ R`, the derived fiber `K ⊗_R^{\mathbf L} κ(𝔭)` is bounded below. -/
@[stacks 0GHJ]
theorem isPerfectOver_iff_boundedBelow_and_primeResidueFields_boundedBelow
    (K : DModA) (hK : K.IsPseudoCoherent) :
    DerivedCategory.IsPerfectOver R K ↔
      (∃ n : ℤ, K.IsGE n) ∧
        ∀ p : PrimeSpectrum R,
          ∃ n : ℤ,
            (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⊗[R]^L[
              p.asIdeal.ResidueField]).IsGE n := by
  constructor
  · intro hPerfectOver
    rcases exists_isGE_of_isPerfectOver (R := R) (A := A) K hPerfectOver with ⟨n, hKn⟩
    refine ⟨⟨n, hKn⟩, ?_⟩
    intro p
    -- Proof comment: after extracting finite Tor dimension from `hPerfectOver`, the residue-field
    -- fiber bound is exactly the dedicated helper above.
    exact
      exists_isGE_primeResidueField_of_hasFiniteTorDimension
        (R := R) (A := A) K
        (hasFiniteTorDimension_of_isPerfectOver (R := R) (A := A) K hPerfectOver) p
  · rintro ⟨hboundedBelow, hfibers⟩
    rcases hboundedBelow with ⟨n, hKn⟩
    obtain ⟨d, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'').1
        (inferInstance : Algebra.FiniteType R A)
    let P := MvPolynomial (Fin d) R
    letI : Algebra P A := α.toAlgebra
    letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' rfl
    let L : DerivedCategory (ModuleCat P) :=
      ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K)
    have hα' : Function.Surjective (algebraMap P A) := by
      simpa [P] using hα
    have hLpc : L.IsPseudoCoherent := by
      -- Proof comment: Lemma `15.83.8` is the source-faithful presentation bridge from `A` back
      -- to the polynomial presentation ring `P`.
      let hTFAE :=
        isPseudoCoherent_tfae_of_surjective_of_flat_of_finitePresentation
          (R := R) (B := P) (A := A) K hα'
      exact (hTFAE.out 0 3).mp hK
    have hLge : L.IsGE n := by
      -- Proof comment: the global lower bound survives the presentation restriction because
      -- restriction of scalars is exact.
      exact restrictScalars_isGE_of_isGE α.toRingHom K hKn
    have hPolynomialTFAE :=
      perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE
        (R := P) L hLpc ⟨n, hLge⟩
    have hLfibers :
        ∀ p : PrimeSpectrum R,
          ∃ n : ℤ,
          (((ModuleCat.restrictScalars (algebraMap R P)).mapDerivedCategory.obj L) ⊗[R]^L[
              p.asIdeal.ResidueField]).IsGE n := by
      intro p
      rcases hfibers p with ⟨m, hm⟩
      -- Route correction: keep the source-faithful polynomial-presentation reduction and package
      -- the fiber-bound transfer as a single restriction-of-scalars helper.
      exact
        ⟨m,
          presentation_primeResidueField_bound_of_isGE
            (R := R) (A := A) (d := d) α K p hm⟩
    have hClause4 :
        ∀ q : PrimeSpectrum P,
          ∃ a : ℤ, ∀ i : ℤ, i < a →
            IsZero (primeResidueFieldDerivedHomology q L i) := by
      -- Proof comment: the polynomial-fiber helper now supplies clause `(4)` of the TFAE.
      exact
        eventually_isZero_primeResidueFieldDerivedHomology_of_mvPolynomial_fiber_perfect
          (R := R) (d := d) L hLpc hLfibers
    have hLPerfect : L.IsPerfect := by
      -- Proof comment: once clause `(4)` is available, the polynomial TFAE returns perfectness
      -- of `L` itself.
      exact (hPolynomialTFAE.out 3 0).mp hClause4
    have hLPerfectOver : DerivedCategory.IsPerfectOver R L := by
      -- Proof comment: absolute perfectness over the presentation ring implies relative
      -- perfectness over the original base ring `R`.
      exact isPerfectOver_of_isPerfect (R := R) (A := P) L hLPerfect
    -- Proof comment: the surjective presentation comparison identifies relative perfectness of
    -- `L` with that of the original complex `K`.
    exact
      (isPerfectOver_iff_restrictScalars_of_surjective_of_flat_of_finitePresentation
        (R := R) (A := A) (P := P) hα' K).1 hLPerfectOver

end

end CategoryTheory
