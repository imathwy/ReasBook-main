import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_5_3
import stacks_proof.stacks_project.Chap10.Lemma_10_109_6
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_4
import stacks_proof.stacks_project.Chap15.Lemma_15_67_4
import stacks_proof.stacks_project.Chap15.Lemma_15_67_6
import stacks_proof.stacks_project.Chap15.Lemma_15_75_2

universe u

open CategoryTheory
open scoped DerivedTensorProduct

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R]

namespace ModuleCat

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/- The module-level perfectness owner is the degree-zero specialization of the derived owner
`DerivedCategory.IsPerfect`. The canonical pseudo-coherent/finite-tor-dimension bridge normally
comes from Lemma `15.75.2`, so this file should now just specialize that earlier result. -/
/-- An `R`-module is perfect exactly when it is pseudo-coherent and has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (M : ModuleCat R) :
    M.IsPerfect ↔ M.IsPseudoCoherent ∧ ModuleHasFiniteTorDimension M := by
  -- Proof comment: this is exactly the degree-zero specialization of the derived-category
  -- characterization from Lemma `15.75.2`.
  simpa [ModuleCat.IsPerfect, ModuleCat.IsPseudoCoherent, ModuleHasFiniteTorDimension,
    ModuleCat.single0Functor] using
    (CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
      (R := R) (ModuleCat.single0Functor.obj M))

/- Domain-style sampling for Lemma 15.75.3:
- primary domain: perfect modules over a commutative ring, compared with bounded finite
  projective resolutions;
- sampled owner declarations:
  `ModuleCat.IsPerfect`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: the source-facing owner remains `M.IsPerfect`, while the concrete
  finite-resolution side should reuse the existing Chapter 10 owner
  `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms` rather than a new local wrapper;
- primitive vs. derived:
  primitive data are the module `M` and the chosen resolution length `d`;
  the finite-projective resolution itself is owned upstream in Chapter 10, and the perfectness
  predicate is owned by Definition `15.75.1`;
- source/core/bridge triage:
  `source-facing`: the equivalence below;
  `core/canonical`: `ModuleCat.IsPerfect` and
    `HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`;
  `bridge/view`: Chapter 10's projective-dimension interface sitting behind the proof.

This file should therefore keep the textbook equivalence, but phrase it directly in terms of the
existing owners instead of introducing any parallel resolution packaging.
-/

-- Proof sketch: identify perfect modules with pseudo-coherent modules of finite tor dimension via
-- Lemma `15.75.2`; then use the finite-free resolution description of pseudo-coherence together
-- with the truncation argument from the text to replace the leftmost sufficiently high syzygy by a
-- finite projective module, producing a finite projective resolution. Conversely, a finite
-- projective resolution should give a bounded finite-projective representative of `M[0]`.
/-- Helper for Lemma 15.75.3: the degree-zero single complex on a finite projective module is a
bounded finite-projective complex. -/
private theorem finiteProjectiveModule_single_isBoundedFiniteProjective
    (M : FiniteProjectiveModuleCat R) :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj) := by
  -- Proof comment: the single complex is supported in degree `0`, so outside degree `0` its terms
  -- are zero and hence still finite and projective.
  refine ⟨⟨0, 0, ?_, ?_⟩, ?_, ?_⟩
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).IsStrictlyGE (0 : ℤ))
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).IsStrictlyLE (0 : ℤ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      -- Proof comment: in degree `0`, the single complex literally recovers `M`.
      letI : Module.Finite R M.obj := M.property.1
      simpa using
        (Module.Finite.equiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M.obj).toLinearEquiv.symm)
    · let E : CochainComplex (ModuleCat R) ℤ :=
        (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj
      let hzero := by
        simpa [E] using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M.obj i hi)
      -- Proof comment: every other degree is zero, so finite generation is immediate.
      letI : Subsingleton ↥(E.X i) := ModuleCat.subsingleton_of_isZero hzero
      let e : ModuleCat.of R PUnit ≅ E.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
  · intro i
    by_cases hi : i = 0
    · subst hi
      -- Proof comment: the degree `0` term is identified with the given finite projective module.
      letI : Module.Projective R M.obj := M.property.2
      simpa using
        (Module.Projective.of_equiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M.obj).toLinearEquiv.symm)
    · let E : CochainComplex (ModuleCat R) ℤ :=
        (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj
      let hzero := by
        simpa [E] using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M.obj i hi)
      -- Proof comment: every other degree is zero, and the zero module is projective.
      letI : Subsingleton ↥(E.X i) := ModuleCat.subsingleton_of_isZero hzero
      letI : Module.Free R ↥(E.X i) := Module.Free.of_subsingleton (R := R) (N := ↥(E.X i))
      exact Module.Projective.of_free

/-- Helper for Lemma 15.75.3: a finite projective module is perfect when viewed in degree `0`. -/
private theorem finiteProjectiveModule_single_isPerfect
    (M : FiniteProjectiveModuleCat R) :
    M.obj.IsPerfect := by
  -- Proof comment: witness perfectness by the literal single complex concentrated in degree `0`.
  refine ⟨(CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj, ?_, ?_⟩
  · simpa [ModuleCat.IsPerfect, ModuleCat.single0Functor]
      using (Iso.refl ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj))
  · simpa using finiteProjectiveModule_single_isBoundedFiniteProjective (R := R) M

/-- Helper for Lemma 15.75.3: finite tor dimension gives a natural-number lower tor-amplitude
cutoff for the degree-zero complex of a module. -/
private lemma hasTorAmplitudeGE_nat_of_moduleHasFiniteTorDimension
    (M : ModuleCat R) (hM : ModuleHasFiniteTorDimension M) :
    ∃ d : ℕ, HasTorAmplitudeGE (ModuleCat.single0Functor.obj M) (-(d : ℤ)) := by
  rcases hM with ⟨a, b, hAmp⟩
  refine ⟨Int.natAbs a, ?_⟩
  -- Proof comment: lowering the left endpoint only weakens tor-amplitude, and `-natAbs a ≤ a`.
  rw [hasTorAmplitudeGE_iff]
  intro N i hi
  exact hAmp N i (by
    intro hmem
    have : a ≤ i := hmem.1
    omega)

/-- Helper for Lemma 15.75.3: tensoring a nonpositive derived module with a degree-zero module
stays nonpositive. -/
private lemma tensor_single_isLE_zero_of_isLE_zero
    (K : DerivedCategory (ModuleCat R)) (hK : K.IsLE 0) (N : ModuleCat R) :
    (K ⊗[R]^L (ModuleCat.single0Functor.obj N)).IsLE 0 := by
  -- Proof comment: replace `K` by a strict `≤ 0` cochain representative, where positive
  -- homology of the tensor complex vanishes because the positive terms themselves vanish.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  letI : K.IsLE 0 := hK
  obtain ⟨L, hLle, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K 0
  letI : L.IsStrictlyLE 0 := hLle
  let Tsingle : CochainComplex (ModuleCat R) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N
  have hTensorTermZero :
      IsZero
        ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).X i) := by
    -- Proof comment: right tensoring preserves the vanishing of the positive degree-`i` term.
    change IsZero (((CategoryTheory.MonoidalCategory.tensorRight N).obj (L.X i)))
    exact CategoryTheory.Functor.map_isZero
      (CategoryTheory.MonoidalCategory.tensorRight N)
      (L.isZero_of_isStrictlyLE 0 i hi)
  have hOrdinaryHomologyZero :
      IsZero ((HomologicalComplex.tensorObj L Tsingle).homology i) := by
    let eSc := tensor_single0_shortComplex_iso (R := R) L N i
    have hMappedHomologyZero :
        IsZero
          ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).sc i).homology := by
      -- Proof comment: with zero middle term, the short complex computing degree-`i` homology is
      -- exact.
      exact
        ShortComplex.isZero_homology_of_isZero_X₂
          (S := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).sc i)
          (by simpa [HomologicalComplex.sc] using hTensorTermZero)
    exact (ShortComplex.homologyMapIso eSc).isZero_iff.2 hMappedHomologyZero
  have hRepresentedHomologyZero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((DerivedCategory.Q.obj L) ⊗[R]^L (ModuleCat.single0Functor.obj N))) := by
    -- Proof comment: compare ordinary tensor-complex homology with derived tensor homology.
    exact
      hOrdinaryHomologyZero.of_iso
        (tensorObj_single0_homology_iso_derivedTensor (R := R) L i N)
  -- Proof comment: transport the vanishing statement back across the chosen strict representative
  -- of `K`.
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedTensorProduct (ModuleCat.single0Functor.obj N)).mapIso eL)).isZero_iff.2
      hRepresentedHomologyZero

/-- Helper for Lemma 15.75.3: in the degree-zero single chain complex, the incoming differential
vanishes after identifying the zeroth term with the underlying module. -/
private theorem single0_objXSelf_comp_d_eq_zero
    (M : ModuleCat R) :
    ((ChainComplex.single₀ (ModuleCat R)).obj M).d 1 0 ≫
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom = 0 := by
  -- Proof comment: the single complex has no nonzero degree-`1` term, so its first differential
  -- vanishes.
  rw [HomologicalComplex.single_obj_d]
  simp [ChainComplex.single₀ObjXSelf]
  rfl

/-- Helper for Lemma 15.75.3: on the degree-zero single chain complex, the canonical map from
zeroth opcycles to the module is the descended degree-zero term map. -/
private theorem single0_opcycles_self_inv_eq_descOpcycles
    (M : ModuleCat R) :
    (HomologicalComplex.singleObjOpcyclesSelfIso
      (ComplexShape.down ℕ) (0 : ℕ) M).inv =
    ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom
      1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
  -- Proof comment: both maps out of the degree-zero opcycles are characterized by the same
  -- composite with `pOpcycles`.
  apply (cancel_epi (((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0)).1
  calc
    ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        (HomologicalComplex.singleObjOpcyclesSelfIso
          (ComplexShape.down ℕ) (0 : ℕ) M).inv =
      (HomologicalComplex.singleObjXSelf
        (ComplexShape.down ℕ) (0 : ℕ) M).hom := by
          simpa [ChainComplex.single₀ObjXSelf] using
            (HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv
              (c := ComplexShape.down ℕ) (j := (0 : ℕ)) (A := M))
    _ =
      ((ChainComplex.single₀ (ModuleCat R)).obj M).pOpcycles 0 ≫
        ((ChainComplex.single₀ (ModuleCat R)).obj M).descOpcycles
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) (0 : ℕ) M).hom
          1 (by simp) (single0_objXSelf_comp_d_eq_zero (R := R) M) := by
            symm
            simpa using
              (HomologicalComplex.p_descOpcycles
                (K := (ChainComplex.single₀ (ModuleCat R)).obj M)
                (i := (0 : ℕ))
                (k := (HomologicalComplex.singleObjXSelf
                  (ComplexShape.down ℕ) (0 : ℕ) M).hom)
                (j := 1)
                (hj := by simp)
                (hk := single0_objXSelf_comp_d_eq_zero (R := R) M))

/-- Helper for Lemma 15.75.3: the augmentation of a finite free resolution is surjective and
exact at degree `0`. -/
private theorem chosen_resolution_augmentation_exact
    {M : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    {π : F ⟶ moduleSingle[R] M}
    (hπ : ChainComplex.IsFiniteFreeResolution π) :
    Function.Surjective (π.f 0).hom ∧ Function.Exact (F.d 1 0).hom (π.f 0).hom := by
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  let singleX :
      ((moduleSingle[R] M).X 0 ≅ ModuleCat.of R M) :=
    HomologicalComplex.singleObjXSelf
      (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)
  have hcomp_zero :
      F.d 1 0 ≫ (π.f 0 ≫ singleX.hom) = 0 := by
    -- Proof comment: the chain-map identity lands in the zero differential of the degree-zero
    -- single complex.
    simpa [Category.assoc, single0_objXSelf_comp_d_eq_zero (R := R) (ModuleCat.of R M)] using
      congrArg (fun f ↦ f ≫ singleX.hom) (π.comm 1 0)
  let desc :
      F.opcycles 0 ⟶ ModuleCat.of R M :=
    F.descOpcycles (π.f 0 ≫ singleX.hom) 1 (by simp) hcomp_zero
  have hdesc_eq :
      desc =
        (ChainComplex.isoHomologyι₀ F).inv ≫
          HomologicalComplex.homologyMap π 0 ≫
            ((ChainComplex.isoHomologyι₀ (moduleSingle[R] M)) ≪≫
              HomologicalComplex.singleObjOpcyclesSelfIso
                (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).hom := by
    -- Route correction: rewrite the descended opcycles map through the quasi-isomorphism on
    -- `H₀`, then finish with the canonical `H₀(single₀ M) ≅ M` comparison.
    apply (cancel_epi (F.homologyι 0)).1
    calc
      F.homologyι 0 ≫ desc =
        F.homologyι 0 ≫
          HomologicalComplex.opcyclesMap π 0 ≫
            (HomologicalComplex.singleObjOpcyclesSelfIso
              (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).inv := by
              rw [single0_opcycles_self_inv_eq_descOpcycles (R := R) (ModuleCat.of R M)]
              simpa [desc, Category.assoc] using
                (HomologicalComplex.opcyclesMap_comp_descOpcycles
                  (K := F)
                  (L := moduleSingle[R] M)
                  (φ := π)
                  (i := (0 : ℕ))
                  (k := singleX.hom)
                  (j := 1)
                  (hj := by simp)
                  (hk := single0_objXSelf_comp_d_eq_zero (R := R) (ModuleCat.of R M)))
      _ =
        F.homologyι 0 ≫
          (ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              (ChainComplex.isoHomologyι₀ (moduleSingle[R] M)).hom ≫
                (HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).inv := by
                    rw [← Category.assoc]
                    simp [ChainComplex.isoHomologyι₀_inv_naturality, Category.assoc]
      _ =
        F.homologyι 0 ≫
          ((ChainComplex.isoHomologyι₀ F).inv ≫
            HomologicalComplex.homologyMap π 0 ≫
              ((ChainComplex.isoHomologyι₀ (moduleSingle[R] M)) ≪≫
                HomologicalComplex.singleObjOpcyclesSelfIso
                  (ComplexShape.down ℕ) (0 : ℕ) (ModuleCat.of R M)).hom) := by
                    simp [Category.assoc]
  have hdescIso : IsIso desc := by
    rw [hdesc_eq]
    infer_instance
  have hdesc_exact_epi :
      Function.Exact (F.d 1 0).hom ((π.f 0 ≫ singleX.hom).hom) ∧ Epi (π.f 0 ≫ singleX.hom) := by
    rw [ChainComplex.isIso_descOpcycles_iff] at hdescIso
    exact hdescIso
  constructor
  · -- Proof comment: surjectivity is unchanged after composing with the degree-zero
    -- identification.
    have hsurjComp : Function.Surjective ((π.f 0 ≫ singleX.hom).hom) :=
      (ModuleCat.epi_iff_surjective _).1 hdesc_exact_epi.2
    intro m
    rcases hsurjComp (singleX.hom.hom m) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply singleX.hom.hom.injective
    simpa [Category.assoc] using hx
  · -- Proof comment: exactness descends back across the degree-zero identification isomorphism.
    intro x hx
    have hxComp : ((π.f 0 ≫ singleX.hom).hom) x = 0 := by
      simpa [Category.assoc] using congrArg singleX.hom.hom hx
    rcases hdesc_exact_epi.1 x hxComp with ⟨y, rfl⟩
    exact ⟨y, rfl⟩

/-- Helper for Lemma 15.75.3: a pseudo-coherent module is finitely presented. -/
private theorem finitePresentation_of_isPseudoCoherent
    (M : ModuleCat R) (hMpc : M.IsPseudoCoherent) :
    Module.FinitePresentation R M := by
  rcases
      (moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution
        (R := R) M).1 hMpc with
    ⟨F, π, hπ⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  obtain ⟨hπsurj, hπexact⟩ :=
    chosen_resolution_augmentation_exact (R := R) (M := M) (F := F) (π := π) hπ
  let _ : Module.Finite R (F.X 1) :=
    ChainComplex.IsFiniteFreeResolution.finite (R := R) (π := π) 1
  let _ : Module.Finite R (F.X 0) :=
    ChainComplex.IsFiniteFreeResolution.finite (R := R) (π := π) 0
  let _ : Module.Projective R (F.X 0) := by
    let _ : Module.Free R (F.X 0) :=
      ChainComplex.IsFiniteFreeResolution.free (R := R) (π := π) 0
    infer_instance
  let _ : Module.FinitePresentation R (F.X 0) :=
    Module.finitePresentation_of_projective R (F.X 0)
  -- Proof comment: the first two terms of the finite free resolution give a finite presentation
  -- of `M`.
  exact Module.finitePresentation_of_surjective_of_exact
    (F.d 1 0).hom (π.f 0).hom hπsurj hπexact

/-- Helper for Lemma 15.75.3: a positive-length finite projective resolution packages into a
bounded finite-projective cochain complex quasi-isomorphic to the degree-zero single complex. -/
private theorem bounded_finiteProjective_complex_of_resolution_succ
    (M : ModuleCat R) {n : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M (n + 1)) :
    ∃ L : CochainComplex (ModuleCat R) ℤ,
      ∃ α : L ⟶ (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M,
        QuasiIso α ∧ CochainComplex.IsBoundedFiniteProjective L := by
  -- TODO(Lemma 15.75.3): follow the source route. Turn the explicit resolution
  -- `0 ⟶ F_{n+1} ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0` into the cochain complex `E^{-i} = Fᵢ`, define the
  -- augmentation `E ⟶ M[0]`, and check it is a quasi-isomorphism degreewise from the given
  -- exactness, surjectivity, and injectivity data.
  sorry

/-- Helper for Lemma 15.75.3: pseudo-coherence plus a sufficiently low tor-amplitude cutoff
produces a finite projective resolution with finite terms. -/
private theorem hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_pseudoCoherent_and_hasTorAmplitudeGE
    (M : ModuleCat R) (hMpc : M.IsPseudoCoherent) {d : ℕ}
    (hTorGE : HasTorAmplitudeGE (ModuleCat.single0Functor.obj M) (-(d : ℤ))) :
    HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := by
  cases d with
  | zero =>
      -- Proof comment: in length `0`, the source route reduces to proving that `M` is finitely
      -- presented and flat, hence finite projective.
      have hMtor0 : ModuleHasTorDimensionLE M 0 := by
        -- Proof comment: the lower tor-amplitude hypothesis handles negative degrees, while the
        -- tensor product with any degree-zero test module is automatically supported in degrees
        -- `≤ 0`.
        intro N i hi
        by_cases hneg : i < 0
        · rw [hasTorAmplitudeGE_iff] at hTorGE
          exact hTorGE N i hneg
        · have hpos : 0 < i := by
            have hi0 : i ≠ 0 := by
              intro hEq
              apply hi
              simpa [hEq]
            omega
          have hLE :
              ((ModuleCat.single0Functor.obj M) ⊗[R]^L (ModuleCat.single0Functor.obj N)).IsLE 0 :=
            tensor_single_isLE_zero_of_isLE_zero (R := R)
              (K := ModuleCat.single0Functor.obj M) inferInstance N
          rw [DerivedCategory.isLE_iff] at hLE
          exact hLE i hpos
      have hMflat : Module.Flat R M :=
        (ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R) (M := M)).1 hMtor0
      have hMfp : Module.FinitePresentation R M :=
        finitePresentation_of_isPseudoCoherent (R := R) M hMpc
      -- Proof comment: finite presentation plus flatness upgrades `M` to a finite projective
      -- module, exactly the length-zero resolution datum.
      rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff]
      let _ : Module.Flat R M := hMflat
      let _ : Module.FinitePresentation R M := hMfp
      exact ⟨Module.Flat.projective_of_finitePresentation (R := R) (M := M), inferInstance⟩
  | succ n =>
      -- Route correction: the remaining source-faithful work is the positive-length cutoff
      -- packaging, not the zero-length endpoint above.
      -- TODO(Lemma 15.75.3): choose a bounded-above finite-free model of `M[0]`, use the
      -- cutoff-flatness theorem of Lemma `15.67.2` at degree `-(n + 1)`, upgrade the cutoff
      -- cokernel to finite projective via Algebra Lemma `10.78.2`, and package the resulting
      -- finite exact sequence as the Chapter 10 resolution owner.
      sorry

/-- Helper for Lemma 15.75.3: an explicit finite projective resolution should imply perfectness of
the module. -/
lemma isPerfect_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat R) {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d) :
    M.IsPerfect := by
  -- Route correction: isolate the source-faithful higher-length bridge, but discharge the
  -- degree-zero endpoint now using the literal single-complex representative.
  cases d with
  | zero =>
      rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff] at hM
      let P : FiniteProjectiveModuleCat R := ⟨M, ⟨hM.2, hM.1⟩⟩
      -- Proof comment: the `d = 0` owner says exactly that `M` itself is finite projective.
      simpa [P] using finiteProjectiveModule_single_isPerfect (R := R) P
  | succ n =>
      -- Proof comment: delegate the source-faithful packaging of the higher-length resolution to
      -- the dedicated helper, then turn the resulting quasi-isomorphism into the required derived
      -- isomorphism.
      obtain ⟨L, α, hα, hL⟩ :=
        bounded_finiteProjective_complex_of_resolution_succ (R := R) M hM
      have hQα : IsIso (DerivedCategory.Q.map α) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) α).2 hα
      letI := hQα
      exact ⟨L, (asIso (DerivedCategory.Q.map α)).symm, hL⟩

/-- Lemma 15.75.3: an `R`-module is perfect if and only if there exists a finite resolution
`0 ⟶ F_d ⟶ ⋯ ⟶ F₁ ⟶ F₀ ⟶ M ⟶ 0` in which every `Fᵢ` is a finite projective `R`-module. -/
@[stacks 066Q]
theorem isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat R) :
    M.IsPerfect ↔ ∃ d : ℕ, HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d := by
  constructor
  · intro hM
    rcases (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (R := R) M).1 hM with
      ⟨hMpc, hMtor⟩
    obtain ⟨d, hTorGE⟩ :=
      hasTorAmplitudeGE_nat_of_moduleHasFiniteTorDimension (R := R) M hMtor
    -- Proof comment: the remaining source-faithful work is now isolated to the cutoff-to-
    -- resolution helper built from pseudo-coherence and the chosen lower tor-amplitude bound.
    exact ⟨d,
      hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_of_pseudoCoherent_and_hasTorAmplitudeGE
        (R := R) M hMpc hTorGE⟩
  · rintro ⟨d, hd⟩
    -- Proof comment: the reverse direction factors through the dedicated helper above so the
    -- remaining blocker stays isolated to one source-faithful bridge.
    exact isPerfect_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms (R := R) M hd

/-- Helper for Lemma 15.75.3: forgetting projectivity termwise turns a finite projective
resolution with finite terms into a finite flat resolution of the same length. -/
private theorem hasFiniteFlatResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
    (M : ModuleCat R) {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLEWithFiniteTerms M d) :
    ModuleCat.HasFiniteFlatResolutionLengthLE M d := by
  cases d with
  | zero =>
      rw [hasFiniteProjectiveResolutionLengthLEWithFiniteTerms_zero_iff] at hM
      -- Proof comment: in length `0`, projective modules are flat, so the flat-resolution owner
      -- reduces to the same endpoint module.
      letI : Module.Projective R M := hM.1
      exact (ModuleCat.hasFiniteFlatResolutionLengthLE_zero_iff (R := R) (M := M)).2
        (Module.Flat.of_projective (R := R) (M := M))
  | succ n =>
      rcases hM with ⟨P, δ, π, hπsurj, hExact₀, hExact, hInj⟩
      refine ⟨(fun i ↦ (P i).obj), ?_, δ, π, hπsurj, hExact₀, hExact, hInj⟩
      intro i
      -- Proof comment: each finite projective term is flat after forgetting projectivity.
      letI : Module.Projective R (P i).obj := (P i).property.2
      exact Module.Flat.of_projective (R := R) (M := (P i).obj)

-- Proof sketch: choose the finite projective resolution supplied by the previous equivalence and
-- forget the projective structure to obtain a finite flat resolution of the same length. Then use
-- the canonical tor-dimension/flat-resolution bridge from Lemma `15.67.6`.
/-- A perfect `R`-module has tor dimension at most some finite integer. -/
theorem exists_moduleHasTorDimensionLE_of_isPerfect
    (M : ModuleCat R) (hM : M.IsPerfect) :
    ∃ d : ℕ, ModuleHasTorDimensionLE M d := by
  rcases
      (isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms
        (R := R) M).1 hM with
    ⟨d, hd⟩
  refine ⟨d, ?_⟩
  -- Proof comment: forget projectivity termwise to obtain a finite flat resolution, then apply
  -- the Chapter `15.67` flat-resolution/tor-dimension bridge.
  exact ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE (M := M)
    (hasFiniteFlatResolutionLengthLE_of_hasFiniteProjectiveResolutionLengthLEWithFiniteTerms
      (R := R) M hd)

end ModuleCat

end
