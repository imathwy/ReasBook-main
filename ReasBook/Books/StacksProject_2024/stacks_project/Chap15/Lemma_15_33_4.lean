import Mathlib
import StacksProject_2024.Chap10.Lemma_10_136_12
import StacksProject_2024.Chap15.Lemma_15_28_6
import StacksProject_2024.Chap15.Lemma_15_30_2
import StacksProject_2024.Chap15.Lemma_15_30_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open MonoidalCategory
open RingTheory Sequence
open ModuleCat
open scoped KoszulComplex
open scoped TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

/- Domain-style sampling:
- primary domain: explicit polynomial presentations of relative global complete intersections and
  their Koszul complexes in commutative algebra;
- sampled owner declarations:
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.naive`,
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.IsRegular.isKoszulRegularOn`;
- best owner abstraction: for the explicit quotient by the displayed relations `f`, the source-
  facing hypothesis should be the naive presentation-level predicate
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`; the conclusion already uses the
  chapter owner `IsKoszulRegularSequence`;
- primitive vs. derived: the primitive data are the relations `f`; the intrinsic existential class
  `Algebra.IsRelativeGlobalCompleteIntersection R _` is derived bridge data that forgets which
  presentation witnesses the complete-intersection condition, so it is too coarse for this item.

Source/core/bridge triage:
- `source-facing`: the theorem about the specific relations `f₁, …, f_c` in the displayed
  polynomial quotient;
- `core/canonical`: the naive presentation of that quotient together with its presentation-level
  relative-global-complete-intersection predicate, and the owner predicate
  `RingTheory.Sequence.IsKoszulRegularSequence`;
- `bridge/view`: Lemma `10.136.12` for localized regularity of the displayed relations and Lemma
  `15.30.2` upgrading regular sequences to Koszul-regularity.
-/
variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))
local notation "PolynomialRing" => MvPolynomial (Fin n) R

/-- Helper for Lemma 15.33.4: every homology module of the Koszul complex on the relations is
supported on the zero locus of the presentation ideal. -/
private theorem koszul_homology_support_subset_presented_zeroLocus
    (i : ℕ) :
    Module.support PolynomialRing ((K^•(f)).homology i) ⊆
      PrimeSpectrum.zeroLocus (PresentedIdeal : Set PolynomialRing) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp
  have hx_ann :
      x ∈ Module.annihilator PolynomialRing ((K^•(f)).homology i) :=
    ideal_span_le_annihilator_koszulComplex_homology (f := f) i hx
  have hxm : x • m = 0 :=
    (Module.mem_annihilator.mp hx_ann) m
  exact hm ((Submodule.mem_annihilator_span_singleton _ _).mpr hxm)

/-- Helper for Lemma 15.33.4: at a prime containing the presentation ideal, the localized
relations are Koszul-regular on the localized polynomial ring. -/
private theorem localized_relations_isKoszulRegularOn_of_mem_zeroLocus
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    {p : PrimeSpectrum PolynomialRing} (hp : PresentedIdeal ≤ p.asIdeal) :
    RingTheory.Sequence.IsKoszulRegularOn (Localization.AtPrime p.asIdeal)
      (List.ofFn (fun j ↦ algebraMap PolynomialRing (Localization.AtPrime p.asIdeal) (f j))).get := by
  let q : PrimeSpectrum PresentedAlgebra :=
    (Ideal.span (Set.range f)).primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p, hp⟩
  have hcomap :
      PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q = p := by
    exact congrArg Subtype.val
      ((Ideal.span (Set.range f)).primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply
        ⟨p, hp⟩)
  have hregular :
      Sequence.IsRegular (Localization.AtPrime p.asIdeal)
        (List.ofFn (fun j ↦ algebraMap PolynomialRing (Localization.AtPrime p.asIdeal) (f j))) := by
    -- The relative-GCI hypothesis gives regularity at the quotient prime, and the chosen `q`
    -- has comap exactly `p`, so the target local ring is definitionally the requested one.
    rw [← hcomap]
    simpa [q] using
      (Algebra.relativeGCI_localized_relations_isRegular (f := f) hP q)
  -- Lemma `15.30.2` upgrades local regularity to local Koszul-regularity.
  exact RingTheory.Sequence.IsRegular.isKoszulRegularOn
    (M := Localization.AtPrime p.asIdeal) hregular

/-- Helper for Lemma 15.33.4: tensoring the Koszul complex with the regular module over a ring
recovers the bare Koszul complex via the left unitor. -/
private noncomputable def koszul_tensor_self_iso
    (A : Type u) [CommRing A] {r : ℕ} (s : Fin r → A) :
    ((tensorLeft (ModuleCat.of A A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (K^•(s)) ≅
      K^•(s) :=
  (NatIso.mapHomologicalComplex
    (MonoidalCategory.leftUnitorNatIso (ModuleCat A))
    (ComplexShape.down ℕ)).app (K^•(s))

/-- Helper for Lemma 15.33.4: the localized bare Koszul complex on the relations agrees with
scalar extension of the global bare Koszul complex. -/
private noncomputable def localized_koszul_complex_iso_extendScalars
    {p : PrimeSpectrum PolynomialRing} :
    K^•(fun j ↦ algebraMap PolynomialRing (Localization.AtPrime p.asIdeal) (f j)) ≅
      ((ModuleCat.extendScalars
          (algebraMap PolynomialRing (Localization.AtPrime p.asIdeal))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (K^•(f)) :=
  -- First replace the bare local Koszul complex by the tensor model over the localized ring.
  (koszul_tensor_self_iso (Localization.AtPrime p.asIdeal)
      (fun j ↦ algebraMap PolynomialRing (Localization.AtPrime p.asIdeal) (f j))).symm ≪≫
    -- Then invoke the chapter's canonical base-change comparison for tensor Koszul complexes.
    (RingTheory.Sequence.tensor_koszul_complex_image_iso_extendScalars
      (R := PolynomialRing) (S := Localization.AtPrime p.asIdeal)
      (M := PolynomialRing) (N := Localization.AtPrime p.asIdeal)
      (f := Algebra.linearMap PolynomialRing (Localization.AtPrime p.asIdeal))
      (IsBaseChange.linearMap (R := PolynomialRing) (S := Localization.AtPrime p.asIdeal)) f) ≪≫
    -- Finally remove the global tensor coefficient by scalar-extending the left-unitor bridge.
    (((ModuleCat.extendScalars
        (algebraMap PolynomialRing (Localization.AtPrime p.asIdeal))).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapIso (koszul_tensor_self_iso PolynomialRing f))

/-- Helper for Lemma 15.33.4: exact scalar extension to the prime localization agrees with the
canonical localized module. -/
private theorem extendScalars_localizedModule_iso
    {p : PrimeSpectrum PolynomialRing} (M : ModuleCat PolynomialRing) :
    (ModuleCat.extendScalars
      (algebraMap PolynomialRing (Localization.AtPrime p.asIdeal))).obj M ≅
      ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := by
  let A := Localization.AtPrime p.asIdeal
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap PolynomialRing A)).obj (ModuleCat.of A A)) ≃ₗ[A]
        A :=
    { __ := AddEquiv.refl A
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsScalarTower PolynomialRing A
      ↑((ModuleCat.restrictScalars (algebraMap PolynomialRing A)).obj (ModuleCat.of A A)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eTensor :
      (ModuleCat.extendScalars (algebraMap PolynomialRing A)).obj M ≅
        ModuleCat.of A (A ⊗[PolynomialRing] M) := by
    -- Expand scalar extension into the honest tensor product over the polynomial ring.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl PolynomialRing ↑M)).toModuleIso
  let eLocal :
      ModuleCat.of A (A ⊗[PolynomialRing] M) ≅
        ModuleCat.of A (LocalizedModule.AtPrime p.asIdeal M) :=
    ((LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm).toModuleIso
  -- Compose the tensor-model rewrite with the canonical localization/tensor equivalence.
  exact eTensor ≪≫ eLocal

/-- Helper for Lemma 15.33.4: the homology of the scalar-extended global Koszul complex is the
localized global Koszul homology module. -/
private noncomputable def extendScalars_koszul_homology_iso_localizedModule
    {p : PrimeSpectrum PolynomialRing} (i : ℕ) :
    ((((ModuleCat.extendScalars
          (algebraMap PolynomialRing (Localization.AtPrime p.asIdeal))).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj
        (K^•(f))).homology i) ≅
      ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal ((K^•(f)).homology i)) :=
  let A := Localization.AtPrime p.asIdeal
  let F : ModuleCat.{u} PolynomialRing ⥤ ModuleCat.{u} A :=
    ModuleCat.extendScalars (algebraMap PolynomialRing A)
  let _ : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : F.PreservesHomology := inferInstance
  let K : HomologicalComplex (ModuleCat.{u} PolynomialRing) (ComplexShape.down ℕ) := K^•(f)
  -- First commute homology past exact scalar extension.
  (K.sc i).mapHomologyIso F ≪≫
    -- Then identify the scalar extension of the homology object with prime localization.
    extendScalars_localizedModule_iso
      (f := f) (p := p) (ModuleCat.of PolynomialRing ((K^•(f)).homology i))

/-- Helper for Lemma 15.33.4: after localizing at a prime over the presentation ideal, the
localized positive Koszul homology module vanishes. -/
private theorem localized_koszul_homology_isZero_of_mem_zeroLocus
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    {p : PrimeSpectrum PolynomialRing} (hp : PresentedIdeal ≤ p.asIdeal)
    (i : ℕ) (hi : 1 ≤ i) :
    IsZero (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal ((K^•(f)).homology i))) := by
  let A := Localization.AtPrime p.asIdeal
  have hKoszulLocal :
      RingTheory.Sequence.IsKoszulRegularOn A
        (List.ofFn (fun j ↦ algebraMap PolynomialRing A (f j))).get := by
    simpa using localized_relations_isKoszulRegularOn_of_mem_zeroLocus (f := f) hP hp
  have hlocal :
      IsZero
        ((K^•((List.ofFn (fun j ↦ algebraMap PolynomialRing A (f j))).get)).homology i) := by
    -- The local Koszul-regularity statement already gives the vanishing of positive homology for
    -- the bare local Koszul complex on the localized relations.
    exact
      (RingTheory.Sequence.isKoszulRegularSequence_iff
        ((List.ofFn (fun j ↦ algebraMap PolynomialRing A (f j))).get)).mp hKoszulLocal i hi
  have hbase :
      IsZero
        ((((ModuleCat.extendScalars (algebraMap PolynomialRing A)).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
            (K^•(f))).homology i) := by
    -- Transport the local vanishing along the source-faithful base-change comparison of bare
    -- Koszul complexes.
    exact IsZero.of_iso hlocal
      (HomologicalComplex.homologyMapIso
        (localized_koszul_complex_iso_extendScalars (f := f) (p := p)) i)
  -- Rewrite scalar-extended homology as the usual localized homology module.
  exact IsZero.of_iso hbase
    (extendScalars_koszul_homology_iso_localizedModule (f := f) (p := p) i)

-- Proof sketch: by Lemma `10.136.12`, every localization of the displayed presentation at a prime
-- of `PresentedAlgebra` makes the localized relations regular. Lemma `15.30.2` upgrades each such
-- localized regular sequence to localized Koszul-regularity, and the local vanishing of positive
-- Koszul homology descends back to the global Koszul complex on `f`.
/-- Lemma 15.33.4: if the quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete
intersection over `R`, then the defining equations `f₁, …, f_c` form a Koszul-regular sequence in
`R[x₁, …, xₙ]`. -/
theorem relativeGCI_relations_isKoszulRegularSequence
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation) :
    IsKoszulRegularSequence f := by
  rw [RingTheory.Sequence.isKoszulRegularSequence_iff]
  intro i hi
  have hsupport :
      Module.support PolynomialRing ((K^•(f)).homology i) ⊆
        PrimeSpectrum.zeroLocus (PresentedIdeal : Set PolynomialRing) :=
    koszul_homology_support_subset_presented_zeroLocus (f := f) i
  have hsupport_empty :
      Module.support PolynomialRing ((K^•(f)).homology i) = ∅ := by
    apply Set.Subset.antisymm
    · intro p hp
      have hpzero : PresentedIdeal ≤ p.asIdeal := hsupport hp
      have hlocal :
          IsZero (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal ((K^•(f)).homology i))) :=
        localized_koszul_homology_isZero_of_mem_zeroLocus (f := f) hP hpzero i hi
      have hsub :
          Subsingleton (LocalizedModule.AtPrime p.asIdeal ((K^•(f)).homology i)) := by
        simpa [ModuleCat.isZero_iff_subsingleton] using hlocal
      have hpnontrivial :
          Nontrivial (LocalizedModule.AtPrime p.asIdeal ((K^•(f)).homology i)) :=
        Module.mem_support_iff.mp hp
      rcases hpnontrivial.exists_pair_ne with ⟨x, y, hxy⟩
      exact False.elim (hxy (Subsingleton.elim x y))
    · exact Set.empty_subset _
  -- Empty support means the positive homology module is zero.
  have hsub : Subsingleton ((K^•(f)).homology i) := by
    exact (Module.support_eq_empty_iff (R := PolynomialRing)
      (M := ((K^•(f)).homology i))).mp hsupport_empty
  simpa [ModuleCat.isZero_iff_subsingleton] using hsub

end Algebra
