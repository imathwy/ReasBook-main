import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap15.Lemma_15_69_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped DerivedExt

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "single₀" => (DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ) : ModuleCat B ⥤ DModB)
local notation "singleCpx₀" => (CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ))

/- Domain triage:
* primary domain: the naive cotangent complex `NL_{B/A}` in `D(B)` and its smooth/formally smooth
  Ext-vanishing criteria;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the source-facing Chapter 10 owner for `NL_{B/A}` in `D(B)`;
  - `Generators.self`, the canonical self-presentation `A[B] ↠ B`;
  - `Extension.naiveCotangentChainComplex`, the chapter owner for the two-term naive cotangent
    complex of a presentation;
  - `derivedExtToModuleFunctor`, the Chapter 15 owner for the degree-`1` derived `Ext`
    functorial test;
  - `Algebra.formallySmooth_tfae_presentation_section_conormal_sequence_projective`, the
    presentation-independent formal smoothness criterion.
* best owner abstraction: the primitive data for this remark are only the algebra map `A → B`,
  whose source-facing derived owner is `NL_{B/A} = naiveCotangent A B`. The chosen
  self-presentation and its two-term representative are bridge data internal to that owner. The
  smoothness and formal smoothness criteria are derived API and should be stated for `NL_{B/A}`,
  using the canonical vanishing condition `IsZero (derivedExtToModuleFunctor (naiveCotangentObject
  A B) 1)` rather than a local wrapper predicate, and not for its raw representative.
* layer triage:
  - `source-facing`: the criterion in terms of `Ext^1_B(NL_{B/A}, N)`;
  - `core/canonical`: `naiveCotangent A B`;
  - `bridge/view`: the derived-category realization
    `DerivedCategory.Q.obj
      (((Generators.self A B).toExtension.naiveCotangentChainComplex).extend embeddingDownNat)`.

Primitive data are only the algebra map and the canonical owner `NL_{B/A}`. The derived `Ext`
vanishing condition and the smooth/formally smooth criteria are already owned upstream and are
reused directly here. -/

/-- Helper for Remark 15.85.2: all higher terms of the self-presentation naive cotangent chain
complex vanish. -/
lemma naiveCotangentChainComplex_X_succ_succ_isZero
    (n : ℕ) :
    IsZero ((naiveCotangent A B).X (n + 2)) := by
  -- Proof comment: `NL_{B/A}` is literally built as a two-term chain complex, so every term in
  -- degrees `≥ 2` is canonically the zero module.
  let E : Algebra.Extension A B := (Generators.self A B).toExtension
  let succZero :
      ∀ {X₀ X₁ : ModuleCat B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of B PUnit, 0, by simp⟩
  let C := E.naiveCotangentChainComplex
  have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of B PUnit := rfl
  have hX : C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
    simpa [C, Algebra.naiveCotangent, Algebra.Extension.naiveCotangentChainComplex] using
      (ChainComplex.mk'XIso
        (ModuleCat.of B E.CotangentSpace)
        (ModuleCat.of B (ULift E.Cotangent))
        (ModuleCat.ofHom (E.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
        succZero n)
  exact
    IsZero.of_iso
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit))
      (hX ≪≫ eqToIso hs)

/-- Helper for Remark 15.85.2: the canonical cochain model of `NL_{B/A}` is supported in degrees
`≥ -1`. -/
lemma naiveCotangentCochain_isStrictlyGE_negOne :
    CochainComplex.IsStrictlyGE
      ((naiveCotangent A B).extend embeddingDownNat)
      (-1) := by
  -- Proof comment: extending from chain degree `j` to cochain degree `-j` leaves only degrees
  -- `0` and `-1`.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have hnonneg : 0 ≤ -i - 2 := by omega
  have hexists : ∃ n : ℕ, i = -((n + 2 : ℕ) : ℤ) := by
    refine ⟨Int.toNat (-i - 2), ?_⟩
    have htoNat : ((Int.toNat (-i - 2) : ℕ) : ℤ) = -i - 2 :=
      Int.toNat_of_nonneg hnonneg
    omega
  rcases hexists with ⟨n, rfl⟩
  exact
    (naiveCotangentChainComplex_X_succ_succ_isZero (A := A) (B := B) n).of_iso
      (show ((naiveCotangent A B).extend embeddingDownNat).X (-((n + 2 : ℕ) : ℤ)) ≅
          (naiveCotangent A B).X (n + 2) from
        (naiveCotangent A B).extendXIso
          embeddingDownNat
          (show embeddingDownNat.f (n + 2) = -((n + 2 : ℕ) : ℤ) by
            rfl))

/-- Helper for Remark 15.85.2: the canonical cochain model of `NL_{B/A}` is supported in degrees
`≤ 0`. -/
lemma naiveCotangentCochain_isStrictlyLE_zero :
    CochainComplex.IsStrictlyLE
      ((naiveCotangent A B).extend embeddingDownNat)
      0 := by
  -- Proof comment: positive cochain degrees do not occur in the extension of a chain complex on
  -- `ℕ`.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact
    (naiveCotangent A B).isZero_extend_X embeddingDownNat i fun j hij ↦ by
      change (-((j : ℕ) : ℤ)) = i at hij
      omega

/-- Helper for Remark 15.85.2: the naive cotangent object `NL_{B/A}` lies in `D(B)_{\ge -1}`. -/
lemma naiveCotangentObject_isGE_negOne :
    (naiveCotangentObject A B).IsGE (-1) := by
  -- Proof comment: the chosen representative is the canonical self-presentation two-term
  -- complex, so its cohomology vanishes below degree `-1`.
  rw [naiveCotangentObject, DerivedCategory.isGE_Q_obj_iff]
  letI :
      CochainComplex.IsStrictlyGE
        ((naiveCotangent A B).extend embeddingDownNat)
        (-1) :=
    naiveCotangentCochain_isStrictlyGE_negOne (A := A) (B := B)
  infer_instance

/-- Helper for Remark 15.85.2: the naive cotangent object `NL_{B/A}` lies in `D(B)_{\le 0}`. -/
lemma naiveCotangentObject_isLE_zero :
    (naiveCotangentObject A B).IsLE 0 := by
  -- Proof comment: the same self-presentation model has no positive-degree terms, hence no
  -- positive cohomology.
  rw [naiveCotangentObject, DerivedCategory.isLE_Q_obj_iff]
  letI :
      CochainComplex.IsStrictlyLE
        ((naiveCotangent A B).extend embeddingDownNat)
        0 :=
    naiveCotangentCochain_isStrictlyLE_zero (A := A) (B := B)
  infer_instance

/-- Helper for Remark 15.85.2: in degree `-1`, the cycles of a cochain complex are the kernel of
the outgoing differential. -/
private noncomputable def two_term_cycles_negOne_iso_kernel
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    P.cycles (-1) ≅ ModuleCat.of B (LinearMap.ker ((P.d (-1) 0).hom)) := by
  let hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
    simpa using (CochainComplex.prev ℤ (-1))
  let hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
    simpa using (CochainComplex.next ℤ (-1))
  let T : ShortComplex (ModuleCat B) := P.sc' (-2) (-1) 0
  let eShortKernel :
      T.cycles ≅ ModuleCat.of B (LinearMap.ker ((P.d (-1) 0).hom)) := by
    -- Proof comment: on the owner short complex, cycles are exactly the kernel of the outgoing
    -- differential.
    simpa [T, hnext] using
      (T.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer T.g)
  -- Proof comment: move the ambient cycle object to the owner short complex, then identify that
  -- short-complex cycle object with the concrete kernel module.
  exact (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext) ≪≫ eShortKernel

/-- Helper for Remark 15.85.2: the degree-`-1` cycles-to-kernel identification is characterized
by the ambient cycle inclusion. -/
private theorem two_term_cycles_negOne_iso_kernel_hom_comp_subtype
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (two_term_cycles_negOne_iso_kernel (B := B) (P := P)).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
        P.iCycles (-1) := by
  let hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
    simpa using (CochainComplex.prev ℤ (-1))
  let hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
    simpa using (CochainComplex.next ℤ (-1))
  let T : ShortComplex (ModuleCat B) := P.sc' (-2) (-1) 0
  -- Proof comment: compare both maps after rewriting through the owner short complex `T`,
  -- where `cyclesIsoKernel` and `kernelIsoKer` expose the concrete kernel inclusion.
  have hShort :
      (two_term_cycles_negOne_iso_kernel (B := B) (P := P)).hom ≫
          ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
        (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.iCycles := by
    let hKer :
        (ModuleCat.kernelIsoKer T.g).hom ≫
            ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
          kernel.ι T.g := by
      simpa [T] using ModuleCat.kernelIsoKer_hom_ker_subtype (f := T.g)
    have hComp :
        (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.cyclesIsoKernel.hom ≫
            (ModuleCat.kernelIsoKer T.g).hom ≫
              ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
          (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.cyclesIsoKernel.hom ≫
            kernel.ι T.g := by
      exact
        congrArg
          (fun k : kernel T.g ⟶ T.X₂ ↦
            (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.cyclesIsoKernel.hom ≫ k)
          hKer
    simpa [two_term_cycles_negOne_iso_kernel, T, Category.assoc,
      CategoryTheory.ShortComplex.cyclesIsoKernel] using hComp
  have hCycles :
      (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.iCycles = P.iCycles (-1) := by
    simpa [T] using
      P.cyclesIsoSc'_hom_iCycles (-2) (-1) 0 hprev hnext
  exact hShort.trans hCycles

/-- Helper for Remark 15.85.2: in a cochain complex supported in degrees `≥ -1`, the degree-`-1`
homology is the kernel of `d^{-1}`. -/
private noncomputable def two_term_homology_negOne_iso_kernel
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) [P.IsStrictlyGE (-1)] :
    P.homology (-1) ≅ ModuleCat.of B (LinearMap.ker ((P.d (-1) 0).hom)) := by
  have hzero_prev : P.d (-2) (-1) = 0 := by
    -- Proof comment: the predecessor term vanishes below the lower support bound.
    exact (P.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _
  let eHomology :
      P.homology (-1) ≅ P.cycles (-1) :=
    (P.isoHomologyπ (-2) (-1) (by simp) hzero_prev).symm
  -- Proof comment: first identify `H^{-1}` with cycles, then rewrite cycles as the concrete
  -- kernel of the only possible outgoing differential.
  exact eHomology ≪≫ two_term_cycles_negOne_iso_kernel (B := B) P

/-- Helper for Remark 15.85.2: in degree `0`, the opcycles of a cochain complex are the cokernel
of the incoming differential. -/
private noncomputable def two_term_opcycles_zero_iso_cokernel
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    P.opcycles 0 ≅ cokernel (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Proof comment: compare the owner opcycle cokernel with the categorical cokernel of `d^{-1}`.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (P.d (-1) 0))
      hOpcycles).symm

/-- Helper for Remark 15.85.2: the degree-`0` opcycles-to-cokernel identification is
characterized by the ambient quotient map `pOpcycles`. -/
private theorem pOpcycles_comp_two_term_opcycles_zero_iso_cokernel_hom
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    P.pOpcycles 0 ≫ (two_term_opcycles_zero_iso_cokernel (B := B) P).hom =
      cokernel.π (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Proof comment: both coforks present the same cokernel, so the comparison iso carries the
  -- owner quotient map `pOpcycles` to the categorical cokernel projection.
  simpa [two_term_opcycles_zero_iso_cokernel, hOpcycles] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      hOpcycles
      (cokernelIsCokernel (P.d (-1) 0))
      WalkingParallelPair.one

/-- Helper for Remark 15.85.2: in a cochain complex supported in degrees `≤ 0`, the degree-`0`
homology is the cokernel of `d^{-1}`. -/
private noncomputable def two_term_homology_zero_iso_cokernel
    (P : CochainComplex (ModuleCat.{max u v} B) ℤ) (hLE : P.IsStrictlyLE 0) :
    P.homology 0 ≅ cokernel (P.d (-1) 0) := by
  letI : P.IsStrictlyLE 0 := hLE
  have hzero_next : P.d 0 1 = 0 := by
    -- Proof comment: the target in degree `1` vanishes above the upper support bound.
    exact (P.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  let eHomology :
      P.homology 0 ≅ P.opcycles 0 :=
    P.isoHomologyι 0 1 (by simp) hzero_next
  -- Proof comment: first identify `H^0` with the degree-zero opcycles, then rewrite those
  -- opcycles as the categorical cokernel of `d^{-1}`.
  exact eHomology ≪≫ two_term_opcycles_zero_iso_cokernel (B := B) P

/-- Helper for Remark 15.85.2: the only differential of the self-presentation cochain model is
the owner cotangent map precomposed with the canonical `ULift` linear equivalence. -/
private theorem embeddingDownNat_zero :
    embeddingDownNat.f 0 = (0 : ℤ) := by
  simp

/-- Helper for Remark 15.85.2: the extension from chain to cochain degree sends `1` to `-1`. -/
private theorem embeddingDownNat_one :
    embeddingDownNat.f 1 = (-1 : ℤ) := by
  simp

/-- Helper for Remark 15.85.2: projective amplitude in a fixed interval is preserved by
isomorphism in the derived category. -/
private lemma hasProjectiveAmplitudeIn_iff_of_iso
    {K L : DModB} {a b : ℤ} (e : K ≅ L) :
    HasProjectiveAmplitudeIn K a b ↔ HasProjectiveAmplitudeIn L a b := by
  constructor
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    exact ⟨P, e.symm ≪≫ eP, hPge, hPle, hPproj⟩
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    exact ⟨P, e ≪≫ eP, hPge, hPle, hPproj⟩

/-- Helper for Remark 15.85.2: a projective `B`-module concentrated in degree `0` has
projective amplitude in `[0, 0]`. -/
private lemma single_zero_hasProjectiveAmplitude_of_projective
    (M : ModuleCat B) (hM : Projective M) :
    HasProjectiveAmplitudeIn ((single₀).obj M) 0 0 := by
  refine ⟨(singleCpx₀).obj M,
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M).symm,
    ?_, ?_, ?_⟩
  · -- Proof comment: the literal single complex is supported in degree `0`.
    simpa using
      (inferInstance : ((singleCpx₀).obj M).IsStrictlyGE (0 : ℤ))
  · -- Proof comment: the same single complex is also supported in degrees `≤ 0`.
    simpa using
      (inferInstance : ((singleCpx₀).obj M).IsStrictlyLE (0 : ℤ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      -- Proof comment: in degree `0`, the single complex is canonically the original module.
      exact
        Projective.of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).symm
          hM
    · let hzero :
        IsZero (((singleCpx₀).obj M).X i) := by
        simpa using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i hi)
      -- Proof comment: every other degree is zero, so its term is automatically projective.
      exact Projective.of_iso hzero.isoZero.symm (by infer_instance)

/-- Helper for Remark 15.85.2: degree `-1` of the extended self-presentation cochain model is the
original chain degree `1`. -/
private abbrev self_presentation_negOne_iso :
    ((show CpxB from (naiveCotangent A B).extend embeddingDownNat).X (-1)) ≅
      (naiveCotangent A B).X 1 :=
  (naiveCotangent A B).extendXIso embeddingDownNat (embeddingDownNat_one)

/-- Helper for Remark 15.85.2: degree `0` of the extended self-presentation cochain model is the
original chain degree `0`. -/
private abbrev self_presentation_zero_iso :
    ((show CpxB from (naiveCotangent A B).extend embeddingDownNat).X 0) ≅
      (naiveCotangent A B).X 0 :=
  (naiveCotangent A B).extendXIso embeddingDownNat (embeddingDownNat_zero)

/-- Helper for Remark 15.85.2: after identifying degrees `-1` and `0` with the original chain
degrees `1` and `0`, the extended differential is the owner cotangent map. -/
private theorem self_presentation_d_negOne_zero_hom :
    (show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0 =
      (self_presentation_negOne_iso (A := A) (B := B)).hom ≫
        ModuleCat.ofHom
          ((Generators.self A B).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) ≫
        (self_presentation_zero_iso (A := A) (B := B)).inv := by
  let eNeg := self_presentation_negOne_iso (A := A) (B := B)
  let eZero := self_presentation_zero_iso (A := A) (B := B)
  have htransport :
      eNeg.inv ≫ (show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0 ≫
          eZero.hom =
        (naiveCotangent A B).d 1 0 := by
    -- Proof comment: `extend_d_eq` rewrites the extended cochain differential to the original
    -- chain differential once the endpoint degree identifications are fixed.
    rw [HomologicalComplex.extend_d_eq
      (K := naiveCotangent A B) (e := embeddingDownNat)
      (i := 1) (j := 0) (i' := (-1 : ℤ)) (j' := (0 : ℤ))
      (embeddingDownNat_one) (embeddingDownNat_zero)]
    simp [eNeg, eZero]
  have hd10 :
      (naiveCotangent A B).d 1 0 =
        ModuleCat.ofHom
          ((Generators.self A B).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) :=
    by
      -- Proof comment: the self-presentation naive cotangent complex is a two-term chain complex
      -- with this single nonzero differential in degrees `1 → 0`.
      simpa [Algebra.naiveCotangent] using
        Algebra.Extension.naiveCotangentChainComplex_d_1_0
          ((Generators.self A B).toExtension)
  have hcomp :=
    congrArg (fun f ↦ eNeg.hom ≫ f ≫ eZero.inv) htransport
  calc
    (show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0 =
        eNeg.hom ≫ (naiveCotangent A B).d 1 0 ≫ eZero.inv := by
          simpa [eNeg, eZero, Category.assoc] using hcomp
    _ = eNeg.hom ≫
          ModuleCat.ofHom
            ((Generators.self A B).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) ≫
          eZero.inv := by
            rw [hd10]
            rfl

/-- Helper for Remark 15.85.2: the endpoint identifications form the comparison square required
for kernel and cokernel transport. -/
private theorem self_presentation_d_negOne_zero_comm :
    (show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0 ≫
        (self_presentation_zero_iso (A := A) (B := B)).hom =
      (self_presentation_negOne_iso (A := A) (B := B)).hom ≫
        (naiveCotangent A B).d 1 0 := by
  -- Proof comment: compose the already-normalized differential formula with the degree-zero
  -- identification and cancel the inverse/hom round trip of that endpoint isomorphism.
  calc
    (show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0 ≫
        (self_presentation_zero_iso (A := A) (B := B)).hom =
      (self_presentation_negOne_iso (A := A) (B := B)).hom ≫
        ModuleCat.ofHom
          ((Generators.self A B).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) := by
            rw [self_presentation_d_negOne_zero_hom (A := A) (B := B)]
            simp [Category.assoc]
    _ = (self_presentation_negOne_iso (A := A) (B := B)).hom ≫
        (naiveCotangent A B).d 1 0 := by
          simpa [Algebra.naiveCotangent] using
            congrArg
              (fun f ↦ (self_presentation_negOne_iso (A := A) (B := B)).hom ≫ f)
              (Algebra.Extension.naiveCotangentChainComplex_d_1_0
                ((Generators.self A B).toExtension))

/-- Helper for Remark 15.85.2: the degree-`1 → 0` differential in the self-presentation chain
model is exactly the owner cotangent map precomposed with the canonical `ULift` linear
equivalence. -/
private theorem self_presentation_chain_d_one_zero_hom :
    (naiveCotangent A B).d 1 0 =
      ModuleCat.ofHom
        ((Generators.self A B).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) :=
  by
    -- Proof comment: the self-presentation naive cotangent complex is definitionally the
    -- two-term owner chain complex attached to `Extension.cotangentComplex`.
    simpa [Algebra.naiveCotangent] using
      Algebra.Extension.naiveCotangentChainComplex_d_1_0
        ((Generators.self A B).toExtension)

/-- Helper for Remark 15.85.2: the normalized chain differential has the same kernel as the owner
cotangent map. -/
private noncomputable def self_presentation_chain_d_one_zero_kernel_iso_cotangentComplex_ker :
    ModuleCat.of B (LinearMap.ker (((naiveCotangent A B).d 1 0).hom)) ≅
      ModuleCat.of B (LinearMap.ker ((Generators.self A B).toExtension.cotangentComplex)) := by
  let E : Algebra.Extension A B := (Generators.self A B).toExtension
  let e : ULift E.Cotangent ≃ₗ[B] E.Cotangent := ULift.moduleEquiv
  have hd :
      LinearMap.ker (((naiveCotangent A B).d 1 0).hom) =
        LinearMap.ker (E.cotangentComplex.comp e.toLinearMap) := by
    -- Proof comment: first rewrite the chain differential to the owner `cotangentComplex`
    -- precomposed with the canonical `ULift` equivalence.
    simpa [E, e] using
      congrArg LinearMap.ker
        (congrArg ModuleCat.Hom.hom (self_presentation_chain_d_one_zero_hom (A := A) (B := B)))
  have hker_comp :
      Submodule.map e.symm.toLinearMap (LinearMap.ker E.cotangentComplex) =
        LinearMap.ker (E.cotangentComplex.comp e.toLinearMap) := by
    -- Proof comment: pulling back the kernel across a linear equivalence is the standard
    -- `map/comap` description of the kernel of a composite.
    calc
      Submodule.map e.symm.toLinearMap (LinearMap.ker E.cotangentComplex) =
          Submodule.comap e.toLinearMap (LinearMap.ker E.cotangentComplex) := by
            simpa using
              (Submodule.map_equiv_eq_comap_symm e.symm (LinearMap.ker E.cotangentComplex))
      _ = LinearMap.ker (E.cotangentComplex.comp e.toLinearMap) := by
            rw [LinearMap.ker_comp]
  let eMap :
      LinearMap.ker E.cotangentComplex ≃ₗ[B]
        Submodule.map e.symm.toLinearMap (LinearMap.ker E.cotangentComplex) :=
    (LinearMap.ker E.cotangentComplex).equivMapOfInjective e.symm.toLinearMap e.symm.injective
  -- Proof comment: identify the normalized kernel with the mapped owner kernel, then descend that
  -- mapped kernel back to the owner one using the inverse `ULift` equivalence.
  exact
    ((LinearEquiv.ofEq _ _ hd).trans
      ((LinearEquiv.ofEq _ _ hker_comp).symm.trans eMap.symm)).toModuleIso

/-- Helper for Remark 15.85.2: removing the `ULift` source equivalence does not change the
kernel of the self-presentation differential in degree `-1 → 0`. -/
private noncomputable def self_presentation_d_negOne_zero_kernel_iso_cotangentComplex_ker :
    ModuleCat.of B (LinearMap.ker
      (((show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0).hom)) ≅
      ModuleCat.of B (LinearMap.ker ((Generators.self A B).toExtension.cotangentComplex)) := by
  let P : CochainComplex (ModuleCat.{max u v} B) ℤ :=
    show CpxB from (naiveCotangent A B).extend embeddingDownNat
  let eKer :
      kernel (P.d (-1) 0) ≅ kernel ((naiveCotangent A B).d 1 0) :=
    kernel.mapIso
      (P.d (-1) 0)
      ((naiveCotangent A B).d 1 0)
      (self_presentation_negOne_iso (A := A) (B := B))
      (self_presentation_zero_iso (A := A) (B := B))
      (by
        -- Proof comment: the endpoint degree identifications turn the extended differential
        -- into the plain chain differential.
        simpa [P] using self_presentation_d_negOne_zero_comm (A := A) (B := B))
  -- Proof comment: move from categorical kernels to concrete kernel submodules on each side,
  -- then compose with the normalized chain-level kernel transport.
  exact
    (ModuleCat.kernelIsoKer (P.d (-1) 0)).symm ≪≫
      eKer ≪≫
      ModuleCat.kernelIsoKer ((naiveCotangent A B).d 1 0) ≪≫
      self_presentation_chain_d_one_zero_kernel_iso_cotangentComplex_ker (A := A) (B := B)

/-- Helper for Remark 15.85.2: exactness of the self-presentation conormal sequence identifies
the kernel of the owner cotangent map with `H₁(L_{B/A})`. -/
private noncomputable def self_presentation_cotangentComplex_ker_iso_h1Cotangent :
    ModuleCat.of B
      (LinearMap.ker ((Generators.self A B).toExtension.cotangentComplex)) ≅
      ModuleCat.of B (H1Cotangent A B) := by
  let E : Algebra.Extension A B := (Generators.self A B).toExtension
  have hRangeKer :
      LinearMap.range E.h1Cotangentι = LinearMap.ker E.cotangentComplex :=
    ((LinearMap.exact_iff).mp E.exact_hCotangentι_cotangentComplex).symm
  let toKer : E.H1Cotangent →ₗ[B] LinearMap.ker E.cotangentComplex :=
    LinearMap.codRestrict
      (LinearMap.ker E.cotangentComplex)
      E.h1Cotangentι
      (fun x ↦ by
        -- Proof comment: exactness of
        -- `H₁(L_{B/A}) → E.Cotangent → E.CotangentSpace`
        -- is precisely the statement that the image of `h1Cotangentι` lands in the kernel.
        change (E.cotangentComplex.comp E.h1Cotangentι) x = 0
        simpa [LinearMap.comp_apply] using
          LinearMap.congr_fun
            (Function.Exact.linearMap_comp_eq_zero E.exact_hCotangentι_cotangentComplex) x)
  have htoKer_injective : Function.Injective toKer := by
    intro x y hxy
    apply E.h1Cotangentι_injective
    exact congrArg Subtype.val hxy
  have htoKer_surjective : Function.Surjective toKer := by
    intro y
    have hy_range : y.1 ∈ LinearMap.range E.h1Cotangentι := by
      -- Proof comment: exactness rewrites the kernel of `E.cotangentComplex` as the range of
      -- `E.h1Cotangentι`, so every kernel element comes from cotangent homology.
      simpa [LinearMap.mem_ker, hRangeKer] using y.2
    rcases hy_range with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  let eKer :
      LinearMap.ker E.cotangentComplex ≃ₗ[B] E.H1Cotangent :=
    (LinearEquiv.ofBijective toKer ⟨htoKer_injective, htoKer_surjective⟩).symm
  -- Proof comment: after identifying the owner `H₁` with the global owner
  -- `H1Cotangent A B`, we obtain the desired kernel description.
  exact (eKer.trans (Generators.self A B).equivH1Cotangent).toModuleIso

/-- Helper for Remark 15.85.2: removing the `ULift` source equivalence does not change the
cokernel of the self-presentation differential in degree `-1 → 0`. -/
private noncomputable def self_presentation_chain_d_one_zero_cokernel_iso_cotangentComplex_cokernel
    :
    cokernel ((naiveCotangent A B).d 1 0) ≅
      cokernel (ModuleCat.ofHom ((Generators.self A B).toExtension.cotangentComplex)) := by
  let E : Algebra.Extension A B := (Generators.self A B).toExtension
  let e : ULift E.Cotangent ≃ₗ[B] E.Cotangent := ULift.moduleEquiv
  have hd :
      LinearMap.range (((naiveCotangent A B).d 1 0).hom) =
        LinearMap.range E.cotangentComplex := by
    -- Proof comment: precomposing with a surjective linear equivalence does not change the range.
    rw [self_presentation_chain_d_one_zero_hom]
    change LinearMap.range (E.cotangentComplex.comp e.toLinearMap) = LinearMap.range E.cotangentComplex
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro y ⟨x, rfl⟩
      rcases e.surjective x with ⟨x', rfl⟩
      exact ⟨x', rfl⟩
  -- Proof comment: identify both cokernels with quotients by their ranges and replace the
  -- normalized range by the owner range.
  exact
    (ModuleCat.cokernelIsoRangeQuotient ((naiveCotangent A B).d 1 0)).trans <|
      (Submodule.quotEquivOfEq
        (LinearMap.range (((naiveCotangent A B).d 1 0).hom))
        (LinearMap.range E.cotangentComplex)
        hd).toModuleIso.trans <|
          (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom E.cotangentComplex)).symm

/-- Helper for Remark 15.85.2: removing the endpoint transport leaves the same cokernel as the
normalized chain differential. -/
private noncomputable def self_presentation_d_negOne_zero_cokernel_iso_cotangentComplex_cokernel :
    cokernel ((show CpxB from (naiveCotangent A B).extend embeddingDownNat).d (-1) 0) ≅
      cokernel (ModuleCat.ofHom ((Generators.self A B).toExtension.cotangentComplex)) := by
  let P : CpxB := show CpxB from (naiveCotangent A B).extend embeddingDownNat
  let eCoker :
      cokernel (P.d (-1) 0) ≅ cokernel ((naiveCotangent A B).d 1 0) :=
    cokernel.mapIso
      (P.d (-1) 0)
      ((naiveCotangent A B).d 1 0)
      (self_presentation_negOne_iso (A := A) (B := B))
      (self_presentation_zero_iso (A := A) (B := B))
      (by
        -- Proof comment: the same endpoint comparison square identifies the two cokernels.
        simpa [P] using self_presentation_d_negOne_zero_comm (A := A) (B := B))
  -- Proof comment: once the endpoint transport is removed, the cokernel is exactly the one from
  -- the normalized chain differential, which was already compared to the owner cokernel.
  exact
    eCoker ≪≫
      self_presentation_chain_d_one_zero_cokernel_iso_cotangentComplex_cokernel
        (A := A) (B := B)

/-- Helper for Remark 15.85.2: exactness and surjectivity of the owner map
`E.CotangentSpace → Ω[B⁄A]` identify the cokernel of `E.cotangentComplex` with `Ω[B⁄A]`. -/
private noncomputable def self_presentation_cotangentComplex_cokernel_iso_kaehler :
    cokernel (ModuleCat.ofHom ((Generators.self A B).toExtension.cotangentComplex)) ≅
      ModuleCat.of B (ULift.{max u v, v} Ω[B⁄A]) := by
  let E : Algebra.Extension A B := (Generators.self A B).toExtension
  have hRangeKer :
      LinearMap.range E.cotangentComplex = LinearMap.ker E.toKaehler :=
    ((LinearMap.exact_iff).mp E.exact_cotangentComplex_toKaehler).symm
  let eQuot :
      (E.CotangentSpace ⧸ LinearMap.range E.cotangentComplex) ≃ₗ[B]
        ULift.{max u v, v} Ω[B⁄A] :=
    (Submodule.quotEquivOfEq
      (LinearMap.range E.cotangentComplex)
      (LinearMap.ker E.toKaehler)
      hRangeKer).trans
        ((E.toKaehler.quotKerEquivOfSurjective E.toKaehler_surjective).trans
          (ULift.moduleEquiv : ULift.{max u v, v} Ω[B⁄A] ≃ₗ[B] Ω[B⁄A]).symm)
  -- Proof comment: first identify the categorical cokernel with the quotient by
  -- `range(E.cotangentComplex)`, then replace that range by `ker(E.toKaehler)` and use the first
  -- isomorphism theorem for the surjective map `E.toKaehler`.
  exact
    (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom E.cotangentComplex)).trans
      eQuot.toModuleIso

/-- Helper for Remark 15.85.2: the degree-`-1` homology of `NL_{B/A}` is the owner first
cotangent homology `H1Cotangent A B`. -/
private noncomputable def naiveCotangentObject_homology_negOne_iso_h1Cotangent :
    ((H (-1)).obj (naiveCotangentObject A B)) ≅
      ModuleCat.of B (H1Cotangent A B) := by
  let P : CpxB := show CpxB from (naiveCotangent A B).extend embeddingDownNat
  letI :
      CochainComplex.IsStrictlyGE P (-1) :=
    by
      simpa [P] using naiveCotangentCochain_isStrictlyGE_negOne (A := A) (B := B)
  have eQ :
      ((H (-1)).obj (naiveCotangentObject A B)) ≅ P.homology (-1) := by
    -- Proof comment: `naiveCotangentObject A B` is represented by the canonical cochain model
    -- `P`, so derived homology agrees with the ordinary homology of that representative.
    simpa [naiveCotangentObject, P] using
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) (-1)).app P
  -- Proof comment: for the two-term self-presentation model, `H^{-1}` is the kernel of the
  -- unique differential, and that kernel is already identified with `H1Cotangent A B`.
  exact
    eQ ≪≫
      two_term_homology_negOne_iso_kernel (B := B) P ≪≫
      self_presentation_d_negOne_zero_kernel_iso_cotangentComplex_ker
        (A := A) (B := B) ≪≫
      self_presentation_cotangentComplex_ker_iso_h1Cotangent (A := A) (B := B)

/-- Helper for Remark 15.85.2: the degree-`0` homology of `NL_{B/A}` is the owner K\"ahler
differential module `Ω[B⁄A]`, expressed through the canonical `ULift` used by the owner API. -/
private noncomputable def naiveCotangentObject_homology_zero_iso_kaehler :
    ((H 0).obj (naiveCotangentObject A B)) ≅
      ModuleCat.of B (ULift.{max u v, v} Ω[B⁄A]) := by
  let P : CpxB := show CpxB from (naiveCotangent A B).extend embeddingDownNat
  have hLE : P.IsStrictlyLE 0 := by
    -- Proof comment: the canonical cochain model only occupies degrees `-1` and `0`.
    simpa [P] using naiveCotangentCochain_isStrictlyLE_zero (A := A) (B := B)
  have eQ :
      ((H 0).obj (naiveCotangentObject A B)) ≅ P.homology 0 := by
    -- Proof comment: pass from the derived-category homology object to homology of the chosen
    -- two-term representative.
    simpa [naiveCotangentObject, P] using
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) (0 : ℤ)).app P
  -- Proof comment: for the same two-term model, `H^0` is the cokernel of the unique
  -- differential, and that cokernel is the owner module of K\"ahler differentials.
  exact
    eQ ≪≫
      two_term_homology_zero_iso_cokernel (B := B) P hLE ≪≫
      self_presentation_d_negOne_zero_cokernel_iso_cotangentComplex_cokernel
        (A := A) (B := B) ≪≫
      self_presentation_cotangentComplex_cokernel_iso_kaehler (A := A) (B := B)

/-- Helper for Remark 15.85.2: the two-term cohomology condition on `NL_{B/A}` is exactly formal
smoothness. -/
lemma naiveCotangentObject_two_term_condition_iff_formallySmooth :
    (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
        Projective ((H 0).obj (naiveCotangentObject A B))) ↔
      FormallySmooth A B := by
  let eNeg := naiveCotangentObject_homology_negOne_iso_h1Cotangent (A := A) (B := B)
  let eZero := naiveCotangentObject_homology_zero_iso_kaehler (A := A) (B := B)
  rw [Algebra.formallySmooth_iff]
  constructor
  · rintro ⟨hneg, hproj₀⟩
    have hzeroH1 : IsZero (ModuleCat.of B (H1Cotangent A B)) := by
      -- Proof comment: transport the vanishing of `H^{-1}(NL_{B/A})` to the owner
      -- `H1Cotangent A B`.
      exact eNeg.isZero_iff.1 hneg
    have hprojULift :
        Projective (ModuleCat.of B (ULift.{max u v, v} Ω[B⁄A])) := by
      -- Proof comment: transport projectivity of `H^0(NL_{B/A})` to the owner K\"ahler module.
      exact Projective.of_iso eZero hproj₀
    have hsub : Subsingleton (H1Cotangent A B) := by
      exact (ModuleCat.isZero_iff_subsingleton).1 hzeroH1
    have hprojModuleULift : Module.Projective B (ULift.{max u v, v} Ω[B⁄A]) := by
      -- Proof comment: categorical projectivity of a module object is the same as projectivity
      -- of its underlying `B`-module.
      letI : Projective (ModuleCat.of B (ULift.{max u v, v} Ω[B⁄A])) := hprojULift
      infer_instance
    have hprojModule : Module.Projective B Ω[B⁄A] := by
      -- Proof comment: descend projectivity across the canonical `ULift` linear equivalence.
      letI : Module.Projective B (ULift.{max u v, v} Ω[B⁄A]) := hprojModuleULift
      exact
        Module.Projective.of_equiv
          ((ULift.moduleEquiv :
            ULift.{max u v, v} Ω[B⁄A] ≃ₗ[B] Ω[B⁄A]).symm)
    exact ⟨hprojModule, hsub⟩
  · intro hSmooth
    have hprojOmega : Module.Projective B Ω[B⁄A] := hSmooth.1
    have hsub : Subsingleton (H1Cotangent A B) := hSmooth.2
    have hneg :
        IsZero ((H (-1)).obj (naiveCotangentObject A B)) := by
      have hzeroH1 : IsZero (ModuleCat.of B (H1Cotangent A B)) := by
        -- Proof comment: `Algebra.formallySmooth_iff` gives the owner homology vanishing
        -- exactly as subsingleton first cotangent homology.
        exact (ModuleCat.isZero_iff_subsingleton).2 hsub
      exact eNeg.isZero_iff.2 hzeroH1
    have hprojModuleULift : Module.Projective B (ULift.{max u v, v} Ω[B⁄A]) := by
      -- Proof comment: transport the owner projectivity of `Ω[B⁄A]` to the `ULift` version
      -- appearing in the cokernel owner isomorphism.
      letI : Module.Projective B Ω[B⁄A] := hprojOmega
      exact
        Module.Projective.of_equiv
          ((ULift.moduleEquiv :
            ULift.{max u v, v} Ω[B⁄A] ≃ₗ[B] Ω[B⁄A]).symm)
    have hprojZeroTarget :
        Projective (ModuleCat.of B (ULift.{max u v, v} Ω[B⁄A])) := by
      letI : Module.Projective B (ULift.{max u v, v} Ω[B⁄A]) := hprojModuleULift
      infer_instance
    have hproj₀ : Projective ((H 0).obj (naiveCotangentObject A B)) := by
      -- Proof comment: move the owner projectivity back across the `H^0(NL_{B/A})` comparison.
      exact Projective.of_iso eZero.symm hprojZeroTarget
    exact ⟨hneg, hproj₀⟩

/-- Helper for Remark 15.85.2: vanishing of all degree-`1` extensions out of `NL_{B/A}` is
exactly vanishing of the degree-`1` derived-Ext functor. -/
lemma naiveCotangentObject_ext_one_vanishing_iff_derivedExt_functor_isZero :
    (∀ (N : ModuleCat B), ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N), e = 0) ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
  constructor
  · intro hExt
    -- Proof comment: objectwise `Ext¹`-vanishing is exactly the assertion that every value of
    -- the degree-`1` derived-Ext functor is the zero object.
    rw [Functor.isZero_iff]
    intro N
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    refine ⟨?_⟩
    intro x y
    exact (hExt N x).trans (hExt N y).symm
  · intro hExt
    -- Proof comment: once the owner functor is zero, each individual `Ext¹` group is a
    -- subsingleton, so every class is equal to `0`.
    rw [Functor.isZero_iff] at hExt
    intro N e
    have hsub :
        Subsingleton (Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N)) := by
      simpa [derivedExtToModuleFunctor] using
        (AddCommGrpCat.isZero_iff_subsingleton.1 (hExt N))
    let _ : Subsingleton (Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N)) := hsub
    exact Subsingleton.elim _ _

/-- Helper for Remark 15.85.2: under the canonical two-term bounds for `NL_{B/A}`, vanishing of
`H^{-1}` together with projectivity of `H^0` is equivalent to projective amplitude in `[0, 0]`. -/
lemma naiveCotangentObject_two_term_condition_iff_projective_amplitude_zero_zero :
    (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
        Projective ((H 0).obj (naiveCotangentObject A B))) ↔
      HasProjectiveAmplitudeIn (naiveCotangentObject A B) 0 0 := by
  constructor
  · rintro ⟨hneg, hproj₀⟩
    have hKGE₀ : (naiveCotangentObject A B).IsGE 0 := by
      -- Proof comment: below degree `0`, the only potentially nonzero cohomology is `H^{-1}`,
      -- and the theorem hypothesis kills that remaining degree.
      rw [DerivedCategory.isGE_iff]
      intro i hi
      by_cases hEq : i = -1
      · subst hEq
        simpa using hneg
      · let _ : (naiveCotangentObject A B).IsGE (-1) :=
          naiveCotangentObject_isGE_negOne (A := A) (B := B)
        exact
          DerivedCategory.isZero_of_isGE (naiveCotangentObject A B) (-1) i (by omega)
    classical
    let hsingle :=
      DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
        (naiveCotangentObject A B) 0
    let N : ModuleCat B := Classical.choose hsingle
    let e : naiveCotangentObject A B ≅ (single₀).obj N :=
      Classical.choice (Classical.choose_spec hsingle)
    let eH :
        ((H 0).obj (naiveCotangentObject A B)) ≅ N :=
      (H 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) (0 : ℤ)).app N
    have hNproj : Projective N := by
      -- Proof comment: transport projectivity of `H^0(NL_{B/A})` to the concentrated degree-zero
      -- model returned by the standard t-structure comparison.
      exact Projective.of_iso eH hproj₀
    have hAmpSingle : HasProjectiveAmplitudeIn ((single₀).obj N) 0 0 :=
      single_zero_hasProjectiveAmplitude_of_projective (B := B) N hNproj
    -- Proof comment: replace `NL_{B/A}` by its degree-zero single-object model.
    exact
      (hasProjectiveAmplitudeIn_iff_of_iso (B := B) e).2 hAmpSingle
  · rintro ⟨P, eP, hPge, hPle, hPproj⟩
    let eSingle :
        DerivedCategory.Q.obj P ≅ (single₀).obj (P.X 0) :=
      representative_single_iso_of_strict_bounds (A := ModuleCat B) P 0
    let e : naiveCotangentObject A B ≅ (single₀).obj (P.X 0) := eP ≪≫ eSingle
    have hzeroSingle :
        IsZero ((H (-1)).obj ((single₀).obj (P.X 0))) := by
      -- Proof comment: a degree-zero single object has no cohomology in degree `-1`.
      exact DerivedCategory.isZero_of_isGE _ 0 (-1) (by omega)
    have hneg : IsZero ((H (-1)).obj (naiveCotangentObject A B)) := by
      -- Proof comment: transport the degree-`-1` vanishing back across the concentrated-model
      -- comparison.
      exact hzeroSingle.of_iso ((H (-1)).mapIso e)
    let eH :
        ((H 0).obj (naiveCotangentObject A B)) ≅ P.X 0 :=
      (H 0).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) (0 : ℤ)).app (P.X 0)
    have hproj₀ : Projective ((H 0).obj (naiveCotangentObject A B)) := by
      -- Proof comment: `H^0(NL_{B/A})` identifies with the unique surviving degree of the
      -- projective representative.
      exact Projective.of_iso eH.symm (hPproj 0)
    exact ⟨hneg, hproj₀⟩

/-- Helper for Remark 15.85.2: in the `a = b = 0` specialization of the Chapter 15 TFAE, the
boundary clause for `NL_{B/A}` reduces to vanishing of the degree-`1` derived-Ext functor. -/
lemma naiveCotangentObject_boundary_clause_iff_derived_ext_one_functor_is_zero :
    ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj (naiveCotangentObject A B))) ∧
        (∀ (N : ModuleCat B), ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N),
          e = 0)) ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
  constructor
  · intro h
    -- Proof comment: the homology-vanishing half is automatic from the two-term bounds, so only
    -- the degree-`1` Ext clause matters.
    exact
      (naiveCotangentObject_ext_one_vanishing_iff_derivedExt_functor_isZero
        (A := A) (B := B)).1 h.2
  · intro hExt
    constructor
    · intro n hn
      -- Proof comment: outside `[-1, 0]`, the standard lower and upper bounds on `NL_{B/A}`
      -- force every cohomology object to vanish.
      by_cases hlt : n < -1
      · let _ : (naiveCotangentObject A B).IsGE (-1) :=
            naiveCotangentObject_isGE_negOne (A := A) (B := B)
        exact DerivedCategory.isZero_of_isGE (naiveCotangentObject A B) (-1) n hlt
      · have hgt : 0 < n := by
          by_contra hgt
          have hge : -1 ≤ n := by omega
          have hle : n ≤ 0 := by omega
          exact hn ⟨hge, hle⟩
        let _ : (naiveCotangentObject A B).IsLE 0 :=
          naiveCotangentObject_isLE_zero (A := A) (B := B)
        exact DerivedCategory.isZero_of_isLE (naiveCotangentObject A B) 0 n hgt
    · -- Proof comment: translate the owner zero-functor statement back to the source-facing
      -- degree-`1` `Ext`-vanishing clause.
      exact
        (naiveCotangentObject_ext_one_vanishing_iff_derivedExt_functor_isZero
          (A := A) (B := B)).2 hExt

/-- Helper for Remark 15.85.2: the clause `(4)` of the projective-amplitude TFAE at `a = b = 0`
uses a logically equivalent reformulation of `n ∉ [-1, 0]`. -/
private lemma naiveCotangentObject_boundary_clause_simplified_iff :
    ((∀ n : ℤ,
        (-1 ≤ n → 0 < n) → IsZero ((H n).obj (naiveCotangentObject A B))) ∧
        (∀ (N : ModuleCat B), ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N),
          e = 0)) ↔
      ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj (naiveCotangentObject A B))) ∧
        (∀ (N : ModuleCat B), ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N),
          e = 0)) := by
  constructor
  · rintro ⟨hH, hExt⟩
    constructor
    · intro n hn
      apply hH n
      intro hge
      by_contra hgt
      exact hn ⟨hge, le_of_not_gt hgt⟩
    · exact hExt
  · rintro ⟨hH, hExt⟩
    constructor
    · intro n hn
      apply hH n
      intro hmem
      exact not_lt_of_ge hmem.2 (hn hmem.1)
    · exact hExt

/-- Helper for Remark 15.85.2: clause `(4)` of the projective-amplitude TFAE at `a = b = 0`
specializes exactly to the boundary statement for `NL_{B/A}`. -/
private lemma naiveCotangentObject_projective_amplitude_zero_zero_iff_boundary_clause :
    HasProjectiveAmplitudeIn (naiveCotangentObject A B) 0 0 ↔
      ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj (naiveCotangentObject A B))) ∧
        (∀ (N : ModuleCat B), ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N),
          e = 0)) := by
  -- Proof comment: this is exactly clause `(4)` of `projectiveAmplitudeIn_ext_vanishing_tfae`
  -- after specializing to the interval `[0, 0]`.
  simpa using
    ((projectiveAmplitudeIn_ext_vanishing_tfae
      (R := B) (naiveCotangentObject A B) 0 0).out 0 3)

/-- Helper for Remark 15.85.2: Lemma `15.85.1` specialized to the naive cotangent object turns the
two-term cohomology condition into degree-`1` derived-Ext vanishing. -/
lemma naiveCotangentObject_two_term_condition_iff_ext1_vanishes :
    (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
        Projective ((H 0).obj (naiveCotangentObject A B))) ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
  -- Route correction: instead of importing `Lemma_15_85_1` through the broken upstream path, we
  -- replay its source-faithful specialization locally for `K = NL_{B/A}`.
  -- Proof comment: first rewrite the two-term source condition as amplitude in `[0, 0]`, then
  -- specialize clause `(4)` of the Chapter 15 TFAE, and finally translate its boundary clause to
  -- vanishing of the degree-`1` derived-Ext functor.
  calc
    (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
        Projective ((H 0).obj (naiveCotangentObject A B))) ↔
      HasProjectiveAmplitudeIn (naiveCotangentObject A B) 0 0 :=
        naiveCotangentObject_two_term_condition_iff_projective_amplitude_zero_zero
          (A := A) (B := B)
    _ ↔
        ((∀ n : ℤ, n ∉ Set.Icc (-1) 0 → IsZero ((H n).obj (naiveCotangentObject A B))) ∧
          (∀ (N : ModuleCat B),
            ∀ e : Ext^(1 : ℤ)(naiveCotangentObject A B, (single₀).obj N), e = 0)) :=
        naiveCotangentObject_projective_amplitude_zero_zero_iff_boundary_clause
          (A := A) (B := B)
    _ ↔ IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) :=
        naiveCotangentObject_boundary_clause_iff_derived_ext_one_functor_is_zero
          (A := A) (B := B)

-- Proof sketch: combine the canonical criterion `Algebra.smooth_iff`, which rewrites smoothness
-- as finite presentation plus formal smoothness, with the degree-`1` derived `Ext`-vanishing
-- criterion `IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1)` applied to the
-- canonical owner `NL_{B/A}`, and with Proposition `10.138.8`, which identifies formal
-- smoothness with
-- vanishing of `H¹(L_{B/A})` together with projectivity of `Ω[B⁄A]`.
/-- Remark 15.85.2 (1): an `A`-algebra `B` is smooth if and only if it is of finite presentation
and `Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem smooth_iff_finitePresentation_and_naiveCotangent_ext1_vanishes :
    Smooth A B ↔
      FinitePresentation A B ∧
        IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := by
  -- Proof comment: the smoothness owner theorem already splits the statement into finite
  -- presentation plus formal smoothness, so only the formal-smooth criterion needs to be
  -- substituted.
  have hFormal :
      FormallySmooth A B ↔
        IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
    -- Proof comment: rewrite formal smoothness to the two-term cohomology condition and then
    -- apply the specialized degree-`1` Ext criterion for the naive cotangent object.
    calc
      FormallySmooth A B ↔
          (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
            Projective ((H 0).obj (naiveCotangentObject A B))) := by
              simpa using
                (naiveCotangentObject_two_term_condition_iff_formallySmooth
                  (A := A) (B := B)).symm
      _ ↔ IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
        exact naiveCotangentObject_two_term_condition_iff_ext1_vanishes (A := A) (B := B)
  constructor
  · intro h
    -- Proof comment: smoothness already supplies finite presentation and formal smoothness.
    let _ : Smooth A B := h
    exact ⟨inferInstance, hFormal.mp inferInstance⟩
  · rintro ⟨hfp, hExt⟩
    -- Proof comment: conversely, finite presentation plus the rewritten formal-smoothness clause
    -- reconstruct smoothness by the owner instance.
    let _ : FinitePresentation A B := hfp
    let _ : FormallySmooth A B := hFormal.mpr hExt
    have hSmooth : Smooth A B := by
      rw [Algebra.smooth_iff]
      exact ⟨inferInstance, inferInstance⟩
    exact hSmooth

-- Proof sketch: apply Lemma `15.85.1` to the canonical owner `NL_{B/A}`,
-- whose only nonzero cohomology groups are `H^{-1}(NL_{B/A}) = H1Cotangent A B` and
-- `H^0(NL_{B/A}) = Ω[B⁄A]`, and then rewrite the resulting condition using Proposition
-- `10.138.8`, i.e. `Algebra.formallySmooth_iff`.
/-- Remark 15.85.2 (2): an `A`-algebra `B` is formally smooth if and only if
`Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem formallySmooth_iff_naiveCotangent_ext1_vanishes :
    FormallySmooth A B ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := by
  -- Proof comment: Lemma `15.85.1` turns degree-`1` derived-Ext vanishing for `NL_{B/A}` into
  -- the two-term cohomology condition, and the bridge lemma identifies that condition with
  -- formal smoothness.
  calc
    FormallySmooth A B ↔
        (IsZero ((H (-1)).obj (naiveCotangentObject A B)) ∧
          Projective ((H 0).obj (naiveCotangentObject A B))) := by
            simpa using
              (naiveCotangentObject_two_term_condition_iff_formallySmooth
                (A := A) (B := B)).symm
    _ ↔ IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) (1 : ℤ)) := by
      exact naiveCotangentObject_two_term_condition_iff_ext1_vanishes (A := A) (B := B)

end

end Algebra
