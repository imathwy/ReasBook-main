import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_6
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "DModRI" => DerivedCategory ModRI
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
variable (PClass : ObjectProperty ModR)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "ReduceCpx" => ReduceModI.mapHomologicalComplex (ComplexShape.up ℤ)
local notation "RestrictModI" => ModuleCat.restrictScalars (Ideal.Quotient.mk I)
local notation "RestrictCpx" => RestrictModI.mapHomologicalComplex (ComplexShape.up ℤ)
local notation "PClassModI" => (PClass.map ReduceModI)

/- Domain-style sampling:
- primary domain: bounded-above derived representatives of module complexes, together with
  reduction modulo an ideal;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction: the chosen bounded-above cochain complex with terms in `PClass`
  `P : CochainComplex.MinusWithTermsIn PClass`, together with the chapter owners
  `PClass.IsClosedUnderBinaryCoproducts` and `PClass.IsStableUnderRetracts` for the direct-sum and
  direct-summand conditions; representation / reduction remain direct isomorphism data on that
  owner object, and the reduced complex is already owned by
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- primitive data: `P : CochainComplex.MinusWithTermsIn PClass`, an isomorphism
  `K ≅ DerivedCategory.Q.obj (P : CpxR)`, and the reduced owner
  `E : CochainComplex.MinusWithTermsIn PClassModI`;
- derived API: the bounded-above condition and termwise membership of `E`, plus existential
  theorems asserting that such a representative or lift exists.

Source/core/bridge triage:
- `source-facing`: existence of a bounded-above `PClass`-complex representing `K`, and of one whose
  reduction modulo `I` is a prescribed complex `E`;
- `core/canonical`: the chosen complex `P` together with owner-style predicates on `P`;
- `bridge/view`: the termwise reduction condition
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ E`. -/

-- Proof sketch: choose a bounded-above `PClass`-representative of `K`, identify its derived
-- reduction modulo `I` with the termwise scalar extension to `R ⧸ I`, compare that complex with
-- the underlying complex of the owner `E` in `D(R ⧸ I)`, and then lift the resulting acyclic cone
-- by the previous lifting lemma. The cokernel complex of the lifted map gives the desired
-- representative of `K` with prescribed reduction.
/-- Helper for Lemma 15.76.2: each term of the quotient-side bounded-above complex `E` is
projective over `R ⧸ I`. -/
lemma projective_term_of_reduced_complex
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    (E : CochainComplex.MinusWithTermsIn PClassModI)
    (i : ℤ) :
    Projective ((E : CpxRI).X i) := by
  -- Unpack the reduction witness for degree `i` and transport projectivity across the chosen
  -- quotient-side isomorphism.
  rcases exists_term_lift_of_minusWithTermsIn (I := I) PClass E i with ⟨P, hP, ⟨e⟩⟩
  letI : Projective P := hprojective hP
  exact Projective.of_iso e inferInstance

/-- Helper for Lemma 15.76.2: the quotient-side complex `E` can be viewed as a bounded-above
projective complex. -/
abbrev reduced_complex_projectiveMinus
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    (E : CochainComplex.MinusWithTermsIn PClassModI) :
    CochainComplex.ProjectiveMinus ModRI :=
  ⟨⟨(E : CpxRI), E.minus⟩,
    fun i ↦ projective_term_of_reduced_complex (I := I) (PClass := PClass) hprojective E i⟩

/-- Helper for Lemma 15.76.2: a bounded-above `PClass`-complex with projective terms is termwise
flat, so the public derived scalar-extension comparison from Lemma `15.67.13` applies to it. -/
lemma termwiseFlat_of_minusWithTermsIn_projective
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    (P : CochainComplex.MinusWithTermsIn PClass) :
    (P : CpxR).IsTermwiseFlat := by
  -- Read the owner degreewise and convert each categorical projective term into the usual module
  -- flatness instance.
  intro i
  letI : Projective ((P : CpxR).X i) := hprojective (P.term_mem i)
  exact Module.Flat.of_projective

/-- Helper for Lemma 15.76.2: a bounded-above `PClass`-representative computes derived reduction
by ordinary termwise reduction modulo `I`. -/
lemma derived_reduction_iso_of_representative
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    (K : DModR)
    (P : CochainComplex.MinusWithTermsIn PClass)
    (eK : K ≅ DerivedCategory.Q.obj (P : CpxR)) :
    (K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (ReduceCpx.obj (P : CpxR)) := by
  obtain ⟨b, hP_le⟩ := P.exists_isStrictlyLE
  have hP_flat :
      (P : CpxR).IsTermwiseFlat :=
    termwiseFlat_of_minusWithTermsIn_projective (PClass := PClass) hprojective P
  have hCompute :
      ((DerivedCategory.Q.obj (P : CpxR)) ⊗[R]^L[(R ⧸ I)]) ≅
        DerivedCategory.Q.obj (ReduceCpx.obj (P : CpxR)) := by
    -- Compute derived reduction on the bounded-above flat representative `P`.
    simpa [ReduceCpx] using
      (derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
        (A := R) (B := R ⧸ I) (E := (P : CpxR)) hP_flat hP_le)
  -- Transport the strict representative computation across the chosen isomorphism `eK`.
  exact (derivedTensorWithAlgebra (algebraMap R (R ⧸ I))).mapIso eK ≪≫ hCompute

/-- Helper for Lemma 15.76.2: conjugating a homotopy-category map through
`DerivedCategory.quotientCompQhIso` recovers its `DerivedCategory.Q`-image over `R ⧸ I`. -/
lemma quotientCompQhIso_homCongr_map
    {E L : CpxRI} (f : E ⟶ L) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso ModRI).app E)
        ((DerivedCategory.quotientCompQhIso ModRI).app L))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient ModRI (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- Rewrite the conjugated homotopy-category map as the naturality square of
  -- `quotientCompQhIso`, then cancel the inverse/forward comparison pair.
  change
    (DerivedCategory.quotientCompQhIso ModRI).inv.app E ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient ModRI (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModRI).hom.app L =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient ModRI (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModRI).hom.app L =
        (DerivedCategory.quotientCompQhIso ModRI).hom.app E ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso ModRI).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso ModRI).inv.app E ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient ModRI (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso ModRI).hom.app L =
      (DerivedCategory.quotientCompQhIso ModRI).inv.app E ≫
        ((DerivedCategory.quotientCompQhIso ModRI).hom.app E ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso ModRI).inv.app E ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
      simpa using
        (Iso.inv_hom_id_assoc
          ((DerivedCategory.quotientCompQhIso ModRI).app E)
          (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.76.2: a derived-category comparison from a bounded-above projective
complex can be strictified to an actual quasi-isomorphism of cochain complexes. -/
lemma exists_quasiIso_of_projective_representative_comparison
    (E : CochainComplex.ProjectiveMinus ModRI)
    {L : CpxRI}
    (h : DerivedCategory.Q.obj (E : CpxRI) ≅ DerivedCategory.Q.obj L) :
    ∃ δ : (E : CpxRI) ⟶ L,
      QuasiIso δ ∧ DerivedCategory.Q.map δ = h.hom := by
  let HoQ : CpxRI ⥤ HomotopyCategory ModRI (ComplexShape.up ℤ) :=
    HomotopyCategory.quotient ModRI (ComplexShape.up ℤ)
  let eHom :
      (DerivedCategory.Qh.obj (HoQ.obj (E : CpxRI)) ⟶
          DerivedCategory.Qh.obj (HoQ.obj L)) ≃
        (DerivedCategory.Q.obj (E : CpxRI) ⟶ DerivedCategory.Q.obj L) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso ModRI).app (E : CpxRI))
      ((DerivedCategory.quotientCompQhIso ModRI).app L)
  let hHo : DerivedCategory.Qh.obj (HoQ.obj (E : CpxRI)) ⟶
      DerivedCategory.Qh.obj (HoQ.obj L) := eHom.symm h.hom
  obtain ⟨δHo, hδHo⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
      (𝒜 := ModRI) E L).surjective hHo
  obtain ⟨δ, rfl⟩ := HoQ.map_surjective δHo
  have hQδ : DerivedCategory.Q.map δ = h.hom := by
    -- Compare the strict lift to the target isomorphism after conjugating both by
    -- `quotientCompQhIso`.
    apply eHom.injective
    simpa [hHo, quotientCompQhIso_homCongr_map (I := I) (f := δ)] using hδHo
  have hIsoQδ : IsIso (DerivedCategory.Q.map δ) := by
    rw [hQδ]
    infer_instance
  exact ⟨δ, (DerivedCategory.isIso_Q_map_iff_quasiIso ModRI δ).1 hIsoQδ, hQδ⟩

/-- Helper for Lemma 15.76.2: the mapping cone of a morphism between bounded-above termwise
`PClass`-complexes is again bounded above with terms in `PClassModI`. -/
lemma mappingCone_minusWithTermsIn_of_module_class
    [PClass.IsClosedUnderBinaryCoproducts]
    (E : CochainComplex.MinusWithTermsIn PClassModI)
    (P : CochainComplex.MinusWithTermsIn PClass)
    (δ : (E : CpxRI) ⟶ ReduceCpx.obj (P : CpxR)) :
    CochainComplex.MinusWithTermsIn PClassModI := by
  obtain ⟨bE, hE_le⟩ := E.exists_isStrictlyLE
  obtain ⟨bP, hP_le⟩ := P.exists_isStrictlyLE
  refine ⟨⟨CochainComplex.mappingCone δ, ?_⟩, ?_⟩
  · -- Proof comment: one upper bound controls both the shifted source term and the target term.
    refine (CochainComplex.minus_iff ModRI _).2 ⟨max (bE - 1) bP, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hEi : bE < i + 1 := by omega
    have hPi : bP < i := by omega
    have hEzero : IsZero ((E : CpxRI).X (i + 1)) := by
      letI : (E : CpxRI).IsStrictlyLE bE := hE_le
      simpa using (E : CpxRI).isZero_of_isStrictlyLE bE (i + 1) hEi
    have hPzero : IsZero ((ReduceCpx.obj (P : CpxR)).X i) := by
      letI : (P : CpxR).IsStrictlyLE bP := hP_le
      simpa [ReduceCpx] using
        (ReduceModI.map_isZero ((P : CpxR).isZero_of_isStrictlyLE bP i hPi))
    rw [CochainComplex.mappingCone.isZero_X_iff (φ := δ) i]
    exact ⟨hEzero, hPzero⟩
  · intro i
    -- Proof comment: degree `i` of the cone is the biproduct of `E^{i+1}` and the reduced
    -- degree `i` term of `P`, so the object property follows from binary-coproduct closure.
    let _ : ∀ j : ℤ,
        Limits.HasBinaryBiproduct ((E : CpxRI).X (j + 1)) ((ReduceCpx.obj (P : CpxR)).X j) :=
      fun _ ↦ inferInstance
    let _ : HomologicalComplex.HasHomotopyCofiber δ :=
      mappingCone_hasHomotopyCofiber (f := δ)
    let e : (CochainComplex.mappingCone δ).X i ≅
        (E : CpxRI).X (i + 1) ⊞ (ReduceCpx.obj (P : CpxR)).X i :=
      HomologicalComplex.homotopyCofiber.XIsoBiprod δ i (i + 1)
        (ComplexShape.up_mk i (i + 1) rfl)
    have hEi : PClassModI ((E : CpxRI).X (i + 1)) := E.term_mem (i + 1)
    have hPi : PClassModI ((ReduceCpx.obj (P : CpxR)).X i) := by
      simpa [ReduceCpx] using P.term_mem i
    exact PClassModI.prop_of_iso e (PClassModI.prop_biprod hEi hPi)

/-- Helper for Lemma 15.76.2: the cone of a strict quasi-isomorphism of `R/I`-complexes is
acyclic. -/
lemma mappingCone_acyclic_of_quasiIso_local
    {E L : CpxRI} (δ : E ⟶ L) [QuasiIso δ] :
    (CochainComplex.mappingCone δ).Acyclic := by
  have hq :
      HomotopyCategory.quasiIso ModRI (up ℤ)
        ((HomotopyCategory.quotient ModRI (up ℤ)).map δ) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := ModRI) (c := up ℤ) δ).2 inferInstance
  have hq' :
      (HomotopyCategory.subcategoryAcyclic ModRI).trW
        ((HomotopyCategory.quotient ModRI (up ℤ)).map δ) := by
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := ModRI)] using hq
  have hmem :
      HomotopyCategory.subcategoryAcyclic ModRI
        ((HomotopyCategory.quotient ModRI (up ℤ)).obj (CochainComplex.mappingCone δ)) := by
    -- Proof comment: in the standard cone triangle, the cone term is exactly the acyclic witness
    -- attached to a quasi-isomorphism.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic ModRI).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh δ)
        (HomotopyCategory.mappingCone_triangleh_distinguished δ)).1 hq'
  exact
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := ModRI) (CochainComplex.mappingCone δ)).1 hmem

/-- Helper for Lemma 15.76.2: the cokernel of the second biproduct inclusion is the first
summand. -/
private noncomputable def biprod_inr_cokernel_iso
    {A B : ModRI} :
    cokernel (biprod.inr : B ⟶ A ⊞ B) ≅ A := by
  let cofork : CokernelCofork (biprod.inr : B ⟶ A ⊞ B) :=
    CokernelCofork.ofπ (biprod.fst : A ⊞ B ⟶ A) (by simp)
  let hcofork : IsColimit cofork :=
    Cofork.IsColimit.mk cofork
      (fun s ↦ biprod.inl ≫ s.π)
      (by
        -- A morphism out of a biproduct is determined by its two summand restrictions; the
        -- cofork condition already kills the `B`-summand.
        intro s
        apply biprod.hom_ext'
        · simp [cofork]
        · simpa [cofork] using s.condition)
      (by
        -- Uniqueness follows after precomposing with the first coprojection.
        intro s m hm
        calc
          m = biprod.inl ≫ cofork.π ≫ m := by simp [cofork]
          _ = biprod.inl ≫ s.π := by rw [hm])
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (biprod.inr : B ⟶ A ⊞ B))
    hcofork

/-- Helper for Lemma 15.76.2: each component of the cone inclusion is the canonical second
summand inclusion, hence a split monomorphism. -/
lemma mappingCone_inr_f_isSplitMono
    {E L : CpxRI} (δ : E ⟶ L) (i : ℤ) :
    IsSplitMono ((CochainComplex.mappingCone.inr δ).f i) := by
  -- Degree `i` of the cone is `E.X (i + 1) ⊞ L.X i`, so `mappingCone.inr` is split by the
  -- projection onto the second summand.
  let hsplit : IsSplitMono (biprod.inr : L.X i ⟶ E.X (i + 1) ⊞ L.X i) := by
    refine IsSplitMono.mk' ⟨biprod.snd, by simp⟩
  simpa using hsplit

/-- Helper for Lemma 15.76.2: the cokernel of each component of the cone inclusion is the shifted
source term. -/
noncomputable lemma mappingCone_inr_f_cokernel_iso
    {E L : CpxRI} (δ : E ⟶ L) (i : ℤ) :
    cokernel ((CochainComplex.mappingCone.inr δ).f i) ≅ E.X (i + 1) := by
  -- After rewriting the cone term as a biproduct, this is the standard cokernel of
  -- `biprod.inr`.
  simpa using
    (biprod_inr_cokernel_iso (I := I) (A := E.X (i + 1)) (B := L.X i))

/-- Helper for Lemma 15.76.2: evaluating the cokernel complex of the cone inclusion at degree
`i` identifies the complex-level cokernel projection with the ordinary component cokernel
projection. -/
lemma mappingCone_inr_cokernel_component_iso_hom_pi
    {E L : CpxRI} (δ : E ⟶ L) (i : ℤ) :
    (cokernel.π (CochainComplex.mappingCone.inr δ)).f i ≫
        (PreservesCokernel.iso
          (HomologicalComplex.eval ModRI (ComplexShape.up ℤ) i)
          (CochainComplex.mappingCone.inr δ)).hom ≫
        (mappingCone_inr_f_cokernel_iso (I := I) δ i).hom =
      cokernel.π ((CochainComplex.mappingCone.inr δ).f i) := by
  -- Proof comment: first pass from the complex cokernel to the evaluated component cokernel, then
  -- use the already computed pointwise cokernel of the biproduct inclusion.
  have hcomponent :
      (cokernel.π (CochainComplex.mappingCone.inr δ)).f i ≫
          (PreservesCokernel.iso
            (HomologicalComplex.eval ModRI (ComplexShape.up ℤ) i)
            (CochainComplex.mappingCone.inr δ)).hom =
        cokernel.π ((CochainComplex.mappingCone.inr δ).f i) := by
    simpa [CategoryTheory.Limits.PreservesCokernel.iso] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (isColimitOfHasCokernelOfPreservesColimit
          (HomologicalComplex.eval ModRI (ComplexShape.up ℤ) i)
          (CochainComplex.mappingCone.inr δ))
        (colimit.isColimit
          (parallelPair ((CochainComplex.mappingCone.inr δ).f i) 0))
        WalkingParallelPair.one)
  calc
    (cokernel.π (CochainComplex.mappingCone.inr δ)).f i ≫
        (PreservesCokernel.iso
          (HomologicalComplex.eval ModRI (ComplexShape.up ℤ) i)
          (CochainComplex.mappingCone.inr δ)).hom ≫
        (mappingCone_inr_f_cokernel_iso (I := I) δ i).hom =
      cokernel.π ((CochainComplex.mappingCone.inr δ).f i) ≫
        (mappingCone_inr_f_cokernel_iso (I := I) δ i).inv ≫
          (mappingCone_inr_f_cokernel_iso (I := I) δ i).hom := by
            simpa [Category.assoc] using
              congrArg
                (fun ζ ↦ ζ ≫ (mappingCone_inr_f_cokernel_iso (I := I) δ i).hom)
                hcomponent
    _ = cokernel.π ((CochainComplex.mappingCone.inr δ).f i) := by
      simp [Category.assoc]

/-- Helper for Lemma 15.76.2: each component of the cone inclusion is split mono with the
expected cokernel. -/
lemma mappingCone_inr_f_splitMono_and_cokernel_iso
    {E L : CpxRI} (δ : E ⟶ L) (i : ℤ) :
    IsSplitMono ((CochainComplex.mappingCone.inr δ).f i) ∧
      cokernel ((CochainComplex.mappingCone.inr δ).f i) ≅ E.X (i + 1) := by
  -- Bundle the two degreewise cone facts so the main proof can reuse one stable interface.
  exact ⟨mappingCone_inr_f_isSplitMono (I := I) δ i,
    mappingCone_inr_f_cokernel_iso (I := I) δ i⟩

/-- Helper for Lemma 15.76.2: the quotient-model differential transport from a reduced complex
back to the underlying restricted complex agrees with the original source differential. -/
lemma restricted_quotient_differential_naturality
    {X : CpxR} (i : ℤ) :
    ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X i))).mkQ) ≫
        RestrictModI.map
          ((reduceModI_obj_iso_quotient (I := I) (X.X i)).inv ≫
            (ReduceCpx.obj X).d i (i + 1) ≫
            (reduceModI_obj_iso_quotient (I := I) (X.X (i + 1))).hom) =
      X.d i (i + 1) ≫
        ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X (i + 1)))).mkQ) := by
  -- Proof comment: evaluate both morphisms on representatives; the quotient-model naturality
  -- theorem already says that the conjugated reduced differential sends `mkQ x` to `mkQ (d x)`.
  ext x
  simpa [ReduceCpx] using
    reduceModI_obj_iso_quotient_naturality_on_mkQ (I := I) (f := X.d i (i + 1)) x

/-- Helper for Lemma 15.76.2: the degree-`i` restricted-scalar component attached to a morphism
out of a reduced complex. -/
private abbrev restricted_component_of_reduction_map
    {X : CpxR} {Y : CpxRI}
    (f : ReduceCpx.obj X ⟶ Y)
    (i : ℤ) :
    X.X i ⟶ (RestrictCpx.obj Y).X i :=
  ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X i))).mkQ) ≫
    RestrictModI.map
      ((reduceModI_obj_iso_quotient (I := I) (X.X i)).inv ≫ f.f i)

/-- Helper for Lemma 15.76.2: the quotient-model components attached to a morphism out of a
reduced complex commute with the differentials after restricting scalars. -/
lemma restricted_component_of_reduction_map_comm
    {X : CpxR} {Y : CpxRI}
    (f : ReduceCpx.obj X ⟶ Y)
    (i : ℤ) :
    restricted_component_of_reduction_map (I := I) (f := f) i ≫
        (RestrictCpx.obj Y).d i (i + 1) =
      X.d i (i + 1) ≫
        restricted_component_of_reduction_map (I := I) (f := f) (i + 1) := by
  let qi :
      X.X i ⟶ ModuleCat.of R (X.X i ⧸ (I • (⊤ : Submodule R (X.X i)))) :=
    ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X i))).mkQ)
  let qj :
      X.X (i + 1) ⟶ ModuleCat.of R (X.X (i + 1) ⧸ (I • (⊤ : Submodule R (X.X (i + 1))))) :=
    ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X (i + 1)))).mkQ)
  let ei := reduceModI_obj_iso_quotient (I := I) (X.X i)
  let ej := reduceModI_obj_iso_quotient (I := I) (X.X (i + 1))
  -- Proof comment: first rewrite the target differential through the chain-map relation for `f`,
  -- then isolate the quotient-model differential transport and replace it by the source
  -- differential using the dedicated naturality lemma above.
  calc
    restricted_component_of_reduction_map (I := I) (f := f) i ≫
        (RestrictCpx.obj Y).d i (i + 1) =
      qi ≫
        RestrictModI.map
          (((ei.inv ≫ (ReduceCpx.obj X).d i (i + 1) ≫ ej.hom) ≫
            (ej.inv ≫ f.f (i + 1)))) := by
          rw [show f.f i ≫ Y.d i (i + 1) =
              (ReduceCpx.obj X).d i (i + 1) ≫ f.f (i + 1) by
                simpa using f.comm i (i + 1)]
          simp [restricted_component_of_reduction_map, qi, ei, ej, Category.assoc]
    _ = (qi ≫
          RestrictModI.map
            (ei.inv ≫ (ReduceCpx.obj X).d i (i + 1) ≫ ej.hom)) ≫
          RestrictModI.map (ej.inv ≫ f.f (i + 1)) := by
            simp [Functor.map_comp, Category.assoc]
    _ = (X.d i (i + 1) ≫ qj) ≫
          RestrictModI.map (ej.inv ≫ f.f (i + 1)) := by
            simpa [qi, qj, ei, ej] using
              restricted_quotient_differential_naturality (I := I) (X := X) i
    _ = X.d i (i + 1) ≫
          restricted_component_of_reduction_map (I := I) (f := f) (i + 1) := by
            simp [restricted_component_of_reduction_map, qj, ej, Category.assoc]

/-- Helper for Lemma 15.76.2: the quotient-model components define an actual cochain-map after
restricting scalars. -/
lemma restricted_chainMap_of_reduction_map_comm
    {X : CpxR} {Y : CpxRI}
    (f : ReduceCpx.obj X ⟶ Y) :
    ∀ i j, (ComplexShape.up ℤ).Rel i j →
      restricted_component_of_reduction_map (I := I) (f := f) i ≫
          (RestrictCpx.obj Y).d i j =
        X.d i j ≫ restricted_component_of_reduction_map (I := I) (f := f) j := by
  intro i j hij
  have hij' : i + 1 = j := by
    simpa using hij
  subst hij'
  simpa using restricted_component_of_reduction_map_comm (I := I) (f := f) i

/-- Helper for Lemma 15.76.2: a morphism out of a reduced complex induces a strict cochain map
from the original complex to the restricted target. -/
private def restricted_chainMap_of_reduction_map
    {X : CpxR} {Y : CpxRI}
    (f : ReduceCpx.obj X ⟶ Y) :
    X ⟶ RestrictCpx.obj Y :=
  { f := fun i ↦ restricted_component_of_reduction_map (I := I) (f := f) i
    comm' := restricted_chainMap_of_reduction_map_comm (I := I) (f := f) }

/-- Helper for Lemma 15.76.2: the degree-`i` quotient component from a lifted complex `A` to the
restricted-scalar mapping cone identified by `eA`. -/
private abbrev restricted_mappingCone_quotient_component
    {E : CpxRI}
    {P : CochainComplex.MinusWithTermsIn PClass}
    (δ : E ⟶ ReduceCpx.obj (P : CpxR))
    (A : CochainComplex.MinusWithTermsIn PClass)
    (eA : ReduceCpx.obj (A : CpxR) ≅ CochainComplex.mappingCone δ)
    (i : ℤ) :
    (A : CpxR).X i ⟶ (RestrictCpx.obj (CochainComplex.mappingCone δ)).X i :=
  restricted_component_of_reduction_map (I := I) (f := eA.hom) i

/-- Helper for Lemma 15.76.2: each quotient-side component is epi because it is the quotient map
followed by an isomorphism after restricting scalars. -/
lemma restricted_mappingCone_quotient_component_epi
    {E : CpxRI}
    {P : CochainComplex.MinusWithTermsIn PClass}
    (δ : E ⟶ ReduceCpx.obj (P : CpxR))
    (A : CochainComplex.MinusWithTermsIn PClass)
    (eA : ReduceCpx.obj (A : CpxR) ≅ CochainComplex.mappingCone δ)
    (i : ℤ) :
    Epi (restricted_mappingCone_quotient_component
      (I := I) (PClass := PClass) δ A eA i) := by
  -- The first factor is the usual module quotient map, and the second factor is the restricted
  -- scalar image of an isomorphism.
  let q :
      (A : CpxR).X i ⟶
        ModuleCat.of R (((A : CpxR).X i) ⧸ (I • (⊤ : Submodule R ((A : CpxR).X i)))) :=
    ModuleCat.ofHom ((I • (⊤ : Submodule R ((A : CpxR).X i))).mkQ)
  have hq : Function.Surjective q.hom := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R ((A : CpxR).X i))) x
    exact ⟨y, rfl⟩
  haveI : Epi q := (ModuleCat.epi_iff_surjective q).2 hq
  haveI :
      IsIso
        (RestrictModI.map
          ((reduceModI_obj_iso_quotient (I := I) ((A : CpxR).X i)).inv ≫ eA.hom.f i)) := by
    infer_instance
  simpa [restricted_mappingCone_quotient_component, q]
    using (show Epi
      (q ≫
        RestrictModI.map
          ((reduceModI_obj_iso_quotient (I := I) ((A : CpxR).X i)).inv ≫ eA.hom.f i)) by
        infer_instance)

/-- Helper for Lemma 15.76.2: restricting scalars preserves the acyclicity of the cone on the
strict comparison `δ`. -/
lemma restricted_mappingCone_acyclic
    {E : CpxRI}
    {P : CochainComplex.MinusWithTermsIn PClass}
    (δ : E ⟶ ReduceCpx.obj (P : CpxR))
    [QuasiIso δ] :
    ((RestrictCpx.obj (CochainComplex.mappingCone δ)) : CpxR).Acyclic := by
  -- Proof comment: the cone is already acyclic over `R/I`; exactness of restriction of scalars
  -- carries that acyclicity back to the underlying `R`-complex.
  exact _root_.restrictScalarsComplex_acyclic_of_acyclic
    (algebraMap R (R ⧸ I))
    (CochainComplex.mappingCone δ)
    (mappingCone_acyclic_of_quasiIso_local (I := I) δ)

/-- Helper for Lemma 15.76.2: passing a reduction-side map through a source cochain-map and then
restricting scalars agrees degreewise with first restricting scalars and then composing in
`Cpx(R)`. -/
lemma restricted_component_of_reduction_map_comp
    {X A : CpxR} {Y : CpxRI}
    (φ : X ⟶ A)
    (f : ReduceCpx.obj A ⟶ Y)
    (i : ℤ) :
    restricted_component_of_reduction_map (I := I) (f := ReduceCpx.map φ ≫ f) i =
      φ.f i ≫ restricted_component_of_reduction_map (I := I) (f := f) i := by
  let eX := reduceModI_obj_iso_quotient (I := I) (X.X i)
  let eA := reduceModI_obj_iso_quotient (I := I) ((A : CpxR).X i)
  -- Proof comment: evaluate both sides on a representative `x`; the quotient-model naturality
  -- formula transports `mkQ (φ x)` across the fixed reduction isomorphisms.
  ext x
  have hnat :
      ((((eX.inv ≫ (ReduceModI.map (φ.f i)) ≫ eA.hom).hom).restrictScalars R)
        ((I • (⊤ : Submodule R (X.X i))).mkQ x)) =
        ((I • (⊤ : Submodule R ((A : CpxR).X i))).mkQ ((φ.f i).hom x)) := by
    simpa [eX, eA, ReduceCpx] using
      reduceModI_obj_iso_quotient_naturality_on_mkQ (I := I) (f := φ.f i) x
  simpa [restricted_component_of_reduction_map, eX, eA, Functor.map_comp, Category.assoc]
    using congrArg
      (fun z ↦ (((RestrictModI.map (eA.inv ≫ f.f i)).hom).hom) z)
      hnat

/-- Helper for Lemma 15.76.2: the restricted chain-map attached to a reduction-side morphism is
functorial in the source complex. -/
lemma restricted_chainMap_of_reduction_map_comp
    {X A : CpxR} {Y : CpxRI}
    (φ : X ⟶ A)
    (f : ReduceCpx.obj A ⟶ Y) :
    restricted_chainMap_of_reduction_map (I := I) (PClass := PClass)
        (f := ReduceCpx.map φ ≫ f) =
      φ ≫ restricted_chainMap_of_reduction_map (I := I) (PClass := PClass) (f := f) := by
  -- Proof comment: equality of cochain maps is checked degreewise, where the component formula
  -- was isolated in the previous lemma.
  ext i
  simpa [restricted_chainMap_of_reduction_map] using
    restricted_component_of_reduction_map_comp
      (I := I) (φ := φ) (f := f) i

/-- Helper for Lemma 15.76.2: the quotient-to-restriction adapter is faithful on morphisms out of
`ReduceCpx.obj X`. -/
lemma restricted_chainMap_of_reduction_map_faithful
    {X : CpxR} {Y : CpxRI}
    {f g : ReduceCpx.obj X ⟶ Y}
    (hfg :
      restricted_chainMap_of_reduction_map (I := I) (PClass := PClass) (f := f) =
        restricted_chainMap_of_reduction_map (I := I) (PClass := PClass) (f := g)) :
    f = g := by
  ext i
  let q :
      X.X i ⟶ ModuleCat.of R (X.X i ⧸ (I • (⊤ : Submodule R (X.X i)))) :=
    ModuleCat.ofHom ((I • (⊤ : Submodule R (X.X i))).mkQ)
  have hq : Function.Surjective q.hom := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R (X.X i))) x
    exact ⟨y, rfl⟩
  letI : Epi q := (ModuleCat.epi_iff_surjective q).2 hq
  let e := reduceModI_obj_iso_quotient (I := I) (X.X i)
  have hcomp :
      restricted_component_of_reduction_map (I := I) (f := f) i =
        restricted_component_of_reduction_map (I := I) (f := g) i := by
    exact congrArg (fun η ↦ η.f i) hfg
  have hmap :
      RestrictModI.map (e.inv ≫ f.f i) =
        RestrictModI.map (e.inv ≫ g.f i) := by
    apply (cancel_epi q).1
    simpa [restricted_component_of_reduction_map, e] using hcomp
  have hred : e.inv ≫ f.f i = e.inv ≫ g.f i := by
    ext x
    exact congrArg (fun ζ ↦ ζ.hom x) hmap
  exact (cancel_mono e.inv).1 hred

/-- Helper for Lemma 15.76.2: the strict factorization over `R` recovers the source-faithful
reduction-side square over `R/I`. -/
lemma reduction_square_of_strict_factorization_through_cone_lift
    {E : CpxRI}
    {P A : CochainComplex.MinusWithTermsIn PClass}
    (δ : E ⟶ ReduceCpx.obj (P : CpxR))
    (eA : ReduceCpx.obj (A : CpxR) ≅ CochainComplex.mappingCone δ)
    (φ : (P : CpxR) ⟶ (A : CpxR))
    (hφα :
      φ ≫ restricted_chainMap_of_reduction_map
            (I := I) (PClass := PClass) (f := eA.hom) =
        restricted_chainMap_of_reduction_map
          (I := I) (PClass := PClass) (f := CochainComplex.mappingCone.inr δ)) :
    ReduceCpx.map φ ≫ eA.hom = CochainComplex.mappingCone.inr δ := by
  -- Proof comment: first rewrite the strict factorization as equality of the adapted restricted
  -- chain maps, then cancel the faithful quotient-to-restriction adapter.
  apply restricted_chainMap_of_reduction_map_faithful (I := I) (PClass := PClass)
  calc
    restricted_chainMap_of_reduction_map
        (I := I) (PClass := PClass) (f := ReduceCpx.map φ ≫ eA.hom) =
      φ ≫ restricted_chainMap_of_reduction_map
        (I := I) (PClass := PClass) (f := eA.hom) := by
          simpa using
            restricted_chainMap_of_reduction_map_comp
              (I := I) (PClass := PClass) φ eA.hom
    _ =
      restricted_chainMap_of_reduction_map
        (I := I) (PClass := PClass) (f := CochainComplex.mappingCone.inr δ) := hφα

/-- Helper for Lemma 15.76.2: once the reduction-side square is strict, reduction modulo `I`
identifies the cokernel of `φ` with the cokernel of the cone inclusion. -/
noncomputable lemma reduceCpx_cokernel_iso_of_factor_square
    {X Y : CpxR} {Z : CpxRI}
    (φ : X ⟶ Y)
    (e : ReduceCpx.obj Y ≅ Z)
    (g : ReduceCpx.obj X ⟶ Z)
    (hcomm : ReduceCpx.map φ ≫ e.hom = g) :
    ReduceCpx.obj (cokernel φ) ≅ cokernel g := by
  -- Proof comment: first use the preserved-cokernel comparison for `ReduceCpx`, then transport
  -- the target along the strict commutative square via `cokernel.mapIso`.
  exact
    PreservesCokernel.iso ReduceCpx φ ≪≫
      cokernel.mapIso (ReduceCpx.map φ) g (Iso.refl _) e (by simpa using hcomm)

/-- Helper for Lemma 15.76.2: a strict reduction square with the cone inclusion identifies each
reduced component of `φ` as a split monomorphism whose cokernel is the shifted source term of the
cone. -/
lemma reduced_component_splitMono_and_cokernel_iso_of_cone_square
    {E : CpxRI}
    {P A : CochainComplex.MinusWithTermsIn PClass}
    (δ : E ⟶ ReduceCpx.obj (P : CpxR))
    (eA : ReduceCpx.obj (A : CpxR) ≅ CochainComplex.mappingCone δ)
    (φ : (P : CpxR) ⟶ (A : CpxR))
    (hsquare : ReduceCpx.map φ ≫ eA.hom = CochainComplex.mappingCone.inr δ)
    (i : ℤ) :
    IsSplitMono (ReduceModI.map (φ.f i)) ∧
      cokernel (ReduceModI.map (φ.f i)) ≅ E.X (i + 1) := by
  have hcomp :
      ReduceModI.map (φ.f i) ≫ eA.hom.f i = (CochainComplex.mappingCone.inr δ).f i := by
    -- Proof comment: the strict square is already known on complexes, so evaluating at degree
    -- `i` gives the exact component comparison needed here.
    simpa [ReduceCpx] using congrArg (fun ζ ↦ ζ.f i) hsquare
  let coneRetraction :
      (CochainComplex.mappingCone δ).X i ⟶ (ReduceCpx.obj (P : CpxR)).X i := by
    -- Proof comment: degree `i` of the cone is a biproduct, and `mappingCone.inr` is the second
    -- coprojection, so the second projection is a retraction.
    simpa using
      (biprod.snd :
        E.X (i + 1) ⊞ (ReduceCpx.obj (P : CpxR)).X i ⟶
          (ReduceCpx.obj (P : CpxR)).X i)
  have hsplit :
      IsSplitMono (ReduceModI.map (φ.f i)) := by
    -- Proof comment: transport the explicit retraction of the cone inclusion back across the
    -- isomorphism component `eA.hom.f i`.
    refine IsSplitMono.mk' ⟨eA.hom.f i ≫ coneRetraction, ?_⟩
    calc
      ReduceModI.map (φ.f i) ≫ (eA.hom.f i ≫ coneRetraction) =
          (ReduceModI.map (φ.f i) ≫ eA.hom.f i) ≫ coneRetraction := by simp [Category.assoc]
      _ = (CochainComplex.mappingCone.inr δ).f i ≫ coneRetraction := by rw [hcomp]
      _ = 𝟙 _ := by
        -- The chosen retraction is exactly the projection splitting the cone inclusion.
        simp [coneRetraction]
  let ecokerComp :
      cokernel (ReduceModI.map (φ.f i)) ≅ cokernel ((CochainComplex.mappingCone.inr δ).f i) :=
    cokernel.mapIso
      (ReduceModI.map (φ.f i))
      ((CochainComplex.mappingCone.inr δ).f i)
      (Iso.refl _)
      (asIso (eA.hom.f i))
      hcomp
  -- Proof comment: after identifying the targets through `eA`, the component cokernel is the
  -- standard cokernel of the cone inclusion, which was computed earlier.
  exact ⟨hsplit, ecokerComp ≪≫ mappingCone_inr_f_cokernel_iso (I := I) δ i⟩

/-- Helper for Lemma 15.76.2: if a map in `PClass` splits as a monomorphism, then its cokernel
again lies in `PClass`. -/
lemma module_class_of_cokernel_of_split_mono
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    {P₁ P₂ : ModR} (f : P₁ ⟶ P₂)
    (hP₁ : PClass P₁) (hP₂ : PClass P₂)
    [IsSplitMono f] :
    PClass (cokernel f) := by
  let r : P₂ ⟶ P₁ := @retraction _ _ _ _ f inferInstance
  have hrf : f ≫ r = 𝟙 P₁ := by
    simpa [r] using IsSplitMono.id f
  have hsurj_r : Function.Surjective r.hom := by
    intro x
    refine ⟨f.hom x, ?_⟩
    exact congrArg (fun ζ ↦ ζ.hom x) hrf
  have hker : PClass (kernel r) := by
    -- Proof comment: the retraction `r` is surjective onto the projective source `P₁`, so the
    -- kernel of `r` is a direct summand of `P₂` and remains in `PClass`.
    exact module_class_of_kernel_of_surjective_to_projective
      PClass hprojective r hP₂ hP₁ hsurj_r
  have hπker_condition : (𝟙 P₂ - r ≫ f) ≫ r = 0 := by
    -- Proof comment: `1 - r ≫ f` lands in the kernel because `f ≫ r = 1`.
    calc
      (𝟙 P₂ - r ≫ f) ≫ r = r - r ≫ f ≫ r := by simp [sub_comp, Category.assoc]
      _ = 0 := by
        rw [hrf]
        simp [Category.assoc]
  let πker : P₂ ⟶ kernel r :=
    kernel.lift r (𝟙 P₂ - r ≫ f) hπker_condition
  have hπker_f : f ≫ πker = 0 := by
    -- Proof comment: the complement projection kills the image of the split mono.
    apply kernel.hom_ext
    calc
      f ≫ πker ≫ kernel.ι r = f ≫ (𝟙 P₂ - r ≫ f) := by simp [πker, Category.assoc]
      _ = 0 := by
        rw [comp_sub, Category.assoc, hrf]
        simp
  let cofork : CokernelCofork f := CokernelCofork.ofπ πker hπker_f
  have hπker_ι : πker ≫ kernel.ι r = 𝟙 P₂ - r ≫ f := by
    simp [πker]
  have hι_πker : kernel.ι r ≫ πker = 𝟙 (kernel r) := by
    -- Proof comment: on the kernel summand, the complement projection acts by the identity.
    apply kernel.hom_ext
    calc
      kernel.ι r ≫ πker ≫ kernel.ι r =
          kernel.ι r ≫ (𝟙 P₂ - r ≫ f) := by simp [πker, Category.assoc]
      _ = kernel.ι r := by
        rw [comp_sub, Category.assoc]
        have hzero : kernel.ι r ≫ r = 0 := kernel.condition r
        rw [hzero]
        simp
  have hcofork : IsColimit cofork := by
    refine Cofork.IsColimit.mk cofork
      (fun s ↦ kernel.ι r ≫ s.π)
      ?_
      ?_
    · intro s
      calc
        πker ≫ kernel.ι r ≫ s.π = (𝟙 P₂ - r ≫ f) ≫ s.π := by
          rw [hπker_ι]
        _ = s.π := by
          rw [sub_comp, Category.assoc, s.condition]
          simp
    · intro s m hm
      calc
        m = (kernel.ι r ≫ πker) ≫ m := by rw [hι_πker]; simp
        _ = kernel.ι r ≫ s.π := by rw [hm]
  let ecoker : cokernel f ≅ kernel r :=
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel f) hcofork
  -- Proof comment: the cokernel is canonically identified with the kernel complement cut out by
  -- the retraction.
  exact PClass.prop_of_iso ecoker hker

/-- Lemma 15.76.2: let `R` be a ring, let `I ⊆ R` be an ideal, and let `PClass` be a class of
`R`-modules satisfying the projectivity, direct-sum closure, retract-stability/direct-summand
closure, and surjectivity-modulo-`I` hypotheses. If `E^•` is a bounded-above complex of
`R/I`-modules representing `K ⊗_R^{\mathbf L} R/I`, and if `K` admits a bounded-above
representative with terms in `PClass`, then there exists a bounded-above complex `P^•` with terms
in `PClass` which represents `K` in `D(R)` and whose reduction modulo `I` is isomorphic to
`E^•`. -/
theorem exists_boundedAbove_representative_lifting_derivedReduction
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsClosedUnderBinaryCoproducts]
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective ((ReduceModI.map f).hom) →
      Function.Surjective f.hom)
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn PClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hKrep : ∃ P : CochainComplex.MinusWithTermsIn PClass,
      K ≅ DerivedCategory.Q.obj (P : CpxR)) :
    ∃ P : CochainComplex.MinusWithTermsIn PClass,
      (K ≅ DerivedCategory.Q.obj (P : CpxR)) ×
        (ReduceModI.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P : CpxR) ≅ (E : CpxRI) := by
  obtain ⟨P₀, eK₀⟩ := hKrep
  let Eproj : CochainComplex.ProjectiveMinus ModRI :=
    reduced_complex_projectiveMinus (I := I) (PClass := PClass) hprojective E
  have hReduction :
      (K ⊗[R]^L[(R ⧸ I)]) ≅
        DerivedCategory.Q.obj (ReduceCpx.obj (P₀ : CpxR)) :=
    derived_reduction_iso_of_representative
      (I := I) (PClass := PClass) hprojective K P₀ eK₀
  obtain ⟨hErep⟩ := hErep
  let hComparison :
      DerivedCategory.Q.obj (E : CpxRI) ≅
        DerivedCategory.Q.obj (ReduceCpx.obj (P₀ : CpxR)) :=
    hErep.symm ≪≫ hReduction
  obtain ⟨δ, hδ, _hQδ⟩ :=
    exists_quasiIso_of_projective_representative_comparison
      (I := I) Eproj hComparison
  let _ : QuasiIso δ := hδ
  -- Route correction: the source-faithful proof is now back on the Stacks path. We have the
  -- strict quasi-isomorphism `δ : E ⟶ ReduceCpx.obj P₀`; the remaining work is the cone lift from
  -- Lemma `15.76.1`, the degreewise split-mono upgrade of the lifted map, and the shifted
  -- cokernel identification.
  let Cowner : CochainComplex.MinusWithTermsIn PClassModI :=
    mappingCone_minusWithTermsIn_of_module_class
      (I := I) (PClass := PClass) E P₀ δ
  have hConeAcyclic : (Cowner : CpxRI).Acyclic := by
    -- Proof comment: the cone on the strict comparison `δ` is acyclic, exactly as in the source.
    change (CochainComplex.mappingCone δ).Acyclic
    exact mappingCone_acyclic_of_quasiIso_local (I := I) δ
  obtain ⟨A, eA, hAacyclic⟩ :=
    exists_boundedAbove_acyclic_lift_of_module_class
      (I := I) PClass hprojective hsurj Cowner hConeAcyclic
  let ResC : CpxR := RestrictCpx.obj (CochainComplex.mappingCone δ)
  let α : (A : CpxR) ⟶ ResC :=
    restricted_chainMap_of_reduction_map
      (I := I) (PClass := PClass) (f := eA.hom)
  have hα_epi : ∀ i : ℤ, Epi (α.f i) := by
    intro i
    -- Proof comment: each component is the quotient map followed by the restricted image of the
    -- degreewise isomorphism from `eA`.
    simpa [α, restricted_chainMap_of_reduction_map] using
      restricted_mappingCone_quotient_component_epi
        (I := I) (PClass := PClass) δ A eA i
  let γ : (P₀ : CpxR) ⟶ ResC :=
    restricted_chainMap_of_reduction_map
      (I := I) (PClass := PClass) (f := CochainComplex.mappingCone.inr δ)
  have hResCAcyclic : ResC.Acyclic := by
    -- Proof comment: `ResC` is the restricted cone on the strict quasi-isomorphism `δ`.
    simpa [ResC] using
      restricted_mappingCone_acyclic (I := I) (PClass := PClass) (P := P₀) δ
  have hα_quasiIso : QuasiIso α := by
    -- Proof comment: both the source and the target of `α` are acyclic, so every induced
    -- homology map is an isomorphism between zero objects.
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hsource : IsZero ((A : CpxR).homology i) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hAacyclic i
    have htarget : IsZero (ResC.homology i) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hResCAcyclic i
    exact IsZero.isIso hsource htarget (HomologicalComplex.homologyMap α i)
  let P₀proj : CochainComplex.ProjectiveMinus ModR :=
    ⟨⟨(P₀ : CpxR), P₀.minus⟩, fun i ↦ hprojective (P₀.term_mem i)⟩
  let _ : QuasiIso α := hα_quasiIso
  obtain ⟨φ, hφα⟩ :=
    CochainComplex.exists_strict_factor_through_termwiseEpi_quasiIso_from_boundedAbove_projective
      P₀proj α γ hα_epi
  have hsquare :
      ReduceCpx.map φ ≫ eA.hom = CochainComplex.mappingCone.inr δ := by
    -- Proof comment: the strict lift over `R` determines the exact reduction square over `R/I`
    -- through the faithful adapter proved above.
    exact reduction_square_of_strict_factorization_through_cone_lift
      (I := I) (PClass := PClass) δ eA φ hφα
  let ecoker :
      ReduceCpx.obj (cokernel φ) ≅ cokernel (CochainComplex.mappingCone.inr δ) :=
    reduceCpx_cokernel_iso_of_factor_square
      (I := I) (φ := φ) (e := eA) (g := CochainComplex.mappingCone.inr δ) hsquare
  have hReducedComponent :
      ∀ i : ℤ, IsSplitMono (ReduceModI.map (φ.f i)) ∧
        cokernel (ReduceModI.map (φ.f i)) ≅ E.X (i + 1) := by
    intro i
    -- Proof comment: the strict reduction square from the source-faithful cone lift has now been
    -- reduced to the degreewise split-mono/cokernel statement needed for the final module lemma.
    exact reduced_component_splitMono_and_cokernel_iso_of_cone_square
      (I := I) (PClass := PClass) δ eA φ hsquare i
  --
  -- TODO: upgrade the degreewise cone-cokernel identification to a complex isomorphism
  -- `cokernel (CochainComplex.mappingCone.inr δ) ≅ (E : CpxRI)⟦(1 : ℤ)⟧`, then transport `ecoker`
  -- across that shift and apply the source module-theoretic split-mono/cokernel argument to the
  -- already prepared degreewise data `hReducedComponent`.
  let _ := ResC
  let _ := α
  let _ := hα_epi
  let _ := γ
  let _ := hResCAcyclic
  let _ := hα_quasiIso
  let _ := P₀proj
  let _ := φ
  let _ := hφα
  let _ := hsquare
  let _ := ecoker
  let _ := eA
  let _ := hAacyclic
  let _ := hReducedComponent
  sorry

end

end CategoryTheory
