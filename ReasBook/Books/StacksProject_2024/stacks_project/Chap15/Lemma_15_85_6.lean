import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_7_Leray_s_acyclicity_lemma
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_85_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_9

noncomputable section

open ComplexShape
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
local notation "KModR" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)
local notation "QisR" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
private abbrev extCpx : CpxR ⥤ CpxR' :=
  (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (up ℤ)
local notation "ExtCpx" => (extCpx : CpxR ⥤ CpxR')

/- Domain-style sampling for Lemma 15.85.6:
- primary domain: derived base change for two-term representatives in `D(R)`;
- sampled owner declarations:
  `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`,
  `DerivedCategory.TStructure.t.truncGE`, `Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing datum is the chosen two-term representative `P` of
  `K`, while the core/canonical owners are `IsTwoTermRepresentative`, `K ⊗[R]^L[R']`, and
  `t.truncGE (-1)`;
- primitive vs. derived:
  primitive data are the representative `P` and the flatness of its degree-zero term;
  the scalar-extended complex `ExtCpx.obj P` is only the canonical bridge/view from cochain-level
  base change back to the owner predicate on the truncation target;
- source/core/bridge triage:
  `source-facing`: the statement that two-term representatives stay two-term after flat base
  change and truncation;
  `core/canonical`: `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`, and `t.truncGE`;
  `bridge/view`: the cochain-level scalar extension `ExtCpx.obj P`.

Accordingly, the theorem remains in the owner namespace `IsTwoTermRepresentative` and uses the
imported scalar-extension owner `ExtCpx` directly, rather than introducing a parallel wrapper or
weakening the result to a bare isomorphism statement. -/

-- Proof sketch: write `P` as a two-term complex `P⁻¹ → P⁰` with `P⁰` flat. Tensor the
-- distinguished triangle `P⁰ → P → P⁻¹[1] → P⁰[1]` with `R'`. The flatness of `P⁰` identifies
-- its ordinary tensor product with the derived tensor product, and the degree-support hypothesis
-- on `P` already forces the same cohomological support for `K`, so the scalar-extended complex is
-- concentrated in degrees `-1` and `0`. The induced comparison to `K ⊗[R]^L[R']` is therefore
-- an isomorphism on homology in degrees `≥ -1`, so the scalar-extended complex computes the
-- upper truncation `τ_{\ge -1}` and remains a two-term representative there.
namespace IsTwoTermRepresentative

/-- Helper for Lemma 15.85.6: cochain-level scalar extension preserves the lower support bound
`IsStrictlyGE (-1)`. -/
private theorem extendScalars_preserves_isStrictlyGE
    (P : CpxR) (hP : P.IsStrictlyGE (-1)) :
    ((ExtCpx).obj P).IsStrictlyGE (-1) := by
  -- The lower support statement is checked degreewise and transported through
  -- `ModuleCat.extendScalars` via `Functor.map_isZero`.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  simpa using
    (ModuleCat.extendScalars (algebraMap R R')).map_isZero
      (P.isZero_of_isStrictlyGE (-1) i hi)

/-- Helper for Lemma 15.85.6: cochain-level scalar extension preserves the upper support bound
`IsStrictlyLE 0`. -/
private theorem extendScalars_preserves_isStrictlyLE
    (P : CpxR) (hP : P.IsStrictlyLE 0) :
    ((ExtCpx).obj P).IsStrictlyLE 0 := by
  -- The upper support statement is proved in the same degreewise way.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  simpa using
    (ModuleCat.extendScalars (algebraMap R R')).map_isZero
      (P.isZero_of_isStrictlyLE 0 i hi)

/-- Helper for Lemma 15.85.6: scalar extension preserves support in the two-term window
`[-1, 0]`. -/
private theorem extendScalars_preserves_two_term_support
    (P : CpxR) (hGE : P.IsStrictlyGE (-1)) (hLE : P.IsStrictlyLE 0) :
    ((ExtCpx).obj P).IsStrictlyGE (-1) ∧ ((ExtCpx).obj P).IsStrictlyLE 0 := by
  -- Package the separate lower and upper support bounds for later reuse.
  exact
    ⟨extendScalars_preserves_isStrictlyGE (R := R) (R' := R') P hGE,
      extendScalars_preserves_isStrictlyLE (R := R) (R' := R') P hLE⟩

/-- Helper for Lemma 15.85.6: the homotopy-to-derived scalar-extension bridge used to build the
canonical comparison map to the underived scalar-extended complex. -/
private noncomputable abbrev extendScalarsHomotopyToDerived :
    KModR ⥤ DModR' :=
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).left_adjoint_additive
  mapHomotopyCategoryToDerived F

/-- Helper for Lemma 15.85.6: the homotopy-to-derived scalar-extension bridge admits the expected
total left derived functor. -/
private theorem extendScalarsHomotopyToDerived_hasLeftDerivedFunctor :
    (extendScalarsHomotopyToDerived (R := R) (R' := R') :
      KModR ⥤ DModR').HasLeftDerivedFunctor QisR := by
  -- This is exactly the chapter owner theorem for derived scalar extension.
  simpa [extendScalarsHomotopyToDerived, mapHomotopyCategoryToDerived] using
    (extendScalarsToDerived_hasLeftDerivedFunctor (R := R) (A := R') (algebraMap R R') :
      (extendScalarsHomotopyToDerived (R := R) (R' := R') :
        KModR ⥤ DModR').HasLeftDerivedFunctor QisR)

/-- Helper for Lemma 15.85.6: once the scalar-extended complex is still supported in degrees
`≥ -1`, its image in the derived category lies in `D^{≥ -1}`. -/
private theorem derivedCategory_Q_obj_extCpx_isGE_of_isStrictlyGE
    (P : CpxR) [P.IsStrictlyGE (-1)] :
    DerivedCategory.IsGE (DerivedCategory.Q.obj ((ExtCpx).obj P)) (-1) := by
  -- Translate the cochain-level support bound to the standard t-structure bound on `Q.obj`.
  rw [DerivedCategory.isGE_Q_obj_iff]
  infer_instance

/-- Helper for Lemma 15.85.6: in a cochain complex supported in degrees `≥ -1`, the only
incoming differential to degree `-1` vanishes, so `H^{-1}` is the kernel of `d^{-1}`. -/
private noncomputable def two_term_cycles_negOne_iso_kernel
    (P : CpxR) :
    P.cycles (-1) ≅ ModuleCat.of R (LinearMap.ker ((P.d (-1) 0).hom)) := by
  let hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
    simpa using (CochainComplex.prev ℤ (-1))
  let hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
    simpa using (CochainComplex.next ℤ (-1))
  let T : ShortComplex (ModuleCat R) := P.sc' (-2) (-1) 0
  let eShortKernel :
      T.cycles ≅ ModuleCat.of R (LinearMap.ker ((P.d (-1) 0).hom)) := by
    -- On the owner short complex, cycles are exactly the kernel of the outgoing differential.
    simpa [T, hnext] using
      (T.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer T.g)
  -- First move the ambient cycle object to the owner short complex, then identify its kernel.
  exact (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext) ≪≫ eShortKernel

/-- Helper for Lemma 15.85.6: the degree-`-1` cycles-to-kernel identification is characterized
by the ambient cycle inclusion. -/
private theorem two_term_cycles_negOne_iso_kernel_hom_comp_subtype
    (P : CpxR) :
    (two_term_cycles_negOne_iso_kernel (R := R) (P := P)).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
        P.iCycles (-1) := by
  let hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
    simpa using (CochainComplex.prev ℤ (-1))
  let hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
    simpa using (CochainComplex.next ℤ (-1))
  let T : ShortComplex (ModuleCat R) := P.sc' (-2) (-1) 0
  -- Route correction: compare both maps after rewriting through the owner short complex `T`,
  -- where `cyclesIsoKernel` and `kernelIsoKer` expose the concrete kernel inclusion.
  calc
    (two_term_cycles_negOne_iso_kernel (R := R) (P := P)).hom ≫
        ModuleCat.ofHom (LinearMap.ker ((P.d (-1) 0).hom)).subtype =
      (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext).hom ≫ T.iCycles := by
        simp [two_term_cycles_negOne_iso_kernel, T, Category.assoc, hnext]
    _ = P.iCycles (-1) := by
        simpa [T] using
          P.cyclesIsoSc'_hom_iCycles (-2) (-1) 0 hprev hnext

/-- Helper for Lemma 15.85.6: in a cochain complex supported in degrees `≥ -1`, the only
incoming differential to degree `-1` vanishes, so `H^{-1}` is the kernel of `d^{-1}`. -/
private noncomputable def two_term_homology_negOne_iso_kernel
    (P : CpxR) [P.IsStrictlyGE (-1)] :
    P.homology (-1) ≅ ModuleCat.of R (LinearMap.ker ((P.d (-1) 0).hom)) := by
  have hzero_prev : P.d (-2) (-1) = 0 := by
    -- Below degree `-1`, the source term is zero, so the predecessor differential vanishes.
    exact (P.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _
  let eHomology :
      P.homology (-1) ≅ P.cycles (-1) :=
    (P.isoHomologyπ (-2) (-1) (by simp) hzero_prev).symm
  -- First identify homology with cycles, then replace cycles by the concrete kernel module.
  exact eHomology ≪≫ two_term_cycles_negOne_iso_kernel (R := R) (P := P)

/-- Helper for Lemma 15.85.6: in a cochain complex supported in degrees `≤ 0`, the opcycles in
degree `0` are the cokernel of `d^{-1}`. -/
private noncomputable def two_term_opcycles_zero_iso_cokernel
    (P : CpxR) :
    P.opcycles 0 ≅ cokernel (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Compare the owner opcycle cokernel with the categorical cokernel of `d^{-1}`.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (P.d (-1) 0))
      hOpcycles).symm

/-- Helper for Lemma 15.85.6: the degree-`0` opcycles-to-cokernel identification is
characterized by the ambient quotient map `pOpcycles`. -/
private theorem pOpcycles_comp_two_term_opcycles_zero_iso_cokernel_hom
    (P : CpxR) :
    P.pOpcycles 0 ≫ (two_term_opcycles_zero_iso_cokernel (R := R) (P := P)).hom =
      cokernel.π (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Both cokernel presentations represent the same cofork, so the comparison iso carries the
  -- owner projection `pOpcycles` to the categorical cokernel projection.
  simpa [two_term_opcycles_zero_iso_cokernel, hOpcycles] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      hOpcycles
      (cokernelIsCokernel (P.d (-1) 0))
      WalkingParallelPair.one

/-- Helper for Lemma 15.85.6: in a cochain complex supported in degrees `≤ 0`, the outgoing
differential from degree `0` vanishes, so `H^0` is the cokernel of `d^{-1}`. -/
private noncomputable def two_term_homology_zero_iso_cokernel
    (P : CpxR) [P.IsStrictlyGE (-1)] (hLE : P.IsStrictlyLE 0) :
    P.homology 0 ≅ cokernel (P.d (-1) 0) := by
  letI : P.IsStrictlyLE 0 := hLE
  have hzero_next : P.d 0 1 = 0 := by
    -- Above degree `0`, the target term is zero, so the outgoing differential vanishes.
    exact (P.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  let eHomology :
      P.homology 0 ≅ P.opcycles 0 :=
    P.isoHomologyι 0 1 (by simp) hzero_next
  -- First identify homology with the opcycle cokernel, then rewrite that cokernel to `d^{-1}`.
  exact eHomology ≪≫ two_term_opcycles_zero_iso_cokernel (R := R) (P := P)

/-- Helper for Lemma 15.85.6: after extending scalars, the only potentially nonzero differential
of a two-term cochain complex is the scalar extension of the original degree `-1 → 0`
differential. -/
private theorem extCpx_d_negOne_zero_eq_baseChange
    (P : CpxR) :
    (((ExtCpx).obj P).d (-1) 0).hom =
      LinearMap.baseChange R' ((P.d (-1) 0).hom) := by
  -- This is the definitional description of `mapHomologicalComplex` for `extendScalars`.
  rfl

/-- Helper for Lemma 15.85.6: ordinary scalar extension carries the categorical cokernel of a
module map to the cokernel of the base-changed map. -/
private noncomputable def cokernel_baseChange_iso
    {M₁ M₀ : ModuleCat R} (d : M₁ ⟶ M₀) :
    (ModuleCat.extendScalars (algebraMap R R')).obj (cokernel d) ≅
      cokernel (ModuleCat.ofHom (LinearMap.baseChange R' d.hom)) := by
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (F.map (cokernel.π d))
          (by
            simpa using congrArg F.map (cokernel.condition d))) := by
    -- Scalar extension is a left adjoint, hence preserves the cokernel cofork of `d`.
    exact isColimitOfHasCokernelOfPreservesColimit F d
  -- Compare the transported cokernel cofork with the categorical cokernel of `d.baseChange`.
  exact
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (ModuleCat.ofHom (LinearMap.baseChange R' d.hom)))
      hColim

/-- Helper for Lemma 15.85.6: the scalar-extension cokernel comparison carries the transported
quotient map to the categorical quotient map of the base-changed differential. -/
private theorem cokernel_baseChange_iso_inv_π
    {M₁ M₀ : ModuleCat R} (d : M₁ ⟶ M₀) :
    (ModuleCat.extendScalars (algebraMap R R')).map (cokernel.π d) ≫
        (cokernel_baseChange_iso (R := R) (R' := R') d).inv =
      cokernel.π (ModuleCat.ofHom (LinearMap.baseChange R' d.hom)) := by
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let hColim :
      IsColimit
        (CokernelCofork.ofπ
          (F.map (cokernel.π d))
          (by
            simpa using congrArg F.map (cokernel.condition d))) := by
    -- Reuse the preserved cokernel cofork from `cokernel_baseChange_iso`.
    exact isColimitOfHasCokernelOfPreservesColimit F d
  -- The inverse comparison sends the transported cokernel projection to the target cokernel
  -- projection.
  simpa [cokernel_baseChange_iso, hColim] using
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (cokernelIsCokernel (ModuleCat.ofHom (LinearMap.baseChange R' d.hom)))
      hColim
      WalkingParallelPair.one

/-- Helper for Lemma 15.85.6: if the original two-term model is supported in degrees `≤ 0`, then
its derived scalar extension also stays in `D^{≤ 0}`. -/
private theorem derivedTensorWithAlgebra_Q_obj_isLE_of_isStrictlyLE
    (P : CpxR) (hLE : P.IsStrictlyLE 0) :
    DerivedCategory.IsLE
      ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) 0 := by
  -- First place the chosen model `P` itself in `D^{≤ 0}`, then use the existing right
  -- t-exactness instance for derived scalar extension.
  letI : DerivedCategory.IsLE (DerivedCategory.Q.obj P) 0 := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    exact hLE
  infer_instance

/-- Helper for Lemma 15.85.6: the canonical counit comparison from derived scalar extension of a
cochain model to the ordinary scalar-extended cochain model. -/
private noncomputable def derivedTensorWithAlgebra_complex_comparison
    (P : CpxR) :
    ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((ExtCpx).obj P) :=
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).left_adjoint_additive
  letI :
      (extendScalarsHomotopyToDerived (R := R) (R' := R') :
        KModR ⥤ DModR').HasLeftDerivedFunctor QisR :=
    extendScalarsHomotopyToDerived_hasLeftDerivedFunctor (R := R) (R' := R')
  (derivedTensorWithAlgebra (algebraMap R R')).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app P).inv ≫
    ((extendScalarsHomotopyToDerived (R := R) (R' := R')).totalLeftDerivedCounit QhR QisR).app
      ((HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj P) ≫
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat R') (up ℤ) ⥤ DModR').map
      ((Functor.mapHomotopyCategoryFactors
        F (up ℤ)).inv.app P) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat R')).app
      ((ExtCpx).obj P)).hom

/-- Helper for Lemma 15.85.6: a zero object of `ModuleCat R` is flat. -/
private theorem flat_of_isZero_moduleCat_local
    (M : ModuleCat R) (hM : IsZero M) :
    Module.Flat R M := by
  -- Proof comment: every zero object is linearly equivalent to the literal zero module, which is
  -- flat by the standard free-module instance.
  let Z : ModuleCat R := ModuleCat.of R PUnit
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  letI : Subsingleton ↥Z := ModuleCat.subsingleton_of_isZero hZ
  letI : Module.Free R ↥Z := Module.Free.of_subsingleton (R := R) (N := ↥Z)
  let _ : Module.Flat R Z := Module.Flat.of_free
  let e : M ≅ Z := hM.iso hZ
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.85.6: on a degree-zero single complex, the canonical comparison
`Q(single₀ M) ≅ M[0]` induces the identity on zeroth homology. -/
private theorem homology_map_singleFunctorIsoCompQ_app_zero_eq_id
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    (DerivedCategory.homologyFunctor (ModuleCat S) (0 : ℤ)).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M).hom) =
      𝟙 _ := by
  -- Proof comment: the degree-zero component of `singleFunctorIsoCompQ` is definitionally the
  -- identity on the derived single object, so `H⁰` also sees the identity map.
  change
    (DerivedCategory.homologyFunctor (ModuleCat S) (0 : ℤ)).map
        (𝟙 (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M))) =
      𝟙 _
  simp

/-- Helper for Lemma 15.85.6: after identifying `Q(single₀ M)` with `M[0]`, the remaining
zeroth-homology tail is exactly the standard `H⁰(single₀ M) ≅ M` owner map. -/
private theorem homology_single_zero_transport_comp_eq
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    (DerivedCategory.homologyFunctor (ModuleCat S) (0 : ℤ)).map
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M).hom) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) (0 : ℤ)).app M).hom =
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) (0 : ℤ)).app M).hom := by
  -- Proof comment: once the first factor is the identity on `H⁰`, the composite reduces to the
  -- owner `singleFunctorCompHomologyFunctorIso` itself.
  rw [homology_map_singleFunctorIsoCompQ_app_zero_eq_id]
  simp

/-- Helper for Lemma 15.85.6: unfolding the owner degree-zero single-complex comparison exposes
the explicit `homologyFunctorFactors` tail followed by the chain-level
`singleObjHomologySelfIso`. -/
private theorem singleFunctorCompHomologyFunctorIso_app_zero_owner_formula
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) (0 : ℤ)).app M).hom =
      (DerivedCategory.homologyFunctor (ModuleCat S) 0).map
        (𝟙 (((DerivedCategory.singleFunctors (ModuleCat S)).functor (0 : ℤ)).obj M)) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) 0).hom.app
        (((CochainComplex.singleFunctors (ModuleCat S)).functor (0 : ℤ)).obj M)) ≫
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  -- Proof comment: unfold the owner composite once; the degree-zero postcomposition comparison is
  -- the identity, so only the homology-factor comparison and the chain-level `H⁰(single₀ M) ≅ M`
  -- tail remain.
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso_hom_app_zero_eq_id]
  let α :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat S) 0).hom.app
      (((CochainComplex.singleFunctors (ModuleCat S)).functor (0 : ℤ)).obj M))
  let β :=
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℤ) (0 : ℤ) M).hom
  have hmap :
      (DerivedCategory.homologyFunctor (ModuleCat S) 0).map
          (𝟙 (((DerivedCategory.singleFunctors (ModuleCat S)).functor (0 : ℤ)).obj M)) =
        𝟙 _ := by
    simp
  -- Rebracket the remaining identity leg into the advertised owner normal form.
  refine (congrArg (fun t ↦ t ≫ α ≫ β) hmap).trans ?_
  calc
    𝟙 _ ≫ α ≫ β = (𝟙 _ ≫ α) ≫ β := by simp
    _ = α ≫ β := by simp [α, β]

/-- Helper for Lemma 15.85.6: after unfolding the degree-zero single-complex comparison, the
residual derived `H⁰` tail cancels to the chain-level `singleObjHomologySelfIso`. -/
private theorem single_zero_h0_tail_eq_singleObjHomologySelfIso
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    ((DerivedCategory.homologyFunctorFactors (ModuleCat S) 0).inv.app
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M)) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat S) (0 : ℤ)).app
        M).hom =
      (HomologicalComplex.singleObjHomologySelfIso
        (ComplexShape.up ℤ) (0 : ℤ) M).hom := by
  -- Proof comment: first expose the owner formula for
  -- `singleFunctorCompHomologyFunctorIso.app`; the middle factor is then `H⁰` applied to the
  -- identity, so `homologyFunctorFactors` cancels immediately.
  rw [singleFunctorCompHomologyFunctorIso_app_zero_owner_formula]
  simpa [Functor.map_id, Category.assoc] using
    (((DerivedCategory.homologyFunctorFactors (ModuleCat S) 0).app
      ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M)).inv_hom_id_assoc
        ((HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.up ℤ) (0 : ℤ) M).hom))

/-- Helper for Lemma 15.85.6: the zeroth homology of the derived image of a degree-zero single
complex is canonically the original module. -/
private noncomputable def derived_single_zero_homology_zero_iso
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    ((DerivedCategory.homologyFunctor (ModuleCat S) (0 : ℤ)).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M))) ≅
      M :=
  -- Proof comment: first pass from derived homology to the cochain-model homology, then use the
  -- standard degree-zero single-complex identification.
  (DerivedCategory.homologyFunctorFactors (ModuleCat S) (0 : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M) ≪≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) M)

/-- Helper for Lemma 15.85.6: shifting a degree-zero single complex by `1` transports its
degree-`-1` homology back to the underlying module. -/
private noncomputable def derived_shifted_single_zero_homology_negOne_iso
    {S : Type u} [CommRing S] (M : ModuleCat S) :
    ((DerivedCategory.homologyFunctor (ModuleCat S) (-1 : ℤ)).obj
        ((DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M))⟦(1 : ℤ)⟧)) ≅
      M :=
  -- Proof comment: rewrite `H^{-1}` of the shift to `H⁰` of the unshifted single complex, then
  -- apply the canonical degree-zero identification above.
  (((DerivedCategory.homologyFunctor (ModuleCat S) (0 : ℤ)).shiftIso
      (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by omega)).app
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M))) ≪≫
    derived_single_zero_homology_zero_iso M

/-- Helper for Lemma 15.85.6: the raw counit comparison is an isomorphism for a degree-zero
single complex on a flat module. -/
private theorem single_zero_complex_comparison_isIso_of_flat
    (M : ModuleCat R) [Module.Flat R M] :
    IsIso
      (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R')
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) := by
  let E : CpxR := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M
  let F : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  letI : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).left_adjoint_additive
  let G : KModR ⥤ DModR' := F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh
  let qE : KModR := (HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj E
  letI : G.HasLeftDerivedFunctor QisR := by
    change
      ((ModuleCat.extendScalars (algebraMap R R')).mapHomotopyCategory (up ℤ) ⋙
        DerivedCategory.Qh).HasLeftDerivedFunctor QisR
    simpa using
      extendScalarsToDerived_hasLeftDerivedFunctor (R := R) (A := R') (algebraMap R R')
  have hEFlat : E.IsTermwiseFlat := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa using (inferInstance : Module.Flat R M)
    · have hzero : IsZero (E.X i) := by
        simpa [E] using
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i hi)
      exact flat_of_isZero_moduleCat_local (R := R) (E.X i) hzero
  have hELE : E.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simpa [E] using
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M i (by omega))
  letI : E.IsKFlat := by
    let hminus : CochainComplex.minus (ModuleCat R) E :=
      (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨0, hELE⟩
    exact CochainComplex.isKFlat_of_boundedAbove_of_flat E hminus hEFlat
  letI : G.ComputesLeftDerivedAt QisR qE := by
    infer_instance
  letI : IsIso ((G.totalLeftDerivedCounit QhR QisR).app qE) :=
    (Functor.computesLeftDerivedAt_iff (F := G) (S := QisR) (X := qE)).1 inferInstance
  -- The remaining factors in the raw counit comparison are the canonical quotient and
  -- homotopy-factor comparison isomorphisms.
  simpa [E, G, F, qE, derivedTensorWithAlgebra_complex_comparison]

/-- Helper for Lemma 15.85.6: because the ordinary scalar-extended complex already lies in
`D^{≥ -1}`, the canonical counit comparison factors through `τ_{\ge -1}`. -/
private noncomputable def derivedTensorWithAlgebra_truncGE_comparison
    (P : CpxR) [P.IsStrictlyGE (-1)] :
    (t.truncGE (-1)).obj
        ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((ExtCpx).obj P) :=
  letI : ((ExtCpx).obj P).IsStrictlyGE (-1) :=
    extendScalars_preserves_isStrictlyGE (R := R) (R' := R') P inferInstance
  letI :
      DerivedCategory.IsGE (DerivedCategory.Q.obj ((ExtCpx).obj P)) (-1) :=
    derivedCategory_Q_obj_extCpx_isGE_of_isStrictlyGE (R := R) (R' := R') P
  t.descTruncGE
    (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)
    (-1)

/-- Helper for Lemma 15.85.6: after composing the truncation comparison with the canonical
truncation projection, one recovers the raw counit comparison on the chosen cochain model. -/
private theorem homologyMap_truncGEπ_comp_derivedTensorWithAlgebra_truncGE_comparison
    (P : CpxR) [P.IsStrictlyGE (-1)] (i : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        ((t.truncGEπ (-1)).app
          ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)))) ≫
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) =
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) := by
  -- Apply the homology functor to the defining factorization of `t.descTruncGE`.
  simpa [Functor.map_comp, derivedTensorWithAlgebra_truncGE_comparison] using
    congrArg
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map)
      (t.π_descTruncGE
        (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)
        (-1))

/-- Helper for Lemma 15.85.6: in degree `-1`, the truncation comparison is an isomorphism on
homology exactly when the raw counit comparison is. This removes the truncation transport in the
flatness-sensitive degree. -/
private theorem homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_iff_complex_comparison_negOne
    (P : CpxR) [P.IsStrictlyGE (-1)] :
    IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat R') (-1)).map
          (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) ↔
      IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat R') (-1)).map
          (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R') (-1)
  let source :=
    ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P))
  let e :
      H.obj ((t.truncGE (-1)).obj source) ≅ H.obj source :=
    homology_truncGE_iso (R := R') source (-1) (-1) (by omega)
  have hfac :
      e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P) =
        H.map (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P) := by
    simpa [e, source] using
      homologyMap_truncGEπ_comp_derivedTensorWithAlgebra_truncGE_comparison
        (R := R) (R' := R') (P := P) (i := (-1 : ℤ))
  constructor
  · intro htrunc
    haveI : IsIso
        (H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      htrunc
    haveI :
        IsIso (e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      by infer_instance
    rw [hfac] at ‹IsIso _›
    simpa using (show IsIso (H.map (derivedTensorWithAlgebra_complex_comparison
      (R := R) (R' := R') P)) from inferInstance)
  · intro hcomplex
    haveI : IsIso (H.map (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) :=
      hcomplex
    haveI :
        IsIso (e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      by
        rw [hfac]
        infer_instance
    exact IsIso.of_isIso_comp_left e.inv
      (H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P))

/-- Helper for Lemma 15.85.6: in degree `0`, the truncation comparison is an isomorphism on
homology exactly when the raw counit comparison is. This removes the truncation projection from
the remaining degree-`0` base-change computation. -/
private theorem homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_iff_complex_comparison_zero
    (P : CpxR) [P.IsStrictlyGE (-1)] :
    IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat R') 0).map
          (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) ↔
      IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat R') 0).map
          (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R') 0
  let source :=
    ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P))
  let e :
      H.obj ((t.truncGE (-1)).obj source) ≅ H.obj source :=
    homology_truncGE_iso (R := R') source (-1) 0 (by omega)
  have hfac :
      e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P) =
        H.map (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P) := by
    simpa [e, source] using
      homologyMap_truncGEπ_comp_derivedTensorWithAlgebra_truncGE_comparison
        (R := R) (R' := R') (P := P) (i := (0 : ℤ))
  constructor
  · intro htrunc
    haveI : IsIso
        (H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      htrunc
    haveI :
        IsIso
          (e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      by infer_instance
    rw [hfac] at ‹IsIso _›
    simpa using
      (show IsIso
        (H.map (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) from
          inferInstance)
  · intro hcomplex
    haveI :
        IsIso (H.map (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) :=
      hcomplex
    haveI :
        IsIso
          (e.inv ≫ H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) :=
      by
        rw [hfac]
        infer_instance
    exact IsIso.of_isIso_comp_left e.inv
      (H.map (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P))

/-- Helper for Lemma 15.85.6: below degree `-1`, both source and target of the truncation
comparison have zero homology, so the induced map is automatically an isomorphism. -/
private theorem homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_of_lt_negOne
    (P : CpxR) [P.IsStrictlyGE (-1)] (i : ℤ) (hi : i < -1) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R') i
  have hsrc :
      Limits.IsZero
        (H.obj
          ((t.truncGE (-1)).obj
            ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)))) := by
    -- The lower truncation kills all homology below degree `-1`.
    exact DerivedCategory.isZero_of_isGE _ (-1) i hi
  have htgt :
      Limits.IsZero (H.obj (DerivedCategory.Q.obj ((ExtCpx).obj P))) := by
    -- The ordinary scalar-extended complex is also supported in degrees `≥ -1`.
    letI :
        DerivedCategory.IsGE (DerivedCategory.Q.obj ((ExtCpx).obj P)) (-1) :=
      derivedCategory_Q_obj_extCpx_isGE_of_isStrictlyGE (R := R) (R' := R') P
    exact DerivedCategory.isZero_of_isGE _ (-1) i hi
  exact
    Limits.IsZero.isIso hsrc htgt
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P))

/-- Helper for Lemma 15.85.6: on a degree-zero single complex, the raw comparison to ordinary
scalar extension is an isomorphism on zeroth homology. -/
private theorem single_zero_complex_comparison_h0_isIso
    (M : ModuleCat R) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat R') (0 : ℤ)).map
        (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R')
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) := by
  -- Route correction: the source-faithful proof should normalize this map through
  -- `singleFunctorIsoCompQ` and `singleFunctorCompHomologyFunctorIso`, then identify the
  -- transported morphism with ordinary scalar extension in degree `0`.
  -- TODO: prove the exact transport identity and conclude by cancellation of the canonical
  -- `H⁰(single₀ -)` identifications.
  sorry

/-- Helper for Lemma 15.85.6: the raw comparison on a two-term representative is an isomorphism
on degree `-1` homology once the degree-zero term is flat. -/
private theorem complex_comparison_negOne_isIso_of_two_term_flat_zero
    (P : CpxR) [P.IsStrictlyGE (-1)] (hLE : P.IsStrictlyLE 0)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat R') (-1 : ℤ)).map
        (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) := by
  -- Route correction: use the split short exact row
  -- `single₀ (P.X 0) ⟶ P ⟶ single₀ (P.X (-1))⟦1⟧`, compare its derived-tensor triangle with the
  -- ordinary scalar-extension triangle, and read the middle `H^{-1}` map from exactness once the
  -- left comparison is handled by flatness and the right comparison is reduced to
  -- `single_zero_complex_comparison_h0_isIso`.
  -- TODO: package the row as `triangleOfSES`, identify the third component through `shiftIso`,
  -- and conclude from the long exact homology sequence.
  let _ := hLE
  let _ := hflat0
  sorry

/-- Helper for Lemma 15.85.6: the raw comparison on a two-term representative is an isomorphism
on degree `0` homology once the degree-zero term is flat. -/
private theorem complex_comparison_zero_isIso_of_two_term_flat_zero
    (P : CpxR) [P.IsStrictlyGE (-1)] (hLE : P.IsStrictlyLE 0)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat R') (0 : ℤ)).map
        (derivedTensorWithAlgebra_complex_comparison (R := R) (R' := R') P)) := by
  -- Route correction: after the same split-triangle comparison is in place, transport both sides
  -- to cokernels via `two_term_homology_zero_iso_cokernel` and identify the resulting map with
  -- the inverse of `cokernel_baseChange_iso`.
  -- TODO: normalize the middle homology map to the cokernel base-change comparison using
  -- `extCpx_d_negOne_zero_eq_baseChange` and `cokernel_baseChange_iso_inv_π`.
  let _ := hLE
  let _ := hflat0
  sorry

/-- Helper for Lemma 15.85.6: above degree `0`, both source and target of the truncation
comparison have zero homology, so the induced map is automatically an isomorphism. -/
private theorem homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_of_gt_zero
    (P : CpxR) [P.IsStrictlyGE (-1)] (hLE : P.IsStrictlyLE 0) (i : ℤ) (hi : 0 < i) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R') i
  have hsrc :
      Limits.IsZero
        (H.obj
          ((t.truncGE (-1)).obj
            ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)))) := by
    -- The source inherits the upper bound `D^{≤ 0}` from the derived scalar-extension object.
    letI :
        DerivedCategory.IsLE
          ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) 0 :=
      derivedTensorWithAlgebra_Q_obj_isLE_of_isStrictlyLE (R := R) (R' := R') P hLE
    exact DerivedCategory.isZero_of_isLE _ 0 i hi
  have htgt :
      Limits.IsZero (H.obj (DerivedCategory.Q.obj ((ExtCpx).obj P))) := by
    -- The ordinary scalar-extended complex is still a two-term complex with top degree `0`.
    letI : P.IsStrictlyLE 0 := hLE
    letI :
        DerivedCategory.IsLE (DerivedCategory.Q.obj ((ExtCpx).obj P)) 0 := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      infer_instance
    exact DerivedCategory.isZero_of_isLE _ 0 i hi
  exact
    Limits.IsZero.isIso hsrc htgt
      ((DerivedCategory.homologyFunctor (ModuleCat R') i).map
        (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P))

/-- Helper for Lemma 15.85.6: the remaining source-faithful blocker is to show that the canonical
comparison from `τ_{\ge -1}(P ⊗_R^{\mathbf L} R')` to the ordinary scalar-extended two-term
complex is an isomorphism when `P.X 0` is flat. -/
private theorem isIso_derivedTensorWithAlgebra_truncGE_comparison
    (P : CpxR) [P.IsStrictlyGE (-1)] (hLE : P.IsStrictlyLE 0)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsIso (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P) := by
  -- Route correction: first discharge the vanishing degrees by support, then isolate the genuine
  -- base-change work to the two surviving homology groups in degrees `-1` and `0`.
  refine
    (derivedCategory_isIso_iff_homology_map_isIso
      (ℬ := ModuleCat R')
      (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)).2 ?_
  intro i
  by_cases hi_lt : i < -1
  · -- Outside the two-term window on the left, truncation forces both sides to have zero homology.
    exact
      homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_of_lt_negOne
        (R := R) (R' := R') P i hi_lt
  by_cases hi_negOne : i = -1
  · subst hi_negOne
    -- First peel off the truncation factor. The remaining source-faithful task is the degree
    -- `-1` kernel comparison for the raw counit map on the two-term model.
    rw [homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_iff_complex_comparison_negOne
      (R := R) (R' := R') (P := P)]
    -- The remaining source-faithful degree `-1` computation is isolated in the dedicated helper.
    exact
      complex_comparison_negOne_isIso_of_two_term_flat_zero
        (R := R) (R' := R') P hLE hflat0
  by_cases hi_zero : i = 0
  · subst hi_zero
    -- First peel off the truncation factor in degree `0` as well. The remaining source-faithful
    -- task is now the raw degree-`0` cokernel comparison for the counit map on the two-term
    -- model.
    rw [homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_iff_complex_comparison_zero
      (R := R) (R' := R') (P := P)]
    -- The remaining source-faithful degree `0` computation is isolated in the dedicated helper.
    exact
      complex_comparison_zero_isIso_of_two_term_flat_zero
        (R := R) (R' := R') P hLE hflat0
  have hi_pos : 0 < i := by omega
  -- Above the two-term window on the right, both source and target already have zero homology.
  exact
    homologyMap_derivedTensorWithAlgebra_truncGE_comparison_isIso_of_gt_zero
      (R := R) (R' := R') P hLE i hi_pos

/-- Lemma 15.85.6: if `P` is a two-term representative of `K` whose degree-zero term is flat,
then the scalar extension of `P` along `R → R'` is a two-term representative of
`τ_{\ge -1}(K ⊗_R^{\mathbf L} R')`. -/
theorem truncGE_derivedTensorWithAlgebra
    {K : DModR} {P : CpxR}
    (hP : IsTwoTermRepresentative K P)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsTwoTermRepresentative ((t.truncGE (-1)).obj (K ⊗[R]^L[R'])) ((ExtCpx).obj P) :=
  by
  rcases hP with ⟨hiso, hGE, hLE⟩
  rcases hiso with ⟨eP⟩
  have hsupport :
      ((ExtCpx).obj P).IsStrictlyGE (-1) ∧ ((ExtCpx).obj P).IsStrictlyLE 0 :=
    extendScalars_preserves_two_term_support (R := R) (R' := R') P hGE hLE
  have hrep :
      IsIsomorphic (DerivedCategory.Q.obj ((ExtCpx).obj P))
        ((t.truncGE (-1)).obj (K ⊗[R]^L[R'])) := by
    letI : P.IsStrictlyGE (-1) := hGE
    -- Route correction: the remaining work is isolated in the canonical truncation comparison
    -- rather than hidden in the final packaging of `IsTwoTermRepresentative`.
    letI : IsIso (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P) :=
      isIso_derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P hLE hflat0
    -- Compose the canonical truncation comparison with the representing isomorphism `Q(P) ≅ K`.
    let e₁ :
        DerivedCategory.Q.obj ((ExtCpx).obj P) ≅
          (t.truncGE (-1)).obj
            ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) :=
      (asIso (derivedTensorWithAlgebra_truncGE_comparison (R := R) (R' := R') P)).symm
    let e₂ :
        (t.truncGE (-1)).obj
            ((derivedTensorWithAlgebra (algebraMap R R')).obj (DerivedCategory.Q.obj P)) ≅
          (t.truncGE (-1)).obj (K ⊗[R]^L[R']) :=
      (t.truncGE (-1)).mapIso
        ((derivedTensorWithAlgebra (algebraMap R R')).mapIso eP)
    exact ⟨e₁ ≪≫ e₂⟩
  exact ⟨hrep, hsupport.1, hsupport.2⟩

end IsTwoTermRepresentative

end

end CategoryTheory
