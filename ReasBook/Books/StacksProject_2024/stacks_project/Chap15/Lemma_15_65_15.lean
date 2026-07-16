import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_83_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_11
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_1
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')
local notation "HR" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "HR'" => DerivedCategory.homologyFunctor (ModuleCat R')

/-- Helper for Lemma 15.65.15: scalar extension along `R → R'` is additive on module categories,
so it lifts to complexes and the derived category. -/
local instance extendScalars_additive [Algebra R R'] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R R')).left_adjoint_additive

/-- Helper for Lemma 15.65.15: flat scalar extension preserves finite limits, so exact scalar
extension already acts on the derived category. -/
local instance extendScalars_preservesFiniteLimits_of_flat
    [Algebra R R'] [Module.Flat R R'] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R R' from inferInstance))

/-- Helper for Lemma 15.65.15: under flatness, exact scalar extension agrees with the canonical
derived base-change functor. -/
noncomputable def extendScalars_mapDerivedCategory_iso_of_flat
    [Algebra R R'] [Module.Flat R R'] :
    (ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory ≅
      derivedTensorWithAlgebra (algebraMap R R') := by
  let F₀ : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let F :
      HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat R') :=
    F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) := by
    -- Exact flat scalar extension is the source functor whose total left-derived owner is
    -- `derivedTensorWithAlgebra`.
    simpa [F, F₀] using
      (extendScalarsToDerived_hasLeftDerivedFunctor
        (R := R) (A := R') (algebraMap R R'))
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)) := by
    -- Because flat scalar extension is exact, it already inverts quasi-isomorphisms.
    simpa [F₀] using
      (Functor.isLeftDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactorsh)
  -- Compare the exact derived scalar-extension functor with the canonical owner
  -- `derivedTensorWithAlgebra`.
  simpa [derivedTensorWithAlgebra, F, F₀] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
            DerivedCategory (ModuleCat R))
        (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)))
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit
        F
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤
            DerivedCategory (ModuleCat R))
        (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
      (Iso.refl F))

/-- Helper for Lemma 15.65.15: exact flat scalar extension commutes with homology on the derived
category of modules. -/
noncomputable def extendScalars_homology_iso_of_flat
    [Algebra R R'] [Module.Flat R R']
    (L : DModR) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap R R')).obj
        ((HR i).obj L) ≅
      (HR' i).obj
        (((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).obj L) := by
  let HS := HR
  let HT := HR'
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eR : (HS i).obj L ≅ K.homology i :=
    ((HS i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K
  let e :
      (HT i).obj (((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).obj L) ≅
        (ModuleCat.extendScalars (algebraMap R R')).obj ((HS i).obj L) :=
    (HT i).mapIso
        (((((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R') i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.extendScalars (algebraMap R R')) ≪≫
        (ModuleCat.extendScalars (algebraMap R R')).mapIso eR.symm
  -- Pass to a chosen complex model of `L`, compare chain-level homology before and after exact
  -- flat scalar extension, and then return to derived-category homology.
  exact e.symm

/- Domain-style sampling for Lemma 15.65.15:
- primary domain: faithful-flat descent of pseudo-coherence in derived categories of modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `derivedTensorWithAlgebra`,
  `isPseudoCoherent_iff_forall_isMPseudoCoherent`;
- best owner abstraction: this file is `source-facing`, so the public descent statements should be
  organized around the actual ring map `f : R →+* R'`; the `core/canonical` owners remain the
  Chapter 15 predicates `K.IsMPseudoCoherent` and `K.IsPseudoCoherent` on `D(R)`, together with
  the derived scalar-extension owner `derivedTensorWithAlgebra f`, while the chapter base-change
  notation `K ⊗[R]^L[R']` remains the bridge view after passing from `f` to `f.toAlgebra`;
- primitive vs. derived:
  primitive data are the ring map `f`, the derived object `K`, the faithfully flatness of `f`,
  and the pseudo-coherence of the derived base change along `f`;
  the descent statements below are derived API over those owners, so there should be no parallel
  wrapper notion for faithful-flat descent itself;
- source/core/bridge triage:
  `source-facing`: descent of `m`-pseudo-coherence and pseudo-coherence;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`,
    `DerivedCategory.IsPseudoCoherent`, and `derivedTensorWithAlgebra`;
  `bridge/view`: the chapter notation `K ⊗[R]^L[R']` for derived scalar extension along the
    explicit ring map `f`.

This file therefore keeps the source-facing descent theorems, but its public surface should stay
entirely on the existing owner predicates and the canonical scalar-extension owner notation, with
the ring map kept explicit rather than hidden in an ambient algebra instance.
-/

-- Proof sketch: use faithful flatness to reflect the vanishing range of cohomology from the
-- base-changed derived complex back to `K`, descend finiteness of the top surviving cohomology by
-- faithful-flat descent for modules, and then run the downward induction on the largest nonzero
-- cohomological degree as in the Stacks proof, applying Lemmas `15.65.7`, `15.65.3`, and
-- `15.65.2` to the cone construction.
/-- Helper for Lemma 15.65.15: a faithfully flat algebra map supplies the corresponding
faithfully flat module structure on the target ring. -/
theorem module_faithfullyFlat_of_ringHom_faithfullyFlat
    [Algebra R R'] (hff : (algebraMap R R').FaithfullyFlat) :
    Module.FaithfullyFlat R R' := by
  exact
    (RingHom.faithfullyFlat_algebraMap_iff :
      (algebraMap R R').FaithfullyFlat ↔ Module.FaithfullyFlat R R').mp hff

/-- Helper for Lemma 15.65.15: faithful flatness descends finite generation from the tensor base
change module. -/
theorem finite_of_finite_tensorProduct_of_faithfullyFlat_baseChange
    [Algebra R R'] (hff : (algebraMap R R').FaithfullyFlat)
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R' (R' ⊗[R] M)] :
    Module.Finite R M := by
  letI : Module.FaithfullyFlat R R' :=
    module_faithfullyFlat_of_ringHom_faithfullyFlat (R := R) (R' := R') hff
  -- This is exactly the Chapter 10 descent theorem for finite generation.
  simpa using Module.Finite.of_finite_tensorProduct_of_faithfullyFlat R' (R := R) (M := M)

/-- Helper for Lemma 15.65.15: faithful flatness descends finite presentation from the tensor base
change module. -/
theorem finitePresentation_of_finitePresentation_tensorProduct_of_faithfullyFlat_baseChange
    [Algebra R R'] (hff : (algebraMap R R').FaithfullyFlat)
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R' (R' ⊗[R] M)] :
    Module.FinitePresentation R M := by
  letI : Module.FaithfullyFlat R R' :=
    module_faithfullyFlat_of_ringHom_faithfullyFlat (R := R) (R' := R') hff
  -- This is the Chapter 10 finite-presentation descent theorem specialized to the present base
  -- change.
  simpa using
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
      (R := R) (S := R') (M := M)

/-- Helper for Lemma 15.65.15: faithful flat scalar extension reflects zero modules. -/
lemma isZero_of_extendScalars_of_faithfullyFlat
    [Algebra R R'] (Y : ModuleCat R) (hff : (algebraMap R R').FaithfullyFlat)
    (hY : IsZero ((ModuleCat.extendScalars (algebraMap R R')).obj Y)) :
    IsZero Y := by
  letI : Module.FaithfullyFlat R R' :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hff
  -- Zero objects in `ModuleCat` are exactly subsingleton underlying modules.
  letI : Subsingleton ↑((ModuleCat.extendScalars (algebraMap R R')).obj Y) :=
    ModuleCat.subsingleton_of_isZero hY
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
    { __ := AddEquiv.refl R'
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  let e :
      (ModuleCat.extendScalars (algebraMap R R')).obj Y ≅ ModuleCat.of R' (R' ⊗[R] ↑Y) := by
    -- Rewrite exact scalar extension in the tensor-product model expected by faithful flatness.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R ↑Y)).toModuleIso
  have hsub_tensor : Subsingleton (TensorProduct R R' ↑Y) := by
    -- Identify scalar extension with the tensor-product module before reflecting along faithful
    -- flatness.
    let hzero_tensor : IsZero (ModuleCat.of R' (R' ⊗[R] ↑Y)) :=
      IsZero.of_iso hY e.symm
    simpa using ModuleCat.subsingleton_of_isZero hzero_tensor
  have hsub_Y : Subsingleton ↑Y := by
    -- Faithful flatness reflects subsingletons through tensoring with `R'`.
    exact
      (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R R').1 hsub_tensor
  letI : Subsingleton ↑Y := hsub_Y
  exact ModuleCat.isZero_of_subsingleton Y

/-- Helper for Lemma 15.65.15: the witness in `m`-pseudo-coherence gives a uniform upper bound on
the nonvanishing homology degrees. -/
lemma exists_homology_upper_bound_of_isMPseudoCoherent
    {K : DModR} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((HR j).obj K) := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
  -- Above `max m b`, the bounded finite-free witness already has zero homology, and the defining
  -- comparison map is an isomorphism.
  refine ⟨max m b, ?_⟩
  intro j hj
  have hbj : b < j := by
    omega
  have hmj : m < j := by
    omega
  have hsource : IsZero ((HR j).obj (DerivedCategory.Q.obj E)) := by
    have hQ : (DerivedCategory.Q.obj E).IsLE b := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      let _ : E.IsStrictlyLE b := hEb
      infer_instance
    let _ : (DerivedCategory.Q.obj E).IsLE b := hQ
    exact DerivedCategory.isZero_of_isLE _ b j hbj
  let eH : ((HR j).obj (DerivedCategory.Q.obj E)) ≅ ((HR j).obj K) := by
    let _ : IsIso ((HR j).map α) := hαgt j hmj
    exact asIso ((HR j).map α)
  exact eH.isZero_iff.1 hsource

/-- Helper for Lemma 15.65.15: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso_local {K L : DModR} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded finite-free witness and postcompose its comparison map
  -- with the target isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.65.15: a derived complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
private theorem isPseudoCoherent_iff_forall_isMPseudoCoherent_local (K : DModR) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  -- TODO(Lemma 15.65.15): re-express the pseudo-coherence TFAE through a universe-stable
  -- representative API. The current direct use of `cochainComplex_pseudoCoherent_tfae` does not
  -- elaborate in this file, even though the same statement is source-faithful.
  sorry

/-- Helper for Lemma 15.65.15: an `m`-pseudo-coherent witness also works for every larger bound.
-/
private lemma isMPseudoCoherent_mono_local
    {K : DModR} {m n : ℤ} (hmn : m ≤ n)
    (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: reuse the same bounded finite-free model and weaken only the degree cutoff.
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro i hi
    exact hαgt i (lt_of_le_of_lt hmn hi)
  · by_cases hnm : n = m
    · subst hnm
      simpa using hαm
    · have hmn' : m < n := by
        omega
      letI : IsIso ((HR n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.15: the degree-zero single complex on a finite free module is
termwise finite free. -/
private lemma single_zero_complex_isTermwiseFiniteFree_local
    (F : ModuleCat R) [Module.Free R F] [Module.Finite R F] :
    ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: the degree-zero term is `F`, while every other term is a zero module.
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i = 0
  · let e :
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).X i) ≅ F := by
        subst hi
        simpa using HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) F
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · let E : CochainComplex (ModuleCat R) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
    let hzero : IsZero (E.X i) := by
      simpa [E] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) F i hi)
    letI : Subsingleton ↥(E.X i) := ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free R (E.X i) :=
      Module.Free.of_subsingleton (R := R) (N := ↥(E.X i))
    have hfinite : Module.Finite R (E.X i) := by
      let e : ModuleCat.of R PUnit ≅ E.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
    exact ⟨hfree, hfinite⟩

/-- Helper for Lemma 15.65.15: a finite free module is `m`-pseudo-coherent for every `m`. -/
private lemma finite_free_module_isMPseudoCoherent_local
    (F : ModuleCat R) (m : ℤ) [Module.Free R F] [Module.Finite R F] :
    F.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat R) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
  let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree_local (R := R) F
  let α : DerivedCategory.Q.obj E ⟶ ModuleCat.single0Functor.obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom
  -- Proof comment: the single complex itself is the bounded finite-free model, and the canonical
  -- comparison to `F[0]` is an isomorphism in every degree.
  refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
  · intro i hi
    letI : IsIso ((HR i).map α) := Functor.map_isIso (HR i) α
    infer_instance
  · letI : IsIso ((HR m).map α) := Functor.map_isIso (HR m) α
    infer_instance

/-- Helper for Lemma 15.65.15: a module that is `(m - n)`-pseudo-coherent yields an
`m`-pseudo-coherent single derived object in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module_local
    (M : ModuleCat R) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj M)).IsMPseudoCoherent m := by
  let eQ :
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj M) ≅
        (DerivedCategory.singleFunctor (ModuleCat R) n).obj M :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) n).app M
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ModuleCat.single0Functor.obj M :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧).IsMPseudoCoherent (m - n) := by
    -- Proof comment: after shifting by `n`, the degree-`n` single object becomes the degree-zero
    -- single object on `M`.
    rw [ModuleCat.IsMPseudoCoherent] at hM
    exact isMPseudoCoherent_of_iso e.symm (m - n) hM
  have hSingle :
      ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
    -- Proof comment: shift the pseudo-coherence bound back to the original unshifted object.
    exact
      (isMPseudoCoherent_shift_iff
        ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n m).1 hShift
  exact isMPseudoCoherent_of_iso eQ.symm m hSingle

/-- Helper for Lemma 15.65.15: a map into cycles kills the outgoing differential, so it supplies
the compatibility needed to build `mkHomFromSingle`. -/
private theorem single_cover_cycle_condition
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    (α : F ⟶ C.cycles n) :
    ∀ k, n + 1 = k → (α ≫ C.iCycles n) ≫ C.d n k = 0 := by
  intro k hk
  -- Proof comment: a morphism landing in cycles annihilates the outgoing differential by the
  -- defining equation of `C.iCycles n`.
  simpa [Category.assoc] using congrArg (fun t ↦ α ≫ t) (C.iCycles_d n k)

/-- Helper for Lemma 15.65.15: for a single complex concentrated in degree `n`, the canonical map
from cycles to homology is the inverse of the standard single-homology comparison. -/
private theorem single_cycles_to_homology_eq_single_homology_local
    (n : ℤ) (F : ModuleCat R) :
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj F).homologyπ n =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv := by
  -- TODO(Lemma 15.65.15): isolate the exact normalization lemma for the single-complex cycles and
  -- homology identifications. This is the rewrite-stable bridge needed by the head-cover map.
  sorry

/-- Helper for Lemma 15.65.15: the `mkHomFromSingle` map induced by a lift into cycles gives the
expected degree-`n` map on homology. -/
private theorem single_cover_to_complex_map_homology_comparison
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    (α : F ⟶ C.cycles n) :
    let β :
      (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C :=
      HomologicalComplex.mkHomFromSingle
        (K := C) (j := n) (α ≫ C.iCycles n)
        (single_cover_cycle_condition (C := C) n α)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
        HomologicalComplex.homologyMap β n =
      α ≫ C.homologyπ n := by
  -- TODO(Lemma 15.65.15): prove the exact degree-`n` homology comparison for the lifted single
  -- map by normalizing `cyclesMap` and `homologyπ` through the single-complex self isomorphisms.
  sorry

/-- Helper for Lemma 15.65.15: a projective cover of the degree-`n` homology lifts to a morphism
from the degree-`n` single complex. -/
private theorem single_cover_to_complex_map
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    [Module.Projective R F] (q : F ⟶ C.homology n) :
    ∃ β : (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
        HomologicalComplex.homologyMap β n = q := by
  have hsurj : Function.Surjective (C.homologyπ n) :=
    (ModuleCat.epi_iff_surjective (C.homologyπ n)).1 inferInstance
  obtain ⟨αlin, hαlin⟩ :=
    Module.projective_lifting_property (C.homologyπ n).hom q.hom hsurj
  let α : F ⟶ C.cycles n := ModuleCat.ofHom αlin
  have hα : α ≫ C.homologyπ n = q := by
    -- Proof comment: projectivity lifts `q` through the canonical quotient map from cycles to
    -- homology.
    ext x
    exact LinearMap.congr_fun hαlin x
  let β :
      (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C :=
    HomologicalComplex.mkHomFromSingle
      (K := C) (j := n) (α ≫ C.iCycles n)
      (single_cover_cycle_condition (C := C) n α)
  refine ⟨β, ?_⟩
  -- Proof comment: the dedicated normalization lemma turns the lifted cycles map back into the
  -- original quotient map `q`.
  simpa [β, hα] using
    (single_cover_to_complex_map_homology_comparison (R := R) (C := C) n α)

/-- Helper for Lemma 15.65.15: if the induced map from a degree-`n` single complex already covers
the top homology object, then the underlying chain-level homology map is an epimorphism. -/
private theorem single_cover_to_complex_map_epi_of_epi
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    [Module.Projective R F] (q : F ⟶ C.homology n) [Epi q] :
    ∃ β : (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C,
      Epi (HomologicalComplex.homologyMap β n) := by
  obtain ⟨β, hβq⟩ := single_cover_to_complex_map (R := R) (C := C) n q
  have hq_epi : Epi q := inferInstance
  have hcomparison_epi :
      Epi
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
          HomologicalComplex.homologyMap β n) := by
    -- Proof comment: the normalized comparison map is exactly the given epi cover `q`.
    simpa [hβq] using hq_epi
  have hβ_epi : Epi (HomologicalComplex.homologyMap β n) := by
    -- Proof comment: the single-object homology comparison is an isomorphism, so epimorphy
    -- descends from the normalized composite to the actual homology map.
    exact
      epi_of_epi
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv
        (HomologicalComplex.homologyMap β n)
  exact ⟨β, hβ_epi⟩

/-- Helper for Lemma 15.65.15: a surjective cover of the top homology kills all cone homology in
degrees `≥ n`. -/
private theorem mappingCone_homology_isZero_ge_of_single_cover
    {C : CochainComplex (ModuleCat R) ℤ} {n : ℤ} {F : ModuleCat R}
    (β : (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C)
    (hβ_epi : Epi (HomologicalComplex.homologyMap β n))
    (hC : ∀ i : ℤ, n < i → IsZero (C.homology i)) :
    ∀ i : ℤ, n ≤ i → IsZero ((CochainComplex.mappingCone β).homology i) := by
  intro i hi
  -- Proof comment: above degree `n`, both source and target homology vanish; at degree `n`, the
  -- given surjectivity is exactly the hypothesis of Lemma `13.19.11`.
  refine
    CochainComplex.isZero_mappingCone_homology_of_homologyMap_iso_above_and_epi_at
      β n i ?_ hβ_epi hi
  intro j hj
  let hsrc :
      IsZero (((CochainComplex.singleFunctor (ModuleCat R) n).obj F).homology j) :=
    HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) n F j (by omega)
  let htgt : IsZero (C.homology j) := hC j hj
  exact hsrc.isIso htgt (HomologicalComplex.homologyMap β j)

/-- Helper for Lemma 15.65.15: faithfully flat derived base change of a finite-free single complex
is again `m`-pseudo-coherent. -/
private theorem derivedTensor_single_finite_free_isMPseudoCoherent_local
    (f : R →+* R') (F : ModuleCat.{u} R) (n m : ℤ)
    (hff : f.FaithfullyFlat)
    [Module.Free R F] [Module.Finite R F] :
    ((derivedTensorWithAlgebra f).obj
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj F))).IsMPseudoCoherent m := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp <| by
    simpa using hff.flat
  let Ext := ModuleCat.extendScalars (algebraMap R R')
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
    { __ := AddEquiv.refl R'
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  let eTensor :
      Ext.obj F ≅ ModuleCat.of R' (R' ⊗[R] ↑F) := by
    -- Proof comment: rewrite exact scalar extension in the tensor-product model where the finite
    -- and free instances are already canonical.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R ↑F)).toModuleIso
  letI : Module.Free R' ↑(Ext.obj F) :=
    Module.Free.of_equiv' (inferInstance : Module.Free R' (R' ⊗[R] ↑F)) eTensor.toLinearEquiv.symm
  letI : Module.Finite R' ↑(Ext.obj F) :=
    Module.Finite.equiv eTensor.toLinearEquiv.symm
  let eMap :
      (Ext.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj F))) ≅
        DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat R') n).obj (Ext.obj F)) :=
    (Ext.mapDerivedCategory.mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) n).app F)) ≪≫
      Ext.mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj F) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor Ext n).app F) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R') n).app (Ext.obj F)).symm
  have hmodule :
      (Ext.obj F).IsMPseudoCoherent (m - n) :=
    finite_free_module_isMPseudoCoherent_local (R := R') (Ext.obj F) (m - n)
  have hsingle :
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat R') n).obj (Ext.obj F))).IsMPseudoCoherent m :=
    singleFunctor_isMPseudoCoherent_of_module_local (R := R') (Ext.obj F) n m hmodule
  have hExact :
      (Ext.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj F))).IsMPseudoCoherent m :=
    isMPseudoCoherent_of_iso eMap.symm m hsingle
  -- Proof comment: compare canonical derived tensor with exact flat scalar extension on the
  -- single complex and then apply the degree-`n` single-object pseudo-coherence result upstairs.
  exact
    isMPseudoCoherent_of_iso
      ((extendScalars_mapDerivedCategory_iso_of_flat (R := R) (R' := R')).app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj F))) m
      hExact

/-- Helper for Lemma 15.65.15: the top surviving homology of a faithfully flat base change being
`m`-pseudo-coherent descends to a finite module upstairs. -/
private theorem homology_finite_of_faithfullyFlat_baseChange_cutoff
    (f : R →+* R') (C : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℤ)
    (hmn : m ≤ n)
    (hff : f.FaithfullyFlat)
    (hbase : ((derivedTensorWithAlgebra f).obj (DerivedCategory.Q.obj C)).IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, n < i → IsZero (C.homology i)) :
    Module.Finite R (C.homology n) := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp <| by
    simpa using hff.flat
  let Ext := ModuleCat.extendScalars (algebraMap R R')
  let C' : CochainComplex (ModuleCat.{u} R') ℤ :=
    (Ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have hbase' :
      (DerivedCategory.Q.obj C').IsMPseudoCoherent m := by
    let e :
        ((derivedTensorWithAlgebra f).obj (DerivedCategory.Q.obj C)) ≅
          DerivedCategory.Q.obj C' :=
      (((extendScalars_mapDerivedCategory_iso_of_flat (R := R) (R' := R')).app
          (DerivedCategory.Q.obj C)).symm) ≪≫
        Ext.mapDerivedCategoryFactors.app C
    exact isMPseudoCoherent_of_iso e m hbase
  have hbase_n :
      (DerivedCategory.Q.obj C').IsMPseudoCoherent n :=
    isMPseudoCoherent_mono_local hmn hbase'
  have hvanish' : ∀ i : ℤ, n < i → IsZero (C'.homology i) := by
    intro i hi
    let e :
        Ext.obj (C.homology i) ≅ C'.homology i := by
      simpa [C'] using ((C.sc i).mapHomologyIso Ext).symm
    -- Proof comment: exact scalar extension sends each vanishing cohomology module above the
    -- cutoff to a vanishing cohomology module of the scalar-extended complex.
    exact e.isZero_iff.1 (Functor.map_isZero Ext (hvanish i hi))
  have hfinite' : Module.Finite R' (C'.homology n) := by
    have hC' : C'.IsMPseudoCoherent n := by
      simpa [CochainComplex.IsMPseudoCoherent] using hbase_n
    exact CochainComplex.homology_finite_of_isMPseudoCoherent (R := R') hC' hvanish'
  let eHom :
      Ext.obj (C.homology n) ≅ C'.homology n := by
    simpa [C'] using ((C.sc n).mapHomologyIso Ext).symm
  letI : Module.Finite R' (Ext.obj (C.homology n)) :=
    Module.Finite.equiv eHom.toLinearEquiv.symm
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
    { __ := AddEquiv.refl R'
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  let eTensor :
      Ext.obj (C.homology n) ≅ ModuleCat.of R' (R' ⊗[R] ↑(C.homology n)) := by
    -- Proof comment: rewrite exact scalar extension in the tensor-product model expected by the
    -- faithful-flat finite-generation descent theorem.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr
        restrictScalarsSelfEquiv
        (LinearEquiv.refl R ↑(C.homology n))).toModuleIso
  letI : Module.Finite R' (R' ⊗[R] ↑(C.homology n)) :=
    Module.Finite.equiv eTensor.toLinearEquiv
  -- Proof comment: finite generation now descends from the tensor-product model along faithful
  -- flatness.
  simpa using
    finite_of_finite_tensorProduct_of_faithfullyFlat_baseChange
      (R := R) (R' := R') (by simpa using hff) (C.homology n)

/-- Helper for Lemma 15.65.15: a cochain representative with zero homology in every degree `≥ m`
already gives an `m`-pseudo-coherent derived object. -/
private theorem derived_isMPseudoCoherent_of_preimage_homology_isZero_ge
    (C : CochainComplex (ModuleCat R) ℤ) (m : ℤ)
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero (C.homology i)) :
    (DerivedCategory.Q.obj C).IsMPseudoCoherent m := by
  -- TODO(Lemma 15.65.15): recover the derived vanishing criterion through the theorem-local
  -- cochain-to-derived bridge already used elsewhere in Chapter 15.
  sorry

/-- Helper for Lemma 15.65.15: if the head term and middle term of the mapping-cone triangle stay
`m`-pseudo-coherent after base change, then so does the base-changed cone. -/
private theorem base_change_mappingCone_isMPseudoCoherent_of_head_cover
    (f : R →+* R') {C : CochainComplex (ModuleCat R) ℤ} {n m : ℤ} {F : ModuleCat R}
    (β : (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C)
    (hhead :
      DerivedCategory.IsMPseudoCoherent
        (((derivedTensorWithAlgebra f).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) n).obj F))))
        m)
    (hbase :
      ((derivedTensorWithAlgebra f).obj (DerivedCategory.Q.obj C)).IsMPseudoCoherent m) :
    ((derivedTensorWithAlgebra f).obj
      (DerivedCategory.Q.obj (CochainComplex.mappingCone β))).IsMPseudoCoherent m := by
  -- TODO(Lemma 15.65.15): package the mapped mapping-cone triangle under derived tensor and apply
  -- `isMPseudoCoherent_obj₃_of_distinguishedTriangle` once the object identifications are
  -- normalized.
  sorry

/-- Helper for Lemma 15.65.15: once a cochain representative has no homology above a cutoff,
faithfully flat descent of `m`-pseudo-coherence follows by descending on that cutoff. -/
private theorem descend_isMPseudoCoherent_of_upper_cutoff_preimage
    (f : R →+* R') (C : CochainComplex (ModuleCat R) ℤ) (m n : ℤ)
    (hff : f.FaithfullyFlat)
    (hbase : ((derivedTensorWithAlgebra f).obj (DerivedCategory.Q.obj C)).IsMPseudoCoherent m)
    (hvanish : ∀ i : ℤ, n < i → IsZero (C.homology i)) :
    (DerivedCategory.Q.obj C).IsMPseudoCoherent m := by
  -- TODO(Lemma 15.65.15): finish the source-faithful induction on the top nonvanishing homology
  -- degree. The remaining missing pieces are:
  -- 1. the single-complex homology normalization used to build the head map;
  -- 2. the mapped mapping-cone triangle adapter after derived base change;
  -- 3. a universe-stable vanishing-to-pseudo-coherent bridge for `Q.obj` representatives.
  sorry

/-- Helper for Lemma 15.65.15: faithful flat derived base change reflects vanishing of
degree-`i` homology. -/
lemma homology_isZero_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ)
    (hff : f.FaithfullyFlat)
    (hzero : IsZero ((HR' i).obj ((derivedTensorWithAlgebra f).obj K))) :
    IsZero ((HR i).obj K) := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp <| by
    simpa using hff.flat
  let e₁ :
      (ModuleCat.extendScalars (algebraMap R R')).obj ((HR i).obj K) ≅
        (HR' i).obj
          (((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).obj K) :=
    extendScalars_homology_iso_of_flat (R := R) (R' := R') K i
  let e₂ :
      (HR' i).obj
          (((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).obj K) ≅
        (HR' i).obj ((derivedTensorWithAlgebra f).obj K) := by
    -- Replace exact flat scalar extension on the derived category by the canonical owner
    -- `derivedTensorWithAlgebra`.
    simpa using
      (HR' i).mapIso
        ((extendScalars_mapDerivedCategory_iso_of_flat (R := R) (R' := R')).app K)
  have hzero' :
      IsZero ((ModuleCat.extendScalars (algebraMap R R')).obj ((HR i).obj K)) := by
    -- Transport the vanishing of derived-base-changed homology back to exact scalar extension of
    -- the original homology module.
    exact (e₁ ≪≫ e₂).isZero_iff.2 hzero
  -- Faithful flatness now reflects zero from the scalar-extended homology module.
  simpa using
    isZero_of_extendScalars_of_faithfullyFlat
      (R := R) (R' := R') ((HR i).obj K) (by simpa using hff) hzero'

/-- Lemma 15.65.15 (1): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is `m`-pseudo-coherent, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DerivedCategory (ModuleCat.{u} R)) (m : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := by
  letI : Algebra R R' := f.toAlgebra
  let C : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  let eC : DerivedCategory.Q.obj C ≅ K := DerivedCategory.Q.objObjPreimageIso K
  -- Proof comment: the source proof inducts on the highest nonvanishing cohomology degree after
  -- first reflecting the vanishing range of `K ⊗[R]^L[R']` back to `K` via flat homology base
  -- change, then using the module-theoretic descent helpers above for the top cohomology.
  have hbase_bound :
      ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((HR' j).obj ((derivedTensorWithAlgebra f).obj K)) :=
    exists_homology_upper_bound_of_isMPseudoCoherent
      (R := R') (K := (derivedTensorWithAlgebra f).obj K) (m := m) hK
  rcases hbase_bound with ⟨b, hb⟩
  have hbound :
      ∀ j : ℤ, max m b < j → IsZero ((HR j).obj K) := by
    intro j hj
    -- Reflect the vanishing range of the base-changed complex back along faithful flatness.
    exact homology_isZero_of_faithfullyFlat_baseChange f K j hff <|
      hb j (lt_of_le_of_lt (le_max_right m b) hj)
  have hvanishC :
      ∀ j : ℤ, max m b < j → IsZero (C.homology j) := by
    intro j hj
    let eH : (HR j).obj K ≅ C.homology j :=
      ((HR j).mapIso eC).symm ≪≫ (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).app C
    exact eH.isZero_iff.1 (hbound j hj)
  have hQC :
      (DerivedCategory.Q.obj C).IsMPseudoCoherent m :=
    descend_isMPseudoCoherent_of_upper_cutoff_preimage
      (R := R) (R' := R') f C m (max m b) hff
      (isMPseudoCoherent_of_iso
        (((derivedTensorWithAlgebra f).mapIso eC).symm) m hK)
      hvanishC
  -- Proof comment: transport the descended pseudo-coherent structure back across the chosen
  -- cochain representative of `K`.
  exact isMPseudoCoherent_of_iso eC m hQC

-- Proof sketch: apply part `(1)` for every integer `m` and then use the canonical owner theorem
-- `isPseudoCoherent_iff_forall_isMPseudoCoherent`.
/-- Lemma 15.65.15 (2): if the faithfully flat derived base change of a derived `R`-complex `K`
along a faithfully flat ring map `f : R →+* R'` is pseudo-coherent, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DerivedCategory (ModuleCat.{u} R))
    (hff : f.FaithfullyFlat)
    (hK : ((derivedTensorWithAlgebra f).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  -- Proof comment: rewrite pseudo-coherence as degreewise `m`-pseudo-coherence, descend each
  -- cutoff by part `(1)`, and then reconstruct pseudo-coherence downstairs.
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local] at hK ⊢
  intro m
  exact isMPseudoCoherent_of_faithfullyFlat_baseChange f K m hff (hK m)

end

end CategoryTheory
