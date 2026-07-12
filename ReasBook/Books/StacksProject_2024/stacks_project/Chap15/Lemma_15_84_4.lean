import Mathlib
import StacksProject_2024.Chap10.Lemma_10_36_23
import StacksProject_2024.Chap10.Lemma_10_127_18
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap15.Lemma_15_59_3
import StacksProject_2024.Chap15.Lemma_15_65_4
import StacksProject_2024.Chap15.Lemma_15_65_17
import StacksProject_2024.Chap15.Lemma_15_65_9
import StacksProject_2024.Chap15.Lemma_15_82_7
import StacksProject_2024.Chap15.Lemma_15_66_6
import StacksProject_2024.Chap15.Lemma_15_67_2
import StacksProject_2024.Chap15.Lemma_15_67_3
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Lemma_15_67_13
import StacksProject_2024.Chap15.Lemma_15_67_20
import StacksProject_2024.Chap15.Lemma_15_67_8
import StacksProject_2024.Chap15.Lemma_15_83_2
import StacksProject_2024.Chap15.Lemma_15_83_4
import StacksProject_2024.Chap15.Lemma_15_83_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped CategoryTheory DerivedTensorProduct TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 15.84.4:
- primary domain: relative perfectness in the derived category `D(A)` and its description by
  bounded cochain representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `CochainComplex.IsTermwiseFlat`,
  `Compᵇ((ModuleCat A))`,
  `Functor.mapHomologicalComplex`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem belongs on the chapter owner
  `DerivedCategory.IsPerfectOver R`, while the representative-side condition should live on the
  bounded owner `P : Compᵇ((ModuleCat A))` through its ambient complex `P.obj`, together with the
  canonical restriction-of-scalars functor
  `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` and the genuinely
  extra termwise `Module.FinitePresentation A` hypothesis;
- primitive vs. derived:
  primitive data are the bounded representative `P : Compᵇ((ModuleCat A))`, canonical termwise
  `R`-flatness of the restricted ambient complex
  `((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj P.obj`,
  termwise finite presentation over `A`, and the isomorphism class of the represented derived
  object `DerivedCategory.Q.obj P.obj`;
  derived API is the iff-criterion identifying `DerivedCategory.IsPerfectOver R` with the
  existence of such a representative;
- source/core/bridge triage:
  `source-facing`: the representative criterion of Lemma 15.84.4;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `Compᵇ((ModuleCat A))`, and
    `CategoryTheory.IsIsomorphic`, together with the owner predicate
    `CochainComplex.IsTermwiseFlat`;
  `bridge/view`: the ambient restriction-of-scalars functor
    `(ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)` acting on the
    underlying ambient complex `P.obj`.
-/

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "BoundedCpxA" => Compᵇ((ModuleCat A))
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "Q" => DerivedCategory.Q
local notation "HR" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Res" => (ModuleCat.restrictScalars (algebraMap R A))
local notation "ResCpx" => (Res.mapHomologicalComplex (up ℤ))
local notation "ResDer" => Res.mapDerivedCategory

/-- Helper for Lemma 15.84.4: a linear equivalence gives an isomorphism in `ModuleCat`. -/
private def moduleCat_iso_of_linearEquiv
    {S : Type u} [CommRing S] {M N : Type u} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (e : M ≃ₗ[S] N) :
    ModuleCat.of S M ≅ ModuleCat.of S N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap

/-- Helper for Lemma 15.84.4: restricting scalars of a concrete `T`-module recovers the same
underlying `S`-module. -/
private noncomputable def restrictOfIso
    {S T M : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [AddCommGroup M] [Module T M] :
    (ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T M) ≅ ModuleCat.of S M :=
  (show
      ↑((ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T M)) ≃ₗ[S] M from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun x ↦ rfl
        right_inv := fun x ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }).toModuleIso

/-- Helper for Lemma 15.84.4: exact scalar extension on module categories is the usual
tensor-product module. -/
private noncomputable def moduleCat_extendScalars_tensor_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (M : ModuleCat S) :
    (ModuleCat.extendScalars (algebraMap S T)).obj M ≅ ModuleCat.of T (T ⊗[S] (M : Type u)) := by
  let eSelf :
      ↑((ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
    { __ := AddEquiv.refl T
      map_smul' := fun _ _ ↦ rfl }
  -- Proof comment: `ModuleCat.extendScalars` is defined by tensoring with the target algebra.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      eSelf
      (LinearEquiv.refl S (M : Type u))).toModuleIso

/-- Helper for Lemma 15.84.4: a zero module is finite free. -/
private lemma moduleCat_finite_free_of_isZero
    {S : Type u} [CommRing S] (M : ModuleCat S) (hM : IsZero M) :
    Module.Free S M ∧ Module.Finite S M := by
  -- Proof comment: a zero module is free by subsingleton, and finite because it is linearly
  -- equivalent to the one-generator zero module.
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  refine ⟨Module.Free.of_subsingleton S M, ?_⟩
  let e : ModuleCat.of S PUnit ≅ M :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of S PUnit)).isoZero ≪≫ hM.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.84.4: restriction of scalars preserves a lower strict support bound on a
cochain complex. -/
private lemma restrictScalarsComplex_isStrictlyGE
    {E : CpxA} {a : ℤ} (hE : E.IsStrictlyGE a) :
    (ResCpx.obj E).IsStrictlyGE a := by
  -- Proof comment: degreewise zero terms stay zero after applying the exact restriction functor.
  rw [CochainComplex.isStrictlyGE_iff] at hE ⊢
  intro i hi
  change IsZero (Res.obj (E.X i))
  simpa using Res.map_isZero (hE i hi)

/-- Helper for Lemma 15.84.4: restriction of scalars preserves an upper strict support bound on a
cochain complex. -/
private lemma restrictScalarsComplex_isStrictlyLE
    {E : CpxA} {b : ℤ} (hE : E.IsStrictlyLE b) :
    (ResCpx.obj E).IsStrictlyLE b := by
  -- Proof comment: the same exactness argument carries the upper support condition across
  -- restriction of scalars.
  rw [CochainComplex.isStrictlyLE_iff] at hE ⊢
  intro i hi
  change IsZero (Res.obj (E.X i))
  simpa using Res.map_isZero (hE i hi)

/-- Helper for Lemma 15.84.4: on retained degrees, the lower truncation embedding lands back in
the original index. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: `embeddingUpIntGE a` is affine on the surviving degrees.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.84.4: above the cutoff, lower truncation agrees with the original complex
term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : CpxA) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n := by
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: the generic truncation API identifies the retained degree directly.
  exact K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.84.4: an `A`-module that is `R`-flat and finitely presented over `A`
is finitely presented over one polynomial presentation of `A` coming from the finite-presentation
data on `R → A`. -/
private theorem finitePresentation_over_polynomial_cover_of_finitePresentation
    {n : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] A)
    (hα : Function.Surjective α)
    (hker : RingHom.ker α.toRingHom).FG
    (M : ModuleCat A)
    (hFP : Module.FinitePresentation A M) :
    let P := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let _ : Module P M := Module.compHom M α.toRingHom
    Module.FinitePresentation P M := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hα
  letI : Algebra.FinitePresentation P A :=
    Algebra.FinitePresentation.of_surjective (f := α) hα hker
  -- Proof comment: over a finite finitely presented algebra extension, finite presentation is
  -- equivalent before and after restricting scalars.
  exact
    (Module.FinitePresentation.iff_of_finite_finitePresentation (R := P) (S := A) (M := M)).2
      hFP

/-- Helper for Lemma 15.84.4: finite presentation over `A` already gives relative
`(-1)`-pseudo-coherence over `R`. -/
private theorem module_isMinusOnePseudoCoherentRelativeTo_of_finitePresentation
    (M : ModuleCat A)
    (hFP : Module.FinitePresentation A M) :
    Module.IsMPseudoCoherentRelativeTo R A M (-1) := by
  obtain ⟨n, α, hα, hkerα⟩ := (inferInstance : Algebra.FinitePresentation R A).out
  have hMP :
      let P := MvPolynomial (Fin n) R
      let _ : Algebra P A := α.toAlgebra
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M :=
    finitePresentation_over_polynomial_cover_of_finitePresentation
      (R := R) (A := A) α hα hkerα M hFP
  have hMrel :
      Module.FinitePresentationRelativeTo R A M := by
    -- Proof comment: package the chosen polynomial cover together with the descended
    -- finite-presentation witness.
    refine ⟨n, α, hα, ?_⟩
    simpa using hMP
  -- Proof comment: the relative `(-1)`-pseudo-coherent criterion is exactly relative finite
  -- presentation.
  exact
    (Module.isMinusOnePseudoCoherentRelativeTo_iff_finitePresentationRelativeTo
      (R := R) (A := A) (M := M)).2 hMrel

/-- Helper for Lemma 15.84.4: the approximation of a module can be reused to approximate the
regular target algebra on the same directed ring stages. -/
private noncomputable def regular_module_approximation_of_module_approximation
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M) :
    DirectedFinitePresentationModuleApproximation (algebraMap R A) A where
  toDirectedFiniteTypeHomApproximation := Approx.toDirectedFiniteTypeHomApproximation
  hasBijectiveBaseChangeTransitions := Approx.hasBijectiveBaseChangeTransitions
  moduleStage := Approx.SStage
  instAddCommGroupModuleStage := fun i ↦ inferInstance
  instModuleModuleStage := fun i ↦ inferInstance
  instModuleFiniteModuleStage := fun i ↦ inferInstance
  moduleMap := fun {i j} h ↦
    { toFun := Approx.SMap i j h
      map_add' := fun x y ↦ map_add (Approx.SMap i j h) x y
      map_smul' := by
        intro r s
        -- Proof comment: the stage transition is linear because it is a ring homomorphism.
        change Approx.SMap i j h (r * s) = Approx.SMap i j h r * Approx.SMap i j h s
        exact map_mul (Approx.SMap i j h) r s }
  moduleMap_id := by
    intro i s
    -- Proof comment: the self-transition in the directed system is the identity map.
    simpa using (DirectedSystem.map_self (f := fun i j h ↦ Approx.SMap i j h) i s)
  moduleMap_comp := by
    intro i j k hij hjk s
    -- Proof comment: composition of module transitions is exactly composition of ring
    -- transitions on the target-stage rings.
    simpa using (DirectedSystem.map_map' (f := fun i j h ↦ Approx.SMap i j h) hij hjk s)
  moduleToLimit := fun i ↦
    { toFun := Approx.targetStageToLimit i
      map_add' := fun x y ↦ map_add (Approx.targetStageToLimit i) x y
      map_smul' := by
        intro r s
        -- Proof comment: the canonical map from a target stage ring to `A` is linear over the
        -- stage ring for the same multiplicative reason.
        change
          Approx.targetStageToLimit i (r * s) =
            Approx.targetStageToLimit i r * Approx.targetStageToLimit i s
        exact map_mul (Approx.targetStageToLimit i) r s }
  moduleToLimit_comp := by
    intro i j h s
    -- Proof comment: both routes to the limit ring are identified by the directed colimit
    -- structure on the target stages.
    change Approx.targetStageToLimit j (Approx.SMap i j h s) = Approx.targetStageToLimit i s
    simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.comp_apply] using
      congrArg Approx.colimitTarget.toRingHom
        (Ring.DirectLimit.of_f (G := Approx.SStage) (f := fun i j h ↦ Approx.SMap i j h) h s)
  transitionBaseChangeMap_bijective := by
    intro i j h
    -- Proof comment: the regular target-stage module base changes by the standard right-unit
    -- tensor identification.
    simpa [LinearMap.liftBaseChange_tmul, TensorProduct.rid_tmul, Algebra.smul_def] using
      (TensorProduct.rid (Approx.SStage i) (Approx.SStage j)).bijective
  finalBaseChangeMap_bijective := by
    intro i
    -- Proof comment: the same right-unit tensor identification recovers the regular `A`-module
    -- from a target stage.
    simpa [LinearMap.liftBaseChange_tmul, TensorProduct.rid_tmul, Algebra.smul_def] using
      (TensorProduct.rid (Approx.SStage i) A).bijective

/-- Helper for Lemma 15.84.4: there is one descended stage where both the stage algebra and the
stage module are flat over the same source stage. -/
private theorem exists_common_flat_stage_model
    (M : ModuleCat A)
    (hFlat : Module.Flat R (Res.obj M))
    (hFP : Module.FinitePresentation A M) :
    ∃ Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M,
      ∃ i : Approx.Λ,
        Module.Flat (Approx.RStage i) (Approx.SStage i) ∧
          Module.Flat (Approx.RStage i) (Approx.moduleStage i) := by
  classical
  letI : Module.FinitePresentation A M := hFP
  let hf : (algebraMap R A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨Approx⟩ :=
    exists_directedFinitePresentationModuleApproximation
      (f := algebraMap R A) (M := M) hf
  let regApprox :=
    regular_module_approximation_of_module_approximation (R := R) (A := A) Approx
  have hFlatA :
      let _ : Module R A := Module.compHom A (algebraMap R A)
      Module.Flat R A := inferInstance
  obtain ⟨iA, hiA⟩ := eventually_flat_stageModules_of_flat_limit regApprox hFlatA
  have hFlatM :
      let _ : Module R M := Module.compHom M (algebraMap R A)
      Module.Flat R M := by
        simpa using hFlat
  obtain ⟨iM, hiM⟩ := eventually_flat_stageModules_of_flat_limit Approx hFlatM
  obtain ⟨i, hiA', hiM'⟩ := exists_ge_ge iA iM
  -- Proof comment: pass to a common upper bound in the directed stage poset so both eventual
  -- flatness statements hold simultaneously.
  exact ⟨Approx, i, hiA i hiA', hiM i hiM'⟩

/-- Helper for Lemma 15.84.4: a source stage in the directed approximation is Noetherian because
it is of finite type over `ℤ`. -/
private theorem source_stage_isNoetherian_local
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    IsNoetherianRing (Approx.RStage i) := by
  let _ : Algebra ℤ (Approx.RStage i) := (Int.castRingHom (Approx.RStage i)).toAlgebra
  let _ : Algebra.FiniteType ℤ (Approx.RStage i) := Approx.source_finiteType i
  -- Proof comment: finite type over the Noetherian ring `ℤ` implies Noetherianity.
  exact Algebra.FiniteType.isNoetherianRing ℤ (Approx.RStage i)

/-- Helper for Lemma 15.84.4: a target stage in the directed approximation is Noetherian because
it is of finite type over the corresponding Noetherian source stage. -/
private theorem target_stage_isNoetherian_local
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    IsNoetherianRing (Approx.SStage i) := by
  let _ : Algebra (Approx.RStage i) (Approx.SStage i) := (Approx.stageMap i).toAlgebra
  let _ : Algebra.FiniteType (Approx.RStage i) (Approx.SStage i) := Approx.target_finiteType i
  let _ : IsNoetherianRing (Approx.RStage i) := source_stage_isNoetherian_local (R := R) (A := A) Approx i
  -- Proof comment: finite type over a Noetherian source stage forces the target stage to be
  -- Noetherian as well.
  exact Algebra.FiniteType.isNoetherianRing (Approx.RStage i) (Approx.SStage i)

/-- Helper for Lemma 15.84.4: at any descended stage, the stage module is pseudo-coherent because
the stage rings are Noetherian and the stage module is finite. -/
private theorem stage_module_isPseudoCoherent
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)).IsPseudoCoherent := by
  let _ : IsNoetherianRing (Approx.RStage i) := source_stage_isNoetherian_local (R := R) (A := A) Approx i
  let _ : IsNoetherianRing (Approx.SStage i) := target_stage_isNoetherian_local (R := R) (A := A) Approx i
  -- Proof comment: over the Noetherian target stage, finite modules are exactly the
  -- pseudo-coherent modules.
  exact
    (Module.isPseudoCoherent_iff_finite
      (R := Approx.SStage i) (M := Approx.moduleStage i)).2 inferInstance

/-- Helper for Lemma 15.84.4: at any descended stage, the stage module is pseudo-coherent
relative to the source stage because the source stage is Noetherian and the target stage algebra
is finite type. -/
private theorem stage_module_isPseudoCoherentRelativeTo_source
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)).IsPseudoCoherentRelativeTo
      (Approx.RStage i) := by
  let _ : IsNoetherianRing (Approx.RStage i) :=
    source_stage_isNoetherian_local (R := R) (A := A) Approx i
  let _ : Algebra.FiniteType (Approx.RStage i) (Approx.SStage i) := Approx.target_finiteType i
  -- Proof comment: over a Noetherian source stage, relative pseudo-coherence is equivalent to
  -- finite generation over the target stage.
  exact
    (_root_.Module.isPseudoCoherentRelativeTo_iff_finite
      (R := Approx.RStage i) (A := Approx.SStage i) (M := Approx.moduleStage i)).2
      inferInstance

/-- Helper for Lemma 15.84.4: relative pseudo-coherence is invariant under isomorphisms of
bundled modules. -/
private theorem moduleCat_isPseudoCoherentRelativeTo_of_iso_local
    {R' S : Type u} [CommRing R'] [CommRing S] [Algebra R' S] [Algebra.FiniteType R' S]
    {M N : ModuleCat S} (e : M ≅ N) :
    M.IsPseudoCoherentRelativeTo R' ↔ N.IsPseudoCoherentRelativeTo R' := by
  let P : ObjectProperty (DerivedCategory (ModuleCat S)) :=
    fun K ↦ K.IsPseudoCoherentRelativeTo R'
  constructor
  · intro hM
    -- Proof comment: transport the degree-zero derived witness across the induced isomorphism.
    exact P.prop_of_iso (ModuleCat.single0Functor.mapIso e) hM
  · intro hN
    -- Proof comment: the same argument applies in the reverse direction.
    exact P.prop_of_iso (ModuleCat.single0Functor.mapIso e.symm) hN

/-- Helper for Lemma 15.84.4: flatness of a descended stage algebra forces Tor independence with
the target base ring. -/
private theorem flat_stage_isTorIndependent_with_target
    {R₀ S₀ T : Type u} [CommRing R₀] [CommRing S₀] [CommRing T]
    [Algebra R₀ S₀] [Algebra R₀ T] [Module.Flat R₀ S₀] :
    IsTorIndependent R₀ S₀ T := by
  intro p hp
  have hp_outside : (-(p : ℤ)) ∉ Set.Icc (0 : ℤ) 0 := by
    -- Proof comment: positive Tor degrees correspond to strictly negative homological degrees.
    intro hp_mem
    omega
  have htor0 :
      CategoryTheory.ModuleHasTorDimensionLE (ModuleCat.of R₀ S₀) 0 :=
    (ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R₀) (M := ModuleCat.of R₀ S₀)).2
      inferInstance
  have hzero_homology :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R₀) (-(p : ℤ))).obj
          ((ModuleCat.single0Functor.obj (ModuleCat.of R₀ S₀)) ⊗[R₀]^L
            (ModuleCat.single0Functor.obj (ModuleCat.of R₀ T)))) := by
    -- Proof comment: evaluate the tor-dimension-`0` owner on the test module `T`.
    simpa [CategoryTheory.ModuleHasTorDimensionLE] using
      htor0 (ModuleCat.of R₀ T) (-(p : ℤ)) hp_outside
  -- Proof comment: identify the vanishing derived tensor homology with the corresponding Tor
  -- object.
  exact
    IsZero.of_iso hzero_homology
      (CategoryTheory.tor_single0_tensor_homology_iso_local
        (R := R₀) (ModuleCat.of R₀ S₀) (ModuleCat.of R₀ T) p).symm

/-- Helper for Lemma 15.84.4: a flat degree-zero module computes derived scalar extension by the
ordinary scalar-extended module. -/
private noncomputable def derivedTensorWithAlgebra_single0_of_flat_module
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (N : ModuleCat S) (hFlat : Module.Flat S N) :
    ((derivedTensorWithAlgebra (algebraMap S T)).obj (ModuleCat.single0Functor.obj N)) ≅
      ModuleCat.single0Functor.obj ((ModuleCat.extendScalars (algebraMap S T)).obj N) := by
  let E : CochainComplex (ModuleCat S) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj N
  have hEFlat : E.IsTermwiseFlat := by
    -- Proof comment: the unique nonzero term of the single complex is exactly the given flat
    -- module, so the entire strict complex is termwise flat.
    intro n
    change Module.Flat S (((if n = 0 then N else 0 : ModuleCat S) : ModuleCat S) : Type u)
    by_cases h : n = 0
    · subst h
      simpa using hFlat
    · rw [if_neg h]
      infer_instance
  have hELE : E.IsStrictlyLE 0 := by
    -- Proof comment: the single complex is supported in degree `0`, hence bounded above by `0`.
    simpa [E] using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj N).IsStrictlyLE 0)
  -- Proof comment: first compute the derived scalar extension on the strict one-term model, then
  -- rewrite the resulting strict scalar extension back to the degree-zero module object.
  exact
    ((derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := S) (B := T) (E := E) hEFlat hELE) ≪≫
      (DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.extendScalars (algebraMap S T))
          (0 : ℤ)).app N)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat T) (0 : ℤ)).app
        ((ModuleCat.extendScalars (algebraMap S T)).obj N)).symm) ≪≫
      ((derivedTensorWithAlgebra (algebraMap S T)).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app N)).symm

/-- Helper for Lemma 15.84.4: the directed approximation already packages the source-base-change
of the stage module as the restricted target module. -/
private noncomputable def common_flat_stage_source_base_change_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    ((ModuleCat.extendScalars (Approx.sourceStageToLimit i)).obj
      ((ModuleCat.restrictScalars (Approx.stageMap i)).obj
        (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))) ≅
      Res.obj M := by
  -- Proof comment: this is exactly the linear equivalence stored by
  -- `Approx.finalBaseChangeSource i`, rewritten through the standard exact scalar-extension model.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (Approx.finalBaseChangeSource i).toModuleIso

/-- Helper for Lemma 15.84.4: after first restricting the stage module to the source stage, its
derived base change to `R` is the degree-zero object of the restricted target module. -/
private noncomputable def common_flat_stage_source_single0_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    (hMflatStage : Module.Flat (Approx.RStage i) (Approx.moduleStage i)) :
    ((derivedTensorWithAlgebra (Approx.sourceStageToLimit i)).obj
      (ModuleCat.single0Functor.obj
        ((ModuleCat.restrictScalars (Approx.stageMap i)).obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i))))) ≅
      ModuleCat.single0Functor.obj (Res.obj M) := by
  -- Proof comment: the degree-zero source-stage module is flat, so the derived base change is the
  -- ordinary base-changed module; the approximation identifies that module with `M|_R`.
  exact
    derivedTensorWithAlgebra_single0_of_flat_module
      ((ModuleCat.restrictScalars (Approx.stageMap i)).obj
        (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))
      hMflatStage ≪≫
      ModuleCat.single0Functor.mapIso
        (common_flat_stage_source_base_change_iso (R := R) (A := A) Approx i)

/-- Helper for Lemma 15.84.4: the common flat stage tensor product algebra is canonically
identified with the target algebra `A`. -/
private noncomputable def common_flat_stage_target_alg_equiv
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    B ≃ₐ[R] A := by
  let _ : Algebra (Approx.RStage i) R := (Approx.sourceStageToLimit i).toAlgebra
  let _ : Algebra (Approx.RStage i) (Approx.SStage i) := (Approx.stageMap i).toAlgebra
  let _ : Algebra (Approx.SStage i) A := (Approx.targetStageToLimit i).toAlgebra
  let _ : Algebra (Approx.RStage i) A :=
    ((algebraMap R A).comp (Approx.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (Approx.RStage i) R A := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (Approx.RStage i) (Approx.SStage i) A :=
    Approx.targetStageToLimit_isScalarTower i
  let _ : Algebra.IsPushout (Approx.RStage i) R (Approx.SStage i) A :=
    Approx.finalSquare_isPushout i
  let eRight :
      (R ⊗[Approx.RStage i] Approx.SStage i) ≃ₐ[R] A :=
    (Algebra.IsPushout.cancelBaseChangeAlg
      (Approx.RStage i) R (Approx.SStage i) A (Approx.SStage i)).symm.trans
      (Algebra.TensorProduct.rid (Approx.SStage i) R A)
  -- Proof comment: commute the tensor factors into the source notation used in this file and
  -- then collapse the pushout tensor square to the actual target algebra `A`.
  exact
    (AlgEquiv.restrictScalars R
      (Algebra.TensorProduct.comm (Approx.RStage i) (Approx.SStage i) R)).trans eRight

/-- Helper for Lemma 15.84.4: after transporting the pushout-side scalar extension of the stage
module across the canonical tensor-product algebra identification, one recovers the target module
`M`. -/
private noncomputable def common_flat_stage_pushout_module_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    let e : B ≃ₐ[R] A := common_flat_stage_target_alg_equiv (R := R) (A := A) Approx i
    ((ModuleCat.restrictScalars e.symm.toAlgHom).obj
      ((ModuleCat.extendScalars (algebraMap (Approx.SStage i) B)).obj
        (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))) ≅
      ModuleCat.of A M := by
  let B := (Approx.SStage i) ⊗[Approx.RStage i] R
  let e : B ≃ₐ[R] A := common_flat_stage_target_alg_equiv (R := R) (A := A) Approx i
  let eTensor :
      (ModuleCat.extendScalars (algebraMap (Approx.SStage i) B)).obj
        (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)) ≅
          ModuleCat.of B (B ⊗[Approx.SStage i] Approx.moduleStage i) :=
    moduleCat_extendScalars_tensor_iso
      (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i))
  let eRestrict :
      ((ModuleCat.restrictScalars e.symm.toAlgHom).obj
        ((ModuleCat.extendScalars (algebraMap (Approx.SStage i) B)).obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))) ≅
          ModuleCat.of A (B ⊗[Approx.SStage i] Approx.moduleStage i) := by
    -- Proof comment: first rewrite exact scalar extension to the concrete tensor-product model,
    -- then forget that the resulting tensor product is only presented as a `B`-module.
    exact
      (ModuleCat.restrictScalars e.symm.toAlgHom).mapIso eTensor ≪≫
        restrictOfIso (A := A) (B := B) (M := B ⊗[Approx.SStage i] Approx.moduleStage i)
  let eCoeff :
      ↑((ModuleCat.restrictScalars e.symm.toAlgHom).obj (ModuleCat.of B B)) ≃ₗ[A] A :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a b
        change e ((e.symm.toRingHom a) * b) = a * e b
        rw [AlgEquiv.map_mul, e.apply_symm_apply] }
  let eChangeCoeffs :
      ModuleCat.of A (B ⊗[Approx.SStage i] Approx.moduleStage i) ≅
        ModuleCat.of A (A ⊗[Approx.SStage i] Approx.moduleStage i) := by
    -- Proof comment: transport the left tensor factor from the pushout algebra `B` to the actual
    -- target algebra `A` via the canonical algebra equivalence.
    simpa using
      (TensorProduct.AlgebraTensorModule.congr
        eCoeff
        (LinearEquiv.refl (Approx.SStage i) (Approx.moduleStage i))).toModuleIso
  let eFinal :
      ModuleCat.of A (A ⊗[Approx.SStage i] Approx.moduleStage i) ≅
        ModuleCat.of A M := by
    -- Proof comment: the approximation already identifies the ordinary target-side base change of
    -- the stage module with the original module `M`.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (Approx.finalBaseChange i).toModuleIso
  exact eRestrict ≪≫ eChangeCoeffs ≪≫ eFinal

/-- Helper for Lemma 15.84.4: a natural isomorphism between exact module functors yields the
corresponding objectwise comparison on derived categories. -/
private noncomputable def mapDerivedCategory_obj_iso_of_natIso
    {S T : Type u} [CommRing S] [CommRing T]
    {F G : ModuleCat S ⥤ ModuleCat T}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory (ModuleCat S)) :
    (F.mapDerivedCategory.obj K) ≅ (G.mapDerivedCategory.obj K) := by
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: normalize both derived objects to the same strict representative and then
  -- insert the cochain-level image of the functor isomorphism.
  exact
    (F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (F.mapDerivedCategoryFactors.app C) ≪≫
      DerivedCategory.Q.mapIso
        ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app C) ≪≫
      (G.mapDerivedCategoryFactors.app C).symm ≪≫
      (G.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- Helper for Lemma 15.84.4: the derived functor of an exact composite agrees objectwise with
the composite of the induced derived functors. -/
private noncomputable def mapDerivedCategory_comp_obj_iso
    {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    (F : ModuleCat S ⥤ ModuleCat T) (G : ModuleCat T ⥤ ModuleCat U)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory (ModuleCat S)) :
    ((F ⋙ G).mapDerivedCategory.obj K) ≅
      (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) := by
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: both sides are computed by the same strict image `G(F(C))`, so we only keep
  -- the canonical comparison maps relating the strict and derived constructions.
  exact
    ((F ⋙ G).mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      ((F ⋙ G).mapDerivedCategoryFactors.app C) ≪≫
      (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).symm ≪≫
      (G.mapDerivedCategory).mapIso ((F.mapDerivedCategoryFactors.app C).symm) ≪≫
      (G.mapDerivedCategory).mapIso
        ((F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K))

/-- Helper for Lemma 15.84.4: scalar extension across a ring equivalence is the inverse
restriction-of-scalars functor. -/
private noncomputable def extendScalars_iso_restrictScalars_inverse
    {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    ModuleCat.extendScalars e.toRingHom ≅ ModuleCat.restrictScalars e.symm := by
  -- Proof comment: both functors are left adjoint to restriction along `e`, so left-adjoint
  -- uniqueness identifies them.
  exact
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- Helper for Lemma 15.84.4: after swapping the tensor factors, the stage-algebra map into the
pushout algebra `Sᵢ ⊗[Rᵢ] R` becomes the canonical map into `R ⊗[Rᵢ] Sᵢ`. -/
private theorem common_flat_stage_comm_base_change_comp_left
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    let Acomm := R ⊗[Approx.RStage i] Approx.SStage i
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    ((Algebra.TensorProduct.comm (Approx.RStage i) R (Approx.SStage i)).symm.toRingEquiv.toRingHom).comp
        (algebraMap (Approx.SStage i) B) =
      algebraMap (Approx.SStage i) Acomm := by
  ext s
  -- Proof comment: both maps send a stage scalar to the pure tensor `1 ⊗ s`.
  simp [RingHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.84.4: after swapping the tensor factors, the target-base map into
`R ⊗[Rᵢ] Sᵢ` becomes the canonical map into `Sᵢ ⊗[Rᵢ] R`. -/
private theorem common_flat_stage_comm_base_change_comp_right
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ) :
    let Acomm := R ⊗[Approx.RStage i] Approx.SStage i
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    ((Algebra.TensorProduct.comm (Approx.RStage i) R (Approx.SStage i)).toRingEquiv.toRingHom).comp
        (algebraMap R Acomm) =
      algebraMap R B := by
  ext r
  -- Proof comment: both maps send a base scalar to the pure tensor `1 ⊗ r`.
  simp [RingHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.84.4: transporting the pushout-side derived tensor product across the
tensor-factor swap identifies it with the standard base-change object over `R ⊗[Rᵢ] Sᵢ`. -/
private noncomputable def common_flat_stage_comm_derivedTensor_transport_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    {K : DerivedCategory (ModuleCat (Approx.SStage i))} :
    let Acomm := R ⊗[Approx.RStage i] Approx.SStage i
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    (((ModuleCat.restrictScalars
        (Algebra.TensorProduct.comm (Approx.RStage i) R (Approx.SStage i)).toRingEquiv.toRingHom)
        .mapDerivedCategory).obj
      (K ⊗[Approx.SStage i]^L[B])) ≅
      (K ⊗[Approx.SStage i]^L[Acomm]) := by
  let Acomm := R ⊗[Approx.RStage i] Approx.SStage i
  let B := (Approx.SStage i) ⊗[Approx.RStage i] R
  let e : Acomm ≃+* B := (Algebra.TensorProduct.comm (Approx.RStage i) R (Approx.SStage i)).toRingEquiv
  letI : Algebra B Acomm := e.symm.toRingHom.toAlgebra
  letI : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  letI : Module.Flat B Acomm := RingHom.flat_algebraMap_iff.mp <| by
    simpa [RingHom.algebraMap_toAlgebra] using
      (show RingHom.Flat e.symm.toRingHom from inferInstance)
  letI : (ModuleCat.extendScalars e.symm.toRingHom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj e.symm.toRingHom).left_adjoint_additive
  letI :
      PreservesFiniteLimits (ModuleCat.extendScalars e.symm.toRingHom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (f := e.symm.toRingHom)
      (show RingHom.Flat e.symm.toRingHom from inferInstance)
  -- Proof comment: exact restriction along the tensor-factor swap is exact scalar extension along
  -- the inverse equivalence, so the remaining comparison is the direct-versus-iterated derived
  -- tensor-product isomorphism.
  calc
    (((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory).obj
        (K ⊗[Approx.SStage i]^L[B])) ≅
      ((ModuleCat.extendScalars e.symm.toRingHom).mapDerivedCategory.obj
        (K ⊗[Approx.SStage i]^L[B])) :=
      (mapDerivedCategory_obj_iso_of_natIso
        (extendScalars_iso_restrictScalars_inverse e.symm).symm
        (K ⊗[Approx.SStage i]^L[B])).symm
    _ ≅
        ((derivedTensorWithAlgebra e.symm.toRingHom).obj
          (K ⊗[Approx.SStage i]^L[B])) :=
      (extendScalars_mapDerivedCategory_iso_of_flat
        (R := B) (R' := Acomm)).app _
    _ ≅ (K ⊗[Approx.SStage i]^L[Acomm]) :=
      (derivedTensorWithAlgebraCompIso
        (algebraMap (Approx.SStage i) B)
        e.symm.toRingHom
        (algebraMap (Approx.SStage i) Acomm)
        (common_flat_stage_comm_base_change_comp_left (R := R) (A := A) Approx i)).app K

/-- Helper for Lemma 15.84.4: after restricting the pushout-side derived tensor product from the
pushout algebra to `R`, one recovers the source-side derived base change along `Rᵢ → R`. -/
private noncomputable def common_flat_stage_restricted_base_change_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    {K : DerivedCategory (ModuleCat (Approx.SStage i))} :
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    ((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj
      (K ⊗[Approx.SStage i]^L[B])) ≅
      (((ModuleCat.restrictScalars (Approx.stageMap i)).mapDerivedCategory.obj K) ⊗[Approx.RStage i]^L[R]) := by
  let Acomm := R ⊗[Approx.RStage i] Approx.SStage i
  let B := (Approx.SStage i) ⊗[Approx.RStage i] R
  let e : Acomm ≃+* B := (Algebra.TensorProduct.comm (Approx.RStage i) R (Approx.SStage i)).toRingEquiv
  -- Proof comment: first rewrite restriction from `B` to `R` through the tensor-factor swap, then
  -- replace the swapped pushout-side base change by the canonical source-side base-change
  -- comparison from Lemma `15.61.2`.
  calc
    ((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj
        (K ⊗[Approx.SStage i]^L[B])) ≅
      (((ModuleCat.restrictScalars e.toRingHom ⋙
          ModuleCat.restrictScalars (algebraMap R Acomm)).mapDerivedCategory).obj
        (K ⊗[Approx.SStage i]^L[B])) :=
      mapDerivedCategory_obj_iso_of_natIso
        (ModuleCat.restrictScalarsComp'
          (algebraMap R Acomm)
          e.toRingHom
          (algebraMap R B)
          (common_flat_stage_comm_base_change_comp_right (R := R) (A := A) Approx i))
        (K ⊗[Approx.SStage i]^L[B])
    _ ≅
        ((ModuleCat.restrictScalars (algebraMap R Acomm)).mapDerivedCategory.obj
          (((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory).obj
            (K ⊗[Approx.SStage i]^L[B]))) :=
      mapDerivedCategory_comp_obj_iso
        (ModuleCat.restrictScalars e.toRingHom)
        (ModuleCat.restrictScalars (algebraMap R Acomm))
        (K ⊗[Approx.SStage i]^L[B])
    _ ≅
        ((ModuleCat.restrictScalars (algebraMap R Acomm)).mapDerivedCategory.obj
          (K ⊗[Approx.SStage i]^L[Acomm])) :=
      ((ModuleCat.restrictScalars (algebraMap R Acomm)).mapDerivedCategory).mapIso
        (common_flat_stage_comm_derivedTensor_transport_iso (R := R) (A := A) Approx i)
    _ ≅
        (((ModuleCat.restrictScalars (Approx.stageMap i)).mapDerivedCategory.obj K) ⊗[Approx.RStage i]^L[R]) :=
      derivedTensorBaseChangeIso (A := Approx.RStage i) (R := Approx.SStage i) (Aprime := R) K

/-- Helper for Lemma 15.84.4: for the stage degree-zero object, the restricted pushout-side
derived base change is the degree-zero object of `M` restricted to `R`. -/
private noncomputable def common_flat_stage_pushout_single0_restrict_iso
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    (hMflatStage : Module.Flat (Approx.RStage i) (Approx.moduleStage i)) :
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    ((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj
      ((derivedTensorWithAlgebra (algebraMap (Approx.SStage i) B)).obj
        (ModuleCat.single0Functor.obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i))))) ≅
      ModuleCat.single0Functor.obj (Res.obj M) := by
  -- Proof comment: specialize the structural restricted-base-change comparison to the stage
  -- degree-zero object, then close it with the already proved source-side flat single-object
  -- comparison.
  exact
    common_flat_stage_restricted_base_change_iso (R := R) (A := A) Approx i ≪≫
      common_flat_stage_source_single0_iso (R := R) (A := A) Approx i hMflatStage

/-- Helper for Lemma 15.84.4: at a common flat stage, the pushout-side derived tensor product of
the stage degree-zero module is the ordinary pushout-side degree-zero module in `D(B)`. -/
private theorem common_flat_stage_pushout_single0_comparison
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    (hAflatStage : Module.Flat (Approx.RStage i) (Approx.SStage i))
    (hMflatStage : Module.Flat (Approx.RStage i) (Approx.moduleStage i)) :
    let B := (Approx.SStage i) ⊗[Approx.RStage i] R
    ((derivedTensorWithAlgebra (algebraMap (Approx.SStage i) B)).obj
      (ModuleCat.single0Functor.obj
        (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))) ≅
      ModuleCat.single0Functor.obj
        ((ModuleCat.extendScalars (algebraMap (Approx.SStage i) B)).obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i))) := by
  -- Route correction: the comparison has to live in `D(B)` itself, not only after restricting all
  -- the way to `R`.
  -- TODO(Lemma 15.84.4): choose the explicit finite-free stage resolution from
  -- `stage_module_isPseudoCoherent`, compute derived tensor by its bounded-above cochain view,
  -- and show the scalar-extended resolution still resolves the ordinary pushout module by the
  -- source-stage flatness hypotheses `hAflatStage` and `hMflatStage`.
  let _ := hAflatStage
  let _ := hMflatStage
  sorry

/-- Helper for Lemma 15.84.4: under a finite algebra map, restricting scalars preserves
module-level relative pseudo-coherence. -/
private theorem moduleCat_isPseudoCoherentRelativeTo_restrictScalars_of_finite_local
    {R' S T : Type u} [CommRing R'] [CommRing S] [CommRing T]
    [Algebra R' S] [Algebra R' T] [Algebra S T]
    [Algebra.FiniteType R' S] [Algebra.FiniteType S T]
    (M : ModuleCat T)
    (hM : M.IsPseudoCoherentRelativeTo R') :
    ((ModuleCat.restrictScalars (algebraMap S T)).obj M).IsPseudoCoherentRelativeTo R' := by
  letI : Algebra.FiniteType R' T :=
    Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R' S)
      (inferInstance : Algebra.FiniteType S T)
  have hSingle :
      (ModuleCat.single0Functor.obj M).IsPseudoCoherentRelativeTo R' := by
    -- Proof comment: reinterpret the module-level relative condition as the degree-zero derived
    -- condition on the corresponding single complex.
    simpa [ModuleCat.IsPseudoCoherentRelativeTo] using hM
  have hRestrDerived :
      (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory.obj
        (ModuleCat.single0Functor.obj M))).IsPseudoCoherentRelativeTo R' :=
    (isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
      (R := R') (A := S) (B := T)
      (ModuleCat.single0Functor.obj M)).1 hSingle
  let P : ObjectProperty (DerivedCategory (ModuleCat S)) :=
    fun K ↦ K.IsPseudoCoherentRelativeTo R'
  have hRestrSingle :
      (ModuleCat.single0Functor.obj
        ((ModuleCat.restrictScalars (algebraMap S T)).obj M)).IsPseudoCoherentRelativeTo R' := by
    -- Proof comment: replace derived restriction of the degree-zero object by the degree-zero
    -- object of the restricted module.
    exact
      P.prop_of_iso
        (restrictScalars_single0_iso (algebraMap S T) M)
        hRestrDerived
  simpa [ModuleCat.IsPseudoCoherentRelativeTo] using hRestrSingle

/-- Helper for Lemma 15.84.4: once the raw pushout-side degree-zero comparison is available, a
single common flat stage yields relative pseudo-coherence of the target module. -/
private theorem module_isPseudoCoherentRelativeTo_of_common_flat_stage
    {M : ModuleCat A}
    (Approx : DirectedFinitePresentationModuleApproximation (algebraMap R A) M)
    (i : Approx.Λ)
    (hAflatStage : Module.Flat (Approx.RStage i) (Approx.SStage i))
    (hMflatStage : Module.Flat (Approx.RStage i) (Approx.moduleStage i)) :
    Module.IsPseudoCoherentRelativeTo R A M := by
  let B := (Approx.SStage i) ⊗[Approx.RStage i] R
  let e : B ≃ₐ[R] A := common_flat_stage_target_alg_equiv (R := R) (A := A) Approx i
  let pushoutModule : ModuleCat B :=
    (ModuleCat.extendScalars (algebraMap (Approx.SStage i) B)).obj
      (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i))
  have hStageRel :
      (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)).IsPseudoCoherentRelativeTo
        (Approx.RStage i) :=
    stage_module_isPseudoCoherentRelativeTo_source (R := R) (A := A) Approx i
  have hTor :
      IsTorIndependent (Approx.RStage i) (Approx.SStage i) R :=
    flat_stage_isTorIndependent_with_target
      (R₀ := Approx.RStage i) (S₀ := Approx.SStage i) (T := R)
  have hBaseDerived :
      ((derivedTensorWithAlgebra (algebraMap (Approx.SStage i) B)).obj
        (ModuleCat.single0Functor.obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))).IsPseudoCoherentRelativeTo R := by
    -- Proof comment: the stage module is relatively pseudo-coherent over the source stage, so
    -- Tor-independent base change upgrades the degree-zero object to the pushout algebra.
    simpa using
      (derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent
        (R := Approx.RStage i) (A := Approx.SStage i) (R' := R)
        (K := ModuleCat.single0Functor.obj
          (ModuleCat.of (Approx.SStage i) (Approx.moduleStage i)))
        hTor (by
          simpa [ModuleCat.IsPseudoCoherentRelativeTo, Module.IsPseudoCoherentRelativeTo] using
            hStageRel))
  let P : ObjectProperty (DerivedCategory (ModuleCat B)) :=
    fun K ↦ K.IsPseudoCoherentRelativeTo R
  have hPushoutSingle :
      (ModuleCat.single0Functor.obj pushoutModule).IsPseudoCoherentRelativeTo R := by
    -- Proof comment: the new `D(B)` comparison turns the Tor-independent base-change object into
    -- the ordinary pushout-side degree-zero module.
    exact
      P.prop_of_iso
        (common_flat_stage_pushout_single0_comparison
          (R := R) (A := A) Approx i hAflatStage hMflatStage)
        hBaseDerived
  have hPushoutModule :
      pushoutModule.IsPseudoCoherentRelativeTo R := by
    -- Proof comment: now read the derived degree-zero statement back as a module-level relative
    -- pseudo-coherence witness over the pushout algebra.
    simpa [pushoutModule, ModuleCat.IsPseudoCoherentRelativeTo] using hPushoutSingle
  letI : Algebra A B := e.symm.toAlgHom.toAlgebra
  letI : Algebra.FiniteType A B :=
    Algebra.FiniteType.of_surjective (R := A) e.symm.toAlgHom e.symm.surjective
  have hRestrPushout :
      ((ModuleCat.restrictScalars e.symm.toAlgHom).obj pushoutModule).IsPseudoCoherentRelativeTo R := by
    -- Proof comment: restriction of scalars along the finite algebra equivalence keeps the
    -- relative pseudo-coherence statement.
    simpa [RingHom.algebraMap_toAlgebra, pushoutModule] using
      moduleCat_isPseudoCoherentRelativeTo_restrictScalars_of_finite_local
        (R' := R) (S := A) (T := B) pushoutModule hPushoutModule
  have hTargetCat :
      (ModuleCat.of A M).IsPseudoCoherentRelativeTo R := by
    -- Proof comment: the common-stage pushout module is the original module `M` after transport
    -- across the canonical tensor-product algebra equivalence.
    exact
      (moduleCat_isPseudoCoherentRelativeTo_of_iso_local
        (R' := R)
        (e := common_flat_stage_pushout_module_iso (R := R) (A := A) Approx i)).1
        hRestrPushout
  simpa [Module.IsPseudoCoherentRelativeTo, ModuleCat.IsPseudoCoherentRelativeTo] using hTargetCat

/-- Helper for Lemma 15.84.4: an `A`-module that is `R`-flat and finitely presented over `A`
is pseudo-coherent over `A`. -/
private theorem module_isPseudoCoherent_of_flat_finitePresentation
    (M : ModuleCat A)
    (hFlat : Module.Flat R (Res.obj M))
    (hFP : Module.FinitePresentation A M) :
    M.IsPseudoCoherent := by
  classical
  obtain ⟨Approx, i, hAflatStage, hMflatStage⟩ :=
    exists_common_flat_stage_model (R := R) (A := A) M hFlat hFP
  have hRel :
      Module.IsPseudoCoherentRelativeTo R A M :=
    module_isPseudoCoherentRelativeTo_of_common_flat_stage
      (R := R) (A := A) Approx i hAflatStage hMflatStage
  have hSingleAbs :
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherent := by
    -- Proof comment: the source ring map `R → A` is pseudo-coherent, so relative and absolute
    -- pseudo-coherence agree on the degree-zero object.
    exact
      (isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
        (R := R) (A := A)
        ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)).1 <| by
          simpa [Module.IsPseudoCoherentRelativeTo, ModuleCat.IsPseudoCoherentRelativeTo] using hRel
  simpa [ModuleCat.IsPseudoCoherent] using hSingleAbs

/-- Helper for Lemma 15.84.4: an `A`-module that is `R`-flat and finitely presented over `A`
is pseudo-coherent relative to `R`. -/
private theorem module_isPseudoCoherentRelativeTo_of_flat_finitePresentation
    (M : ModuleCat A)
    (hFlat : Module.Flat R (Res.obj M))
    (hFP : Module.FinitePresentation A M) :
    Module.IsPseudoCoherentRelativeTo R A M := by
  have hAbs : M.IsPseudoCoherent :=
    module_isPseudoCoherent_of_flat_finitePresentation (R := R) (A := A) M hFlat hFP
  have hSingleAbs :
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsPseudoCoherent := by
    -- Proof comment: rewrite the module-level absolute pseudo-coherence statement as the
    -- degree-zero derived object.
    simpa [ModuleCat.IsPseudoCoherent] using hAbs
  -- Proof comment: once absolute pseudo-coherence is known, the pseudo-coherent ring map
  -- comparison returns the desired relative statement.
  simpa [Module.IsPseudoCoherentRelativeTo, ModuleCat.IsPseudoCoherentRelativeTo] using
    (isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
      (R := R) (A := A) ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)).2
      hSingleAbs

/-- Helper for Lemma 15.84.4: a degree-zero `A`-module that is `R`-flat and finitely presented
over `A` is perfect over `R`. -/
private theorem single0_isPerfectOver_of_flat_finitePresentation
    (M : ModuleCat A)
    (hFlat : Module.Flat R (Res.obj M))
    (hFP : Module.FinitePresentation A M) :
    DerivedCategory.IsPerfectOver R
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M) := by
  rw [DerivedCategory.IsPerfectOver]
  constructor
  · -- Proof comment: the missing source descent step is isolated in the module-level helper.
    simpa using
      module_isPseudoCoherent_of_flat_finitePresentation (R := R) (A := A) M hFlat hFP
  · -- Proof comment: flatness gives tor dimension at most `0` on the restricted module, and the
    -- single-object restriction comparison rewrites that to the exact derived object we need.
    have hResTor : ModuleHasFiniteTorDimension (Res.obj M) := by
      exact
        ((ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R) (M := Res.obj M)).2 hFlat)
          .hasFiniteTorDimension
    exact
      (hasFiniteTorDimension_of_iso (R := R)
        (restrictScalars_single0_iso (algebraMap R A) M)).2 <| by
          simpa [ModuleHasFiniteTorDimension] using hResTor

/-- Helper for Lemma 15.84.4: a bounded representative with termwise `R`-flat finitely presented
terms is perfect over `R`. -/
private theorem isPerfectOver_of_bounded_termwise_flat_finitePresentation_representative
    (K : DModA) (P : BoundedCpxA)
    (hFlat :
      CochainComplex.IsTermwiseFlat
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
          P.obj))
    (hFP : ∀ i : ℤ, Module.FinitePresentation A (P.obj.X i))
    (hIso : IsIsomorphic K (DerivedCategory.Q.obj P.obj)) :
    DerivedCategory.IsPerfectOver R K := by
  rcases hIso with ⟨eK⟩
  rcases (CochainComplex.bounded_iff (ModuleCat A) P.obj).1 P.property with ⟨hPplus, hPminus⟩
  rcases (CochainComplex.plus_iff (ModuleCat A) P.obj).1 hPplus with ⟨a, hPge⟩
  rcases (CochainComplex.minus_iff (ModuleCat A) P.obj).1 hPminus with ⟨b, hPle⟩
  have hTermPc : ∀ i : ℤ, (P.obj.X i).IsPseudoCoherent := by
    intro i
    -- Proof comment: the only nontrivial termwise ingredient is the isolated single-module
    -- source argument.
    exact
      module_isPseudoCoherent_of_flat_finitePresentation (R := R) (A := A) (P.obj.X i)
        (hFlat i) (hFP i)
  have hQPc : (DerivedCategory.Q.obj P.obj).IsPseudoCoherent := by
    -- Proof comment: bounded-above plus termwise pseudo-coherence upgrades the whole strict
    -- representative to a pseudo-coherent derived object.
    exact
      CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise
        (R := A) P.obj hPminus hTermPc
  have hResBounded :
      CochainComplex.bounded (ModuleCat R) (ResCpx.obj P.obj) := by
    -- Proof comment: restriction of scalars preserves both support bounds of the chosen bounded
    -- representative.
    exact
      (CochainComplex.bounded_iff (ModuleCat R) (ResCpx.obj P.obj)).2
        ⟨(CochainComplex.plus_iff (ModuleCat R) (ResCpx.obj P.obj)).2
            ⟨a, restrictScalarsComplex_isStrictlyGE (R := R) (A := A) hPge⟩,
          (CochainComplex.minus_iff (ModuleCat R) (ResCpx.obj P.obj)).2
            ⟨b, restrictScalarsComplex_isStrictlyLE (R := R) (A := A) hPle⟩⟩
  let PR : Compᵇ((ModuleCat R)) := ⟨ResCpx.obj P.obj, hResBounded⟩
  have hTermTor : ∀ i : ℤ, ModuleHasFiniteTorDimension (PR.obj.X i) := by
    intro i
    -- Proof comment: every restricted term has tor dimension at most `0` because the witness
    -- terms are `R`-flat.
    exact
      ((ModuleCat.hasTorDimensionLE_zero_iff_flat (R := R) (M := PR.obj.X i)).2 <| by
        simpa [PR] using hFlat i).hasFiniteTorDimension
  have hQResTor : HasFiniteTorDimension (DerivedCategory.Q.obj PR.obj) := by
    -- Proof comment: the bounded termwise tor-dimension theorem packages the termwise flatness
    -- over the restricted bounded complex.
    exact
      hasFiniteTorDimension_of_bounded_of_termwise_hasFiniteTorDimension
        (R := R) PR hTermTor
  have hResTor : HasFiniteTorDimension (ResDer.obj (DerivedCategory.Q.obj P.obj)) := by
    -- Proof comment: compare the restricted derived object with the derived image of the
    -- restricted strict complex.
    exact
      (hasFiniteTorDimension_of_iso (R := R)
        (Res.mapDerivedCategoryFactors.app P.obj)).2 hQResTor
  rw [DerivedCategory.IsPerfectOver]
  constructor
  · -- Proof comment: transport pseudo-coherence from the chosen representative back to `K`.
    exact Algebra.isPseudoCoherent_of_iso eK.symm hQPc
  · -- Proof comment: transport finite tor dimension through the restricted derived isomorphism.
    exact (hasFiniteTorDimension_of_iso (R := R) (ResDer.mapIso eK)).2 hResTor

-- Proof sketch: for `(→)`, represent `K` by a bounded-above finite-free complex using
-- pseudo-coherence, then truncate it using the finite tor-amplitude bounds and Lemma `15.67.2`
-- to obtain a bounded representative with termwise `R`-flat finitely presented terms. For `(←)`,
-- each term of a bounded representative is pseudo-coherent over `A` and has finite tor dimension
-- over `R`, hence is perfect over `R`; closure of `R`-perfect objects under shifts and cones from
-- Lemma `15.84.2` gives perfection of the whole complex.
variable (R) in
/-- Lemma 15.84.4: for a flat ring map `R → A` of finite presentation, an object `K` of `D(A)` is
perfect over `R` if and only if it is isomorphic in `D(A)` to a bounded cochain complex of
`A`-modules with `R`-flat finitely presented terms. -/
theorem isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
    (K : DModA) :
    DerivedCategory.IsPerfectOver R K ↔
      ∃ P : BoundedCpxA,
        CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj
            P.obj) ∧
          (∀ i : ℤ, Module.FinitePresentation A (P.obj.X i)) ∧
          IsIsomorphic K (DerivedCategory.Q.obj P.obj) := by
  constructor
  · intro hK
    rw [DerivedCategory.IsPerfectOver] at hK
    rcases hK.2 with ⟨a, b, hAmp⟩
    rcases hK.1 with ⟨E, ⟨c, hEc⟩, hEfree, α, hα⟩
    letI : E.IsTermwiseFiniteFree := hEfree
    let eα : Q.obj E ≅ K := asIso α
    let RE : CpxR := ResCpx.obj E
    have hREflat : RE.IsTermwiseFlat := by
      -- Proof comment: finite free `A`-terms are flat over `A`, hence flat over `R` by
      -- transitivity with the ambient flat algebra `A`.
      intro i
      let _ : Module.Free A (E.X i) := (hEfree.out i).1
      let _ : Module.Flat A (E.X i) := inferInstance
      simpa [RE] using (Module.Flat.trans R A (E.X i))
    have hREminus : CochainComplex.minus (ModuleCat R) RE := by
      exact (CochainComplex.minus_iff (ModuleCat R) RE).2 ⟨c,
        restrictScalarsComplex_isStrictlyLE (R := R) (A := A) hEc⟩
    let eRes : ResDer.obj K ≅ Q.obj RE :=
      (ResDer.mapIso eα.symm) ≪≫ Res.mapDerivedCategoryFactors.app E
    have hAmpRE : HasTorAmplitudeIn (Q.obj RE) a b := by
      -- Proof comment: transport the tor-amplitude interval from the restricted object `K|_R`
      -- to the chosen restricted cochain representative `RE`.
      exact (hasTorAmplitudeIn_of_iso (R := R) eRes).1 hAmp
    have hEbelow : ∀ i : ℤ, i < a → IsZero (E.homology i) := by
      intro i hi
      -- Proof comment: first read the vanishing on the restricted derived object, then compare
      -- restricted homology with the homology of the restricted complex, and finally reflect zero
      -- back through restriction of scalars.
      have hzeroK : IsZero ((HR i).obj (ResDer.obj K)) :=
        homology_isZero_of_hasTorAmplitudeIn_below (R := R) (ResDer.obj K) a b i hAmp hi
      have hzeroQ : IsZero ((HR i).obj (Q.obj RE)) := by
        exact hzeroK.of_iso ((HR i).mapIso eRes)
      have hzeroRE : IsZero (RE.homology i) := by
        exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app RE).isZero_iff.1 hzeroQ
      have hzeroResHom : IsZero (Res.obj (E.homology i)) := by
        exact hzeroRE.of_iso ((E.sc i).mapHomologyIso Res).symm
      exact isZero_of_restrictScalars_obj (f := algebraMap R A) (M := E.homology i) hzeroResHom
    have hπ : QuasiIso (E.πTruncGE a) := by
      -- Proof comment: the lower truncation is a quasi-isomorphism because the original
      -- pseudo-coherent model has no homology below the chosen lower tor-amplitude bound.
      exact quasiIso_piTruncGE_of_isZero_homology_below a E hEbelow
    let T : CpxA := E.truncGE a
    let RT : CpxR := ResCpx.obj T
    have hTGE : T.IsStrictlyGE a := by
      infer_instance
    have hRTflat : RT.IsTermwiseFlat := by
      intro i
      by_cases hi_lt : i < a
      · have hzero : IsZero (RT.X i) := by
          have hRTGE : RT.IsStrictlyGE a :=
            restrictScalarsComplex_isStrictlyGE (R := R) (A := A) hTGE
          rw [CochainComplex.isStrictlyGE_iff] at hRTGE
          exact hRTGE i hi_lt
        let hff : Module.Free R (RT.X i) ∧ Module.Finite R (RT.X i) :=
          moduleCat_finite_free_of_isZero (S := R) (RT.X i) hzero
        let _ : Module.Free R (RT.X i) := hff.1
        infer_instance
      · by_cases hi_eq : i = a
        · subst hi_eq
          -- Proof comment: the new boundary term is the cokernel controlled by Lemma `15.67.2`.
          simpa [RT, T] using
            CochainComplex.flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
              RE a hREminus hREflat hAmpRE.hasTorAmplitudeGE
        · have hai : a < i := by omega
          let eT : RT.X i ≅ RE.X i := by
            exact Res.mapIso (truncGE_term_iso_of_gt (K := E) a i hai)
          let _ : Module.Flat R (RE.X i) := hREflat i
          exact Module.Flat.of_retract eT.hom.hom eT.inv.hom (by
            ext x
            simp)
    have hTFp : ∀ i : ℤ, Module.FinitePresentation A (T.X i) := by
      intro i
      by_cases hi_lt : i < a
      · have hzero : IsZero (T.X i) := by
          rw [CochainComplex.isStrictlyGE_iff] at hTGE
          exact hTGE i hi_lt
        let hff : Module.Free A (T.X i) ∧ Module.Finite A (T.X i) :=
          moduleCat_finite_free_of_isZero (S := A) (T.X i) hzero
        let _ : Module.Free A (T.X i) := hff.1
        let _ : Module.Finite A (T.X i) := hff.2
        exact Module.finitePresentation_of_projective A (T.X i)
      · by_cases hi_eq : i = a
        · subst hi_eq
          -- Proof comment: finite presentation of the new cutoff term is the standard
          -- finitely-presented cokernel calculation for a termwise finite-free complex.
          change Module.FinitePresentation A
            (differentialCokernel (R := A) (E := E) a)
          simpa [differentialCokernel, CochainComplex.dFrom] using
            differential_cokernel_finitePresentation (R := A) (E := E) a
        · have hai : a < i := by omega
          let eT : T.X i ≅ E.X i := truncGE_term_iso_of_gt (K := E) a i hai
          let _ : Module.Free A (E.X i) := (hEfree.out i).1
          let _ : Module.Finite A (E.X i) := (hEfree.out i).2
          let _ : Module.FinitePresentation A (E.X i) :=
            Module.finitePresentation_of_projective A (E.X i)
          exact Module.FinitePresentation.of_equiv eT.symm.toLinearEquiv
    have hTLE : T.IsStrictlyLE (max a c) := by
      -- Proof comment: above `max a c` the truncated complex agrees with the original one, and
      -- the original pseudo-coherent representative already vanishes there.
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      have hai : a < i := lt_of_le_of_lt (le_max_left _ _) hi
      exact ((truncGE_term_iso_of_gt (K := E) a i hai).isZero_iff).2 (by
        rw [CochainComplex.isStrictlyLE_iff] at hEc
        exact hEc i (lt_of_le_of_lt (le_max_right _ _) hi))
    have hTbounded : CochainComplex.bounded (ModuleCat A) T := by
      exact
        (CochainComplex.bounded_iff (ModuleCat A) T).2
          ⟨(CochainComplex.plus_iff (ModuleCat A) T).2 ⟨a, hTGE⟩,
            (CochainComplex.minus_iff (ModuleCat A) T).2 ⟨max a c, hTLE⟩⟩
    let P : BoundedCpxA := ⟨T, hTbounded⟩
    let eT : K ≅ Q.obj T := eα.symm ≪≫ asIso (Q.map (E.πTruncGE a))
    -- Proof comment: the truncated bounded complex now carries the required termwise flatness
    -- and finite-presentation data, and still represents `K`.
    exact ⟨P, hRTflat, hTFp, ⟨eT⟩⟩
  · rintro ⟨P, hFlat, hFP, hIso⟩
    -- Proof comment: the reverse implication now factors through the bounded-packaging helper,
    -- leaving only the single-module pseudo-coherence descent as the remaining blocker.
    exact
      isPerfectOver_of_bounded_termwise_flat_finitePresentation_representative
        (R := R) (A := A) K P hFlat hFP hIso

end

end
end CategoryTheory
