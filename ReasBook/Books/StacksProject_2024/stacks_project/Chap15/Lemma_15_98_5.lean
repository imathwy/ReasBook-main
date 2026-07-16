import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_75_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_14
import StacksProject_2024.stacks_project.Chap15.Definition_15_92_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_88_5_TowerBridge

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory.TStructure
open Opposite
open CategoryTheory.SequentialInverseSystem
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- Helper for Lemma 15.98.5: a bounded-above derived module over a commutative ring admits a
bounded-above projective representative. -/
lemma boundedAbove_projective_model_of_mem_t_minus
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u} R))) K) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat.{u} R),
      IsIsomorphic K (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat.{u} R) ℤ)) := by
  letI : EnoughProjectives (ModuleCat.{u} R) := inferInstance
  let Kminus : boundedAboveDerivedCategory (ModuleCat.{u} R) := ⟨K, hK⟩
  -- Proof comment: a bounded-above derived object has a preimage complex with eventually zero
  -- homology, so the standard projective-resolution owner packages it into `ProjectiveMinus`.
  obtain ⟨b, hb⟩ :=
    boundedAbove_objPreimage_eventually_isZero_homology (𝒜 := ModuleCat.{u} R) Kminus
  obtain ⟨P⟩ :=
    nonempty_projectiveResolution_of_eventually_isZero_homology
      (K := DerivedCategory.Q.objPreimage K) ⟨b, hb⟩
  have hπ : IsIso (DerivedCategory.Q.map P.π) := by
    -- Proof comment: the projective-resolution comparison is a quasi-isomorphism, hence an
    -- isomorphism after passing to the derived category.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact
    ⟨P,
      ⟨((asIso (DerivedCategory.Q.map P.π)) ≪≫ DerivedCategory.Q.objObjPreimageIso K).symm⟩⟩

/-- Helper for Lemma 15.98.5: stagewise power-zero on a sequential system implies derived
completeness of any derived limit. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: this is exactly the public power-zero derived-completeness bridge from
  -- Lemma `15.92.14`, specialized to the current tower.
  exact
    CategoryTheory.isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
      I Ksys K' hpow hlim

/-- The sequential inverse system of quotient rings `A / I^(n+1)`. -/
abbrev idealPowerQuotientRingSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  sequentialRingSystem (fun n ↦ A ⧸ I ^ (n + 1))
    (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))

local notation "F" => idealPowerQuotientRingSystem I

/-- Each quotient stage `A / I^(n+1)` is naturally an `A`-algebra. -/
instance idealPowerQuotientStageRingAlgebra (n : ℕ) :
    Algebra A (stageRing F n) := by
  change Algebra A (A ⧸ I ^ (n + 1))
  exact RingHom.toAlgebra (Ideal.Quotient.mk (I ^ (n + 1)))

private theorem idealPowerQuotient_algebraMap_comp (n : ℕ) :
    algebraMap A (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap A (stageRing F (n + 1))) := by
  ext x
  change (algebraMap A (A ⧸ I ^ (n + 1))) x =
      ((stageTransitionRingHom F n).comp (algebraMap A (A ⧸ I ^ (n + 2)))) x
  have htransition : stageTransitionRingHom F n = Ideal.Quotient.factorPowSucc I (n + 1) := by
    simp [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom]
  rw [htransition]
  rfl

/-- The quotient transition maps are compatible with the ambient `A`-algebra structures. -/
instance idealPowerQuotientStageRingIsScalarTower (n : ℕ) :
    IsScalarTower A (stageRing F (n + 1)) (stageRing F n) := by
  exact IsScalarTower.of_algebraMap_eq' (idealPowerQuotient_algebraMap_comp (I := I) n)

/-- Each quotient transition ring is naturally an algebra over the previous quotient stage. -/
instance idealPowerQuotientSuccStageAlgebra (n : ℕ) :
    Algebra (A ⧸ I ^ (n + 2)) (A ⧸ I ^ (n + 1)) :=
  RingHom.toAlgebra (Ideal.Quotient.factorPowSucc I (n + 1))

/-- A compatible tower of derived quotient stages `K_n ∈ D(A / I^(n+1))`. -/
abbrev IdealPowerQuotientDerivedTower :=
  DerivedModuleTower (stageRing F) (stageTransitionRingHom F)

/- Domain-style sampling:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  the chapter bridge owner for stagewise restriction/base change and the derived-completeness owner;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChange`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal-power quotient tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, with derived completeness coming from
  `Definition_15_92_4`;
- primitive data: the tower `T : IdealPowerQuotientDerivedTower I` and the chosen derived limit
  `K` of the canonical fixed-base inverse system `stageRestrictionToBaseTower F A T`;
- derived API: the canonical fixed-base tower owner
  `stageRestrictionToBaseTower` and the upstream stagewise base-change owner
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the predicate
  `K.IsDerivedCompleteWithRespectTo I`.

Source/core/bridge triage:
- `source-facing`: the two statements of Lemma `15.98.5`;
- `core/canonical`: `CategoryTheory.IsDerivedLimit` and
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the quotient-stage
  base-change object `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, reused directly from
  `Lemma_15_98_4`. -/

/-- Helper for Lemma 15.98.5: on the `n`th quotient stage, the scalar `f^(n+1)` acts by zero
after restricting scalars back to `A`. -/
lemma ideal_power_quotient_stage_power_zero
    (T : IdealPowerQuotientDerivedTower I) {f : A} (hf : f ∈ I) (n : ℕ) :
    ∃ e : ℕ, (f ^ e : A) • 𝟙 (stageRestrictionToBase F A T n) = 0 := by
  let F₀ :=
    (ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let C := DerivedCategory.Q.objPreimage (T.obj n)
  let eT : DerivedCategory.Q.obj C ≅ T.obj n := DerivedCategory.Q.objObjPreimageIso (T.obj n)
  let eX :
      stageRestrictionToBase F A T n ≅ DerivedCategory.Q.obj (F₀.obj C) :=
    ((ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapDerivedCategory).mapIso
        eT.symm ≪≫
      (ModuleCat.restrictScalars (algebraMap A (stageRing F n))).mapDerivedCategoryFactors.app C
  have hpow_zero :
      (algebraMap A (stageRing F n)) (f ^ (n + 1)) = 0 := by
    -- Proof comment: `f^(n+1)` lands in `I^(n+1)`, so its image in the quotient stage vanishes.
    change Ideal.Quotient.mk (I ^ (n + 1)) (f ^ (n + 1)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hf (n + 1))
  have hcomplex_zero :
      ((f ^ (n + 1) : A) • 𝟙 (F₀.obj C)) = 0 := by
    -- Proof comment: after restriction of scalars, the scalar action is multiplication by the
    -- image of `f^(n+1)` in `A / I^(n+1)`, which is already zero.
    ext i x
    change (((algebraMap A (stageRing F n)) (f ^ (n + 1)) : stageRing F n) •
        (show C.X i from x)) = 0
    rw [hpow_zero, zero_smul]
  have hderived_zero :
      (f ^ (n + 1) : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C)) = 0 := by
    -- Proof comment: applying `Q` to the zero complex endomorphism gives zero in the derived
    -- category, and `Q` preserves scalar multiples of identity morphisms.
    simpa [Functor.map_smul] using congrArg DerivedCategory.Q.map hcomplex_zero
  refine ⟨n + 1, ?_⟩
  -- Proof comment: transport the zero scalar endomorphism back across the comparison isomorphism
  -- between the restricted stage and its strict cochain model.
  calc
    (f ^ (n + 1) : A) • 𝟙 (stageRestrictionToBase F A T n) =
        eX.hom ≫ ((f ^ (n + 1) : A) • 𝟙 (DerivedCategory.Q.obj (F₀.obj C))) ≫ eX.inv := by
          simp [CategoryTheory.Linear.comp_smul, CategoryTheory.Linear.smul_comp]
    _ = 0 := by simp [hderived_zero]

-- Proof sketch: restrict the tower `K_n` from `D(A / I^(n+1))` to `D(A)`. On stage `n`, the
-- ideal power `I^(n+1)` acts trivially, so for every `f ∈ I` a sufficiently large power of `f`
-- kills the `n`th stage. Apply Lemma `15.92.14` to the resulting inverse system in `D(A)`.
/-- Lemma 15.98.5 (1): let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` viewed over `A`. Then `K` is
derived complete with respect to `I`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    : K.IsDerivedCompleteWithRespectTo I := by
  -- Proof comment: Lemma `15.92.14` applies once each quotient stage is killed by a suitable
  -- power of every `f ∈ I`; here the textbook exponent is exactly the stage index plus one.
  refine CategoryTheory.isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    I (stageRestrictionToBaseTower F A T) K ?_ hKlim
  intro f hf n
  exact ideal_power_quotient_stage_power_zero (I := I) T hf n

section

variable [IsNoetherianRing A]

/-- Helper for Lemma 15.98.5: the transition kernel is contained in the nilradical of the
successor quotient ring. -/
private theorem idealPowerQuotient_transition_kernel_le_nilradical (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)) ≤ nilradical (A ⧸ I ^ (n + 2)) := by
  intro x hx
  rcases Ideal.Quotient.mk_surjective x with ⟨a, rfl⟩
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  have ha : a ∈ I ^ (n + 1) := by
    change Ideal.Quotient.factorPowSucc I (n + 1) (Ideal.Quotient.mk (I ^ (n + 2)) a) = 0 at hx
    change Ideal.Quotient.mk (I ^ (n + 1)) a = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.1 hx
  have hsq_mem_high :
      a ^ 2 ∈ I ^ ((n + 1) + (n + 1)) := by
    simpa [pow_add, pow_two] using (Ideal.mul_mem_mul ha ha : a * a ∈ I ^ (n + 1) * I ^ (n + 1))
  have hsq_mem : a ^ 2 ∈ I ^ (n + 2) := by
    exact
      (Ideal.pow_le_pow_right (show n + 2 ≤ (n + 1) + (n + 1) by omega)) hsq_mem_high
  -- Proof comment: kernel elements are represented by classes from `I^(n+1)`, whose square
  -- lands in `I^(n+2)`, so they are nilpotent already with exponent `2`.
  simpa [pow_two] using
    (Ideal.Quotient.eq_zero_iff_mem.2 hsq_mem :
      Ideal.Quotient.mk (I ^ (n + 2)) (a ^ 2) = 0)

/-- Helper for Lemma 15.98.5: the kernel of the quotient transition
`A / I^(n + 2) → A / I^(n + 1)` is nilpotent. -/
lemma idealPowerQuotient_transition_kernel_isNilpotent (n : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))) := by
  -- Proof comment: in the Noetherian successor quotient ring, containment in the nilradical is
  -- equivalent to nilpotence of the ideal.
  exact
    (Ideal.FG.isNilpotent_iff_le_nilradical
      (IsNoetherian.noetherian (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))))).2
      (idealPowerQuotient_transition_kernel_le_nilradical (I := I) n)

/-- Helper for Lemma 15.98.5: the successor quotient transition
`A / I^(n + 2) → A / I^(n + 1)` is surjective. -/
lemma idealPowerQuotient_factorPowSucc_surjective (n : ℕ) :
    Function.Surjective (Ideal.Quotient.factorPowSucc I (n + 1)) := by
  intro x
  rcases Ideal.Quotient.mk_surjective x with ⟨a, rfl⟩
  -- Proof comment: every class modulo `I^(n+1)` is represented by an element of `A`, and the
  -- same representative defines a preimage modulo `I^(n+2)`.
  refine ⟨Ideal.Quotient.mk (I ^ (n + 2)) a, ?_⟩
  rfl

/-- Helper for Lemma 15.98.5: normalize the quotient of `A / I^(n + 2)` by the kernel of the
successor transition to the previous quotient `A / I^(n + 1)`. -/
noncomputable def idealPowerQuotient_factorPowSucc_quotientKerEquiv (n : ℕ) :
    ((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))) ≃+*
      (A ⧸ I ^ (n + 1)) :=
  RingHom.quotientKerEquivOfSurjective
    (f := Ideal.Quotient.factorPowSucc I (n + 1))
    (idealPowerQuotient_factorPowSucc_surjective (I := I) n)

/-- Helper for Lemma 15.98.5: the normalized quotient-kernel equivalence evaluates on quotient
classes by the original successor transition map. -/
lemma idealPowerQuotient_factorPowSucc_quotientKerEquiv_mk
    (n : ℕ) (x : A ⧸ I ^ (n + 2)) :
    idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n
      (Ideal.Quotient.mk (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))) x) =
      Ideal.Quotient.factorPowSucc I (n + 1) x := by
  -- Proof comment: this is exactly the defining computation rule of
  -- `RingHom.quotientKerEquivOfSurjective`.
  simp [idealPowerQuotient_factorPowSucc_quotientKerEquiv]

/-- Helper for Lemma 15.98.5: the inverse normalized quotient-kernel equivalence recovers the
canonical quotient class in `((A / I^(n + 2)) / ker)`. -/
lemma idealPowerQuotient_factorPowSucc_quotientKerEquiv_symm_apply
    (n : ℕ) (x : A ⧸ I ^ (n + 2)) :
    (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n).symm
      (Ideal.Quotient.factorPowSucc I (n + 1) x) =
      Ideal.Quotient.mk (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))) x := by
  -- Proof comment: rewrite the target by the forward computation rule and then cancel the ring
  -- equivalence with its inverse.
  rw [← idealPowerQuotient_factorPowSucc_quotientKerEquiv_mk (I := I) n x]
  exact (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n).symm_apply_apply _

/-- Helper for Lemma 15.98.5: scalar extension across a ring equivalence agrees with the inverse
restriction-of-scalars equivalence. -/
noncomputable def extendScalars_iso_restrictScalars_inverse
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ModuleCat.extendScalars e.toRingHom ≅ ModuleCat.restrictScalars e.symm := by
  -- Proof comment: both functors are left adjoint to restriction along `e`, so left-adjoint
  -- uniqueness identifies them.
  exact
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- Helper for Lemma 15.98.5: restriction of scalars across the normalized quotient-kernel ring
equivalence transports a bounded-above projective stage model to the quotient-side ring. -/
noncomputable def factorPowSucc_kernel_transport_projective_minus
    (n : ℕ)
    (P : CochainComplex.ProjectiveMinus (ModuleCat (A ⧸ I ^ (n + 1)))) :
    CochainComplex.ProjectiveMinus
      (ModuleCat
        (((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))))) := by
  classical
  let e := idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n
  let E :
      CochainComplex
        (ModuleCat
          (((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))))) ℤ :=
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ)
  let b : ℤ := Classical.choose P.exists_isStrictlyLE
  have hPb : (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ).IsStrictlyLE b :=
    Classical.choose_spec P.exists_isStrictlyLE
  have hEbound : E.IsStrictlyLE b := by
    -- Proof comment: restriction of scalars across the ring equivalence preserves the same
    -- degreewise zero terms, hence the same upper support bound.
    rw [CochainComplex.isStrictlyLE_iff] at hPb ⊢
    intro i hi
    change IsZero (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.obj
      ((P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ).X i)))
    simpa [E, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.map_isZero (hPb i hi))
  refine ⟨⟨E, (CochainComplex.minus_iff _ E).2 ⟨b, hEbound⟩⟩, fun i ↦ ?_⟩
  -- Proof comment: projective terms stay projective under an equivalence of module categories.
  let M : ModuleCat (A ⧸ I ^ (n + 1)) :=
    (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ).X i
  let N :
      ModuleCat
        (((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))) :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.obj M
  let _ : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    ⟨by
        ext x
        simp
      , by
        ext x
        simp⟩
  let _ : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    ⟨by
        ext x
        simp
      , by
        ext x
        simp⟩
  let _ : Module.Projective (A ⧸ I ^ (n + 1)) M := by
    let _ : Projective M := P.term_mem i
    infer_instance
  let eTerm : M ≃ₛₗ[e.symm.toRingHom] N :=
    { __ := AddEquiv.refl M
      map_smul' := by
        intro s x
        change s • x = (e.toRingHom (e.symm.toRingHom s)) • x
        simp }
  let _ : Module.Projective
      (((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))) N :=
    Module.Projective.of_equiv
      (σ := e.symm.toRingHom)
      (σ' := e.toRingHom)
      eTerm
  simpa [E, M, N, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (show Projective N from inferInstance)

/-- Helper for Lemma 15.98.5: reducing a successor-stage complex modulo the transition kernel and
then transporting it back across the quotient-kernel equivalence is the same as reducing directly
along `A / I^(n+2) → A / I^(n+1)`. -/
noncomputable def factorPowSucc_kernel_inverse_extendScalars_obj_iso
    (n : ℕ)
    (X : CochainComplex (ModuleCat (A ⧸ I ^ (n + 2))) ℤ) :
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).inverse.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars
              (Ideal.Quotient.mk
                (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))))
            (ComplexShape.up ℤ)).obj X))) ≅
      ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
          (ComplexShape.up ℤ)).obj X) := by
  let e := idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n
  let σ :=
    Ideal.Quotient.mk (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))
  let τ := e.toRingHom
  have hcomp : τ.comp σ = Ideal.Quotient.factorPowSucc I (n + 1) := by
    ext x
    -- Proof comment: the quotient-kernel equivalence was defined so that its forward map is the
    -- original successor transition on quotient representatives.
    simpa [σ, τ] using
      idealPowerQuotient_factorPowSucc_quotientKerEquiv_mk (I := I) n x
  let Y :
      CochainComplex
        (ModuleCat
          (((A ⧸ I ^ (n + 2)) ⧸ RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))))) ℤ :=
    ((Functor.mapHomologicalComplex
      (ModuleCat.extendScalars σ)
      (ComplexShape.up ℤ)).obj X)
  let η₁ :
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y) ≅
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars τ)
            (ComplexShape.up ℤ)).obj Y)) :=
    ((CategoryTheory.NatIso.mapHomologicalComplex
      (extendScalars_iso_restrictScalars_inverse (e := e))
      (ComplexShape.up ℤ)).app Y).symm
  let η₂ :
      (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars τ)
            (ComplexShape.up ℤ)).obj Y)) ≅
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
          (ComplexShape.up ℤ)).obj X) := by
    -- Proof comment: composing extension of scalars along `σ` and then `τ` is extension of
    -- scalars along `τ.comp σ = factorPowSucc`.
    simpa [Y] using
      (CategoryTheory.NatIso.mapHomologicalComplex
        ((ModuleCat.extendScalarsComp σ τ).symm ≪≫
          eqToIso (congrArg (fun u ↦ ModuleCat.extendScalars u) hcomp))
        (ComplexShape.up ℤ)).app X
  exact η₁.trans η₂

/-- Helper for Lemma 15.98.5: transporting a stage model across the quotient-kernel ring
equivalence and then applying the inverse transport recovers the original complex. -/
noncomputable def factorPowSucc_kernel_transport_counit_iso
    (n : ℕ)
    (P : CochainComplex.ProjectiveMinus (ModuleCat (A ⧸ I ^ (n + 1)))) :
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).inverse.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
            (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ))) ≅
      (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ) := by
  let e := idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n
  -- Proof comment: this is the unit isomorphism of the restriction-of-scalars equivalence,
  -- applied degreewise to cochain complexes.
  exact
    ((NatIso.mapHomologicalComplex
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso
      (ComplexShape.up ℤ)).app
        (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ)).symm

/-- Helper for Lemma 15.98.5: the bounded-above first quotient stage admits a bounded-above
projective representative over `A / I`. -/
lemma exists_boundedAbove_projective_stage_zero_model
    (T : IdealPowerQuotientDerivedTower I)
    (hK₁_bounded : ∃ b : ℤ, (T.obj 0).IsLE b) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat (stageRing F 0)),
      IsIsomorphic
        (T.obj 0)
        (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat (stageRing F 0)) ℤ)) := by
  rcases hK₁_bounded with ⟨b, hb⟩
  -- Proof comment: stage `0` is already an object over `stageRing F 0 = A / I`, so the generic
  -- bounded-above projective-representative lemma applies directly.
  exact boundedAbove_projective_model_of_mem_t_minus (K := T.obj 0) ⟨b, hb⟩

/-- Helper for Lemma 15.98.5: after transporting across the quotient-kernel ring equivalence,
derived reduction modulo the transition kernel agrees with direct derived reduction to the
previous quotient stage. -/
noncomputable def factorPowSucc_kernel_inverse_extendScalars_iso
    (n : ℕ)
    (K : DerivedCategory (ModuleCat (A ⧸ I ^ (n + 2)))) :
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).inverse.mapDerivedCategory).obj
        (K ⊗[(A ⧸ I ^ (n + 2))]^L[
          ((A ⧸ I ^ (n + 2)) ⧸
            RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))]) ≅
      (K ⊗[(A ⧸ I ^ (n + 2))]^L[(A ⧸ I ^ (n + 1))]) := by
  let e := idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n
  let C := DerivedCategory.Q.objPreimage K
  let σ :=
    Ideal.Quotient.mk (RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))
  let eK : DerivedCategory.Q.obj C ≅ K :=
    DerivedCategory.Q.objObjPreimageIso K
  -- Proof comment: compute both derived reductions through the same strict preimage complex, then
  -- insert the already-proved strict comparison
  -- `factorPowSucc_kernel_inverse_extendScalars_obj_iso`.
  calc
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).obj
        (K ⊗[(A ⧸ I ^ (n + 2))]^L[
          ((A ⧸ I ^ (n + 2)) ⧸
            RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1)))])) ≅
      (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).obj
        (DerivedCategory.Q.obj
          (((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars σ)
              (ComplexShape.up ℤ)).obj C)))) := by
            exact
              (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategory).mapIso
                (((derivedTensorWithAlgebra σ).mapIso eK.symm) ≪≫
                  ((ModuleCat.extendScalars σ).mapDerivedCategoryFactors.app C)))
    _ ≅
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars σ)
              (ComplexShape.up ℤ)).obj C)))) := by
            exact
              ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).inverse.mapDerivedCategoryFactors.app
                (((Functor.mapHomologicalComplex
                    (ModuleCat.extendScalars σ)
                    (ComplexShape.up ℤ)).obj C)))
    _ ≅
      (DerivedCategory.Q.obj
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
            (ComplexShape.up ℤ)).obj C))) := by
            exact
              DerivedCategory.Q.mapIso
                (factorPowSucc_kernel_inverse_extendScalars_obj_iso (I := I) n C)
    _ ≅
      (K ⊗[(A ⧸ I ^ (n + 2))]^L[(A ⧸ I ^ (n + 1))]) := by
            exact
              ((((derivedTensorWithAlgebra (Ideal.Quotient.factorPowSucc I (n + 1))).mapIso
                  eK.symm) ≪≫
                ((ModuleCat.extendScalars
                    (Ideal.Quotient.factorPowSucc I (n + 1))).mapDerivedCategoryFactors.app C)).symm)

/-- Helper for Lemma 15.98.5: transporting a projective stage model across the quotient-kernel
ring equivalence commutes with passing to the derived category. -/
noncomputable def factorPowSucc_kernel_transport_q_obj_iso
    (n : ℕ)
    (P : CochainComplex.ProjectiveMinus (ModuleCat (A ⧸ I ^ (n + 1)))) :
    (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).functor.mapDerivedCategory).obj
        (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ))) ≅
      (DerivedCategory.Q.obj
        (factorPowSucc_kernel_transport_projective_minus (I := I) n P :
          CochainComplex
            (ModuleCat
              (((A ⧸ I ^ (n + 2)) ⧸
                RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))))) ℤ)) := by
  -- Proof comment: this is exactly the canonical `mapDerivedCategoryFactors` comparison for the
  -- transported strict complex.
  simpa [factorPowSucc_kernel_transport_projective_minus] using
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (idealPowerQuotient_factorPowSucc_quotientKerEquiv (I := I) n)).functor.mapDerivedCategoryFactors.app
        (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ))

/-- Helper for Lemma 15.98.5: a bounded-above projective model at stage `n` lifts across the
successor quotient map to a bounded-above projective model at stage `n + 1`, and its strict
reduction recovers the original stage model. -/
lemma strict_boundedAbove_projective_stage_succ
    (T : IdealPowerQuotientDerivedTower I) (n : ℕ)
    (P :
      CochainComplex.ProjectiveMinus
        (ModuleCat (A ⧸ I ^ (n + 1))))
    (eP :
      IsIsomorphic
        (T.obj n)
        (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ)))
    (hstage :
      IsIsomorphic
        (T.obj (n + 1) ⊗[(A ⧸ I ^ (n + 2))]^L[(A ⧸ I ^ (n + 1))])
        (T.obj n)) :
    ∃ P' : CochainComplex.ProjectiveMinus (ModuleCat (A ⧸ I ^ (n + 2))),
      IsIsomorphic
          (T.obj (n + 1))
          (DerivedCategory.Q.obj (P' : CochainComplex (ModuleCat (A ⧸ I ^ (n + 2))) ℤ)) ∧
        IsIsomorphic
          ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (Ideal.Quotient.factorPowSucc I (n + 1)))
              (ComplexShape.up ℤ)).obj
            (P' : CochainComplex (ModuleCat (A ⧸ I ^ (n + 2))) ℤ))
          (P : CochainComplex (ModuleCat (A ⧸ I ^ (n + 1))) ℤ) := by
  sorry

-- Proof sketch: choose bounded-above flat representatives for the stages using the bounded-above
-- hypothesis on `K_1` and the nilpotent lifting statement of Lemma `15.76.3`, then represent the
-- derived limit by the termwise inverse limit complex. Tensoring this bounded-above flat complex
-- with `A / I^(n+1)` commutes with the inverse limit and stabilizes at stage `n`, giving the
-- desired identification with `K_n`.
/-- Lemma 15.98.5 (2): let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` whose stagewise derived
reductions `K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1)` identify with `K_n`. If the
first stage `K_1` is bounded above, then the derived base change of `K` to each quotient
`A / I^(n+1)` recovers `K_n`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_boundedAbove_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁_bounded : ∃ b : ℤ, (T.obj 0).IsLE b)
    (hstageBaseChange :
      ∀ n : ℕ,
        IsIsomorphic
          (T.obj (n + 1) ⊗[(A ⧸ I ^ (n + 2))]^L[(A ⧸ I ^ (n + 1))])
          (T.obj n)) :
    ∀ n : ℕ, IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) :=
  -- Route correction: the stage-`0` bounded-above projective model and the nilpotent quotient
  -- kernels are now available as local helpers. The remaining gap is the source-faithful bridge
  -- that transports each strict stage model over `A / I^(n+1)` across the quotient equivalence
  -- attached to `RingHom.ker (Ideal.Quotient.factorPowSucc I (n + 1))`, and then packages the
  -- resulting strict models into one fixed-base sequential-system complex over `A`.
  -- TODO: inductively lift the stage-`0` projective model using
  -- `exists_boundedAbove_projective_representative_lifting_mod_nilpotent`, with the quotient-side
  -- comparison transported across `(A ⧸ I ^ (n + 2)) ⧸ ker(factorPowSucc) ≅ A ⧸ I ^ (n + 1)`.
  -- After strictifying the resulting tower over `A`, apply
  -- `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`, identify the derived limit
  -- with the ordinary termwise inverse-limit complex, and compute tensor by eventual
  -- stabilization modulo `I^(n+1)`.
  sorry

end

end
