import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.Chap15.Lemma_15_101_1
import StacksProject_2024.Chap15.Remark_15_101_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open IadicFiniteModuleSystem
open Opposite

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {B : Type u} [CommRing B] [IsNoetherianRing B] [Algebra A B]

local notation "SeqModA" => SequentialInverseSystem (ModuleCat A)

/- Domain-style sampling for Lemma 15.101.11:
- primary domain: commutative algebra and homological algebra of `Ext` towers over ideal-power
  quotients and their inverse limits;
- sampled owner declarations:
  `idealPowerModuleQuotient`,
  `IadicFiniteModuleSystem.stageRing`,
  `SeqRingMod`,
  `sequentialRingedModuleEvaluation`;
- best owner abstraction: the quotient-side tower should reuse the chapter owners
  `idealPowerModuleQuotient` and `SequentialInverseSystem (ModuleCat A)` rather than a raw
  quotient type and raw `ℕᵒᵖ ⥤ ModuleCat A` witness; on the reduction side, a strict varying-ring
  representative should be carried by
  `SeqRingMod (fun n ↦ stageRing B ((Ideal.map (algebraMap A B) I)) (Nat.succPNat n)) ...`, with
  the A-module inverse system obtained by the canonical restriction-of-scalars bridge rather than
  by an arbitrary bare `SequentialInverseSystem (ModuleCat A)`;
- primitive data: the ideal `I`, the modules `M` and `N`, the degree `i`, and the stagewise
  quotient and reduction `Ext` objects;
- derived API: the quotient tower `extIdealPowerQuotientTower`, the strict varying-ring owner
  `SeqRingMod ...` for a reduction-side representative, and the A-restricted tower derived from
  that owner.

Source/core/bridge triage:
- `source-facing`: the quotient stages
  `Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)` and the reduced stages
  `Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)`;
- `core/canonical`: `idealPowerModuleQuotient`, `SeqRingMod`,
  `sequentialRingedModuleEvaluation`, `SequentialInverseSystem (ModuleCat A)`,
  `Functor.ofOpSequence`, `extIdealPowerQuotientTower`, and `limit`;
- `bridge/view`: the A-restricted sequential tower attached to a strict
  `SeqRingMod` representative of the reduced stages. -/

variable (B)

private abbrev extIdealPower (I : Ideal A) (n : ℕ) : Ideal B :=
  (Ideal.map (algebraMap A B) I) ^ (n + 1)

variable {B}

/-- The `n`th quotient stage
`Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)`, viewed as an `A`-module. -/
private abbrev extIdealPowerQuotientStage (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj <|
    ModuleCat.of B (idealPowerModuleQuotient (Ideal.map (algebraMap A B) I) (Ext M N i) n)

/-- The transition morphism
`Ext^i_B(M, N) / I^(n+2) Ext^i_B(M, N) ⟶ Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)`. -/
private abbrev extIdealPowerQuotientStep (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    extIdealPowerQuotientStage I M N i (n + 1) ⟶
      extIdealPowerQuotientStage I M N i n :=
  (ModuleCat.restrictScalars (algebraMap A B)).map <|
    ModuleCat.ofHom
      (AdicCompletion.transitionMap (Ideal.map (algebraMap A B) I) (Ext M N i)
        (Nat.le_succ (n + 1)))

/-- The sequential inverse system
`(Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N))_n`, indexed from `n = 0`. -/
abbrev extIdealPowerQuotientTower (I : Ideal A) (M N : ModuleCat B) (i : ℕ) : SeqModA :=
  Functor.ofOpSequence (extIdealPowerQuotientStep I M N i)

/-- The quotient module `M / I^(n+1) M`, viewed over `B / I^(n+1) B`. -/
private abbrev extIdealPowerQuotientModule (I : Ideal A) (M : ModuleCat B) (n : ℕ) :
    ModuleCat (B ⧸ (extIdealPower B I n : Ideal B)) :=
  ModuleCat.of
    (B ⧸ (extIdealPower B I n : Ideal B))
    (M ⧸ (((extIdealPower B I n : Ideal B)) • (⊤ : Submodule B M)))

/-- The stage `Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)` as a module over
`B / I^(n+1) B`. -/
abbrev extIdealPowerReductionStageOverQuotient
    (I : Ideal A) (M N : ModuleCat B) (i n : ℕ) :
    ModuleCat (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)) :=
  ModuleCat.of (B ⧸ (extIdealPower B I n : Ideal B))
    (Ext
      (extIdealPowerQuotientModule I M n)
      (extIdealPowerQuotientModule I N n)
      i)

omit [IsNoetherianRing A] in
private theorem extIdealPowerReductionTransition_comp_algebraMap
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1))).comp
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1)))) =
      algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)) :=
  rfl

/-- Evaluation of a strict reduction-side `SeqRingMod` representative at stage `n`,
followed by restriction of scalars to `A`. -/
private abbrev extIdealPowerReductionTowerEvaluation
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    SeqRingMod
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) ⥤
      ModuleCat A :=
  sequentialRingedModuleEvaluation
      (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
      (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
        (Nat.le_succ (n + 1))) n ⋙
    ModuleCat.restrictScalars
      (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)))

/-- The successor transition on the A-restricted tower attached to a strict reduction-side
`SeqRingMod` representative. -/
private abbrev extIdealPowerReductionTowerStep
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) :
    extIdealPowerReductionTowerEvaluation B I (n + 1) ⟶
      extIdealPowerReductionTowerEvaluation B I n :=
  (Functor.whiskerRight
      (sequentialRingedModuleEvaluationStep
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) n)
      (ModuleCat.restrictScalars
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1)))))) ≫
    Functor.whiskerLeft
      (sequentialRingedModuleEvaluation
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
          (Nat.le_succ (n + 1))) n)
      ((ModuleCat.restrictScalarsComp'
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat (n + 1))))
        (Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1)))
        (algebraMap A (stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)))
        (extIdealPowerReductionTransition_comp_algebraMap B I n)).inv)

/-- The sequential inverse system of `A`-modules obtained from a strict reduction-side
`SeqRingMod` representative by stagewise restriction of scalars. -/
abbrev extIdealPowerReductionTowerOverA
    (I : Ideal A)
    (T :
      SeqRingMod
        (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
        (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1)))) :
    SeqModA :=
  @Functor.ofOpSequence (ModuleCat A) _
    (fun n ↦ (extIdealPowerReductionTowerEvaluation B I n).obj T)
    (fun n ↦ (extIdealPowerReductionTowerStep B I n).app T)

/-- Helper for Lemma 15.101.11: the stage ring `B / I^(n+1)B` in the strict reduction-side
sequential ring system. -/
private abbrev extIdealPowerReductionRing (I : Ideal A) (n : ℕ) : Type u :=
  stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n)

/-- Helper for Lemma 15.101.11: the successor ring map
`B / I^(n+2)B → B / I^(n+1)B` in the strict reduction-side sequential ring system. -/
private abbrev extIdealPowerReductionRingStep (I : Ideal A) (n : ℕ) :
    extIdealPowerReductionRing (B := B) I (n + 1) →+*
      extIdealPowerReductionRing (B := B) I n :=
  Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1))

/-- Helper for Lemma 15.101.11: if a strict reduction-side object with the correct stages and
inverse limit has already been constructed, the target theorem is immediate. -/
private theorem exists_extIdealPowerReductionTower_of_data
    (I : Ideal A) (M N : ModuleCat B) (i : ℕ)
    (T :
      SeqRingMod
        (fun n ↦ extIdealPowerReductionRing (B := B) I n)
        (fun n ↦ extIdealPowerReductionRingStep (B := B) I n))
    (hstage :
      ∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ extIdealPowerReductionRing (B := B) I n)
            (fun n ↦ extIdealPowerReductionRingStep (B := B) I n) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n))
    (hlimit :
      IsIsomorphic
        (limit (extIdealPowerQuotientTower I M N i))
        (limit (extIdealPowerReductionTowerOverA I T))) :
    ∃ T :
        SeqRingMod
          (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
          (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
            (Nat.le_succ (n + 1))),
      (∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
            (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
              (Nat.le_succ (n + 1))) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n)) ∧
        IsIsomorphic
          (limit (extIdealPowerQuotientTower I M N i))
          (limit (extIdealPowerReductionTowerOverA I T)) := by
  -- This is only the final packaging step; the real work is constructing `T`, `hstage`, and
  -- `hlimit` from the chosen finite free resolution.
  exact ⟨T, hstage, hlimit⟩

/-- Helper for Lemma 15.101.11: every degree of the cochain view of a chosen free resolution is
projective. This is the bounded-above projective input used before forming the ambient Hom
complex. -/
private theorem chosen_resolution_view_term_projective
    (M : ModuleCat B)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat B)).obj M)
    [ChainComplex.IsFreeResolution π]
    (n : ℤ) :
    Projective ((F.extend ComplexShape.embeddingDownNat).X n) := by
  by_cases hnonpos : n ≤ 0
  · let e :
        (F.extend ComplexShape.embeddingDownNat).X n ≅ F.X (Int.toNat (-n)) :=
      F.extendXIso ComplexShape.embeddingDownNat (by
        have hneg : 0 ≤ -n := by linarith
        simpa [ComplexShape.embeddingDownNat, Int.toNat_of_nonneg hneg] using
          (show -((Int.toNat (-n) : ℕ) : ℤ) = n by
            rw [Int.toNat_of_nonneg hneg]
            omega))
    -- Negative cochain degrees come from free chain terms, so projectivity is transported across
    -- the canonical `extendXIso`.
    letI : Module.Free B (F.X (Int.toNat (-n))) :=
      ChainComplex.IsFreeResolution.free (R := B) π (Int.toNat (-n))
    exact Projective.of_iso e inferInstance
  · have hpos : 0 < n := by omega
    let hzero :
        CategoryTheory.Limits.IsZero ((F.extend ComplexShape.embeddingDownNat).X n) :=
      F.isZero_extend_X ComplexShape.embeddingDownNat n fun j hj ↦ by
        have hnonpos' : (ComplexShape.embeddingDownNat.f j : ℤ) ≤ 0 := by
          simp [ComplexShape.embeddingDownNat]
        rw [hj] at hnonpos'
        omega
    -- Positive cochain degrees vanish after reindexing, so they are automatically projective.
    exact Projective.of_iso hzero.isoZero (by infer_instance)

/-- Helper for Lemma 15.101.11: the cochain view of a chosen free resolution packages as the
standard bounded-above quasi-isomorphism with projective terms. -/
private theorem chosen_resolution_view_strictlyLE_quasiIso_with_projective_terms
    (M : ModuleCat B)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat B)).obj M)
    [ChainComplex.IsFreeResolution π] :
    IsStrictlyLEQuasiIsoWithTermsIn (isProjective (ModuleCat B)) 0
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M)
      (F.extend ComplexShape.embeddingDownNat)
      (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat) where
  quasiIso := by
    -- Extending the augmentation by zero preserves the chosen free-resolution quasi-isomorphism.
    infer_instance
  strictlyLE := by
    -- The source proof uses the cochain view supported in nonpositive degrees.
    infer_instance
  term_mem n := by
    -- The only extra owner datum is termwise projectivity of the reindexed complex.
    letI : Projective ((F.extend ComplexShape.embeddingDownNat).X n) :=
      chosen_resolution_view_term_projective (M := M) π n
    infer_instance

/-- Helper for Lemma 15.101.11: the chosen cochain resolution view is available as a Chapter `13`
projective-resolution owner of `M[0]`. -/
private noncomputable abbrev chosen_resolution_view_projectiveResolution
    (M : ModuleCat B)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat B)).obj M)
    [ChainComplex.IsFreeResolution π] :
    CochainComplex.ProjectiveResolution ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) :=
  (chosen_resolution_view_strictlyLE_quasiIso_with_projective_terms (M := M) π).toProjectiveResolution

/-- Helper for Lemma 15.101.11: the cochain view of a chosen free resolution computes the derived
degree-zero object `M[0]`. This fixes the ambient source-side object before quotienting the Hom
complex. -/
private theorem chosen_resolution_view_single0_iso
    (M : ModuleCat B)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (ChainComplex.single₀ (ModuleCat B)).obj M)
    [ChainComplex.IsFreeResolution π] :
    Nonempty
      (DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ≅
        (DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) := by
  let f :
      DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ⟶
        DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat B)).obj M).extend
          ComplexShape.embeddingDownNat) :=
    DerivedCategory.Q.map (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat)
  have hf : IsIso f := by
    -- The chosen free resolution is already a quasi-isomorphism before reindexing.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e :
      DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ≅
        DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat B)).obj M).extend
          ComplexShape.embeddingDownNat) :=
    asIso f
  refine ⟨e ≪≫ ?_⟩
  -- Normalize the extended single complex back to the canonical derived object `M[0]`.
  exact
    (DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M).symm

-- Proof sketch: choose a resolution of the finite `B`-module `M` by finite free `B`-modules.
-- Because `B` and `M` are flat over `A`, reduction modulo `I^(n+1)` stays exact and computes
-- `Ext^i` over `B / I^(n+1) B`. The resulting levelwise identifications of the Hom complexes with
-- the quotients modulo `I^(n+1)` reduce the statement to Lemma `15.101.1 (2)` for the associated
-- homology towers.
/-- Helper for Lemma 15.101.11: after choosing one finite free `B`-resolution of `M`, the
remaining source-faithful task is to construct the strict quotient-Hom tower whose stages compute
the reduced `Ext` groups and whose restricted inverse limit compares with the quotient tower of
ambient `Ext`. -/
private theorem chosen_finite_free_resolution_yields_reduction_tower_data
    (I : Ideal A) (M N : ModuleCat B)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat B)) M))
    [ChainComplex.IsFiniteFreeResolution π] :
    ∃ T :
        SeqRingMod
          (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
          (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
            (Nat.le_succ (n + 1))),
      (∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
            (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
              (Nat.le_succ (n + 1))) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n)) ∧
        IsIsomorphic
          (limit (extIdealPowerQuotientTower I M N i))
          (limit (extIdealPowerReductionTowerOverA I T)) := by
  -- Route correction: the proof route is now fixed at the chosen-resolution stage.
  -- First freeze the source-faithful ambient objects coming from the chosen resolution.
  let P := chosen_resolution_view_projectiveResolution (M := M) π
  let E :=
    CochainComplex.HomComplex
      (P : CochainComplex.ProjectiveMinus (ModuleCat B))
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj N)
  let S :
      ShortComplex (ModuleCat A) :=
    (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      E).sc (i : ℤ)
  have hsingle :
      Nonempty
        (DerivedCategory.Q.obj (F.extend ComplexShape.embeddingDownNat) ≅
          (DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) :=
    chosen_resolution_view_single0_iso (M := M) π
  -- The remaining work is now exactly the source-faithful strict quotient-Hom construction for
  -- this ambient short complex.
  -- TODO: build the strict quotient-Hom system attached to `S`, identify the ambient left
  -- homology with `Ext^i_B(M, N)` using `P` and `hsingle`, prove each evaluated stage computes the
  -- reduced `Ext` group by flatness of `B` and `M` over `A`, and then transport
  -- `CategoryTheory.ShortComplex.limit_idealPowerHomologyTower_iso_limit_leftHomologyQuotientTower`
  -- across those identifications.
  sorry

/-- Helper for Lemma 15.101.11: once the chosen finite free resolution supplies the strict
reduction-side tower data, the public existential statement is the canonical packaging step. -/
private theorem exists_extIdealPowerReductionTower_of_chosen_finite_free_resolution
    (I : Ideal A) (M N : ModuleCat B)
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ)
    {F : ChainComplex (ModuleCat B) ℕ}
    (π : F ⟶ (CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat B)) M))
    [ChainComplex.IsFiniteFreeResolution π] :
    ∃ T :
        SeqRingMod
          (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
          (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
            (Nat.le_succ (n + 1))),
      (∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
            (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
              (Nat.le_succ (n + 1))) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n)) ∧
        IsIsomorphic
          (limit (extIdealPowerQuotientTower I M N i))
          (limit (extIdealPowerReductionTowerOverA I T)) := by
  -- The chosen-resolution theorem already isolates the only genuinely hard comparison data.
  rcases
      chosen_finite_free_resolution_yields_reduction_tower_data
        (I := I) (M := M) (N := N) hBflat hMflat i π
    with ⟨T, hstage, hlimit⟩
  -- The public statement is exactly the reusable packaging theorem for those data.
  exact exists_extIdealPowerReductionTower_of_data (I := I) (M := M) (N := N) (i := i)
    T hstage hlimit

/-- Lemma 15.101.11: let `A → B` be a flat homomorphism of Noetherian rings, let `I ⊆ A` be an
ideal, and let `M, N` be `B`-modules with `M` finite over `B` and flat over `A`. Then for every
degree `i`, the inverse limit of the quotients
`Ext^i_B(M, N) / I^(n+1) Ext^i_B(M, N)` is canonically isomorphic to the inverse limit of some
strict compatible varying-ring module system `T` over the quotient-ring tower
`B / I^(n+1)B`, whose stagewise evaluations recover the reduced `Ext` stages
`Ext^i_{B / I^(n+1) B}(M / I^(n+1) M, N / I^(n+1) N)`. The inverse limit on the reduction side is
taken on the induced `A`-module tower `extIdealPowerReductionTowerOverA I T`. Lean starts the
quotient tower at `n = 0`, corresponding to the textbook quotient by `I^1`. -/
theorem exists_extIdealPowerReductionTower_limit_isomorphic_limit_extIdealPowerQuotientTower
    (I : Ideal A) (M N : ModuleCat B) [Module.Finite B M]
    (hBflat : (algebraMap A B).Flat)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (i : ℕ) :
    ∃ T :
        SeqRingMod
          (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
          (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I) (Nat.le_succ (n + 1))),
      (∀ n : ℕ,
        IsIsomorphic
          ((sequentialRingedModuleEvaluation
            (fun n ↦ stageRing B (Ideal.map (algebraMap A B) I) (Nat.succPNat n))
            (fun n ↦ Ideal.Quotient.factorPow (Ideal.map (algebraMap A B) I)
              (Nat.le_succ (n + 1))) n).obj T)
          (extIdealPowerReductionStageOverQuotient I M N i n)) ∧
        IsIsomorphic
          (limit (extIdealPowerQuotientTower I M N i))
          (limit (extIdealPowerReductionTowerOverA I T)) := by
  -- Route correction: the public theorem now follows the source proof literally by first fixing a
  -- single finite free resolution of the finite module `M`.
  rcases module_exists_finite_free_resolution (R := B) (M := M) with ⟨F, π, hπ⟩
  letI : ChainComplex.IsFiniteFreeResolution π := hπ
  -- All remaining comparison work is isolated in the chosen-resolution helper above.
  exact
    exists_extIdealPowerReductionTower_of_chosen_finite_free_resolution
      (I := I) (M := M) (N := N) hBflat hMflat i π

end
