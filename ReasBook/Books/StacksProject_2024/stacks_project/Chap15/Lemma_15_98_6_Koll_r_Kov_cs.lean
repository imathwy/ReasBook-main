import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap15.Lemma_15_87_14_Emmanouil
import StacksProject_2024.Chap15.Lemma_15_88_1_Base
import StacksProject_2024.Chap15.Lemma_15_88_5_TowerBridge
import StacksProject_2024.Chap15.Lemma_15_95_4
import StacksProject_2024.Chap15.Proposition_15_95_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the sequential inverse system of quotient rings
`A / I^(n+1)` used by the source proof. -/
private abbrev idealPowerQuotientRingSystem (I : Ideal A) : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  sequentialRingSystem (fun n ↦ A ⧸ I ^ (n + 1))
    (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): a compatible tower of derived objects over the
quotient rings `A / I^(n+1)`. -/
private abbrev IdealPowerQuotientDerivedTower (I : Ideal A) :=
  DerivedModuleTower
    (stageRing (idealPowerQuotientRingSystem I))
    (stageTransitionRingHom (idealPowerQuotientRingSystem I))

/- Domain-style sampling for Lemma 15.98.6:
- primary domain: Milnor short exact sequences for derived inverse limits, specialized to the
  ideal-power quotient-tensor tower computing derived completion;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `DerivedCategory.homologyCompletionComparison`,
  `DerivedCategory.homologyCompletionComparison_isIso`,
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`;
- best owner abstraction: this numbered item is `source-facing`, but its primitive comparison data
  are still owned by the canonical Milnor short exact sequence and the derived-completion
  comparison morphism. Any chosen `ι` and `π` from the Milnor sequence are only `bridge/view`
  witnesses and should not remain in the public theorem surface;
- primitive vs. derived:
  primitive data are the ideal `I`, the derived object `K`, the degree `i`, the finite cohomology
  hypothesis, and the Mittag-Leffler hypothesis on the previous-degree tower;
  derived API is the resulting canonical object-level isomorphism between
  `(H^i(K))^∧` and `lim H^i(K_n)`, while the chosen Milnor comparison
  `H^i(K^∧) ⟶ lim H^i(K_n)` remains internal bridge data. -/

/-- The quotient module `M / I^(n + 1) M`. -/
abbrev idealPowerModuleQuotient (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : Type v :=
  M ⧸ (I ^ (n + 1) • (⊤ : Submodule A M))

/-- The `n`th quotient stage `M / I^(n + 1) M` in the ideal-power inverse system of an
`A`-module. -/
abbrev idealPowerQuotientStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    ModuleCat A :=
  ModuleCat.of A (idealPowerModuleQuotient I M n)

/-- The transition morphism `M / I^(n + 2) M ⟶ M / I^(n + 1) M` in the ideal-power quotient
inverse system. -/
abbrev idealPowerQuotientStep (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientStage I M (n + 1) ⟶
      idealPowerQuotientStage I M n :=
  ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1)))

/-- The sequential inverse system `(M / I^(n + 1) M)_n` attached to an `A`-module `M`. -/
abbrev idealPowerQuotientInverseSystem (I : Ideal A) (M : ModuleCat A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (idealPowerQuotientStep I M)

/-- The inverse system
`(H^i((A / I^(n+1))[0] ⊗_A^{\mathbf L} K))_n`, which is canonically identified with the textbook
tower `(H^i(K ⊗_A^{\mathbf L} A / I^(n+1)))_n` over a commutative base ring. -/
abbrev idealPowerQuotientTensorHomologyInverseSystem
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  (idealPowerQuotientTensorDerivedInverseSystem I K) ⋙ H i

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): a derived-limit witness transports across an
isomorphism of limiting objects while the ideal-power quotient tensor tower is kept fixed. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DMod} {K L : DMod}
    (e : K ≅ L)
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit Ksys L := by
  rcases hK with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let T : Triangle DMod :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let T' : Triangle DMod :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom)
  have hIso : T ≅ T' := by
    -- Proof comment: only the first vertex changes, so the comparison triangle is induced by the
    -- chosen isomorphism of limiting objects.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [T, T']
    · simp [T, T']
    · simp [T, T']
  have hT' : T' ∈ distTriang DMod := by
    -- Proof comment: distinguished triangles are stable under isomorphism, so the transported
    -- Milnor triangle remains distinguished.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DMod (1 : ℤ)).map e.hom, hT'⟩⟩

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): once a functor to derived-complete objects is known
to be left adjoint to the inclusion, its value at `K` is canonically the same as the chosen
derived completion `K^∧`. -/
private noncomputable def leftAdjointValueIso_derivedCompletion
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (adj : L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (K : DMod) :
    (L.obj K).obj ≅ K^∧[I, I.fg_of_isNoetherianRing] := by
  let inclusion : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory ⥤ DMod :=
    (DerivedCategory.derivedCompleteObjectProperty I).ι
  let canonicalLeftAdjoint :
      DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory :=
    @Functor.leftAdjoint _ _ _ _ inclusion
      (DerivedCategory.derivedCompleteInclusion_isRightAdjoint_of_fg
        I I.fg_of_isNoetherianRing)
  let canonicalAdj :
      canonicalLeftAdjoint ⊣ inclusion :=
    @Adjunction.ofIsRightAdjoint _ _ _ _ inclusion
      (DerivedCategory.derivedCompleteInclusion_isRightAdjoint_of_fg
        I I.fg_of_isNoetherianRing)
  let eSub : L.obj K ≅ canonicalLeftAdjoint.obj K :=
    (adj.leftAdjointUniq canonicalAdj).app K
  -- Proof comment: both functors are left adjoint to the same inclusion, so left-adjoint
  -- uniqueness gives an isomorphism in the derived-complete subcategory; forgetting that
  -- isomorphism identifies the underlying objects in `D(A)`.
  simpa [DerivedCategory.derivedCompletion, DerivedCategory.derivedCompletionOf,
    inclusion, canonicalLeftAdjoint] using
    ((DerivedCategory.derivedCompleteObjectProperty I).ι.mapIso eSub)

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): after the explicit quotient-completion model is
shown to be left adjoint to the derived-complete inclusion, any derived-limit witness on its value
at `K` transports directly to the canonical completion object `K^∧`. -/
private theorem isDerivedLimit_derivedCompletion_of_leftAdjoint
    (I : Ideal A)
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (adj : L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (K : DMod)
    (hL :
      IsDerivedLimit
        (idealPowerQuotientTensorDerivedInverseSystem I K)
        (L.obj K).obj) :
    IsDerivedLimit
      (idealPowerQuotientTensorDerivedInverseSystem I K)
      (K^∧[I, I.fg_of_isNoetherianRing]) := by
  -- Proof comment: the comparison to the canonical completion object is now purely formal,
  -- independent of the explicit quotient-tower model used to produce `hL`.
  exact
    isDerivedLimit_of_object_iso
      (leftAdjointValueIso_derivedCompletion I L adj K)
      hL

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the quotient-stage algebra maps
`A → A / I^(n+2) → A / I^(n+1)` compose to the direct quotient map `A → A / I^(n+1)`. -/
private theorem idealPowerQuotient_stage_algebraMap_comp
    (I : Ideal A) (n : ℕ) :
    algebraMap A (stageRing (idealPowerQuotientRingSystem I) n) =
      (stageTransitionRingHom (idealPowerQuotientRingSystem I) n).comp
        (algebraMap A (stageRing (idealPowerQuotientRingSystem I) (n + 1))) := by
  ext x
  change (algebraMap A (A ⧸ I ^ (n + 1))) x =
      ((stageTransitionRingHom (idealPowerQuotientRingSystem I) n).comp
        (algebraMap A (A ⧸ I ^ (n + 2)))) x
  have htransition :
      stageTransitionRingHom (idealPowerQuotientRingSystem I) n =
        Ideal.Quotient.factorPowSucc I (n + 1) := by
    simp [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom]
  rw [htransition]
  rfl

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the source-faithful tower has stage
`K ⊗_A^L A / I^(n+1)` and uses the canonical iterated-vs-direct quotient-base-change morphism
between consecutive stages. -/
private noncomputable abbrev quotient_tensor_derived_tower
    (I : Ideal A) (K : DMod) :
    IdealPowerQuotientDerivedTower I where
  obj n :=
    (derivedTensorWithAlgebra
      (algebraMap A (stageRing (idealPowerQuotientRingSystem I) n))).obj K
  stepMap n :=
    (derivedTensorWithAlgebraAdjunction
        (R := stageRing (idealPowerQuotientRingSystem I) (n + 1))
        (A := stageRing (idealPowerQuotientRingSystem I) n)).homEquiv
      (((derivedTensorWithAlgebraCompIso
          (algebraMap A (stageRing (idealPowerQuotientRingSystem I) (n + 1)))
          (stageTransitionRingHom (idealPowerQuotientRingSystem I) n)
          (algebraMap A (stageRing (idealPowerQuotientRingSystem I) n))
          (idealPowerQuotient_stage_algebraMap_comp I n)).app K).hom)

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the quotient-tensor tower satisfies the expected
stagewise derived base-change isomorphisms
`(K ⊗_A^L A / I^(n+2)) ⊗_{A / I^(n+2)}^L A / I^(n+1) ≅ K ⊗_A^L A / I^(n+1)`. -/
private theorem quotient_tensor_derived_tower_stageBaseChange_isIso
    (I : Ideal A) (K : DMod) (n : ℕ) :
    IsIso (stageDerivedBaseChangeComparison (quotient_tensor_derived_tower I K) n) := by
  -- Proof comment: by construction, the tower step is the adjoint transpose of the canonical
  -- iterated-vs-direct derived scalar-extension isomorphism, so the base-change comparison
  -- recovers that isomorphism verbatim.
  change
    IsIso
      (((derivedTensorWithAlgebraAdjunction
            (R := stageRing (idealPowerQuotientRingSystem I) (n + 1))
            (A := stageRing (idealPowerQuotientRingSystem I) n)).homEquiv
          ((derivedTensorWithAlgebra
              (algebraMap A (stageRing (idealPowerQuotientRingSystem I) (n + 1)))).obj K)
          ((derivedTensorWithAlgebra
              (algebraMap A (stageRing (idealPowerQuotientRingSystem I) n)).obj K))).symm
        (((derivedTensorWithAlgebraAdjunction
              (R := stageRing (idealPowerQuotientRingSystem I) (n + 1))
              (A := stageRing (idealPowerQuotientRingSystem I) n)).homEquiv
            ((derivedTensorWithAlgebra
                (algebraMap A (stageRing (idealPowerQuotientRingSystem I) (n + 1)))).obj K)
            ((derivedTensorWithAlgebra
                (algebraMap A (stageRing (idealPowerQuotientRingSystem I) n)).obj K)))
          (((derivedTensorWithAlgebraCompIso
              (algebraMap A (stageRing (idealPowerQuotientRingSystem I) (n + 1)))
              (stageTransitionRingHom (idealPowerQuotientRingSystem I) n)
              (algebraMap A (stageRing (idealPowerQuotientRingSystem I) n))
              (idealPowerQuotient_stage_algebraMap_comp I n)).app K).hom))) := by
    dsimp [stageDerivedBaseChangeComparison, quotient_tensor_derived_tower]
  rw [Equiv.apply_symm_apply]
  infer_instance

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the canonical derived completion object `K^∧`
should only be used through the weaker fact that it is a derived limit of the quotient-tensor
tower. This is the exact input needed for the Milnor short exact sequence route in this file. -/
private theorem toDerivedCompletion_isComparison_idealPowerQuotientTensor
    (I : Ideal A) (K : DMod) :
    IsDerivedCompletionIdealPowerQuotientTensorComparison
      I
      K
      (K^∧[I, I.fg_of_isNoetherianRing])
      (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K) := by
  -- Route correction: the real missing source-facing bridge is not another abstract
  -- `IsDerivedLimit` transport, but the concrete comparison predicate asserting that
  -- `toDerivedCompletion` presents `K^∧` as the canonical quotient-tower derived limit.
  --
  -- TODO: construct the Milnor presentation for `toDerivedCompletion` from the quotient-tensor
  -- tower and verify that its stage projections agree with `idealPowerQuotientTensorToStage`.
  -- The current upstream `Remark_15_92_11` only exposes `K^∧` as a placeholder reflector object,
  -- so this source-facing comparison lemma must be provided before the derived-limit witness can
  -- be discharged in a source-faithful way.
  sorry

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): the canonical derived completion object `K^∧`
should only be used through the weaker fact that it is a derived limit of the quotient-tensor
tower. This is the exact input needed for the Milnor short exact sequence route in this file. -/
private theorem toDerivedCompletion_isDerivedLimit_idealPowerQuotientTensor
    (I : Ideal A) (K : DMod) :
    IsDerivedLimit
      (idealPowerQuotientTensorDerivedInverseSystem I K)
      (K^∧[I, I.fg_of_isNoetherianRing]) := by
  -- Proof comment: once the source-facing quotient-tower comparison for `toDerivedCompletion`
  -- is available, the derived-limit witness is exactly the owner theorem attached to that
  -- comparison predicate.
  exact
    (toDerivedCompletion_isComparison_idealPowerQuotientTensor I K).isDerivedLimit

private theorem exists_homologyDerivedCompletionToLimit
    (I : Ideal A) (K : DMod) (i : ℤ) :
    ∃ (π :
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
      (ι :
        firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
          (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  have hlimit :
      IsDerivedLimit
        (idealPowerQuotientTensorDerivedInverseSystem I K)
        (K^∧[I, I.fg_of_isNoetherianRing]) :=
    toDerivedCompletion_isDerivedLimit_idealPowerQuotientTensor I K
  rcases CategoryTheory.derivedLimit_cohomology_shortExact
      (idealPowerQuotientTensorDerivedInverseSystem I K)
      (K^∧[I, I.fg_of_isNoetherianRing]) hlimit i with
    ⟨ι, π, h, hshort⟩
  refine ⟨π, ι, h, ?_⟩
  -- Proof comment: the short exact sequence now depends only on the derived-limit witness, so no
  -- explicit comparison morphism survives in the local statement.
  simpa [idealPowerQuotientTensorHomologyInverseSystem, sub_eq_add_neg] using hshort

/-- Helper for Lemma 15.98.6 (Kollár-Kovács): a Mittag-Leffler hypothesis on the previous-degree
homology tower kills the Milnor `R^1 lim` obstruction term. -/
private theorem firstDerivedLimit_isZero_of_tensorHomology_isMittagLeffler
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hML :
      (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsZero (firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1))) := by
  -- Proof comment: use the canonical `R^1 lim`-vanishing owner for Mittag-Leffler towers.
  exact
    firstDerivedLimit_isZero_of_isMittagLeffler
      (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1))
      hML

/-- If `π : H^i(K^∧) ⟶ \varprojlim_n H^i(K_n)` appears in the Milnor short exact sequence for the
quotient-tensor tower and the previous-degree tower is Mittag-Leffler, then composing `π` with the
canonical comparison `(H^i(K))^∧ → H^i(K^∧)` from Lemma `15.95.4` yields an isomorphism. -/
private theorem homologyCompletionComparison_comp_isIso_of_shortExact
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (ι :
      firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
    (π :
      (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
    (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π) := by
  have hzero :
      IsZero (firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1))) := by
    -- Proof comment: the previous-degree tower is Mittag-Leffler, so the Milnor obstruction
    -- vanishes before we read off exactness of the short complex.
    exact firstDerivedLimit_isZero_of_tensorHomology_isMittagLeffler I K i hML_prev
  haveI : IsIso π := (ShortComplex.ShortExact.isIso_g_iff hshort).2 hzero
  haveI : IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite) :=
    DerivedCategory.homologyCompletionComparison_isIso I K i hKfinite
  infer_instance

-- Proof sketch: Proposition `15.95.2` identifies derived completion with the derived inverse
-- limit of the ideal-power tensor tower. Lemma `15.95.4` identifies `H^i` of that derived
-- completion with the `I`-adic completion of `H^i(K)`, i.e. the inverse limit of the quotients
-- `H^i(K) / I^(n+1) H^i(K)`. Lemma `15.88.4` gives the Milnor short exact sequence for the right
-- derived inverse limit, whose left term is `R^1 lim H^{i-1}(K_n)`, and the Mittag-Leffler
-- hypothesis in degree `i - 1` kills that obstruction via Lemma `15.88.1`.
/-- Lemma 15.98.6 (Kollár-Kovács): let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)`,
and set `K_n = K ⊗_A^{\mathbf L} A / I^(n+1)`. If every `H^j(K)` is a finite `A`-module and the
inverse system `(H^{i - 1}(K_n))_n` satisfies the Mittag-Leffler condition, then there exists a
Milnor comparison from `(H^i(K))^∧` to `\varprojlim_n H^i(K_n)`, obtained by composing the
canonical map `(H^i(K))^∧ → H^i(K^∧)` with a Milnor comparison
`H^i(K^∧) → \varprojlim_n H^i(K_n)`. Since that Milnor comparison is chosen only through the
owner theorem `derivedLimit_cohomology_shortExact`, the public surface is the resulting canonical
object-level isomorphism between the completion of `H^i(K)` and the limit of the tower
`(H^i(K_n))_n`. The Lean indexing starts at `n = 0`, corresponding to the textbook power `I^1`. -/
theorem homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIsomorphic
      (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
      (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  rcases exists_homologyDerivedCompletionToLimit I K i with ⟨π, ι, h, hshort⟩
  let φ :
      ModuleCat.of A (AdicCompletion I ((H i).obj K)) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i) :=
    DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π
  have hφ : IsIso φ := by
    simpa [φ] using
      homologyCompletionComparison_comp_isIso_of_shortExact
        I K i hKfinite ι π h hshort hML_prev
  let _ := hφ
  exact ⟨asIso φ⟩

end
