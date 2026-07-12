import Mathlib
import StacksProject_2024.Chap18.ConstantIdealPowerQuotientSheaf
import StacksProject_2024.Chap18.Lemma_18_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite OrderDual

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
variable {Λ : Type v} [CommRing Λ]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{v} Λ)]

/-- The completed constant sheaf `\underline Λ^∧ = lim_n \underline{Λ / I^n}`. -/
abbrev constantIadicCompletionSheaf
    (I : Ideal Λ) :
    Sheaf J (ModuleCat.{v} Λ) :=
  limit (constantIdealPowerQuotientSheafSystem J I)


/-- The sections of the completed constant sheaf over `U`. -/
abbrev constantIadicCompletionSections
    (I : Ideal Λ) (U : C) :
    ModuleCat.{v} Λ :=
  (constantIadicCompletionSheaf J I).1.obj (op U)

/-- The sections of the constant quotient sheaf `\underline{Λ / I}` over `U`. -/
abbrev constantIdealQuotientSections
    (I : Ideal Λ) (U : C) :
    ModuleCat.{v} Λ :=
  (constantIdealQuotientSheaf J I).1.obj (op U)

/-- The sectionwise inverse system `n ↦ \underline{Λ / I^n}(U)`. -/
abbrev constantIdealPowerQuotientSectionSystem
    (I : Ideal Λ) (U : C) :
    ℕᵒᵖ ⥤ ModuleCat.{v} Λ :=
  constantIdealPowerQuotientSheafSystem J I ⋙
    sheafToPresheaf J (ModuleCat.{v} Λ) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{v} Λ)).obj (op U)

/-- The canonical map from the sections of the completed constant sheaf to the sections of
`\underline{Λ / I}`, induced by the projection to the first quotient in the inverse system. -/
abbrev constantIadicCompletionSectionsToConstantIdealQuotient
    (I : Ideal Λ) (U : C) :
    constantIadicCompletionSections J I U →ₗ[Λ] constantIdealQuotientSections J I U :=
  (((limit.π (constantIdealPowerQuotientSheafSystem J I) (op 1)).hom.app (op U)).hom)

/-- Helper for Lemma 18.42.4: evaluating the naturality square of
`constantCommuteCompose` identifies the underlying abelian-group map of a module-valued constant
sheaf section map with the corresponding forgotten section map. -/
private lemma constantModuleForgetSectionsNaturality
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    {A B : ModuleCat.{v} Λ} (u : A ⟶ B) (U : C)
    (x : (((constantSheaf J (ModuleCat.{v} Λ)).obj A).obj.obj (op U))) :
    let E := constantCommuteCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{max u v})
    let eA := ((sheafToPresheaf J AddCommGrpCat.{max u v}).mapIso (E.app A)).app (op U)
    let eB := ((sheafToPresheaf J AddCommGrpCat.{max u v}).mapIso (E.app B)).app (op U)
    eB.hom ((((constantSheaf J (ModuleCat.{v} Λ)).map u).hom.app (op U)) x) =
      (((constantSheaf J AddCommGrpCat.{max u v}).map
          ((forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{max u v}).map u)).hom.app (op U))
        (eA.hom x) := by
  -- TODO: recover the `AddCommGrpCat`-valued constant-sheaf comparison without importing the
  -- broken owner file `Lemma_18_42_2`; the intended proof is the naturality computation copied
  -- from that owner.
  sorry

/-- Helper for Lemma 18.42.4: a surjective module homomorphism induces a surjective map on
sections of the associated constant module sheaves. -/
private lemma constantModuleSheafAppSurjective
    {A B : ModuleCat.{v} Λ} (u : A ⟶ B)
    (hu : Function.Surjective u.hom) (U : C) :
    Function.Surjective (((constantSheaf J (ModuleCat.{v} Λ)).map u).hom.app (op U)) := by
  -- TODO: once the previous naturality bridge is restored, transport sectionwise surjectivity from
  -- `AddCommGrpCat` back to `ModuleCat` exactly as in the owner proof copied here.
  sorry

/-- Helper for Lemma 18.42.4: each quotient transition `Λ / I^(n + 1) → Λ / I^n` is surjective. -/
private lemma idealPowerQuotientTransition_surjective
    (I : Ideal Λ) (n : ℕ) :
    Function.Surjective (idealPowerQuotientTransition (Λ := Λ) I n).hom := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective Λ (I ^ n) z
  -- Proof comment: the same representative descends along the quotient factor map.
  refine ⟨Ideal.Quotient.mkₐ Λ (I ^ (n + 1)) x, ?_⟩
  simp [idealPowerQuotientTransition, Ideal.Quotient.factorₐ, Ideal.Quotient.factor,
    Ideal.Quotient.mkₐ_eq_mk]

/-- Helper for Lemma 18.42.4: every element of `I` acts by zero on sections of
`\underline{Λ / I}`. -/
private lemma idealSmulEqZero_constantIdealQuotientSections
    (I : Ideal Λ) (U : C) {a : Λ} (ha : a ∈ I) (y : constantIdealQuotientSections J I U) :
    a • y = 0 := by
  -- TODO: re-express `constantIdealQuotientSections J I U` through the quotient/tensor bridge from
  -- Lemma `18.42.2`; then `a ∈ I` kills the quotient factor immediately.
  sorry

-- Proof sketch: the target is a `Λ / I`-module, so multiplication by any element of `I` is zero;
-- hence the projection to the first quotient annihilates `I · \underline{Λ}^∧(U)`.
/-- The projection from completed sections to `\underline{Λ / I}(U)` kills the submodule generated
by `I`. -/
-- TODO: transport `constantIdealQuotientSections J I U` to the tensor model
-- `\underline{Λ}(U) ⊗[Λ] (Λ ⧸ I)` from Lemma `18.42.2`, where `I` kills the quotient factor.
-- In this workspace state that prerequisite API is not importable because the earlier chapter
-- `.olean` artifacts are absent, so the local bridge cannot be reused here yet.
theorem smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
    (I : Ideal Λ) (U : C) :
    I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)) ≤
      LinearMap.ker
        (constantIadicCompletionSectionsToConstantIdealQuotient J I U) := by
  -- Proof comment: after projecting to the first quotient stage, the target sections are
  -- annihilated by `I`, so every generator of `I • ⊤` lands in the kernel.
  refine Submodule.smul_le.mpr ?_
  intro a ha x hx
  change
    constantIadicCompletionSectionsToConstantIdealQuotient J I U (a • x) = 0
  rw [LinearMap.map_smul]
  simpa using
    idealSmulEqZero_constantIdealQuotientSections
      (J := J) I U ha
      (constantIadicCompletionSectionsToConstantIdealQuotient J I U x)

/-- Helper for Lemma 18.42.4: evaluating the limit sheaf at `U` identifies the completed sections
with the categorical inverse limit of the sectionwise quotient tower. -/
noncomputable def constantIadicCompletionSectionsIsoLimitSectionSystem
    (I : Ideal Λ) (U : C) :
    constantIadicCompletionSections J I U ≅
      limit (constantIdealPowerQuotientSectionSystem J I U) :=
  preservesLimitIso
    (sheafToPresheaf J (ModuleCat.{v} Λ) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{v} Λ)).obj (op U))
    (constantIdealPowerQuotientSheafSystem J I)

/-- Helper for Lemma 18.42.4: the sectionwise limit identification intertwines the `n`th limit
projection with the corresponding quotient-stage projection. -/
theorem constantIadicCompletionSectionsIsoLimitSectionSystem_hom_π
    (I : Ideal Λ) (U : C) (n : ℕᵒᵖ) :
    (constantIadicCompletionSectionsIsoLimitSectionSystem (J := J) I U).hom ≫
        limit.π (constantIdealPowerQuotientSectionSystem J I U) n =
      (((limit.π (constantIdealPowerQuotientSheafSystem J I) n).hom.app (op U))) := by
  -- Proof comment: this is exactly the canonical projection formula for `preservesLimitIso`.
  simpa [constantIadicCompletionSectionsIsoLimitSectionSystem] using
    (preservesLimitIso_hom_π
      (sheafToPresheaf J (ModuleCat.{v} Λ) ⋙
        (evaluation Cᵒᵖ (ModuleCat.{v} Λ)).obj (op U))
      (constantIdealPowerQuotientSheafSystem J I) n)

/-- Helper for Lemma 18.42.4: the transition maps on the sectionwise quotient tower are
surjective. -/
theorem constantIdealPowerQuotientSectionSystem_transition_surjective
    (I : Ideal Λ) (U : C) (n : ℕ) :
    Function.Surjective
      ((((constantIdealPowerQuotientSectionSystem J I U).map (homOfLE (Nat.le_succ n)).op).hom)) := by
  -- TODO: after restoring `constantModuleSheafAppSurjective`, unfold the successor map of the
  -- section tower and apply that bridge to `idealPowerQuotientTransition_surjective`.
  sorry

/-- Helper for Lemma 18.42.4: the positive indexing category `OrderDual ℕ+` maps to the original
`ℕᵒᵖ` quotient tower by forgetting that the indices start at `1`. -/
private abbrev positiveToOpNat : OrderDual ℕ+ ⥤ ℕᵒᵖ where
  obj n := op (((OrderDual.ofDual n : ℕ+) : ℕ))
  map {i j} f :=
    (homOfLE
      (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))).op
  map_id _ := by
    -- Proof comment: the index category `ℕᵒᵖ` is thin, so identity arrows are unique.
    apply Subsingleton.elim
  map_comp _ _ := by
    -- Proof comment: composition in a thin category is determined uniquely by the underlying
    -- inequality, so the reindexing functor preserves it automatically.
    apply Subsingleton.elim

/-- Helper for Lemma 18.42.4: the positive quotient tower is the tail of the original
sectionwise quotient system, reindexed by `OrderDual ℕ+`. -/
abbrev constantIdealPowerQuotientPositiveSectionSystem
    (I : Ideal Λ) (U : C) :
    OrderDual ℕ+ ⥤ ModuleCat.{v} Λ :=
  positiveToOpNat ⋙ constantIdealPowerQuotientSectionSystem J I U

/-- Helper for Lemma 18.42.4: evaluating constant module sheaves preserves zero objects. -/
private theorem constantModuleSectionsIsZeroOfIsZero
    {M : ModuleCat.{v} Λ} (hM : IsZero M) (U : C) :
    IsZero ((((constantSheaf J (ModuleCat.{v} Λ)).obj M).1.obj (op U))) := by
  -- TODO: package the composite functor "constant sheaf, then evaluate at `U`" in a universe-stable
  -- auxiliary declaration and apply `Functor.map_isZero` there.
  sorry

/-- Helper for Lemma 18.42.4: the zero-th stage of the original quotient-section tower is the
zero module because `Λ / I^0 = Λ / Λ = 0`. -/
theorem constantIdealPowerQuotientSectionSystem_zero_isZero
    (I : Ideal Λ) (U : C) :
    IsZero ((constantIdealPowerQuotientSectionSystem J I U).obj (op 0)) := by
  have hStage :
      IsZero (idealPowerQuotientSequence (Λ := Λ) I 0) := by
    -- Proof comment: `I ^ 0 = ⊤`, so the quotient ring is subsingleton and hence zero in
    -- `ModuleCat`.
    simpa [idealPowerQuotientSequence, pow_zero] using
      (ModuleCat.isZero_of_subsingleton
        (ModuleCat.of Λ (Λ ⧸ (⊤ : Ideal Λ))))
  -- Proof comment: the section object at stage `0` is evaluation of the constant sheaf on that
  -- zero module.
  simpa [constantIdealPowerQuotientSectionSystem, constantIdealPowerQuotientSheafSystem,
    idealPowerQuotientSystem] using
    constantModuleSectionsIsZeroOfIsZero (J := J)
      (M := idealPowerQuotientSequence (Λ := Λ) I 0) hStage U

/-- Helper for Lemma 18.42.4: the step maps in the positive quotient tower are exactly the
surjective successor maps from the original sectionwise quotient system. -/
theorem constantIdealPowerQuotientPositiveSectionSystem_step_surjective
    (I : Ideal Λ) (U : C) (n : ℕ+) :
    Function.Surjective
      (((constantIdealPowerQuotientPositiveSectionSystem (J := J) I U).map
        (homOfLE (show n ≤ n + 1 by
          exact_mod_cast Nat.le_succ (n : ℕ)))).hom) := by
  -- TODO: once the previous transition-surjectivity theorem is restored, unfold the reindexing
  -- functor and identify this map with the corresponding successor map in the original tower.
  sorry

/-- The canonical map from the quotient of completed sections modulo `I` to
`\underline{Λ / I}(U)`. -/
abbrev constantIadicCompletionSectionsModIComparison
    (I : Ideal Λ) (U : C) :
    ((constantIadicCompletionSections J I U) ⧸
      (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U)))) →ₗ[Λ]
      constantIdealQuotientSections J I U :=
  (I • (⊤ : Submodule Λ (constantIadicCompletionSections J I U))).liftQ
    (constantIadicCompletionSectionsToConstantIdealQuotient J I U)
    (smul_top_le_constantIadicCompletionSectionsToConstantIdealQuotient_ker
      J I U)

-- Proof sketch: evaluate the inverse-limit sheaf at `U`, identify the result with the limit of the
-- system `Λ / I^n` of flat `Λ / I^n`-modules with surjective transition maps, and then apply the
-- flatness criterion for inverse limits over a Noetherian base.
/-- Lemma 18.42.4 (1): for a Noetherian ring `Λ`, the sections of the completed constant sheaf
`\underline Λ^∧ = lim_n \underline{Λ / I^n}` are flat over `Λ`. -/
-- TODO: reindex the quotient-section tower by `ℕ+`, identify
-- `constantIadicCompletionSections J I U` with that positive-indexed inverse limit, prove the
-- stage maps are surjective, and then invoke Lemma `15.27.4 (2)`. That imported prerequisite is
-- currently unavailable here because the earlier chapter `.olean` file is missing.
theorem constantIadicCompletionSheaf_app_flat
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Module.Flat Λ (constantIadicCompletionSections J I U) := by
  -- Route correction: the first bridge is now explicit in
  -- `constantIadicCompletionSectionsIsoLimitSectionSystem`, so the remaining work is to reindex
  -- this sectionwise tower by positive integers and import the stage flatness/surjectivity inputs.
  sorry

-- Proof sketch: compare the inverse system `Λ / I^n` with its reduction modulo `I`, use exactness
-- of inverse limits with surjective transition maps, and identify the resulting quotient with the
-- constant sheaf on `Λ / I`.
/-- Lemma 18.42.4 (2): the quotient of the completed constant sheaf by `I` identifies with the
constant sheaf `\underline{Λ / I}` on sections. -/
-- TODO: after the positive-tower limit model and stage tensor identifications are available,
-- apply Lemma `15.27.4 (1)` with `Q = Λ ⧸ I` and transport the resulting comparison map to
-- `constantIadicCompletionSectionsModIComparison J I U`. This uses the same currently missing
-- earlier chapter `.olean` prerequisites.
theorem constantIadicCompletionSectionsModIComparison_bijective
    [IsNoetherianRing Λ] (I : Ideal Λ) (U : C) :
    Function.Bijective (constantIadicCompletionSectionsModIComparison J I U) := by
  -- Route correction: once the positive-tower model is in place, the same sectionwise limit
  -- comparison should identify the Chapter `15.27.4 (1)` map with this quotient comparison.
  sorry

end CategoryTheory
