import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import stacks_proof.stacks_project.Chap18.Lemma_18_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite OrderDual

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
variable {Λ : Type v} [CommRing Λ]
variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{v} Λ)]

/-- The `n`th quotient `Λ / I^n`, viewed as an object of `ModuleCat Λ`. -/
abbrev idealPowerQuotientSequence (I : Ideal Λ) (n : ℕ) : ModuleCat.{v} Λ :=
  ModuleCat.of Λ (Λ ⧸ I ^ n)

/-- The transition map `Λ / I^(n + 1) → Λ / I^n` in the `I`-adic quotient tower. -/
abbrev idealPowerQuotientTransition (I : Ideal Λ) (n : ℕ) :
    idealPowerQuotientSequence I (n + 1) ⟶ idealPowerQuotientSequence I n :=
  ModuleCat.ofHom
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).toLinearMap

/-- The inverse system `n ↦ Λ / I^n` in `ModuleCat Λ`. -/
abbrev idealPowerQuotientSystem (I : Ideal Λ) : ℕᵒᵖ ⥤ ModuleCat.{v} Λ :=
  Functor.ofOpSequence (idealPowerQuotientTransition I)

/-- The inverse system of constant sheaves with values `Λ / I^n`. -/
abbrev constantIdealPowerQuotientSheafSystem
    (I : Ideal Λ) :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{v} Λ) :=
  idealPowerQuotientSystem I ⋙ constantSheaf J (ModuleCat.{v} Λ)

/-- The completed constant sheaf `\underline Λ^∧ = lim_n \underline{Λ / I^n}`. -/
abbrev constantIadicCompletionSheaf
    (I : Ideal Λ) :
    Sheaf J (ModuleCat.{v} Λ) :=
  limit (constantIdealPowerQuotientSheafSystem J I)

/-- The constant sheaf with value `Λ / I`. -/
abbrev constantIdealQuotientSheaf
    (I : Ideal Λ) :
    Sheaf J (ModuleCat.{v} Λ) :=
  (constantIdealPowerQuotientSheafSystem J I).obj (op 1)

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
    {A B : ModuleCat.{v} Λ} (u : A ⟶ B) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})]
    [J.HasSheafCompose (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})]
    (x : (((constantSheaf J (ModuleCat.{v} Λ)).obj A).obj.obj (op U))) :
    let E := constantCommuteCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})
    let eA := ((sheafToPresheaf J AddCommGrpCat.{v}).mapIso (E.app A)).app (op U)
    let eB := ((sheafToPresheaf J AddCommGrpCat.{v}).mapIso (E.app B)).app (op U)
    eB.hom ((((constantSheaf J (ModuleCat.{v} Λ)).map u).hom.app (op U)) x) =
      (((constantSheaf J AddCommGrpCat.{v}).map
          ((forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}).map u)).hom.app (op U))
        (eA.hom x) := by
  let E := constantCommuteCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})
  let eA := ((sheafToPresheaf J AddCommGrpCat.{v}).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J AddCommGrpCat.{v}).mapIso (E.app B)).app (op U)
  -- Proof comment: evaluate the naturality square of `constantCommuteCompose` on the section
  -- over `U` and then read the result in `AddCommGrpCat`.
  have hnat :
      ((((constantSheaf J (ModuleCat.{v} Λ) ⋙
          sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})).map u) ≫
          (E.hom.app B)).hom.app (op U)) =
        (((E.hom.app A) ≫
          (constantSheaf J AddCommGrpCat.{v}).map
            ((forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}).map u)).hom.app (op U)) := by
    exact
      congrArg
        (fun α :
          ((constantSheaf J (ModuleCat.{v} Λ) ⋙
              sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})).obj A) ⟶
            ((forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v} ⋙
                constantSheaf J AddCommGrpCat.{v}).obj B) =>
          α.hom.app (op U))
        (E.hom.naturality u)
  simpa [E, eA, eB] using ConcreteCategory.congr_hom hnat x

/-- Helper for Lemma 18.42.4: a surjective module homomorphism induces a surjective map on
sections of the associated constant module sheaves. -/
private lemma constantModuleSheafAppSurjective
    {A B : ModuleCat.{v} Λ} (u : A ⟶ B)
    (hu : Function.Surjective u.hom) (U : C) :
    Function.Surjective (((constantSheaf J (ModuleCat.{v} Λ)).map u).hom.app (op U)) := by
  -- TODO: reuse the sibling `constant_module_sheaf_app_surjective` proof shape once the local
  -- `AddCommGrpCat.{v}` sheafification/composition owner spelling is stabilized in this file.
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
  -- TODO: prove this by expressing the stage-`1` section object as the evaluation of the
  -- constant sheaf on `Λ ⧸ I` and then transporting the zero action of `I` through that quotient
  -- module structure.
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
  -- TODO: package the evaluation-of-limit isomorphism with a universe-stable owner spelling
  -- before replaying `preservesLimitIso` in this file.
  sorry

/-- Helper for Lemma 18.42.4: the sectionwise limit identification intertwines the `n`th limit
projection with the corresponding quotient-stage projection. -/
theorem constantIadicCompletionSectionsIsoLimitSectionSystem_hom_π
    (I : Ideal Λ) (U : C) (n : ℕᵒᵖ) :
    (constantIadicCompletionSectionsIsoLimitSectionSystem (J := J) I U).hom ≫
        limit.π (constantIdealPowerQuotientSectionSystem J I U) n =
      (((limit.π (constantIdealPowerQuotientSheafSystem J I) n).hom.app (op U))) := by
  -- TODO: once the universe-stable owner spelling for
  -- `constantIadicCompletionSectionsIsoLimitSectionSystem` is restored, this is the companion
  -- `preservesLimitIso_hom_π` projection formula.
  sorry

/-- Helper for Lemma 18.42.4: the transition maps on the sectionwise quotient tower are
surjective. -/
theorem constantIdealPowerQuotientSectionSystem_transition_surjective
    (I : Ideal Λ) (U : C) (n : ℕ) :
    Function.Surjective
      ((((constantIdealPowerQuotientSectionSystem J I U).map (homOfLE (Nat.le_succ n)).op).hom)) := by
  -- Proof comment: the section-tower transition is evaluation of the constant-sheaf image of the
  -- quotient-step map `Λ / I^(n + 1) → Λ / I^n`.
  simpa [constantIdealPowerQuotientSectionSystem, constantIdealPowerQuotientSheafSystem,
    idealPowerQuotientSystem, idealPowerQuotientTransition] using
    constantModuleSheafAppSurjective (J := J)
      (u := idealPowerQuotientTransition (Λ := Λ) I n)
      (idealPowerQuotientTransition_surjective (Λ := Λ) I n) U

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
  -- TODO: once the composite functor is given a universe-stable owner spelling, apply
  -- `Functor.map_isZero` to that explicit composite.
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
  -- TODO: identify the positive-tail successor map with the corresponding original successor map
  -- through `positiveToOpNat`; the current blocker is a non-definitional mismatch in the reindexed
  -- `Functor.map` spelling.
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
