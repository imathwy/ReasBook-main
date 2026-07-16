import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_86_3
import stacks_proof.stacks_project.Chap10.Lemma_10_87_1
import stacks_proof.stacks_project.Chap10.Lemma_10_98_1
import stacks_proof.stacks_project.Chap10.Lemma_10_98_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat A)

/-!
The remaining short-exactness bridge has to be replayed at the low universe of the local
`limit_projection_moduleInvLim` functor.  The imported Lemma `10.87.1` uses a higher-universe
abelian-group target, so the helpers below rebuild the same forget-limit-reflect argument with
`AddCommGrpCat` itself.
-/

/-- Helper for Chap10 Lemma 10 98 2: the low-universe forgetful functor from `A`-modules to
abelian groups. -/
private abbrev limit_projection_smallForgetToAbelianGroup :
    ModuleCat A ⥤ AddCommGrpCat :=
  forget₂ (ModuleCat A) AddCommGrpCat

/-- Helper for Chap10 Lemma 10 98 2: the low-universe category of abelian-group inverse systems
over `ℕ+`. -/
private abbrev limit_projection_smallAbelianGroupInverseSystem : Type 1 :=
  OrderDual ℕ+ ⥤ AddCommGrpCat

/-- Helper for Chap10 Lemma 10 98 2: the inverse-limit functor on low-universe abelian-group
inverse systems. -/
private abbrev limit_projection_smallAbelianInvLim :
    limit_projection_smallAbelianGroupInverseSystem ⥤ AddCommGrpCat :=
  lim

/-- Helper for Chap10 Lemma 10 98 2: forgetting modules stagewise gives a functor from module
inverse systems to low-universe abelian-group inverse systems. -/
private abbrev limit_projection_smallForgetInverseSystemFunctor :
    ModuleInverseSystem ⥤ limit_projection_smallAbelianGroupInverseSystem :=
  (Functor.whiskeringRight (OrderDual ℕ+) (ModuleCat A) AddCommGrpCat).obj
    limit_projection_smallForgetToAbelianGroup

/-- Helper for Chap10 Lemma 10 98 2: the low-universe limit-forget comparison is natural in a
morphism of module inverse systems. -/
private theorem limit_projection_small_preservesLimitIso_hom_limMap_forget
    {X Y : ModuleInverseSystem} (α : X ⟶ Y) :
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup X).hom ≫
        limMap (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup) =
      limit_projection_smallForgetToAbelianGroup.map (limMap α) ≫
        (preservesLimitIso limit_projection_smallForgetToAbelianGroup Y).hom := by
  -- Compare the two morphisms out of the limit after every stage projection.
  apply limit.hom_ext
  intro i
  have hmid :
      (preservesLimitIso limit_projection_smallForgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup) ≫
            limit.π (Y ⋙ limit_projection_smallForgetToAbelianGroup) i =
        limit_projection_smallForgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
    calc
      (preservesLimitIso limit_projection_smallForgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup) ≫
            limit.π (Y ⋙ limit_projection_smallForgetToAbelianGroup) i
        = (preservesLimitIso limit_projection_smallForgetToAbelianGroup X).hom ≫
            limit.π (X ⋙ limit_projection_smallForgetToAbelianGroup) i ≫
              (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup).app i := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦
                      (preservesLimitIso limit_projection_smallForgetToAbelianGroup X).hom ≫ t)
                    (limMap_π
                      (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup) i)
      _ = limit_projection_smallForgetToAbelianGroup.map (limit.π X i) ≫
            (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup).app i := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦
                    t ≫ (Functor.whiskerRight α limit_projection_smallForgetToAbelianGroup).app i)
                  (preservesLimitIso_hom_π
                    (G := limit_projection_smallForgetToAbelianGroup) (F := X) i)
      _ = limit_projection_smallForgetToAbelianGroup.map (limit.π X i) ≫
            limit_projection_smallForgetToAbelianGroup.map (α.app i) := by
              rfl
      _ = limit_projection_smallForgetToAbelianGroup.map (limit.π X i ≫ α.app i) := by
              rw [← limit_projection_smallForgetToAbelianGroup.map_comp]
      _ = limit_projection_smallForgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
              rw [limMap_π]
  have hfinal :
      limit_projection_smallForgetToAbelianGroup.map (limMap α ≫ limit.π Y i) =
        (limit_projection_smallForgetToAbelianGroup.map (limMap α) ≫
            (preservesLimitIso limit_projection_smallForgetToAbelianGroup Y).hom) ≫
          limit.π (Y ⋙ limit_projection_smallForgetToAbelianGroup) i := by
    rw [limit_projection_smallForgetToAbelianGroup.map_comp]
    have hπY :
        limit_projection_smallForgetToAbelianGroup.map (limit.π Y i) =
          (preservesLimitIso limit_projection_smallForgetToAbelianGroup Y).hom ≫
            limit.π (Y ⋙ limit_projection_smallForgetToAbelianGroup) i := by
      simpa using
        (preservesLimitIso_hom_π
          (G := limit_projection_smallForgetToAbelianGroup) (F := Y) i).symm
    rw [hπY]
    simp [Category.assoc]
  exact hmid.trans hfinal

/-- Helper for Chap10 Lemma 10 98 2: forgetting a short exact sequence of module inverse systems
to low-universe abelian-group inverse systems preserves short exactness. -/
private theorem limit_projection_small_forgetful_image_shortExact
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact) :
    (S.map limit_projection_smallForgetInverseSystemFunctor).ShortExact := by
  -- Exact functors preserve the input short exact sequence after stagewise forgetting.
  simpa using hS.map_of_exact limit_projection_smallForgetInverseSystemFunctor

/-- Helper for Chap10 Lemma 10 98 2: the first square in the low-universe limit-forget short
complex comparison commutes. -/
private theorem limit_projection_small_limit_forget_comparison_f_comm
    (S : ShortComplex ModuleInverseSystem) :
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₁).hom ≫
        ((S.map limit_projection_smallForgetInverseSystemFunctor).map
          limit_projection_smallAbelianInvLim).f =
      ((S.map limit_projection_moduleInvLim).map limit_projection_smallForgetToAbelianGroup).f ≫
        (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₂).hom := by
  -- The square is the naturality of the preserves-limit comparison for the first map.
  simpa [limit_projection_smallForgetInverseSystemFunctor, limit_projection_smallAbelianInvLim,
    limit_projection_moduleInvLim] using
    limit_projection_small_preservesLimitIso_hom_limMap_forget (A := A) S.f

/-- Helper for Chap10 Lemma 10 98 2: the second square in the low-universe limit-forget short
complex comparison commutes. -/
private theorem limit_projection_small_limit_forget_comparison_g_comm
    (S : ShortComplex ModuleInverseSystem) :
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₂).hom ≫
        ((S.map limit_projection_smallForgetInverseSystemFunctor).map
          limit_projection_smallAbelianInvLim).g =
      ((S.map limit_projection_moduleInvLim).map limit_projection_smallForgetToAbelianGroup).g ≫
        (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₃).hom := by
  -- The same naturality square handles the second map of the short complex.
  simpa [limit_projection_smallForgetInverseSystemFunctor, limit_projection_smallAbelianInvLim,
    limit_projection_moduleInvLim] using
    limit_projection_small_preservesLimitIso_hom_limMap_forget (A := A) S.g

/-- Helper for Chap10 Lemma 10 98 2: the forgotten module inverse-limit short complex is
canonically isomorphic to the inverse limit of the forgotten abelian-group short complex. -/
private noncomputable def limit_projection_small_limit_forget_comparison_iso
    (S : ShortComplex ModuleInverseSystem) :
    ((S.map limit_projection_moduleInvLim).map limit_projection_smallForgetToAbelianGroup) ≅
      ((S.map limit_projection_smallForgetInverseSystemFunctor).map
        limit_projection_smallAbelianInvLim) :=
  ShortComplex.isoMk
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₁)
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₂)
    (preservesLimitIso limit_projection_smallForgetToAbelianGroup S.X₃)
    (limit_projection_small_limit_forget_comparison_f_comm (A := A) S)
    (limit_projection_small_limit_forget_comparison_g_comm (A := A) S)

/-- Helper for Chap10 Lemma 10 98 2: after low-universe abelian-group forgetting, the custom
module inverse-limit short complex is short exact. -/
private theorem limit_projection_small_forgetful_limit_sequence_shortExact
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat A)).IsMittagLeffler) :
    ((S.map limit_projection_moduleInvLim).map
      limit_projection_smallForgetToAbelianGroup).ShortExact := by
  have hForgottenShortExact :
      (S.map limit_projection_smallForgetInverseSystemFunctor).ShortExact :=
    limit_projection_small_forgetful_image_shortExact (A := A) S hS
  have hForgottenLimitShortExact :
      ((S.map limit_projection_smallForgetInverseSystemFunctor).map
        limit_projection_smallAbelianInvLim).ShortExact := by
    -- Lemma `10.86.4` applies to the low-universe forgotten short complex.
    have hML' :
        ((S.map limit_projection_smallForgetInverseSystemFunctor).X₁ ⋙
          forget AddCommGrpCat).IsMittagLeffler := by
      simpa [limit_projection_smallForgetInverseSystemFunctor,
        limit_projection_smallForgetToAbelianGroup] using hML
    simpa [limit_projection_smallAbelianInvLim] using
      inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
        (S := S.map limit_projection_smallForgetInverseSystemFunctor)
        hForgottenShortExact hML'
  -- Transport exactness across the explicit limit-forget comparison isomorphism.
  exact ShortComplex.shortExact_of_iso
    (limit_projection_small_limit_forget_comparison_iso (A := A) S).symm
    hForgottenLimitShortExact

/-- Helper for Chap10 Lemma 10 98 2: a short exact sequence of module inverse systems with a
Mittag-Leffler left term remains short exact after applying the custom low-universe inverse-limit
functor. -/
private theorem limit_projection_moduleInvLim_shortExact_of_isMittagLeffler_left
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat A)).IsMittagLeffler) :
    (S.map limit_projection_moduleInvLim).ShortExact := by
  have hForgetfulLimitShortExact :
      ((S.map limit_projection_moduleInvLim).map
        limit_projection_smallForgetToAbelianGroup).ShortExact :=
    limit_projection_small_forgetful_limit_sequence_shortExact (A := A) S hS hML
  -- The faithful low-universe forgetful functor reflects short exactness back to modules.
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (F := limit_projection_smallForgetToAbelianGroup) hForgetfulLimitShortExact

/- Domain triage:
* `source-facing`: Lemma `10.98.2` studies a sequential inverse system of `A`-modules whose
  transition kernels are exactly the ideal-power submodules `I ^ n M_{n + 1}`, and concludes that
  each canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` identifies with `M_n`.
* `core/canonical` owners: the inverse system itself as a functor `OrderDual ℕ+ ⥤ ModuleCat A`,
  its stages `M_.obj (OrderDual.toDual n)`, the canonical projections `limit.π`, the quotient
  equivalence API `LinearMap.quotKerEquivOfSurjective` and `Submodule.quotEquivOfEq`, and the
  owner predicate `IsAdicComplete`.
* `bridge/view`: the lower-level surjectivity and kernel calculation for the canonical projection
  `lim M_ → M_n` are companion ingredients used only to build the canonical quotient equivalence.

Relevant owner declarations sampled for this refinement:
* `CategoryTheory.Limits.limit.π`
* `IsAdicComplete`
* `isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot`
* the inverse-limit comparison pattern in `Lemma_10_98_4`

Primitive data are only the inverse system `M_` and the source hypotheses on its transition maps.
The stages, limit module, and limit projections are canonical derived API from that owner, so the
public statement keeps the stagewise surjectivity and kernel-identification hypotheses explicit
instead of packaging them into a second owner predicate. -/

/-- Chap10 Lemma 10 98 2: applying Lemma `10.87.1` to the frozen source short complex gives a
short exact sequence on inverse limits. -/
private theorem limit_projection_quotient_shortComplex_limit_shortExact
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
      limit_projection_moduleInvLim).ShortExact := by
  -- Route correction: the imported Lemma `10.87.1` uses a higher abelian-group universe, so we
  -- apply the low-universe replay proved above to the frozen quotient-kernel short complex.
  exact limit_projection_moduleInvLim_shortExact_of_isMittagLeffler_left
    (limit_projection_quotient_shortComplex_input I M_ hSurj hKer)
    (limit_projection_quotient_shortComplex_input_shortExact I M_ hSurj hKer)
    (limit_projection_kernel_system_isMittagLeffler_input I M_ hSurj hKer)

/-- Helper for Lemma 10.98.2: the inverse-limit row coming from the frozen source short complex is
exact in the concrete linear-map form used later in the proof. -/
private theorem limit_projection_limit_row_exact
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    Function.Exact
        ((limMap
            (limit_projection_kernel_ι I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom)
        ((limMap
            (limit_projection_stageMap I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom) := by
  have hLimitShortExact :
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim).ShortExact :=
    limit_projection_quotient_shortComplex_limit_shortExact I M_ hSurj hKer
  -- Rewrite the categorical exactness field into the concrete `Function.Exact` statement
  -- requested by the downstream completion argument.
  simpa [limit_projection_quotient_shortComplex_input_f_eq,
    limit_projection_quotient_shortComplex_input_g_eq, limit_projection_moduleInvLim] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim)).1 hLimitShortExact.exact

/-- Helper for Lemma 10.98.2: the two inverse-limit consequences needed from the source short
exact row, namely exactness in the middle and monicity on the left. -/
private theorem limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    Function.Exact
        ((limMap
            (limit_projection_kernel_ι I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom)
        ((limMap
            (limit_projection_stageMap I M_
              (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
                I M_ hSurj hKer))).hom) ∧
      Mono
        (limMap
        (limit_projection_kernel_ι I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients
              I M_ hSurj hKer))) := by
  have hLimitShortExact :
      ((limit_projection_quotient_shortComplex_input I M_ hSurj hKer).map
        limit_projection_moduleInvLim).ShortExact :=
    limit_projection_quotient_shortComplex_limit_shortExact I M_ hSurj hKer
  constructor
  · -- First extract exactness from the short exact inverse-limit row in the concrete form needed.
    exact limit_projection_limit_row_exact I M_ hSurj hKer
  · -- Then project the monomorphism of the left map from the same short exact sequence.
    simpa [limit_projection_quotient_shortComplex_input_f_eq, limit_projection_moduleInvLim] using
      hLimitShortExact.mono_f

/-- Helper for Lemma 10.98.2: applying the frozen inverse-limit short exact sequence gives
exactness of
`lim K_n → lim ((lim M_i)/I^n lim M_i) → lim M_n`. -/
private theorem limit_projection_quotient_limit_exact_of_successive_ideal_power_quotients
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    Function.Exact
      ((limMap
          (limit_projection_kernel_ι I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom)
      ((limMap
          (limit_projection_stageMap I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom) := by
  -- Project the exactness component from the single remaining source-faithful blocker.
  exact
    (limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
      I M_ hSurj hKer).1

/-- Helper for Lemma 10.98.2: the left map in the inverse-limit short complex is monic. -/
private theorem limit_projection_kernel_limit_map_mono_of_successive_ideal_power_quotients
    (I : Ideal A) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    Mono
      (limMap
        (limit_projection_kernel_ι I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))) := by
  -- Project the monomorphism component from the same remaining blocker theorem.
  exact
    (limit_projection_quotient_limit_exact_and_mono_of_successive_ideal_power_quotients
      I M_ hSurj hKer).2

/-- Helper for Lemma 10.98.2: the map on inverse limits
`\varprojlim ((\varprojlim M_i) / I^n (\varprojlim M_i)) → \varprojlim M_n`
is injective, because after identifying the middle limit with the adic completion it is the
completion comparison from Lemma `10.98.1`. -/
private theorem limit_projection_quotient_limit_map_injective_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    Function.Injective
      ((limMap
          (limit_projection_stageMap I M_
            (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))).hom) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hcomplete :
      IsAdicComplete I (limit M_ : ModuleCat A) := by
    exact isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot I hI M_ hStage
  have hbij :
      Function.Bijective (completion_to_inverse_limit I M_ hStage) := by
    exact completion_to_inverse_limit_bijective_of_complete I M_ hStage hcomplete
  -- Rewrite the right map as the completion comparison preceded by the canonical middle isomorphism.
  rw [quotient_limit_map_eq_completion_to_inverse_limit I M_ hStage]
  intro x y hxy
  have hmid :
      (limit_projection_quotient_limit_iso I M_).hom x =
        (limit_projection_quotient_limit_iso I M_).hom y := by
    exact hbij.1 hxy
  have hmid_inj :
      Function.Injective ((limit_projection_quotient_limit_iso I M_).hom) := by
    intro a b hab
    have hab' := congrArg (fun z ↦ (limit_projection_quotient_limit_iso I M_).inv z) hab
    simpa using hab'
  exact hmid_inj hmid

/-- Helper for Lemma 10.98.2: the inverse limit of the kernel system
`ker((\varprojlim M_i) / I^n (\varprojlim M_i) → M_n)` vanishes. -/
private theorem limit_projection_kernel_limit_isZero_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    IsZero
      (limit
        (limit_projection_kernel_system I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer))) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hExact :
      Function.Exact
        ((limMap (limit_projection_kernel_ι I M_ hStage)).hom)
        ((limMap (limit_projection_stageMap I M_ hStage)).hom) := by
    -- Lemma `10.87.1` gives the exact inverse-limit row from the source short complex.
    simpa [hStage] using
      limit_projection_quotient_limit_exact_of_successive_ideal_power_quotients
        I M_ hSurj hKer
  have hRightInj :
      Function.Injective ((limMap (limit_projection_stageMap I M_ hStage)).hom) := by
    -- The right map is the completion comparison in disguise, hence injective by completeness.
    simpa [hStage] using
      limit_projection_quotient_limit_map_injective_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer
  have hf_zero : limMap (limit_projection_kernel_ι I M_ hStage) = 0 := by
    -- Exactness forces the image of the left map into the kernel of an injective right map.
    apply ModuleCat.hom_ext
    ext x
    apply hRightInj
    simpa using
      LinearMap.congr_fun (Function.Exact.linearMap_comp_eq_zero hExact) x
  letI :
      Mono (limMap (limit_projection_kernel_ι I M_ hStage)) := by
    simpa [hStage] using
      limit_projection_kernel_limit_map_mono_of_successive_ideal_power_quotients
        I M_ hSurj hKer
  have hzero :
      IsZero (limit (limit_projection_kernel_system I M_ hStage)) := by
    -- A monomorphism which is also the zero map can only have the zero object as source.
    exact IsZero.of_mono_eq_zero (limMap (limit_projection_kernel_ι I M_ hStage)) hf_zero
  simpa [hStage] using hzero

/-- Helper for Lemma 10.98.2: the descended quotient-stage map is bijective once the source-proof
inverse-system-of-kernels argument is installed. -/
private theorem inverse_limit_quotient_desc_bijective_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    ∀ n : ℕ+,
      Function.Bijective
        (limit_projection_quotient_desc I M_
          (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) n) := by
  intro n
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  have hKernelLimitZero :
      IsZero (limit (limit_projection_kernel_system I M_ hStage)) := by
    -- This is the source step `lim N_n/(N_n ∩ I^n M) = 0`.
    simpa [hStage] using
      limit_projection_kernel_limit_isZero_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer
  refine ⟨?_, ?_⟩
  · -- Route correction: injectivity is the remaining kernel-vanishing step from the source proof.
    have hsurjKernel :
        Function.Surjective (limitProjection (limit_projection_kernel_system I M_ hStage) n) := by
      -- The kernel system itself has surjective successor maps, so its limit projects
      -- surjectively onto every stage.
      apply limit_projection_surjective_of_successive_ideal_power_quotients
        (M_ := limit_projection_kernel_system I M_ hStage)
      intro m
      simpa [hStage, limit_projection_kernel_system_map_succ] using
        quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients
          I M_ hSurj hKer m
    have hker_bot :
        LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro y hy
      let y' : LinearMap.ker (limit_projection_quotient_desc I M_ hStage n) := ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hsurjKernel y'
      have hid :
          (𝟙 (limit (limit_projection_kernel_system I M_ hStage)) :
            limit (limit_projection_kernel_system I M_ hStage) ⟶
              limit (limit_projection_kernel_system I M_ hStage)) = 0 := by
        exact (IsZero.iff_id_eq_zero
          (X := limit (limit_projection_kernel_system I M_ hStage))).1 hKernelLimitZero
      have hx0 : x = 0 := by
        calc
          x = (𝟙 _ :
              limit (limit_projection_kernel_system I M_ hStage) ⟶
                limit (limit_projection_kernel_system I M_ hStage)) x := by simp
          _ = 0 := by simpa [hid]
      have hy' : y' = 0 := by
        calc
          y' = (limitProjection (limit_projection_kernel_system I M_ hStage) n) x := hx.symm
          _ = (limitProjection (limit_projection_kernel_system I M_ hStage) n) 0 := by rw [hx0]
          _ = 0 := by
                simpa using (limitProjection (limit_projection_kernel_system I M_ hStage) n).map_zero
      have hy0 : y = 0 := by
        exact congrArg Subtype.val hy'
      exact hy0
    exact LinearMap.ker_eq_bot.1 hker_bot
  · intro x
    -- Surjectivity descends from the already-proved surjectivity of `lim M_ → M_n`.
    rcases limit_projection_surjective_of_successive_ideal_power_quotients M_ hSurj n x with
      ⟨y, rfl⟩
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simpa [hStage] using
      congrArg (fun g ↦ g y) (limit_projection_quotient_desc_comp_mkQ I M_ hStage n)

/-- Consequence of Chap10 Lemma 10 98 2: if a sequential inverse system of `A`-modules has transition maps
`M_{n + 1} → M_n` that are surjective with kernel `I^n M_{n + 1}`, then for every `n` the
canonical quotient `(\varprojlim M_n) / I^n (\varprojlim M_n)` is linearly equivalent to the `n`th
stage. -/
@[stacks 09B8]
abbrev inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ((limit M_ : ModuleCat A) ⧸
        (I ^ (n : ℕ) • (⊤ : Submodule A (limit M_ : ModuleCat A)))) ≃ₗ[A]
      M_.obj (OrderDual.toDual n) :=
  LinearEquiv.ofBijective
    (limit_projection_quotient_desc I M_
      (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer) n)
    (inverse_limit_quotient_desc_bijective_of_successive_ideal_power_quotients
      I hI M_ hSurj hKer n)

-- Proof sketch: unfold the quotient equivalence into the kernel-identification equivalence followed
-- by the first isomorphism theorem for the surjective projection `lim M_ → M_n`, then apply the
-- corresponding `quotKerEquivOfSurjective_apply_mk` computation rule.
/-- The quotient equivalence of Lemma `10.98.2` sends the class of an inverse-limit element to its
`n`th stage projection. -/
theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_apply_mk
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) (x : (limit M_ : ModuleCat A)) :
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients
        I hI M_ hSurj hKer n (Submodule.Quotient.mk x) =
      limitProjection M_ n x := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer
  -- Evaluate the imported quotient-desc computation rule on the representative `x`.
  simpa [inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients, hStage] using
    congrArg (fun g ↦ g x) (limit_projection_quotient_desc_comp_mkQ I M_ hStage n)

-- Proof sketch: the kernel computation implies `I^n M_n = 0` for every stage, so Lemma `10.98.1`
-- applies directly to the inverse system `M_`.
/-- The inverse limit of a sequential system with successive quotients `M_n = M_{n + 1} / I^n
M_{n + 1}` is `I`-adically complete. -/
theorem isAdicComplete_inverseLimit_of_successive_ideal_power_quotients
    (I : Ideal A) (hI : I.FG) (M_ : ModuleInverseSystem)
    (hSurj :
      ∀ n : ℕ+,
        Function.Surjective
          ((stageMap M_ n :
            M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))))
    (hKer :
      ∀ n : ℕ+,
        LinearMap.ker
            ((stageMap M_ n :
              M_.obj (OrderDual.toDual (n + 1)) →ₗ[A] M_.obj (OrderDual.toDual n))) =
          I ^ (n : ℕ) • (⊤ : Submodule A ↥(M_.obj (OrderDual.toDual (n + 1))))) :
    IsAdicComplete I (limit M_ : ModuleCat A) := by
  -- Apply Lemma `10.98.1` to the stagewise annihilation statement just proved above.
  exact isAdicComplete_inverseLimit_of_stagewise_pow_smul_top_eq_bot I hI M_
    (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients I M_ hSurj hKer)

end
