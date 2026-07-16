import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_86_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} [Ring R]

local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat R
local notation "moduleInvLim" => (lim : ModuleInverseSystem ⥤ ModuleCat R)

-- Domain-style sampling:
-- * source-facing layer: short exact sequences of inverse systems of `R`-modules over `ℕ+`.
-- * core/canonical owner: `CategoryTheory.Functor.IsMittagLeffler` on the underlying
--   `Type`-valued inverse system, together with
--   `inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left`.
-- * relevant sampled declarations:
--   `CategoryTheory.Functor.IsMittagLeffler`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`,
--   `CategoryTheory.Functor.IsMittagLeffler.toPreimages`,
--   `inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left`.
-- * primitive data: a short exact sequence of module inverse systems and the owner
--   Mittag-Leffler hypothesis on the left term.
-- * bridge/view output: short exactness after applying the inverse-limit functor on `ModuleCat R`.
--
-- Proof sketch: this is the module-valued bridge specialization of Lemma `10.86.4`. Apply that
-- inverse-limit short-exactness theorem to the underlying inverse system of abelian groups
-- attached to the short exact sequence of `R`-modules; the owner hypothesis here is unchanged,
-- namely the canonical `Functor.IsMittagLeffler` condition on the underlying `Type`-valued left
-- inverse system.
/-- Helper for Lemma 10.87.1: the forgetful functor from `R`-modules to abelian groups. -/
private abbrev forgetToAbelianGroup : ModuleCat R ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat R) AddCommGrpCat.{u}

/-- Helper for Lemma 10.87.1: the ambient category of abelian-group inverse systems over `ℕ+`. -/
private abbrev AbelianGroupInverseSystem : Type (u + 1) :=
  OrderDual ℕ+ ⥤ AddCommGrpCat.{u}

/-- Helper for Lemma 10.87.1: the inverse-limit functor on abelian-group inverse systems. -/
private abbrev abelianInvLim : AbelianGroupInverseSystem ⥤ AddCommGrpCat.{u} :=
  lim

/-- Helper for Lemma 10.87.1: the whiskering functor on inverse systems induced by forgetting
`R`-modules to abelian groups. -/
private abbrev forgetInverseSystemFunctor : ModuleInverseSystem ⥤ AbelianGroupInverseSystem :=
  (Functor.whiskeringRight (OrderDual ℕ+) (ModuleCat R) AddCommGrpCat).obj
    forgetToAbelianGroup

/-- Helper for Lemma 10.87.1: forgetting a short exact sequence of module inverse systems to
abelian-group inverse systems preserves short exactness. -/
private theorem forgetful_image_shortExact
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact) :
    (S.map forgetInverseSystemFunctor).ShortExact := by
  -- Apply the exactness-preserving whiskering functor induced by `forget₂`.
  simpa using hS.map_of_exact forgetInverseSystemFunctor

/-- Helper for Lemma 10.87.1: the comparison isomorphisms `preservesLimitIso
forgetToAbelianGroup`
intertwine the maps on inverse limits induced by a morphism of module inverse systems. -/
private theorem preservesLimitIso_hom_limMap_forget
    {X Y : ModuleInverseSystem}
    (α : X ⟶ Y) :
    (preservesLimitIso forgetToAbelianGroup X).hom ≫
        limMap (Functor.whiskerRight α forgetToAbelianGroup) =
      forgetToAbelianGroup.map (limMap α) ≫ (preservesLimitIso forgetToAbelianGroup Y).hom := by
  -- Compare both composites after evaluating at every stage of the inverse system.
  apply limit.hom_ext
  intro i
  have hmid :
      (preservesLimitIso forgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α forgetToAbelianGroup) ≫
            limit.π (Y ⋙ forgetToAbelianGroup) i =
        forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
    calc
      (preservesLimitIso forgetToAbelianGroup X).hom ≫
          limMap (Functor.whiskerRight α forgetToAbelianGroup) ≫
            limit.π (Y ⋙ forgetToAbelianGroup) i
        = (preservesLimitIso forgetToAbelianGroup X).hom ≫
            limit.π (X ⋙ forgetToAbelianGroup) i ≫
              (Functor.whiskerRight α forgetToAbelianGroup).app i := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t =>
                      (preservesLimitIso forgetToAbelianGroup X).hom ≫ t)
                    (limMap_π (Functor.whiskerRight α forgetToAbelianGroup) i)
      _ = forgetToAbelianGroup.map (limit.π X i) ≫
            (Functor.whiskerRight α forgetToAbelianGroup).app i := by
              simpa [Category.assoc] using
                congrArg
                  (fun t => t ≫ (Functor.whiskerRight α forgetToAbelianGroup).app i)
                  (preservesLimitIso_hom_π (G := forgetToAbelianGroup) (F := X) i)
      _ = forgetToAbelianGroup.map (limit.π X i) ≫
            forgetToAbelianGroup.map (α.app i) := by
              rfl
      _ = forgetToAbelianGroup.map (limit.π X i ≫ α.app i) := by
              rw [← forgetToAbelianGroup.map_comp]
      _ = forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) := by
              rw [limMap_π]
  have hfinal :
      forgetToAbelianGroup.map (limMap α ≫ limit.π Y i) =
        (forgetToAbelianGroup.map (limMap α) ≫
            (preservesLimitIso forgetToAbelianGroup Y).hom) ≫
          limit.π (Y ⋙ forgetToAbelianGroup) i := by
    rw [forgetToAbelianGroup.map_comp]
    have hπY :
        forgetToAbelianGroup.map (limit.π Y i) =
          (preservesLimitIso forgetToAbelianGroup Y).hom ≫
            limit.π (Y ⋙ forgetToAbelianGroup) i := by
      simpa using
        (preservesLimitIso_hom_π (G := forgetToAbelianGroup) (F := Y) i).symm
    rw [hπY]
    simp [Category.assoc]
  exact hmid.trans hfinal

/-- Helper for Lemma 10.87.1: the first square in the limit comparison short-complex isomorphism
commutes. -/
private theorem limit_forget₂_comparison_f_comm
    (S : ShortComplex ModuleInverseSystem) :
    (preservesLimitIso forgetToAbelianGroup S.X₁).hom ≫
        ((S.map forgetInverseSystemFunctor).map abelianInvLim).f =
      ((S.map moduleInvLim).map forgetToAbelianGroup).f ≫
        (preservesLimitIso forgetToAbelianGroup S.X₂).hom := by
  -- This is the naturality square for `S.f` under the limit-forget comparison.
  simpa using preservesLimitIso_hom_limMap_forget (R := R) S.f

/-- Helper for Lemma 10.87.1: the second square in the limit comparison short-complex isomorphism
commutes. -/
private theorem limit_forget₂_comparison_g_comm
    (S : ShortComplex ModuleInverseSystem) :
    (preservesLimitIso forgetToAbelianGroup S.X₂).hom ≫
        ((S.map forgetInverseSystemFunctor).map abelianInvLim).g =
      ((S.map moduleInvLim).map forgetToAbelianGroup).g ≫
        (preservesLimitIso forgetToAbelianGroup S.X₃).hom := by
  -- The same naturality argument handles `S.g`.
  simpa using preservesLimitIso_hom_limMap_forget (R := R) S.g

/-- Helper for Lemma 10.87.1: the forgotten limit short complex is canonically isomorphic to the
limit short complex of the forgotten inverse systems. -/
private noncomputable def limit_forget₂_comparison_iso
    (S : ShortComplex ModuleInverseSystem) :
    ((S.map moduleInvLim).map forgetToAbelianGroup) ≅
      ((S.map forgetInverseSystemFunctor).map abelianInvLim) :=
  ShortComplex.isoMk
    (preservesLimitIso forgetToAbelianGroup S.X₁)
    (preservesLimitIso forgetToAbelianGroup S.X₂)
    (preservesLimitIso forgetToAbelianGroup S.X₃)
    (limit_forget₂_comparison_f_comm (R := R) S)
    (limit_forget₂_comparison_g_comm (R := R) S)

/-- Helper for Lemma 10.87.1: after forgetting to abelian groups, Lemma 10.86.4 gives short
exactness on inverse limits. -/
private theorem forgetful_limit_sequence_shortExact
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat R)).IsMittagLeffler) :
    ((S.map moduleInvLim).map forgetToAbelianGroup).ShortExact := by
  have hForgottenShortExact : (S.map forgetInverseSystemFunctor).ShortExact :=
    forgetful_image_shortExact (R := R) S hS
  have hForgottenLimitShortExact :
      ((S.map forgetInverseSystemFunctor).map abelianInvLim).ShortExact := by
    -- Lemma 10.86.4 applies directly to the forgotten short exact sequence.
    have hML' :
        ((S.map forgetInverseSystemFunctor).X₁ ⋙ forget AddCommGrpCat.{u}).IsMittagLeffler := by
      simpa using hML
    simpa using
      inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
        (S := S.map forgetInverseSystemFunctor) hForgottenShortExact hML'
  -- Transport the abelian-group exactness statement back across the canonical limit comparison.
  exact ShortComplex.shortExact_of_iso
    (limit_forget₂_comparison_iso (R := R) S).symm
    hForgottenLimitShortExact

/-- Lemma 10.87.1: for a short exact sequence of inverse systems of `R`-modules over `ℕ+`, if the
left system is Mittag-Leffler, then the induced sequence on inverse limits
`0 ⟶ \varprojlim K_i ⟶ \varprojlim L_i ⟶ \varprojlim M_i ⟶ 0`
is short exact. -/
@[stacks 03CA]
theorem moduleInverseLimit_shortExact_of_isMittagLeffler_left
    (S : ShortComplex ModuleInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat R)).IsMittagLeffler) :
    (S.map moduleInvLim).ShortExact := by
  -- Follow the source proof: forget to abelian groups, apply Lemma 10.86.4, then reflect.
  have hForgetfulLimitShortExact :
      ((S.map moduleInvLim).map forgetToAbelianGroup).ShortExact :=
    forgetful_limit_sequence_shortExact (R := R) S hS hML
  -- The faithful forgetful functor reflects short exactness back to `ModuleCat R`.
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (F := forgetToAbelianGroup) hForgetfulLimitShortExact
