import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_16_1 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

/- Domain-style sampling for Definition 18.16.1:
- primary domain: lower shriek on abelian presheaves and abelian sheaves along a functor of
  sites, with continuity only for comparison to the chosen sheaf-level owner;
- sampled owner declarations:
  `Functor.lan`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lower shriek `g_{p!}` on abelian presheaves, together with the
    induced sheaf-level lower shriek given by sheafifying the presheaf lower shriek;
  `core/canonical`: the presheaf owner `u.op.lan` and, under continuity, the chosen sheaf owner
    `u.sheafPullback AddCommGrpCat J K`;
  `bridge/view`: the pointwise colimit formula
    `u.op.leftKanExtensionObjIsoColimit`, and, under continuity, the identification of the
    source-level sheaf construction
    `Functor.sheafPullbackConstruction.sheafPullback` with the canonical owner by
    `Functor.sheafPullbackConstruction.sheafPullbackIso`.

Primitive data are the functor `u`, the existence of left Kan extensions along `u.op`, and weak
sheafification on the target site; continuity is only primitive for the comparison with the chosen
sheaf-owner `u.sheafPullback`. The lower shriek owners and their pointwise/construction-level
descriptions are derived API already owned upstream, so this file should recall those owners
directly rather than keep parallel local `abelian...` wrappers.
-/

section PresheafLevel

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]

/- Definition 18.16.1, presheaf level: the abelian lower shriek is the canonical left Kan
extension along `u.op`, namely `u.op.lan`. -/
#check (u.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})

end

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseLeftKanExtension F]
variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Dᵒᵖ)

/- Companion bridge: the value of the presheaf lower shriek at `V` is the colimit over the
costructured-arrow category of arrows `V ⟶ u(U)`. -/
#check (u.op.leftKanExtensionObjIsoColimit F V :
  ((u.op.lan).obj F).obj V ≅ colimit (CostructuredArrow.proj u.op V ⋙ F))

end

end PresheafLevel

section SheafLevel

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

section

variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Definition 18.16.1, sheaf level: the source-facing lower shriek is obtained by applying the
presheaf lower shriek to the underlying presheaf and then sheafifying. -/
#check (Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

end

section

variable [u.IsContinuous J K]
variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension F]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Companion bridge: under continuity, the canonical chosen sheaf owner for the abelian lower
shriek is `u.sheafPullback AddCommGrpCat J K`. -/
#check (u.sheafPullback AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

/- Companion bridge: the source-level construction by applying the presheaf lower shriek to the
underlying presheaf and then sheafifying is
`Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat J K`. -/
#check (Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{w} J K :
  Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

/- Companion bridge: the canonical owner and the source-level construction are canonically
isomorphic. -/
#check (Functor.sheafPullbackConstruction.sheafPullbackIso u AddCommGrpCat.{w} J K :
  u.sheafPullback AddCommGrpCat.{w} J K ≅
    Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{w} J K)

end

end SheafLevel

end CategoryTheory

/-! ### Lemma_18_16_2 (from Chap18) -/
open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

section

variable [∀ ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension ℱ]
variable (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (𝒢 : Dᵒᵖ ⥤ AddCommGrpCat.{w})

/- Domain-style sampling for Lemma 18.16.2:
- primary domain: adjunctions defining lower shriek / inverse-image for presheaves and sheaves of
  abelian groups on sites;
- sampled owner declarations:
  `CategoryTheory.Functor.lanAdjunction`,
  `CategoryTheory.Functor.sheafAdjunctionContinuous`,
  `Definition_18_16_1`'s canonical lower-shriek owners `u.op.lan` and
  `u.sheafPullback AddCommGrpCat J K`,
  `Lemma_18_13_2`'s direct recall of the same adjunction pattern for module sheaves;
- best owner abstractions: `CategoryTheory.Functor.lanAdjunction` for the presheaf-level lower
  shriek and `CategoryTheory.Functor.sheafAdjunctionContinuous` for the sheaf-level lower shriek;
- primitive data: the site functor `u`, continuity for the sheaf clause, and the standard
  Kan-extension / sheafification existence hypotheses;
- derived API: the Hom-set bijections obtained from these owner adjunctions via `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the textbook Hom-set equivalences for lower shriek versus inverse image on
  abelian presheaves and abelian sheaves;
- `core/canonical`: the owner adjunctions
  `u.op.lanAdjunction AddCommGrpCat` and
  `u.sheafAdjunctionContinuous AddCommGrpCat J K`;
- `bridge/view`: the specializations of `.homEquiv` at concrete objects `ℱ` and `𝒢`.

This item is therefore a canonical-recall item: it should recall the owner adjunctions directly
and keep the Hom-set equivalences only as thin companions. -/

/- Lemma 18.16.2 (1), owner form: the presheaf-level lower shriek on abelian presheaves is the
adjunction `u.op.lan ⊣ (Functor.whiskeringLeft _ _ _).obj u.op`. -/
recall CategoryTheory.Functor.lanAdjunction

/- Lemma 18.16.2 (1): for abelian-group-valued presheaves, the lower shriek `g_{p!}` is the
left Kan extension `u.op.lan`, left adjoint to pullback `u^p`; equivalently, there is a
canonical bifunctorial hom-set equivalence
`Mor((u.op.lan).obj ℱ, 𝒢) ≃ Mor(ℱ, u^p 𝒢)`. -/
#check
  (((u.op.lanAdjunction AddCommGrpCat.{w}).homEquiv ℱ 𝒢) :
    ((u.op.lan).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ u.op ⋙ 𝒢))

variable [u.IsContinuous J K]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable (ℱ : Sheaf J AddCommGrpCat.{w}) (𝒢 : Sheaf K AddCommGrpCat.{w})

/- Lemma 18.16.2 (2), owner form: the sheaf-level lower shriek on abelian sheaves is the
adjunction `u.sheafPullback AddCommGrpCat J K ⊣
u.sheafPushforwardContinuous AddCommGrpCat J K`. -/
recall CategoryTheory.Functor.sheafAdjunctionContinuous

/- Lemma 18.16.2 (2): for abelian sheaves, the lower shriek `g_!`, implemented by
`u.sheafPullback AddCommGrpCat J K`, is left adjoint to the inverse-image functor
`u.sheafPushforwardContinuous AddCommGrpCat J K`; equivalently, there is a canonical
bifunctorial hom-set equivalence
`Mor((u.sheafPullback AddCommGrpCat J K).obj ℱ, 𝒢) ≃
  Mor(ℱ, (u.sheafPushforwardContinuous AddCommGrpCat J K).obj 𝒢)`. -/
#check
  (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).homEquiv ℱ 𝒢) :
    ((u.sheafPullback AddCommGrpCat.{w} J K).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj 𝒢))

end

end CategoryTheory

/-! ### Lemma_18_16_3 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

-- Proof sketch: `u.sheafPullback AddCommGrpCat J K` is the canonical lower shriek `g_!`, hence
-- right exact because it is a left adjoint. Under the pullback and equalizer hypotheses on `u`,
-- the Chapter 7 owner API upgrades the source-style finite connected limit argument to the
-- canonical sheaf-pullback owner, yielding exactness on abelian sheaves.
/-- Lemma 18.16.3: if `u : C ⥤ D` is continuous, `C` has fibre products and equalizers, and `u`
commutes with them, then the lower shriek
`g_! : Ab(\mathcal C) ⥤ Ab(\mathcal D)`, realized in the project API as
`u.sheafPullback AddCommGrpCat J K`, is exact. The additional sheafification and Kan-extension
hypotheses are the standard Lean assumptions needed to construct this functor. -/
theorem sheafPullback_addCommGrp_exact_of_continuous_preserves_pullbacks_equalizers
    (u : C ⥤ D)
    [u.IsContinuous J K]
    [∀ ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension ℱ]
    [HasSheafify K AddCommGrpCat.{w}]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

end CategoryTheory

/-! ### Lemma_18_16_4 (from Chap18) -/
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (G : C ⥤ D)
variable [G.Full] [G.Faithful]

/- Domain-style sampling for Lemma 18.16.4:
- primary domain: unit and counit isomorphisms for sheaf adjunctions induced by a fully faithful
  functor of sites;
- sampled owner API:
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`,
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful`;
- best owner abstractions: the adjunction owners
  `G.sheafAdjunctionContinuous AddCommGrpCat J K` and
  `G.sheafAdjunctionCocontinuous AddCommGrpCat J K`;
- source/core/bridge triage:
  `source-facing`: the canonical maps `ℱ ⟶ g⁻¹(g_! ℱ)` and `g⁻¹(g_* ℱ) ⟶ ℱ` for abelian sheaves;
  `core/canonical`: the general owner-level `IsIso` instances from
    `Chap07/Lemma_7_21_7`;
  `bridge/view`: this file is only the `AddCommGrpCat` specialization of those instances, so its
    public surface should be direct recall/reuse rather than fresh wrapper instance names.

Primitive data are the site functor `G`, its full faithfulness, and the owner-specific adjunction
existence hypotheses. The `IsIso` facts are derived API owned by `Lemma_7_21_7`, so this file
should expose only the specialized canonical inference, not a second parallel instance layer. -/

section

variable [G.IsContinuous J K]
variable [(G.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K).IsRightAdjoint]
variable (ℱ : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.16.4 (1): for an abelian sheaf `ℱ` on `C`, the canonical map
`ℱ ⟶ g⁻¹(g_! ℱ)`, i.e. the unit component of
`G.sheafAdjunctionContinuous AddCommGrpCat J K`, is an isomorphism. This is the direct
`AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful

#synth IsIso ((G.sheafAdjunctionContinuous AddCommGrpCat.{max u v} J K).unit.app ℱ)

end

section

variable [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, G.op.HasPointwiseRightKanExtension F]
variable (ℱ : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.16.4 (2): for an abelian sheaf `ℱ` on `C`, the canonical map
`g⁻¹(g_* ℱ) ⟶ ℱ`, i.e. the counit component of
`G.sheafAdjunctionCocontinuous AddCommGrpCat J K`, is an isomorphism. This is the direct
`AddCommGrpCat` specialization of the chapter-level owner instance. -/
recall counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful

#synth IsIso ((G.sheafAdjunctionCocontinuous AddCommGrpCat.{max u v} J K).counit.app ℱ)

end

end CategoryTheory

/-! ### Remark_18_16_5 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B)

-- Proof sketch: `ModuleCat.extendScalars f` already has the canonical right adjoint
-- `ModuleCat.restrictScalars f` via `ModuleCat.extendRestrictScalarsAdj f`. If it also had a left
-- adjoint, then it would be a right adjoint and hence preserve all limits, in particular finite
-- limits. For extension of scalars, preservation of finite limits forces flatness of `f`.
/-- Remark 18.16.5: if extension of scalars along a ring map `f : A →+* B` also has a left
adjoint, equivalently if `ModuleCat.extendScalars f` is a right adjoint, then `f` is flat. This
is the module-theoretic obstruction to extending lower shriek functors for arbitrary morphisms of
ringed topoi. -/
theorem flat_of_extendScalars_isRightAdjoint
    (h : (ModuleCat.extendScalars.{u, u, u} f).IsRightAdjoint) :
    f.Flat := by
  letI := h
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) := by infer_instance
  letI : PreservesFiniteLimits (ModuleCat.restrictScalars.{u, u, u} f) := by infer_instance
  have hleft : PreservesFiniteLimits
      (tensorLeft ((ModuleCat.restrictScalars.{u, u, u} f).obj (ModuleCat.of B B))) := by
    change PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars.{u, u, u} f)
    exact comp_preservesFiniteLimits _ _
  rw [RingHom.Flat]
  change Module.Flat A ↑((ModuleCat.restrictScalars.{u, u, u} f).obj (ModuleCat.of B B))
  exact (Module.Flat.iff_preservesFiniteLimits_tensorLeft
    ((ModuleCat.restrictScalars.{u, u, u} f).obj (ModuleCat.of B B))).2 hleft

end

/-! ### Lemma_18_16_6 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 18.16.6:
- primary domain: lower shriek / inverse-image / direct-image functors on abelian sheaves under an
  adjunction of site functors;
- sampled owner declarations:
  `Functor.sheafPullback`,
  `Functor.sheafPullbackCocontinuous`,
  `CategoryTheory.sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint`,
  `CategoryTheory.continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- best owner abstractions:
  `u.sheafPullback AddCommGrpCat J K` for the lower shriek attached to the continuous right
  adjoint `u`,
  `w.sheafPullbackCocontinuous AddCommGrpCat K J` for the inverse image attached to the
  cocontinuous left adjoint `w`,
  and `w.sheafPushforwardCocontinuous AddCommGrpCat K J` for the corresponding direct image;
- primitive data: the functors `u`, `w`, the adjunction `w ⊣ u`, and the standard Kan-extension /
  sheafification hypotheses needed to form these owner functors;
- derived API: the Chapter 7 comparison isomorphisms between these owners and the resulting
  exactness statement on abelian sheaves.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison of the abelian lower shriek `g_!` with the inverse- and
  direct-image functors attached to the cocontinuous left adjoint `w`, plus exactness of `g_!`;
- `core/canonical`: the Chapter 7 owner functors
  `u.sheafPullback AddCommGrpCat J K`,
  `w.sheafPullbackCocontinuous AddCommGrpCat K J`,
  `u.sheafPushforwardContinuous AddCommGrpCat J K`,
  `w.sheafPushforwardCocontinuous AddCommGrpCat K J`;
- `bridge/view`: the Chapter 7 comparison theorems specialized below to `AddCommGrpCat`.

The previous one-off Chapter 18 wrapper for the cocontinuous inverse image was a duplicate wheel.
The canonical owner now lives upstream in Chapter 7 as
`Functor.sheafPullbackCocontinuous`, so this file reuses that owner directly.
-/

section

variable (u : C ⥤ D) (w : D ⥤ C)
variable [u.IsContinuous J K]
variable (adj : w ⊣ u)

-- Proof sketch: compare `u.sheafPullback AddCommGrpCat J K` with the canonical owner
-- `w.sheafPullbackCocontinuous AddCommGrpCat K J` from Chapter 7, then use the same finite-limit
-- and left-adjoint argument as in the set-valued case.
/-- Lemma 18.16.6 (1): if `u : C ⥤ D` is continuous and has a left adjoint `w`, then the lower
shriek `g_!` on abelian sheaves, realized as `u.sheafPullback AddCommGrpCat J K`, is exact. -/
theorem sheafPullback_addCommGrp_exact_of_leftAdjoint
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, u.op.HasLeftKanExtension P]
    [HasSheafify K AddCommGrpCat.{max u v}] :
    exactFunctor (Sheaf J AddCommGrpCat.{max u v}) (Sheaf K AddCommGrpCat.{max u v})
      (u.sheafPullback AddCommGrpCat.{max u v} J K) := sorry

section

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]

/- Lemma 18.16.6 (2): the abelian lower shriek is the inverse-image functor attached to the
cocontinuous left adjoint `w`; this is exactly the `AddCommGrpCat` specialization of the Chapter 7
owner comparison. -/
#check
  (sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint
      u w adj AddCommGrpCat.{max u v} :
    u.sheafPullback AddCommGrpCat.{max u v} J K ≅
      w.sheafPullbackCocontinuous AddCommGrpCat.{max u v} K J)

end

section

variable [w.IsCocontinuous K J]
variable [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}, w.op.HasPointwiseRightKanExtension P]

/- Lemma 18.16.6 (3): the inverse image `g⁻¹` attached to `u` is the direct image attached to the
cocontinuous left adjoint `w`; this is the corresponding `AddCommGrpCat` specialization of the
Chapter 7 owner comparison. -/
#check
  (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      w u AddCommGrpCat.{max u v} adj :
    u.sheafPushforwardContinuous AddCommGrpCat.{max u v} J K ≅
      w.sheafPushforwardCocontinuous AddCommGrpCat.{max u v} K J)

end

end

end CategoryTheory
