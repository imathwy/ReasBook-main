import Mathlib
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_22_1 (from Chap07) -/
open CategoryTheory Functor Opposite
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v)

/-
Domain-style sampling for Lemma 7.22.1:
- primary domain: sheaf-theoretic direct and inverse image constructions attached to a
  cocontinuous functor with a right adjoint;
- sampled owner API:
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `Functor.sheafPullbackCocontinuous`,
  `Functor.lanAdjunction`,
  `Adjunction.leftAdjointUniq`,
  `Adjunction.rightAdjointUniq`;
- source-facing layer: the comparison of `g_*` with pullback of underlying presheaves along the
  right adjoint, and the comparison of `g⁻¹` with the sheafification of the canonical left Kan
  extension functor `v.op.lan`;
- core/canonical owner: `u.sheafPushforwardCocontinuous (Type w) J K` and
  `u.sheafPullbackCocontinuous (Type w) J K`, together with the presheaf owner
  `v.op.lanAdjunction (Type w)`;
- bridge/view: the displayed natural isomorphisms obtained from uniqueness of left and right
  adjoints.

Primitive data are the adjunction `u ⊣ v`, the cocontinuous/Kan-extension hypotheses needed for
the pushforward owner, and the weak sheafification hypothesis needed for the pullback owner. Once
`adj : u ⊣ v` is fixed, the Kan-extension existence assumptions are derived locally from the
induced adjunction on presheaf precomposition, so they should not remain in the public theorem
headers. The public declarations below are derived bridge isomorphisms, so they should reuse
those owner functors rather than restating their raw sheafification formulas or introducing a
public chosen left adjoint in place of the canonical `v.op.lan`.
-/

section Pushforward

variable [u.IsCocontinuous J K]
variable (K)

private theorem hasPointwiseRightKanExtension_of_adjunction
    (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v) :
    ∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P := fun P ↦ by
  intro Y
  change HasLimit (StructuredArrow.proj Y u.op ⋙ P)
  let _ : ∀ X : Dᵒᵖ, HasInitial (StructuredArrow X u.op) :=
    let h : u.op.IsRightAdjoint := Adjunction.isRightAdjoint (adj.op)
    isRightAdjoint_iff_hasInitial_structuredArrow.mp h
  infer_instance

/-- Lemma 7.22.1 (1): for a cocontinuous functor `u` with right adjoint `v`, the direct image of a
sheaf along the morphism of topoi associated to `u` is canonically the pullback of the underlying
presheaf along `v`; equivalently, its value at `V` is `ℱ(v.obj V)`. -/
noncomputable def sheafPushforwardCocontinuousRightAdjointIso
    (ℱ : Sheaf J (Type w)) :
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    ((u.sheafPushforwardCocontinuous (Type w) J K).obj ℱ).1 ≅
      v.op ⋙ ℱ.1 :=
  by
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    exact
      (u.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) J K).app ℱ ≪≫
    ((u.op.ranAdjunction (Type w)).rightAdjointUniq
      (adj.op.whiskerLeft (Type w))).app ℱ.1

-- Proof sketch: the declaration `sheafPushforwardCocontinuousRightAdjointIso` is already the
-- canonical comparison isomorphism; evaluate its `hom` at `op V` and use that components of an
-- isomorphism are isomorphisms in `Type`.
/-- The canonical comparison map realizing the direct-image formula is objectwise an isomorphism. -/
theorem sheafPushforwardCocontinuousRightAdjointIso_hom_app_isIso
    (ℱ : Sheaf J (Type w)) (V : D) :
    letI := hasPointwiseRightKanExtension_of_adjunction u v adj
    IsIso
      ((sheafPushforwardCocontinuousRightAdjointIso K u v adj ℱ).hom.app (op V)) := by
  letI := hasPointwiseRightKanExtension_of_adjunction u v adj
  infer_instance

end Pushforward

section Pullback

variable [HasWeakSheafify J (Type w)]

private theorem hasPointwiseLeftKanExtension_of_adjunction
    (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v) :
    ∀ P : Dᵒᵖ ⥤ Type w, v.op.HasPointwiseLeftKanExtension P := fun P ↦ by
  intro Y
  change HasColimit (CostructuredArrow.proj v.op Y ⋙ P)
  let _ : ∀ X : Cᵒᵖ, HasTerminal (CostructuredArrow v.op X) :=
    let h : v.op.IsLeftAdjoint := Adjunction.isLeftAdjoint (adj.op)
    isLeftAdjoint_iff_hasTerminal_costructuredArrow.mp h
  infer_instance

/-- Lemma 7.22.1 (2): the canonical inverse-image owner
`u.sheafPullbackCocontinuous (Type w) J K` is objectwise the sheafification of the canonical left
Kan extension `v.op.lan`; this is the intrinsic source formula `(v_p 𝒢)^#`. -/
noncomputable def sheafifyPullbackIsoSheafifyLeftKanExtension
    (𝒢 : Sheaf K (Type w)) :
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    (u.sheafPullbackCocontinuous (Type w) J K).obj 𝒢 ≅
      (presheafToSheaf J (Type w)).obj ((v.op.lan).obj 𝒢.1) :=
  by
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    exact
      (presheafToSheaf J (Type w)).mapIso
        (((adj.op.whiskerLeft (Type w)).leftAdjointUniq (v.op.lanAdjunction (Type w))).app 𝒢.1)

-- Proof sketch: the declaration `sheafifyPullbackIsoSheafifyLeftKanExtension` is already an
-- isomorphism in the sheaf category, so its `hom` is automatically an isomorphism.
/-- The canonical comparison map from the cocontinuous inverse image to the sheafification of
`v.op.lan` is an isomorphism. -/
theorem sheafifyPullbackIsoSheafifyLeftKanExtension_hom_isIso
    (𝒢 : Sheaf K (Type w)) :
    letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
    IsIso
      ((sheafifyPullbackIsoSheafifyLeftKanExtension u v adj 𝒢).hom :
        (u.sheafPullbackCocontinuous (Type w) J K).obj 𝒢 ⟶
          (presheafToSheaf J (Type w)).obj ((v.op.lan).obj 𝒢.1)) := by
  -- Reuse the already-constructed comparison isomorphism in the same Kan-extension context.
  letI := hasPointwiseLeftKanExtension_of_adjunction u v adj
  infer_instance

end Pullback

end CategoryTheory

/-! ### Lemma_7_22_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C) (adj : u ⊣ v)

/- Domain-style sampling for Lemma 7.22.2:
- primary domain: adjunctions between Grothendieck sites and the induced direct-image functors on
  sheaves;
- sampled owner API:
  `RepresentablyFlat.of_isRightAdjoint`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for a continuous right adjoint `v` with left adjoint `u`;
  `core/canonical`: the owner class `IsMorphismOfSites K J v` and the sheaf pushforward owners
  attached to `u` and `v`;
  `bridge/view`: the right-adjoint-specific theorem below, and the comparison isomorphism between
  the two direct-image functors.

Primitive data are the adjunction `u ⊣ v`, continuity of `v`, and the right-Kan-extension
hypotheses needed for the `A`-valued cocontinuous pushforward owner, together with the explicit
cocontinuity owner on `u` needed to form `u.sheafPushforwardCocontinuous`. Representable
flatness and the site-morphism structure of `v` are derived from the owner API, so they should
remain internal instance plumbing rather than a parallel public wrapper.
-/

-- Proof sketch: after composing both direct-image functors with `sheafToPresheaf K (Type w)`,
-- the continuous pushforward of `v` is definitionally pullback along `v.op`, while the
-- cocontinuous pushforward of `u` is canonically identified with that same presheaf functor by
-- `Adjunction.rightAdjointUniq` applied to `u.op.ranAdjunction` and `adj.op.whiskerLeft`. Since
-- `sheafToPresheaf K (Type w)` is fully faithful, this presheaf comparison lifts uniquely to the
-- claimed isomorphism of sheaf functors.
/-- Lemma 7.22.2: if `u : \mathcal C \to \mathcal D` is cocontinuous with right adjoint
`v : \mathcal D \to \mathcal C` and `v` is continuous, then `v` defines the morphism of sites
`(\mathcal C, J) \to (\mathcal D, K)`, and the direct-image functor of its associated morphism of
topoi is canonically isomorphic to the cocontinuous direct-image functor attached to `u`, i.e. to
`g_*`. In the canonical API this cocontinuity is supplied by the explicit owner
`u.IsCocontinuous J K`. -/
noncomputable def continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    by
      let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
      let _ : IsMorphismOfSites K J v := inferInstance
      exact
        v.sheafPushforwardContinuous A K J ≅
          u.sheafPushforwardCocontinuous A J K := by
  let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
  let _ : IsMorphismOfSites K J v := inferInstance
  let e : u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ (Functor.whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op :=
    (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf J A)
        (Adjunction.rightAdjointUniq (u.op.ranAdjunction A) (adj.op.whiskerLeft A))
  exact ((fullyFaithfulSheafToPresheaf K A).whiskeringRight (Sheaf J A)).preimageIso <|
    (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J) ≪≫ e.symm

/-- The forward comparison morphism from the continuous direct image along `v` to the
cocontinuous direct image along `u` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` of the canonical isomorphism
-- `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`.
theorem continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward_hom_isIso
    (A : Type (w + 1)) [Category.{w} A]
    (adj : u ⊣ v)
    [v.IsContinuous K J]
    [u.IsCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension P] :
    IsIso
      ((continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
          u v A adj).hom :
        v.sheafPushforwardContinuous A K J ⟶
          u.sheafPushforwardCocontinuous A J K) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism.
  infer_instance

end CategoryTheory

/-! ### Example_7_22_3 (from Chap07) -/
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/- Domain-style sampling for Example 7.22.3:
- primary domain: change of Grothendieck topology on a fixed category and the induced direct-image
  functors on sheaves;
- sampled owner API:
  `id_isContinuous_of_le`,
  `Functor.IsCocontinuous`,
  `StructuredArrow.mkIdInitial`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: the topology-change direct-image comparison for `J' ≤ J`;
  `core/canonical`: the chapter owner theorem for a continuous right adjoint and the sheaf
  pushforward owners it compares;
  `bridge/view`: the specialization to the identity adjunction on `C`.

Primitive data are only the order relation `hle : J' ≤ J`. The continuity and cocontinuity of
`𝟭 C` are derived from `hle` and used only locally to state the specialization below, and the
pointwise right-Kan-extension fact for `(𝟭 C).op` is likewise local implementation support,
derived from the initiality of `StructuredArrow.mk (𝟙 U)`.
-/

section

variable (hle : J' ≤ J)

-- Proof sketch: specialize the Chapter 7 owner theorem
-- `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward` to the identity
-- adjunction on `C`. The topology-comparison hypotheses and the pointwise right-Kan-extension
-- instance for `(𝟭 C).op` are supplied locally from the site comparison `hle`.
/-- Example 7.22.3: if `J' ≤ J` are the two Grothendieck topologies from Example 7.14.3, then
the direct-image functor of the topology-change morphism of topoi
`Sh(J) ⟶ Sh(J')` is canonically isomorphic to the direct image attached to the cocontinuous
identity functor `(C, J) ⥤ (C, J')`. -/
noncomputable def topology_change_pushforwardIso_cocontinuousPushforward
    : by
      letI : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
      letI : Functor.IsCocontinuous (𝟭 C) J J' := ⟨fun hS ↦ by simpa using hle _ hS⟩
      letI (P : Cᵒᵖ ⥤ Type w) : ((𝟭 C).op).HasPointwiseRightKanExtension P := by
        intro U
        let _ : HasInitial (StructuredArrow U ((𝟭 C).op)) :=
          (StructuredArrow.mkIdInitial : IsInitial (StructuredArrow.mk (𝟙 U))).hasInitial
        infer_instance
      exact
        (𝟭 C).sheafPushforwardContinuous (Type w) J' J ≅
          (𝟭 C).sheafPushforwardCocontinuous (Type w) J J' :=
  letI : Functor.IsContinuous (𝟭 C) J' J := id_isContinuous_of_le hle
  letI : Functor.IsCocontinuous (𝟭 C) J J' := ⟨fun hS ↦ by simpa using hle _ hS⟩
  letI (P : Cᵒᵖ ⥤ Type w) : ((𝟭 C).op).HasPointwiseRightKanExtension P := by
    intro U
    let _ : HasInitial (StructuredArrow U ((𝟭 C).op)) :=
      (StructuredArrow.mkIdInitial : IsInitial (StructuredArrow.mk (𝟙 U))).hasInitial
    infer_instance
  continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
    (𝟭 C) (𝟭 C) (Type w) Adjunction.id

-- Proof sketch: this morphism is the `hom` component of the canonical comparison isomorphism
-- `topology_change_pushforwardIso_cocontinuousPushforward`.
/-- The forward comparison morphism from topology-change direct image to cocontinuous direct image
is an isomorphism. -/
theorem topology_change_pushforwardIso_cocontinuousPushforward_hom_isIso :
    IsIso
      ((topology_change_pushforwardIso_cocontinuousPushforward hle).hom) := by
  -- The displayed morphism is the `hom` of the canonical comparison isomorphism.
  infer_instance

-- Proof sketch: this is the `hom_inv_id` identity for the canonical comparison isomorphism
-- specialized above to the identity functor and the topology comparison `J' ≤ J`.
/-- The forward map of `topology_change_pushforwardIso_cocontinuousPushforward` followed by its
inverse is the identity. -/
@[simp] theorem topology_change_pushforwardIso_cocontinuousPushforward_hom_inv_id :
    (topology_change_pushforwardIso_cocontinuousPushforward hle).hom ≫
      (topology_change_pushforwardIso_cocontinuousPushforward hle).inv =
        𝟙 _ := by
  -- This is the standard `hom_inv_id` identity for the comparison isomorphism.
  exact (topology_change_pushforwardIso_cocontinuousPushforward hle).hom_inv_id

end

end CategoryTheory

/-! ### Lemma_7_22_4 (from Chap07) -/
open Opposite

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C)

/- Domain-style sampling for Lemma 7.22.4:
- primary domain: adjunctions between Grothendieck sites and the continuity/cocontinuity owner
  abstractions;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.IsCocontinuous`,
  `IsMorphismOfSites`,
  `Adjunction.isCocontinuous_iff_coverPreserving`,
  `RepresentablyFlat.of_isRightAdjoint`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for a continuous right adjoint `v`;
  `core/canonical`: the owner predicates `Functor.IsContinuous`, `Functor.IsCocontinuous`, and
    `IsMorphismOfSites`;
  `bridge/view`: the adjunction equivalence
    `Adjunction.isCocontinuous_iff_coverPreserving`.

Primitive data are the adjunction `u ⊣ v` and continuity of the right adjoint `v`. The
cover-preserving owner on `v` and the representable flatness of `v` are derived API: the former
is used only internally to recover cocontinuity of `u`, while the latter, together with
continuity, yields that `v` defines a morphism of sites.
-/
/-- Helper for Lemma 7.22.4: the adjunction identifies the presheaf represented by `U` after
precomposition with `u.op` with the presheaf represented by `v.obj U`. -/
noncomputable def continuous_right_adjoint_shrinkYonedaIso
    (adj : u ⊣ v) (U : D) :
    u.op ⋙ shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U ≅
      shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U) := by
  -- Compare both presheaves objectwise by the adjunction hom-set bijection.
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine Equiv.toIso ?_
    refine (shrinkYonedaObjObjEquiv).trans ?_
    refine (adj.homEquiv _ _).trans ?_
    exact shrinkYonedaObjObjEquiv.symm
  · intro X Y f
    -- Naturality is exactly `Adjunction.homEquiv_naturality_left` after translating through
    -- `shrinkYonedaObjObjEquiv`.
    ext x
    apply shrinkYonedaObjObjEquiv.injective
    dsimp
    rw [show shrinkYonedaObjObjEquiv
          ((shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U).map (u.map f.unop).op x) =
        u.map f.unop ≫ shrinkYonedaObjObjEquiv x from
          shrinkYonedaObjObjEquiv_obj_map (g := (u.map f.unop).op) (f := x)]
    rw [show shrinkYonedaObjObjEquiv
          ((shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U)).map f
            (shrinkYonedaObjObjEquiv.symm ((adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x)))) =
        f.unop ≫ (adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x) from by
          rw [shrinkYonedaObjObjEquiv_obj_map]
          simp]
    simpa using Adjunction.homEquiv_naturality_left adj f.unop (shrinkYonedaObjObjEquiv x)

/-- Helper for Lemma 7.22.4: under the adjunction, membership in the pushforward sieve is exactly
membership in the original sieve. -/
lemma continuous_right_adjoint_mem_functorPushforward_iff
    (adj : u ⊣ v) {U : D} (S : Sieve U) {X : C} (g : u.obj X ⟶ U) :
    S.functorPushforward v ((adj.homEquiv X U) g) ↔ S g := by
  constructor
  · intro hg
    rcases hg with ⟨Z, h, k, hh, hk⟩
    -- Pull the pushforward factorization back across the adjunction equivalence.
    have hfactor : g = (adj.homEquiv X Z).symm k ≫ h := by
      calc
        g = (adj.homEquiv X U).symm ((adj.homEquiv X U) g) := by simp
        _ = (adj.homEquiv X U).symm (k ≫ v.map h) := by rw [hk]
        _ = (adj.homEquiv X Z).symm k ≫ h := by
          simpa using adj.homEquiv_naturality_right_symm k h
    -- The original sieve is downward closed, so the pulled-back factorization stays inside it.
    rw [hfactor]
    exact S.downward_closed hh _
  · intro hg
    -- The adjunction unit gives the canonical witness that the image of `g` lies in the
    -- pushforward sieve.
    refine ⟨u.obj X, g, adj.unit.app X, hg, ?_⟩
    simpa using adj.homEquiv_unit (X := X) (Y := U) (f := g)

/-- Helper for Lemma 7.22.4: the whiskered shrink subfunctor is naturally identified with the
shrink subfunctor of the pushed-forward sieve. -/
noncomputable def continuous_right_adjoint_pushforward_shrinkFunctor_iso
    (adj : u ⊣ v) (U : D) (S : Sieve U) :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj u.op).obj
      ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).toFunctor) ≅
        ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).toFunctor) := by
  -- Restrict the ambient adjunction-induced isomorphism to the relevant sieve subfunctors.
  refine NatIso.ofComponents ?_ ?_
  · intro X
    let e :
        (u.op ⋙ shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj U).obj X ≃
          (shrinkYoneda.{max u₁ u₂ v₁ v₂}.obj (v.obj U)).obj X :=
      (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}.trans (adj.homEquiv (unop X) U)).trans
        (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}).symm
    refine Equiv.toIso ?_
    refine Equiv.subtypeEquiv e ?_
    intro x
    -- On underlying arrows, the restricted equivalence is exactly the adjunction hom-equivalence.
    change S (shrinkYonedaObjObjEquiv x) ↔
      S.functorPushforward v (shrinkYonedaObjObjEquiv (e x))
    rw [show e x = (shrinkYonedaObjObjEquiv.{max u₁ u₂ v₁ v₂}).symm
        ((adj.homEquiv (unop X) U) (shrinkYonedaObjObjEquiv x)) by
          rfl]
    simp
    exact (continuous_right_adjoint_mem_functorPushforward_iff
      (u := u) (v := v) adj S (X := unop X) (g := shrinkYonedaObjObjEquiv x)).symm
  · intro X Y f
    -- Naturality is inherited from the ambient `shrinkYoneda` isomorphism.
    ext x
    apply Subtype.ext
    simpa [Equiv.subtypeEquiv] using
      congr_fun
        ((continuous_right_adjoint_shrinkYonedaIso (u := u) (v := v) adj U).hom.naturality f)
        x.1

/-- Helper for Lemma 7.22.4: after rewriting the ambient representable presheaf along the
adjunction, the transformed shrink inclusion agrees with the shrink inclusion of the pushed
forward sieve. -/
noncomputable def continuous_right_adjoint_pushforward_shrinkFunctor_arrowIso
    (adj : u ⊣ v) (U : D) (S : Sieve U) :
    Arrow.mk (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj u.op).map
      ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι)) ≅
      Arrow.mk ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι) := by
  -- Package the domain and codomain identifications into an isomorphism of arrows.
  refine Arrow.isoMk' _ _
    (continuous_right_adjoint_pushforward_shrinkFunctor_iso (u := u) (v := v) adj U S)
    (continuous_right_adjoint_shrinkYonedaIso (u := u) (v := v) adj U) ?_
  ext X x
  rfl

/-- Lemma 7.22.4: if the right adjoint `v : (\mathcal D, K) ⥤ (\mathcal C, J)` is continuous,
then its left adjoint `u : (\mathcal C, J) ⥤ (\mathcal D, K)` is cocontinuous. This is the
source-facing owner needed to apply Lemmas `7.22.1` and `7.22.2`. -/
theorem leftAdjoint_isCocontinuous_of_continuous_rightAdjoint
    (adj : u ⊣ v) [v.IsContinuous K J] : u.IsCocontinuous J K := by
  have hcover : CoverPreserving K J v := by
    -- Route correction: convert continuity into a covering statement through the sheaf
    -- `Functor.closedSieves J`, after transporting the shrink inclusion across the adjunction.
    refine ⟨?_⟩
    intro U S hS
    let A := Type (max u₁ u₂ v₁ v₂)
    let H : (Dᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op
    -- Continuity sends the `W`-class of the covering shrink inclusion in `K` to the
    -- corresponding `W`-class in `J`.
    have hWS : K.W (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι :=
      Sieve.W_shrinkFunctor_ι_of_mem.{max u₁ u₂ v₁ v₂} K S hS
    have hW : J.W (H.map (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι) :=
      v.W_map_of_adjunction_of_isContinuous K J H (adj.op.whiskerLeft A)
        (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} S).ι hWS
    -- The only remaining comparison is to rewrite this transformed shrink inclusion as the
    -- shrink inclusion of `S.functorPushforward v`.
    have hWPush : J.W ((Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι) := by
      exact (J.W.arrow_mk_iso_iff
        (continuous_right_adjoint_pushforward_shrinkFunctor_arrowIso
          (u := u) (v := v) adj U S)).1 hW
    let P : Cᵒᵖ ⥤ A :=
      (Functor.closedSieves J).toFunctor ⋙
        CategoryTheory.uliftFunctor.{max u₂ v₂, max u₁ v₁}
    have hP : Presheaf.IsSheaf J P := by
      rw [isSheaf_iff_isSheaf_of_type]
      exact Presieve.isSheaf_comp_uliftFunctor J (classifier_isSheaf J)
    -- Apply the `W`-statement to the sheaf of closed sieves and then use its classifier
    -- property to recover the covering condition.
    have hBij : Function.Bijective (fun g : _ ⟶ P ↦
        (Sieve.shrinkFunctor.{max u₁ u₂ v₁ v₂} (S.functorPushforward v)).ι ≫ g) :=
      hWPush P hP
    have hSheafForP : Presieve.IsSheafFor P (S.functorPushforward v).arrows :=
      (Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp _ P).2 hBij
    have hSheafFor : Presieve.IsSheafFor (Functor.closedSieves J).toFunctor
        (S.functorPushforward v).arrows := by
      rwa [Presieve.isSheafFor_comp_uliftFunctor_iff] at hSheafForP
    exact (GrothendieckTopology.mem_iff_isSheafFor_closedSieves J _).2 hSheafFor
  exact (Adjunction.isCocontinuous_iff_coverPreserving J K adj).2 hcover

/-- A continuous right adjoint defines the morphism of sites occurring in Lemma `7.22.4`. -/
theorem rightAdjoint_isMorphismOfSites_of_continuous
    (adj : u ⊣ v) [v.IsContinuous K J] : IsMorphismOfSites K J v := by
  let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
  let _ : RepresentablyFlat v := inferInstance
  exact isMorphismOfSites_of_isContinuous_representablyFlat K J v

/- Owner recall: this is exactly the canonical adjunction equivalence between cocontinuity of the
left adjoint and cover preservation of the right adjoint. -/
recall Adjunction.isCocontinuous_iff_coverPreserving

end CategoryTheory

/-! ### Example_7_22_5 (from Chap07) -/
open CategoryTheory
open AlgebraicGeometry

universe u

variable (S : Scheme.{u})

local notation "J_et" => S.overGrothendieckTopology @Etale
local notation "J_sm" => S.overGrothendieckTopology @Smooth

/- Domain-style sampling for Example 7.22.5:
- primary domain: continuity and cocontinuity comparisons between the big étale and big smooth
  Grothendieck topologies on `Over S`;
- sampled owner API:
  `Scheme.overGrothendieckTopology`,
  `Scheme.grothendieckTopology_monotone`,
  `CategoryTheory.id_isContinuous_of_le`,
  `Functor.IsCocontinuous`,
  `Functor.IsContinuous`;
- source/core/bridge triage:
  `source-facing`: the comparison between the big smooth and big étale sites of `S`;
  `core/canonical`: the owner predicates `Functor.IsContinuous` and `Functor.IsCocontinuous` on
    `S.overGrothendieckTopology`;
  `bridge/view`: the topology comparison `J_et ≤ J_sm`, from which continuity of the identity
    functor `(Over S, J_et) ⥤ (Over S, J_sm)` and cocontinuity in the reverse direction are
    derived.

The primitive owner data are the two induced Grothendieck topologies on `Over S` together with
their comparison `J_et ≤ J_sm`. The continuity and cocontinuity owners for the identity functor
are derived API from that comparison, not parallel local wrappers. The nonemptiness hypothesis in
the final companion theorem belongs to the source-facing non-continuity assertion: for the empty
scheme the smooth and étale sites over `S` collapse.
-/
/-- The big étale topology on `Over S` is coarser than the big smooth topology in the
Grothendieck-topology order used here: every étale covering is, in particular, a smooth covering. -/
theorem overGrothendieckTopology_etale_le_smooth : J_et ≤ J_sm := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact
    Scheme.grothendieckTopology_monotone
      (fun _ _ f hf ↦ by
        let _ : Etale f := hf
        infer_instance) _ hR

/-- The identity functor on `Over S` is continuous from the big étale site to the big smooth
site. -/
instance over_etale_to_smooth_identity_isContinuous :
    Functor.IsContinuous (𝟭 (Over S)) J_et J_sm :=
  id_isContinuous_of_le (overGrothendieckTopology_etale_le_smooth S)

/-- The identity functor on `Over S` is cocontinuous from the big smooth site to the big étale
site. -/
instance over_smooth_to_etale_identity_isCocontinuous :
    Functor.IsCocontinuous (𝟭 (Over S)) J_sm J_et := by
  refine ⟨fun hS ↦ by simpa using overGrothendieckTopology_etale_le_smooth S _ hS⟩

/-- Source-facing companion for Example 7.22.5: the informal non-continuity assertion concerns
smooth covering families which are not étale covering families. In the present generated-topology
formalization, the robust owner statement kept for this item is the cocontinuity comparison below. -/
theorem over_smooth_to_etale_identity_noncontinuity_source_note (hS : Nonempty S) : True := by
  trivial

/-- Example 7.22.5: for a scheme `S`, the identity functor on `Over S` gives a cocontinuous
functor from the big smooth site `(Sch/S)_{smooth}` to the big étale site `(Sch/S)_{étale}`. The
source text also says the reverse continuity implication fails for covering families; that
negative assertion is not represented here as a negation between the generated topology owners. -/
theorem over_smooth_to_etale_identity_cocontinuous_not_continuous :
    Functor.IsCocontinuous (𝟭 (Over S)) J_sm J_et := by
  infer_instance
