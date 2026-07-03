import Mathlib
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_21_1 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.21.1:
- primary domain: morphisms of topoi induced by cocontinuous functors of sites;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `Functor.sheafPullbackCocontinuous_exact`;
- source-facing layer: the cocontinuous-functor specialization producing a morphism
  `Sh(J) ⟶ Sh(K)`;
- core/canonical owner: `MorphismOfTopoiIn`, with constructor style already set by
  `Functor.morphismOfTopoiInOfContinuous`;
- bridge/view: the simp lemmas identifying `g_*` and `g⁻¹` with the cocontinuous
  pushforward/pullback functors.

Primitive data are just the cocontinuous functor and the sheafification/right-Kan-extension
hypotheses. The adjunction and left exactness are derived from the owner declarations in
Lemma 7.20.3, so the public API should reuse those rather than restating them as separate local
data.
-/

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsCocontinuous J K] [HasSheafify J (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension P]

/-- Lemma 7.21.1: a cocontinuous functor of sites `u : C ⥤ D` determines a morphism of topoi
`g : Sh(J) ⟶ Sh(K)` whose direct image is `u.sheafPushforwardCocontinuous` and whose inverse
image is the sheafified pullback `u.sheafPullbackCocontinuous J K`. -/
def morphismOfTopoiInOfCocontinuous
    : MorphismOfTopoiIn K J where
  inverseImageFunctor :=
    (LeftExactFunctor.ofExact (Sheaf K (Type w)) (Sheaf J (Type w))).obj <|
      let _ : PreservesFiniteLimits (u.sheafPullbackCocontinuous (Type w) J K) :=
        (u.sheafPullbackCocontinuous_exact J K).1
      let _ : PreservesFiniteColimits (u.sheafPullbackCocontinuous (Type w) J K) :=
        (u.sheafPullbackCocontinuous_exact J K).2
      ExactFunctor.of (u.sheafPullbackCocontinuous (Type w) J K)
  pushforward := u.sheafPushforwardCocontinuous (Type w) J K
  adjunction := u.sheafPullbackCocontinuousAdjunction J K

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; the direct-image field was defined to
-- be `u.sheafPushforwardCocontinuous (Type w) J K`.
/-- The direct-image functor of `morphismOfTopoiInOfCocontinuous` is the cocontinuous sheaf
pushforward functor. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_pushforward :
    (u.morphismOfTopoiInOfCocontinuous J K) _* =
      u.sheafPushforwardCocontinuous (Type w) J K := rfl

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; the inverse-image field was defined to
-- be `u.sheafPullbackCocontinuous J K`.
/-- The inverse-image functor of `morphismOfTopoiInOfCocontinuous` is the sheafified inverse-image
functor attached to the cocontinuous functor. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_inverseImage :
    (u.morphismOfTopoiInOfCocontinuous J K)⁻¹ =
      u.sheafPullbackCocontinuous (Type w) J K := by
  -- The inverse-image notation is the stored left-exact functor, so this is definitional.
  rfl

-- Proof sketch: unfold `morphismOfTopoiInOfCocontinuous`; its `adjunction` field was defined to
-- be `u.sheafPullbackCocontinuousAdjunction J K`.
/-- The cocontinuous morphism of topoi is defined using the canonical adjunction between the
sheafified pullback and pushforward functors. -/
theorem morphismOfTopoiInOfCocontinuous_spec :
    (u.morphismOfTopoiInOfCocontinuous J K).adjunction =
      u.sheafPullbackCocontinuousAdjunction J K := by
  -- The adjunction field was assigned directly in the defining structure.
  rfl

end CategoryTheory.Functor

/-! ### Lemma_7_21_2 (from Chap07) -/
open CategoryTheory Opposite

universe t u₁ u₂ u₃ v₁ v₂ v₃

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
variable (u : C ⥤ D) (v : D ⥤ E)
variable [Functor.IsCocontinuous u J K] [Functor.IsCocontinuous v K L]

/- Domain-style sampling for Lemma 7.21.2:
- primary domain: cocontinuous functors between sites and their induced direct-image functors on
  sheaf categories;
- sampled owner API:
  `CategoryTheory.isCocontinuous_comp`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the textbook statement that direct images for cocontinuous functors compose;
  `core/canonical`: `Functor.sheafPushforwardCocontinuous` for `A`-valued sheaves;
  `bridge/view`: the composition isomorphism for that owner, parallel to the continuous-side
  owner theorem in mathlib.

Primitive data are just the cocontinuous functors and the right Kan extension hypotheses for
`A`-valued presheaves. The composition isomorphism is derived API from that owner abstraction, so
the public statement should live at the owner level for arbitrary coefficients `A`, not only at the
specialization `A = Type t`.
-/

/- Lemma 7.21.2: the composite of two cocontinuous functors between sites is again
cocontinuous. -/
recall CategoryTheory.isCocontinuous_comp

namespace CategoryTheory.Functor

section

variable {A : Type t} [Category A]
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
variable [∀ F : Dᵒᵖ ⥤ A, v.op.HasPointwiseRightKanExtension F]

/-- A natural isomorphism between cocontinuous functors of sites induces the corresponding
isomorphism between their sheaf pushforward functors. This is the cocontinuous analogue of
`Functor.sheafPushforwardContinuousIso`. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousIso
    {u' : C ⥤ D} (e : u ≅ u')
    [u'.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ A, u'.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ≅
      u'.sheafPushforwardCocontinuous A J K := by
  let ranIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ≅
        (u'.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) :=
    ((u.op.ranAdjunction A).ofNatIsoLeft
        ((whiskeringLeft _ _ _).mapIso (NatIso.op e.symm))).rightAdjointUniq
      (u'.op.ranAdjunction A)
  let uPush := u.sheafPushforwardCocontinuous A J K
  let u'Push := u'.sheafPushforwardCocontinuous A J K
  let presheafIso :
      uPush ⋙ sheafToPresheaf K A ≅
        u'Push ⋙ sheafToPresheaf K A :=
    calc
      uPush ⋙ sheafToPresheaf K A ≅ sheafToPresheaf J A ⋙ u.op.ran :=
        u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K
      _ ≅ sheafToPresheaf J A ⋙ u'.op.ran :=
        isoWhiskerLeft _ ranIso
      _ ≅ u'Push ⋙ sheafToPresheaf K A :=
        (u'.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf K A) presheafIso

/-- The cocontinuous sheaf pushforward attached to a composite is the composite of the
cocontinuous sheaf pushforwards attached to the factors. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousComp
    [∀ F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        (letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
         (u ⋙ v).sheafPushforwardCocontinuous A J L) := by
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  let uPush := u.sheafPushforwardCocontinuous A J K
  let vPush := v.sheafPushforwardCocontinuous A K L
  let uvPush := (u ⋙ v).sheafPushforwardCocontinuous A J L
  let ranCompIso :
      (u.op.ran : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) ⋙ (v.op.ran : (Dᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) ≅
        ((u ⋙ v).op.ran : (Cᵒᵖ ⥤ A) ⥤ Eᵒᵖ ⥤ A) :=
    (((v.op.ranAdjunction A).comp (u.op.ranAdjunction A)).ofNatIsoLeft
      (whiskeringLeftObjCompIso u.op v.op).symm).rightAdjointUniq
      ((u ⋙ v).op.ranAdjunction A)
  let presheafIso :
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
        uvPush ⋙ sheafToPresheaf L A :=
    calc
      (uPush ⋙ vPush) ⋙ sheafToPresheaf L A ≅
          uPush ⋙ (vPush ⋙ sheafToPresheaf L A) :=
        Functor.associator _ _ _
      _ ≅ uPush ⋙ (sheafToPresheaf K A ⋙ v.op.ran) :=
        isoWhiskerLeft _ (v.sheafPushforwardCocontinuousCompSheafToPresheafIso A K L)
      _ ≅ (uPush ⋙ sheafToPresheaf K A) ⋙ v.op.ran :=
        (Functor.associator _ _ _).symm
      _ ≅ (sheafToPresheaf J A ⋙ u.op.ran) ⋙ v.op.ran :=
        isoWhiskerRight (u.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K) _
      _ ≅ sheafToPresheaf J A ⋙ (u.op.ran ⋙ v.op.ran) :=
        Functor.associator _ _ _
      _ ≅ sheafToPresheaf J A ⋙ (u ⋙ v).op.ran :=
        isoWhiskerLeft _ ranCompIso
      _ ≅ uvPush ⋙ sheafToPresheaf L A :=
        (u ⋙ v).sheafPushforwardCocontinuousCompSheafToPresheafIso A J L |>.symm
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf L A) presheafIso

/-- If `u ⋙ v` is identified with another cocontinuous functor `uv`, then the composite of the
cocontinuous sheaf pushforwards for `u` and `v` identifies with the cocontinuous sheaf
pushforward for `uv`. This is the cocontinuous analogue of
`Functor.sheafPushforwardContinuousComp'`. -/
@[simps!]
noncomputable def sheafPushforwardCocontinuousComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [uv.IsCocontinuous J L]
    [∀ F : Cᵒᵖ ⥤ A, uv.op.HasPointwiseRightKanExtension F] :
    u.sheafPushforwardCocontinuous A J K ⋙
      v.sheafPushforwardCocontinuous A K L ≅
        uv.sheafPushforwardCocontinuous A J L := by
  letI : Functor.IsCocontinuous (u ⋙ v) J L := isCocontinuous_comp u v J K
  letI : ∀ F : Cᵒᵖ ⥤ A, (u ⋙ v).op.HasPointwiseRightKanExtension F := by
    intro F Y
    rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso F (NatIso.op euv) Y]
    infer_instance
  exact sheafPushforwardCocontinuousComp J K L u v ≪≫
    sheafPushforwardCocontinuousIso J L (u ⋙ v) euv

end

section

variable {A : Type t} [Category A]
variable [Functor.IsContinuous u J K] [Functor.IsContinuous v K L]
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]
variable [∀ F : Dᵒᵖ ⥤ A, v.op.HasLeftKanExtension F]
variable [HasWeakSheafify K A] [HasWeakSheafify L A]

/-- The sheaf pullback attached to a composite of continuous functors is canonically the
composite of the corresponding sheaf pullbacks. This is the left-adjoint mate of
`Functor.sheafPushforwardContinuousComp'`. -/
@[simps!]
noncomputable def sheafPullbackComp'
    {uv : C ⥤ E} (euv : u ⋙ v ≅ uv)
    [Functor.IsContinuous uv J L]
    [∀ F : Cᵒᵖ ⥤ A, uv.op.HasLeftKanExtension F] :
    u.sheafPullback A J K ⋙ v.sheafPullback A K L ≅
      uv.sheafPullback A J L :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        (u.sheafAdjunctionContinuous A J K)
        (v.sheafAdjunctionContinuous A K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' euv A J K L))
    (uv.sheafAdjunctionContinuous A J L)

end

end CategoryTheory.Functor

end

/-! ### Example_7_21_3 (from Chap07) -/
open CategoryTheory
open TopologicalSpace
open TopCat

noncomputable section

universe u

/- Domain-style sampling for Example 7.21.3:
- primary domain: sheaf functors attached to the inclusion of an open subspace;
- sampled owner API:
  `Topology.IsOpenEmbedding.functor_isContinuous`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`,
  `IsOpenMap.cocontinuousPushforwardIsoSheafPushforward`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: compare the sheaf functors induced by the open-subspace site functor with the
  usual restriction `j⁻¹` and direct image `j_*` for `j : U ↪ X`;
  `core/canonical`: `Topology.IsOpenEmbedding.sheafPullbackIso` for the inverse-image side and the
  Chapter 7 owner
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward` for the
  direct-image side;
  `bridge/view`: the specialization from the inclusion `Opens.inclusion' U` to those owners, in
  particular the owner-scoped open-map comparison
  `IsOpenMap.cocontinuousPushforwardIsoSheafPushforward`.

Primitive data are only the open `U` and the opens adjunction
`(Opens.isOpenEmbedding U).functor ⊣ Opens.map (Opens.inclusion' U)`. The inverse-image and
direct-image comparisons are derived owner specializations, so this file should reuse those owners
and the existing owner-scoped open-map specialization directly rather than keep parallel local comparison
isomorphisms.
-/

section

variable {X : TopCat.{u}} (U : Opens X)

/- Companion recall: the continuity of the open-subspace functor is already the canonical owner
`Topology.IsOpenEmbedding.functor_isContinuous`. -/
recall Topology.IsOpenEmbedding.functor_isContinuous

/- Companion recall: the inverse-image comparison for an open embedding is already the canonical
owner `Topology.IsOpenEmbedding.sheafPullbackIso`. -/
recall Topology.IsOpenEmbedding.sheafPullbackIso

/- Example 7.21.3, inverse-image side: for the inclusion `j : U ↪ X`, the inverse-image functor
coming from the open-subspace site functor is the inverse of the canonical open-embedding
pullback isomorphism. -/
#check
  ((Opens.isOpenEmbedding U).sheafPullbackIso (Type u)).symm

/- Companion recall: the direct-image comparison for a continuous right adjoint is owned by the
Chapter 7 theorem
`continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`. -/
recall continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward

/- Companion recall: the owner-scoped open-map specialization already packages the direct-image
comparison in the source-facing form used here. -/
recall IsOpenMap.cocontinuousPushforwardIsoSheafPushforward

/- Example 7.21.3, direct-image side: the cocontinuous pushforward attached to the open-subspace
functor agrees with the usual direct image `j_*`. -/
#check
  (Opens.isOpenEmbedding U).isOpenMap.cocontinuousPushforwardIsoSheafPushforward

end

/-! ### Example_7_21_4 (from Chap07) -/
open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe w

/- Domain-style sampling for Example 7.21.4:
- primary domain: open maps of topological spaces, the induced adjunction on categories of opens,
  and the corresponding direct-image functors on sheaves of sets;
- sampled owner API:
  `IsOpenMap.adjunction`,
  `IsOpenMap.coverPreserving`,
  `Adjunction.isCocontinuous_iff_coverPreserving`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`;
- source/core/bridge triage:
  `source-facing`: the open-map specialization comparing the direct image coming from
  `hf.functor : Opens X ⥤ Opens Y` with the usual sheaf pushforward along `f`;
  `core/canonical`: the opens adjunction `hf.functor ⊣ Opens.map f` and the Chapter 7 comparison
  owner for a continuous right adjoint;
  `bridge/view`: the specialization below from those owners to the open-map setting.

Primitive data are only the map `f` and the proof `hf : IsOpenMap f`. The cocontinuity of
`hf.functor` and the comparison with `TopCat.Sheaf.pushforward` are derived from the canonical
owners above, so this file should expose only the thin specialization layer rather than a parallel
local construction.
-/

namespace IsOpenMap

variable {X Y : TopCat.{w}} {f : X ⟶ Y}

/-- An open map induces a cocontinuous functor on the categories of opens. -/
instance functor_isCocontinuous (hf : IsOpenMap f) :
    hf.functor.IsCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  (Adjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) hf.adjunction).2
    (coverPreserving_opens_map f)

/-- Example 7.21.4: for an open map `f : X ⟶ Y`, the direct-image functor on sheaves of sets
arising from the cocontinuous functor `U ↦ f(U)` agrees with the usual sheaf pushforward along
`f`. -/
-- Proof sketch: use the adjunction `hf.functor ⊣ Opens.map f` on opens, identify cocontinuity of
-- `hf.functor` via the cover-preserving property of `Opens.map f`, and then compare the resulting
-- right Kan extension description of the cocontinuous pushforward with the standard pushforward by
-- precomposition along `Opens.map f`.
noncomputable def cocontinuousPushforwardIsoSheafPushforward (hf : IsOpenMap f) :
    hf.functor.sheafPushforwardCocontinuous (Type w)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ≅
        TopCat.Sheaf.pushforward (Type w) f :=
  (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      hf.functor (Opens.map f) (Type w) hf.adjunction).symm

-- Proof sketch: unfold the definition and observe that the only extra input is the canonical
-- cocontinuity instance `functor_isCocontinuous hf`, so the comparison isomorphism is exactly the
-- specialization of the Chapter 7 continuous-right-adjoint owner theorem.
/-- The open-map comparison isomorphism is the specialization of the continuous-right-adjoint
comparison theorem to the adjunction `hf.functor ⊣ Opens.map f`. -/
theorem cocontinuousPushforwardIsoSheafPushforward_def (hf : IsOpenMap f) :
    cocontinuousPushforwardIsoSheafPushforward hf =
      (continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
        hf.functor (Opens.map f) (Type w) hf.adjunction).symm := by
  -- The specialization was defined to be exactly this symmetric owner isomorphism.
  rfl

-- Proof sketch: this is the `hom_inv_id` identity for the comparison isomorphism defined above.
/-- The forward map of `cocontinuousPushforwardIsoSheafPushforward` followed by its inverse is the
identity. -/
@[simp] theorem cocontinuousPushforwardIsoSheafPushforward_hom_inv_id (hf : IsOpenMap f) :
    (cocontinuousPushforwardIsoSheafPushforward hf).hom ≫
        (cocontinuousPushforwardIsoSheafPushforward hf).inv =
      𝟙 _ := by
  -- This is the standard `hom_inv_id` identity for the comparison isomorphism.
  exact (cocontinuousPushforwardIsoSheafPushforward hf).hom_inv_id

end IsOpenMap

/-! ### Lemma_7_21_5 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe t u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/- Domain-style sampling for Lemma 7.21.5:
- primary domain: the continuous sheaf functor on set-valued sheaves induced by precomposition
  with `u.op`, together with its left adjoint from sheafified left Kan extension and, in the
  cocontinuous case, its right adjoint given by cocontinuous sheaf pushforward;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks functor on sheaves obtained from precomposition with `u.op`, its
  left adjoint `g_!`, and the fact that this functor commutes with arbitrary limits and colimits
  once both adjunctions are available;
  `core/canonical`: the owner central to this file is
  `u.sheafPushforwardContinuous (Type t) J K`; separately, Lemma 7.21.1 packages a cocontinuous
  morphism of topoi whose inverse-image owner is
  `u.sheafPullbackCocontinuous (Type t) J K`, so these two owner packages must not be conflated;
  `bridge/view`: `u.sheafPushforwardContinuousCompSheafToPresheafIso` identifies the underlying
  presheaf of the continuous sheaf functor, `u.sheafPullbackConstruction.sheafAdjunctionContinuous
  (Type t) J K` gives its left adjoint, and `u.sheafAdjunctionCocontinuous (Type t) J K` gives
  the same functor as a left adjoint to the cocontinuous direct image.

Primitive data are the site functor `u`, continuity for the continuous owner, and the
cocontinuity/Kan-extension hypotheses only where the direct-image side is needed. The comparison
isomorphism and the limit/colimit-preservation facts are derived API. In particular, clause `(3)`
should be phrased on the continuous owner `u.sheafPushforwardContinuous (Type t) J K` through its
`IsRightAdjoint` and `IsLeftAdjoint` structures, rather than by identifying it with the
inverse-image field of `u.morphismOfTopoiInOfCocontinuous J K` or introducing a parallel local
wrapper. -/

/- Lemma 7.21.5 (1): the continuous sheaf functor attached to a functor of sites `u`, realized in
Lean by `u.sheafPushforwardContinuous (Type t) J K`, is already given on underlying presheaves by
precomposition with `u.op`, so no further sheafification is needed. The recalled owner itself only
uses the continuous half of the hypotheses. -/
recall Functor.sheafPushforwardContinuousCompSheafToPresheafIso

/- Lemma 7.21.5 (2): the source-facing left adjoint `g_!` to this continuous sheaf functor is
realized by the sheafified left Kan extension along `u.op`. The recalled owner is the adjunction
between that construction and `u.sheafPushforwardContinuous (Type t) J K`. -/
recall Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

/- Lemma 7.21.5 (3): in the cocontinuous case, the canonical adjunction
`u.sheafAdjunctionCocontinuous (Type t) J K` exhibits the same continuous owner
`u.sheafPushforwardContinuous (Type t) J K` as left adjoint to the cocontinuous direct-image
functor `u.sheafPushforwardCocontinuous (Type t) J K`. This is the second adjunction carried by
the continuous owner; it should not be identified with the inverse-image field of
`u.morphismOfTopoiInOfCocontinuous J K`, whose owner is instead
`u.sheafPullbackCocontinuous (Type t) J K`. The main entry here therefore recalls the adjunction
owner itself rather than repackaging its `IsLeftAdjoint` view as a parallel local declaration. -/
recall Functor.sheafAdjunctionCocontinuous

section RightAdjoint

variable [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous (Type t) J K).IsRightAdjoint]

/- Lemma 7.21.5 (3), limit part: once the source-facing left adjoint `g_!` from clause `(2)` is
constructed, the continuous owner `u.sheafPushforwardContinuous (Type t) J K` commutes with
arbitrary limits because it is a right adjoint. This is the generic owner-level instance induced
by `Adjunction.rightAdjoint_preservesLimits`, so no parallel local theorem is kept here. -/
#synth PreservesLimits (u.sheafPushforwardContinuous (Type t) J K)

end RightAdjoint

section LeftAdjoint

variable [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous (Type t) J K).IsLeftAdjoint]

/- Lemma 7.21.5 (3), colimit part: when the same continuous owner
`u.sheafPushforwardContinuous (Type t) J K` carries the left-adjoint structure supplied in the
cocontinuous case by `u.sheafAdjunctionCocontinuous (Type t) J K`, it commutes with arbitrary
colimits as well. This is the generic owner-level instance induced by
`Adjunction.leftAdjoint_preservesColimits`, so no parallel local theorem is kept here. -/
#synth PreservesColimits (u.sheafPushforwardContinuous (Type t) J K)

end LeftAdjoint

end
