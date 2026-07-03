import Mathlib
import StacksProject_2024.Chap06.Definition_6_15_1
import StacksProject_2024.Chap06.Glueing_data_for_sheaves_on_an_open_cover
import StacksProject_2024.Chap06.Lemma_6_21_6
import StacksProject_2024.Chap06.Lemma_6_15_2
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}}

local instance : HasLimits (Type w) := inferInstance
local instance : HasColimits (Type w) := inferInstance
local instance : PreservesLimits (forget (Type w)) := inferInstance
local instance : PreservesFilteredColimits (forget (Type w)) :=
  PreservesColimits.preservesFilteredColimits (forget (Type w))
local instance : (forget (Type w)).ReflectsIsomorphisms := inferInstance

/-- The open subspace attached to an inclusion `W ⊆ U`. -/
private abbrev openSubsetHomOfLE {W U : Opens X} (h : W ≤ U) :
    openSubsetSpace W ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE h)

private abbrev openSubsetRestrictionFunctor {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) ⥤ Opens (openSubsetSpace W) :=
  Opens.map (openSubsetHomOfLE h)

/-- Helper for Lemma 6.33.3: the inverse-image functor on opens induced by an inclusion
`W ⊆ U` is continuous for the canonical Grothendieck topologies. -/
private theorem openSubsetRestrictionFunctor_isContinuous {W U : Opens X} (h : W ≤ U) :
    (openSubsetRestrictionFunctor h).IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace U))
      (Opens.grothendieckTopology (openSubsetSpace W)) := by
  -- This is the standard continuity instance for inverse image on opens.
  infer_instance

/-- The inclusion `W ↪ U ↪ X` is the inclusion `W ↪ X`. -/
@[simp] private theorem openSubsetHomOfLE_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    openSubsetHomOfLE h ≫ openSubsetInclusion U = openSubsetInclusion W :=
  rfl

/-- Helper for Lemma 6.33.3: the open-subspace inclusions induced by nested open subsets compose
as expected. -/
@[simp] private theorem openSubsetHomOfLE_comp {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    openSubsetHomOfLE hAB ≫ openSubsetHomOfLE hBC =
      openSubsetHomOfLE (hAB.trans hBC) := by
  -- The induced map on open subspaces is defined from `homOfLE`, so composition is definitional.
  rfl

/-- Helper for Lemma 6.33.3: inverse-image functors on opens induced by nested inclusions
compose to the inverse-image functor of the composite inclusion. -/
private theorem openSubsetRestrictionFunctor_comp {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    openSubsetRestrictionFunctor hBC ⋙ openSubsetRestrictionFunctor hAB =
      openSubsetRestrictionFunctor (hAB.trans hBC) := by
  -- Both functors are `Opens.map` for the same composite open inclusion.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro V W i
  rfl

/-- Helper for Lemma 6.33.3: restricting from `X` to `U` and then internally to `W ⊆ U`
agrees on opens with restricting directly from `X` to `W`. -/
private theorem openSubsetRestrictionFunctor_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    (Opens.map (openSubsetInclusion U)) ⋙ openSubsetRestrictionFunctor h =
      Opens.map (openSubsetInclusion W) := by
  -- This is the functor-level version of `openSubsetHomOfLE_comp_inclusion`.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro V W i
  rfl

/-- Helper for Lemma 6.33.3: the map induced by the identity inclusion of an open subset is the
identity morphism of the corresponding open subspace. -/
@[simp] private theorem openSubsetHomOfLE_refl (W : Opens X) :
    openSubsetHomOfLE (show W ≤ W from le_rfl) = 𝟙 _ := by
  -- The identity inclusion induces the identity map on the open subspace.
  rfl

/-- Helper for Lemma 6.33.3: the ambient open `W ⊆ U` viewed as an open of `openSubsetSpace U`. -/
private def subspaceOpenOfLE {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) :=
  U.overEquivalence.functor.obj (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.3: the inclusion functor from opens of `openSubsetSpace U` back to
ambient opens of `X`. -/
private abbrev subspaceInclusionFunctor (U : Opens X) :
    Opens (openSubsetSpace U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

/-- Helper for Lemma 6.33.3: the `Over`-equivalence for `U` remembers the ambient open that
produced a given open of `openSubsetSpace U`. -/
private theorem overEquivalenceFunctorObjEq
    (U : Opens X) (V : Over U) :
    (subspaceInclusionFunctor U).obj (U.overEquivalence.functor.obj V) = V.left := by
  -- The represented open in the subspace has exactly the ambient points of `V.left`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, (leOfHom V.hom) hx⟩, hx, rfl⟩

/-- Helper for Lemma 6.33.3: viewing `W ⊆ U` as an open of `openSubsetSpace U` and then including
it back into `X` recovers the original ambient open `W`. -/
private theorem subspaceOpenOfLEImageEq
    {W U : Opens X} (h : W ≤ U) :
    (subspaceInclusionFunctor U).obj (subspaceOpenOfLE h) = W := by
  -- Specialize the `Over U` comparison to the arrow `W ⟶ U`.
  simpa [subspaceOpenOfLE] using
    overEquivalenceFunctorObjEq U (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.3: every open of `openSubsetSpace U` is represented by an ambient open
contained in `U`. -/
private theorem openSubsetOpenRepresentation
    {U : Opens X} (V : Opens (openSubsetSpace U)) :
    ∃ W : Opens X, ∃ hW : W ≤ U, subspaceOpenOfLE hW = V := by
  let OV : Over U := U.overEquivalence.inverse.obj V
  let hW : OV.left ≤ U := leOfHom OV.hom
  refine ⟨OV.left, hW, ?_⟩
  -- The `Over U ≌ Opens (openSubsetSpace U)` counit identifies `V` with its represented ambient
  -- open.
  have hEq : U.overEquivalence.functor.obj OV = V := by
    ext x
    constructor
    · intro hx
      exact (leOfHom ((U.overEquivalence.counitIso.app V).hom)) hx
    · intro hx
      exact (leOfHom ((U.overEquivalence.counitIso.app V).inv)) hx
  simpa [subspaceOpenOfLE, OV, hW] using hEq

/-- Helper for Lemma 6.33.3: membership in an open of `openSubsetSpace U` is equivalent to
membership of the underlying point in its ambient image in `X`. -/
private theorem memSubspaceOpenIff
    {U : Opens X} (A : Opens (openSubsetSpace U)) (x : openSubsetSpace U) :
    x ∈ A ↔ x.1 ∈ (subspaceInclusionFunctor U).obj A := by
  -- The image-open description records exactly the same points as the subspace open itself.
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    cases Subtype.ext hxy
    simpa using hy

/-- Helper for Lemma 6.33.3: membership in the represented open `subspaceOpenOfLE h` is exactly
membership in the ambient open `W`. -/
private theorem memSubspaceOpenOfLE_iff
    {W U : Opens X} (h : W ≤ U) (x : openSubsetSpace U) :
    x ∈ subspaceOpenOfLE h ↔ x.1 ∈ W := by
  -- Rewrite membership in the subspace open through its ambient image in `X`.
  simpa [subspaceOpenOfLEImageEq] using
    (memSubspaceOpenIff (subspaceOpenOfLE h) x)

/-- Helper for Lemma 6.33.3: points of `openSubsetSpace W` land in the represented open
`subspaceOpenOfLE h` after applying the inclusion `W ↪ U`. -/
private theorem openSubsetHomOfLE_mem_subspaceOpenOfLE
    {W U : Opens X} (h : W ≤ U) (x : openSubsetSpace W) :
    openSubsetHomOfLE h x ∈ subspaceOpenOfLE h := by
  -- The underlying point already lies in `W`, and `memSubspaceOpenOfLE_iff` turns that into the
  -- desired membership statement on `openSubsetSpace U`.
  exact (memSubspaceOpenOfLE_iff h (openSubsetHomOfLE h x)).2 x.property

/-- The map of open subspaces induced by an inclusion `W ⊆ U` is an open embedding. -/
private theorem openSubsetHomOfLE_isOpenEmbedding {W U : Opens X} (h : W ≤ U) :
    IsOpenEmbedding (openSubsetHomOfLE h) := by
  exact IsLocalHomeomorph.isOpenEmbedding_of_comp
    U.isOpenEmbedding.isLocalHomeomorph
    (by simpa [Function.comp, openSubsetHomOfLE_comp_inclusion] using W.isOpenEmbedding)
    (by continuity)

/-- Helper for Lemma 6.33.3: restricting an ambient open `A ⊆ B` along the inclusion `B ⊆ C`
produces the subspace open of `C` represented by the same ambient open `A`. -/
private theorem openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB)) =
      subspaceOpenOfLE (hAB.trans hBC) := by
  -- Compare both subspace opens through their ambient images in `X`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyA : y.1 ∈ A := by
      simpa [subspaceOpenOfLEImageEq] using
        (memSubspaceOpenIff (subspaceOpenOfLE hAB) y).1 hy
    exact
      (memSubspaceOpenIff (subspaceOpenOfLE (hAB.trans hBC)) (openSubsetHomOfLE hBC y)).2
        (by simpa [subspaceOpenOfLEImageEq, openSubsetHomOfLE] using hyA)
  · intro hx
    have hxA : x.1 ∈ A := by
      simpa [subspaceOpenOfLEImageEq] using
        (memSubspaceOpenIff (subspaceOpenOfLE (hAB.trans hBC)) x).1 hx
    refine ⟨⟨x.1, hAB hxA⟩, ?_, ?_⟩
    · exact (memSubspaceOpenIff (subspaceOpenOfLE hAB) ⟨x.1, hAB hxA⟩).2
        (by simpa [subspaceOpenOfLEImageEq] using hxA)
    · exact Subtype.ext rfl

/-- Helper for Lemma 6.33.3: evaluating the pullback of a ring sheaf from `C` to `B` on the
represented open `A ⊆ B` agrees with evaluating the original ring sheaf on the represented open
`A ⊆ C`. -/
private noncomputable def openSubsetHomOfLESectionIso
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (𝒪 : TopCat.Sheaf RingCat (openSubsetSpace C)) :
    (((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hBC)).obj 𝒪)).1.obj
        (op (subspaceOpenOfLE hAB)) ≅
      𝒪.1.obj (op (subspaceOpenOfLE (hAB.trans hBC))) :=
  -- First compare the actual pullback with the open-embedding pullback model, then rewrite the
  -- represented test open via `openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE`.
  (((TopCat.Sheaf.forget RingCat (openSubsetSpace B)).mapIso
      (((openSubsetHomOfLE_isOpenEmbedding hBC).sheafPullbackIso RingCat).app 𝒪)).app
      (op (subspaceOpenOfLE hAB))) ≪≫
    eqToIso (by
      change
        𝒪.1.obj
            (op ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB))) =
          𝒪.1.obj (op (subspaceOpenOfLE (hAB.trans hBC)))
      simpa using congrArg (fun V ↦ 𝒪.1.obj (op V))
        (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBC))

/-- Helper for Lemma 6.33.3: restricting the represented open `A ⊆ B` along `B ⊆ C` and then
including it back into `X` still remembers the ambient open `A`. -/
private theorem restrictedRepresentedOpenImageEq
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    (subspaceInclusionFunctor C).obj
        ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB)) = A := by
  -- Rewrite the restricted represented open to the direct represented open `A ⊆ C`.
  rw [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBC, subspaceOpenOfLEImageEq]

/-- The inclusion `U ∩ V ↪ U` is an open embedding. -/
private theorem openSubsetIntersectionLeftInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionLeftInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

/-- The inclusion `U ∩ V ↪ V` is an open embedding. -/
private theorem openSubsetIntersectionRightInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionRightInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

private theorem openSubsetTripleFirstInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleFirstInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

private theorem openSubsetTripleSecondInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleSecondInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

private theorem openSubsetTripleThirdInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleThirdInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

private theorem openSubsetTripleToPairLeftInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairLeftInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

private theorem openSubsetTripleToPairCenterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairCenterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding (inf_le_inf inf_le_right le_rfl)

private theorem openSubsetTripleToPairOuterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairOuterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

/-- Helper for Lemma 6.33.3: `TopCat.Sheaf.pullbackComp` is the left-adjoint comparison
isomorphism for the definitional equality of composite pushforward functors. -/
private theorem sheafPullbackComp_def {W Y Z : TopCat.{w}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp (A := Type w) f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl)) := by
  -- This is the defining comparison between the two left adjoints to the same composite
  -- pushforward functor.
  rfl

/-- Helper for Lemma 6.33.3: the pushforward functors on sheaves satisfy the expected
associativity coherence for composite morphisms of spaces. -/
private theorem sheaf_pushforward_assoc {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type w) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type w) f)
      (TopCat.Sheaf.pushforward (Type w) g)
      (TopCat.Sheaf.pushforward (Type w) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type w) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) := by
  -- Both functor-level coherence paths are definitionally the same after evaluation on objects.
  ext ℱ
  rfl

/-- Helper for Lemma 6.33.3: the pullback-composition isomorphisms inherit associativity coherence
from the comparison of left adjoints to the same composite pushforward functor. -/
private theorem sheaf_pullback_comp_assoc {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type w) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type w) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h) := by
  -- Rewrite the pullback comparisons to `leftAdjointCompIso`, where the standard associativity
  -- coherence is already packaged.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (sheaf_pushforward_assoc f g h))

/-- Helper for Lemma 6.33.3: the canonical pullback-composition comparisons satisfy the standard
pseudofunctor associativity identity in hom form. -/
private theorem sheaf_pullback_pseudofunctor_associativity {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type w) g h)
          (TopCat.Sheaf.pullback (Type w) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type w) h)
          (TopCat.Sheaf.pullbackComp (A := Type w) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  -- Package the associativity coherence in the exact hom-shaped form used by endpoint rewrites.
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type w) g h)
    (TopCat.Sheaf.pullback (Type w) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type w) h)
    (TopCat.Sheaf.pullbackComp (A := Type w) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    -- This is the hom-component form of `sheaf_pullback_comp_assoc`.
    exact congrArg Iso.hom (sheaf_pullback_comp_assoc f g h)
  rw [hcomp]
  ext X
  simpa using Iso.inv_hom_id_app e₁ X

/-- Helper for Lemma 6.33.3: cancelling the left comparison in pullback-composition coherence
identifies the forward endpoint with the direct restriction map. -/
private theorem sheaf_pullback_forward_endpoint {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type w)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
        ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
      (TopCat.Sheaf.pullback (Type w) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
    (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
  have hassoc :
      (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    -- What remains is the forward component of the pullback associativity coherence.
    simpa [Category.assoc] using
      (congrArg (fun α ↦ α.hom.app F) (sheaf_pullback_comp_assoc f g h)).symm
  have hrewrite :
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            t)
        hassoc
  have hassoc' :
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) =
        ((TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    simp [Category.assoc]
  have hcancel :
      ((TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F)
        (Iso.inv_hom_id_app
          (TopCat.Sheaf.pullbackComp (A := Type w) f g)
          ((TopCat.Sheaf.pullback (Type w) h).obj F))
  exact hrewrite.trans (hassoc'.trans hcancel)

/-- Helper for Lemma 6.33.3: cancelling the terminal direct restriction in the inverse
pullback-composition coherence yields the inverse endpoint map. -/
private theorem sheaf_pullback_inverse_endpoint {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type w)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
      (TopCat.Sheaf.pullback (Type w) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
        ((TopCat.Sheaf.pullback (Type w) h).obj F) =
      (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
  have hcoh :
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F =
        eqToHom (by simp) := by
    -- This is exactly the pseudofunctor associativity identity on pullbacks.
    simpa [Category.assoc] using
      congrArg (fun α ↦ α.app F) (sheaf_pullback_pseudofunctor_associativity f g h)
  have hid :
      eqToHom (by simp) =
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    -- The direct comparison composed with its inverse is the identity.
    simpa using
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h) F).symm
  have hrewrite :
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) =
        ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦
          ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
            t)
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h)
          F).symm
  have hcoh' :
      ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F =
        eqToHom (by simp) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    rw [hcoh]
  have hcancel :
      eqToHom (by simp) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    rw [hid]
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F)
        (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h) F)
  exact hrewrite.trans (hcoh'.trans hcancel)

variable {C : Type (w + 1)} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {ι : Type u} {U : ι → Opens X}

private abbrev algebraicRestrictToOpen (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U) :=
  U.isOpenEmbedding.sheafPullback C

private abbrev algebraicRestrictToPairLeft (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback C

private abbrev algebraicRestrictToPairRight (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback C

private abbrev algebraicRestrictToTripleFirst (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictToTripleSecond (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictToTripleThird (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace W) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleLeft (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairLeftInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleCenter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairCenterInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleOuter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairOuterInclusion_isOpenEmbedding U V W).sheafPullback C

private noncomputable def algebraicOpenSubsetRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    ((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullback C) ≅
      ((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullback C) := by
  -- Normalize the composite open-embedding pullback to the pullback along the composite map.
  let eComp :
      (openSubsetHomOfLE_isOpenEmbedding hTW).functor ⋙
          (openSubsetHomOfLE_isOpenEmbedding hWU).functor ≅
        (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by
        ext x
        change x ∈
            (((openSubsetHomOfLE_isOpenEmbedding hWU).functor.obj
                ((openSubsetHomOfLE_isOpenEmbedding hTW).functor.obj V)) : Set _) ↔
          x ∈ (((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor.obj V) : Set _)
        constructor
        · rintro ⟨x₁, hx₁, hx⟩
          rcases (by
            simpa [Topology.IsOpenEmbedding.functor] using hx₁) with ⟨t, htV, rfl⟩
          exact ⟨t, htV, by simpa using hx⟩
        · rintro ⟨t, htV, hx⟩
          refine ⟨(openSubsetHomOfLE hTW) t, ?_, by simpa using hx⟩
          simpa [Topology.IsOpenEmbedding.functor] using ⟨t, htV, rfl⟩))
      (fun {_ _} _ ↦ by apply Subsingleton.elim)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hTW)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding hWU)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU))
  simpa [Topology.IsOpenEmbedding.sheafPullback] using
    (CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (F := (openSubsetHomOfLE_isOpenEmbedding hTW).functor)
      (G := (openSubsetHomOfLE_isOpenEmbedding hWU).functor)
      (FG := (openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).functor)
      (eFG := eComp)
      C
      (Opens.grothendieckTopology (openSubsetSpace T))
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U)))

private noncomputable def algebraicGlobalRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    (U.isOpenEmbedding.sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ≅
      (W.isOpenEmbedding.sheafPullback C) := by
  -- The ambient restriction followed by the internal restriction is the direct pullback along
  -- the inclusion `W ↪ X`.
  let eComp :
      (openSubsetHomOfLE_isOpenEmbedding h).functor ⋙ U.isOpenEmbedding.functor ≅
        W.isOpenEmbedding.functor :=
    NatIso.ofComponents
      (fun V ↦ eqToIso (by
        ext x
        change x ∈
            ((U.isOpenEmbedding.functor.obj
                ((openSubsetHomOfLE_isOpenEmbedding h).functor.obj V)) : Set _) ↔
          x ∈ ((W.isOpenEmbedding.functor.obj V) : Set _)
        constructor
        · rintro ⟨x₁, hx₁, hx⟩
          rcases (by
            simpa [Topology.IsOpenEmbedding.functor] using hx₁) with ⟨w, hwV, rfl⟩
          exact ⟨w, hwV, by simpa using hx⟩
        · rintro ⟨w, hwV, hx⟩
          refine ⟨(openSubsetHomOfLE h) w, ?_, by simpa using hx⟩
          simpa [Topology.IsOpenEmbedding.functor] using ⟨w, hwV, rfl⟩))
      (fun {_ _} _ ↦ by apply Subsingleton.elim)
  letI := Topology.IsOpenEmbedding.functor_isContinuous
    (openSubsetHomOfLE_isOpenEmbedding h)
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  letI := Topology.IsOpenEmbedding.functor_isContinuous W.isOpenEmbedding
  simpa [Topology.IsOpenEmbedding.sheafPullback, openSubsetHomOfLE_comp_inclusion] using
    (CategoryTheory.Functor.sheafPushforwardContinuousComp'
      (F := (openSubsetHomOfLE_isOpenEmbedding h).functor)
      (G := U.isOpenEmbedding.functor)
      (FG := W.isOpenEmbedding.functor)
      (eFG := eComp)
      C
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))
      (Opens.grothendieckTopology X))

private noncomputable def algebraicRestrictToTripleFirstViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U V :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleSecondViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U V :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

private noncomputable def algebraicRestrictToTripleSecondViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft V W :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleThirdViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight V W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def algebraicRestrictToTripleFirstViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U W :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleThirdViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def algebraicGlobalRestrictionToPairViaLeftIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen U :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U)) ⋙
        (algebraicRestrictToPairLeft U V :
          TopCat.Sheaf C (openSubsetSpace U) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def algebraicGlobalRestrictionToPairViaRightIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen V :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace V)) ⋙
        (algebraicRestrictToPairRight U V :
          TopCat.Sheaf C (openSubsetSpace V) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ V from inf_le_right)).symm

local notation "algRestrictToOpen" => algebraicRestrictToOpen
local notation "algRestrictToPairLeft" => algebraicRestrictToPairLeft
local notation "algRestrictToPairRight" => algebraicRestrictToPairRight
local notation "algRestrictToTripleFirst" => algebraicRestrictToTripleFirst
local notation "algRestrictToTripleSecond" => algebraicRestrictToTripleSecond
local notation "algRestrictToTripleThird" => algebraicRestrictToTripleThird
local notation "algRestrictOverlapToTripleLeft" => algebraicRestrictOverlapToTripleLeft
local notation "algRestrictOverlapToTripleCenter" =>
  algebraicRestrictOverlapToTripleCenter
local notation "algRestrictOverlapToTripleOuter" =>
  algebraicRestrictOverlapToTripleOuter

private abbrev algebraicTripleOverlapHom12
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) :=
  ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).mapIso (overlapIso i j)).hom ≫
    ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app (localSheaf j))

private abbrev algebraicTripleOverlapHom23
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app (localSheaf k))

private abbrev algebraicTripleOverlapHom13
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).mapIso (overlapIso i k)).hom ≫
    ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app (localSheaf k))

/-
Domain-style sampling for Lemma 6.33.3:
- primary domain: sheaf descent on an open cover, specialized to sheaves valued in a category of
  algebraic structures;
- sampled owner declarations:
  `IsAlgebraicStructure`,
  `CategoryTheory.sheafCompose`,
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.Realizes`,
  `exists_sheaf_realizing_open_cover_glueing`;
- owner abstraction: the chapter owner remains `SheafOpenCoverGlueing U`, and the algebraic input
  data should only appear through a thin bridge to that owner;
- primitive data: the local `C`-valued sheaves, the pairwise overlap isomorphisms, the cocycle
  condition, and the covering hypothesis;
- derived API: the realization predicate and the existence theorem for a global realizing sheaf.

Source/core/bridge triage:
- `source-facing`: the primitive local sheaves, overlap isomorphisms, cocycle, and cover;
- `core/canonical`: `SheafOpenCoverGlueing U`;
  `bridge/view`: the private helper below that forgets along `F` and packages the resulting
  set-valued descent datum in the existing owner. -/
private abbrev algebraicToTypes (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits F := inferInstance
  letI : (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose F :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) F

private noncomputable def algebraicPairLeftToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((algRestrictToPairLeft U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

private noncomputable def algebraicPairRightToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algRestrictToPairRight U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

private noncomputable def algebraicLeftOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionLeftInclusion U V)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((algebraicToTypes F U).obj ℱ)

private noncomputable def algebraicRightOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
      ℱ) ≅
      (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionRightInclusion U V)).obj
        ((algebraicToTypes F V).obj ℱ) :=
  (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((algebraicToTypes F V).obj ℱ)).symm

/-- Helper for Lemma 6.33.3: forgetting a direct triple restriction agrees definitionally with
forgetting first and then applying the open-embedding pullback on the triple overlap. -/
private noncomputable def algebraicTripleFirstToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((algRestrictToTripleFirst U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
        (openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: forgetting the second direct triple restriction agrees
definitionally with the corresponding open-embedding pullback after forgetting. -/
private noncomputable def algebraicTripleSecondToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algRestrictToTripleSecond U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F V ⋙
        (openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: forgetting the third direct triple restriction agrees definitionally
with the corresponding open-embedding pullback after forgetting. -/
private noncomputable def algebraicTripleThirdToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace W)) :
    ((algRestrictToTripleThird U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) ≅
      ((algebraicToTypes F W ⋙
        (openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: the direct triple restriction of the first local sheaf has the same
underlying sheaf as the actual pullback along the first triple-overlap inclusion. -/
private noncomputable def algebraicTripleFirstOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleFirstInclusion U V W)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((algRestrictToTripleFirst U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  ((openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullbackIso (Type w)).app
      ((algebraicToTypes F U).obj ℱ) ≪≫
    (algebraicTripleFirstToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: the direct triple restriction of the second local sheaf has the same
underlying sheaf as the actual pullback along the second triple-overlap inclusion. -/
private noncomputable def algebraicTripleSecondOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleSecondInclusion U V W)).obj
        ((algebraicToTypes F V).obj ℱ) ≅
      ((algRestrictToTripleSecond U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  ((openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullbackIso (Type w)).app
      ((algebraicToTypes F V).obj ℱ) ≪≫
    (algebraicTripleSecondToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: the direct triple restriction of the third local sheaf has the same
underlying sheaf as the actual pullback along the third triple-overlap inclusion. -/
private noncomputable def algebraicTripleThirdOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V W : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace W)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetTripleThirdInclusion U V W)).obj
        ((algebraicToTypes F W).obj ℱ) ≅
      ((algRestrictToTripleThird U V W ⋙ algebraicToTypes F (U ⊓ V ⊓ W)).obj ℱ) :=
  ((openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullbackIso (Type w)).app
      ((algebraicToTypes F W).obj ℱ) ≪≫
    (algebraicTripleThirdToTypesIso F U V W ℱ).symm

/-- Helper for Lemma 6.33.3: forgetting an arbitrary internal restriction agrees definitionally
with first restricting in `C` and then forgetting to `Type`. -/
private noncomputable def algebraicRestrictionToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ⋙ algebraicToTypes F W).obj ℱ) ≅
      (((algebraicToTypes F U) ⋙
        (openSubsetHomOfLE_isOpenEmbedding h).sheafPullback (Type w)).obj ℱ) :=
  eqToIso rfl

/-- Helper for Lemma 6.33.3: the actual pullback of the forgotten sheaf along an internal open
inclusion matches the forgotten `C`-valued restriction. -/
private noncomputable def algebraicRestrictionOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ⋙
          algebraicToTypes F W).obj ℱ) :=
  ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullbackIso (Type w)).app
      ((algebraicToTypes F U).obj ℱ) ≪≫
    (algebraicRestrictionToTypesIso F h ℱ).symm

/-- Helper for Lemma 6.33.3: transporting a forgotten morphism through an internal restriction is
exactly the naturality square of the owner comparison. -/
private theorem algebraicRestrictionOwnerIso_naturality
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {W U : Opens X} (h : W ≤ U)
    {ℱ 𝒢 : TopCat.Sheaf C (openSubsetSpace U)} (φ : ℱ ⟶ 𝒢) :
    (algebraicRestrictionOwnerIso F h ℱ).inv ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).map
        ((algebraicToTypes F U).map φ) =
    (algebraicToTypes F W).map
      (((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C).map φ) ≫
      (algebraicRestrictionOwnerIso F h 𝒢).inv := by
  -- Route correction: the middle overlap factor should be handled as one naturality square for
  -- the generic owner comparison, not as another path-specific transport chase.
  let e := ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullbackIso (Type w))
  -- Peel off the definitional `eqToIso rfl` layer so the goal becomes the naturality square for
  -- the open-embedding pullback comparison itself.
  rw [show (algebraicRestrictionOwnerIso F h ℱ).inv =
      eqToHom rfl ≫ (e.app ((algebraicToTypes F U).obj ℱ)).inv by
        rfl]
  rw [show (algebraicRestrictionOwnerIso F h 𝒢).inv =
      eqToHom rfl ≫ (e.app ((algebraicToTypes F U).obj 𝒢)).inv by
        rfl]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc]
  have hnat := CategoryTheory.NatIso.naturality_1 e ((algebraicToTypes F U).map φ)
  -- Postcompose by the inverse comparison to isolate the imported middle factor.
  have hpost := congrArg
      (fun t ↦ t ≫ (e.app ((algebraicToTypes F U).obj 𝒢)).inv)
      hnat
  change (e.app ((algebraicToTypes F U).obj ℱ)).inv ≫
        (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE h)).map
          ((algebraicToTypes F U).map φ) =
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback (Type w)).map
          ((algebraicToTypes F U).map φ) ≫
        (e.app ((algebraicToTypes F U).obj 𝒢)).inv
  simpa [Category.assoc] using hpost

/-- Helper for Lemma 6.33.3: the imported forward endpoint of a composite internal restriction can
be rewritten to the direct forgotten composite, while keeping the remaining imported owner bridge
to the middle factor explicit. -/
private theorem algebraicRestrictionCompToTypes_forwardImportedEndpoint
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) (openSubsetHomOfLE hTW)
        (openSubsetHomOfLE hWU)).inv.app
        ((algebraicToTypes F U).obj ℱ) ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
        (algebraicRestrictionOwnerIso F hWU ℱ).hom =
    (algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ).hom ≫
      (algebraicToTypes F T).map
        ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).inv.app ℱ) ≫
      (algebraicRestrictionOwnerIso F hTW
        (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)).inv := by
  -- Route correction: this bridge is stated in the imported-owner spelling that actually survives
  -- after normalizing the triple-overlap path.
  let eWU := algebraicRestrictionOwnerIso F hWU ℱ
  let eTW := algebraicRestrictionOwnerIso F hTW
    (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)
  let eComp := algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ
  -- Peel off the definitional `eqToIso rfl` factors so only the genuine pullback comparisons and
  -- the composed internal restriction isomorphism remain.
  rw [show eWU.hom =
      (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullbackIso (Type w)).app
          ((algebraicToTypes F U).obj ℱ)).hom ≫
        eqToHom rfl by
        rfl]
  rw [show eTW.inv =
      eqToHom rfl ≫
        (((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullbackIso (Type w)).app
          ((algebraicToTypes F W).obj
            (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ))).inv by
        rfl]
  rw [show eComp.hom =
      (((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullbackIso (Type w)).app
          ((algebraicToTypes F U).obj ℱ)).hom ≫
        eqToHom rfl by
        rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
  have hforward := sheaf_pullback_forward_endpoint
      (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU) (𝟙 (openSubsetSpace U))
      ((algebraicToTypes F U).obj ℱ)
  -- TODO: combine the forward pullback endpoint with the mapped composite-restriction comparison
  -- and the naturality square from `algebraicRestrictionOwnerIso_naturality`. The remaining
  -- blocker is the exact placement of the direct-vs-iterated restriction transport.
  sorry

/-- Helper for Lemma 6.33.3: the imported inverse endpoint of a composite internal restriction
rewrites to the inverse of the direct forgotten composite, again keeping the middle imported owner
transport explicit. -/
private theorem algebraicRestrictionCompToTypes_inverseImportedEndpoint
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {T W U : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U) (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (algebraicRestrictionOwnerIso F hTW
        (((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C).obj ℱ)).inv ≫
      (TopCat.Sheaf.pullback (Type w) (openSubsetHomOfLE hTW)).map
        (algebraicRestrictionOwnerIso F hWU ℱ).inv ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) (openSubsetHomOfLE hTW)
          (openSubsetHomOfLE hWU)).hom.app
        ((algebraicToTypes F U).obj ℱ) =
    (algebraicToTypes F T).map
      ((algebraicOpenSubsetRestrictionCompIso (C := C) hTW hWU).hom.app ℱ) ≫
      (algebraicRestrictionOwnerIso F (hTW.trans hWU) ℱ).inv := by
  -- Route correction: the same imported-owner transport appears on the right endpoint, so it is
  -- isolated once here instead of being re-expanded in each overlap leg.
  sorry

/-- Helper for Lemma 6.33.3: the explicit forgotten `12` overlap path is the direct triple-owner
transport of the forgotten algebraic `12` comparison. -/
private theorem algebraicTripleOverlapHom12_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) := by
  -- The pair-to-Types comparisons are definitional, so the pulled-back middle transport reduces
  -- to the forgotten overlap morphism on the pair restriction.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U i) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
            (Type w)).obj (localSheaf i)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U i) (U j) ⋙ algebraicToTypes F (U i ⊓ U j)).obj
          (localSheaf j)))
  -- After rewriting both pulled-back comparison maps to identities, only the central overlap map
  -- remains.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
          t)
      hRight

/-- Helper for Lemma 6.33.3: forgetting the algebraic `12` overlap comparison preserves its
three-factor decomposition before any owner transport is inserted. -/
private theorem algebraicTripleOverlapHom12_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).mapIso
            (overlapIso i j)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app (localSheaf j)) := by
  -- Expand the mapped algebraic path once so later transport lemmas only have to compare owner
  -- spellings, not refactor the algebraic composite again.
  rw [algebraicTripleOverlapHom12, Functor.map_comp, Functor.map_comp]

private theorem algebraicTripleOverlapHom12_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U j))).inv.app
        ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U j)).map (overlapIso i j).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U i) (U j) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairLeftInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U j))).hom.app
        ((algebraicToTypes F (U j)).obj (localSheaf j)) =
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom12 localSheaf overlapIso i j k) ≫
        (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).inv := by
  -- Expand the mapped algebraic `12` path first, so the only remaining work is the two owner
  -- endpoint comparisons against the imported `pullbackComp` spelling.
  rw [algebraicTripleOverlapHom12_mappedPath]
  -- TODO: assemble the rewritten path by first normalizing the two adjacent imported owner maps
  -- to `algebraicRestrictionOwnerIso`, then apply the three generic bridge lemmas
  -- `algebraicRestrictionCompToTypes_forwardImportedEndpoint`,
  -- `algebraicRestrictionOwnerIso_naturality`, and
  -- `algebraicRestrictionCompToTypes_inverseImportedEndpoint` with `congrArg`-based association
  -- wrappers. The remaining blocker is rewrite targeting, not a new mathematical identity.
  sorry

/-- Helper for Lemma 6.33.3: the explicit forgotten `23` overlap path is the direct triple-owner
transport of the forgotten algebraic `23` comparison. -/
private theorem algebraicTripleOverlapHom23_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).mapIso
            (overlapIso j k)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app (localSheaf k)) := by
  -- Expand the mapped algebraic `23` comparison once so the later bridge proof can focus only
  -- on owner transports.
  rw [algebraicTripleOverlapHom23, Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 6.33.3: the pair-to-Types comparisons in the `23` overlap leg are
definitionally trivial after pulling back to the triple overlap. -/
private theorem algebraicTripleOverlapHom23_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) := by
  -- The pair-to-Types comparisons are definitional, so pulling them back to the triple overlap
  -- leaves only the central forgotten overlap morphism.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U j) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U j) (U k)).sheafPullback
            (Type w)).obj (localSheaf j)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U j) (U k) ⋙ algebraicToTypes F (U j ⊓ U k)).obj
          (localSheaf k)))
  -- Rewriting both pulled-back comparison maps to identities leaves exactly the overlap map.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
          t)
      hRight

private theorem algebraicTripleOverlapHom23_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U j) (U k))).inv.app
        ((algebraicToTypes F (U j)).obj (localSheaf j)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U j) (U k) (localSheaf j)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U j) (U k) (localSheaf j)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U j ⊓ U k)).map (overlapIso j k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U j) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U j) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairCenterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U j) (U k))).hom.app
        ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicTripleSecondOwnerIso F (U i) (U j) (U k) (localSheaf j)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom23 localSheaf overlapIso i j k) ≫
        (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
  -- Expand the mapped algebraic `23` path first; the remaining work is again only the two owner
  -- endpoint comparisons and the center pulled-back overlap map.
  rw [algebraicTripleOverlapHom23_mappedPath]
  -- TODO: as in the `12` leg, convert the two adjacent imported owner maps to
  -- `algebraicRestrictionOwnerIso`, then wrap the three generic bridge lemmas with explicit
  -- `congrArg` association contexts. The blocker is again local rewrite targeting only.
  sorry

/-- Helper for Lemma 6.33.3: the explicit forgotten `13` overlap path is the direct triple-owner
transport of the forgotten algebraic `13` comparison. -/
private theorem algebraicTripleOverlapHom13_mappedPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
        (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) =
      (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).mapIso
            (overlapIso i k)).hom) ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app (localSheaf k)) := by
  -- Expand the mapped algebraic `13` comparison once so the last bridge theorem has the same
  -- normal form as the other two.
  rw [algebraicTripleOverlapHom13, Functor.map_comp, Functor.map_comp]

/-- Helper for Lemma 6.33.3: the pair-to-Types comparisons in the `13` overlap leg are
definitionally trivial after pulling back to the triple overlap. -/
private theorem algebraicTripleOverlapHom13_middle_toTypes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullback (Type w)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
      (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom =
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) := by
  -- The pair-to-Types comparisons are again definitional, so pulling them back to the triple
  -- overlap leaves only the outer forgotten overlap morphism.
  have hLeft :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv =
      𝟙 _ := by
    rw [show (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map_id
        ((algebraicToTypes F (U i) ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U k)).sheafPullback
            (Type w)).obj (localSheaf i)))
  have hRight :
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom =
      𝟙 _ := by
    rw [show (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom = eqToHom rfl by rfl]
    exact
      ((TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map_id
        ((algRestrictToPairRight (U i) (U k) ⋙ algebraicToTypes F (U i ⊓ U k)).obj
          (localSheaf k)))
  -- Rewriting both pulled-back comparison maps to identities leaves exactly the overlap map.
  rw [hLeft]
  simpa [Category.assoc] using
    congrArg
      (fun t ↦
        𝟙 _ ≫
          (TopCat.Sheaf.pullback (Type w)
              (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
            ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
          t)
      hRight

private theorem algebraicTripleOverlapHom13_toTypesPath
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] {U : ι → Opens X}
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (TopCat.Sheaf.pullbackComp (A := Type w)
        (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
        (openSubsetIntersectionLeftInclusion (U i) (U k))).inv.app
        ((algebraicToTypes F (U i)).obj (localSheaf i)) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicLeftOwnerIso F (U i) (U k) (localSheaf i)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairLeftToTypesIso F (U i) (U k) (localSheaf i)).inv ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        ((algebraicToTypes F (U i ⊓ U k)).map (overlapIso i k).hom) ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicPairRightToTypesIso F (U i) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullback (Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))).map
        (algebraicRightOwnerIso F (U i) (U k) (localSheaf k)).hom ≫
      (TopCat.Sheaf.pullbackComp (A := Type w)
          (openSubsetTripleToPairOuterInclusion (U i) (U j) (U k))
          (openSubsetIntersectionRightInclusion (U i) (U k))).hom.app
        ((algebraicToTypes F (U k)).obj (localSheaf k)) =
      (algebraicTripleFirstOwnerIso F (U i) (U j) (U k) (localSheaf i)).hom ≫
        (algebraicToTypes F (U i ⊓ U j ⊓ U k)).map
          (algebraicTripleOverlapHom13 localSheaf overlapIso i j k) ≫
        (algebraicTripleThirdOwnerIso F (U i) (U j) (U k) (localSheaf k)).inv := by
  -- Expand the mapped algebraic `13` path first; as above, only the owner transports remain.
  rw [algebraicTripleOverlapHom13_mappedPath]
  -- TODO: the `13` leg has the same remaining assembly issue as `12/23`: after the two imported
  -- owner pairs are normalized to `algebraicRestrictionOwnerIso`, the proof should follow from
  -- the same three generic bridge lemmas with explicit association wrappers.
  sorry

namespace AlgebraicSheafOpenCover

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves valued in
a category of algebraic structures on an open cover. -/
def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    algebraicTripleOverlapHom12 localSheaf overlapIso i j k ≫
      algebraicTripleOverlapHom23 localSheaf overlapIso i j k =
    algebraicTripleOverlapHom13 localSheaf overlapIso i j k

variable {F : C ⥤ Type w} [IsAlgebraicStructure C F] {U : ι → Opens X}

private noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U where
  localSheaf i := (algebraicToTypes F (U i)).obj (localSheaf i)
  overlapIso i j :=
    (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i) ≪≫
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).symm) ≪≫
      ((algebraicToTypes F (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
      (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j) ≪≫
        algebraicRightOwnerIso F (U i) (U j) (localSheaf j))
  cocycle := by
    -- TODO: once the three `_toTypesPath` lemmas above are assembled from the generic bridge
    -- lemmas, the cocycle closes by rewriting the imported `12/23/13` paths and mapping the
    -- source algebraic cocycle through `algebraicToTypes`.
    sorry
  isCover := hU

private abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) :=
  ((algebraicGlobalRestrictionToPairViaLeftIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairLeft (U i) (U j)).mapIso (φ i)).hom

private abbrev realizationRightHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairRight (U i) (U j)).obj (localSheaf j) :=
  ((algebraicGlobalRestrictionToPairViaRightIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairRight (U i) (U j)).mapIso (φ j)).hom

/-- A `C`-valued sheaf realizes an algebraic gluing datum if its restrictions recover the given
local sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in `TopCat.Sheaf C`. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ φ : ∀ i : ι,
      ((U i).isOpenEmbedding.sheafPullback C).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end AlgebraicSheafOpenCover

-- Proof sketch: glue the underlying set-valued sheaves by Lemma 6.33.2, then transport the
-- algebraic structure on sections across the equalizer construction.
/-- Lemma 6.33.3: an algebraic gluing datum on an open cover is realized by a `C`-valued sheaf on
the ambient space. -/
theorem exists_algebraic_sheaf_of_open_cover_glueing
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : TopCat.Sheaf C X, AlgebraicSheafOpenCover.Realizes U localSheaf overlapIso ℱ := by
  -- TODO: build the global `C`-valued presheaf by the equalizer construction from Lemma 6.33.2
  -- carried out in `C`, prove the sheaf condition after forgetting along `F`, and then package
  -- the local restriction isomorphisms; the blocker is the missing structured equalizer/sheaf
  -- assembly in this file.
  sorry

end

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

/-- Restricting the restriction of `𝒪` to `U` further to `W ⊆ U` gives the restriction of `𝒪`
directly to `W`. -/
private noncomputable def restrictedRingSheafPullbackIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪) ≅
      (TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪 :=
  let e :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U) :=
    (TopCat.Sheaf.pullbackComp (openSubsetHomOfLE h) (openSubsetInclusion U) :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U))
  e.app 𝒪 ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback RingCat f).obj 𝒪)
      (openSubsetHomOfLE_comp_inclusion h))

/-- The canonical map of restricted ring sheaves attached to an inclusion `W ⊆ U`. -/
private noncomputable def restrictedRingSheafToPushforward
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪 ⟶
      ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W))).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
      ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪)) ≫
    ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).mapIso
      (restrictedRingSheafPullbackIso 𝒪 h)).hom

/-- Restriction of a ring sheaf to an open subset, as a sheaf on the corresponding open
subspace. -/
abbrev ringSheafRestriction (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    TopCat.Sheaf RingCat (openSubsetSpace U) :=
  (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪

namespace TopCat

set_option quotPrecheck false in
scoped notation:80 𝒪:80 " |_ " U:80 =>
  ringSheafRestriction 𝒪 U

end TopCat

open scoped TopCat

/- Domain-style sampling for the module-valued restriction step:
- primary domain: inverse-image/restriction of sheaves of modules along open inclusions;
- sampled owner declarations: `SheafOfModules.pullback`, `SheafOfModules.pullbackComp`,
  `moduleSheafRestrictionToOpen`, `moduleSheafExtensionByZeroAdjunction`;
- owner abstraction: the core owner is `SheafOfModules.pullback`, while
  `moduleSheafRestrictionToOpen` is the chapter’s canonical open-immersion specialization;
- source/core/bridge triage: the source-facing surface is the restricted ring sheaf notation
  `𝒪 |_ U`; `SheafOfModules.pullback` is core/canonical; and the pairwise overlap restrictions
  below are thin bridge/view specializations for the named inclusions in the open-cover
  geometry. -/

/- Restriction of sheaves of modules along an inclusion `W ⊆ U` of open subsets. -/
/-- Helper for Lemma 6.33.3: unfolding the internal restriction owner exposes the
pullback/pushforward adjunction unit on `openSubsetSpace U` followed by the single codomain
transport to the directly restricted ring sheaf `𝒪 |_ W`. -/
private theorem restrictedRingSheafToPushforward_def
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    restrictedRingSheafToPushforward 𝒪 h =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)) ≫
        ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).mapIso
          (restrictedRingSheafPullbackIso 𝒪 h)).hom) := by
  -- This is exactly the defining formula of `restrictedRingSheafToPushforward`.
  rfl

/-- Helper for Lemma 6.33.3: changing the ring sheaf along
`restrictedRingSheafPullbackIso 𝒪 h` is an equivalence on module sheaves, hence its pushforward is
a right adjoint. -/
private theorem restrictedRingSheafPullbackIso_pushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W)))
      ((restrictedRingSheafPullbackIso 𝒪 h).hom)).IsRightAdjoint := by
  let e := restrictedRingSheafPullbackIso 𝒪 h
  let transportPush :
      SheafOfModules (𝒪 |_ W) ⥤
        SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) :=
    SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W))) e.hom
  let transportInverse :
      SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) ⥤
        SheafOfModules (𝒪 |_ W) :=
    SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W))) e.inv
  have transport_push_inverse_id :
      e.inv ≫
          (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
              (Opens.grothendieckTopology (openSubsetSpace W))
              (Opens.grothendieckTopology (openSubsetSpace W))).map e.hom) =
        𝟙 (𝒪 |_ W) := by
    -- On the identity site, pushing forward a morphism of ring sheaves does not change its
    -- sectionwise action, so the composite reduces to `e.inv ≫ e.hom` on `𝒪 |_ W`.
    rw [show
      (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace W))).map e.hom) = e.hom by
      rfl]
    cases e with
    | mk hom inv hom_inv_id inv_hom_id =>
        simpa [ringSheafRestriction] using inv_hom_id
  have transport_inverse_push_id :
      e.hom ≫
          (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
              (Opens.grothendieckTopology (openSubsetSpace W))
              (Opens.grothendieckTopology (openSubsetSpace W))).map e.inv) =
        𝟙 ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) := by
    -- The same sectionwise computation identifies the opposite composite with `e.hom ≫ e.inv`
    -- on the pullback ring sheaf.
    rw [show
      (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace W))).map e.inv) = e.inv by
      rfl]
    cases e with
    | mk hom inv hom_inv_id inv_hom_id =>
        simpa [ringSheafRestriction] using hom_inv_id
  -- Route correction: isolate the codomain transport from the geometric restriction map and
  -- package it as an identity-site equivalence built from `pushforwardComp` and `pushforwardId`.
  let transportUnitIso :
      𝟭 (SheafOfModules (𝒪 |_ W)) ≅
        transportPush ⋙ transportInverse :=
    (SheafOfModules.pushforwardId (𝒪 |_ W)).symm ≪≫
      SheafOfModules.pushforwardCongr transport_push_inverse_id.symm ≪≫
      (SheafOfModules.pushforwardComp
        (F := 𝟭 (Opens (openSubsetSpace W)))
        (G := 𝟭 (Opens (openSubsetSpace W)))
        e.inv e.hom).symm
  let transportCounitIso :
      transportInverse ⋙ transportPush ≅
        𝟭 (SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U))) :=
    SheafOfModules.pushforwardComp
        (F := 𝟭 (Opens (openSubsetSpace W)))
        (G := 𝟭 (Opens (openSubsetSpace W)))
        e.hom e.inv ≪≫
      SheafOfModules.pushforwardCongr transport_inverse_push_id ≪≫
      SheafOfModules.pushforwardId
        ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U))
  let transportEquiv :
      SheafOfModules (𝒪 |_ W) ≌
        SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) :=
    CategoryTheory.Equivalence.mk
      transportPush
      transportInverse
      transportUnitIso
      transportCounitIso
  letI : transportPush.IsEquivalence :=
    transportEquiv.isEquivalence_functor
  -- Any equivalence is in particular a right adjoint.
  infer_instance

/-- Helper for Lemma 6.33.3: the geometric unit factor in the internal restriction owner already
is a right adjoint by the generic module pullback/pushforward adjunction for the explicit
restriction functor `openSubsetRestrictionFunctor h`. -/
private theorem moduleSheafRestrictionUnit_pushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward (F := openSubsetRestrictionFunctor h)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
        (𝒪 |_ U)))).IsRightAdjoint := by
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  let φ :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
      (𝒪 |_ U)))
  letI :
      (PresheafOfModules.pushforward (F := openSubsetRestrictionFunctor h) φ.hom).IsRightAdjoint :=
    -- Route correction: seed the sheaf-level construction with the explicit presheaf adjunction,
    -- rather than asking typeclass search to rediscover the same right-adjoint package.
    (PresheafOfModules.pullbackPushforwardAdjunction
      (F := openSubsetRestrictionFunctor h) φ.hom).isRightAdjoint
  -- TODO: finish by packaging `SheafOfModules.PullbackConstruction.adjunction φ`; the remaining
  -- blocker is the explicit `HasWeakSheafify` / `WEqualsLocallyBijective` path for
  -- `Opens.grothendieckTopology (openSubsetSpace W)` in this local spelling.
  sorry

private instance moduleSheafRestrictionPushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint := by
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  letI :
      (SheafOfModules.pushforward (F := openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)))).IsRightAdjoint :=
    moduleSheafRestrictionUnit_pushforward_isRightAdjoint 𝒪 h
  letI :
      (SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W)))
        ((restrictedRingSheafPullbackIso 𝒪 h).hom)).IsRightAdjoint :=
    restrictedRingSheafPullbackIso_pushforward_isRightAdjoint 𝒪 h
  let hCompIso :
      (SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W)))
          ((restrictedRingSheafPullbackIso 𝒪 h).hom)) ⋙
        (SheafOfModules.pushforward (F := openSubsetRestrictionFunctor h)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U)))) ≅
      SheafOfModules.pushforward
        (F := openSubsetRestrictionFunctor h ⋙ 𝟭 (Opens (openSubsetSpace W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U))) ≫
          ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
            ((restrictedRingSheafPullbackIso 𝒪 h).hom)) :=
    -- Freeze the source spelling of `pushforwardComp` before any normalization.
    SheafOfModules.pushforwardComp
      (F := openSubsetRestrictionFunctor h)
      (G := 𝟭 (Opens (openSubsetSpace W)))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)))
      ((restrictedRingSheafPullbackIso 𝒪 h).hom)
  letI :
      ((SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W)))
          ((restrictedRingSheafPullbackIso 𝒪 h).hom)) ⋙
        (SheafOfModules.pushforward (F := openSubsetRestrictionFunctor h)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U))))).IsRightAdjoint := inferInstance
  -- Route correction: split the owner into the geometric unit factor and the codomain transport,
  -- then invoke the generic right-adjoint package for pushforward along a composite.
  change
    (SheafOfModules.pushforward
      (F := openSubsetRestrictionFunctor h ⋙ 𝟭 (Opens (openSubsetSpace W)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U))) ≫
        ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology (openSubsetSpace U))
          (Opens.grothendieckTopology (openSubsetSpace W))).map
          ((restrictedRingSheafPullbackIso 𝒪 h).hom))).IsRightAdjoint
  exact Functor.isRightAdjoint_of_iso hCompIso

noncomputable abbrev moduleSheafRestriction
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ W) :=
  let _ :
      (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint :=
    moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 h
  SheafOfModules.pullback (restrictedRingSheafToPushforward 𝒪 h)

/-- Restriction of `𝒪|_U`-modules to `\mathcal O|_{U \cap V}` along the left inclusion
`U \cap V \subset U`. -/
noncomputable abbrev moduleSheafRestrictionToPairLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_left

/-- Restriction of `𝒪|_V`-modules to `\mathcal O|_{U \cap V}` along the right inclusion
`U \cap V \subset V`. -/
noncomputable abbrev moduleSheafRestrictionToPairRight
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_right

private abbrev moduleRestrictToTripleFirst
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

private abbrev moduleRestrictToTripleSecond
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

private abbrev moduleRestrictToTripleThird
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ W) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_right

private abbrev moduleRestrictOverlapToTripleLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ V)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_left

private abbrev moduleRestrictOverlapToTripleCenter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (V ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 (inf_le_inf inf_le_right le_rfl)

private abbrev moduleRestrictOverlapToTripleOuter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

/-- Helper for Lemma 6.33.3: composing two internal restriction owners agrees with the direct
restriction owner. -/
private theorem restrictedRingSheafToPushforward_comp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    restrictedRingSheafToPushforward 𝒪 hWU ≫
        ((openSubsetRestrictionFunctor hWU).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology (openSubsetSpace U))
          (Opens.grothendieckTopology (openSubsetSpace W))).map
          (restrictedRingSheafToPushforward 𝒪 hTW) =
      restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU) := by
  -- TODO: after `CategoryTheory.Sheaf.hom_ext`, reduce an arbitrary open of `openSubsetSpace U`
  -- to a represented open via `openSubsetOpenRepresentation`, and then identify the section maps
  -- by the normalized represented-open formulas.
  sorry

/-- Helper for Lemma 6.33.3: restricting first to `U` and then internally to `W ⊆ U` gives the
same ring-sheaf owner as restricting directly to `W`. -/
private theorem restrictedRingSheafToOpenComp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
        (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (openSubsetSpace U))).map
          (restrictedRingSheafToPushforward 𝒪 h)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)).unit.app 𝒪) := by
  -- TODO: after `CategoryTheory.Sheaf.hom_ext`, rewrite the open of `openSubsetSpace U`
  -- appearing in the pushforward evaluation to a represented open and then reduce both section
  -- maps to direct restriction along `W ↪ X`.
  sorry

/-- Helper for Lemma 6.33.3: once two module-restriction owners are definitionally identified,
their pullback functors are identified by transport along that equality. -/
private noncomputable abbrev moduleSheafPullbackCongrIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat} {R : Sheaf K RingCat} [Functor.IsContinuous F J K]
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R}
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(SheafOfModules.pushforward ψ).IsRightAdjoint]
    (hEq : φ = ψ) :
    SheafOfModules.pullback φ ≅ SheafOfModules.pullback ψ := by
  -- This isolates the equality-to-iso transport so later composition isomorphisms can use a
  -- single stable adapter instead of repeating `change` or `convert`.
  cases hEq
  -- Once the owners are literally the same morphism, the two pullback functors coincide.
  exact Iso.refl _

private noncomputable def moduleSheafRestrictionCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    moduleSheafRestriction 𝒪 hWU ⋙ moduleSheafRestriction 𝒪 hTW ≅
      moduleSheafRestriction 𝒪 (hTW.trans hWU) := by
  letI :
      (openSubsetRestrictionFunctor hTW).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace T)) :=
    openSubsetRestrictionFunctor_isContinuous hTW
  letI :
      (openSubsetRestrictionFunctor hWU).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous hWU
  letI :
      (openSubsetRestrictionFunctor (hTW.trans hWU)).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace T)) :=
    openSubsetRestrictionFunctor_isContinuous (hTW.trans hWU)
  letI :
      (SheafOfModules.pushforward
        (F := openSubsetRestrictionFunctor hWU ⋙ openSubsetRestrictionFunctor hTW)
        (restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU))).IsRightAdjoint := by
    -- Rewrite the direct owner to the composite restriction functor before reusing the existing
    -- right-adjoint package.
    simpa [openSubsetRestrictionFunctor_comp hTW hWU] using
      (moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 (hTW.trans hWU))
  have hEq :
      restrictedRingSheafToPushforward 𝒪 hWU ≫
          ((openSubsetRestrictionFunctor hWU).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
            (restrictedRingSheafToPushforward 𝒪 hTW) =
        restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU) := by
    -- Normalize the composite inverse-image functor before comparing the two owners.
    simpa [openSubsetRestrictionFunctor_comp hTW hWU] using
      restrictedRingSheafToPushforward_comp_eq 𝒪 hTW hWU
  -- Once the owners are compared over the same restriction functor, `pullbackComp` gives the
  -- functor comparison.
  exact
    (SheafOfModules.pullbackComp
      (restrictedRingSheafToPushforward 𝒪 hWU)
      (restrictedRingSheafToPushforward 𝒪 hTW)) ≪≫
      moduleSheafPullbackCongrIso
        (F := openSubsetRestrictionFunctor hWU ⋙ openSubsetRestrictionFunctor hTW) hEq

private noncomputable def moduleSheafRestrictionToOpenCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestriction 𝒪 h ≅
      moduleSheafRestrictionToOpen W 𝒪 := by
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  letI :
      (SheafOfModules.pushforward
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion U)).unit.app 𝒪))).IsRightAdjoint :=
    (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction U 𝒪).isRightAdjoint
  letI :
      (SheafOfModules.pushforward
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion W)).unit.app 𝒪))).IsRightAdjoint := by
    -- Normalize the direct owner to the composite restriction functor before reusing the
    -- canonical right-adjoint instance.
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction W 𝒪).isRightAdjoint
  have hEq :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
          (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace U))).map
            (restrictedRingSheafToPushforward 𝒪 h)) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)).unit.app 𝒪) := by
    -- The mixed owner becomes the direct owner once the restriction functors are normalized.
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      restrictedRingSheafToOpenComp_eq 𝒪 h
  -- Package the composite pullback, then transport its owner to the direct restriction owner.
  exact
    (SheafOfModules.pullbackComp
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪)
      (restrictedRingSheafToPushforward 𝒪 h)) ≪≫
      moduleSheafPullbackCongrIso
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h) hEq

private noncomputable def moduleRestrictToTripleFirstViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleSecondViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

private noncomputable def moduleRestrictToTripleSecondViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleThirdViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def moduleRestrictToTripleFirstViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleThirdViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def moduleRestrictionToPairViaLeftIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestrictionToPairLeft 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictionToPairViaRightIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen V 𝒪 ⋙ moduleSheafRestrictionToPairRight 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ V from inf_le_right)).symm

private noncomputable def moduleToAddCommGrpPairLeftRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairLeft 𝒪 U V).obj ℱ) := by
  -- After transporting from the open-embedding pullback owner to the ordinary pullback owner, the
  -- remaining additive restriction comparison is definitional.
  have hEq :
      (TopCat.Sheaf.pullback AddCommGrpCat.{w} (openSubsetIntersectionLeftInclusion U V)).obj
          ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) =
        (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
          ((moduleSheafRestrictionToPairLeft 𝒪 U V).obj ℱ) := by
    -- TODO: normalize the underlying additive sheaf of `SheafOfModules.pullback
    -- (restrictedRingSheafToPushforward 𝒪 inf_le_left)` to the ordinary sheaf pullback along
    -- `openSubsetIntersectionLeftInclusion U V`.
    sorry
  exact
    (((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso
        AddCommGrpCat.{w}).app ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ)).symm ≪≫
      eqToIso hEq

private noncomputable def moduleToAddCommGrpPairRightRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback
      AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairRight 𝒪 U V).obj ℱ) := by
  -- The right-overlap owner reduces to the same ordinary additive pullback after applying the
  -- standard `sheafPullbackIso`.
  have hEq :
      (TopCat.Sheaf.pullback AddCommGrpCat.{w} (openSubsetIntersectionRightInclusion U V)).obj
          ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) =
        (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
          ((moduleSheafRestrictionToPairRight 𝒪 U V).obj ℱ) := by
    -- TODO: normalize the underlying additive sheaf of `SheafOfModules.pullback
    -- (restrictedRingSheafToPushforward 𝒪 inf_le_right)` to the ordinary sheaf pullback along
    -- `openSubsetIntersectionRightInclusion U V`.
    sorry
  exact
    (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso
        AddCommGrpCat.{w}).app ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ)).symm ≪≫
      eqToIso hEq

variable (𝒪 : TopCat.Sheaf RingCat X)

private abbrev moduleTripleOverlapHom12
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) :=
  ((moduleRestrictToTripleFirstViaIJIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleLeft 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i j)).hom ≫
    ((moduleRestrictToTripleSecondViaIJIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf j))

private abbrev moduleTripleOverlapHom23
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleSecondViaJKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((moduleRestrictOverlapToTripleCenter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((moduleRestrictToTripleThirdViaJKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

private abbrev moduleTripleOverlapHom13
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleFirstViaIKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleOuter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i k)).hom ≫
    ((moduleRestrictToTripleThirdViaIKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves of
`𝒪`-modules on an open cover. -/
private abbrev moduleToTypes (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits (forget AddCommGrpCat.{w}) := inferInstance
  letI :
      (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose
        (forget AddCommGrpCat.{w}) :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  SheafOfModules.toSheaf (𝒪 |_ U) ⋙
    sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) (forget AddCommGrpCat.{w})

private noncomputable def modulePairLeftToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

private noncomputable def modulePairRightToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

private noncomputable def moduleLeftOwnerIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) := by
  letI : PreservesFilteredColimitsOfSize.{w, w, w, w, w + 1, w + 1}
      (forget (Type w)) := by
    exact PreservesColimits.preservesFilteredColimits (forget (Type w))
  exact ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((moduleToTypes 𝒪 U).obj ℱ)

private noncomputable def moduleRightOwnerIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) := by
  letI : PreservesFilteredColimitsOfSize.{w, w, w, w, w + 1, w + 1}
      (forget (Type w)) := by
    exact PreservesColimits.preservesFilteredColimits (forget (Type w))
  exact (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((moduleToTypes 𝒪 V).obj ℱ)).symm

namespace ModuleSheafOpenCover

def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    moduleTripleOverlapHom12 𝒪 localSheaf overlapIso i j k ≫
      moduleTripleOverlapHom23 𝒪 localSheaf overlapIso i j k =
    moduleTripleOverlapHom13 𝒪 localSheaf overlapIso i j k

variable {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U where
  localSheaf i := (moduleToTypes 𝒪 (U i)).obj (localSheaf i)
  overlapIso i j :=
    (moduleLeftOwnerIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
      (modulePairLeftToTypesIso 𝒪 (U i) (U j) (localSheaf i)).symm) ≪≫
      ((moduleToTypes 𝒪 (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
      (modulePairRightToTypesIso 𝒪 (U i) (U j) (localSheaf j) ≪≫
        moduleRightOwnerIso 𝒪 (U i) (U j) (localSheaf j))
  cocycle := by
    -- TODO: transport the module cocycle through the restriction-comparison and additive-owner
    -- isomorphisms once the module normalization block is completed.
    sorry
  isCover := hU

private abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) :=
  ((moduleRestrictionToPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).mapIso (φ i)).hom

private abbrev realizationRightHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j) :=
  ((moduleRestrictionToPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).mapIso (φ j)).hom

/-- A sheaf of `𝒪`-modules realizes a module gluing datum if its restrictions recover the given
local module sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in the categories of sheaves of `𝒪`-modules. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (ℱ : SheafOfModules 𝒪) : Prop :=
  ∃ φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end ModuleSheafOpenCover

-- Proof sketch: the equalizer construction from Lemma 6.33.2 inherits the module structure over
-- each ring of sections, and the resulting sheaf of modules restricts back to the given local
-- module sheaves.
/-- Lemma 6.33.3 for modules: a gluing datum of sheaves of `𝒪`-modules on an open cover is
realized by a sheaf of `𝒪`-modules on the ambient space. -/
theorem exists_module_sheaf_of_open_cover_glueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : SheafOfModules 𝒪, ModuleSheafOpenCover.Realizes U localSheaf overlapIso ℱ := by
  -- TODO: construct the global presheaf of modules by the equalizer recipe, package it with
  -- `PresheafOfModules.ofPresheaf`, verify the sheaf condition after forgetting to additive
  -- sheaves, and then assemble the realization isomorphisms. The blocker is the missing module
  -- restriction normalization package above.
  sorry

end
