import Mathlib
import StacksProject_2024.Chap07.Definition_7_43_7
import StacksProject_2024.Chap07.Lemma_7_41_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (i : MorphismOfTopoiIn J K)

/- Domain-style sampling for Lemma 7.43.8:
- primary domain: closed immersions of topoi and the owner-level consequences for the direct-image
  functor and the adjunction counit;
- sampled owner API:
  `MorphismOfTopoiIn.IsClosedImmersion`,
  `MorphismOfTopoiIn.IsEmbedding`,
  `Adjunction.counit_isIso_of_R_fully_faithful`,
  the canonical implication theorems from `Lemma_7_41_1`;
- best owner abstraction: the source-facing class `MorphismOfTopoiIn.IsClosedImmersion i`, whose
  primitive data are only the embedding structure and the closed-subtopos condition on
  `(i _*).essImage`;
- primitive data: `i.IsClosedImmersion`;
- derived API: the canonical fully faithful structure on `(i _*)` together with the reflection and
  preservation properties on `(i _*)` that this lemma records for closed immersions.

Source/core/bridge triage:
- `source-facing`: the closed-immersion consequences listed in Lemma 7.43.8;
- `core/canonical`: `MorphismOfTopoiIn.IsEmbedding`, `(i _*).Full`,
  `(i _*).Faithful`, `IsIso i.adjunction.counit`, and the standard
  `Preserves`/`Reflects` owner classes on `(i _*)`;
- `bridge/view`: the passage from `i.IsClosedImmersion` to those owner-level consequences. -/

/-- Lemma 7.43.8 (1): for a closed immersion of topoi, the direct-image functor `i_*` is fully
faithful. -/
noncomputable instance closedImmersion_pushforwardFullyFaithful [i.IsClosedImmersion] :
    (i _*).FullyFaithful :=
  .ofFullyFaithful (i _*)

/-- Helper for Lemma 7.43.8: a full faithful functor preserves any chosen colimit shape once its
essential image is closed under that shape. -/
private theorem preservesColimitsOfShape_of_essImage_closed
    {A : Type*} [Category A] {B : Type*} [Category B]
    {S : Type*} [Category S]
    (F : A ⥤ B) [HasColimitsOfShape S A] [HasColimitsOfShape S B]
    [F.Full] [F.Faithful] [F.essImage.IsClosedUnderColimitsOfShape S] :
    PreservesColimitsOfShape S F := by
  -- Factor through the essential image: the first factor is an equivalence, and the inclusion
  -- preserves these colimits because the essential image is closed under them.
  letI : HasColimitsOfShape S F.EssImageSubcategory := inferInstance
  letI : PreservesColimitsOfShape S F.essImage.ι := inferInstance
  letI : PreservesColimitsOfShape S F.toEssImage := inferInstance
  exact preservesColimitsOfShape_of_natIso (Functor.toEssImageCompι F)

/-- Helper for Lemma 7.43.8: in a slice category, terminality is equivalent to the structure map
being an isomorphism. -/
private theorem over_isTerminal_iff_isIso_hom
    {X : Sheaf J (Type w)} (Y : Over X) :
    Nonempty (IsTerminal Y) ↔ IsIso Y.hom := by
  constructor
  · rintro ⟨hY⟩
    -- The unique map from `Y` to the identity object in the slice is an isomorphism between
    -- terminal objects, and its left component is exactly `Y.hom`.
    have hIso : IsIso (Over.mkIdTerminal.from Y) := by
      exact Limits.isIso_of_isTerminal hY Over.mkIdTerminal (Over.mkIdTerminal.from Y)
    have hIsoLeft : IsIso ((Over.forget X).map (Over.mkIdTerminal.from Y)) := by
      infer_instance
    simpa [Over.mkIdTerminal_from_left] using hIsoLeft
  · intro hY
    -- An isomorphic structure map identifies `Y` with the terminal identity object of the slice.
    letI : IsIso Y.hom := hY
    let e : Y.left ≅ X := ⟨Y.hom, inv Y.hom, by simp, by simp⟩
    exact ⟨IsTerminal.ofIso Over.mkIdTerminal ((Over.isoMk e (by simp [e])).symm)⟩

/-- Helper for Lemma 7.43.8: `WalkingSpan.zero` is the initial object of the pushout shape. -/
private noncomputable def walkingSpan_zero_isInitial :
    IsInitial (WalkingSpan.zero) := by
  refine IsInitial.ofUniqueHom (fun j ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
  cases j with
  | none => exact 𝟙 _
  | some j =>
      cases j with
      | left => exact WalkingSpan.Hom.fst
      | right => exact WalkingSpan.Hom.snd

/-- Helper for Lemma 7.43.8: the closed-subtopos witness rewrites the essential image of a closed
immersion into the terminal-object condition in the slice localization. -/
private theorem closedImmersion_essImage_eq_star_terminal [i.IsClosedImmersion] :
    ∃ F : Sheaf J (Type w),
      (i _*).essImage = fun G : Sheaf J (Type w) ↦ Nonempty (IsTerminal ((Over.star F).obj G)) := by
  let h : i.IsClosedImmersion := inferInstance
  have hClosed : IsClosedSubtopos (i _*).essImage := h.isClosedSubtopos
  rcases hClosed.exists_subterminal with ⟨F, _, hPdef⟩
  refine ⟨F, funext ?_⟩
  intro G
  -- Rewrite the closed-subtopos defining equation through the slice localization object.
  have hhom : ((Over.star F).obj G).hom = (prod.fst : F ⨯ G ⟶ F) := by
    rw [Over.star_obj_hom]
    exact Limits.prod.lift_fst (prod.fst : F ⨯ G ⟶ F) (𝟙 (F ⨯ G))
  rw [hPdef, over_isTerminal_iff_isIso_hom]
  constructor <;> intro hIso <;> simpa [hhom] using hIso

/-- Helper for Lemma 7.43.8: the slice-terminal condition is stable under coequalizers because the
localization inverse-image functor preserves them and `WalkingParallelPair.one` is terminal. -/
private theorem star_terminal_closed_under_coequalizers
    (F : Sheaf J (Type w)) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun G : Sheaf J (Type w) ↦ Nonempty (IsTerminal ((Over.star F).obj G)))
      WalkingParallelPair := by
  let P : ObjectProperty (Sheaf J (Type w)) :=
    fun G ↦ Nonempty (IsTerminal ((Over.star F).obj G))
  letI : P.IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro G G' e hG
    rcases hG with ⟨t⟩
    exact ⟨IsTerminal.ofIso t ((Over.star F).mapIso e)⟩
  change P.IsClosedUnderColimitsOfShape WalkingParallelPair
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨K, hK⟩
  -- `Over.forget F` creates colimits, and under `forget` the functor `Over.star F` is just
  -- product with `F`, which preserves colimits in the ambient topos.
  letI : PreservesColimitsOfShape WalkingParallelPair (Over.star F ⋙ Over.forget F) := by
    letI : Closed F := by infer_instance
    letI : PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft F) := by
      infer_instance
    change PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj F)
    exact preservesColimitsOfShape_of_natIso
      (CartesianMonoidalCategory.tensorLeftIsoProd F)
  letI : PreservesColimitsOfShape WalkingParallelPair (Over.star F) :=
    preservesColimitsOfShape_of_reflects_of_preserves (Over.star F) (Over.forget F)
  let c := (colimit.cocone K).map (Over.star F)
  have hc : IsColimit c := isColimitOfPreserves (Over.star F) (colimit.isColimit K)
  let t₀ : IsTerminal ((K ⋙ Over.star F).obj WalkingParallelPair.zero) :=
    Classical.choice (hK WalkingParallelPair.zero)
  let t₁ : IsTerminal ((K ⋙ Over.star F).obj WalkingParallelPair.one) :=
    Classical.choice (hK WalkingParallelPair.one)
  let e₀ : (K ⋙ Over.star F).obj WalkingParallelPair.zero ≅
      (K ⋙ Over.star F).obj WalkingParallelPair.one :=
    t₀.uniqueUpToIso t₁
  let α : K ⋙ Over.star F ≅
      (Functor.const WalkingParallelPair).obj ((K ⋙ Over.star F).obj WalkingParallelPair.one) :=
    NatIso.ofComponents
      (fun j ↦ by
        cases j
        · exact e₀
        · exact Iso.refl _)
      (fun {j j'} f ↦ by
        cases f
        · simpa using t₁.hom_ext ((K ⋙ Over.star F).map WalkingParallelPairHom.left) e₀.hom
        · simpa using t₁.hom_ext ((K ⋙ Over.star F).map WalkingParallelPairHom.right) e₀.hom
        · cases j <;> simp [e₀])
  let hConst :
      IsColimit
        (Limits.constCocone WalkingParallelPair
          ((K ⋙ Over.star F).obj WalkingParallelPair.one)) :=
    Limits.isColimitConstCocone WalkingParallelPair _
  -- A connected diagram of terminal slice objects is naturally isomorphic to a constant diagram.
  exact ⟨IsTerminal.ofIso t₁ (IsColimit.coconePointsIsoOfNatIso hConst hc α.symm)⟩

/-- Helper for Lemma 7.43.8: the slice-terminal condition is stable under pushouts because the
localization inverse-image functor preserves them and a pushout of terminal objects is terminal. -/
private theorem star_terminal_closed_under_pushouts
    (F : Sheaf J (Type w)) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun G : Sheaf J (Type w) ↦ Nonempty (IsTerminal ((Over.star F).obj G)))
      WalkingSpan := by
  let P : ObjectProperty (Sheaf J (Type w)) :=
    fun G ↦ Nonempty (IsTerminal ((Over.star F).obj G))
  letI : P.IsClosedUnderIsomorphisms := by
    refine ⟨?_⟩
    intro G G' e hG
    rcases hG with ⟨t⟩
    exact ⟨IsTerminal.ofIso t ((Over.star F).mapIso e)⟩
  change P.IsClosedUnderColimitsOfShape WalkingSpan
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨K, hK⟩
  -- `Over.forget F` creates colimits, and under `forget` the functor `Over.star F` is just
  -- product with `F`, which preserves colimits in the ambient topos.
  letI : PreservesColimitsOfShape WalkingSpan (Over.star F ⋙ Over.forget F) := by
    letI : Closed F := by infer_instance
    letI : PreservesColimitsOfShape WalkingSpan (MonoidalCategory.tensorLeft F) := by
      infer_instance
    change PreservesColimitsOfShape WalkingSpan (prod.functor.obj F)
    exact preservesColimitsOfShape_of_natIso
      (CartesianMonoidalCategory.tensorLeftIsoProd F)
  letI : PreservesColimitsOfShape WalkingSpan (Over.star F) :=
    preservesColimitsOfShape_of_reflects_of_preserves (Over.star F) (Over.forget F)
  let c := (colimit.cocone K).map (Over.star F)
  have hc : IsColimit c := isColimitOfPreserves (Over.star F) (colimit.isColimit K)
  let t₀ : IsTerminal ((K ⋙ Over.star F).obj WalkingSpan.zero) :=
    Classical.choice (hK WalkingSpan.zero)
  letI : ∀ (a b : WalkingSpan) (f : a ⟶ b), IsIso ((K ⋙ Over.star F).map f) := by
    intro a b f
    exact Limits.isIso_of_isTerminal (Classical.choice (hK a)) (Classical.choice (hK b))
      ((K ⋙ Over.star F).map f)
  let hTerminal :
      IsColimit
        (coconeOfDiagramInitial walkingSpan_zero_isInitial (K ⋙ Over.star F)) :=
    colimitOfDiagramInitial walkingSpan_zero_isInitial (K ⋙ Over.star F)
  -- The initial vertex of the span already determines the pushout once every map is an isomorphism.
  exact ⟨IsTerminal.ofIso t₀ (hTerminal.coconePointUniqueUpToIso hc)⟩

/-- Helper for Lemma 7.43.8: the essential-image factorization of a closed immersion makes the
direct-image functor preserve coequalizers. -/
private theorem closedImmersion_pushforwardPreservesCoequalizers_aux [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingParallelPair (i _*) := by
  rcases closedImmersion_essImage_eq_star_terminal (i := i) with ⟨F, hEss⟩
  -- The closed witness identifies the essential image with a property already known to be stable
  -- under coequalizers in the slice formulation.
  haveI : (i _*).essImage.IsClosedUnderColimitsOfShape WalkingParallelPair := by
    simpa [hEss] using star_terminal_closed_under_coequalizers (J := J) F
  -- Factor `i_*` through its essential image and use closure of that image under coequalizers.
  let F' : Sheaf K (Type w) ⥤ Sheaf J (Type w) := i _*
  exact preservesColimitsOfShape_of_essImage_closed (S := WalkingParallelPair) F'

/-- Helper for Lemma 7.43.8: the essential-image factorization of a closed immersion makes the
direct-image functor preserve pushouts. -/
private theorem closedImmersion_pushforwardPreservesPushouts_aux [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingSpan (i _*) := by
  rcases closedImmersion_essImage_eq_star_terminal (i := i) with ⟨F, hEss⟩
  -- The same slice-terminal description is stable under pushouts by the localization exactness
  -- argument from the source proof.
  haveI : (i _*).essImage.IsClosedUnderColimitsOfShape WalkingSpan := by
    simpa [hEss] using star_terminal_closed_under_pushouts (J := J) F
  -- Factor `i_*` through its essential image and use closure of that image under pushouts.
  let F' : Sheaf K (Type w) ⥤ Sheaf J (Type w) := i _*
  exact preservesColimitsOfShape_of_essImage_closed (S := WalkingSpan) F'

/-- Helper for Lemma 7.43.8: the counit of the closed-immersion adjunction is an isomorphism
because `i_*` is fully faithful. -/
private theorem closedImmersion_counit_isIso [i.IsClosedImmersion] :
    IsIso i.adjunction.counit := by
  -- Closed immersions are embeddings, so the standard adjunction theorem applies directly.
  let h : i.IsClosedImmersion := inferInstance
  letI : (i _*).Full := h.toIsEmbedding.toFull
  letI : (i _*).Faithful := h.toIsEmbedding.toFaithful
  exact Adjunction.counit_isIso_of_R_fully_faithful i.adjunction

/-- Lemma 7.43.8 (2): for a closed immersion of topoi, the direct-image functor `i_*` sends
surjections to surjections. -/
instance closedImmersion_pushforwardPreservesEpimorphisms [i.IsClosedImmersion] :
    (i _*).PreservesEpimorphisms := by
  -- The source proof first establishes pushout preservation and then invokes the owner-level
  -- implication from Lemma 7.41.1.
  exact pushforwardPreservesPushouts_implies_pushforwardPreservesEpimorphisms
    (f := i) (closedImmersion_pushforwardPreservesPushouts_aux (i := i))

/-- Lemma 7.43.8 (3): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with coequalizers. -/
instance closedImmersion_pushforwardPreservesCoequalizers [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingParallelPair (i _*) := by
  -- This is the coequalizer half of the essential-image argument implemented above.
  exact closedImmersion_pushforwardPreservesCoequalizers_aux (i := i)

/-- Lemma 7.43.8 (4): for a closed immersion of topoi, the direct-image functor `i_*` commutes
with pushouts. -/
instance closedImmersion_pushforwardPreservesPushouts [i.IsClosedImmersion] :
    PreservesColimitsOfShape WalkingSpan (i _*) := by
  -- This is the pushout half of the essential-image argument implemented above.
  exact closedImmersion_pushforwardPreservesPushouts_aux (i := i)

/-- Lemma 7.43.8 (5): for a closed immersion of topoi, the direct-image functor `i_*` reflects
injections. -/
instance closedImmersion_pushforwardReflectsMonomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsMonomorphisms := by
  -- Once the counit is an isomorphism, the generic owner theorem gives reflection of monomorphisms.
  exact counitIsIso_implies_pushforwardReflectsMonomorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

/-- Lemma 7.43.8 (6): for a closed immersion of topoi, the direct-image functor `i_*` reflects
surjections. -/
instance closedImmersion_pushforwardReflectsEpimorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsEpimorphisms := by
  -- The same counit-isomorphism bridge yields reflection of epimorphisms.
  exact counitIsIso_implies_pushforwardReflectsEpimorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

/-- Lemma 7.43.8 (7): for a closed immersion of topoi, the direct-image functor `i_*` reflects
isomorphisms. -/
instance closedImmersion_pushforwardReflectsIsomorphisms [i.IsClosedImmersion] :
    (i _*).ReflectsIsomorphisms := by
  -- The counit-isomorphism criterion also gives reflection of isomorphisms.
  exact counitIsIso_implies_pushforwardReflectsIsomorphisms
    (f := i) (closedImmersion_counit_isIso (i := i))

end

end MorphismOfTopoiIn

end CategoryTheory
