import Mathlib
import stacks_project.Chap07.Lemma_7_29_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u₁ u₂ u₃ v₁ v₂ v₃ w

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.29.8:
- primary domain: equivalences of sheaf topoi presented by dense-subsite comparison functors to a
  common site;
- sampled owner API:
  `Functor.IsDenseSubsite`,
  `MorphismOfTopoiIn`,
  `MorphismOfTopoiIn.id`,
  `CatCommSq`,
  `Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension`;
- best owner abstraction: the main statement should live directly over the common site, the two
  dense-subsite functors into it, and the factorization square through the identity morphism of
  the common sheaf topos; the pointwise right-Kan-extension witnesses belong only to a separate
  bridge theorem realizing the dense-subsite cocontinuous direct-image functors as equivalences on
  sheaves of sets;
- primitive data: the common site `(C', J')`, the dense-subsite functors from `(C, J)` and
  `(D, K)`, and the comparison square expressing `f` through `MorphismOfTopoiIn.id J'`;
- derived API: the equivalence instances for the two cocontinuous sheaf pushforwards and the
  resulting canonical natural isomorphism
  `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
    targetFunctor.sheafPushforwardCocontinuous`;
  the public theorem surfaces should end with `Nonempty` of the square owner or of the comparison
  natural isomorphism, with no extra tautological payload, because those owners already contain the
  relevant comparison data.

Source/core/bridge triage:
- `source-facing`: the existence of a common site presenting an equivalence of topoi;
- `core/canonical`: `Functor.IsDenseSubsite`, `MorphismOfTopoiIn`, `MorphismOfTopoiIn.id`, and
  `CatCommSq`;
- `bridge/view`: the pointwise right Kan extension hypotheses used to realize the two
  dense-subsite cocontinuous direct-image functors as equivalences on set-valued sheaves and turn
  the square through `MorphismOfTopoiIn.id J'` into a canonical natural isomorphism of functors to
  `Sh(C', J')`.
-/

/-- Helper for Remark 7.29.8: once a square through the identity on the common sheaf topos is
available, horizontally inverting the two dense-subsite equivalences identifies the two canonical
functors from `Sh(K)` to `Sh(J')`. -/
private theorem identity_square_induces_canonical_iso
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J)
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (targetFunctor : D ⥤ C') [targetFunctor.IsDenseSubsite K J']
    [∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P]
    (sq :
      CatCommSq
        (targetFunctor.sheafPushforwardContinuous (Type w) K J')
        ((MorphismOfTopoiIn.id J')⁻¹)
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    Nonempty
      (f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type w) J J' ≅
        targetFunctor.sheafPushforwardCocontinuous (Type w) K J') := by
  -- Equip the two continuous pushforwards with the canonical equivalence structures whose
  -- inverses are the cocontinuous pushforwards.
  let sourceAdj := sourceFunctor.sheafAdjunctionCocontinuous (Type w) J J'
  let targetAdj := targetFunctor.sheafAdjunctionCocontinuous (Type w) K J'
  letI :
      (sourceFunctor.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := J) (K := J') sourceFunctor
  letI :
      (targetFunctor.sheafPushforwardCocontinuous (Type w) K J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := K) (K := J') targetFunctor
  letI : IsIso sourceAdj.unit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso sourceAdj.counit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso targetAdj.unit := by
    exact NatIso.isIso_of_isIso_app _
  letI : IsIso targetAdj.counit := by
    exact NatIso.isIso_of_isIso_app _
  let sourceEquiv := sourceAdj.toEquivalence
  let targetEquiv := targetAdj.toEquivalence
  -- Horizontal inversion turns the square on continuous pushforwards into the desired comparison
  -- between the cocontinuous pushforwards.
  let sqInv :=
    CatCommSq.hInv targetEquiv ((MorphismOfTopoiIn.id J')⁻¹) (f⁻¹) sourceEquiv sq
  refine ⟨?_⟩
  simpa [sourceEquiv, targetEquiv] using sqInv.iso.symm

-- Proof sketch: this helper isolates the source-facing existential package from Remark `7.29.8`.
-- The remaining work is the source-faithful replay of the common full-subcategory construction
-- from Lemma `7.29.6`, but now with the D-side functor upgraded to a dense subsite and the middle
-- comparison fixed to the identity on the common site.
/-- Helper for Remark 7.29.8: once the source-side dense-subsite comparison is already known to be
an equivalence on sheaves of sets, the canonical square from Lemma `7.29.6` forces the
target-side continuous pullback functor to be an equivalence as soon as `f⁻¹` is. -/
private theorem target_pullback_isEquivalence_of_canonical_factorization
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence]
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    [(v.sheafPushforwardContinuous (Type w) J J').IsEquivalence]
    (u : D ⥤ C')
    [IsMorphismOfSites K J' u]
    [HasWeakSheafify J' (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    (sq :
      CatCommSq
        (𝟭 (Sheaf K (Type w)))
        (u.sheafPullback (Type w) K J')
        (f⁻¹)
        (v.sheafPushforwardContinuous (Type w) J J')) :
    (u.sheafPullback (Type w) K J').IsEquivalence := by
  have hcomp :
      (u.sheafPullback (Type w) K J' ⋙ v.sheafPushforwardContinuous (Type w) J J').IsEquivalence := by
    -- The square identifies the composite `u.sheafPullback ⋙ v.sheafPushforwardContinuous`
    -- with `f⁻¹`.
    rw [Functor.isEquivalence_iff_of_iso
      ((CatCommSq.iso
          (𝟭 (Sheaf K (Type w)))
          (u.sheafPullback (Type w) K J')
          (f⁻¹)
          (v.sheafPushforwardContinuous (Type w) J J')).symm ≪≫
        Functor.leftUnitor (f⁻¹))]
    infer_instance
  -- Cancel the known equivalence on the right to recover the equivalence of `u.sheafPullback`.
  exact Functor.isEquivalence_of_comp_right
    (u.sheafPullback (Type w) K J')
    (v.sheafPushforwardContinuous (Type w) J J')

/-- Helper for Remark 7.29.8: once the `Type w` pointwise right-Kan-extension bridge is supplied
for a dense-subsite functor, its continuous pushforward on sheaves of sets is an equivalence. -/
private theorem denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (v : C ⥤ C') [v.IsDenseSubsite J J']
    [∀ P : Cᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P] :
    (v.sheafPushforwardContinuous (Type w) J J').IsEquivalence := by
  -- First upgrade the cocontinuous pushforward to an equivalence using the dense-subsite API.
  letI :
      (v.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence :=
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := J) (K := J') v
  -- Then the adjunction identifies the continuous pushforward as the inverse equivalence.
  exact
    (v.sheafAdjunctionCocontinuous (Type w) J J').isEquivalence_left_of_isEquivalence_right

/-- Helper for Remark 7.29.8: in the canonical factorization from Lemma `7.29.6`, once the
source-side `Type w` pointwise right-Kan-extension bridge is available, the target-side pullback
is an equivalence whenever `f⁻¹` is. -/
private theorem site_factorization_target_pullback_isEquivalence_of_source_pointwise_right_kan
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence]
    (sourceFunctor : C ⥤ C') [sourceFunctor.IsDenseSubsite J J']
    [∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P]
    (targetFunctor : D ⥤ C')
    [IsMorphismOfSites K J' targetFunctor]
    [HasWeakSheafify J' (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasLeftKanExtension P]
    (sq :
      CatCommSq
        (𝟭 (Sheaf K (Type w)))
        (targetFunctor.sheafPullback (Type w) K J')
        (f⁻¹)
        (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) :
    (targetFunctor.sheafPullback (Type w) K J').IsEquivalence := by
  -- The source-side comparison functor becomes an equivalence after inserting the Kan bridge.
  letI :
      (sourceFunctor.sheafPushforwardContinuous (Type w) J J').IsEquivalence :=
    denseSubsite_pushforwardContinuous_isEquivalence_of_pointwise_right_kan
      (J := J) (J' := J') sourceFunctor
  -- With the source comparison inverted, the canonical square forces the target pullback to be an
  -- equivalence as well.
  exact target_pullback_isEquivalence_of_canonical_factorization f sourceFunctor targetFunctor sq

/-- Helper for Remark 7.29.8: a common-site factorization package with identity middle morphism. -/
private theorem exists_common_site_identity_factorization_data_of_isEquivalence
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (sq :
        CatCommSq
          (targetFunctor.sheafPushforwardContinuous (Type w) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous (Type w) J J')),
      True := by
  -- Route correction: the public theorem is now reduced to a single helper whose only task is the
  -- common-site construction itself.
  -- The verified prefix now isolates the formal part of the source route:
  -- after inserting the eventual source-side Kan bridge,
  -- `site_factorization_target_pullback_isEquivalence_of_source_pointwise_right_kan`
  -- upgrades the target-side pullback from Lemma `7.29.6` to an equivalence.
  -- TODO: turn that sheaf-level equivalence into a dense-subsite owner on the target-side functor,
  -- then use the induced continuous-pushforward equivalence to rewrite the canonical square
  -- through `(MorphismOfTopoiIn.id J')⁻¹`.
  sorry

-- Proof sketch: the dense-subsite API already provides pointwise right Kan extensions for the
-- lifted presheaf universe used elsewhere in the chapter; this isolates the usable owner while
-- the remaining blocker is to descend it to the theorem-facing `Type w` universe.
/-- Helper for Remark 7.29.8: a dense-subsite functor has pointwise right Kan extensions in the
lifted presheaf universe canonically used by the dense-subsite comparison API. -/
private theorem denseSubsite_has_lifted_pointwise_right_kan_extensions
    {C' : Type u₃} [Category.{v₃} C'] {J' : GrothendieckTopology C'}
    (u : C ⥤ C') [u.IsDenseSubsite J J'] :
    ∀ P : Cᵒᵖ ⥤ Type (max u₁ u₃ v₁ v₃ w), u.op.HasPointwiseRightKanExtension P := by
  -- The lifted-universe right Kan extension instances are already registered on dense subsites.
  intro P
  infer_instance

-- Proof sketch: this strengthens the previous helper by adding the right-Kan-extension witnesses
-- needed for the cocontinuous comparison equivalences on `Type w`-valued sheaves.
/-- Helper for Remark 7.29.8: the common-site identity factorization package together with the
pointwise right-Kan-extension data on both dense-subsite functors. -/
private theorem exists_common_site_identity_factorization_data_of_isEquivalence_with_kan
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : ∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P)
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : ∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P)
      (sq :
        CatCommSq
          (targetFunctor.sheafPushforwardContinuous (Type w) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous (Type w) J J')),
      True := by
  -- TODO: the current `ulift` descent route only creates `Type w`-valued limits from lifted
  -- limits when the structured-arrow shape is `w`-small, but the relevant shapes here live in
  -- universes `max u₁ u₃` and `max u₂ u₃`. A replacement bridge must either supply a genuinely
  -- small model for these structured-arrow categories or avoid the `uliftFunctor` descent
  -- altogether.
  sorry

-- Proof sketch: apply Lemma `7.29.6` to `f`, and use the hypothesis that `f` is an equivalence
-- of topoi to replace the lower morphism by the identity morphism of a common site `(C', J')`.
-- The source-facing statement keeps only the common site, the two dense-subsite functors, and the
-- factorization square through `MorphismOfTopoiIn.id J'`; the right-Kan-extension bridge data
-- needed to realize the induced equivalences on sheaves of sets are recorded separately below.
/-- Remark 7.29.8: if the morphism of topoi `f : Sh(J) ⟶ Sh(K)` is an equivalence, then one can
choose a common site `(C', J')` together with special cocontinuous functors
`C ⥤ C'` and `D ⥤ C'` such that the induced equivalences of sheaf topoi identify `f` with the
factorization through the identity morphism of `Sh(C', J')`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J'),
      Nonempty
        (CatCommSq
          (targetFunctor.sheafPushforwardContinuous (Type w) K J')
          ((MorphismOfTopoiIn.id J')⁻¹)
          (f⁻¹)
          (sourceFunctor.sheafPushforwardContinuous (Type w) J J')) := by
  obtain ⟨C', instC', J', sourceFunctor, hsource, targetFunctor, htarget, sq, _⟩ :=
    exists_common_site_identity_factorization_data_of_isEquivalence f
  -- The helper already packages the common-site data; only the theorem-facing `Nonempty` wrapper
  -- remains to be added.
  exact ⟨C', instC', J', sourceFunctor, hsource, targetFunctor, htarget, ⟨sq⟩⟩

-- Proof sketch: add the pointwise right-Kan-extension bridge data to the source-facing theorem
-- above, so that the two dense-subsite cocontinuous direct-image functors become equivalences on
-- `Type w`-valued sheaves. The factorization square through `MorphismOfTopoiIn.id J'` then
-- identifies the two canonical functors from `Sh(K)` to `Sh(C', J')`,
-- namely `f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous` and
-- `targetFunctor.sheafPushforwardCocontinuous`, by a natural isomorphism.
/-- Bridge companion to Remark 7.29.8: after supplying the pointwise right-Kan-extension
hypotheses needed to realize the dense-subsite cocontinuous direct-image functors as equivalences
on sheaves of sets, the source-facing factorization through `MorphismOfTopoiIn.id J'` yields the
canonical natural isomorphism
`f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous ≅
  targetFunctor.sheafPushforwardCocontinuous`. -/
theorem exists_special_cocontinuous_common_site_factorization_of_isEquivalence_canonical
    (f : MorphismOfTopoiIn K J) [(f⁻¹).IsEquivalence] :
    ∃ (C' : Type u₃) (_ : Category.{v₃} C') (J' : GrothendieckTopology C')
      (sourceFunctor : C ⥤ C') (_ : sourceFunctor.IsDenseSubsite J J')
      (_ : ∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P)
      (targetFunctor : D ⥤ C') (_ : targetFunctor.IsDenseSubsite K J')
      (_ : ∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P),
      Nonempty (
        f⁻¹ ⋙ sourceFunctor.sheafPushforwardCocontinuous (Type w) J J' ≅
          targetFunctor.sheafPushforwardCocontinuous (Type w) K J') := by
  obtain ⟨C', instC', J', sourceFunctor, hsource, hsourceKan,
      targetFunctor, htarget, htargetKan, sq, _⟩ :=
    exists_common_site_identity_factorization_data_of_isEquivalence_with_kan f
  let _ : sourceFunctor.IsDenseSubsite J J' := hsource
  let _ : ∀ P : Cᵒᵖ ⥤ Type w, sourceFunctor.op.HasPointwiseRightKanExtension P := hsourceKan
  let _ : targetFunctor.IsDenseSubsite K J' := htarget
  let _ : ∀ P : Dᵒᵖ ⥤ Type w, targetFunctor.op.HasPointwiseRightKanExtension P := htargetKan
  -- The identity-middle square is now strong enough for the cocontinuous comparison isomorphism.
  exact ⟨C', instC', J', sourceFunctor, hsource, hsourceKan,
    targetFunctor, htarget, htargetKan,
    identity_square_induces_canonical_iso f sourceFunctor targetFunctor sq⟩

end

end CategoryTheory
