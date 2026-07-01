import Mathlib
import stacks_project.Chap14.Definition_14_26_6
import stacks_project.Chap14.Definition_14_30_1
import stacks_project.Chap14.Lemma_14_30_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.SimplicialObject
open CategoryTheory.Limits.Types
open SSet (ι₀ ι₁)
open SSet.modelCategoryQuillen
open scoped MonoidalCategory Simplicial

universe u

noncomputable section

variable {X Y : SSet.{u}} {f : X ⟶ Y}

private theorem mono_coprod_desc_endpoints (X : SSet.{u}) :
    Mono (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  let c : BinaryCofan (X.obj n) (X.obj n) :=
    BinaryCofan.mk ((coprod.inl : X ⟶ X ⨿ X).app n) ((coprod.inr : X ⟶ X ⨿ X).app n)
  have hc : IsColimit c :=
    mapIsColimitOfPreservesOfIsColimit ((evaluation _ _).obj n)
      (coprod.inl : X ⟶ X ⨿ X) (coprod.inr : X ⟶ X ⨿ X) (coprodIsCoprod X X)
  let e : c.pt ≅ Sum (X.obj n) (X.obj n) :=
    hc.coconePointUniqueUpToIso (binaryCoproductColimit (X.obj n) (X.obj n))
  have hinl : c.inl ≫ e.hom = Sum.inl := by
    simpa [c] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (binaryCoproductColimit (X.obj n) (X.obj n)) ⟨WalkingPair.left⟩
  have hinr : c.inr ≫ e.hom = Sum.inr := by
    simpa [c] using
      IsColimit.comp_coconePointUniqueUpToIso_hom hc
        (binaryCoproductColimit (X.obj n) (X.obj n)) ⟨WalkingPair.right⟩
  have hinl' : Sum.inl ≫ e.inv = c.inl := by
    simpa using congrArg (fun k ↦ k ≫ e.inv) hinl.symm
  have hinr' : Sum.inr ≫ e.inv = c.inr := by
    simpa using congrArg (fun k ↦ k ≫ e.inv) hinr.symm
  have hinl_app (a : X.obj n) : e.inv (.inl a) = c.inl a := by
    simpa using congrFun hinl' a
  have hinr_app (a : X.obj n) : e.inv (.inr a) = c.inr a := by
    simpa using congrFun hinr' a
  have hcomp_inl (a : X.obj n) :
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a) = ι₀.app n a := by
    calc
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a) =
          (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (e.inv (.inl a)) := rfl
      _ = (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (c.inl a) := by rw [hinl_app]
      _ =
          ((coprod.inl : X ⟶ X ⨿ X) ≫
            coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n a := rfl
      _ = ι₀.app n a := by
          simpa using congrFun
            (congr_app (coprod.inl_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) n) a
  have hcomp_inr (a : X.obj n) :
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a) = ι₁.app n a := by
    calc
      (e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a) =
          (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (e.inv (.inr a)) := rfl
      _ = (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n (c.inr a) := by rw [hinr_app]
      _ =
          ((coprod.inr : X ⟶ X ⨿ X) ≫
            coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n a := rfl
      _ = ι₁.app n a := by
          simpa using congrFun
            (congr_app (coprod.inr_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) n) a
  have hsum :
      Function.Injective
        ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) :
          Sum (X.obj n) (X.obj n) → (X ⊗ Δ[1]).obj n) := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            have hfst : (ι₀.app n a).1 = (ι₀.app n b).1 := by
              have hfst := congrArg Prod.fst hab
              rw [hcomp_inl a, hcomp_inl b] at hfst
              exact hfst
            simpa using hfst
        | inr b =>
            exfalso
            have hsnd :
                ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a)).2 =
                  ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr b)).2 := by
              simpa using congrArg Prod.snd hab
            have hsnd0 :
                SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl a)).2 0 =
                  SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr b)).2 0 := by
              simpa [SSet.stdSimplex.asOrderHom] using
                congrArg (fun t : Δ[1].obj n ↦ SSet.stdSimplex.asOrderHom t 0) hsnd
            rw [hcomp_inl a, hcomp_inr b] at hsnd0
            have hzero :
                SSet.stdSimplex.asOrderHom ((ι₀.app n a).2) 0 = (0 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₀_app_snd_apply a 0)
            have hone :
                SSet.stdSimplex.asOrderHom ((ι₁.app n b).2) 0 = (1 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₁_app_snd_apply b 0)
            have hsnd01 : (0 : Fin 2) = 1 := hzero.symm.trans (hsnd0.trans hone)
            exact Fin.zero_ne_one hsnd01
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            have hsnd :
                ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a)).2 =
                  ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl b)).2 := by
              simpa using congrArg Prod.snd hab
            have hsnd0 :
                SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inr a)).2 0 =
                  SSet.stdSimplex.asOrderHom
                    ((e.inv ≫ (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).app n) (.inl b)).2 0 := by
              simpa [SSet.stdSimplex.asOrderHom] using
                congrArg (fun t : Δ[1].obj n ↦ SSet.stdSimplex.asOrderHom t 0) hsnd
            rw [hcomp_inr a, hcomp_inl b] at hsnd0
            have hone :
                SSet.stdSimplex.asOrderHom ((ι₁.app n a).2) 0 = (1 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₁_app_snd_apply a 0)
            have hzero :
                SSet.stdSimplex.asOrderHom ((ι₀.app n b).2) 0 = (0 : Fin 2) := by
              simpa [SSet.stdSimplex.asOrderHom] using
                (SSet.ι₀_app_snd_apply b 0)
            have hsnd01 : (1 : Fin 2) = 0 := hone.symm.trans (hsnd0.trans hzero)
            exact Fin.zero_ne_one hsnd01.symm
        | inr b =>
            have hfst : (ι₁.app n a).1 = (ι₁.app n b).1 := by
              have hfst := congrArg Prod.fst hab
              rw [hcomp_inr a, hcomp_inr b] at hfst
              exact hfst
            simpa using hfst
  intro a b hab
  apply e.toEquiv.injective
  apply hsum
  simpa using hab

/- Domain-style sampling for Lemma 14.30.8:
- primary domain: simplicial-set lifting properties and simplicial homotopy equivalences.
- sampled owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `boundaryInclusions_rlp_monomorphisms`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `SSet.Homotopy`.
- best owner abstractions:
  the source hypothesis is already canonically expressed by `I.rlp f`, and the target owner is
  `HomotopyEquiv X Y`/`IsHomotopyEquivalence f`.
- primitive data:
  the morphism `f` together with the owner property `I.rlp f`;
  the section of `f`, the endpoint subcomplex of `X ⊗ Δ[1]`, and the filler map are derived proof
  data, not new public API.
- derived API:
  the induced simplicial homotopy `f ≫ g ∼ 𝟙 X`, transported from an `SSet.Homotopy`.

Source/core/bridge triage:
- `source-facing`: a trivial Kan fibration of simplicial sets is a simplicial homotopy
  equivalence;
- `core/canonical`: the owners `I.rlp` and `HomotopyEquiv`;
- `bridge/view`: the conversion from the simplicial-set homotopy filler to the simplicial-object
  relation `Homotopic` via `SSet.Homotopy.toSimplicialObjectHomotopy`. -/

-- Proof sketch: use Lemma 14.30.2 to upgrade `hf : I.rlp f` to the right lifting property against
-- all monomorphisms. Apply this first to the initial-object inclusion to obtain a section
-- `g : Y ⟶ X` of `f`, and then to the canonical endpoint map `X ⨿ X ⟶ X ⊗ Δ[1]` induced by
-- `ι₀, ι₁`, with endpoint values `f ≫ g` and `𝟙 X`. The resulting filler is an `SSet.Homotopy`
-- from `f ≫ g` to `𝟙 X`, which yields the desired simplicial homotopy equivalence together with
-- `g ≫ f = 𝟙 Y`.
/-- Helper for Lemma 14.30.8: a morphism with the right lifting property against all
monomorphisms admits a section. -/
private theorem section_of_monomorphism_rlp (hmono : (monomorphisms SSet).rlp f) :
    ∃ g : Y ⟶ X, g ≫ f = 𝟙 Y := by
  -- Lift against the initial map to extract the right inverse promised by the source proof.
  have hSection : HasLiftingProperty (initial.to Y) f := hmono (initial.to Y) (by infer_instance)
  have sqSection : CommSq (initial.to X) (initial.to Y) f (𝟙 Y) := by
    -- The unique map out of the initial simplicial set makes the square commute tautologically.
    refine CommSq.mk ?_
    simp
  let _ : sqSection.HasLift := hSection.sq_hasLift sqSection
  refine ⟨CommSq.lift sqSection, ?_⟩
  exact CommSq.fac_right sqSection

/-- Helper for Lemma 14.30.8: the endpoint data `f ≫ g` and `𝟙 X` define the lifting square used
to produce the simplicial homotopy. -/
private theorem endpoint_square_commutes (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f) := by
  -- Check commutativity on the two coproduct summands separately.
  refine CommSq.mk ?_
  apply coprod.hom_ext
  · simp [hg, Category.assoc]
  · simp [hg, Category.assoc]

/-- Helper for Lemma 14.30.8: the lift of the endpoint square restricts to `f ≫ g` at the
`0`-endpoint. -/
private theorem endpoint_lift_h_zero (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    ι₀ ≫ CommSq.lift sqHomotopy = f ≫ g := by
  -- Compose the left factorization identity with the left coproduct injection.
  calc
    ι₀ ≫ CommSq.lift sqHomotopy =
        ((coprod.inl : X ⟶ X ⨿ X) ≫ coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) ≫
          CommSq.lift sqHomotopy := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ CommSq.lift sqHomotopy)
              (coprod.inl_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).symm
    _ = (coprod.inl : X ⟶ X ⨿ X) ≫ coprod.desc (f ≫ g) (𝟙 X) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (coprod.inl : X ⟶ X ⨿ X) ≫ k) (CommSq.fac_left sqHomotopy)
    _ = f ≫ g := by
          simpa using (coprod.inl_desc (f ≫ g) (𝟙 X))

/-- Helper for Lemma 14.30.8: the lift of the endpoint square restricts to the identity at the
`1`-endpoint. -/
private theorem endpoint_lift_h_one (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    ι₁ ≫ CommSq.lift sqHomotopy = 𝟙 X := by
  -- Compose the left factorization identity with the right coproduct injection.
  calc
    ι₁ ≫ CommSq.lift sqHomotopy =
        ((coprod.inr : X ⟶ X ⨿ X) ≫ coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) ≫
          CommSq.lift sqHomotopy := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ CommSq.lift sqHomotopy)
              (coprod.inr_desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁).symm
    _ = (coprod.inr : X ⟶ X ⨿ X) ≫ coprod.desc (f ≫ g) (𝟙 X) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (coprod.inr : X ⟶ X ⨿ X) ≫ k) (CommSq.fac_left sqHomotopy)
    _ = 𝟙 X := by
          simpa using (coprod.inr_desc (f ≫ g) (𝟙 X))

/-- Helper for Lemma 14.30.8: the relative condition for the bottom subcomplex is vacuous, so the
endpoint lift automatically satisfies it. -/
private theorem endpoint_lift_bot_relative (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    (⊥ : X.Subcomplex).ι ▷ Δ[1] ≫ CommSq.lift sqHomotopy =
      fst (⊥ : X.Subcomplex).toSSet Δ[1] ≫
        SSet.Subcomplex.isInitialBot.to (⊥ : X.Subcomplex).toSSet ≫
        (⊥ : X.Subcomplex).ι := by
  -- There are no simplices in the bottom subcomplex, so extensionality closes the goal.
  ext Δ z
  exact False.elim z.1.2

/-- Helper for Lemma 14.30.8: the endpoint lift packages into a simplicial-set homotopy from
`f ≫ g` to `𝟙 X`. -/
private noncomputable def endpoint_filler_homotopy (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    SSet.Homotopy (f ≫ g) (𝟙 X) where
  h := CommSq.lift sqHomotopy
  h₀ := endpoint_lift_h_zero (f := f) g sqHomotopy
  h₁ := endpoint_lift_h_one (f := f) g sqHomotopy
  rel := endpoint_lift_bot_relative (f := f) g sqHomotopy

/-- Helper for Lemma 14.30.8: the filler map yields the Chapter 14 homotopy relation
`f ≫ g ∼ 𝟙 X`. -/
private theorem endpoint_filler_homotopic (g : Y ⟶ X)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    Homotopic (f ≫ g) (𝟙 X) := by
  -- Convert the simplicial-set homotopy furnished by the lift into the simplicial-object one.
  exact Homotopic.of_homotopy (endpoint_filler_homotopy (f := f) g sqHomotopy).toSimplicialObjectHomotopy

/-- Helper for Lemma 14.30.8: a strict section equation already gives the second homotopy
required for a simplicial homotopy equivalence. -/
private theorem section_comp_homotopic_id (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    Homotopic (g ≫ f) (𝟙 Y) := by
  -- Rewrite the composite to the identity and use reflexivity of the homotopy relation.
  simpa [hg] using (Homotopic.refl (𝟙 Y : Y ⟶ Y))

/-- Helper for Lemma 14.30.8: the section and endpoint filler assemble into the canonical
homotopy-equivalence data. -/
private noncomputable def filler_homotopy_equiv_data (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y)
    (sqHomotopy : CommSq (coprod.desc (f ≫ g) (𝟙 X))
      (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f))
    [sqHomotopy.HasLift] :
    HomotopyEquiv X Y where
  hom := f
  inv := g
  homotopyHomInvId := endpoint_filler_homotopic (f := f) g sqHomotopy
  homotopyInvHomId := section_comp_homotopic_id (f := f) g hg

/-- Lemma 14.30.8: every trivial Kan fibration of simplicial sets is a simplicial homotopy
equivalence. -/
lemma trivialKanFibration_isHomotopyEquivalence (hf : I.rlp f) :
    IsHomotopyEquivalence f := by
  -- First upgrade the trivial Kan fibration hypothesis to lifting against all monomorphisms.
  have hmono : (monomorphisms SSet).rlp f :=
    boundaryInclusions_rlp_monomorphisms hf
  rcases section_of_monomorphism_rlp (f := f) hmono with ⟨g, hg⟩
  -- Then apply the same lifting property to the endpoint inclusion in `X ⊗ Δ[1]`.
  have hEndpoint :
      HasLiftingProperty (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f :=
    hmono (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) (mono_coprod_desc_endpoints X)
  have sqHomotopy :
      CommSq (coprod.desc (f ≫ g) (𝟙 X))
        (coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁) f (fst X Δ[1] ≫ f) :=
    endpoint_square_commutes (f := f) g hg
  let _ : sqHomotopy.HasLift := hEndpoint.sq_hasLift sqHomotopy
  -- The extracted section and the endpoint lift give the required homotopy-equivalence witness.
  exact (filler_homotopy_equiv_data (f := f) g hg sqHomotopy).isHomotopyEquivalence

end
