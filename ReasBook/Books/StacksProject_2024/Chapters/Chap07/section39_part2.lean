import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_39_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.39.2:
- primary domain: fibers of cofiltered inverse systems on a site and lifting along finite covering
  families;
- sampled owner API:
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system together with the requirement that, after refinement,
  every finite covering family lifts elements of its canonical fiber functor;
  `core/canonical`: `ofIsCofiltered.fiber` for the inverse-system fiber and
  `SemiRepresentableFamily.Over` for explicit fixed-target covering families;
  `bridge/view`: the refinement datum
  `S' ≅ (j.toOrderHom.toFunctor).op ⋙ T` and the induced natural transformation
  `refinementFiber`, together with its objectwise and raw-stalk applications.

Primitive data are only the inverse systems, the refinement datum, and the finite covering family
itself. The chapter already treats explicit covering families through `SemiRepresentableFamily.Over`
rather than the raw triple `(κ, Wk, π)`, so this file should reuse that owner and derive the
lifting clause from it instead of keeping a parallel coordinate-level encoding.
-/
open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

variable (J)

/-- Helper for Lemma 7.39.2: one finite-cover lifting obligation for the inverse-system fiber of
`S`. -/
structure finite_cover_lift_request (S : ιᵒᵖ ⥤ C) where
  W : C
  𝒰 : SemiRepresentableFamily.Over.{w} W
  finite_index : Finite 𝒰.index
  h𝒰 : 𝒰.toSieve ∈ J W
  f : (fiber.{max u v w} S).obj W

attribute [instance] finite_cover_lift_request.finite_index

variable {J}

/-- Helper for Lemma 7.39.2: a refinement solves a fixed lifting request when the transported
fiber element lifts through one member of the chosen finite covering family. -/
def request_solved {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S)
    {ι' : Type w} [Preorder ι'] (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) : Prop :=
  ∃ i : r.𝒰.index, ∃ y : (fiber.{max u v w} T).obj (r.𝒰.obj i).left,
    (fiber.{max u v w} T).map (r.𝒰.obj i).hom y =
      (refinementFiber j T e).app r.W r.f

/-- Helper for Lemma 7.39.2: transport one finite-cover lifting request along a refinement of
inverse systems. -/
noncomputable def transport_request {S : ιᵒᵖ ⥤ C}
    {ι' : Type w} [Preorder ι'] (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C)
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) (r : finite_cover_lift_request J S) :
    finite_cover_lift_request J T where
  W := r.W
  𝒰 := r.𝒰
  finite_index := r.finite_index
  h𝒰 := r.h𝒰
  f := (refinementFiber j T e).app r.W r.f

/-- Helper for Lemma 7.39.2: a request is realized on its own stage if its fiber element lifts
through one member of the chosen finite covering family. -/
def request_realized {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S) : Prop :=
  ∃ i : r.𝒰.index, ∃ y : (fiber.{max u v w} S).obj (r.𝒰.obj i).left,
    (fiber.{max u v w} S).map (r.𝒰.obj i).hom y = r.f

/-- Helper for Lemma 7.39.2: solving a request after refinement is the same as realizing its
transported request on the refined stage. -/
@[simp] theorem request_solved_iff_request_realized_transport
    {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S)
    {ι' : Type w} [Preorder ι'] (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) :
    request_solved r T j e ↔ request_realized (transport_request (J := J) j T e r) :=
  Iff.rfl

/-- Helper for Lemma 7.39.2: realization of a lifting request persists after further refinement. -/
theorem request_realized_transport
    {S : ιᵒᵖ ⥤ C} {ι' : Type w} [Preorder ι'] (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C)
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) (r : finite_cover_lift_request J S) :
    request_realized (J := J) r →
      request_realized (J := J) (transport_request (J := J) j T e r) := by
  intro hr
  rcases hr with ⟨i, y, hy⟩
  refine ⟨i, (refinementFiber j T e).app _ y, ?_⟩
  -- Naturality transports the local lifting witness to the refined inverse-system fiber.
  have hnat :
      (fiber.{max u v w} T).map (r.𝒰.obj i).hom ((refinementFiber j T e).app _ y) =
        (refinementFiber j T e).app r.W ((fiber.{max u v w} S).map (r.𝒰.obj i).hom y) := by
    simpa using (congrFun ((refinementFiber j T e).naturality (r.𝒰.obj i).hom) y).symm
  exact hnat.trans (congrArg ((refinementFiber j T e).app r.W) hy)

-- Proof sketch: this is exactly the successor step of the source proof. Package one lifting
-- obligation into `finite_cover_lift_request`, then invoke Lemma 7.39.1 on the current stage.
/-- Helper for Lemma 7.39.2: one application of Lemma 7.39.1 extends the current inverse system
so that the images of the chosen sections stay distinct and the chosen lifting request is solved. -/
theorem stage_extend_by_request
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S).presheafFiber).obj ℱ}
    (hss' : s ≠ s')
    (r : finite_cover_lift_request J S) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        request_solved r T j e := by
  -- Apply the single-request refinement lemma to the packaged covering family and fiber element.
  rcases exists_refined_inverse_system_separating_sections_and_lifting_cover
      (J := J) S hss' r.𝒰 r.h𝒰 r.f with
    ⟨ι', hι', hdir, T, j, e, hsep, hsolve⟩
  refine ⟨ι', hι', hdir, T, j, e, hsep, ?_⟩
  -- The conclusion of Lemma 7.39.1 is exactly the `request_solved` predicate by definition.
  simpa [request_solved] using hsolve

/-- Helper for Lemma 7.39.2: compose two refinement order embeddings. -/
def compose_refinement_embedding
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    (j : ι ↪o ι') (k : ι' ↪o ι'') : ι ↪o ι'' where
  toFun := fun i ↦ k (j i)
  inj' := fun _ _ hij ↦ j.injective (k.injective hij)
  map_rel_iff' := by
    intro i i'
    exact k.map_rel_iff.trans j.map_rel_iff

/-- Helper for Lemma 7.39.2: compose the base refinement with a further refinement of the current
stage. -/
noncomputable def compose_refinement_iso
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U) :
    S ≅ ((compose_refinement_embedding j k).toOrderHom.toFunctor).op ⋙ U := by
  -- The new identification is the old one followed by the refinement of the current stage.
  refine e ≪≫ Functor.isoWhiskerLeft _ e' ≪≫ ?_
  simpa [compose_refinement_embedding] using
    (Functor.associator (j.toOrderHom.toFunctor).op (k.toOrderHom.toFunctor).op U)

namespace GrothendieckTopology.Point.ofIsCofiltered

/-- Helper for Lemma 7.39.2: successive refinements induce the same map on inverse-system fibers
as the composed refinement. -/
theorem refinementFiber_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U) :
    refinementFiber (compose_refinement_embedding j k) U (compose_refinement_iso j k e e') =
      refinementFiber j T e ≫ refinementFiber k U e' := by
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨V, f, rfl⟩
  -- Both sides are determined on the canonical fiber generators `fiberMk f`.
  simp [refinementFiber_app_fiberMk, compose_refinement_iso,
    compose_refinement_embedding, Category.assoc]

end GrothendieckTopology.Point.ofIsCofiltered

/-- Helper for Lemma 7.39.2: transporting one request along two successive refinements is the
same as transporting it directly along the composed refinement. -/
theorem transport_request_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U)
    (r : finite_cover_lift_request J S) :
    transport_request (J := J) (compose_refinement_embedding j k) U
        (compose_refinement_iso j k e e') r =
      transport_request (J := J) k U e' (transport_request (J := J) j T e r) := by
  cases r
  -- Only the transported fiber element changes, and `refinementFiber_comp` identifies it.
  simp [transport_request,
    GrothendieckTopology.Point.ofIsCofiltered.refinementFiber_comp]

/-- Helper for Lemma 7.39.2: on a fixed presheaf, the `presheafFiber` map induced by a composite
refinement is the composite of the two induced maps. -/
theorem refinementFiber_presheafFiber_app_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U)
    (F : Cᵒᵖ ⥤ Type (max u v w)) :
    ((refinementFiber j T e ≫ refinementFiber k U e').presheafFiber).app F =
      ((refinementFiber j T e).presheafFiber ≫ (refinementFiber k U e').presheafFiber).app F := by
  -- Compare both maps on the generators of the source presheaf fiber.
  apply (fiber.{max u v w} S).presheafFiber_hom_ext
  intro X x
  -- Evaluate both sides on one generator and normalize each step with
  -- `toPresheafFiber_presheafFiber_app`.
  calc
    (fiber.{max u v w} S).toPresheafFiber X x F ≫
        ((refinementFiber j T e ≫ refinementFiber k U e').presheafFiber).app F =
      (fiber.{max u v w} U).toPresheafFiber X
        (((refinementFiber j T e ≫ refinementFiber k U e').app X) x) F := by
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber j T e ≫ refinementFiber k U e') (F := F) X x
    _ =
      (fiber.{max u v w} U).toPresheafFiber X
        ((refinementFiber k U e').app X ((refinementFiber j T e).app X x)) F := by
          rfl
    _ =
      (fiber.{max u v w} T).toPresheafFiber X ((refinementFiber j T e).app X x) F ≫
        ((refinementFiber k U e').presheafFiber).app F := by
          symm
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber k U e') (F := F) X ((refinementFiber j T e).app X x)
    _ =
      (fiber.{max u v w} S).toPresheafFiber X x F ≫
        ((refinementFiber j T e).presheafFiber).app F ≫
          ((refinementFiber k U e').presheafFiber).app F := by
          rw [← Category.assoc]
          congr 1
          symm
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber j T e) (F := F) X x

/-- Helper for Lemma 7.39.2: a packaged refinement stage over the original system, together with
the requests already forced on that stage. -/
structure refinement_stage
    (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    (s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ) where
  I : Type w
  instPreorder : Preorder I
  instDirected : IsDirected I (· ≤ ·)
  T : Iᵒᵖ ⥤ C
  j : ι ↪o I
  e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T
  separated :
    ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
      (Type (max u v w))).obj ℱ) s ≠
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s'
  solved : Set (finite_cover_lift_request J T)
  solved_realized :
    ∀ ⦃r : finite_cover_lift_request J T⦄, r ∈ solved → request_realized (J := J) r

attribute [instance] refinement_stage.instPreorder refinement_stage.instDirected

/-- Helper for Lemma 7.39.2: the identity order embedding gives the trivial refinement of an
inverse system. -/
noncomputable def identity_refinement_iso (S' : ιᵒᵖ ⥤ C) :
    S' ≅
      ((show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩).toOrderHom.toFunctor).op ⋙ S' := by
  -- The identity refinement is just the left unitor for functor composition.
  simpa using (Functor.leftUnitor S').symm

/-- Helper for Lemma 7.39.2: the trivial refinement acts as the identity on inverse-system
fibers. -/
theorem refinementFiber_identity
    (S' : ιᵒᵖ ⥤ C) :
    refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S') =
      𝟙 (fiber.{max u v w} S') := by
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨U, f, rfl⟩
  -- The identity refinement sends each generator to itself.
  simp [identity_refinement_iso, refinementFiber_app_fiberMk]

/-- Helper for Lemma 7.39.2: the base stage preserves the original separation hypothesis because
the trivial refinement induces the identity on sheaf fibers. -/
theorem identity_refinement_preserves_separation
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S')).presheafFiber).app
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s ≠
    ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S')).presheafFiber).app
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s' := by
  -- After identifying the trivial refinement map with the identity, this is exactly `hss'`.
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  have hpresheafIdentity :
      (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj = 𝟙 _ := by
    -- The induced map on raw sheaf fibers is determined by the canonical generators.
    apply (fiber.{max u v w} S').presheafFiber_hom_ext
    intro X x
    calc
      (fiber.{max u v w} S').toPresheafFiber X x Fobj ≫
          (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj =
        (fiber.{max u v w} S').toPresheafFiber X
          ((show fiber.{max u v w} S' ⟶ fiber.{max u v w} S' from 𝟙 _).app X x) Fobj := by
            simpa using NatTrans.toPresheafFiber_presheafFiber_app
              (η := 𝟙 (fiber.{max u v w} S')) (F := Fobj) X x
      _ = (fiber.{max u v w} S').toPresheafFiber X x Fobj := by
            rfl
      _ = (fiber.{max u v w} S').toPresheafFiber X x Fobj ≫ 𝟙 _ := by
            simp
  rw [show ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
      (identity_refinement_iso (ι := ι) S')).presheafFiber).app Fobj =
      (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj by
        simpa [Fobj, refinementFiber_identity (ι := ι) (S' := S')]
  ]
  rw [hpresheafIdentity]
  simpa using hss'

/-- Helper for Lemma 7.39.2: the empty solved set satisfies the `solved_realized` field
vacuously. -/
theorem empty_solved_requests_realized
    {S' : ιᵒᵖ ⥤ C} :
    ∀ ⦃r : finite_cover_lift_request J S'⦄,
      r ∈ (∅ : Set (finite_cover_lift_request J S')) → request_realized (J := J) r := by
  intro r hr
  simpa using hr

/-- Helper for Lemma 7.39.2: the initial packaged stage is the original inverse system with no
scheduled lifting requests solved yet. -/
noncomputable def base_refinement_stage
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    [IsDirected ι (· ≤ ·)] (hss' : s ≠ s') :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' := {
  I := ι
  instPreorder := inferInstance
  instDirected := inferInstance
  T := S'
  j := ⟨Function.Embedding.refl _, Iff.rfl⟩
  e := identity_refinement_iso (ι := ι) S'
  separated := identity_refinement_preserves_separation (J := J) (ι := ι) (S' := S') hss'
  solved := ∅
  solved_realized := empty_solved_requests_realized (J := J)
}

/-- Helper for Lemma 7.39.2: a global code for one stage-relative finite-cover lifting request. -/
abbrev request_code
    (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    (s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ) :=
  Σ A : refinement_stage (J := J) S' (ℱ := ℱ) s s', finite_cover_lift_request J A.T

/-- Helper for Lemma 7.39.2: a morphism of packaged stages is a further refinement that transports
every previously solved request to a solved request on the larger stage. -/
structure refinement_stage_hom
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A B : refinement_stage (J := J) S' (ℱ := ℱ) s s') where
  k : A.I ↪o B.I
  hT : A.T ≅ (k.toOrderHom.toFunctor).op ⋙ B.T
  solved_mono :
    ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ A.solved →
      transport_request (J := J) k B.T hT r ∈ B.solved

/-- Helper for Lemma 7.39.2: transporting a request along the identity refinement leaves the
request unchanged. -/
theorem transport_request_identity
    {S' : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S') :
    transport_request (J := J)
        (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S') r = r := by
  cases r
  -- The only nontrivial field is the transported fiber element, and the identity refinement fixes it.
  simp [transport_request, refinementFiber_identity (ι := ι) (S' := S')]

/-- Helper for Lemma 7.39.2: every packaged stage has the obvious identity self-refinement. -/
noncomputable def refinement_stage_hom_refl
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    refinement_stage_hom (J := J) A A where
  k := ⟨Function.Embedding.refl _, Iff.rfl⟩
  hT := identity_refinement_iso (ι := A.I) A.T
  solved_mono := by
    intro r hr
    -- The identity stage morphism does not change the transported request.
    simpa [transport_request_identity (J := J) (ι := A.I) r] using hr

namespace refinement_stage_hom

/-- Helper for Lemma 7.39.2: transport one request along a morphism of packaged stages. -/
noncomputable def map_request
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) (r : finite_cover_lift_request J A.T) :
    finite_cover_lift_request J B.T :=
  transport_request (J := J) h.k B.T h.hT r

/-- Helper for Lemma 7.39.2: a realized request remains realized after transporting it along a
stage morphism. -/
theorem map_request_realized
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) (r : finite_cover_lift_request J A.T) :
    request_realized (J := J) r →
      request_realized (J := J) (h.map_request r) := by
  -- This is the request-transport monotonicity needed in the successor and union steps.
  exact request_realized_transport (J := J) h.k B.T h.hT r

/-- Helper for Lemma 7.39.2: compose two morphisms of packaged stages. -/
noncomputable def comp
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D) :
    refinement_stage_hom (J := J) A D where
  k := compose_refinement_embedding hAB.k hBD.k
  hT := compose_refinement_iso hAB.k hBD.k hAB.hT hBD.hT
  solved_mono := by
    intro r hr
    -- Rewrite the two-step transport as the direct composite transport, then use monotonicity
    -- along each stage morphism once.
    have hmid : hAB.map_request r ∈ B.solved := hAB.solved_mono hr
    rw [show transport_request (J := J) (compose_refinement_embedding hAB.k hBD.k) D.T
          (compose_refinement_iso hAB.k hBD.k hAB.hT hBD.hT) r =
        transport_request (J := J) hBD.k D.T hBD.hT (hAB.map_request r) by
          simpa [map_request] using
            transport_request_comp (J := J) hAB.k hBD.k hAB.hT hBD.hT r]
    exact hBD.solved_mono hmid

end refinement_stage_hom

/-- Helper for Lemma 7.39.2: packaged refinement stages are ordered by existence of a stage
morphism. -/
instance refinement_stage_preorder
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ} :
    Preorder (refinement_stage (J := J) S' (ℱ := ℱ) s s') where
  le A B := Nonempty (refinement_stage_hom (J := J) A B)
  le_refl A := by
    -- Every stage refines itself by the identity stage morphism.
    exact ⟨refinement_stage_hom_refl (J := J) A⟩
  le_trans A B D hAB hBD := by
    rcases hAB with ⟨hAB⟩
    rcases hBD with ⟨hBD⟩
    -- Compose the two refinement morphisms to obtain the transitive comparison.
    exact ⟨refinement_stage_hom.comp (J := J) hAB hBD⟩

/-- Helper for Lemma 7.39.2: any two members of a chain admit a common successor inside the
same chain. -/
theorem chain_common_successor
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {c : Set (refinement_stage (J := J) S' (ℱ := ℱ) s s')}
    (_hcne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A ∈ c) (hB : B ∈ c) :
    ∃ D ∈ c,
      Nonempty (refinement_stage_hom (J := J) A D) ∧
        Nonempty (refinement_stage_hom (J := J) B D) := by
  -- In a chain, either `A ≤ B` or `B ≤ A`; choose the later stage as the common successor.
  rcases hchain.total hA hB with hAB | hBA
  · refine ⟨B, hB, hAB, ?_⟩
    -- The later stage always maps to itself by the identity stage morphism.
    exact ⟨refinement_stage_hom_refl (J := J) B⟩
  · refine ⟨A, hA, ?_, hBA⟩
    -- Symmetrically, if `B ≤ A`, then `A` is the common successor.
    exact ⟨refinement_stage_hom_refl (J := J) A⟩

namespace refinement_stage_hom

/-- Helper for Lemma 7.39.2: if a request is already marked solved on a stage, then after
transporting it along any stage morphism it is realized on the target stage. -/
theorem map_request_realized_of_mem_solved
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B)
    {r : finite_cover_lift_request J A.T} (hr : r ∈ A.solved) :
    request_realized (J := J) (h.map_request r) := by
  -- First transport solvedness along the stage morphism, then use the target-stage invariant.
  exact B.solved_realized (h.solved_mono hr)

end refinement_stage_hom

-- Proof sketch: repackage the one-step extension theorem at the level of packaged stages by
-- transporting the previously solved requests to the larger stage and adding the new request.
/-- Helper for Lemma 7.39.2: extend a packaged stage by one additional request while preserving
all previously solved requests. -/
theorem extend_stage_by_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B, h.map_request r ∈ B.solved := by
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let sA := ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj s
  let sA' := ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj s'
  have hAsep : sA ≠ sA' := by
    -- The current stage already separates the transported images of `s` and `s'`.
    simpa [sA, sA', Fobj] using A.separated
  rcases stage_extend_by_request (J := J) A.T (ℱ := ℱ) (s := sA) (s' := sA') hAsep r with
    ⟨I', hI', hdir', U, k, e', hsep, hsolve⟩
  let B : refinement_stage (J := J) S' (ℱ := ℱ) s s' := {
    I := I'
    instPreorder := hI'
    instDirected := hdir'
    T := U
    j := compose_refinement_embedding A.j k
    e := compose_refinement_iso A.j k A.e e'
    separated := by
      -- Route correction: the successor stage separates `s` and `s'` through the composed
      -- refinement, so we normalize that composite map before applying the one-step result.
      have hsepMap :
          ((refinementFiber (compose_refinement_embedding A.j k) U
              (compose_refinement_iso A.j k A.e e')).presheafFiber).app Fobj =
            ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj ≫
              ((refinementFiber k U e').presheafFiber).app Fobj := by
        calc
          ((refinementFiber (compose_refinement_embedding A.j k) U
              (compose_refinement_iso A.j k A.e e')).presheafFiber).app Fobj =
              ((refinementFiber A.j A.T A.e ≫ refinementFiber k U e').presheafFiber).app
                Fobj := by
                  simpa using congrArg (fun η => η.presheafFiber.app Fobj)
                    (GrothendieckTopology.Point.ofIsCofiltered.refinementFiber_comp
                      A.j k A.e e')
          _ = ((refinementFiber A.j A.T A.e).presheafFiber ≫
                (refinementFiber k U e').presheafFiber).app Fobj := by
                  simpa using refinementFiber_presheafFiber_app_comp
                    (j := A.j) (k := k) (e := A.e) (e' := e') Fobj
          _ = ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj ≫
                ((refinementFiber k U e').presheafFiber).app Fobj := by
                  rfl
      intro hEq
      have hEq' :
          ((refinementFiber k U e').presheafFiber).app Fobj sA =
            ((refinementFiber k U e').presheafFiber).app Fobj sA' := by
        have hEqMap :
            ((((refinementFiber A.j A.T A.e).presheafFiber).app Fobj) ≫
                (((refinementFiber k U e').presheafFiber).app Fobj)) s =
              ((((refinementFiber A.j A.T A.e).presheafFiber).app Fobj) ≫
                (((refinementFiber k U e').presheafFiber).app Fobj)) s' := by
          -- Rewrite the composed refinement map into the normalized two-step composite.
          rw [← hsepMap]
          exact hEq
        simpa [sA, sA', Fobj] using hEqMap
      exact hsep hEq'
    solved :=
      {r' | ∃ r₀ : finite_cover_lift_request J A.T,
          r₀ ∈ A.solved ∧ transport_request (J := J) k U e' r₀ = r'} ∪
        {transport_request (J := J) k U e' r}
    solved_realized := by
      intro r' hr'
      rcases hr' with hr' | hr'
      · rcases hr' with ⟨r₀, hr₀, rfl⟩
        -- Previously solved requests stay realized after transporting them to the successor stage.
        exact request_realized_transport (J := J) k U e' r₀ (A.solved_realized hr₀)
      · rcases Set.mem_singleton_iff.mp hr' with rfl
        -- The new request is realized by the one-step extension theorem.
        simpa [request_solved_iff_request_realized_transport] using hsolve
  }
  refine ⟨B, ?_⟩
  refine ⟨{ k := k, hT := e', solved_mono := ?_ }, ?_⟩
  · intro r₀ hr₀
    -- By construction, all old solved requests are transported into the new solved set.
    exact Or.inl ⟨r₀, hr₀, rfl⟩
  · -- The chosen request is added to the solved set at the successor stage.
    exact Or.inr (Set.mem_singleton _)

/-- Helper for Lemma 7.39.2: once an earlier-stage request has been transported into the current
prefix stage, the successor constructor is just `extend_stage_by_request` on that transported
request. -/
noncomputable def next_stage_for_scheduled_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  Classical.choose <| extend_stage_by_request (J := J) L (h.map_request r)

/-- Helper for Lemma 7.39.2: the current prefix stage maps canonically into the successor stage
obtained by solving one transported request. -/
noncomputable def next_stage_for_scheduled_request_hom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    refinement_stage_hom (J := J) L (next_stage_for_scheduled_request (J := J) A₀ L h r) :=
  Classical.choose <| Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))

/-- Helper for Lemma 7.39.2: the scheduled request is solved at the successor stage produced from
the current prefix stage. -/
theorem next_stage_for_scheduled_request_solved
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).map_request (h.map_request r) ∈
      (next_stage_for_scheduled_request (J := J) A₀ L h r).solved := by
  -- Unpack the witness returned by `extend_stage_by_request` for the transported request.
  exact Classical.choose_spec <|
    Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))

/-- Helper for Lemma 7.39.2: if a packaged refinement stage realizes every request on its own
fiber functor, then that stage already supplies the theorem's final refinement. -/
theorem stage_realizing_all_requests_yields_target
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hA : ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := by
  refine ⟨A.I, inferInstance, inferInstance, A.T, A.j, A.e, ?_⟩
  refine ⟨A.separated, ?_⟩
  intro W 𝒰 _ h𝒰 f
  -- Package the final-stage lifting problem as one request and apply the stage hypothesis.
  let r : finite_cover_lift_request J A.T := {
    W := W
    𝒰 := 𝒰
    finite_index := inferInstance
    h𝒰 := h𝒰
    f := f
  }
  simpa [r, request_realized] using hA r

/-- Helper for Lemma 7.39.2: the remaining source-faithful construction is to produce a terminal
packaged refinement stage whose own finite-cover requests are all realized. -/
theorem exists_terminal_refinement_stage_realizing_all_requests
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r := by
  -- Route correction: the generated Lean target quantifies over the final refined fiber itself,
  -- so the unresolved step is exactly the stage-aware transfinite/Zorn construction that forces
  -- every request on the terminal stage to factor through an earlier scheduled one.
  --
  -- TODO: use `chain_common_successor` to build the sigma-union upper bound for a nonempty chain,
  -- prove that its separatedness descends along a later chain member via filtered-colimit
  -- equality reflection, and then apply Zorn to obtain a maximal stage.
  sorry

-- Proof sketch: well-order the class of pairs consisting of a finite covering family and an
-- element of `u'(W)`, then iterate Lemma 7.39.1 by transfinite recursion so that each stage
-- preserves the separation of `s` and `s'` while forcing the lifting condition for the next pair.
-- The directed union of the resulting chain is again a refinement of the original directed system,
-- and the induced canonical maps still separate `s` and `s'` while satisfying the required
-- finite-cover lifting property for every stage of the well-order.
/-- Lemma 7.39.2: given a directed inverse system on a site and two distinct elements of the
canonical raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf, there exists a refinement of the inverse system whose induced canonical map on sheaf
fibers still separates those elements and whose refined object fiber functor has the property that
every element over an object lifts through some member of any finite covering family of that
object. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_all_finite_covers
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := by
  -- Reduce the theorem to the existence of a terminal packaged stage realizing all of its own
  -- finite-cover lifting requests.
  rcases exists_terminal_refinement_stage_realizing_all_requests
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' with
    ⟨A, hA⟩
  exact stage_realizing_all_requests_yields_target (J := J) (A := A) hA

end

end CategoryTheory

/-! ### Proposition_7_39_3 (from Chap07) -/
universe u v

namespace CategoryTheory

open Opposite
open GrothendieckTopology
open GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] initiallySmall_of_essentiallySmall

/- Domain-style sampling for Proposition 7.39.3:
- primary domain: enough points on a Grothendieck site, built from point fibers of cofiltered
  inverse systems and the canonical conservative-family criterion;
- sampled owner API:
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `GrothendieckTopology.isConservativePointFamily_iff_exists_point_separating_sections`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `HasFiniteRefinementProperty`;
- source/core/bridge triage:
  `source-facing`: the site-level theorem that the finite-refinement hypothesis implies enough
    points;
  `core/canonical`: `J.HasEnoughPoints` and the owner notion `GrothendieckTopology.Point`;
  `bridge/view`: the separation criterion for conservative families of points and the
    inverse-system fiber construction used to manufacture the required points.

Primitive data are only the finite-limit hypothesis on `C` and the source-facing finite-refinement
assumption `∀ X, J.HasFiniteRefinementProperty X`. Conservative-family packaging and the passage
from a cofiltered inverse system to a point are derived API from the owner layer above, so this
file should stay a thin theorem at the `HasEnoughPoints` owner rather than introducing any local
wrapper around conservative point families or point data.
-/
/-- Helper for Proposition 7.39.3: the raw presheaf fiber map attached to the trivial one-object
inverse system is injective, so distinct sections remain distinct before applying
Lemma 7.39.2. -/
lemma trivial_inverse_system_toPresheafFiber_injective
    {ℱ : Sheaf J (Type (max u v))} (U : C) :
    let I₀ := ULift.{max u v} PUnit
    let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
    let x₀ : (fiber.{max u v} S₀).obj U :=
      fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
    Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj) := by
  let I₀ := ULift.{max u v} PUnit
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  change Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj)
  intro s s' hss
  let u₀ : C ⥤ Type (max u v) := fiber.{max u v} S₀
  have hpullback :
      ∃ (Y : C) (f : Y ⟶ U) (y : u₀.obj Y), u₀.map f y = x₀ ∧
        ℱ.obj.map f.op s = ℱ.obj.map f.op s' := by
    -- Compare the two germs by the canonical point-fiber equality criterion.
    simpa [u₀] using
      ((fiber.{max u v} S₀).toPresheafFiber_eq_iff' U x₀ s s').1 hss
  obtain ⟨Y, f, y, hy, hpullback⟩ := hpullback
  -- Represent the witness `y` by an actual stage map in the one-object inverse system.
  obtain ⟨V, g, rfl⟩ := fiberMk_jointly_surjective y
  have hfiberMk :
      fiberMk.{max u v} (g ≫ f) = fiberMk.{max u v} (𝟙 U) := by
    simpa [x₀, u₀] using hy
  -- Since the indexing category has one object, that pullback arrow has a section.
  obtain ⟨W, q, hq⟩ := exists_of_fiberMk_eq_fiberMk (p := S₀) hfiberMk
  have hsection : g ≫ f = 𝟙 U := by
    simpa [S₀] using hq
  -- Apply the section to the pullback equality to recover equality of the original sections.
  calc
    s = ℱ.obj.map (g ≫ f).op s := by simpa [hsection]
    _ = ℱ.obj.map g.op (ℱ.obj.map f.op s) := by simp
    _ = ℱ.obj.map g.op (ℱ.obj.map f.op s') := by rw [hpullback]
    _ = ℱ.obj.map (g ≫ f).op s' := by simp
    _ = s' := by simpa [hsection]

/-- Helper for Proposition 7.39.3: once every finite covering family lifts elements of the fiber
functor, the finite-refinement hypothesis upgrades that to the covering-sieve lifting condition
needed in Proposition 7.33.3. -/
lemma coversLiftToFunctorFibers_of_finite_family_lifting
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
    {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [InitiallySmall ιᵒᵖ] (T : ιᵒᵖ ⥤ C)
    (hlift :
      ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} W) [Finite 𝒰.index],
        𝒰.toSieve ∈ J W →
          ∀ f : (fiber.{max u v} T).obj W,
            ∃ i : 𝒰.index, ∃ y : (fiber.{max u v} T).obj (𝒰.obj i).left,
              (fiber.{max u v} T).map (𝒰.obj i).hom y = f) :
    CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
  intro W R hR f
  -- Refine the arbitrary covering sieve by a finite covering family.
  obtain ⟨𝒱, h𝒱fin, h𝒱, hle⟩ :=
    (hfinite W).finite_refinement (R : Presieve W) (by simpa using hR)
  have hle' : 𝒱.toSieve ≤ R := by
    simpa using hle
  let _ : Finite 𝒱.index := h𝒱fin
  -- The assumed finite-family lifting produces a lift through one member of that refinement.
  obtain ⟨i, y, hy⟩ := hlift (W := W) 𝒱 h𝒱 f
  refine ⟨(𝒱.obj i).left, (𝒱.obj i).hom, ?_, y, hy⟩
  have hi : 𝒱.toSieve (𝒱.obj i).hom := by
    exact (Sieve.le_generate 𝒱.toPresieve) _ _ (Presieve.ofArrows.mk i)
  exact hle' _ hi

/-- Helper for Proposition 7.39.3: every unequal pair of sections of a set-valued sheaf is
separated by the germs at some point obtained from the refinement construction of Lemma 7.39.2. -/
lemma exists_point_separating_sections_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
  {ℱ : Sheaf J (Type (max u v))} (U : C) (s s' : ℱ.obj.obj (op U))
    (hs : s ≠ s') :
    ∃ p : GrothendieckTopology.Point.{max u v} J, ∃ x : p.fiber.obj U,
      p.toPresheafFiber U x ℱ.obj s ≠ p.toPresheafFiber U x ℱ.obj s' := by
  let I₀ := ULift.{max u v} PUnit
  letI : IsDirected I₀ (· ≤ ·) := ⟨fun _ _ ↦ ⟨ULift.up PUnit.unit, trivial, trivial⟩⟩
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  let a : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s
  let a' : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s'
  have hraw : a ≠ a' := by
    -- The trivial inverse system records the original sections faithfully.
    intro haa'
    exact hs ((trivial_inverse_system_toPresheafFiber_injective (J := J) (ℱ := ℱ) U) haa')
  -- Route correction: keep the source proof's trivial-system-to-refinement architecture rather
  -- than replacing it with a direct conservative-family argument.
  obtain ⟨ι', _, _, T, j, e, hsep, hlift⟩ :=
    exists_refined_inverse_system_separating_sections_and_lifting_all_finite_covers
      (J := J) (S' := S₀) (ℱ := ℱ) (s := a) (s' := a') hraw
  have hcover : CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
    -- Upgrade the finite-cover lifting output of Lemma 7.39.2 to arbitrary coverings.
    exact coversLiftToFunctorFibers_of_finite_family_lifting (J := J) hfinite T hlift
  obtain ⟨p, rfl⟩ :=
    (exists_point_with_fiber_iff_preservesFiniteLimits_and_covering_jointlySurjective
      (J := J) (u := fiber.{max u v} T)).2
      ⟨inferInstance, hcover⟩
  refine ⟨_, (refinementFiber j T e).app U x₀, ?_⟩
  -- The separating raw-fiber inequality is exactly the inequality of germs at the refined point.
  simpa [a, a'] using hsep

/-- Helper for Proposition 7.39.3: once a family of points separates every unequal pair of
sections, Lemma 7.38.3 identifies that family as conservative. -/
lemma section_separating_family_isConservative
    {ι : Type _}
    (p : ι → GrothendieckTopology.Point.{max u v} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s') :
    (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
  -- TODO: re-establish Lemma 7.38.3 in this dependency closure by reconstructing the missing
  -- stalk-faithfulness bridge from separating sections, or repair the broken earlier file
  -- `Lemma_7_38_3.lean` and import its owner theorem here.
  sorry

-- Proof sketch: for any two distinct sections of a sheaf, start with the trivial one-object
-- inverse system at the ambient object and apply Lemma 7.39.2 to obtain a refined inverse system
-- that still separates the sections and whose associated fiber functor is jointly surjective for
-- every finite covering family. The finite-refinement hypothesis upgrades this to all covering
-- families, so Proposition 7.33.3 turns the resulting functor into a point; Lemma 7.38.3 then
-- shows that the resulting family of points is conservative.
/-- Proposition 7.39.3: if finite limits exist in `C` and every covering family in `(C, J)`
admits a finite covering refinement, then `(C, J)` has enough points. -/
theorem hasEnoughPoints_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    J.HasEnoughPoints := by
  classical
  let ι :=
    Σ (ℱ : Sheaf J (Type (max u v))) (U : C),
      { ss : ℱ.obj.obj (op U) × ℱ.obj.obj (op U) // ss.1 ≠ ss.2 }
  let p : ι → GrothendieckTopology.Point.{max u v} J
    | ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩ =>
        Classical.choose <|
          exists_point_separating_sections_of_finite_cover_refinement
            (J := J) (ℱ := ℱ) hfinite U s s' hs
  have hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s' := by
    intro ℱ U s s' hs
    let i : ι := ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩
    refine ⟨i, ?_⟩
    -- Index the conservative family by all unequal pairs of sections and use the chosen witness.
    simpa [p, i] using
      (Classical.choose_spec <|
        exists_point_separating_sections_of_finite_cover_refinement
          (J := J) (ℱ := ℱ) hfinite U s s' hs)
  have hconservative : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
    -- First record the verified source-faithful frontier: the chosen family is conservative.
    exact section_separating_family_isConservative (J := J) p hsep
  -- Package the conservative family through the owner-level enough-points bridge.
  have hEnough :
      GrothendieckTopology.HasEnoughPoints.{max (max (u + 1) (v + 1)) u v} J := by
    -- The owner theorem accepts a conservative family indexed in the same universe as `ι`.
    exact
    (GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily
      (J := J) (w := max (max (u + 1) (v + 1)) u v)).2 ⟨ι, p, hconservative⟩
  exact hEnough

end CategoryTheory

/-! ### Lemma_7_39_4 (from Chap07) -/
universe w v u

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/- Domain-style sampling for Lemma 7.39.4:
- primary domain: enough points on a Grothendieck site via a family covering the terminal object
  and enough points on the corresponding slice sites;
- sampled owner API:
  `GrothendieckTopology.CoversTop`,
  `GrothendieckTopology.HasEnoughPoints`,
  `hasEnoughPoints_of_covering_family_and_slice_sites`,
  `hasEnoughPoints_of_finite_cover_refinement`;
- best owner abstraction: `J.HasEnoughPoints`, with the covering-family input expressed by the
  canonical owner `J.CoversTop U`;
- source/core/bridge triage:
  `source-facing`: this lemma combines a covering family of localizations with the slice-site
    finite-refinement hypothesis from Proposition 7.39.3;
  `core/canonical`: `J.HasEnoughPoints`, `J.CoversTop U`, and
    `(J.over (U i)).HasFiniteRefinementProperty`;
  `bridge/view`: Proposition 7.39.3 produces enough points on each slice site, and Lemma 7.38.5
    transports those slice points back to points of `(C, J)`.

Primitive data are only the canonical cover-family owner `J.CoversTop U` and the slice-site
finite-refinement hypotheses. The enough-points structure on each slice is derived API from
Proposition 7.39.3, so this file should stay a thin composition theorem rather than restating the
cover-family hypothesis in an ad hoc `∃ S : J.Cover W, ...` form.
-/
-- Proof sketch: the first hypothesis is the site-level form of the statement that the coproduct of
-- the representables `h_{U i}` surjects onto the terminal sheaf. For each `i`, apply Proposition
-- 7.39.3 to the slice site `(C / U i, J.over (U i))` to obtain enough points there; then use the
-- cover-family criterion from Lemma 7.38.5, and transport slice points back to points of `C` via
-- Lemma 7.34.2.
/-- Helper for Lemma 7.39.4: a site with finite limits and the finite-refinement property has
enough points. This is the local slice-site input supplied by Proposition 7.39.3. -/
lemma site_has_enough_points_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    HasEnoughPoints.{w} J :=
by
  -- Apply Proposition 7.39.3 directly: finite refinement on the site produces enough points.
  simpa using hasEnoughPoints_of_finite_cover_refinement (J := J) hfinite

/-- Helper for Lemma 7.39.4: every slice site in the covering family has enough points once the
slice-site finite-refinement hypothesis is available. -/
lemma slice_sites_have_enough_points
    {I : Type w} (U : I → C)
    [∀ i : I, Limits.HasFiniteLimits (Over (U i))]
    (hfinite : ∀ i : I, ∀ X : Over (U i), (J.over (U i)).HasFiniteRefinementProperty X) :
    ∀ i : I, HasEnoughPoints.{w} (J.over (U i)) := by
  intro i
  -- Apply the local finite-refinement theorem on the slice site indexed by `i`.
  simpa using site_has_enough_points_of_finite_cover_refinement
    (J := J.over (U i)) (hfinite := hfinite i)

/-- Lemma 7.39.4: if the family `U` covers the terminal object of `(C, J)` and each slice site
`(C / U i, J.over (U i))` satisfies the finite-limit and
finite-refinement hypotheses of Proposition 7.39.3, then `(C, J)` has enough points. -/
lemma hasEnoughPoints_of_covering_family_and_slice_finite_cover_refinement
    {I : Type w} (U : I → C)
    (hcover : J.CoversTop U)
    [∀ i : I, Limits.HasFiniteLimits (Over (U i))]
    (hfinite : ∀ i : I, ∀ X : Over (U i), (J.over (U i)).HasFiniteRefinementProperty X) :
    HasEnoughPoints.{w} J := by
  -- The global enough-points statement follows once each slice site has enough points.
  apply hasEnoughPoints_of_covering_family_and_slice_sites U hcover
  -- Package the slice-site application of Proposition 7.39.3 into a single local family.
  exact slice_sites_have_enough_points (J := J) U hfinite

end CategoryTheory
