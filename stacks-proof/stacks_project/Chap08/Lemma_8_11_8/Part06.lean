import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part05

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: after transporting a chosen-cover pullback comparison back to
sheaves on `C / V`, the chosen-cover descent functor sends it right back to the original
descent-data morphism. This isolates the remaining blocker to constructing the datum-side
comparison itself and its id/comp laws. -/
theorem chosen_cover_transport_transition_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (e :
      chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f ≅
        chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V) :
    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
      (chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian f e).hom) = e.hom := by
  -- This is the generic cover-descent transport identity specialized to the fixed chosen cover.
  simpa [chosen_cover_pulled_descent_datum, chosen_cover_descent_datum,
    chosen_cover_descent_functor, chosen_cover_transport_transition] using
    localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V) e

/-- Helper for Lemma 8.11.8: taking the fixed chosen-cover component of the transported
datum-side comparison simply reads off the corresponding component of the original descent-data
isomorphism. This keeps later composition proofs at one chosen-cover arrow before any secondary
cover normalization. -/
private theorem chosen_cover_transport_transition_functor_map_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (e :
      chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f ≅
        chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        (chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian f e).hom).hom I) =
      e.hom.hom I := by
  -- Read the fixed chosen-cover component from the already-packaged descent-functor transport
  -- identity instead of reopening the sheaf-side transport shell.
  exact
    congrArg (fun ψ ↦ ψ.hom I)
      (chosen_cover_transport_transition_functor_map
        (𝒮 := 𝒮) hGerbe hAbelian f e)

/-- Helper for Lemma 8.11.8: on one chosen-cover arrow, the chosen-cover descent functor sends
the identity pullback comparison on the descended chosen-cover sheaf to the pointwise identity on
sections. This isolates the transport shell that remains in the `transition_id` proof. -/
private theorem chosen_cover_descent_functor_map_overMapPullbackId_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (T : (Over I.Y)ᵒᵖ)
    (α :
      ((chosen_cover_pulled_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)).obj I).1.obj T) :
    ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
        (((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom)).hom I).1.app T) α = α := by
  -- Evaluate the chosen-cover descent image on the fixed cover arrow `I`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)]
  -- The owner-side identity pullback comparison is pointwise the identity on sections.
  simp [chosen_cover_pulled_descent_datum, chosen_cover_descent_functor,
    GrothendieckTopology.overMapPullbackId_hom_app_hom_app]

/-- Helper for Lemma 8.11.8: after mapping the identity pullback comparison through the
chosen-cover descent functor, the resulting morphism of descent data is the identity. This
packages the pointwise slice calculation into the owner-level normalization used in the
`transition_id` branch. -/
theorem chosen_cover_descent_functor_map_overMapPullbackId_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) :
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
        (((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) =
      𝟙 _ := by
  -- Check equality of descent-data morphisms componentwise on the chosen cover of `U`.
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  -- Each component is a morphism of sheaves on `C / I.Y`; compare them sectionwise.
  apply Sheaf.hom_ext
  intro T
  funext α
  -- The pointwise calculation was already isolated above.
  exact
    chosen_cover_descent_functor_map_overMapPullbackId_app
      (𝒮 := 𝒮) hGerbe hAbelian U I T α

/-- Helper for Lemma 8.11.8: the `I`-component of the pulled chosen-cover descent datum is the
composite pullback of the descended chosen-cover sheaf along `I.f ≫ f`. This removes the outer
iterated-pullback shell before the mixed local descent comparison on `I.Y`. -/
private noncomputable def chosen_cover_pulled_component_composite_pullback_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_pulled_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian f).obj I ≅
      (J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) :=
  (J.overMapPullbackComp (Type (max u v)) I.f f).app
    (chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Helper for Lemma 8.11.8: after rewriting the pulled `I`-component as the composite pullback
along `q := I.f ≫ f`, the remaining local comparison lives entirely on the chosen cover of `I.Y`.
This is the stable source-side normalization needed before building the mixed local descent
comparison. -/
private noncomputable def chosen_cover_pulled_component_local_source_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        ((chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f).obj I) ≅
      (chosen_cover_descent_functor
        (𝒮 := 𝒮) hGerbe I.Y).obj
          ((J.overMapPullback (Type (max u v)) (I.f ≫ f)).obj
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).mapIso
    (chosen_cover_pulled_component_composite_pullback_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I)

/-- Helper for Lemma 8.11.8: evaluating the normalized outer pullback isomorphism on one chosen
cover arrow `K` is just the pullback of the composite-pullback comparison morphism along `K.f`.
This isolates the exact component shell that the mixed-cover datum must later compose with. -/
private theorem chosen_cover_pulled_component_local_source_iso_hom_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    (chosen_cover_pulled_component_local_source_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom.hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom) := by
  -- Evaluate the chosen-cover descent functor on the fixed secondary-cover arrow `K`.
  rfl

-- Route correction for Lemma 8.11.8: once the outer pullback shell is normalized to
-- `q := I.f ≫ f`, the remaining source-faithful step is a single descent-data comparison on the
-- chosen cover of `I.Y`. The next two declarations isolate its component family and `isoMk`
-- comm square before repackaging them as one descent-data isomorphism.
/-- Helper for Lemma 8.11.8: freeze the `K`-component of the normalized mixed-cover source side
before any `isoMk` packaging. This keeps the remaining blocker at the explicit owner-level
pullback shell rather than reintroducing the outer descent-functor transport. -/
theorem mixed_cover_source_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    (chosen_cover_pulled_component_local_source_iso
      (𝒮 := 𝒮) hGerbe hAbelian f I).hom.hom K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom) := by
  -- Reuse the already-isolated component computation so later mixed-cover proofs can normalize
  -- the source branch in one named step.
  simpa using
    chosen_cover_pulled_component_local_source_iso_hom_component
      (𝒮 := 𝒮) hGerbe hAbelian f I K

/-- Helper for Lemma 8.11.8: name the target-side local owner on `K.Y`. Once the source side is
normalized to a matching owner, the mixed-cover comparison should be the chosen local comparison
between these two objects over `K.Y`. -/
private noncomputable abbrev mixed_cover_target_local_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {V : C} (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    𝒮.p.Fiber K.Y :=
  K.f ^*[canonicalPullbackChoice 𝒮.p]
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)

/-- Helper for Lemma 8.11.8: the target component of the chosen-cover descent datum over `I.Y` is
definitionally the pullback of the automorphism sheaf of the chosen local object over `V` along
`K.f`. This removes the target normalization from the live blocker, leaving only the missing
source-owner bridge on `C / K.Y`. -/
private theorem mixed_cover_target_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {V : C}
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((chosen_cover_descent_functor
      (𝒮 := 𝒮) hGerbe I.Y).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).obj K =
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)) := by
  -- The chosen-cover descent functor on `I.Y` is literally `toDescentData`, so the `K`-component
  -- is the pullback sheaf along `K.f`.
  rfl

/-- Helper for Lemma 8.11.8: the source-faithful owner for pulling back the chosen-cover sheaf
from `U` to `Y` is the pullback of the chosen gerbe cover of `U` along `q`. -/
private noncomputable abbrev chosen_cover_pullback_cover
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (q : Y ⟶ U) : J.Cover Y :=
  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).pullback q

/-- Helper for Lemma 8.11.8: membership in the pullback of the chosen gerbe cover is exactly
membership of the composite arrow in the original chosen gerbe cover. This keeps later adapter
proofs from unfolding `Cover.pullback` directly when matching theorem inputs. -/
theorem chosen_cover_pullback_cover_hom_mem_iff
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y Z : C} (q : Y ⟶ U) (g : Z ⟶ Y) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q) g ↔
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (g ≫ q) := by
  -- `Cover.coe_pullback` is the transport-stable characterization needed for later pullback-cover
  -- arrow specializations.
  simpa [chosen_cover_pullback_cover] using
    (GrothendieckTopology.Cover.coe_pullback
      (S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) q g)

/-- Helper for Lemma 8.11.8: forgetting a refined pullback-cover arrow back to the original
chosen cover commutes with `Arrow.precomp`. This is the transport-stable `.base` simplification
needed when a blocked specialization names an explicit refined pullback-cover arrow first and only
afterwards rewrites its base arrow. -/
theorem chosen_cover_pullback_cover_precomp_base
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y Z : C} (q : Y ⟶ U)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow) (g : Z ⟶ I.Y) :
    (I.precomp g).base = I.base.precomp g := by
  -- Both sides are the same original-cover arrow with source `Z`; only the association of the
  -- stored composite map differs before definitional reduction.
  cases I
  rfl

/-- Helper for Lemma 8.11.8: on one arrow of the pullback cover of the chosen gerbe cover of
`U`, the source component is already the chosen-cover component indexed by the base arrow
`I.base`. This removes the outer `q`-pullback shell before the local comparison to `y` is
packaged as descent data. -/
private noncomputable def pullback_cover_source_component_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).obj I ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base) :=
  -- The pullback-cover component is definitionally the chosen-cover component over the base
  -- arrow `I.base : (chosen_gerbe_cover U).Arrow`.
  chosen_cover_underlying_automorphism_sheaf_cover_iso
    (𝒮 := 𝒮) hGerbe hAbelian U I.base

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover of `x` and `z`, one overlap
leg `g : Z ⟶ K.Y` identifies the common-owner pullback `q ^* x` with the iterated pullback
through `K.f`. This is the source-side owner normalization used before comparing conjugation
maps. -/
private noncomputable abbrev chosen_local_common_owner_source_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Z : C}
    {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p] x ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p] x) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫ hc.pullbackCompComponentIso K.f g x

/-- Helper for Lemma 8.11.8: the same overlap leg identifies the common-owner pullback `q ^* z`
with the iterated pullback through `K.f` on the target side. -/
private noncomputable abbrev chosen_local_common_owner_target_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Z : C}
    {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p] z ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p] z) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫ hc.pullbackCompComponentIso K.f g z

/-- Helper for Lemma 8.11.8: after both endpoints are rewritten to the common owner `q`, one
chosen local isomorphism on the cover becomes a concrete comparison
`q ^*[canonicalPullbackChoice 𝒮.p] x ≅ q ^*[canonicalPullbackChoice 𝒮.p] z`. -/
private noncomputable abbrev chosen_local_common_owner_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U Z : C}
    {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p] x ≅
      q ^*[canonicalPullbackChoice 𝒮.p] z :=
  let hc := canonicalPullbackChoice 𝒮.p
  chosen_local_common_owner_source_iso
      (𝒮 := 𝒮) hGerbe q g hg ≪≫
    (hc.pullbackFunctor g).mapIso
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K) ≪≫
    (chosen_local_common_owner_target_iso
      (𝒮 := 𝒮) hGerbe q g hg).symm

/-- Helper for Lemma 8.11.8: once two chosen local isomorphisms are rewritten to the same owner
`q`, abelianity makes their induced conjugation isomorphisms equal because the two normalized
fiber morphisms are parallel. -/
private theorem chosen_local_common_owner_conjugation_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K₁ K₂ : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q g₁ hg₁).hom =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q g₂ hg₂).hom := by
  -- Both rewritten local isomorphisms have the same endpoints over `q`, so the conjugation map
  -- depends only on those endpoints and not on the chosen overlap leg.
  simpa using
    automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe q g₁ hg₁).hom
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe q g₂ hg₂).hom

/-- Helper for Lemma 8.11.8: pulling back a chosen-local common-owner comparison along one more
owner leg produces exactly the common-owner comparison for the composite owner. This isolates the
owner-change datum at the fiber-isomorphism level before any automorphism-sheaf transport is
expanded. -/
private theorem chosen_local_common_owner_isomorphism_pullback_eq_owner_leg
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z W : C} {x z : 𝒮.p.Fiber U}
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (q : Z ⟶ U) (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (s : W ⟶ Z) :
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor s).mapIso
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q g hg) =
      chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe (s ≫ q) (s ≫ g)
        (by simpa [Category.assoc, hg]) := by
  -- Route correction: perform the owner change once at the common-owner isomorphism itself, so
  -- later proofs can transport that equality instead of rebuilding the shell pointwise.
  cases hg
  rfl

/-- Helper for Lemma 8.11.8: after transporting the common-owner comparison along one more owner
leg, the induced automorphism-sheaf conjugation shell is exactly the shell for the composite
owner. This is the sheaf-level owner-change bridge used before evaluating on sections. -/
theorem chosen_local_common_owner_conjugation_pullback_eq_owner_leg
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z W : C} {x z : 𝒮.p.Fiber U}
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (q : Z ⟶ U) (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (s : W ⟶ Z) :
    ((J.pseudofunctorOver (Type (max u v))).map s.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe q g hg).hom).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe (s ≫ q) (s ≫ g)
          (by simpa [Category.assoc, hg])).hom).hom := by
  -- First rewrite the pulled shell as conjugation by the pulled common-owner comparison, then
  -- replace that pulled comparison by the canonical composite-owner comparison.
  rw [automorphismUnderlyingSheafConj_pullbackFunctor_map
    (𝒮 := 𝒮) hAbelian s
    (chosen_local_common_owner_isomorphism
      (𝒮 := 𝒮) hGerbe q g hg).hom]
  simpa using
    congrArg
      (fun e ↦ (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom).hom)
      (chosen_local_common_owner_isomorphism_pullback_eq_owner_leg
        (𝒮 := 𝒮) hGerbe q g hg s)

/-- Helper for Lemma 8.11.8: if two chosen local comparisons from a fixed owner `A` are both
rewritten to the same owner `q`, then composing the comparison to `x` with the pulled morphism
`φ : x ⟶ y` gives the comparison to `y`. This is the common-owner cross-cover step required when
the chosen local cover for `(A,x)` and the chosen local cover for `(A,y)` differ. -/
private theorem chosen_local_cross_cover_common_owner_conjugation_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {A x y : 𝒮.p.Fiber U} (φ : x ⟶ y) (q : Z ⟶ U)
    {Kx : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A x).Arrow}
    {Ky : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A y).Arrow}
    (gx : Z ⟶ Kx.Y) (gy : Z ⟶ Ky.Y)
    (hgx : gx ≫ Kx.f = q := by cat_disch) (hgy : gy ≫ Ky.f = q := by cat_disch) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gx hgx).hom ≪≫
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ) =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gy hgy).hom := by
  -- Route correction: compare the two local choices only after both have been transported to the
  -- same owner `q`, so endpoint-independence applies to the composite comparison.
  rw [← automorphismUnderlyingSheafConj_comp]
  simpa using
    (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      ((chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gx hgx).hom ≫
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ))
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe q gy hgy).hom)

/-- Helper for Lemma 8.11.8: the previous cross-cover common-owner comparison is also available
on the underlying sheaf morphisms, which is the form needed after expanding `Iso.hom` in the
remaining local pulled-conjugation proof. -/
private theorem chosen_local_cross_cover_common_owner_conjugation_hom_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {A x y : 𝒮.p.Fiber U} (φ : x ⟶ y) (q : Z ⟶ U)
    {Kx : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A x).Arrow}
    {Ky : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A y).Arrow}
    (gx : Z ⟶ Kx.Y) (gy : Z ⟶ Ky.Y)
    (hgx : gx ≫ Kx.f = q := by cat_disch) (hgy : gy ≫ Ky.f = q := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gx hgx).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ)).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gy hgy).hom).hom := by
  -- Pass from the iso-level cross-cover comparison to the morphism-level form needed later.
  simpa using
    congrArg Iso.hom
      (chosen_local_cross_cover_common_owner_conjugation_eq
        (𝒮 := 𝒮) hGerbe hAbelian φ q gx gy hgx hgy)

/-- Helper for Lemma 8.11.8: the cross-cover common-owner comparison can be evaluated directly on
one section of the common owner. This is the pointwise form needed when the final local-cover
gluing step compares the two branches on each refinement member before applying separatedness. -/
theorem chosen_local_cross_cover_common_owner_conjugation_hom_eq_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {A x y : 𝒮.p.Fiber U} (φ : x ⟶ y) (q : Z ⟶ U)
    {Kx : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A x).Arrow}
    {Ky : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A y).Arrow}
    (gx : Z ⟶ Kx.Y) (gy : Z ⟶ Ky.Y)
    (hgx : gx ≫ Kx.f = q := by cat_disch) (hgy : gy ≫ Ky.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (q ^*[canonicalPullbackChoice 𝒮.p] A)).1.obj T) :
    (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe q gx hgx).hom).hom) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).map φ)).hom).1.app T) α =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe q gy hgy).hom).hom).1.app T) α) := by
  -- Evaluate the owner-level cross-cover equality on the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app T))
        (chosen_local_cross_cover_common_owner_conjugation_hom_eq
          (𝒮 := 𝒮) hGerbe hAbelian φ q gx gy hgx hgy))
      α

/-- Helper for Lemma 8.11.8: on a section `T` of the common owner `Z`, pulling back along
`g : Z ⟶ K.Y` presents the section owner on `C / K.Y` as the composite arrow `T.unop.hom ≫ g`. -/
private theorem chosen_local_section_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    ((Over.map g).obj T.unop).hom = T.unop.hom ≫ g := by
  -- The pullback owner in `Over K.Y` is definitionally the composite arrow `T.unop.hom ≫ g`.
  rfl

/-- Helper for Lemma 8.11.8: after evaluating at a section `T : Over Z`, the chosen-local owner
arrow composes with `K.f` to the common-owner arrow `T.unop.hom ≫ q`, both in `C` and in the
`LocallyDiscrete` coordinates used by `mapComp'`. -/
private theorem chosen_local_section_arrow
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    (((Over.map g).obj T.unop).hom ≫ K.f = T.unop.hom ≫ q) ∧
      (K.f.op.toLoc ≫ ((Over.map g).obj T.unop).hom.op.toLoc =
        (T.unop.hom ≫ q).op.toLoc) := by
  constructor
  · -- First identify the evaluated owner arrow and compose with the fixed witness `hg`.
    change T.unop.hom ≫ g ≫ K.f = T.unop.hom ≫ q
    simpa [Category.assoc, hg]
  · -- Then translate the same equality into the `LocallyDiscrete` coordinates for `mapComp'`.
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
      congrArg Quiver.Hom.toLoc <|
        congrArg Quiver.Hom.op <| by
          change T.unop.hom ≫ g ≫ K.f = T.unop.hom ≫ q
          simpa [Category.assoc, hg]

/-- Helper for Lemma 8.11.8: after evaluating on a section `T : Over Z`, the chosen-local leg
produces the exact `LocallyDiscrete` equality witness needed by `pseudofunctorOver.mapComp'`. -/
private theorem chosen_local_mapComp'_witness
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    K.f.op.toLoc ≫ ((Over.map g).obj T.unop).hom.op.toLoc =
      (T.unop.hom ≫ q).op.toLoc := by
  -- This is exactly the second component of the section-level owner-arrow normalization.
  simpa using
    (chosen_local_section_arrow
      (𝒮 := 𝒮) hGerbe q g hg T).2

/-- Helper for Lemma 8.11.8: the flexible comparison `mapComp'` on one chosen-local section
splits into the equality transport coming from the common-owner witness, followed by the strict
composition comparison. -/
private theorem chosen_local_mapComp'_eq_map₂Iso_comp_mapComp
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    (J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc ((Over.map g).obj T.unop).hom.op.toLoc (T.unop.hom ≫ q).op.toLoc
        (chosen_local_mapComp'_witness
          (𝒮 := 𝒮) hGerbe q g hg T) =
      (J.pseudofunctorOver (Type (max u v))).map₂Iso
        (eqToIso (by
          simpa using
            (chosen_local_mapComp'_witness
              (𝒮 := 𝒮) hGerbe q g hg T).symm)) ≪≫
        (J.pseudofunctorOver (Type (max u v))).mapComp
          K.f.op.toLoc ((Over.map g).obj T.unop).hom.op.toLoc := by
  -- This is the defining expansion of the flexible comparison `mapComp'`.
  simp [Pseudofunctor.mapComp']

/-- Helper for Lemma 8.11.8: at the fiber level, the inverse `mapComp'` component is exactly the
inverse source-side common-owner comparison. -/
private theorem chosen_local_common_owner_source_iso_inv_eq_mapComp'_inv_app
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).inv.toNatTrans.app x =
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe q g hg).inv := by
  -- Route correction: substitute `hg` first, then the flexible `mapComp'` shell is the canonical
  -- pullback-composition comparison.
  cases hg
  simpa [chosen_local_common_owner_source_iso] using
    (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
      (hc := canonicalPullbackChoice 𝒮.p) K.f g x)

/-- Helper for Lemma 8.11.8: at the fiber level, the hom `mapComp'` component is exactly the
hom target-side common-owner comparison. -/
private theorem chosen_local_common_owner_target_iso_hom_eq_mapComp'_hom_app
    (hGerbe : IsGerbe J 𝒮.p)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).hom.toNatTrans.app z =
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe q g hg).hom := by
  -- The target-side common-owner comparison is the hom-side version of the same canonical
  -- pullback-composition package.
  cases hg
  simpa [chosen_local_common_owner_target_iso] using
    (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
      (hc := canonicalPullbackChoice 𝒮.p) K.f g z)

/-- Helper for Lemma 8.11.8: after evaluating the inverse chosen-local boundary map on one
section object `T : Over Z`, the only remaining transport is the source-side common-owner
comparison isomorphism. -/
theorem chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_source_iso
            (𝒮 := 𝒮) hGerbe q g hg).inv.hom).hom := by
  -- Upgrade the solved fiber-level owner normalization to an equality of sheaf morphisms.
  apply Sheaf.hom_ext
  ext T α
  rw [chosen_local_mapComp'_eq_map₂Iso_comp_mapComp
    (𝒮 := 𝒮) hGerbe q g hg T]
  rw [local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op]
  simpa [automorphismUnderlyingSheafConj, automorphismUnderlyingSheafConj_hom,
    automorphismUnderlyingSheaf, automorphismAddCommSheafConj, automorphismAddCommPresheaf,
    automorphismSection, automorphismSectionObj, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.conj_apply, Functor.mapIso_hom, Functor.mapIso_inv, chosen_local_section_owner,
    chosen_local_common_owner_source_iso_inv_eq_mapComp'_inv_app]

/-- Helper for Lemma 8.11.8: after evaluating the forward chosen-local boundary map on one
section object `T : Over Z`, the only remaining transport is the target-side common-owner
comparison isomorphism. -/
theorem chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe q g hg).hom).hom := by
  -- Upgrade the target-side fiber normalization to an equality of sheaf morphisms.
  apply Sheaf.hom_ext
  ext T α
  rw [chosen_local_mapComp'_eq_map₂Iso_comp_mapComp
    (𝒮 := 𝒮) hGerbe q g hg T]
  rw [local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op]
  simpa [automorphismUnderlyingSheafConj, automorphismUnderlyingSheafConj_hom,
    automorphismUnderlyingSheaf, automorphismAddCommSheafConj, automorphismAddCommPresheaf,
    automorphismSection, automorphismSectionObj, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.conj_apply, Functor.mapIso_hom, Functor.mapIso_inv, chosen_local_section_owner,
    chosen_local_common_owner_target_iso_hom_eq_mapComp'_hom_app]

/-- Helper for Lemma 8.11.8: after pulling one chosen local conjugation map along `g`, the middle
morphism is exactly conjugation by the pulled chosen local isomorphism. -/
theorem chosen_local_pulled_conjugation_eq_pulled_iso_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K)).hom).hom := by
  -- This is the general pulled-conjugation adapter specialized to the chosen local isomorphism.
  simpa using
    automorphismUnderlyingSheafConj_pullbackFunctor_map
      (𝒮 := 𝒮) hAbelian g
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom

/-- Helper for Lemma 8.11.8: the pulled chosen local conjugation map factors through the common
owner as the source comparison inverse, followed by the common-owner conjugation, followed by the
target comparison. -/
theorem chosen_local_pulled_conjugation_eq_common_owner_middle
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe q g hg).inv.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe q g hg).hom).hom := by
  -- Rewrite the middle map as conjugation by the pulled chosen local isomorphism, then expand
  -- the common-owner comparison isomorphism and use functoriality of conjugation.
  rw [chosen_local_pulled_conjugation_eq_pulled_iso_conj
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  have hpulled :
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
          (chosen_local_isomorphism
            (𝒮 := 𝒮) hGerbe x z K)).hom =
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe q g hg).inv.hom ≫
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe q g hg).hom ≫
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe q g hg).hom := by
    -- This is just the hom-level expansion of `chosen_local_common_owner_isomorphism`.
    simp [chosen_local_common_owner_isomorphism, Category.assoc]
  rw [hpulled, automorphismUnderlyingSheafConj_hom_comp]
  rw [automorphismUnderlyingSheafConj_hom_comp]
  rfl

/-- Helper for Lemma 8.11.8: on the source side, the raw forward `mapComp'` boundary cancels the
common-owner source inverse comparison. -/
private theorem chosen_local_source_boundary_normalization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe q g hg).inv.hom).hom = 𝟙 _ := by
  -- Replace the source common-owner inverse comparison by the raw boundary `inv`, then cancel
  -- the `mapComp'` isomorphism componentwise.
  rw [chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  let compNatIso := Cat.Hom.toNatIso <|
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)
  simpa [compNatIso] using congr_app compNatIso.hom_inv_id
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)

/-- Helper for Lemma 8.11.8: on the target side, the common-owner comparison cancels the raw
inverse `mapComp'` boundary map. -/
theorem chosen_local_target_boundary_normalization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) = 𝟙 _ := by
  -- Replace the target common-owner comparison by the raw boundary `hom`, then cancel the
  -- `mapComp'` isomorphism componentwise.
  rw [← chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  let compNatIso := Cat.Hom.toNatIso <|
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)
  simpa [compNatIso] using congr_app compNatIso.hom_inv_id
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)

/-- Helper for Lemma 8.11.8: on the target side, the raw inverse `mapComp'` boundary also
cancels against the common-owner target comparison in the opposite order. This is the
point where the common-owner route exposes the target shell as a genuine isomorphism rather
than a one-sided normalization. -/
private theorem chosen_local_target_boundary_normalization_symm
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe q g hg).hom).hom = 𝟙 _ := by
  -- Rewrite the target common-owner comparison to the forward `mapComp'` boundary and cancel the
  -- underlying comparison isomorphism in the `inv ≫ hom` order used by the blocked transport.
  rw [← chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  let compNatIso := Cat.Hom.toNatIso <|
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)
  simpa [compNatIso] using congr_app compNatIso.inv_hom_id
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)

/-- Helper for Lemma 8.11.8: once both chosen-local descent-transition maps are exposed as their
canonical `mapComp'` comparison morphisms, the `isoMk` square reduces to the common-owner
conjugation equality. -/
private theorem chosen_local_automorphism_descent_square_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K₁ K₂ : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₁).hom).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)).hom q g₁ g₂ =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom q g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₂).hom).hom) := by
  -- Route correction: expose the chosen-local `toDescentData` transitions first, so the proof is
  -- only owner normalization plus the common-owner conjugation equality.
  change
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₁).hom).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) =
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₂).hom).hom) := by
          simp [Category.assoc]
  -- Normalize the left branch to the common owner `q`.
  rw [Category.assoc]
  rw [chosen_local_pulled_conjugation_eq_common_owner_middle
    (𝒮 := 𝒮) hGerbe hAbelian q g₁ hg₁]
  rw [Category.assoc, chosen_local_target_boundary_normalization
    (𝒮 := 𝒮) hGerbe hAbelian q g₁ hg₁]
  rw [← chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian q g₁ hg₁]
  -- Normalize the right branch to the same owner `q`.
  rw [← Category.assoc]
  rw [chosen_local_pulled_conjugation_eq_common_owner_middle
    (𝒮 := 𝒮) hGerbe hAbelian q g₂ hg₂]
  rw [← Category.assoc, chosen_local_source_boundary_normalization
    (𝒮 := 𝒮) hGerbe hAbelian q g₂ hg₂]
  rw [← chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian q g₂ hg₂]
  -- Once both branches land on the same owner `q`, abelianity kills the choice of overlap leg.
  simpa [Category.assoc] using
    congrArg
      (fun i ↦
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
          i.hom ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)))
      (chosen_local_common_owner_conjugation_eq
        (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂)

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover of two fiber objects, the
componentwise chosen local conjugations package into one descent-data isomorphism. This isolates
the pairwise-local comparison step before it is specialized to the pullback cover of `q`. -/
private noncomputable def chosen_local_automorphism_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x z : 𝒮.p.Fiber U) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) ≅
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z) :=
  -- Route correction: build the source-faithful local comparison for `x` and `z` directly on
  -- their chosen local-isomorphism cover, instead of hiding it inside the later pullback-cover
  -- comparison.
  Pseudofunctor.DescentData.isoMk
    (fun K ↦
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom)
    (fun q g₁ g₂ hg₁ hg₂ ↦
      -- The remaining `isoMk` square is exactly the chosen-local common-owner normalization
      -- isolated above.
      chosen_local_automorphism_descent_square_normalized
        (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂)

/-- Helper for Lemma 8.11.8: transport the pairwise-local descent comparison for two locally
isomorphic fiber objects back to an isomorphism of sheaves on `C / U`. -/
private noncomputable def chosen_local_automorphism_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x z : 𝒮.p.Fiber U) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z :=
  -- The pairwise-local comparison lives on the chosen local-isomorphism cover first, and only
  -- afterwards is transported back to the slice sheaf on `C / U`.
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z)
    (chosen_local_automorphism_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian x z)

/-- Helper for Lemma 8.11.8: after transporting the pairwise-local comparison back to sheaves on
`C / U`, the chosen local-isomorphism cover descent functor sends it right back to the original
descent-data component. This removes the remaining transport shell around
`chosen_local_automorphism_iso` before the pullback-cover overlap square is normalized. -/
theorem chosen_local_automorphism_iso_functor_map_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x z : 𝒮.p.Fiber U)
    (L : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z)).functor.map
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian x z).hom).hom L =
        (chosen_local_automorphism_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian x z).hom.hom L := by
  let e := chosen_local_automorphism_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian x z
  -- Route correction: expose the transported sheaf comparison through the explicit cover-descent
  -- equivalence before taking the `L`-component.
  simpa [chosen_local_automorphism_iso, e] using
    congrArg (fun φ ↦ φ.hom L)
      (localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z) e)

/-- Helper for Lemma 8.11.8: on one chosen-local cover arrow, the transported pairwise-local
comparison is already the concrete conjugation map induced by that chosen local isomorphism.
This is the transport-stable target-side component used before passing to the secondary cover. -/
theorem chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x z : 𝒮.p.Fiber U)
    (L : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z)).functor.map
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian x z).hom).hom L =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z L).hom).hom := by
  -- Route correction: collapse the transported component all the way to the underlying
  -- chosen-local conjugation map now, so the later pullback-cover target square does not have to
  -- reopen the `isoMk` packaging of `chosen_local_automorphism_descent_iso`.
  simpa [chosen_local_automorphism_descent_iso] using
    chosen_local_automorphism_iso_functor_map_component
      (𝒮 := 𝒮) hGerbe hAbelian x z L

/-- Helper for Lemma 8.11.8: on one arrow of the pullback cover of the chosen gerbe cover of
`U`, compare the normalized source component with the automorphism sheaf of the pulled local
object `I.f ^* y`. This isolates the pointwise component before the remaining overlap square is
packaged by `isoMk`. -/
private noncomputable def pullback_cover_local_object_component_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).obj I ≅
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I :=
  -- First remove the outer chosen-cover shell, then compare the two owners over `I.Y` by the
  -- pairwise-local automorphism-sheaf comparison.
  pullback_cover_source_component_iso
      (𝒮 := 𝒮) hGerbe hAbelian q I ≪≫
    chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y)

/-- Helper for Lemma 8.11.8: after identifying one pullback-cover component with the corresponding
chosen-cover component on `U`, the pullback-cover source transition is exactly the chosen-cover
descent transition over the common arrow `r ≫ q`. This isolates the source-side normalization
before the local comparison to `y` is inserted. -/
theorem pullback_cover_source_component_transition
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((pullback_cover_source_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q I₁).hom) ≫
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom (r ≫ q) g₁ g₂ =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).hom r g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((pullback_cover_source_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q I₂).hom) := by
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
  let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
  let D :=
    automorphism_cover_descent_datum
      (𝒮 := 𝒮) hAbelian S xS
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
      (automorphism_cover_overlap_self (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian S xS)
  let FU := localizedSheafFromCoverDescentData (J := J) S D
  let ε := localizedSheafFromCoverDescentData_counitIso (J := J) S D
  have hcomm :=
    ε.hom.comm (r ≫ q) g₁ g₂
      (by
        change g₁ ≫ (I₁.f ≫ q) = r ≫ q
        simpa [Category.assoc, hg₁])
      (by
        change g₂ ≫ (I₂.f ≫ q) = r ≫ q
        simpa [Category.assoc, hg₂])
  -- Route correction: unfold the chosen-cover descended sheaf back to the explicit fixed-cover
  -- descent package so the source transition is read directly from the counit `comm` field.
  simpa [S, xS, D, FU, ε, chosen_cover_descent_datum, chosen_cover_descent_functor,
    chosen_cover_pullback_cover, pullback_cover_source_component_iso,
    chosen_cover_underlying_automorphism_sheaf, chosen_cover_underlying_automorphism_sheaf_cover_iso,
    chosen_cover_underlying_automorphism_descent] using hcomm

end CategoryTheory
