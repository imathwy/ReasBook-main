import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part05
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.FiberPullbackComp

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

/-- Helper for Lemma 8.11.8: the chosen-cover descent functor preserves the identity pullback
comparison `overMapPullbackId` on the descended chosen-cover sheaf, sending its underlying
morphism to the hom-component of its `mapIso` image. (After the Mathlib refactor
`J.overMapPullback (𝟙 U)` is no longer definitionally `𝟭`, so the descended comparison is the
genuine `overMapPullbackId` transport rather than a literal identity; the spirit "the chosen-cover
transport of the identity pullback comparison is canonical" is captured by this functoriality
identity.) -/
theorem chosen_cover_descent_functor_map_overMapPullbackId_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) :
    (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
        (((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) =
      ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
        ((J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))).hom := by
  -- `Functor.mapIso_hom`: the functor's action on the comparison morphism is the hom-component
  -- of its action on the comparison iso.
  rfl

/-- Helper for Lemma 8.11.8: the `I`-component of the pulled chosen-cover descent datum is the
composite pullback of the descended chosen-cover sheaf along `I.f ≫ f`. This removes the outer
iterated-pullback shell before the mixed local descent comparison on `I.Y`. -/
noncomputable def chosen_cover_pulled_component_composite_pullback_iso
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
noncomputable def chosen_cover_pulled_component_local_source_iso
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
noncomputable abbrev chosen_cover_pullback_cover
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
  -- stored composite map differs (the refactor made `≫` no longer definitionally associative).
  cases I
  ext
  all_goals
    first
      | rfl
      | rw [Category.assoc]
      | rw [← Category.assoc]
      | exact heq_of_eq (by rw [Category.assoc])
      | exact heq_of_eq (by rw [← Category.assoc])
      | simp [GrothendieckTopology.Cover.Arrow.base_f,
          GrothendieckTopology.Cover.Arrow.precomp_f, Category.assoc]

/-- Helper for Lemma 8.11.8: on one arrow of the pullback cover of the chosen gerbe cover of
`U`, the source component is already the chosen-cover component indexed by the base arrow
`I.base`. This removes the outer `q`-pullback shell before the local comparison to `y` is
packaged as descent data. -/
noncomputable def pullback_cover_source_component_iso
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
  -- The pullback-cover component is `(F.map I.f) ((overMapPullback q) G)`, which is the
  -- `(F.map (I.f ≫ q))`-pullback of `G = chosen_cover_underlying_automorphism_sheaf U` by
  -- the pseudofunctor composition `mapComp'`; and `I.base.f = I.f ≫ q`, so the chosen-cover
  -- comparison `chosen_cover_underlying_automorphism_sheaf_cover_iso U I.base` identifies it with
  -- `automorphismUnderlyingSheaf (chosen_gerbe_cover_object U I.base)`.
  ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
        q.op.toLoc I.f.op.toLoc (I.f ≫ q).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).symm ≪≫
    chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U I.base

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover of `x` and `z`, one overlap
leg `g : Z ⟶ K.Y` identifies the common-owner pullback `q ^* x` with the iterated pullback
through `K.f`. This is the source-side owner normalization used before comparing conjugation
maps. -/
noncomputable abbrev chosen_local_common_owner_source_iso
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
noncomputable abbrev chosen_local_common_owner_target_iso
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
noncomputable abbrev chosen_local_common_owner_isomorphism
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
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s
          (q ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor s).mapIso
            (asIso (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe q g hg).hom)).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian s
          (q ^*[canonicalPullbackChoice 𝒮.p] z)).inv := by
  -- This is exactly the base-change formula for pulling a conjugation back along `s`.
  exact automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian s
    (chosen_local_common_owner_isomorphism (𝒮 := 𝒮) hGerbe q g hg).hom

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

/-- Public morphism-level form of the cross-cover common-owner comparison.

The app-level lemma below is useful after evaluating sheaves, but the Part08 assembly adapters
need to rewrite the sheaf morphism itself before choosing a section. -/
theorem chosen_local_cross_cover_common_owner_conjugation_hom_eq_morphism
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
          (𝒮 := 𝒮) hGerbe q gy hgy).hom).hom :=
  chosen_local_cross_cover_common_owner_conjugation_hom_eq
    (𝒮 := 𝒮) hGerbe hAbelian φ q gx gy hgx hgy

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
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
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
  · -- The pulled owner arrow `((Over.map g).obj T.unop).hom` reduces to `T.unop.hom ≫ g`, so the
    -- goal is `T.unop.hom ≫ g ≫ K.f = T.unop.hom ≫ q`; close it with the witness `hg`.
    simp [Category.assoc, hg]
  · -- Then translate the same equality into the `LocallyDiscrete` coordinates for `mapComp'`.
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
      congrArg Quiver.Hom.toLoc <|
        congrArg Quiver.Hom.op <| by
          simp [Category.assoc, hg]

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

-- Local rebuilds (the originals are `private` in Part02) of the two base-change/`mapComp'`
-- bridge lemmas and their self-contained helpers, used to discharge the chosen-local source/target
-- boundary normalizations below.
private theorem comp_sandwich_eq_p06
    {D : Type*} [Category D] {A B E F G H I K : D}
    {a : A ⟶ B} {b : B ⟶ E} {c : E ⟶ F} {m : F ⟶ G}
    {d : G ⟶ H} {e : H ⟶ I} {f : I ⟶ K}
    {L : A ⟶ F} {R : G ⟶ K}
    (hL : a ≫ b ≫ c = L) (hR : d ≫ e ≫ f = R) :
    a ≫ (b ≫ (c ≫ m ≫ d) ≫ e) ≫ f = L ≫ m ≫ R := by
  calc
    a ≫ (b ≫ (c ≫ m ≫ d) ≫ e) ≫ f =
        (a ≫ b ≫ c) ≫ m ≫ (d ≫ e ≫ f) := by
          simp only [Category.assoc]
    _ = L ≫ m ≫ R := by
          rw [hL, hR]

private theorem pseudofunctor_mapComp'_sandwich_app_heq_of_eq_p06
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    {k k' : b₀ ⟶ b₂} (hk : k = k')
    (w : f ≫ g = k) (w' : f ≫ g = k') (X : F.obj b₀)
    {α : (F.map k).toFunctor.obj X ⟶ (F.map k).toFunctor.obj X}
    {β : (F.map k').toFunctor.obj X ⟶ (F.map k').toFunctor.obj X}
    (hα : HEq α β) :
    HEq
      ((F.mapComp' f g k w).inv.toNatTrans.app X ≫ α ≫
        (F.mapComp' f g k w).hom.toNatTrans.app X)
      ((F.mapComp' f g k' w').inv.toNatTrans.app X ≫ β ≫
        (F.mapComp' f g k' w').hom.toNatTrans.app X) := by
  subst hk
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  have hα' : α = β := eq_of_heq hα
  subst hα'
  rfl

private theorem iso_inv_eq_of_hom_eq_p06 {D : Type*} [Category D] {A B : D}
    (e f : A ≅ B) (h : e.hom = f.hom) :
    e.inv = f.inv := by
  rw [← cancel_mono e.hom]
  rw [h]
  simp only [Iso.inv_hom_id]
  rw [← h]
  simp only [Iso.inv_hom_id]

private theorem pseudofunctorOver_mapComp'_inv_automorphismUnderlyingSheaf_app_heq_p06
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (f : Y ⟶ U) (g : Z ⟶ Y) (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U)
    (w : f.op.toLoc ≫ g.op.toLoc = q.op.toLoc)
    (T : (Over Z)ᵒᵖ)
    (α : (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))).obj.obj T) :
    HEq
      (((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom.app T) α)
      α := by
  simpa using
    (GrothendieckTopology.pf_mapComp'_inv_component_apply_heq
      (J := J) (f := f.op.toLoc) (g' := g.op.toLoc) (k := q.op.toLoc) (hk := w)
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) T α)

private theorem baseComp_eq_of_toLoc_comp_eq_p06
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc) :
    g ≫ f = gf := by
  apply Quiver.Hom.op_inj
  have hop :
      (g ≫ f).op.toLoc = gf.op.toLoc := by
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using hgf
  exact congrArg Discrete.as hop

private theorem automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom_p06
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (f : Y ⟶ U) (g : Z ⟶ Y) (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U)
    (w : f.op.toLoc ≫ g.op.toLoc = q.op.toLoc)
    (e :
      q ^*[canonicalPullbackChoice 𝒮.p] x ≅
        g ^*[canonicalPullbackChoice 𝒮.p]
          (f ^*[canonicalPullbackChoice 𝒮.p] x))
    (he :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app x = e.inv) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.symm.hom).hom =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom := by
  apply Sheaf.hom_ext
  ext T α
  change
    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.symm.hom).hom.hom.app T)
      (((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (f ^*[canonicalPullbackChoice 𝒮.p] x)).hom.hom.app T)
        ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom).hom.app
          T α)) =
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom.hom.app T)
        (((((J.pseudofunctorOver (Type (max u v))).mapComp'
            f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom.app T) α)
  simp only
    [GrothendieckTopology.pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map_hom_app,
      automorphismUnderlyingSheafBaseChangeIso_hom_app,
      automorphismUnderlyingSheafConj_hom_app,
      overMapCompPresheafHomIso_hom_app,
      Iso.conj_apply, Functor.mapIso_hom, Functor.mapIso_inv]
  have heHomSymm :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).hom.toNatTrans.app x = e.symm.inv := by
    simpa [Cat.Hom.toNatIso] using
      iso_inv_eq_of_hom_eq_p06
        ((Cat.Hom.toNatIso
          ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
            f.op.toLoc g.op.toLoc q.op.toLoc w)).app x).symm e.symm he
  have heInvSymm :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app x = e.symm.hom := by
    simpa using he
  rw [← heHomSymm, ← heInvSymm]
  have hq : g ≫ f = q := baseComp_eq_of_toLoc_comp_eq_p06 f g q w
  subst q
  have hcomp :
      (g ≫ f).op.toLoc ≫ (unop T).hom.op.toLoc =
        f.op.toLoc ≫ (((Over.map g).obj (unop T)).hom).op.toLoc := by
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc]
  let F := canonicalFiberPseudofunctor 𝒮.p
  let hc := canonicalPullbackChoice 𝒮.p
  let h := (unop T).hom
  let y := f ^*[hc] x
  let Kfg := F.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc w
  let Kg := F.mapComp' g.op.toLoc h.op.toLoc (g.op.toLoc ≫ h.op.toLoc) rfl
  let Kf := F.mapComp' f.op.toLoc (((Over.map g).obj (unop T)).hom).op.toLoc
    (f.op.toLoc ≫ (((Over.map g).obj (unop T)).hom).op.toLoc) rfl
  let Kgf := F.mapComp' (g ≫ f).op.toLoc h.op.toLoc
    (f.op.toLoc ≫ (((Over.map g).obj (unop T)).hom).op.toLoc) hcomp
  let Kgf₀ := F.mapComp' (g ≫ f).op.toLoc h.op.toLoc
    ((g ≫ f).op.toLoc ≫ h.op.toLoc) rfl
  let A := (F.map h.op.toLoc).toFunctor.map (Kfg.hom.toNatTrans.app x)
  let B := Kg.inv.toNatTrans.app y
  let C₁ := Kf.inv.toNatTrans.app x
  let D := Kf.hom.toNatTrans.app x
  let E := Kg.hom.toNatTrans.app y
  let G := (F.map h.op.toLoc).toFunctor.map (Kfg.inv.toNatTrans.app x)
  let L := Kgf.inv.toNatTrans.app x
  let R := Kgf.hom.toNatTrans.app x
  let L₀ := Kgf₀.inv.toNatTrans.app x
  let R₀ := Kgf₀.hom.toNatTrans.app x
  let β :=
    (((((J.pseudofunctorOver (Type (max u v))).mapComp'
        f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc w).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom.app T) α)
  change A ≫ (B ≫ (C₁ ≫ α ≫ D) ≫ E) ≫ G = L₀ ≫ β ≫ R₀
  have hα : HEq β α := by
    exact
      pseudofunctorOver_mapComp'_inv_automorphismUnderlyingSheaf_app_heq_p06
        (𝒮 := 𝒮) hAbelian f g (g ≫ f) x w T α
  have h13 :
      g.op.toLoc ≫ h.op.toLoc = (((Over.map g).obj (unop T)).hom).op.toLoc := by
    rfl
  have hfront : A ≫ B ≫ C₁ = L := by
    have hassoc :=
      (F.mapComp'₀₂₃_inv_app
        f.op.toLoc g.op.toLoc h.op.toLoc
        (g ≫ f).op.toLoc (((Over.map g).obj (unop T)).hom).op.toLoc
        (f.op.toLoc ≫ (((Over.map g).obj (unop T)).hom).op.toLoc)
        w h13 hcomp x)
    simpa [A, B, C₁, L, Kfg, Kg, Kf, Kgf, y, Category.assoc] using hassoc.symm
  have htail : D ≫ E ≫ G = R := by
    have hassoc :=
      (F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app
        f.op.toLoc g.op.toLoc h.op.toLoc
        (g ≫ f).op.toLoc (((Over.map g).obj (unop T)).hom).op.toLoc
        (f.op.toLoc ≫ (((Over.map g).obj (unop T)).hom).op.toLoc)
        w h13 rfl x)
    have hDE : D ≫ E = R ≫ A := by
      simpa [D, E, R, A, F, h, y, Kfg, Kg, Kf, Kgf, Category.assoc] using hassoc
    have hAG : A ≫ G = 𝟙 _ := by
      dsimp [A, G]
      rw [← Functor.map_comp]
      have hKfg :
          Kfg.hom.toNatTrans.app x ≫ Kfg.inv.toNatTrans.app x = 𝟙 _ := by
        simpa [Cat.Hom.toNatIso] using
          Iso.hom_inv_id_app (Cat.Hom.toNatIso Kfg) x
      simpa using
        congrArg ((F.map h.op.toLoc).toFunctor.map) hKfg
    have hDEG : (D ≫ E) ≫ G = (R ≫ A) ≫ G := by
      exact congrArg (fun m ↦ m ≫ G) hDE
    have hRAG : (R ≫ A) ≫ G = R := by
      calc
        (R ≫ A) ≫ G = R ≫ (A ≫ G) := Category.assoc R A G
        _ = R ≫ 𝟙 _ := congrArg (fun m ↦ R ≫ m) hAG
        _ = R := Category.comp_id R
    simpa only [Category.assoc] using hDEG.trans hRAG
  have hleft : A ≫ (B ≫ (C₁ ≫ α ≫ D) ≫ E) ≫ G = L ≫ α ≫ R := by
    exact comp_sandwich_eq_p06 hfront htail
  have hmiddle : HEq (L ≫ α ≫ R) (L₀ ≫ β ≫ R₀) := by
    change
      HEq (Kgf.inv.toNatTrans.app x ≫ α ≫ Kgf.hom.toNatTrans.app x)
        (Kgf₀.inv.toNatTrans.app x ≫ β ≫ Kgf₀.hom.toNatTrans.app x)
    exact
      pseudofunctor_mapComp'_sandwich_app_heq_of_eq_p06 F (g ≫ f).op.toLoc h.op.toLoc
        hcomp.symm hcomp rfl x hα.symm
  exact eq_of_heq ((heq_of_eq hleft).trans hmiddle)

private theorem automorphismUnderlyingSheafBaseChangeIso_comp_conj_inv_p06
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} (f : Y ⟶ U) (g : Z ⟶ Y) (q : Z ⟶ U)
    (x : 𝒮.p.Fiber U)
    (w : f.op.toLoc ≫ g.op.toLoc = q.op.toLoc)
    (e :
      q ^*[canonicalPullbackChoice 𝒮.p] x ≅
        g ^*[canonicalPullbackChoice 𝒮.p]
          (f ^*[canonicalPullbackChoice 𝒮.p] x))
    (he :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).hom.toNatTrans.app x = e.hom) :
    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.symm.hom).inv ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (f ^*[canonicalPullbackChoice 𝒮.p] x)).inv) ≫
        ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) := by
  let A :
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≅
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (q ^*[canonicalPullbackChoice 𝒮.p] x) :=
    (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x)) ≪≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
        (f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.symm.hom)
  let B :
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
          (((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≅
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (q ^*[canonicalPullbackChoice 𝒮.p] x) :=
    ((Cat.Hom.toNatIso
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w)).symm.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≪≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x)
  have heInv :
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
          f.op.toLoc g.op.toLoc q.op.toLoc w).inv.toNatTrans.app x = e.inv := by
    simpa [Cat.Hom.toNatIso] using
      iso_inv_eq_of_hom_eq_p06
        ((Cat.Hom.toNatIso
          ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
            f.op.toLoc g.op.toLoc q.op.toLoc w)).app x) e he
  simpa [A, B, Category.assoc, Cat.Hom.toNatIso] using
    iso_inv_eq_of_hom_eq_p06 A B
      (automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom_p06
        (𝒮 := 𝒮) hAbelian f g q x w e heInv)

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

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
        ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x) ≪≫
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
            (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_source_iso
            (𝒮 := 𝒮) hGerbe q g hg).inv).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv := by
  -- Consume the generic two-step base-change bridge with the chosen-local source common-owner
  -- comparison, then cancel the outer `q`-base-change isomorphism.
  have w : K.f.op.toLoc ≫ g.op.toLoc = q.op.toLoc := by cat_disch
  have hbr := automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom_p06
    (𝒮 := 𝒮) hAbelian K.f g q x w
    (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe q g hg)
    (chosen_local_common_owner_source_iso_inv_eq_mapComp'_inv_app
      (𝒮 := 𝒮) hGerbe q g hg)
  simp only [Iso.symm_hom] at hbr
  have hbr2 := Iso.eq_comp_inv
    (α := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x) |>.mpr hbr.symm
  rw [hbr2, Iso.trans_hom, Functor.mapIso_hom]
  erw [Category.assoc, Category.assoc]

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
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q z).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
        ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z) ≪≫
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
            (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv) := by
  -- Consume the inverse-side base-change bridge with the chosen-local target common-owner
  -- comparison, then cancel the outer `q`-base-change isomorphism and identify the conjugation
  -- inverse with the forward conjugation.
  have w : K.f.op.toLoc ≫ g.op.toLoc = q.op.toLoc := by cat_disch
  have hbr := automorphismUnderlyingSheafBaseChangeIso_comp_conj_inv_p06
    (𝒮 := 𝒮) hAbelian K.f g q z w
    (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg)
    (chosen_local_common_owner_target_iso_hom_eq_mapComp'_hom_app
      (𝒮 := 𝒮) hGerbe q g hg)
  -- `Conj` of the inverse comparison, inverted, is `Conj` of the forward comparison.
  have hconjinv :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).symm.hom).inv =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).hom).hom := by
    rw [← cancel_epi (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).symm.hom).hom]
    rw [Iso.hom_inv_id, ← Iso.trans_hom, ← automorphismUnderlyingSheafConj_comp,
      show (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).symm.hom ≫
          (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).hom = 𝟙 _ from
        (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).inv_hom_id,
      automorphismUnderlyingSheafConj_self (𝒮 := 𝒮) hAbelian (𝟙 _), Iso.refl_hom]
  -- Rewrite `hbr` into the goal's right-hand shape.
  rw [hconjinv] at hbr
  erw [Category.assoc] at hbr
  rw [← Functor.mapIso_inv] at hbr
  erw [← Iso.trans_inv] at hbr
  -- `hbr : (Conj target.hom).hom ≫ (mapIso ≪≫ bc).inv = bc(q,z).inv ≫ mapComp'.hom.app`
  exact (Iso.eq_inv_comp _ |>.mp hbr).symm

end

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
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
            (asIso (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom)).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv := by
  -- This is the base-change formula for pulling the conjugation along `g`.
  exact automorphismUnderlyingSheafConj_pullbackFunctor_map
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
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_source_iso
            (𝒮 := 𝒮) hGerbe q g hg).inv).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe q g hg).hom).hom) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv := by
  -- Start from the proven base-change formula for the pulled conjugation, then rewrite the middle
  -- conjugation through the common-owner factorization, which holds because the two middle
  -- morphisms are parallel.
  rw [chosen_local_pulled_conjugation_eq_pulled_iso_conj (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  refine congrArg (fun m =>
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫ m ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv) ?_
  have hiso :
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
            (asIso (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom)).hom =
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe q g hg).inv ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism (𝒮 := 𝒮) hGerbe q g hg).hom ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).hom := by
    rw [← automorphismUnderlyingSheafConj_comp, ← automorphismUnderlyingSheafConj_comp]
    exact automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _
  simpa using congrArg Iso.hom hiso

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

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
      ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe q g hg).inv).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).inv = 𝟙 _ := by
  -- The trailing three factors are exactly `mapComp'.inv` by the source bridge, so the composite
  -- is `mapComp'.hom ≫ mapComp'.inv = 𝟙`.
  erw [← chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  simpa [Cat.Hom.toNatIso] using
    Iso.hom_inv_id_app
      (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)))
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)

/-- Helper for Lemma 8.11.8: on the target side, the common-owner comparison cancels the raw
inverse `mapComp'` boundary map. -/
theorem chosen_local_target_boundary_normalization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q z).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
      ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) = 𝟙 _ := by
  -- The leading three factors are exactly `mapComp'.hom` by the target bridge, so the composite
  -- is `mapComp'.hom ≫ mapComp'.inv = 𝟙`.
  have h4 := chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian q g hg
  have hcancel :
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) = 𝟙 _ := by
    simpa [Cat.Hom.toNatIso] using
      Iso.hom_inv_id_app
        (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)))
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)
  rw [h4] at hcancel
  erw [Category.assoc, Category.assoc] at hcancel
  exact hcancel

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
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q z).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
      ((((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv) = 𝟙 _ := by
  -- The trailing three factors are exactly `mapComp'.hom` by the target bridge, so the composite
  -- is `mapComp'.inv ≫ mapComp'.hom = 𝟙`.
  erw [← chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  simpa [Cat.Hom.toNatIso] using
    Iso.inv_hom_id_app
      (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)))
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)

end

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

/-- Helper for Lemma 8.11.8: a generic category-theoretic telescoping identity.  All associativity
and inverse-pair cancellation happen on abstract morphisms (so `simp [Category.assoc]` is not
blocked by the `^*[cpc]`-object `kabstract` wall), and the two cancellation facts `h₁ ≫ h₁' = 𝟙`
and `k ≫ k' = 𝟙` are supplied by the caller as `mapComp'` hom/inv inverse pairs. -/
private theorem descent_square_telescope_p06 {D : Type*} [Category D]
    {O0 O1 O1' O2 O3 O4 O5 O6 : D}
    (p : O0 ⟶ O1) (bx : O1 ⟶ O1') (m : O1' ⟶ O2) (bz : O2 ⟶ O3)
    (h1 : O3 ⟶ O4) (h1' : O4 ⟶ O3) (j : O3 ⟶ O5)
    (k : O1 ⟶ O6) (k' : O6 ⟶ O1)
    (hh : h1 ≫ h1' = 𝟙 O3) (kk : k ≫ k' = 𝟙 O1) :
    ((p ≫ bx) ≫ m ≫ bz ≫ h1) ≫ h1' ≫ j =
      (p ≫ k) ≫ ((k' ≫ bx) ≫ m ≫ bz ≫ j) := by
  have hLHS : ((p ≫ bx) ≫ m ≫ bz ≫ h1) ≫ h1' ≫ j = p ≫ bx ≫ m ≫ bz ≫ j := by
    rw [show ((p ≫ bx) ≫ m ≫ bz ≫ h1) ≫ h1' ≫ j
        = p ≫ bx ≫ m ≫ bz ≫ (h1 ≫ h1') ≫ j by simp only [Category.assoc], hh, Category.id_comp]
  have hRHS : (p ≫ k) ≫ ((k' ≫ bx) ≫ m ≫ bz ≫ j) = p ≫ bx ≫ m ≫ bz ≫ j := by
    rw [show (p ≫ k) ≫ ((k' ≫ bx) ≫ m ≫ bz ≫ j)
        = p ≫ (k ≫ k') ≫ bx ≫ m ≫ bz ≫ j by simp only [Category.assoc], kk, Category.id_comp]
  rw [hLHS, hRHS]

/-- Helper for Lemma 8.11.8 (stackstest2 §1.2/§1.3): pulling the chosen-local conjugation
component `srcShell K = bc(K.f,x) ≪≫ Conj(chosen_local K) ≪≫ bc(K.f,z)⁻¹` back along one overlap
leg `g` factors, through the canonical `mapComp'` boundary comparisons, as the common-owner
conjugation over `q`. This is the source-faithful encoding of the fact that the local conjugation,
normalized to the common owner `q`, no longer depends on the particular cover arrow `K`. -/
theorem chosen_local_srcShell_pulled_eq_common_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x z : 𝒮.p.Fiber U} (q : Z ⟶ U)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom ≪≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z).symm).hom) =
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q z).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) := by
  -- Source-boundary fact `ha` (one `bc(q,x)` inverse pair cancels) and target-boundary fact `hb`
  -- (one `bc(q,z)` inverse pair cancels).
  have ha :
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_source_iso (𝒮 := 𝒮) hGerbe q g hg).inv).hom =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom := by
    have hL1 := chosen_local_source_mapComp'_inv_eq_common_owner_source_iso_inv
      (𝒮 := 𝒮) hGerbe hAbelian q g hg
    rw [Iso.trans_hom, Functor.mapIso_hom] at hL1
    rw [hL1]
    erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hb :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso (𝒮 := 𝒮) hGerbe q g hg).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
          (K.f ^*[canonicalPullbackChoice 𝒮.p] z)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z).inv =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q z).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) := by
    have hL2 := chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian q g hg
    rw [Iso.trans_inv, Functor.mapIso_inv] at hL2
    rw [hL2]
    erw [Iso.inv_hom_id_assoc]
    rfl
  -- Expand `srcShell K`, distribute the pullback functor, replace the pulled middle conjugation by
  -- its common-owner factorization, then assemble through the generic sandwich identity.
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.map_comp]
  erw [chosen_local_pulled_conjugation_eq_common_owner_middle (𝒮 := 𝒮) hGerbe hAbelian q g hg]
  exact comp_sandwich_eq_p06 ha hb

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
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁.f x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₁).hom ≪≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₁.f z).symm).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)).hom q g₁ g₂ =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow ↦ K.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom q g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂.f x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K₂).hom ≪≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K₂.f z).symm).hom) := by
  -- (1) Unfold both `toDescentData` transitions to their canonical `mapComp'` sandwiches.
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom]
  -- (2) Replace the two pulled `srcShell` legs by their common-owner forms (stackstest2 §1.2/§1.3),
  --     and identify the two common-owner middles (leg-independent by abelianity, §1.2).
  erw [chosen_local_srcShell_pulled_eq_common_owner (𝒮 := 𝒮) hGerbe hAbelian q g₁ hg₁]
  erw [chosen_local_srcShell_pulled_eq_common_owner (𝒮 := 𝒮) hGerbe hAbelian q g₂ hg₂]
  rw [chosen_local_common_owner_conjugation_eq (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂]
  -- (3) The two inner `mapComp'.hom.app ≫ mapComp'.inv.app` inverse pairs telescope, leaving the
  --     identical common-owner normal form on both sides; the cancellations + associativity are
  --     handled on abstract morphisms by `descent_square_telescope_p06`.
  have hh :
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)) = 𝟙 _ := by
    simpa [Cat.Hom.toNatIso] using
      Iso.hom_inv_id_app
        (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)))
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z)
  have w₂ : K₂.f.op.toLoc ≫ g₂.op.toLoc = q.op.toLoc := by
    simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
      congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg₂
  have kk :
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc w₂).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc w₂).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) = 𝟙 _ := by
    simpa [Cat.Hom.toNatIso] using
      Iso.hom_inv_id_app
        (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc w₂))
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
  exact descent_square_telescope_p06 _ _ _ _ _ _ _ _ _ hh kk

end

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover of two fiber objects, the
componentwise chosen local conjugations package into one descent-data isomorphism. This isolates
the pairwise-local comparison step before it is specialized to the pullback cover of `q`. -/
noncomputable def chosen_local_automorphism_descent_iso
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
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z K).hom ≪≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z).symm)
    (fun {_Y} q {_K₁ _K₂} g₁ g₂ hg₁ hg₂ ↦
      -- The `isoMk` square is exactly the chosen-local common-owner normalization (stackstest2
      -- §1.2/§1.3), proven above.
      chosen_local_automorphism_descent_square_normalized
        (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂)

/-- Helper for Lemma 8.11.8: transport the pairwise-local descent comparison for two locally
isomorphic fiber objects back to an isomorphism of sheaves on `C / U`. -/
noncomputable def chosen_local_automorphism_iso
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
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe x z L).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f z).inv := by
  -- Route correction: collapse the transported component to the bridged chosen-local conjugation
  -- map (now wrapped by base-change isos after the refactor).
  simpa [chosen_local_automorphism_descent_iso] using
    chosen_local_automorphism_iso_functor_map_component
      (𝒮 := 𝒮) hGerbe hAbelian x z L

/-- Helper for Lemma 8.11.8: for any locally-isomorphic cover overlap, the transported overlap
map is the first base-change, followed by the chosen-local comparison between the two overlap
objects, followed by the inverse second base-change. -/
theorem automorphism_overlap_hom_eq_chosen_local_tail
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂ hf₁ hf₂ =
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian f₁ (xS I₁)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian f₂ (xS I₂)).inv := by
  let Soverlap :=
    local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS
      (I₁ := I₁) (I₂ := I₂) f₁ f₂
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) Soverlap).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) Soverlap).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) Soverlap).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [automorphism_overlap_hom_secondary_cover_component
    (𝒮 := 𝒮) hGerbe hAbelian
    (S := S) (xS := xS) (q := q) (I₁ := I₁) (I₂ := I₂)
    (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂) (K := K)]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
    (𝒮 := 𝒮) hGerbe hAbelian S xS
    (I₁ := I₁) (I₂ := I₂) f₁ f₂ K]
  simp only [Soverlap, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv]
  have hlocal :=
    chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
      (𝒮 := 𝒮) hGerbe hAbelian
      (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
      (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component] at hlocal
  let F := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  let a :=
    F.map
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian f₁ (xS I₁)).hom
  let c :=
    F.map
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian f₂ (xS I₂)).inv
  simpa [F, a, c, local_overlap_source_object, local_overlap_target_object,
    local_overlap_conjugation_iso, local_overlap_isomorphism, Category.assoc] using
    (congrArg (fun m ↦ a ≫ m ≫ c) hlocal).symm

/-- Helper for Lemma 8.11.8: on one arrow of the pullback cover of the chosen gerbe cover of
`U`, compare the normalized source component with the automorphism sheaf of the pulled local
object `I.f ^* y`. This isolates the pointwise component before the remaining overlap square is
packaged by `isoMk`. -/
noncomputable def pullback_cover_local_object_component_iso
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
      (I.f ^*[canonicalPullbackChoice 𝒮.p] y) ≪≫
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f y).symm

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

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
          (𝒮 := 𝒮) hGerbe hAbelian q I₁ ≪≫
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).symm).hom) ≫
      (chosen_cover_descent_datum
        (𝒮 := 𝒮) hGerbe hAbelian U).hom (Y := Z) (r ≫ q)
        (i₁ := I₁.base) (i₂ := I₂.base) g₁ g₂
        (by
          have h₁ : g₁ ≫ I₁.f = r := hg₁
          simp only [GrothendieckTopology.Cover.Arrow.base_f]
          exact (reassoc_of% h₁) q)
        (by
          have h₂ : g₂ ≫ I₂.f = r := hg₂
          simp only [GrothendieckTopology.Cover.Arrow.base_f]
          exact (reassoc_of% h₂) q) =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).hom r g₁ g₂ hg₁ hg₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((pullback_cover_source_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q I₂ ≪≫
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).symm).hom) := by
  -- The source transition is the naturality square of the base-change comparison isomorphisms
  -- `pullback_cover_source_component_iso ≪≫ cover_iso.symm`, which after the cover comparison
  -- cancels are exactly the pseudofunctor `mapComp'` comparison `2`-cells.  The square is then
  -- the `3`-fold pseudofunctor associativity coherence (the pentagon), see stackstest2 §3.
  -- the three composing arrows over each branch are `q`, `Iᵢ.f`, `gᵢ`.
  have ha₁ : q.op.toLoc ≫ I₁.f.op.toLoc = (I₁.f ≫ q).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  have hb₁ : I₁.f.op.toLoc ≫ g₁.op.toLoc = r.op.toLoc := by
    simp only [← Quiver.Hom.comp_toLoc, ← op_comp]; rw [hg₁]
  have hc₁ : (I₁.f ≫ q).op.toLoc ≫ g₁.op.toLoc = (r ≫ q).op.toLoc := by
    simp only [← Quiver.Hom.comp_toLoc, ← op_comp]; rw [← Category.assoc, hg₁]
  have ha₂ : q.op.toLoc ≫ I₂.f.op.toLoc = (I₂.f ≫ q).op.toLoc := by
    simp [← Quiver.Hom.comp_toLoc, ← op_comp]
  have hb₂ : I₂.f.op.toLoc ≫ g₂.op.toLoc = r.op.toLoc := by
    simp only [← Quiver.Hom.comp_toLoc, ← op_comp]; rw [hg₂]
  have hc₂ : (I₂.f ≫ q).op.toLoc ≫ g₂.op.toLoc = (r ≫ q).op.toLoc := by
    simp only [← Quiver.Hom.comp_toLoc, ← op_comp]; rw [← Category.assoc, hg₂]
  simp only [pullback_cover_source_component_iso, chosen_cover_descent_datum,
    chosen_cover_descent_functor, Iso.trans_hom,
    Iso.symm_hom, Category.assoc,
    Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    GrothendieckTopology.Cover.Arrow.base_f]
  -- cancel the chosen-cover comparison isomorphisms inside `(F.map gᵢ).map`.
  erw [(chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom_inv_id,
    Category.comp_id,
    (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom_inv_id,
    Category.comp_id]
  -- normalise the `Cat.Hom.toNatIso` comparison cells to bare `mapComp'` natural transformations.
  have hn₁ : (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
        q.op.toLoc I₁.f.op.toLoc (I₁.f ≫ q).op.toLoc ha₁)).app
        (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U)).inv) =
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        q.op.toLoc I₁.f.op.toLoc (I₁.f ≫ q).op.toLoc ha₁).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U) := rfl
  have hn₂ : (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
        q.op.toLoc I₂.f.op.toLoc (I₂.f ≫ q).op.toLoc ha₂)).app
        (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U)).inv) =
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        q.op.toLoc I₂.f.op.toLoc (I₂.f ≫ q).op.toLoc ha₂).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U) := rfl
  erw [hn₁, hn₂]
  -- pentagon on the `I₁` (inverse) branch.
  erw [(J.pseudofunctorOver (Type (max u v))).mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
    q.op.toLoc I₁.f.op.toLoc g₁.op.toLoc
    (I₁.f ≫ q).op.toLoc r.op.toLoc (r ≫ q).op.toLoc ha₁ hb₁ hc₁
    (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U)]
  -- pentagon on the `I₂` (forward) branch.
  erw [(J.pseudofunctorOver (Type (max u v))).mapComp'₀₂₃_hom_app
    q.op.toLoc I₂.f.op.toLoc g₂.op.toLoc
    (I₂.f ≫ q).op.toLoc r.op.toLoc (r ≫ q).op.toLoc ha₂ hb₂ hc₂
    (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U)]
  -- the central `mapComp' q r (r≫q)` `inv ≫ hom` cancels.
  erw [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rfl

end

end CategoryTheory
