import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part11

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
private theorem chosen_cover_transport_transition_id_comp
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    (∀ U : C,
        chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := 𝟙 U)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U)) =
          (J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) ∧
      ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
        (J.overMapPullbackComp (Type (max u v)) g f).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
          chosen_cover_transport_transition
            (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
            (chosen_cover_descent_transition_iso
              (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)) =
            (J.overMapPullback (Type (max u v)) g).mapIso
              (chosen_cover_transport_transition
                (𝒮 := 𝒮) hGerbe hAbelian (f := f)
                (chosen_cover_descent_transition_iso
                  (𝒮 := 𝒮) hGerbe hAbelian f)) ≪≫
              chosen_cover_transport_transition
                (𝒮 := 𝒮) hGerbe hAbelian (f := g)
                (chosen_cover_descent_transition_iso
                  (𝒮 := 𝒮) hGerbe hAbelian g) := by
  constructor
  · intro U
    -- Route correction: the sheaf-side identity law is now completely reduced to the datum-side
    -- identity for `chosen_cover_descent_transition_iso (𝟙 U)`.
    apply
      chosen_cover_transport_transition_id_of_descent_identity
        (𝒮 := 𝒮) hGerbe hAbelian U
    -- The remaining identity-law blocker has been isolated as its own datum-side lemma.
    exact
      chosen_cover_descent_transition_iso_id_hom
        (𝒮 := 𝒮) hGerbe hAbelian U
  · intro U V W f g
    -- Route correction: the sheaf-side cocycle law is now reduced to one equality in the chosen
    -- cover descent category over `W`; the remaining proof should normalize both branches via
    -- `chosen_cover_transport_transition_functor_map` and `Pseudofunctor.DescentData.pullFunctorCompIso`.
    apply
      (chosen_cover_transport_transition_comp_reduction
        (𝒮 := 𝒮) hGerbe hAbelian f g).2
    -- First expose all transported sheaf-side comparisons as their datum-side morphisms on the
    -- chosen cover of `W`.
    rw [chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f))]
    rw [chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)]
    rw [chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian (f := g)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian g)]
    -- The remaining post-rewrite cocycle identity is now isolated in one helper after the three
    -- functor-map normalizations, so this theorem only packages the transport reduction.
    exact
      chosen_cover_transport_transition_comp_after_functor_map
        (𝒮 := 𝒮) hGerbe hAbelian f g

private theorem chosen_cover_pullback_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ transition : ∀ {U V : C} (f : V ⟶ U),
        (J.overMapPullback (Type (max u v)) f).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≅
          chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian V,
      (∀ U : C,
          transition (𝟙 U) =
            (J.overMapPullbackId (Type (max u v)) U).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U)) ∧
        ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          (J.overMapPullbackComp (Type (max u v)) g f).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
            transition (g ≫ f) =
              (J.overMapPullback (Type (max u v)) g).mapIso (transition f) ≪≫
                transition g := by
  -- Route correction: the remaining base-change step is still the datum-level pullback
  -- comparison on the chosen cover of the source object, together with its id/comp laws.
  -- The transport shell is now factored out into `chosen_cover_transport_transition` and
  -- `chosen_cover_transport_transition_functor_map`, so the remaining blocker is purely to build
  -- the datum-side identity/composition laws for the now-packaged transition
  -- `chosen_cover_descent_transition_iso`.
  refine ⟨fun {U V} f ↦ ?_, ?_⟩
  · -- First transport the packaged datum-side comparison back to the sheaf on `C / V`.
    exact
      chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian f
        (chosen_cover_descent_transition_iso
          (𝒮 := 𝒮) hGerbe hAbelian f)
  · exact
      chosen_cover_transport_transition_id_comp
        (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Lemma 8.11.8: once the chosen-cover descended slice sheaves are fixed, the
remaining absolute-glueing step is exactly to provide the transition isomorphisms and their
identity/cocycle laws. -/
theorem fixed_cover_absolute_glueing_transition
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ transition : ∀ {U V : C} (f : V ⟶ U),
        (J.overMapPullback (Type (max u v)) f).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≅
          chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian V,
      (∀ U : C,
          transition (𝟙 U) =
            (J.overMapPullbackId (Type (max u v)) U).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U)) ∧
        ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
          (J.overMapPullbackComp (Type (max u v)) g f).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
            transition (g ≫ f) =
              (J.overMapPullback (Type (max u v)) g).mapIso (transition f) ≪≫
                transition g := by
  -- Route correction: the source proof constructs these maps first on chosen-cover descent data
  -- and only then transports them back with `localizedSheafFromCoverDescentData_mapIso`.
  exact chosen_cover_pullback_descent_iso (𝒮 := 𝒮) hGerbe hAbelian

/-- Helper for Lemma 8.11.8: if the comparison between the descended chosen-cover sheaf and one
local automorphism sheaf is first built on the chosen-cover descent-data side, then the previous
transport helper turns it into the required slice-sheaf comparison on `C / U`. This removes all
later sheaf-side bookkeeping from the remaining slice-local source-proof task. -/
private noncomputable def chosenCoverSliceComparisonOfDescentIso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (e :
      ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≅
        ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) :
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
  -- Transport the chosen-cover descent-data comparison back across the explicit cover-descent
  -- equivalence for the fixed gerbe cover of `U`.
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) e

/-- Helper for Lemma 8.11.8: after applying the chosen-cover descent functor to the transported
slice comparison, one recovers the original descent-data morphism. This pins the remaining slice
comparison blocker down to constructing the descent-data comparison itself. -/
theorem chosenCoverSliceComparisonOfDescentIso_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (e :
      ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≅
        ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).functor.map
      (chosenCoverSliceComparisonOfDescentIso
        (𝒮 := 𝒮) hGerbe hAbelian x e).hom) = e.hom := by
  -- This is exactly the generic transport characterization specialized to the fixed chosen cover.
  simpa [chosenCoverSliceComparisonOfDescentIso] using
    localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) e

/-- Helper for Lemma 8.11.8: on one fixed slice `C / U`, the comparison from the descended
chosen-cover sheaf to the automorphism sheaf of `x` is obtained by first removing the trivial
identity-pullback shell and then applying the already-built pullback comparison specialized to
`q = 𝟙 U`. -/
private noncomputable def chosen_cover_identity_pullback_comparison_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) :=
  ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
      (((J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).symm)) ≪≫
    chosen_cover_pullback_to_local_object_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x

/-- Helper for Lemma 8.11.8: a chosen-cover arrow of `U` also defines the corresponding arrow of
the pullback cover of that same chosen cover along `𝟙 U`. -/
private theorem chosen_cover_identity_pullback_arrow_hf
    (hGerbe : IsGerbe J 𝒮.p) {U : C}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U)) L.f := by
  -- Membership in the identity pullback cover is exactly membership in the original chosen cover.
  simpa [chosen_cover_pullback_cover] using L.hf

/-- Helper for Lemma 8.11.8: realize one chosen-cover arrow `L` as the corresponding arrow of the
identity pullback cover used in the source-faithful comparison for `q = 𝟙 U`. -/
private noncomputable def chosen_cover_identity_pullback_arrow
    (hGerbe : IsGerbe J 𝒮.p) {U : C}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U)).Arrow :=
  ⟨L.Y, L.f, chosen_cover_identity_pullback_arrow_hf (𝒮 := 𝒮) hGerbe L⟩

/-- Helper for Lemma 8.11.8: the identity-pullback arrow attached to `L` has base arrow exactly
`L` in the original chosen gerbe cover of `U`. -/
private theorem chosen_cover_identity_pullback_arrow_base
    (hGerbe : IsGerbe J 𝒮.p) {U : C}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L).base = L := by
  -- Only the identity-composition shell introduced by `Arrow.base` has to be simplified away.
  ext <;> simp [chosen_cover_identity_pullback_arrow]

/-- Helper for Lemma 8.11.8: on one chosen-cover arrow `L`, the pulled comparison to `x` on the
slice `C / L.Y` is the component of the identity-pullback cover comparison indexed by the
corresponding pullback-cover arrow. -/
private theorem chosen_cover_identity_pullback_component_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x).hom) =
      (pullback_cover_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x
        (chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L)).hom := by
  let I := chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L
  let e := pullback_cover_local_object_comparison_descent_iso
    (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x
  -- Evaluate the sheaf comparison through the explicit cover-descent equivalence on the
  -- identity pullback cover, and then read off the `I`-component of the transported datum iso.
  rw [← localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U))
    ((chosen_cover_pullback_to_local_object_iso
      (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x).hom) I]
  simpa [chosen_cover_pullback_to_local_object_iso, e, I] using
    congrArg (fun φ ↦ φ.hom I)
      (localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
        (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U)) e)

/-- Helper for Lemma 8.11.8: after identifying the unique identity-pullback-cover leg over `L`,
the pulled comparison to `x` factors through the fixed chosen-cover source component and the
local chosen-object comparison over `L.f`. -/
theorem chosen_cover_identity_pullback_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x).hom) =
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U L).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) := by
  -- Unfold the identity-pullback-cover component and replace its base arrow by `L`.
  rw [chosen_cover_identity_pullback_component_hom
    (𝒮 := 𝒮) hGerbe hAbelian x L]
  simpa [pullback_cover_local_object_component_iso, pullback_cover_source_component_iso,
    chosen_cover_identity_pullback_arrow, chosen_cover_identity_pullback_arrow_base]

/-- Helper for Lemma 8.11.8: for one fixed chosen-local component `K` over `(A, L.f^* x)` and one
section object `T : Over K.Y`, pulling back the chosen local cover of `(A, L.f^* y)` along
`T.unop.hom ≫ K.f` gives the source-faithful refinement cover on the slice `C / K.Y`. -/
theorem chosen_local_target_cover_on_slice
    (hGerbe : IsGerbe J 𝒮.p)
    {U : C} {x y : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ) :
    ∃ B : J.Cover T.unop.left,
      ∃ R : (J.over K.Y).Cover T.unop,
        (R : Sieve T.unop) = (Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left) := by
  let qT := T.unop.hom ≫ K.f
  let B : J.Cover T.unop.left :=
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback qT
  let R : (J.over K.Y).Cover T.unop :=
    ⟨(Sieve.overEquiv T.unop).symm (B : Sieve T.unop.left),
      J.overEquiv_symm_mem_over T.unop (B : Sieve T.unop.left) B.condition⟩
  -- This is exactly the slice-site cover obtained from the pulled `y`-cover via `Sieve.overEquiv`.
  exact ⟨B, R, rfl⟩

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
identity leg over `I.Y.left` and the base arrow of `Ī.base` define the same common owner
`qI := I.Y.hom ≫ K.f`. This isolates the owner-arrow witness needed before transporting the right
branch to `op (Over.mk (𝟙 I.Y.left))`. -/
theorem chosen_local_target_refinement_member_identity_leg_eq
    (hGerbe : IsGerbe J 𝒮.p)
    {U : C} {x y : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    (𝟙 I.Y.left) ≫ Ky.f = qI := by
  -- The pulled `y`-cover member has base arrow over exactly the same owner as the restricted
  -- `x`-branch component.
  dsimp
  simpa [hĪ, Category.assoc] using congrArg (fun k ↦ I.f.left ≫ k) Ī.base_f

/-- Helper for Lemma 8.11.8: once the previous common-owner witness is fixed, the `Over.map`
image of the identity leg on `I.Y.left` under the pulled chosen local `y`-cover arrow is exactly
the owner object `I.Y`. This is the object-level transport needed before applying the right-branch
owner-transport rewrite. -/
private theorem chosen_local_target_refinement_member_owner_obj_eq_op
    (hGerbe : IsGerbe J 𝒮.p)
    {U : C} {x y : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    op ((Over.map Ky.f).obj (Over.mk (𝟙 I.Y.left))) = op I.Y := by
  -- Move the common-owner witness to the opposite owner object used by `.app`.
  dsimp
  simpa using
    over_map_obj_mk_eq_op Ī.base.f (𝟙 I.Y.left) (I.Y.hom ≫ K.f)
      (chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I Ī hĪ)

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
right branch first simplifies by naturality to evaluation of the pulled chosen-local comparison at
`op I.Y`. This isolates the outer restriction shell before the remaining owner transport. -/
theorem chosen_local_target_refinement_member_right_branch_restrict_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α) =
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op I.Y))
        αI) := by
  -- First peel off the outer restriction from the right branch by naturality of sheaf morphisms.
  dsimp
  simpa using
    sheaf_hom_app_restrict_eq
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))
      I.f α

/-- Helper for Lemma 8.11.8: on the fixed target refinement member `Ky := Ī.base`, the component
of the chosen-local `y` comparison is exactly the corresponding chosen-local descent component,
evaluated on the identity object of `C / I.Y.left`. This isolates the cover-descent rewrite from
the remaining owner transport to the common owner `qI`. -/
theorem chosen_local_target_refinement_member_right_branch_image_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI =
      ((((chosen_local_automorphism_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI := by
  -- Evaluate the component theorem for `chosen_local_automorphism_iso` on the fixed target
  -- refinement member `Ky`.
  dsimp
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app (op (Over.mk (𝟙 I.Y.left)))))
        (chosen_local_automorphism_iso_functor_map_component
          (𝒮 := 𝒮) hGerbe hAbelian
          (x := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (z := L.f ^*[canonicalPullbackChoice 𝒮.p] y) Ī.base))
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)

/-- Helper for Lemma 8.11.8: the target chosen-local comparison evaluated on one refinement
member can be moved from the owner object `op I.Y` to the literal common-owner shell
`op (Over.mk (𝟙 I.Y.left))` for the pulled `y`-cover arrow `Ky := Ī.base`. This isolates the
pure owner-transport step before the component is replaced by the descent datum. -/
theorem chosen_local_target_refinement_member_right_branch_common_owner_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI =
      ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
          (op I.Y))
        αI) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let Ky :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
    Ī.base
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  have hgy : (𝟙 I.Y.left) ≫ Ky.f = qI := by
    -- Reuse the pulled `y`-cover owner witness for this refinement member.
    simpa [qI, Ky] using
      chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I Ī hĪ
  have hObjop :
      op ((Over.map Ky.f).obj (Over.mk (𝟙 I.Y.left))) = op I.Y := by
    -- Move the common-owner equality to the opposite owner object used by `.app`.
    simpa [qI, Ky] using
      chosen_local_target_refinement_member_owner_obj_eq_op
        (𝒮 := 𝒮) hGerbe L K T I Ī hĪ
  -- Route correction: this is the same owner-transport normalization as the earlier chosen-cover
  -- branch proof, specialized to the pulled chosen-local `y`-cover arrow `Ky`.
  dsimp [qI, Ky, αI]
  symm
  simpa [hObjop] using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := Ī.base.f)
      (φ := (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)
      (k := 𝟙 I.Y.left) (h := I.Y.hom ≫ K.f) (hk := hgy)
      (s := ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)))

/-- Helper for Lemma 8.11.8: once the right branch is evaluated on the literal owner object
`op (Over.mk (𝟙 I.Y.left))`, the `Ky` component of
`chosen_local_automorphism_descent_iso` is already the common-owner conjugation shell over
`qI := I.Y.hom ≫ K.f`. This isolates the last right-branch normalization before the final
cross-cover common-owner comparison. -/
theorem chosen_local_target_refinement_member_descent_component_qI_shell_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((chosen_local_automorphism_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app
      (op (Over.mk (𝟙 I.Y.left))))
      αI =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
            (by simp [qI, Ky, chosen_local_target_refinement_member_identity_leg_eq
              (𝒮 := 𝒮) hGerbe L K T I Ī hĪ])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let Ky :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
    Ī.base
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  have hgy : (𝟙 I.Y.left) ≫ Ky.f = qI := by
    -- The identity leg on the refinement member is already the owner witness for `Ky`.
    simpa [qI, Ky] using
      chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I Ī hĪ
  -- Route correction: normalize the descent component itself, not only the already transported
  -- chosen-local comparison map.
  dsimp [qI, Ky, αI]
  simpa only [Category.comp_id, id_comp] using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app (op (Over.mk (𝟙 I.Y.left)))))
        (chosen_local_pulled_conjugation_eq_common_owner_middle
          (𝒮 := 𝒮) hGerbe hAbelian qI
          (K := Ī.base) (g := 𝟙 I.Y.left) hgy))
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_refinement_member_restrict_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app T) α) =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app
        (op I.Y))
      αI := by
  -- First remove the outer restriction from the source branch by naturality of the composite
  -- sheaf morphism on the pulled chosen local `x`-cover.
  dsimp
  simpa using
    sheaf_hom_app_restrict_eq
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)))
      I.f α

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_refinement_member_owner_transport_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let sourceI :=
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
        (op I.Y))
      αI)
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app
      (op I.Y))
      sourceI =
      (((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
          (op (Over.mk qI))))
        (Eq.mp
          (congrArg
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj)
            (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl))
          sourceI) := by
  -- This is the generic owner-transport rewrite for the `K.f`-pulled `φ`-branch, with the
  -- already isolated source section `sourceI` as input.
  dsimp
  simpa using
    (pseudofunctor_over_map_app_eq_owner_transport
      (J := J) (g := K.f)
      (φ := ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))
      (k := I.Y.hom) (h := I.Y.hom ≫ K.f) (hk := rfl)
      (s := ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
        (op I.Y))
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α))))

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_refinement_member_transported_section_eq_mapped_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (_φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let sourceI :=
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
        (op I.Y))
      αI)
    Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj)
          (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl))
        sourceI =
      ((((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI) := by
  -- Route correction: the transported source section is exactly the `I.Y.hom`-pulled evaluation
  -- of the chosen-local conjugation on the literal owner `op (Over.mk (𝟙 I.Y.left))`.
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  let sourceI :=
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
      (op I.Y))
    αI)
  -- Expose the pulled chosen-local conjugation at the literal identity owner over `I.Y.left`.
  dsimp [qI, αI, sourceI]
  symm
  simpa using
    (pseudofunctor_over_map_app_eq_image_app
      (J := J) (g := I.Y.hom)
      (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)
      (k := 𝟙 I.Y.left))

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_pulled_phi_mapComp_qI_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    {T : (Over K.Y)ᵒᵖ}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_target_iso
          (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
          (by simp [qI])).hom).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
      ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom := by
  -- Collapse the target-side common-owner comparison against the raw `mapComp'` boundary first.
  dsimp
  rw [Category.assoc, chosen_local_target_boundary_normalization
    (𝒮 := 𝒮) hGerbe hAbelian (q := I.Y.hom ≫ K.f) (K := K) (g := I.Y.hom)]
  -- The remaining map is exactly the pullback of conjugation by `pulledφ` to the owner `qI`.
  simpa [Functor.mapIso_hom] using
    automorphismUnderlyingSheafConj_pullbackFunctor_map
      (𝒮 := 𝒮) hAbelian (I.Y.hom ≫ K.f)
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ)

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem automorphismUnderlyingSheafConj_outer_app_eq_pulled_app
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} {x y : 𝒮.p.Fiber U} (f : Y ⟶ U) (q : Z ⟶ Y) (φ : x ⟶ y) :
    let pulledφ :
        (f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).map φ
    ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
      (op (Over.mk q))) =
      (((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 Z))))) := by
  let pulledφ :
      (f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).map φ
  -- Route correction: first rewrite the outer sheaf morphism as conjugation by the pulled
  -- morphism over `Y`, and only then move its evaluation to the literal identity owner of `Z`.
  rw [automorphismUnderlyingSheafConj_pullbackFunctor_map
    (𝒮 := 𝒮) hAbelian f φ]
  -- The `q`-pullback component at `op (Over.mk (𝟙 Z))` is definitionally the original component
  -- at `op (Over.mk q))`.
  simpa [pulledφ] using
    (pseudofunctor_over_map_app_eq_image_app
      (J := J) (g := q)
      (φ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
      (k := 𝟙 Z))

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
private theorem chosen_local_pulled_conjugation_eq_common_owner_middle_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U}
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    ((((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI) =
      ((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv.hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  have hMiddle :
      ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_source_iso
            (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv.hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])).hom).hom := by
    -- The chosen-local pulled conjugation already factors through the shared owner `qI`.
    simpa [qI, Category.assoc] using
      chosen_local_pulled_conjugation_eq_common_owner_middle
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) (g := I.Y.hom) (by simp [qI])
  -- Evaluate the normalized common-owner factorization on the literal owner section `αI`.
  simpa [αI, Category.assoc] using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app (op (Over.mk (𝟙 I.Y.left)))))
        hMiddle)
      αI

/-- Helper for Lemma 8.11.8: on one refinement member of the pulled chosen local `y`-cover, the
restricted left branch can be rewritten all the way to the shared-owner `qI := I.Y.hom ≫ K.f`
shell for the source chosen local cover arrow `K`, followed by the pulled morphism on that same
owner. This isolates the last source-side transport before the cross-cover common-owner
comparison is applied. -/
theorem chosen_local_source_common_owner_boundary_shell_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow)
    (K :
      (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α :
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T))
    {B : J.Cover T.unop.left}
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) (Ī : B.Arrow) (_hĪ : Ī.f = I.f.left) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    ((((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
        (op (Over.mk qI))))
      ((((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        αI)) =
      ((((((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv.hom).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      αI) := by
  let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
  let αI :=
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
  let pulledφ :
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
  have hOuter :
      ((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
        (op (Over.mk qI))) =
        (((((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))) := by
    -- Rewrite the outer conjugation along `L.f` as conjugation by the pulled morphism on `qI`.
    simpa [qI, pulledφ] using
      automorphismUnderlyingSheafConj_outer_app_eq_pulled_app
        (𝒮 := 𝒮) hAbelian L.f I.Y.hom φ
  -- First move the outer branch to the literal owner `op (Over.mk (𝟙 I.Y.left))`.
  rw [hOuter]
  -- Then replace the inner chosen-local conjugation by the common-owner factorization.
  rw [chosen_local_pulled_conjugation_eq_common_owner_middle_app
    (𝒮 := 𝒮) hGerbe hAbelian L K T α I]
  -- The remaining source-side mismatch is now isolated as one explicit evaluated boundary shell.
  simp [Category.assoc]

end CategoryTheory
