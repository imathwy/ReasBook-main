import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part14

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: after removing the common
`overMapPullbackId` shell from `chosen_cover_identity_pullback_comparison_descent_iso`, the
remaining comparison to `x` is compatible with conjugation along any morphism `φ : x ⟶ y`. This
is the thin adapter needed to finish the slice comparison on the chosen cover of `U`. -/
private theorem chosen_cover_identity_pullback_comparison_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    chosen_cover_pullback_to_local_object_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x ≪≫
      ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)) =
      chosen_cover_pullback_to_local_object_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) y := by
  -- Route correction: first collapse the isomorphism equality to descent-data components on the
  -- chosen cover of `U`; the remaining blocker is then a single pulled-sheaf equality on each
  -- chosen-cover arrow.
  apply Iso.ext
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  -- Evaluate the three descent-data morphisms on the fixed chosen-cover arrow `L`.
  rw [chosen_cover_pullback_to_local_object_component_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x L]
  rw [chosen_cover_descent_functor_mapIso_conj_component
    (𝒮 := 𝒮) hGerbe hAbelian φ L]
  rw [chosen_cover_identity_pullback_component_normalized
    (𝒮 := 𝒮) hGerbe hAbelian x L]
  rw [chosen_cover_identity_pullback_component_normalized
    (𝒮 := 𝒮) hGerbe hAbelian y L]
  -- Cancel the common chosen-cover source comparison first; the remaining source-faithful work is
  -- now purely the local chosen-object comparison over `L.f`.
  rw [Category.assoc]
  cancel_mono
  -- The exposed local comparison on `C / L.Y` is now isolated as its own theorem.
  simpa using
    chosen_local_automorphism_iso_pulled_conj
      (𝒮 := 𝒮) hGerbe hAbelian φ L

/-- Helper for Lemma 8.11.8: for one fixed base object `U`, the descended chosen-cover slice
sheaf on `C / U` admits the required comparisons to the local underlying automorphism sheaves, and
these comparisons are compatible with conjugation inside the fiber over `U`. This isolates the
per-slice source-faithful comparison step from the later global packaging over all `U`. -/
private theorem chosen_cover_comparison_descent_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} :
    ∃ comparison : ∀ (x : 𝒮.p.Fiber U),
        ((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≅
          ((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x),
      ∀ {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫
            (((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).mapIso
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)) =
          comparison y := by
  -- Route correction: the remaining slice-local step is the chosen-cover comparison on descent
  -- data; afterwards the sheaf-side comparison is only transport through the chosen-cover
  -- descent equivalence.
  refine ⟨fun x ↦ ?_, ?_⟩
  · -- Package the already-built identity-pullback comparison on the chosen cover of `U`.
    exact
      chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x
  · intro x y φ
    -- Reassociate once so the common `overMapPullbackId` shell is factored out, and then invoke
    -- the dedicated adapter for the remaining comparison to `x` and `y`.
    calc
      chosen_cover_identity_pullback_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian x ≪≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).mapIso
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)) =
        ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
            (((J.overMapPullbackId (Type (max u v)) U).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U)).symm)) ≪≫
          (chosen_cover_pullback_to_local_object_descent_iso
              (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x ≪≫
            ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ))) := by
              simp [chosen_cover_identity_pullback_comparison_descent_iso, Category.assoc]
      _ =
        ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
            (((J.overMapPullbackId (Type (max u v)) U).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian U)).symm)) ≪≫
          chosen_cover_pullback_to_local_object_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) y := by
              exact
                congrArg
                  (fun i ↦
                    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
                      (((J.overMapPullbackId (Type (max u v)) U).app
                        (chosen_cover_underlying_automorphism_sheaf
                          (𝒮 := 𝒮) hGerbe hAbelian U)).symm)) ≪≫ i)
                  (chosen_cover_identity_pullback_comparison_conj
                    (𝒮 := 𝒮) hGerbe hAbelian φ)
      _ =
        chosen_cover_identity_pullback_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian y := by
            simp [chosen_cover_identity_pullback_comparison_descent_iso]

/-- Helper for Lemma 8.11.8: for one fixed base object `U`, the descended chosen-cover slice
sheaf on `C / U` admits the required comparisons to the local underlying automorphism sheaves, and
these comparisons are compatible with conjugation inside the fiber over `U`. This isolates the
per-slice source-faithful comparison step from the later global packaging over all `U`. -/
theorem chosen_cover_slice_comparison
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} :
    ∃ comparison : ∀ (x : 𝒮.p.Fiber U),
        chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∀ {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
  -- Route correction: the actual remaining comparison problem is slice-local in `U`; the later
  -- theorem only has to package these local comparisons uniformly across all base objects.
  obtain ⟨comparison, hcomparison⟩ :=
    chosen_cover_comparison_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian (U := U)
  refine ⟨fun x ↦ ?_, ?_⟩
  · -- Transport the datum-level chosen-cover comparison back to the slice sheaf on `C / U`.
    exact
      chosenCoverSliceComparisonOfDescentIso
        (𝒮 := 𝒮) hGerbe hAbelian x (comparison x)
  · intro x y φ
    let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
    let E := localizedSheafToCoverDescentEquivalence (J := J) S
    -- Compare the two transported slice comparisons after applying the chosen-cover descent
    -- equivalence; the transport shells contract to the datum-level compatibility.
    apply Functor.map_injective E.functor
    rw [Functor.map_comp, Functor.map_comp]
    rw [chosenCoverSliceComparisonOfDescentIso_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian x (comparison x)]
    rw [chosenCoverSliceComparisonOfDescentIso_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian y (comparison y)]
    change
      (comparison x).hom ≫
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).mapIso
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)).hom) =
        (comparison y).hom
    simpa using congrArg Iso.hom (hcomparison (x := x) (y := y) φ)

/-- Helper for Lemma 8.11.8: once the chosen-cover descended slice sheaf on `C / U` is fixed, the
remaining local comparison to `Aut(x)` is a transported chosen-cover descent-data isomorphism. -/
private theorem fixed_cover_absolute_glueing_comparison
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
  refine ⟨fun {U} x ↦ ?_, ?_⟩
  · -- The remaining work is already isolated in the per-slice comparison theorem for this `U`.
    exact Classical.choose
      (chosen_cover_slice_comparison (𝒮 := 𝒮) hGerbe hAbelian (U := U)) x
  · intro U x y φ
    -- The global compatibility statement is exactly the slice-local compatibility packaged above.
    exact
      (Classical.choose_spec
        (chosen_cover_slice_comparison (𝒮 := 𝒮) hGerbe hAbelian (U := U))) φ

/-- Helper for Lemma 8.11.8: once the chosen slice sheaves, their transition family, and the
local comparisons to underlying automorphism sheaves are available, they package directly into an
absolute glueing. -/
private theorem absolute_glueing_of_underlying_automorphism_slices
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (transition : ∀ {U V : C} (f : V ⟶ U),
      (J.overMapPullback (Type (max u v)) f).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≅
        chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian V)
    (transition_id : ∀ U : C,
      transition (𝟙 U) =
        (J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U))
    (transition_comp : ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      (J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
        transition (g ≫ f) =
          (J.overMapPullback (Type (max u v)) g).mapIso (transition f) ≪≫
            transition g)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U ≅
        automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison' y := by
  refine
    ⟨{ obj := chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian
        transition := fun {U V} f ↦ transition f
        transition_id := transition_id
        transition_comp := fun f g ↦ transition_comp f g }, ?_⟩
  exact ⟨comparison, hcomparison⟩

/-- Helper for Lemma 8.11.8: an isomorphism of absolute glueing data induces an isomorphism on
each localized sheaf. -/
private noncomputable def absolute_glueing_iso_app
    {F G : GrothendieckTopology.AbsoluteGlueing J} (η : F ≅ G) (U : C) :
    F.obj U ≅ G.obj U where
  hom := η.hom.app U
  inv := η.inv.app U
  hom_inv_id := by
    -- The inverse law for the absolute-glueing isomorphism is checked componentwise.
    simpa using congrArg (fun α ↦ α.app U) η.hom_inv_id
  inv_hom_id := by
    -- The same componentwise argument gives the reverse inverse law.
    simpa using congrArg (fun α ↦ α.app U) η.inv_hom_id

/-- Helper for Lemma 8.11.8: the Chapter 7 absolute-glueing equivalence reconstructs a global
`Type`-valued sheaf from local slice sheaves with transition data. -/
private noncomputable def absolute_glueing_reconstruction
    (F : GrothendieckTopology.AbsoluteGlueing J) :
    Sheaf J (Type (max u v)) :=
  ((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence).inverse.obj F

/-- Helper for Lemma 8.11.8: the reconstructed sheaf restricts back to the prescribed local sheaf
on each slice `C/U`. -/
private noncomputable def absolute_glueing_reconstruction_over_iso
    (F : GrothendieckTopology.AbsoluteGlueing J) (U : C) :
    (absolute_glueing_reconstruction (J := J) F).over U ≅ F.obj U :=
  let E : Sheaf J (Type (max u v)) ≌ GrothendieckTopology.AbsoluteGlueing J :=
    (GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence
  absolute_glueing_iso_app (η := E.counitIso.app F) U

/-- Helper for Lemma 8.11.8: reconstructing the canonical absolute glueing of a sheaf recovers
its original restriction map on sections. -/
private theorem sheaf_to_absolute_glueing_reconstruction_map
    (F : Sheaf J (Type (max u v))) {U V : C} (f : V ⟶ U) :
    GrothendieckTopology.absoluteGlueingToPresheafMap J
        ((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj F) f =
      F.1.map f.op := by
  -- For canonical glueing data, the terminal-evaluation restriction is exactly the original
  -- restriction map of `F`.
  ext x
  simp [GrothendieckTopology.absoluteGlueingToPresheafMap,
    GrothendieckTopology.absoluteGlueing_transition_app_terminal,
    GrothendieckTopology.sheafToAbsoluteGlueingFunctor, Sheaf.over, Over.mapForget,
    Over.mapForget_eq]

/-- Helper for Lemma 8.11.8: the local counit isomorphisms from the Chapter 7 reconstruction are
compatible with the absolute-glueing transition maps. This isolates the transport square needed
before checking additivity of the reconstructed restriction maps. -/
private theorem absolute_glueing_reconstruction_over_iso_hom_naturality
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    CommSq
      ((J.overMapPullback (Type (max u v)) f).map
        ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom))
      (((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
          (absolute_glueing_reconstruction (J := J) F)).transition f).hom
      (F.transition f).hom
      ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom) := by
  let E : Sheaf J (Type (max u v)) ≌ GrothendieckTopology.AbsoluteGlueing J :=
    (GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).asEquivalence
  -- The reconstruction-over comparison is the counit of the equivalence at `F`, so its
  -- compatibility with `F.transition f` is exactly the naturality square of that counit.
  simpa [E, absolute_glueing_reconstruction, absolute_glueing_reconstruction_over_iso,
    absolute_glueing_iso_app] using
    ((E.counitIso.app F).hom.naturality (f := f))

/-- Helper for Lemma 8.11.8: the naturality square for the reconstruction-over counit can be
read as an explicit equality of restriction morphisms after reassociating the transport shell.
This is the equality shape needed when the final additive reconstruction compares the global
restriction map with the fixed-owner local one. -/
private theorem absolute_glueing_reconstruction_over_iso_hom_naturality_assoc
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    ((J.overMapPullback (Type (max u v)) f).map
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom)) ≫
        (F.transition f).hom =
      (((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
          (absolute_glueing_reconstruction (J := J) F)).transition f).hom ≫
        (absolute_glueing_reconstruction_over_iso (J := J) F V).hom := by
  -- Reassociate the counit naturality square once so later additive-transport lemmas can use it
  -- as a plain morphism equality instead of reopening the `CommSq` API.
  simpa [CommSq, Category.assoc] using
    (absolute_glueing_reconstruction_over_iso_hom_naturality (J := J) F (f := f)).w

/-- Helper for Lemma 8.11.8: pulling the terminal slice object `V / V` back along `f : V ⟶ U`
lands at the explicit slice object `Over.mk f`. This is the terminal-object normalization needed
before evaluating the reconstruction-over counit on sections. -/
private theorem absolute_glueing_reconstruction_over_map_obj_terminal_eq
    {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  -- Unfolding the pullback of the terminal slice object reduces the comparison to `𝟙 V ≫ f = f`.
  change Over.mk ((𝟙 V) ≫ f) = Over.mk f
  simpa using congrArg Over.mk (Category.id_comp f)

/-- Helper for Lemma 8.11.8: for a `Type`-valued functor, transport by `eqToHom` is the same as
the corresponding dependent cast. This keeps later terminal-component calculations explicit. -/
private theorem absolute_glueing_reconstruction_eqToHom_apply_eq_cast
    {D : Type*} [Category D] {G : D ⥤ Type*} {X Y : D} (p : X = Y) (x : G.obj X) :
    eqToHom (congrArg G.obj p) x = cast (congrArg G.obj p) x := by
  -- Reduce to the reflexive equality case, where both transports are definitionally identical.
  cases p
  rfl

/-- Helper for Lemma 8.11.8: a `Type`-valued natural transformation commutes with transport along
an equality of objects. This is the cast-compatibility needed for the terminal evaluation of the
reconstruction-over counit. -/
private theorem absolute_glueing_reconstruction_natTrans_app_cast_eq
    {D : Type*} [Category D] {P Q : D ⥤ Type*} (α : P ⟶ Q)
    {X Y : D} (q : X = Y) (s : P.obj X) :
    α.app Y (Eq.mp (congrArg P.obj q) s) = Eq.mp (congrArg Q.obj q) (α.app X s) := by
  -- Again, after reducing to `rfl`, both sides are the same term.
  cases q
  rfl

/-- Helper for Lemma 8.11.8: after evaluating the local counit isomorphisms
`absolute_glueing_reconstruction_over_iso` at the terminal slice objects, the reconstructed
restriction map is natural with respect to the original transition map of `F`. This isolates the
terminal-component transport identity that the final additive reconstruction must feed into the
fixed-owner additive comparison. -/
private theorem absolute_glueing_reconstruction_over_iso_terminal_naturality
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    GrothendieckTopology.absoluteGlueingToPresheafMap J
        ((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
          (absolute_glueing_reconstruction (J := J) F)) f ≫
      ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
        (Opposite.op (Over.mk (𝟙 V)))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
      GrothendieckTopology.absoluteGlueingToPresheafMap J F f := by
  let R : GrothendieckTopology.AbsoluteGlueing J :=
    ((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
      (absolute_glueing_reconstruction (J := J) F))
  ext x
  let xf : (R.obj U).obj.obj (Opposite.op (Over.mk f)) :=
    (R.obj U).obj.map
      (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op x
  let yf :
      ((J.overMapPullback (Type (max u v)) f).obj (R.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp
      (congrArg (fun X ↦ (R.obj U).obj.obj (Opposite.op X))
        (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
      xf
  let yg :
      ((J.overMapPullback (Type (max u v)) f).obj (F.obj U)).obj.obj
        (Opposite.op (Over.mk (𝟙 V))) :=
    Eq.mp
      (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
        (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
      ((F.obj U).obj.map
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
        (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk (𝟙 U)))) x))
  have hlocal :
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
          (Opposite.op (Over.mk f))) xf =
        (F.obj U).obj.map
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
          (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
            (Opposite.op (Over.mk (𝟙 U)))) x) := by
    -- This is ordinary naturality of the local counit comparison along `Over.homMk f`.
    simpa [xf, FunctorToTypes.map_comp_apply] using
      congrFun
        (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1).naturality
          (show Opposite.op (Over.mk (𝟙 U)) ⟶ Opposite.op (Over.mk f) from
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op))
        x
  have hpullback :
      (((J.overMapPullback (Type (max u v)) f).map
          ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom)).hom.app
            (Opposite.op (Over.mk (𝟙 V))) yf) = yg := by
    -- First move the pulled-back comparison through the terminal-object cast, then rewrite the
    -- resulting middle term by the local naturality of the counit comparison.
    have hcast :
        (((J.overMapPullback (Type (max u v)) f).map
            ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom)).hom.app
              (Opposite.op (Over.mk (𝟙 V))) yf) =
          Eq.mp
            (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
              (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
            (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
              (Opposite.op (Over.mk f))) xf) := by
      simpa [yf] using
        (absolute_glueing_reconstruction_natTrans_app_cast_eq
          (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1))
          ((congrArg Opposite.op
            (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm)
          xf)
    rw [hcast, hlocal]
    rfl
  have hsq :
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yg =
        ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
          (Opposite.op (Over.mk (𝟙 V))))
          ((((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
              (absolute_glueing_reconstruction (J := J) F)).transition f).hom.hom.app
            (Opposite.op (Over.mk (𝟙 V))) yf) := by
    -- Evaluate the already-isolated counit naturality equality at the terminal object of `C / V`.
    have hsq' :=
      congrFun
        (congrArg
          (fun τ ↦ τ.app (Opposite.op (Over.mk (𝟙 V))))
          (absolute_glueing_reconstruction_over_iso_hom_naturality_assoc
            (J := J) F (f := f)))
        yf
    have hsq'' :
        (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
            ((((J.overMapPullback (Type (max u v)) f).map
                ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom)).hom.app
                  (Opposite.op (Over.mk (𝟙 V)))) yf) =
          ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
            (Opposite.op (Over.mk (𝟙 V))))
            ((((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
                (absolute_glueing_reconstruction (J := J) F)).transition f).hom.hom.app
              (Opposite.op (Over.mk (𝟙 V))) yf) := by
      simpa [FunctorToTypes.map_comp_apply] using hsq'
    rw [hpullback] at hsq''
    exact hsq''
  have hyf :
      eqToHom
          (congrArg (fun X ↦ (R.obj U).obj.obj (Opposite.op X))
            (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
          xf = yf := by
    simpa [yf] using
      (absolute_glueing_reconstruction_eqToHom_apply_eq_cast
        (G := (R.obj U).obj)
        (p := (congrArg Opposite.op
          (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm)
        xf)
  have hyg :
      eqToHom
          (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
            (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
            (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
              (Opposite.op (Over.mk (𝟙 U)))) x)) = yg := by
    simpa [yg] using
      (absolute_glueing_reconstruction_eqToHom_apply_eq_cast
        (G := (F.obj U).obj)
        (p := (congrArg Opposite.op
          (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm)
        ((F.obj U).obj.map
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
          (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
            (Opposite.op (Over.mk (𝟙 U)))) x)))
  calc
    ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
        (Opposite.op (Over.mk (𝟙 V))))
        ((((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
            (absolute_glueing_reconstruction (J := J) F)).transition f).hom.hom.app
          (Opposite.op (Over.mk (𝟙 V)))
          (eqToHom
            (congrArg (fun X ↦ (R.obj U).obj.obj (Opposite.op X))
              (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
            xf)) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
        (Opposite.op (Over.mk (𝟙 V))))
        ((((GrothendieckTopology.sheafToAbsoluteGlueingFunctor (J := J)).obj
            (absolute_glueing_reconstruction (J := J) F)).transition f).hom.hom.app
          (Opposite.op (Over.mk (𝟙 V))) yf) := by
            rw [hyf]
    _ =
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V))) yg := hsq.symm
    _ =
      (F.transition f).hom.hom.app (Opposite.op (Over.mk (𝟙 V)))
        (eqToHom
          (congrArg (fun X ↦ (F.obj U).obj.obj (Opposite.op X))
            (absolute_glueing_reconstruction_over_map_obj_terminal_eq f)).symm
          ((F.obj U).obj.map
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
            (((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
              (Opposite.op (Over.mk (𝟙 U)))) x))) := by
            rw [hyg]

/-- Helper for Lemma 8.11.8: after rewriting the reconstructed restriction map by
`sheaf_to_absolute_glueing_reconstruction_map`, the terminal-component naturality of
`absolute_glueing_reconstruction_over_iso` becomes an explicit equality between the underlying
restriction map of the reconstructed sheaf and the given transition map of `F`. This is the
transport identity the final additive reconstruction should combine with the fixed-owner additive
comparisons. -/
private theorem absolute_glueing_reconstruction_restriction_map_after_transport
    (F : GrothendieckTopology.AbsoluteGlueing J) {U V : C} (f : V ⟶ U) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
        (Opposite.op (Over.mk (𝟙 V)))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
      GrothendieckTopology.absoluteGlueingToPresheafMap J F f := by
  -- Replace the left-hand map by the canonical absolute-glueing reconstruction formula and
  -- reuse the terminal-component counit naturality proved just above.
  simpa [sheaf_to_absolute_glueing_reconstruction_map (J := J)
    (F := absolute_glueing_reconstruction (J := J) F) (f := f)] using
    absolute_glueing_reconstruction_over_iso_terminal_naturality (J := J) F (f := f)

/-- Helper for Lemma 8.11.8: after the Chapter 7 reconstruction transport is normalized at the
terminal slice object of `C / V`, postcomposing with any fixed local comparison on `C / V`
produces the exact owner-level equality needed for the final additive packaging. -/
theorem absolute_glueing_reconstruction_restriction_map_after_local_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber V) :
    (absolute_glueing_reconstruction (J := J) F).1.map f.op ≫
      ((absolute_glueing_reconstruction_over_iso (J := J) F V).hom.1.app
        (Opposite.op (Over.mk (𝟙 V)))) ≫
      ((comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V)))) =
      ((absolute_glueing_reconstruction_over_iso (J := J) F U).hom.1.app
        (Opposite.op (Over.mk (𝟙 U)))) ≫
      GrothendieckTopology.absoluteGlueingToPresheafMap J F f ≫
      ((comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V)))) := by
  -- Postcompose the terminal transport identity with the fixed local owner comparison on `C / V`.
  simpa [Category.assoc] using
    congrArg
      (fun η ↦ η ≫ ((comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 V)))))
      (absolute_glueing_reconstruction_restriction_map_after_transport
        (J := J) (F := F) (f := f))

/-- Helper for Lemma 8.11.8: once the underlying automorphism sheaves on the localized sites have
been packaged as absolute glueing data, the Chapter 7 reconstruction yields a global sheaf on `C`
whose slice restrictions keep the prescribed automorphism-sheaf comparisons. -/
private theorem underlying_automorphism_band_of_absolute_glueing
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U), F.obj U ≅ Aut[𝒮](x))
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismSheafConj (𝒮 := 𝒮) φ = comparison y) :
    ∃ G : Sheaf J (Type (max u v)),
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U), G.over U ≅ Aut[𝒮](x),
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismSheafConj (𝒮 := 𝒮) φ = comparison' y := by
  refine ⟨absolute_glueing_reconstruction (J := J) F, ?_⟩
  refine ⟨fun {U} x ↦ ?_, ?_⟩
  · -- The reconstructed global sheaf agrees with the given localized glueing via the counit.
    exact absolute_glueing_reconstruction_over_iso (J := J) F U ≪≫ comparison x
  · intro U x y φ
    -- Precomposing the given localized comparison with the reconstruction isomorphism keeps the
    -- same conjugation compatibility.
    simpa using
      congrArg
        (fun i ↦ absolute_glueing_reconstruction_over_iso (J := J) F U ≪≫ i)
        (hcomparison (U := U) (x := x) (y := y) φ)

/-- Helper for Lemma 8.11.8: once an absolute glueing is identified with the underlying
canonical automorphism sheaves, the Chapter 7 reconstruction already yields the corresponding
global `Type`-valued automorphism band. This isolates the remaining proof work to constructing the
absolute glueing itself and then restoring the slice-wise additive structures. -/
private theorem underlying_absolute_glueing_to_underlying_automorphism_band
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    ∃ G : Sheaf J (Type (max u v)),
      ∃ comparison' : ∀ {U : C} (x : 𝒮.p.Fiber U), G.over U ≅ Aut[𝒮](x),
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison' x ≪≫ automorphismSheafConj (𝒮 := 𝒮) φ = comparison' y := by
  -- Convert the local comparisons to the canonical `Aut[𝒮](x)` owner once, then invoke the
  -- existing absolute-glueing reconstruction for underlying automorphism sheaves.
  refine
    underlying_automorphism_band_of_absolute_glueing
      (𝒮 := 𝒮) F
      (comparison := fun {U} x ↦
        comparison x ≪≫ automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian x)
      ?_
  intro U x y φ
  -- Reassociate the local comparison with the owner-change bridge
  -- `automorphismUnderlyingSheafIso_conj`.
  calc
    (comparison x ≪≫ automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian x) ≪≫
        automorphismSheafConj (𝒮 := 𝒮) φ =
      comparison x ≪≫
        (automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian x ≪≫
          automorphismSheafConj (𝒮 := 𝒮) φ) := by
            simp [Category.assoc]
    _ =
      comparison x ≪≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
          automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y) := by
            exact
              congrArg
                (fun i ↦ comparison x ≪≫ i)
                (automorphismUnderlyingSheafIso_conj
                  (𝒮 := 𝒮) hAbelian φ)
    _ =
      (comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ) ≪≫
        automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y := by
            simp [Category.assoc]
    _ = comparison y ≪≫ automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y := by
          exact congrArg (fun i ↦ i ≪≫ automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y)
            (hcomparison (U := U) (x := x) (y := y) φ)
    _ = (comparison y ≪≫ automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y) := rfl

/-- Helper for Lemma 8.11.8: construct the source-faithful absolute glueing whose local slice
sheaves are the descended automorphism sheaves for the fixed chosen covers. -/
theorem exists_underlying_automorphism_absolute_glueing
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Route correction: the chosen-cover slice sheaf is now fixed explicitly, so this theorem only
  -- packages the two remaining source-faithful ingredients: the absolute-glueing transitions and
  -- the local comparisons to arbitrary automorphism sheaves.
  obtain ⟨transition, htransition_id, htransition_comp⟩ :=
    fixed_cover_absolute_glueing_transition
      (𝒮 := 𝒮) hGerbe hAbelian
  obtain ⟨comparison, hcomparison⟩ :=
    fixed_cover_absolute_glueing_comparison
      (𝒮 := 𝒮) hGerbe hAbelian
  exact
    absolute_glueing_of_underlying_automorphism_slices
      (𝒮 := 𝒮) hGerbe hAbelian
      transition htransition_id htransition_comp comparison hcomparison

/-- Helper for Lemma 8.11.8: on one slice site `C / U`, any comparison between a `Type`-valued
sheaf `A` and the canonical underlying automorphism sheaf of `x` transports the additive
structure from `automorphismAddCommSheaf hAbelian x` back to `A`. -/
theorem slice_addcomm_sheaf_of_underlying_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (A : Sheaf (J.over U) (Type (max u v))) (x : 𝒮.p.Fiber U)
    (comparison : A ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) :
    ∃ A' : Sheaf (J.over U) AddCommGrpCat.{max u v},
      ∃ forgetIso : (A'.1 ⋙ forget AddCommGrpCat.{max u v}) ≅ A.1,
        ∃ liftedComparison : A' ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          Functor.whiskerRight liftedComparison.hom.1 (forget AddCommGrpCat.{max u v}) =
            forgetIso.hom ≫ comparison.hom.1 := by
  let sectionEquiv :
      ∀ T : (Over U)ᵒᵖ, A.1.obj T ≃ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T :=
    fun T ↦
      { toFun := comparison.hom.1.app T
        invFun := comparison.inv.1.app T
        left_inv := by
          intro a
          -- Evaluate the sheaf-iso inverse law at the section `a`.
          exact congrFun (congrArg (fun ψ ↦ (ψ.1.app T)) comparison.hom_inv_id) a
        right_inv := by
          intro a
          -- Evaluate the sheaf-iso forward law at the section `a`.
          exact congrFun (congrArg (fun ψ ↦ (ψ.1.app T)) comparison.inv_hom_id) a }
  let transportedPresheaf : (J.over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
    obj := fun T ↦ by
      let _ : AddCommGroup (A.1.obj T) := Equiv.addCommGroup (sectionEquiv T)
      exact AddCommGrpCat.of (A.1.obj T)
    map := fun {X Y} g ↦ by
      let _ : AddCommGroup (A.1.obj X) := Equiv.addCommGroup (sectionEquiv X)
      let _ : AddCommGroup (A.1.obj Y) := Equiv.addCommGroup (sectionEquiv Y)
      let eX :
          A.1.obj X ≃+ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj X :=
        { toEquiv := sectionEquiv X
          map_add' := by
            intro a b
            rfl }
      let eY :
          A.1.obj Y ≃+ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj Y :=
        { toEquiv := sectionEquiv Y
          map_add' := by
            intro a b
            rfl }
      exact
        AddCommGrpCat.ofHom <|
          AddMonoidHom.mk' (A.1.map g) <| by
            intro a b
            -- Transport additivity to `A.map g` through the comparison with the canonical
            -- abelian automorphism sheaf, where additivity is already built in.
            apply eY.injective
            have hnat_ab := congrFun (comparison.hom.1.naturality g) (a + b)
            have hnat_a := congrFun (comparison.hom.1.naturality g) a
            have hnat_b := congrFun (comparison.hom.1.naturality g) b
            calc
              comparison.hom.1.app Y (A.1.map g (a + b)) =
                  (𝒮.automorphismAddCommSheaf hAbelian x).1.map g
                    (comparison.hom.1.app X (a + b)) := hnat_ab
              _ =
                  (𝒮.automorphismAddCommSheaf hAbelian x).1.map g
                    (comparison.hom.1.app X a + comparison.hom.1.app X b) := by
                      rw [eX.map_add]
              _ =
                  (𝒮.automorphismAddCommSheaf hAbelian x).1.map g
                    (comparison.hom.1.app X a) +
                    (𝒮.automorphismAddCommSheaf hAbelian x).1.map g
                      (comparison.hom.1.app X b) := by
                        exact map_add _ _ _
              _ = comparison.hom.1.app Y (A.1.map g a) +
                    comparison.hom.1.app Y (A.1.map g b) := by
                      rw [hnat_a, hnat_b]
              _ = comparison.hom.1.app Y (A.1.map g a + A.1.map g b) := by
                    rw [eY.map_add]
    map_id := by
      intro X
      apply AddCommGrpCat.ext
      intro a
      rfl
    map_comp := by
      intro X Y Z g h
      apply AddCommGrpCat.ext
      intro a
      rfl
  let A' : Sheaf (J.over U) AddCommGrpCat.{max u v} where
    obj := transportedPresheaf
    property := by
      -- The transported additive structure forgets back to the original `Type`-valued sheaf.
      rw [Presheaf.isSheaf_iff_isSheaf_forget
        (J.over U) transportedPresheaf (forget AddCommGrpCat.{max u v})]
      simpa [transportedPresheaf] using A.property
  let forgetIso :
      (A'.1 ⋙ forget AddCommGrpCat.{max u v}) ≅ A.1 :=
    { hom :=
        { app := fun T a ↦ a
          naturality := by
            intro X Y g
            rfl }
      inv :=
        { app := fun T a ↦ a
          naturality := by
            intro X Y g
            rfl }
      hom_inv_id := by
        ext T a
        rfl
      inv_hom_id := by
        ext T a
        rfl }
  let liftedComparison :
      A' ≅ 𝒮.automorphismAddCommSheaf hAbelian x :=
    by
      let homNat : A'.1 ⟶ (𝒮.automorphismAddCommSheaf hAbelian x).1 :=
        { app := fun T ↦ by
            let _ : AddCommGroup (A.1.obj T) := Equiv.addCommGroup (sectionEquiv T)
            let eT :
                A.1.obj T ≃+ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T :=
              { toEquiv := sectionEquiv T
                map_add' := by
                  intro a b
                  rfl }
            exact AddCommGrpCat.ofHom eT.toAddMonoidHom
          naturality := by
            intro X Y g
            apply AddCommGrpCat.ext
            intro a
            -- The lifted comparison is exactly the original underlying natural isomorphism.
            exact congrFun (comparison.hom.1.naturality g) a }
      let invNat : (𝒮.automorphismAddCommSheaf hAbelian x).1 ⟶ A'.1 :=
        { app := fun T ↦ by
            let _ : AddCommGroup (A.1.obj T) := Equiv.addCommGroup (sectionEquiv T)
            let eT :
                A.1.obj T ≃+ (𝒮.automorphismAddCommSheaf hAbelian x).1.obj T :=
              { toEquiv := sectionEquiv T
                map_add' := by
                  intro a b
                  rfl }
            exact AddCommGrpCat.ofHom eT.symm.toAddMonoidHom
          naturality := by
            intro X Y g
            apply AddCommGrpCat.ext
            intro a
            -- Apply the inverse naturality by transporting once through the section equivalence.
            apply (sectionEquiv Y).injective
            have hnat := congrFun (comparison.inv.1.naturality g) a
            exact hnat }
      refine
        { hom := Sheaf.homEquiv.symm homNat
          inv := Sheaf.homEquiv.symm invNat
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      · apply Sheaf.hom_ext
        ext T a
        -- The inverse law is pointwise the left inverse of the transported section equivalence.
        exact (sectionEquiv T).left_inv a
      · apply Sheaf.hom_ext
        ext T a
        -- The forward law is pointwise the right inverse of the transported section equivalence.
        exact (sectionEquiv T).right_inv a
  refine ⟨A', forgetIso, liftedComparison, ?_⟩
  apply NatTrans.ext
  intro T
  funext a
  -- Both sides are literally the transported section map `comparison.hom.app T`.
  rfl

/-- Helper for Lemma 8.11.8: the underlying absolute-glueing comparisons already produce, for
every localized site `C / U` and every fixed object `x` of the fiber over `U`, a slicewise
`AddCommGrpCat`-valued lift whose underlying sheaf is `F.obj U`. This isolates the first half of
the additive endgame before the genuinely global packaging step. -/
theorem slice_addcomm_lifts_of_absolute_glueing_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) :
    ∃ lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v},
      ∃ forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
          ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1,
        ∃ liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
            lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} (x : 𝒮.p.Fiber U),
            Functor.whiskerRight (liftedComparison x).hom.1
                (forget AddCommGrpCat.{max u v}) =
              (forgetIso x).hom ≫ (comparison x).hom.1 := by
  let liftData :
      ∀ {U : C} (x : 𝒮.p.Fiber U),
        ∃ A' : Sheaf (J.over U) AddCommGrpCat.{max u v},
          ∃ forgetIso : (A'.1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1,
            ∃ liftedComparison : A' ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
              Functor.whiskerRight liftedComparison.hom.1
                  (forget AddCommGrpCat.{max u v}) =
                forgetIso.hom ≫ (comparison x).hom.1 :=
    fun {U} x ↦
      -- Apply the previously isolated slice transport once for the fixed comparison to `x`.
      slice_addcomm_sheaf_of_underlying_comparison
        (𝒮 := 𝒮) hAbelian (F.obj U) x (comparison x)
  refine ⟨fun {U} x ↦ Classical.choose (liftData x), ?_⟩
  refine ⟨fun {U} x ↦ ?_, ?_⟩
  · -- Read the underlying-forgetful comparison from the chosen slicewise additive lift.
    exact Classical.choose (Classical.choose_spec (liftData x))
  · refine ⟨fun {U} x ↦ ?_, fun {U} x ↦ ?_⟩
    · -- Read the lifted comparison to the canonical abelian automorphism sheaf from the same
      -- chosen slicewise additive lift.
      exact Classical.choose (Classical.choose_spec (Classical.choose_spec (liftData x)))
    · -- The forgetful compatibility comes from the strengthened slice-level transport theorem.
      exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (liftData x)))

/-- Helper for Lemma 8.11.8: once the slicewise additive lifts are fixed, forgetting the
composite comparison to `y` along a fiber morphism `φ : x ⟶ y` gives exactly the underlying
comparison induced from `F.obj U`. This isolates the additive-side conjugation compatibility that
the remaining global reconstruction must preserve. -/
theorem slice_addcomm_lifted_comparison_forget_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v}) =
      (forgetIso x).hom ≫ (comparison y).hom.1 := by
  have hcomparison_hom :
      (comparison x).hom.1 ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 =
        (comparison y).hom.1 := by
    -- Extract the underlying natural-transformation equality from the slice comparison law.
    exact congrArg (fun i ↦ i.hom.1) (hcomparison (U := U) (x := x) (y := y) φ)
  -- Forget the additive composite once, then replace the underlying conjugation by the prescribed
  -- underlying comparison compatibility.
  calc
    Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v}) =
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) ≫
        Functor.whiskerRight
          (automorphismAddCommSheafConj hAbelian φ).hom.1
          (forget AddCommGrpCat.{max u v}) := by
            rfl
    _ =
      (forgetIso x).hom ≫ (comparison x).hom.1 ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 := by
          simp [liftedCompatibility, automorphismUnderlyingSheafConj_hom, Category.assoc]
    _ = (forgetIso x).hom ≫ (comparison y).hom.1 := by
          simpa [Category.assoc] using
            congrArg (fun η ↦ (forgetIso x).hom ≫ η) hcomparison_hom

/-- Helper for Lemma 8.11.8: evaluating the forgetful compatibility of one slicewise additive
lift at the terminal object of `C / U` produces the exact composite
`forgetIso ≫ comparison` used by the final reconstructed restriction map. -/
private theorem lifted_comparison_terminal_app_eq_forget_then_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} (x : 𝒮.p.Fiber U) :
    (Functor.whiskerRight (liftedComparison x).hom.1
        (forget AddCommGrpCat.{max u v})).app
        (Opposite.op (Over.mk (𝟙 U))) =
      (forgetIso x).hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
        (comparison x).hom.1.app (Opposite.op (Over.mk (𝟙 U))) := by
  -- Evaluate the stored forgetful compatibility at the terminal object of `C / U`.
  simpa [NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun η ↦ η.app (Opposite.op (Over.mk (𝟙 U))))
      (liftedCompatibility x)

/-- Helper for Lemma 8.11.8: evaluating the additive-side conjugation compatibility at the
terminal object of `C / U` exposes the exact common-owner comparison consumed by the final global
additivity check. -/
private theorem slice_addcomm_lifted_comparison_terminal_app_forget_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (hcomparison : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIso : ∀ {U : C} (x : 𝒮.p.Fiber U),
      ((lifted x).1 ⋙ forget AddCommGrpCat.{max u v}) ≅ (F.obj U).1)
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedCompatibility : ∀ {U : C} (x : 𝒮.p.Fiber U),
      Functor.whiskerRight (liftedComparison x).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (forgetIso x).hom ≫ (comparison x).hom.1)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    (Functor.whiskerRight
        ((liftedComparison x ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
        (forget AddCommGrpCat.{max u v})).app
        (Opposite.op (Over.mk (𝟙 U))) =
      (forgetIso x).hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
        (comparison y).hom.1.app (Opposite.op (Over.mk (𝟙 U))) := by
  -- Evaluate the additive conjugation compatibility at the terminal object of `C / U`.
  simpa [NatTrans.comp_app, Category.assoc] using
    congrArg
      (fun η ↦ η.app (Opposite.op (Over.mk (𝟙 U))))
      (slice_addcomm_lifted_comparison_forget_conj
        (𝒮 := 𝒮) hAbelian F comparison hcomparison
        lifted forgetIso liftedComparison liftedCompatibility φ)

/-- Helper for Lemma 8.11.8: two slicewise additive lifts over the same absolute-glueing owner
are canonically identified by transporting along the additive conjugation on automorphism sheaves.
This is the fixed-owner comparison that the final reconstruction must descend from the family
`lifted x`. -/
private noncomputable def slice_addcomm_common_owner_iso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U}
    (Ax Ay : Sheaf (J.over U) AddCommGrpCat.{max u v})
    (liftedComparisonx : Ax ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedComparisony : Ay ≅ 𝒮.automorphismAddCommSheaf hAbelian y)
    (φ : x ⟶ y) :
    Ax ≅ Ay :=
  -- Route correction: isolate the fixed-owner uniqueness step from the absolute-glueing family,
  -- so later source-faithful descent can compare one descended owner against arbitrary slices
  -- without reintroducing the `∀ x, lifted x` packaging.
  liftedComparisonx ≪≫ automorphismAddCommSheafConj hAbelian φ ≪≫ liftedComparisony.symm

/-- Helper for Lemma 8.11.8: if two slicewise additive lifts share the same fixed underlying
owner, then the common-owner comparison above forgets to the identity on that owner once the two
underlying owner comparisons are compatible with conjugation. This is the fixed-owner uniqueness
adapter needed for the slicewise additive owner produced by descent. -/
theorem slice_addcomm_common_owner_iso_forget_hom
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {A : Sheaf (J.over U) (Type (max u v))}
    {x y : 𝒮.p.Fiber U}
    (comparisonx : A ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (comparisony : A ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)
    (Ax Ay : Sheaf (J.over U) AddCommGrpCat.{max u v})
    (forgetIsox : (Ax.1 ⋙ forget AddCommGrpCat.{max u v}) ≅ A.1)
    (forgetIsoy : (Ay.1 ⋙ forget AddCommGrpCat.{max u v}) ≅ A.1)
    (liftedComparisonx : Ax ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (liftedComparisony : Ay ≅ 𝒮.automorphismAddCommSheaf hAbelian y)
    (liftedCompatibilityx :
      Functor.whiskerRight liftedComparisonx.hom.1
          (forget AddCommGrpCat.{max u v}) =
        forgetIsox.hom ≫ comparisonx.hom.1)
    (liftedCompatibilityy :
      Functor.whiskerRight liftedComparisony.hom.1
          (forget AddCommGrpCat.{max u v}) =
        forgetIsoy.hom ≫ comparisony.hom.1)
    (φ : x ⟶ y)
    (hcomparison :
      comparisonx ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ = comparisony)
    :
    Functor.whiskerRight
        ((slice_addcomm_common_owner_iso
          (𝒮 := 𝒮) hAbelian Ax Ay liftedComparisonx liftedComparisony φ).hom.1)
        (forget AddCommGrpCat.{max u v}) ≫
      forgetIsoy.hom =
        forgetIsox.hom := by
  have hforgetConj :
      Functor.whiskerRight
          ((liftedComparisonx ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
          (forget AddCommGrpCat.{max u v}) =
        forgetIsox.hom ≫ comparisony.hom.1 := by
    -- First forget the additive conjugation comparison back to the common underlying owner.
    calc
      Functor.whiskerRight
          ((liftedComparisonx ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
          (forget AddCommGrpCat.{max u v}) =
        Functor.whiskerRight liftedComparisonx.hom.1
            (forget AddCommGrpCat.{max u v}) ≫
          Functor.whiskerRight
            (automorphismAddCommSheafConj hAbelian φ).hom.1
            (forget AddCommGrpCat.{max u v}) := by
              rfl
      _ =
        forgetIsox.hom ≫ comparisonx.hom.1 ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 := by
            simp [liftedCompatibilityx, automorphismUnderlyingSheafConj_hom, Category.assoc]
      _ = forgetIsox.hom ≫ comparisony.hom.1 := by
            have hcomparison_hom :
                comparisonx.hom.1 ≫
                    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 =
                  comparisony.hom.1 := by
              -- Extract the underlying natural-transformation equality from the owner comparison.
              exact congrArg (fun i ↦ i.hom.1) hcomparison
            simpa [Category.assoc] using
              congrArg (fun η ↦ forgetIsox.hom ≫ η) hcomparison_hom
  have hy :
      Functor.whiskerRight liftedComparisony.inv.1
          (forget AddCommGrpCat.{max u v}) ≫
        forgetIsoy.hom ≫ comparisony.hom.1 = 𝟙 _ := by
    -- Compose the underlying comparison for `y` on the left by the inverse lifted comparison.
    calc
      Functor.whiskerRight liftedComparisony.inv.1
          (forget AddCommGrpCat.{max u v}) ≫
        forgetIsoy.hom ≫ comparisony.hom.1 =
          Functor.whiskerRight liftedComparisony.inv.1
              (forget AddCommGrpCat.{max u v}) ≫
            Functor.whiskerRight liftedComparisony.hom.1
              (forget AddCommGrpCat.{max u v}) := by
                rw [liftedCompatibilityy]
                simp [Category.assoc]
      _ = 𝟙 _ := by
            simp
  have hy' :
      Functor.whiskerRight liftedComparisony.inv.1
          (forget AddCommGrpCat.{max u v}) ≫
        forgetIsoy.hom =
          comparisony.inv.1 := by
    -- Remove the final `comparisony` by postcomposing with its inverse.
    calc
      Functor.whiskerRight liftedComparisony.inv.1
          (forget AddCommGrpCat.{max u v}) ≫
        forgetIsoy.hom =
          (Functor.whiskerRight liftedComparisony.inv.1
              (forget AddCommGrpCat.{max u v}) ≫
            forgetIsoy.hom ≫ comparisony.hom.1) ≫
              comparisony.inv.1 := by
                simp [Category.assoc]
      _ = comparisony.inv.1 := by
            simpa [hy, Category.assoc]
  -- Package the fixed-owner comparison on the additive side and collapse the common owner.
  calc
    Functor.whiskerRight
        ((slice_addcomm_common_owner_iso
          (𝒮 := 𝒮) hAbelian Ax Ay liftedComparisonx liftedComparisony φ).hom.1)
        (forget AddCommGrpCat.{max u v}) ≫
      forgetIsoy.hom =
        Functor.whiskerRight
            ((liftedComparisonx ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) ≫
          (Functor.whiskerRight liftedComparisony.inv.1
            (forget AddCommGrpCat.{max u v}) ≫
            forgetIsoy.hom) := by
              rfl
    _ =
        Functor.whiskerRight
            ((liftedComparisonx ≪≫ automorphismAddCommSheafConj hAbelian φ).hom.1)
            (forget AddCommGrpCat.{max u v}) ≫
          comparisony.inv.1 := by
            rw [hy']
    _ = forgetIsox.hom ≫ comparisony.hom.1 ≫ comparisony.inv.1 := by
          rw [hforgetConj]
          simp [Category.assoc]
    _ = forgetIsox.hom := by
          simp [Category.assoc]

/-- Helper for Lemma 8.11.8: two slicewise additive lifts over the same absolute-glueing owner
are canonically identified by transporting along the additive conjugation on automorphism sheaves.
This is the fixed-owner comparison that the final reconstruction must descend from the family
`lifted x`. -/
private noncomputable def slice_addcomm_lifted_common_owner_iso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (lifted : ∀ {U : C} (x : 𝒮.p.Fiber U), Sheaf (J.over U) AddCommGrpCat.{max u v})
    (liftedComparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      lifted x ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    lifted x ≅ lifted y :=
  -- Follow the source route through the fixed-owner uniqueness lemma, specialized to `F.obj U`.
  slice_addcomm_common_owner_iso
    (𝒮 := 𝒮) hAbelian
    (lifted x) (lifted y) (liftedComparison x) (liftedComparison y) φ

end CategoryTheory
