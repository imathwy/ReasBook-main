import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
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

/-- Helper for Lemma 8.11.8: on each arrow of the identity pullback cover, the chosen-cover
pullback comparison to the pulled local object is compatible with conjugation in the fiber.  This
is the per-component input feeding the sheaf-level conjugation law below; it is exactly the Part14
`chosen_local_automorphism_iso_pulled_conj` after collapsing the `I.f ≫ 𝟙 U` identity shell. -/
private theorem chosen_cover_pullback_to_local_object_component_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y)
    (I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U)).Arrow) :
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
        (I.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f x).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) =
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I.base)
          (I.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f y).inv := by
  have h := chosen_local_automorphism_iso_pulled_conj
    (𝒮 := 𝒮) hGerbe hAbelian φ I.base
  -- The identity pullback collapses `I.base.f = I.f ≫ 𝟙 U` to `I.f`; both are arrows `I.Y ⟶ U`,
  -- so this is a type-preserving rewrite (no `eqToHom`).
  rw [show I.base.f = I.f from by
    simp only [GrothendieckTopology.Cover.Arrow.base_f, Category.comp_id]] at h
  refine (Iso.eq_comp_inv _).mpr ?_
  erw [Category.assoc, Category.assoc]
  exact h

/-- Helper for Lemma 8.11.8: the sheaf-level chosen-cover pullback comparison to the pulled local
object (specialised to `q = 𝟙 U`) is compatible with conjugation in the fiber over `U`.  This is
the source-faithful conjugation law underlying every slice comparison; it is checked on the
identity pullback cover by full faithfulness of the chosen cover descent equivalence and the
per-arrow conjugation law above. -/
private theorem chosen_cover_pullback_to_local_object_iso_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    chosen_cover_pullback_to_local_object_iso (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
      chosen_cover_pullback_to_local_object_iso (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) y := by
  haveI : (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U))).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U))).faithful
  apply Iso.ext
  simp only [Iso.trans_hom, chosen_cover_pullback_to_local_object_iso]
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J)
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U))).functor
  rw [Functor.map_comp, localizedSheafTransportIsoOfCoverDescentIso_functor_map,
    localizedSheafTransportIsoOfCoverDescentIso_functor_map]
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  rw [Pseudofunctor.DescentData.comp_hom]
  simp only [pullback_cover_local_object_comparison_descent_iso,
    Pseudofunctor.DescentData.isoMk_hom_hom,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    pullback_cover_local_object_component_iso, Iso.trans_hom, Iso.symm_hom]
  erw [Category.assoc, Category.assoc,
    chosen_cover_pullback_to_local_object_component_conj (𝒮 := 𝒮) hGerbe hAbelian φ I]
  rfl

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
  -- Both descent-iso ends are the chosen-cover descent functor applied to the sheaf-level pullback
  -- comparison, so the statement is the functor image of the sheaf-level conjugation law.
  simp only [chosen_cover_pullback_to_local_object_descent_iso, ← Functor.mapIso_trans]
  exact congrArg ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso)
    (chosen_cover_pullback_to_local_object_iso_conj (𝒮 := 𝒮) hGerbe hAbelian φ)

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
    -- The shell `overMapPullbackId` is `x`-independent, so the compatibility reduces to the
    -- shell-free adapter `chosen_cover_identity_pullback_comparison_conj`.
    simp only [chosen_cover_identity_pullback_comparison_descent_iso, Iso.trans_assoc]
    rw [chosen_cover_identity_pullback_comparison_conj (𝒮 := 𝒮) hGerbe hAbelian φ]

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
    -- Transport the datum-level compatibility `hcomparison` through the faithful chosen-cover
    -- descent equivalence: the equivalence functor sends each transported slice comparison back to
    -- the datum-level comparison.
    haveI : (localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).functor.Faithful :=
      (localizedSheafToCoverDescentFullyFaithful (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).faithful
    apply Iso.ext
    apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).functor
    rw [Iso.trans_hom, Functor.map_comp,
      chosenCoverSliceComparisonOfDescentIso_functor_map,
      chosenCoverSliceComparisonOfDescentIso_functor_map]
    have h := congrArg Iso.hom (hcomparison (x := x) (y := y) φ)
    simp only [Iso.trans_hom, Functor.mapIso_hom] at h
    exact h

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
  refine ⟨?_, ?_⟩
  · exact
      { obj := fun U ↦ chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U
        transition := fun {U V} f ↦ transition f
        transition_id := transition_id
        transition_comp := fun f g ↦ transition_comp f g }
  · exact ⟨comparison, hcomparison⟩

/-- Helper for Lemma 8.11.8: an isomorphism of absolute glueing data induces an isomorphism on
each localized sheaf. -/
private noncomputable def absolute_glueing_iso_app
    {F G : GrothendieckTopology.AbsoluteGlueing J} (η : F ≅ G) (U : C) :
    F.obj U ≅ G.obj U where
  hom := η.hom.app U
  inv := η.inv.app U
  hom_inv_id := by
    -- The inverse law for the absolute-glueing isomorphism is checked componentwise.
    exact congrArg (fun α : F ⟶ F ↦ α.app U) η.hom_inv_id
  inv_hom_id := by
    -- The same componentwise argument gives the reverse inverse law.
    exact congrArg (fun α : G ⟶ G ↦ α.app U) η.inv_hom_id

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
    {D : Type*} [Category D] {P Q : D ⥤ Type w} (α : P ⟶ Q)
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
          (fun τ ↦ τ.hom.app (Opposite.op (Over.mk (𝟙 V))))
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

/-- Helper for Lemma 8.11.8: source-level terminal transport compatibility before passing through
the Chapter 7 reconstruction counit.  This is the public source-facing form of
`γ^V_{V,f^*x} ∘ ρ_f = γ^U_{U,x}`: the terminal transition map, after the two local comparisons,
is the underlying map of an additive homomorphism between the canonical automorphism groups. -/
abbrev sourceAbsoluteGlueingTerminalRestrictionTransportCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U),
    ∃ g : (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) ⟶
        (𝒮.automorphismAddCommSheaf hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
            (op (Over.mk (𝟙 V))),
      ∀ b : (F.obj U).1.obj (op (Over.mk (𝟙 U))),
        ((comparisonF (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.1.app
            (op (Over.mk (𝟙 V))))
          (GrothendieckTopology.absoluteGlueingToPresheafMap J F f b) =
        g.hom
          ((comparisonF x).hom.1.app (op (Over.mk (𝟙 U))) b)

/-- Helper for Lemma 8.11.8: source-level sheafwise transport compatibility before passing
through the Chapter 7 reconstruction counit.  This is the non-terminal form of the Stacks
Tag `0CJY` omitted compatibility: for every slice object `T : (C / V)ᵒᵖ`, the source transition
`ρ_f` followed by `γ^V_{T,f^*x}` agrees with `γ^U_{fT,x}` followed by the canonical additive
base-change homomorphism. -/
abbrev sourceAbsoluteGlueingSheafwiseRestrictionTransportCompatible
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (F : GrothendieckTopology.AbsoluteGlueing J)
    (comparisonF : ∀ {U : C} (x : 𝒮.p.Fiber U),
      F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) (T : (Over V)ᵒᵖ),
    ∃ g : (𝒮.automorphismAddCommSheaf hAbelian x).1.obj
          (op ((Over.map f).obj T.unop)) ⟶
        (𝒮.automorphismAddCommSheaf hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj T,
      ∀ b : (F.obj U).1.obj (op ((Over.map f).obj T.unop)),
        ((comparisonF (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.1.app T)
          ((F.transition f).hom.1.app T b) =
        g.hom
          ((comparisonF x).hom.1.app (op ((Over.map f).obj T.unop)) b)

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

/-- Helper for Lemma 8.11.8: the canonical chosen-cover transition family used in the source
absolute glueing.  This fixes the `ρ` maps rather than quantifying over an arbitrary compatible
absolute-glueing transition. -/
noncomputable abbrev fixed_cover_absolute_glueing_transition_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :
    (J.overMapPullback (Type (max u v)) f).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U) ≅
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V :=
  chosen_cover_transport_transition
    (𝒮 := 𝒮) hGerbe hAbelian f
    (chosen_cover_descent_transition_iso
      (𝒮 := 𝒮) hGerbe hAbelian f)

/-- Helper for Lemma 8.11.8: the canonical chosen-cover transition is the identity transition over
identity maps. -/
theorem fixed_cover_absolute_glueing_transition_map_id
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ U : C,
      fixed_cover_absolute_glueing_transition_map (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) =
        (J.overMapPullbackId (Type (max u v)) U).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) :=
  by
    intro U
    simpa [fixed_cover_absolute_glueing_transition_map] using
      chosen_cover_transport_transition_id_of_descent_identity
        (𝒮 := 𝒮) hGerbe hAbelian U
        (chosen_cover_descent_transition_iso_id_hom
          (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Helper for Lemma 8.11.8: the canonical chosen-cover transitions satisfy the absolute-glueing
cocycle law. -/
theorem fixed_cover_absolute_glueing_transition_map_comp
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ {U V W : C} (f : V ⟶ U) (g : W ⟶ V),
      (J.overMapPullbackComp (Type (max u v)) g f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U) ≪≫
        fixed_cover_absolute_glueing_transition_map (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) =
          (J.overMapPullback (Type (max u v)) g).mapIso
              (fixed_cover_absolute_glueing_transition_map (𝒮 := 𝒮) hGerbe hAbelian f) ≪≫
            fixed_cover_absolute_glueing_transition_map (𝒮 := 𝒮) hGerbe hAbelian g :=
  by
    intro U V W f g
    rw [fixed_cover_absolute_glueing_transition_map]
    rw [fixed_cover_absolute_glueing_transition_map]
    rw [fixed_cover_absolute_glueing_transition_map]
    rw [chosen_cover_transport_transition_comp_reduction]
    let D := chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe W
    let efg :=
      chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f)
    let eg :=
      chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian g
    let ef :=
      chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f
    let a :=
      (((J.overMapPullbackComp (Type (max u v)) g f).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).hom)
    let b :=
      (chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := g ≫ f) efg).hom
    let c :=
      (((J.overMapPullback (Type (max u v)) g).mapIso
        (chosen_cover_transport_transition
          (𝒮 := 𝒮) hGerbe hAbelian (f := f) ef)).hom)
    let d :=
      (chosen_cover_transport_transition
        (𝒮 := 𝒮) hGerbe hAbelian (f := g) eg).hom
    change D.map (a ≫ b) = D.map (c ≫ d)
    have hb : D.map b = efg.hom := by
      simpa [D, b, efg] using
        chosen_cover_transport_transition_functor_map
          (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) efg
    have hd : D.map d = eg.hom := by
      simpa [D, d, eg] using
        chosen_cover_transport_transition_functor_map
          (𝒮 := 𝒮) hGerbe hAbelian g eg
    calc
      D.map (a ≫ b) = D.map a ≫ D.map b := by
        simpa using (D.map_comp a b)
      _ = D.map a ≫ efg.hom := by
        rw [hb]
      _ = D.map c ≫ eg.hom := by
        simpa [D, a, c, efg, eg, ef] using
          chosen_cover_transport_transition_comp_after_functor_map
            (𝒮 := 𝒮) hGerbe hAbelian f g
      _ = D.map c ≫ D.map d := by
        rw [hd]
      _ = D.map (c ≫ d) := by
        simpa using (D.map_comp c d).symm

/-- Helper for Lemma 8.11.8: the canonical local comparison family `γ` for the fixed chosen-cover
absolute glueing. -/
noncomputable abbrev fixed_cover_absolute_glueing_comparison_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U ≅
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x :=
  chosenCoverSliceComparisonOfDescentIso
    (𝒮 := 𝒮) hGerbe hAbelian x
    (chosen_cover_identity_pullback_comparison_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian x)

/-- Helper for Lemma 8.11.8: the canonical chosen-cover comparisons are compatible with
conjugation in each fiber. -/
theorem fixed_cover_absolute_glueing_comparison_map_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian x ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
        fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian y :=
  by
    intro U x y φ
    have hdescent :
        chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian x ≪≫
          ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).mapIso
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ)) =
        chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian y := by
      simp only [chosen_cover_identity_pullback_comparison_descent_iso, Iso.trans_assoc]
      rw [chosen_cover_identity_pullback_comparison_conj
        (𝒮 := 𝒮) hGerbe hAbelian φ]
    haveI : (localizedSheafToCoverDescentEquivalence (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).functor.Faithful :=
      (localizedSheafToCoverDescentFullyFaithful (J := J)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).faithful
    apply Iso.ext
    apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)).functor
    rw [Iso.trans_hom, Functor.map_comp,
      chosenCoverSliceComparisonOfDescentIso_functor_map,
      chosenCoverSliceComparisonOfDescentIso_functor_map]
    have h := congrArg Iso.hom hdescent
    simp only [Iso.trans_hom, Functor.mapIso_hom] at h
    exact h

/-- Helper for Lemma 8.11.8: the fixed chosen-cover absolute glueing whose local objects are the
descended automorphism sheaves. -/
noncomputable abbrev fixed_cover_underlying_automorphism_absolute_glueing
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    GrothendieckTopology.AbsoluteGlueing J where
  obj := fun U ↦ chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U
  transition := fun {U V} f ↦
    fixed_cover_absolute_glueing_transition_map (𝒮 := 𝒮) hGerbe hAbelian f
  transition_id := fixed_cover_absolute_glueing_transition_map_id (𝒮 := 𝒮) hGerbe hAbelian
  transition_comp := fun f g ↦
    fixed_cover_absolute_glueing_transition_map_comp (𝒮 := 𝒮) hGerbe hAbelian f g

/-- Helper for Lemma 8.11.8: the fixed transition wrapper is pinned to the datum-side
`chosen_cover_descent_transition_iso` after applying the chosen-cover descent functor. -/
private theorem fixed_cover_absolute_glueing_transition_map_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :
    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
      (fixed_cover_absolute_glueing_transition_map
        (𝒮 := 𝒮) hGerbe hAbelian f).hom) =
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f).hom := by
  simpa [fixed_cover_absolute_glueing_transition_map] using
    chosen_cover_transport_transition_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian f
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)

/-- Helper for Lemma 8.11.8: the fixed comparison wrapper is pinned to the identity-pullback
comparison after applying the chosen-cover descent functor. -/
private theorem fixed_cover_absolute_glueing_comparison_map_functor_map
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).map
      (fixed_cover_absolute_glueing_comparison_map
        (𝒮 := 𝒮) hGerbe hAbelian x).hom) =
      (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x).hom := by
  simpa [fixed_cover_absolute_glueing_comparison_map] using
    chosenCoverSliceComparisonOfDescentIso_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian x
      (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x)

private noncomputable abbrev fixed_cover_absolute_glueing_sheafwise_transport_base_change
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :=
  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom

/-- Helper for Lemma 8.11.8: the descended identity-pullback comparison has no residual
`overMapPullbackId` shell on a chosen-cover component. -/
private theorem chosen_cover_identity_pullback_comparison_component_normalized_part15
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x).hom.hom L =
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv := by
  simp only [chosen_cover_identity_pullback_comparison_descent_iso,
    chosen_cover_pullback_to_local_object_descent_iso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Pseudofunctor.DescentData.comp_hom,
    chosen_cover_descent_functor, Pseudofunctor.toDescentData_map_hom]
  rw [chosen_cover_identity_pullback_component_normalized (𝒮 := 𝒮) hGerbe hAbelian x L]
  have hId :
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).inv) ≫
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          (((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).hom) =
      𝟙 _ := by
    let F := ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor
    let e :=
      (J.overMapPullbackId (Type (max u v)) U).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)
    calc
      F.map e.inv ≫ F.map e.hom = F.map (e.inv ≫ e.hom) := by
        exact (F.map_comp e.inv e.hom).symm
      _ = F.map (𝟙 _) := by
        exact congrArg F.map e.inv_hom_id
      _ = 𝟙 _ := by
        simp
  simpa only [Category.assoc, Category.id_comp] using
    congrArg
      (fun m =>
        m ≫
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv)
      hId

/-- Helper for Lemma 8.11.8: naturality of the composite-pullback shell after one further
pullback.  It moves a morphism on `C / U` through the `overMapPullbackComp` component and the
outer `mapComp'` inverse. -/
private theorem overMapPullbackComp_mapComp'_inv_naturality_part15
    {U V Y Z : C} (f : V ⟶ U) (g : Y ⟶ V) (h : Z ⟶ Y)
    (F G : Sheaf (J.over U) (Type (max u v))) (a : F ⟶ G) :
    ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (g ≫ f).op.toLoc h.op.toLoc (h ≫ (g ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app F) ≫
      ((J.pseudofunctorOver (Type (max u v))).map (h ≫ (g ≫ f)).op.toLoc).toFunctor.map a =
    ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          ((J.overMapPullback (Type (max u v)) f).map a)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) g f).app G).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (g ≫ f).op.toLoc h.op.toLoc (h ≫ (g ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app G) := by
  let P := J.pseudofunctorOver (Type (max u v))
  let Fh := (P.map h.op.toLoc).toFunctor
  let M :=
    P.mapComp' (g ≫ f).op.toLoc h.op.toLoc (h ≫ (g ≫ f)).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
  have hM :
      Fh.map
          (((J.overMapPullback (Type (max u v)) (g ≫ f)).map a)) ≫
        M.inv.toNatTrans.app G =
      M.inv.toNatTrans.app F ≫
        ((P.map (h ≫ (g ≫ f)).op.toLoc).toFunctor.map a) := by
    simpa [P, Fh, M] using
      (P.mapComp'_inv_naturality (g ≫ f).op.toLoc h.op.toLoc
        (h ≫ (g ≫ f)).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) a)
  have hComp :
      ((J.overMapPullbackComp (Type (max u v)) g f).hom.app F) ≫
        ((J.overMapPullback (Type (max u v)) (g ≫ f)).map a) =
      (((J.overMapPullback (Type (max u v)) g).map
          ((J.overMapPullback (Type (max u v)) f).map a)) ≫
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app G)) := by
    simpa using
      (((J.overMapPullbackComp (Type (max u v)) g f).hom.naturality a).symm)
  calc
    Fh.map (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom) ≫
          M.inv.toNatTrans.app F ≫
        ((P.map (h ≫ (g ≫ f)).op.toLoc).toFunctor.map a) =
      Fh.map (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom) ≫
        Fh.map (((J.overMapPullback (Type (max u v)) (g ≫ f)).map a)) ≫
        M.inv.toNatTrans.app G := by
        simpa only [Category.assoc] using
          congrArg
            (fun m =>
              Fh.map (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom) ≫ m)
            hM.symm
    _ =
      Fh.map
          (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom ≫
            ((J.overMapPullback (Type (max u v)) (g ≫ f)).map a)) ≫
        M.inv.toNatTrans.app G := by
        simpa only [Category.assoc] using
          congrArg (fun m => m ≫ M.inv.toNatTrans.app G)
            (Fh.map_comp
              (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom)
              (((J.overMapPullback (Type (max u v)) (g ≫ f)).map a))).symm
    _ =
      Fh.map
          (((J.overMapPullback (Type (max u v)) g).map
              ((J.overMapPullback (Type (max u v)) f).map a)) ≫
            ((J.overMapPullbackComp (Type (max u v)) g f).app G).hom) ≫
        M.inv.toNatTrans.app G := by
        simpa only [Category.assoc] using
          congrArg (fun m => Fh.map m ≫ M.inv.toNatTrans.app G) hComp
    _ =
      (Fh.map
          (((J.overMapPullback (Type (max u v)) g).map
            ((J.overMapPullback (Type (max u v)) f).map a)))) ≫
        Fh.map (((J.overMapPullbackComp (Type (max u v)) g f).app G).hom) ≫
        M.inv.toNatTrans.app G := by
        simpa only [Category.assoc] using
          congrArg (fun m => m ≫ M.inv.toNatTrans.app G)
            (Fh.map_comp
              (((J.overMapPullback (Type (max u v)) g).map
                ((J.overMapPullback (Type (max u v)) f).map a)))
                (((J.overMapPullbackComp (Type (max u v)) g f).app G).hom))

/-- Helper for Lemma 8.11.8: the strict object-level form of the over-pullback functor after
composing two maps in `pseudofunctorOver`.  This keeps later base-change bridge proofs from
unfolding the whole pseudofunctor just to recognize the owner object. -/
private theorem pseudofunctorOver_comp_obj_overMapPullback_obj_part15
    {U V Y : C} (f : V ⟶ U) (g : Y ⟶ V)
    (F : Sheaf (J.over U) (Type (max u v))) :
    (((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc ≫
        (J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj F) =
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
        ((J.overMapPullback (Type (max u v)) f).obj F) := by
  rfl

/-- Helper for Lemma 8.11.8: the same object-recognition adapter in the form needed when an
`eqToHom` has been inserted before a morphism from the explicitly pulled owner object. -/
private theorem pseudofunctorOver_comp_obj_overMapPullback_eqToHom_comp_part15
    {U V Y : C} (f : V ⟶ U) (g : Y ⟶ V)
    (F : Sheaf (J.over U) (Type (max u v)))
    {G : Sheaf (J.over Y) (Type (max u v))}
    (m :
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
        ((J.overMapPullback (Type (max u v)) f).obj F) ⟶ G) :
    eqToHom
        (pseudofunctorOver_comp_obj_overMapPullback_obj_part15
          (J := J) f g F) ≫ m = m := by
  change eqToHom rfl ≫ m = m
  exact Category.id_comp m

/-- Helper for Lemma 8.11.8: changing the target of a chosen-local automorphism comparison by a
global fiber isomorphism conjugates the transported sheaf comparison.  The key point is that the
chosen local-isomorphism covers for the two globally isomorphic targets have the same underlying
maximal sieve, so the comparison can be checked on that common cover. -/
private theorem chosen_local_automorphism_iso_conj_of_iso_part15
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (A x y : 𝒮.p.Fiber U) (e : x ≅ y) :
    chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian A x ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom =
      chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian A y := by
  let Sx := chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A x
  let Sy := chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe A y
  let S := Sx ⊓ Sy
  apply Iso.ext
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  let Kx : Sx.Arrow := ⟨K.Y, K.f, K.hf.1⟩
  let Ky : Sy.Arrow := ⟨K.Y, K.f, K.hf.2⟩
  have hx :
      ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian A x).hom).hom K =
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A x Kx).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x).inv := by
    rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
    simpa [Kx] using
      chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
        (𝒮 := 𝒮) hGerbe hAbelian A x Kx
  have hy :
      ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian A y).hom).hom K =
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A y Ky).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f y).inv := by
    rw [localizedSheafToCoverDescentEquivalence_functor_map_component]
    simpa [Ky] using
      chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
        (𝒮 := 𝒮) hGerbe hAbelian A y Ky
  simp only [Iso.trans_hom, Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  rw [hx, hy,
    localizedSheafToCoverDescentEquivalence_functor_map_component,
    automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian K.f e.hom]
  let BA := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f A
  let Bx := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x
  let By := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f y
  let Cx := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A x Kx).hom
  let Ce := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).mapIso
      (asIso e.hom)).hom
  let Cy := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A y Ky).hom
  have hconj :
      Cx.hom ≫ Ce.hom = Cy.hom := by
    have hconjIso : Cx ≪≫ Ce = Cy := by
      dsimp [Cx, Ce, Cy]
      exact
        (automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A x Kx).hom
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).map e.hom)).symm.trans
          (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
            ((chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A x Kx).hom ≫
              ((canonicalPullbackChoice 𝒮.p).pullbackFunctor K.f).map e.hom)
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe A y Ky).hom)
    simpa only [Iso.trans_hom] using congrArg Iso.hom hconjIso
  change ((BA.hom ≫ Cx.hom ≫ Bx.inv) ≫ Bx.hom ≫ Ce.hom ≫ By.inv) =
    BA.hom ≫ Cy.hom ≫ By.inv
  calc
    ((BA.hom ≫ Cx.hom ≫ Bx.inv) ≫ Bx.hom ≫ Ce.hom ≫ By.inv) =
        BA.hom ≫ Cx.hom ≫ Bx.inv ≫ Bx.hom ≫ Ce.hom ≫ By.inv := by
      simp only [Category.assoc]
    _ = BA.hom ≫ Cx.hom ≫ Ce.hom ≫ By.inv := by
      have hcancelTail : Bx.inv ≫ Bx.hom ≫ Ce.hom ≫ By.inv = Ce.hom ≫ By.inv := by
        simpa only [Category.assoc] using (Iso.inv_hom_id_assoc Bx (Ce.hom ≫ By.inv))
      simpa only [Category.assoc] using
        congrArg (fun m => BA.hom ≫ Cx.hom ≫ m) hcancelTail
    _ = BA.hom ≫ Cy.hom ≫ By.inv := by
      have htail : Cx.hom ≫ Ce.hom ≫ By.inv = Cy.hom ≫ By.inv := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ By.inv) hconj
      simpa only [Category.assoc] using congrArg (fun m => BA.hom ≫ m) htail

/-- Helper for Lemma 8.11.8: the inverse of conjugation by the inverse of a fiber isomorphism is
the conjugation morphism induced by the original isomorphism.  Part02 has the same fact privately;
the base-change tail proof below needs this local copy. -/
private theorem automorphismUnderlyingSheafConj_inv_symm_hom_part15
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (e : x ≅ y) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.inv).inv =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom).hom := by
  exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _

/-- Helper for Lemma 8.11.8: the local/local/base-change segment in the pullback-cover
component has been normalized using the Part12 chosen-local composition theorem.  This isolates
the remaining core-component work to the surrounding `overMapPullbackComp`/`mapComp'` shell and
the final two-step base-change inverse tail. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          (L.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).inv) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom =
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv := by
  have hlocal :=
    chosen_local_automorphism_iso_pullback_comp_part12
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  simpa only [Category.assoc] using
    congrArg
      (fun m =>
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫ m)
      hlocal

/-- Helper for Lemma 8.11.8: the same local/base-change tail normalization, but with the
outer pullback-cover source component left in Lean's grouped form.  The source component unfolds
as `mapComp'.inv ≫ cover_iso.hom`; this adapter keeps that leading comparison attached while
normalizing only the local tail. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_grouped
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U) ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom) ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom =
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv := by
  let M :=
    ((J.pseudofunctorOver (Type (max u v))).mapComp'
      (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)
  have htail :=
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_normalized
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  simpa only [M, Category.assoc] using
    congrArg (fun m => M ≫ m) htail

/-- Helper for Lemma 8.11.8: the grouped local tail normalization in the exact projection form
produced by `pullback_cover_source_component_iso`, whose leading comparison is written through
`Cat.Hom.toNatIso`. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_grouped_source
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).inv ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom) ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom =
    ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).inv ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv := by
  simpa only [Category.assoc] using
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_grouped
      (𝒮 := 𝒮) hGerbe hAbelian f x I L

/-- Helper for Lemma 8.11.8: specialized component-level form of the `overMapPullbackComp`
shell naturality needed before the local/base-change tail normalization.  This moves the pulled
fixed comparison for `x` past the composite-pullback shell and its intervening `mapComp'`
inverse. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_shell_moved
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) I.f f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map (L.f ≫ (I.f ≫ f)).op.toLoc).toFunctor.map
        (chosenCoverSliceComparisonOfDescentIso
          (𝒮 := 𝒮) hGerbe hAbelian x
          (chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian x)).hom =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((J.overMapPullback (Type (max u v)) f).map
            (chosenCoverSliceComparisonOfDescentIso
              (𝒮 := 𝒮) hGerbe hAbelian x
              (chosen_cover_identity_pullback_comparison_descent_iso
                (𝒮 := 𝒮) hGerbe hAbelian x)).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) I.f f).app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) := by
  simpa only [Category.assoc] using
    overMapPullbackComp_mapComp'_inv_naturality_part15
      (J := J) f I.f L.f
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)
    (chosenCoverSliceComparisonOfDescentIso
        (𝒮 := 𝒮) hGerbe hAbelian x
      (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x)).hom

/-- Helper for Lemma 8.11.8: after the local/local component has been normalized, the remaining
chosen-local target owner and the three inverse base-change maps are the direct composite owner
tail followed by the two `mapComp'` hom components. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_owner_tail
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv) =
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian
        (L.f ≫ I.f ≫ f) x).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) := by
  let P := J.pseudofunctorOver (Type (max u v))
  let eOuter :=
    (canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso (I.f ≫ f) L.f x
  let eInner :=
    ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).mapIso
      ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso f I.f x)
  have howner :
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom =
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          (L.f ^*[canonicalPullbackChoice 𝒮.p]
            (I.f ^*[canonicalPullbackChoice 𝒮.p]
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom := by
    have h :=
      congrArg Iso.hom
        (chosen_local_automorphism_iso_conj_of_iso_part15
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)
          (L.f ^*[canonicalPullbackChoice 𝒮.p]
            (I.f ^*[canonicalPullbackChoice 𝒮.p]
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))
          (eOuter ≪≫ eInner))
    have hcomp :
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (eOuter.hom ≫ eInner.hom)).hom =
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom := by
      simpa only [Iso.trans_hom] using
        congrArg Iso.hom
          (automorphismUnderlyingSheafConj_comp (𝒮 := 𝒮) hAbelian eOuter.hom eInner.hom)
    calc
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom =
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
            ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (eOuter.hom ≫ eInner.hom)).hom := by
            rw [hcomp]
            rfl
      _ =
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
            (L.f ^*[canonicalPullbackChoice 𝒮.p]
              (I.f ^*[canonicalPullbackChoice 𝒮.p]
                (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom := by
            simpa [eOuter, eInner, Iso.trans_hom] using h
  have hinner :=
    tgtmerge (𝒮 := 𝒮) hAbelian (x := x)
      (cinv := 𝟙 (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))
      f I.f L.f (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
  have hinner' :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv) ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          ((P.map I.f.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv)) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          ((I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (I.f ≫ f) x).inv) ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          ((P.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) := by
    have hconjInner :
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map
            ((canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso f I.f x).inv)).inv =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom := by
      simpa [eInner] using
        automorphismUnderlyingSheafConj_inv_symm_hom_part15 (𝒮 := 𝒮) hAbelian eInner
    rw [hconjInner] at hinner
    simpa [P, eInner, Category.assoc, Functor.map_comp, Functor.map_id, Category.comp_id] using
      hinner.symm
  have houter :=
    automorphismUnderlyingSheafBaseChangeIso_comp_conj_inv
      (𝒮 := 𝒮) hAbelian (I.f ≫ f) L.f (L.f ≫ (I.f ≫ f)) x
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      eOuter
      (by
        simpa [eOuter] using
          fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
            (hc := canonicalPullbackChoice 𝒮.p) (I.f ≫ f) L.f x)
  have houter' :
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          ((I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (I.f ≫ f) x).inv) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian
          (L.f ≫ I.f ≫ f) x).inv ≫
        ((P.mapComp' (I.f ≫ f).op.toLoc L.f.op.toLoc
            (L.f ≫ (I.f ≫ f)).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) := by
    have hconjOuter :
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.symm.hom).inv =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom := by
      simpa [Iso.symm_hom] using
        automorphismUnderlyingSheafConj_inv_symm_hom_part15 (𝒮 := 𝒮) hAbelian eOuter
    rw [hconjOuter] at houter
    simpa [P, eOuter, Category.assoc] using houter
  calc
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv ≫
      ((P.map L.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv) ≫
      ((P.map L.f.op.toLoc).toFunctor.map
        ((P.map I.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv)) =
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eInner.hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv) ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          ((P.map I.f.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv)) := by
      simpa only [Category.assoc] using
        congrArg
          (fun m =>
            m ≫
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
                (I.f ^*[canonicalPullbackChoice 𝒮.p]
                  (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv ≫
              ((P.map L.f.op.toLoc).toFunctor.map
                (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
                  (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv) ≫
              ((P.map L.f.op.toLoc).toFunctor.map
                ((P.map I.f.op.toLoc).toFunctor.map
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv)))
          howner.symm
    _ =
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
          ((I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).inv ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (I.f ≫ f) x).inv) ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          ((P.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) := by
      simpa only [Category.assoc] using
        congrArg
          (fun m =>
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
              ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eOuter.hom).hom ≫ m)
          hinner'
    _ =
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian
          (L.f ≫ I.f ≫ f) x).inv ≫
        ((P.mapComp' (I.f ≫ f).op.toLoc L.f.op.toLoc
            (L.f ≫ (I.f ≫ f)).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)) ≫
        ((P.map L.f.op.toLoc).toFunctor.map
          ((P.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))) := by
      simpa only [Category.assoc] using
        congrArg
          (fun m =>
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
              ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
              m ≫
              ((P.map L.f.op.toLoc).toFunctor.map
                ((P.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
                    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x))))
          houter'

/-- Helper for Lemma 8.11.8: inverse/hom components of the same pseudofunctorial
`mapComp'` isomorphism cancel even when the equality witnesses were synthesized separately. -/
private theorem mapComp'_inv_hom_id_toNatTrans_app_of_witness_part15
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).inv.toNatTrans.app X ≫
      (F.mapComp' f g k w').hom.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Helper for Lemma 8.11.8: the concrete `overMapPullbackComp` component for sheaves over
`C / U` cancels the hom component of the matching `pseudofunctorOver.mapComp'`. -/
private theorem overMapPullbackComp_hom_mapComp'_hom_id_part15
    {U V Y : C} (f : V ⟶ U) (g : Y ⟶ V)
    (F : Sheaf (J.over U) (Type (max u v))) :
    ((J.overMapPullbackComp (Type (max u v)) g f).hom.app F) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app F) =
    𝟙 _ := by
  dsimp [GrothendieckTopology.pseudofunctorOver]
  exact
    congrArg (fun η => η.app F)
      (J.overMapPullbackComp (Type (max u v)) g f).hom_inv_id

/-- Helper for Lemma 8.11.8: on the base arrow of the pullback cover, the transported fixed
chosen-cover comparison is the normalized fixed-cover component. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_fixed_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map (L.f ≫ I.f ≫ f).op.toLoc).toFunctor.map
        (chosenCoverSliceComparisonOfDescentIso
          (𝒮 := 𝒮) hGerbe hAbelian x
          (chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian x)).hom =
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
          ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian
          (L.f ≫ I.f ≫ f) x).inv := by
  have hmap :=
    chosenCoverSliceComparisonOfDescentIso_functor_map
      (𝒮 := 𝒮) hGerbe hAbelian x
      (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x)
  have hcomp := congrArg (fun m => m.hom L.base) hmap
  have hfixed :=
    chosen_cover_identity_pullback_comparison_component_normalized_part15
      (𝒮 := 𝒮) hGerbe hAbelian x L.base
  simpa [chosen_cover_descent_functor, Pseudofunctor.toDescentData_map_hom,
    GrothendieckTopology.Cover.Arrow.base_f, Category.assoc] using hcomp.trans hfixed

/-- Helper for Lemma 8.11.8: the grouped source shell produced by the pullback-cover component
normalization can be moved through the fixed chosen-cover component.  Starting from the exact
`overMapPullbackComp`/`mapComp'` inverse shape left by
`pullback_cover_local_object_component_iso`, this rewrites the fixed component, applies the
local/base-change owner tail, and cancels the two pseudofunctorial shell pairs. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_grouped_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) I.f f).app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)).hom) ≫
      ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).inv ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((J.overMapPullback (Type (max u v)) f).map
            (chosenCoverSliceComparisonOfDescentIso
              (𝒮 := 𝒮) hGerbe hAbelian x
              (chosen_cover_identity_pullback_comparison_descent_iso
                (𝒮 := 𝒮) hGerbe hAbelian x)).hom)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom) := by
  let P := J.pseudofunctorOver (Type (max u v))
  let G :=
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
  let A := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x
  let s : G ⟶ A :=
    (chosenCoverSliceComparisonOfDescentIso
      (𝒮 := 𝒮) hGerbe hAbelian x
      (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian x)).hom
  let FL := (P.map L.f.op.toLoc).toFunctor
  let FI := (P.map I.f.op.toLoc).toFunctor
  let compG := ((J.overMapPullbackComp (Type (max u v)) I.f f).app G).hom
  let compA := ((J.overMapPullbackComp (Type (max u v)) I.f f).app A).hom
  let outerInvG :=
    (P.mapComp'
      (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app G
  let outerInvA :=
    (P.mapComp'
      (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A
  let outerHomA :=
    (P.mapComp'
      (I.f ≫ f).op.toLoc L.f.op.toLoc (L.f ≫ (I.f ≫ f)).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A
  let innerHomA :=
    (P.mapComp'
      f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A
  let cover :=
    (chosen_cover_underlying_automorphism_sheaf_cover_iso
      (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom
  let localSource :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
      (L.f ^*[canonicalPullbackChoice 𝒮.p]
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))).hom
  let bcSource :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).inv
  let localI :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
      (I.f ^*[canonicalPullbackChoice 𝒮.p]
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom
  let bcI :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv
  let localIterated :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
      (L.f ^*[canonicalPullbackChoice 𝒮.p]
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)))).hom
  let bcLIterated :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f
      (I.f ^*[canonicalPullbackChoice 𝒮.p]
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).inv
  let localTotal :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
      ((L.f ≫ I.f ≫ f) ^*[canonicalPullbackChoice 𝒮.p] x)).hom
  let bcTotal :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian
      (L.f ≫ I.f ≫ f) x).inv
  let bcF := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x
  have htail :=
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_tail_grouped_source
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  have howner :=
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_owner_tail
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  have hfixed :=
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_fixed_component
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  have hshell :=
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_shell_moved
      (𝒮 := 𝒮) hGerbe hAbelian f x I L
  have hshell' :
      FL.map compG ≫ outerInvG ≫
          ((P.map (L.f ≫ (I.f ≫ f)).op.toLoc).toFunctor.map s) =
        FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫
          FL.map compA ≫ outerInvA := by
    simpa [P, G, A, s, FL, FI, compG, compA, outerInvG, outerInvA] using hshell
  have hbcF :
      FL.map (FI.map bcF.inv) ≫ FL.map (FI.map bcF.hom) = 𝟙 _ := by
    calc
      FL.map (FI.map bcF.inv) ≫ FL.map (FI.map bcF.hom) =
          FL.map (FI.map bcF.inv ≫ FI.map bcF.hom) := by
            exact (FL.map_comp (FI.map bcF.inv) (FI.map bcF.hom)).symm
      _ = FL.map (FI.map (bcF.inv ≫ bcF.hom)) := by
            rw [← FI.map_comp]
      _ = 𝟙 _ := by
            simp
  have houterCancel :
      outerInvA ≫ outerHomA = 𝟙 _ := by
    simpa [P, A, outerInvA, outerHomA] using
      mapComp'_inv_hom_id_toNatTrans_app_of_witness_part15
        P (I.f ≫ f).op.toLoc L.f.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) A
  have hinnerCancel :
      FL.map compA ≫ FL.map innerHomA = 𝟙 _ := by
    have hcompA : compA ≫ innerHomA = 𝟙 _ := by
      simpa [P, A, compA, innerHomA] using
        overMapPullbackComp_hom_mapComp'_hom_id_part15
          (J := J) f I.f A
    calc
      FL.map compA ≫ FL.map innerHomA =
          FL.map (compA ≫ innerHomA) := by
            exact (FL.map_comp compA innerHomA).symm
      _ = FL.map (𝟙 _) := by
            exact congrArg FL.map hcompA
      _ = 𝟙 _ := by
            simp
  have hinnerTail :
      FL.map compA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom) =
        FL.map (FI.map bcF.hom) := by
    calc
      FL.map compA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom) =
          (FL.map compA ≫ FL.map innerHomA) ≫ FL.map (FI.map bcF.hom) := by
            rfl
      _ = 𝟙 _ ≫ FL.map (FI.map bcF.hom) := by
            exact congrArg (fun m => m ≫ FL.map (FI.map bcF.hom)) hinnerCancel
      _ = FL.map (FI.map bcF.hom) := by
            exact Category.id_comp (FL.map (FI.map bcF.hom))
  change
    FL.map compG ≫ outerInvG ≫ cover ≫ localSource ≫ bcSource ≫
        FL.map localI ≫ FL.map bcI =
      FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫
        FL.map (FI.map bcF.hom)
  calc
    FL.map compG ≫ outerInvG ≫ cover ≫ localSource ≫ bcSource ≫
        FL.map localI ≫ FL.map bcI =
      FL.map compG ≫ outerInvG ≫ cover ≫ localIterated ≫ bcLIterated ≫
        FL.map bcI := by
        simpa [P, G, FL, outerInvG, cover, localSource, bcSource, localI,
          localIterated, bcLIterated, Category.assoc] using
          congrArg (fun m => FL.map compG ≫ m ≫ FL.map bcI) htail
    _ =
      FL.map compG ≫ outerInvG ≫ cover ≫ localIterated ≫ bcLIterated ≫
        FL.map bcI ≫ FL.map (FI.map bcF.inv) ≫ FL.map (FI.map bcF.hom) := by
        simpa only [Category.assoc, Category.comp_id] using
          congrArg
            (fun m =>
              FL.map compG ≫ outerInvG ≫ cover ≫ localIterated ≫ bcLIterated ≫
                FL.map bcI ≫ m)
            hbcF.symm
    _ =
      FL.map compG ≫ outerInvG ≫ cover ≫ localTotal ≫ bcTotal ≫
        outerHomA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom) := by
        simpa [P, A, FL, outerHomA, innerHomA, localIterated, bcLIterated,
          bcI, bcF, localTotal, bcTotal, Category.assoc] using
          congrArg
            (fun m => FL.map compG ≫ outerInvG ≫ cover ≫ m ≫ FL.map (FI.map bcF.hom))
            howner
    _ =
      FL.map compG ≫ outerInvG ≫
        ((P.map (L.f ≫ (I.f ≫ f)).op.toLoc).toFunctor.map s) ≫
        outerHomA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom) := by
        simpa [P, G, A, s, cover, localTotal, bcTotal, Category.assoc] using
          congrArg
            (fun m =>
              FL.map compG ≫ outerInvG ≫ m ≫ outerHomA ≫
                FL.map innerHomA ≫ FL.map (FI.map bcF.hom))
            hfixed.symm
    _ =
      FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫
        FL.map compA ≫ outerInvA ≫ outerHomA ≫
        FL.map innerHomA ≫ FL.map (FI.map bcF.hom) := by
        simpa only [Category.assoc] using
          congrArg
            (fun m => m ≫ outerHomA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom))
            hshell'
    _ =
      FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫
        FL.map compA ≫ FL.map innerHomA ≫ FL.map (FI.map bcF.hom) := by
        erw [reassoc_of% houterCancel]
        rfl
    _ =
      FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫
        FL.map (FI.map bcF.hom) := by
        simpa only [Category.assoc] using
          congrArg
            (fun m =>
              FL.map (FI.map ((J.overMapPullback (Type (max u v)) f).map s)) ≫ m)
            hinnerTail

/-- Helper for Lemma 8.11.8: the component form of the remaining source-faithful
base-change bridge after applying the pullback cover of the chosen cover of `U` along
`I.f ≫ f`.  This is the narrowed frontier: the generic pullback-to-local-object comparison has
already been unfolded to its descent-data component, and the remaining tail is the canonical
two-step automorphism-sheaf base-change comparison. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_core_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
      (pullback_cover_local_object_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom.hom L ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
          (I.f ^*[canonicalPullbackChoice 𝒮.p]
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv =
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
      (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((J.overMapPullback (Type (max u v)) f).map
            (chosenCoverSliceComparisonOfDescentIso
              (𝒮 := 𝒮) hGerbe hAbelian x
            (chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian x)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom) := by
  simpa only [pullback_cover_local_object_comparison_descent_iso,
    Pseudofunctor.DescentData.isoMk_hom_hom,
    pullback_cover_local_object_component_iso, pullback_cover_source_component_iso,
    chosen_cover_pulled_component_composite_pullback_iso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc] using
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_grouped_shell
      (𝒮 := 𝒮) hGerbe hAbelian f x I L

/-- Helper for Lemma 8.11.8: the source-faithful sheaf-level base-change bridge left after the
identity-pullback comparison for `f^*x` and the fixed chosen-cover counit over `I` have both been
normalized and cancelled.  This is the remaining arbitrary-pullback-cover transport statement:
the composite-pullback comparison followed by the local comparison to the chosen object over `V`
agrees with the pullback of the fixed comparison for `x`, followed by the canonical
`automorphismUnderlyingSheafBaseChangeIso` component. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_base_change_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv =
    ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        ((J.overMapPullback (Type (max u v)) f).map
          (chosenCoverSliceComparisonOfDescentIso
            (𝒮 := 𝒮) hGerbe hAbelian x
            (chosen_cover_identity_pullback_comparison_descent_iso
              (𝒮 := 𝒮) hGerbe hAbelian x)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom := by
  -- Check the sheaf equality on the pullback of the chosen cover of `U` along `I.f ≫ f`; this
  -- is the cover on which `chosen_cover_pullback_to_local_object_iso` is defined.
  let S := chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)
  let D := (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  haveI : D.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      S).faithful
  apply Functor.map_injective D
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  have hpull :
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom) =
        (pullback_cover_local_object_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom.hom L := by
    have hmap :=
      localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
        S
        (pullback_cover_local_object_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I))
    have hcomp := congrArg (fun m ↦ m.hom L) hmap
    simpa [S, chosen_cover_pullback_to_local_object_iso,
      localizedSheafToCoverDescentEquivalence_functor_map_component] using hcomp
  simp only [D, S, Functor.map_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [hpull]
  exact
    fixed_cover_absolute_glueing_sheafwise_transport_base_change_core_component
      (𝒮 := 𝒮) hGerbe hAbelian f x I L

/-- Helper for Lemma 8.11.8: the secondary-cover component/counit normalization after the mixed
component has been unfolded to the generic chosen-cover pullback comparison.  This is the exact
remaining normalized component: the pulled composite-pullback shell, the pulled comparison to the
chosen local object over `V`, and the pulled chosen-cover counit must agree with the pulled
identity-pullback comparison for `x` followed by the canonical base-change component. -/
private theorem
    fixed_cover_absolute_glueing_sheafwise_transport_secondary_component_counit_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom) ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I).inv)) ≫
      ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          ((chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.hom I)).hom K =
    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
            ((J.overMapPullback (Type (max u v)) f).map
              (chosenCoverSliceComparisonOfDescentIso
                (𝒮 := 𝒮) hGerbe hAbelian x
                (chosen_cover_identity_pullback_comparison_descent_iso
                  (𝒮 := 𝒮) hGerbe hAbelian x)).hom)).hom I)).hom K ≫
      ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
            ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
              (fixed_cover_absolute_glueing_sheafwise_transport_base_change hAbelian f x)).hom)
                I)).hom) K)) := by
  let FK := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  let transitionComponent :=
    (chosen_cover_pulled_component_composite_pullback_iso
        (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
      (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian V I).inv
  let comparisonComponent :=
    (chosen_cover_identity_pullback_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.hom I
  let pulledComparisonComponent :=
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
      ((J.overMapPullback (Type (max u v)) f).map
        (chosenCoverSliceComparisonOfDescentIso
          (𝒮 := 𝒮) hGerbe hAbelian x
          (chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian x)).hom)).hom) I
  let baseChangeComponent :=
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
      (fixed_cover_absolute_glueing_sheafwise_transport_base_change hAbelian f x)).hom) I
  have hI :
      transitionComponent ≫ comparisonComponent =
        pulledComparisonComponent ≫ baseChangeComponent := by
    dsimp [transitionComponent, comparisonComponent, pulledComparisonComponent, baseChangeComponent]
    simp only [chosen_cover_identity_pullback_comparison_descent_iso,
      chosen_cover_pullback_to_local_object_descent_iso, Iso.trans_hom,
      Functor.map_comp, Functor.mapIso_hom, Pseudofunctor.DescentData.comp_hom]
    simp only [chosen_cover_descent_functor, Pseudofunctor.toDescentData_map_hom]
    rw [chosen_cover_identity_pullback_component_normalized
      (𝒮 := 𝒮) hGerbe hAbelian
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x) I]
    simp only [fixed_cover_absolute_glueing_sheafwise_transport_base_change,
      Iso.symm_hom, Category.assoc]
    let FI := ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor
    let idComparison :=
      (J.overMapPullbackId (Type (max u v)) V).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian V)
    have hIdComparison :
        ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
              (((J.overMapPullbackId (Type (max u v)) V).app
                (chosen_cover_underlying_automorphism_sheaf
                  (𝒮 := 𝒮) hGerbe hAbelian V)).inv) ≫
            ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
              (((J.overMapPullbackId (Type (max u v)) V).app
                (chosen_cover_underlying_automorphism_sheaf
                  (𝒮 := 𝒮) hGerbe hAbelian V)).hom) =
          𝟙 _ := by
      change FI.map idComparison.inv ≫ FI.map idComparison.hom = 𝟙 _
      calc
        FI.map idComparison.inv ≫ FI.map idComparison.hom =
            FI.map (idComparison.inv ≫ idComparison.hom) := by
          exact (FI.map_comp idComparison.inv idComparison.hom).symm
        _ = FI.map (𝟙 _) := by
          exact congrArg FI.map idComparison.inv_hom_id
        _ = 𝟙 _ := by
          simp
    let transitionTail :=
      (chosen_cover_pulled_component_composite_pullback_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I).hom ≫
        (chosen_cover_pullback_to_local_object_iso
            (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ f)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)).hom ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I).inv
    have hIdComparison_assoc :
        (transitionTail ≫
            ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
              (((J.overMapPullbackId (Type (max u v)) V).app
                (chosen_cover_underlying_automorphism_sheaf
                  (𝒮 := 𝒮) hGerbe hAbelian V)).inv)) ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
            (((J.overMapPullbackId (Type (max u v)) V).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian V)).hom) =
        transitionTail := by
      calc
        (transitionTail ≫
              ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
                (((J.overMapPullbackId (Type (max u v)) V).app
                  (chosen_cover_underlying_automorphism_sheaf
                    (𝒮 := 𝒮) hGerbe hAbelian V)).inv)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
              (((J.overMapPullbackId (Type (max u v)) V).app
                (chosen_cover_underlying_automorphism_sheaf
                  (𝒮 := 𝒮) hGerbe hAbelian V)).hom) =
          transitionTail ≫
            (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
                (((J.overMapPullbackId (Type (max u v)) V).app
                  (chosen_cover_underlying_automorphism_sheaf
                    (𝒮 := 𝒮) hGerbe hAbelian V)).inv) ≫
              ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
                (((J.overMapPullbackId (Type (max u v)) V).app
                  (chosen_cover_underlying_automorphism_sheaf
                    (𝒮 := 𝒮) hGerbe hAbelian V)).hom)) := by
            rw [Category.assoc]
        _ = transitionTail ≫ 𝟙 _ := by
            exact congrArg (fun m => transitionTail ≫ m) hIdComparison
        _ = transitionTail := by
            rw [Category.comp_id]
    let remainingTail :=
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian V I).hom ≫
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I)
        (I.f ^*[canonicalPullbackChoice 𝒮.p]
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x))).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.f
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).inv
    have hIdComparison_assoc_tail :
        transitionTail ≫
          ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
            (((J.overMapPullbackId (Type (max u v)) V).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian V)).inv) ≫
          ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
            (((J.overMapPullbackId (Type (max u v)) V).app
              (chosen_cover_underlying_automorphism_sheaf
                (𝒮 := 𝒮) hGerbe hAbelian V)).hom) ≫
          remainingTail =
        transitionTail ≫ remainingTail := by
      simpa only [Category.assoc] using
        congrArg (fun m => m ≫ remainingTail) hIdComparison_assoc
    change transitionTail ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (((J.overMapPullbackId (Type (max u v)) V).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian V)).inv) ≫
        ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (((J.overMapPullbackId (Type (max u v)) V).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian V)).hom) ≫
        remainingTail = _
    rw [hIdComparison_assoc_tail]
    simp only [Category.id_comp]
    dsimp [transitionTail, remainingTail]
    slice_lhs 1 2 =>
      erw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [chosen_cover_identity_pullback_comparison_descent_iso,
      chosen_cover_pulled_component_composite_pullback_iso, Category.assoc] using
      fixed_cover_absolute_glueing_sheafwise_transport_base_change_core
        (𝒮 := 𝒮) hGerbe hAbelian f x I
  have hK := congrArg FK.map hI
  simpa [FK, transitionComponent, comparisonComponent, pulledComparisonComponent,
    baseChangeComponent, Functor.map_comp, Pseudofunctor.toDescentData_map_hom, Category.assoc]
    using hK

/-- Helper for Lemma 8.11.8: after applying the chosen-cover descent functor once more on
`I.Y`, the raw `γ/ρ` component/counit square is reduced to a single secondary-cover component.
The left transition component is normalized through
`chosen_cover_descent_transition_component_mapped_normalized`; the remaining content is exactly
the secondary chosen-cover counit/base-change comparison. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_secondary_component_counit
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) :
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_pulled_component_composite_pullback_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
        (mixed_cover_secondary_cover_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian f I K).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian V I).inv)) ≫
      ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          ((chosen_cover_identity_pullback_comparison_descent_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.hom I)).hom K =
    ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
            ((J.overMapPullback (Type (max u v)) f).map
              (chosenCoverSliceComparisonOfDescentIso
                (𝒮 := 𝒮) hGerbe hAbelian x
                (chosen_cover_identity_pullback_comparison_descent_iso
                  (𝒮 := 𝒮) hGerbe hAbelian x)).hom)).hom I)).hom K ≫
      ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          ((((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
            (fixed_cover_absolute_glueing_sheafwise_transport_base_change hAbelian f x)).hom)
              I)).hom) K)) := by
  -- The remaining proof should normalize the two identity-pullback comparison components and
  -- paste them with the canonical base-change component for `automorphismUnderlyingSheaf`.
  rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian f I K,
    chosen_cover_pullback_to_local_object_component_iso_hom]
  simp only [fixed_cover_absolute_glueing_sheafwise_transport_base_change]
  exact
    fixed_cover_absolute_glueing_sheafwise_transport_secondary_component_counit_normalized
      (𝒮 := 𝒮) hGerbe hAbelian f x I K

/-- Helper for Lemma 8.11.8: the exact remaining non-terminal chosen-cover component/counit
normalization.  On the datum side, the transition component over `I` followed by the
identity-pullback comparison for `f^*x` must agree with pulling the transported identity-pullback
comparison for `x` along `f` and then applying the canonical base-change comparison. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_chosen_cover_component_counit
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f).hom.hom I ≫
      (chosen_cover_identity_pullback_comparison_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.hom I =
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        ((J.overMapPullback (Type (max u v)) f).map
          (chosenCoverSliceComparisonOfDescentIso
            (𝒮 := 𝒮) hGerbe hAbelian x
            (chosen_cover_identity_pullback_comparison_descent_iso
              (𝒮 := 𝒮) hGerbe hAbelian x)).hom)).hom I) ≫
      (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        (automorphismUnderlyingSheafBaseChangeIso
          (𝒮 := 𝒮) hAbelian f x).hom).hom I) := by
  -- This is the non-terminal source square left after the `γ/ρ` wrappers have been normalized:
  -- expand the component transition through `chosen_cover_descent_transition_component_iso`,
  -- normalize the identity-pullback counit on the chosen cover of `V`, and compare it with the
  -- pulled identity-pullback comparison for `x` followed by the canonical base-change iso.
  let D := chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y
  haveI : D.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y)).faithful
  apply Functor.map_injective D
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  simp only [D, Functor.map_comp, Pseudofunctor.DescentData.comp_hom,
    Pseudofunctor.DescentData.isoMk_hom_hom, chosen_cover_descent_transition_iso]
  have htransition :
      ((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe I.Y).map
          (chosen_cover_descent_transition_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I).hom).hom K =
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_pulled_component_composite_pullback_iso
              (𝒮 := 𝒮) hGerbe hAbelian f I).hom) ≫
          (mixed_cover_secondary_cover_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian f I K).hom ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian V I).inv) := by
    simpa [chosen_cover_descent_functor] using
      chosen_cover_descent_transition_component_mapped_normalized
        (𝒮 := 𝒮) hGerbe hAbelian f I K
  rw [htransition]
  exact
    fixed_cover_absolute_glueing_sheafwise_transport_secondary_component_counit
      (𝒮 := 𝒮) hGerbe hAbelian f x I K

/-- Helper for Lemma 8.11.8: after applying the faithful chosen-cover descent functor on
`C / V`, the non-terminal `γ/ρ` transport square is reduced to one component over a chosen-cover
arrow of `V`.  The remaining source calculation is exactly the component/counit normalization:
the fixed transition component `ρ_f`, followed by the descended comparison for `f^*x`, agrees
with the pulled descended comparison for `x` followed by the canonical
`automorphismUnderlyingSheafBaseChangeIso` component. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_descent_component_square_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow) :
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        (fixed_cover_absolute_glueing_transition_map
          (𝒮 := 𝒮) hGerbe hAbelian f).hom).hom I) ≫
      (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        (fixed_cover_absolute_glueing_comparison_map
          (𝒮 := 𝒮) hGerbe hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom).hom I) =
    (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        ((J.overMapPullback (Type (max u v)) f).map
          (fixed_cover_absolute_glueing_comparison_map
            (𝒮 := 𝒮) hGerbe hAbelian x).hom)).hom I) ≫
      (((chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).map
        (automorphismUnderlyingSheafBaseChangeIso
          (𝒮 := 𝒮) hAbelian f x).hom).hom I) := by
  -- The faithful descent reduction has removed the arbitrary section object `T`; what remains is
  -- the concrete chosen-cover component of the source proof's omitted varying-`U` compatibility.
  -- This should be proved by expanding the transported transition component against
  -- `chosen_cover_descent_transition_iso`, normalizing the two chosen-cover counit comparisons,
  -- and using the canonical base-change comparison
  -- `automorphismUnderlyingSheafBaseChangeIso` for the resulting automorphism sheaf.
  rw [fixed_cover_absolute_glueing_transition_map_functor_map,
    fixed_cover_absolute_glueing_comparison_map_functor_map]
  simp only [fixed_cover_absolute_glueing_comparison_map]
  exact
    fixed_cover_absolute_glueing_sheafwise_transport_chosen_cover_component_counit
      (𝒮 := 𝒮) hGerbe hAbelian f x I

/-- Helper for Lemma 8.11.8: the non-terminal sheafwise `γ/ρ` transport square as an equality of
sheaf morphisms on the slice `C / V`.  This is obtained by checking the square after the faithful
chosen-cover descent functor and then reducing to the component normalization above. -/
private theorem fixed_cover_absolute_glueing_sheafwise_transport_morphism_square_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :
    (fixed_cover_absolute_glueing_transition_map
        (𝒮 := 𝒮) hGerbe hAbelian f).hom ≫
      (fixed_cover_absolute_glueing_comparison_map
        (𝒮 := 𝒮) hGerbe hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom =
    ((J.overMapPullback (Type (max u v)) f).map
      (fixed_cover_absolute_glueing_comparison_map
        (𝒮 := 𝒮) hGerbe hAbelian x).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian f x).hom := by
  -- Faithfulness of the chosen-cover descent equivalence lets us check equality componentwise on
  -- the fixed chosen cover of `V`.
  haveI : (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)).faithful
  apply Functor.map_injective (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V)
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa only [Functor.map_comp, Pseudofunctor.DescentData.comp_hom] using
    fixed_cover_absolute_glueing_sheafwise_transport_descent_component_square_core
      (𝒮 := 𝒮) hGerbe hAbelian f x I

/-- Helper for Lemma 8.11.8: the sheafwise source `γ/ρ` square for the fixed chosen-cover
absolute glueing, pinned to the canonical base-change comparison on automorphism sheaves.  This is
the non-terminal statement needed for the forward additivity step in Part16: it holds at every
object `T : (C / V)ᵒᵖ`, not only at `V/V`. -/
theorem fixed_cover_absolute_glueing_sheafwise_transport_component_square_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) (T : (Over V)ᵒᵖ) :
    ∀ b : (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U).1.obj (op ((Over.map f).obj T.unop)),
      ((fixed_cover_absolute_glueing_comparison_map
            (𝒮 := 𝒮) hGerbe hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.1.app T)
        ((fixed_cover_absolute_glueing_transition_map
            (𝒮 := 𝒮) hGerbe hAbelian f).hom.1.app T b) =
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app T)
        ((fixed_cover_absolute_glueing_comparison_map
          (𝒮 := 𝒮) hGerbe hAbelian x).hom.1.app
            (op ((Over.map f).obj T.unop)) b) := by
  intro b
  -- Evaluate the morphism-level square at the requested non-terminal slice object.
  have hsquare :=
    fixed_cover_absolute_glueing_sheafwise_transport_morphism_square_core
      (𝒮 := 𝒮) hGerbe hAbelian f x
  simpa [FunctorToTypes.map_comp_apply] using
    congrFun (congrArg (fun η ↦ η.1.app T) hsquare) b

/-- Helper for Lemma 8.11.8: package the fixed chosen-cover sheafwise source `γ/ρ` square as an
additive-homomorphism-valued transport predicate.  The homomorphism is the canonical
`automorphismUnderlyingSheafBaseChangeIso` component at the slice object `T`. -/
theorem fixed_cover_absolute_glueing_sheafwise_transport_compatible
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    sourceAbsoluteGlueingSheafwiseRestrictionTransportCompatible
      (𝒮 := 𝒮) hAbelian
      (fixed_cover_underlying_automorphism_absolute_glueing (𝒮 := 𝒮) hGerbe hAbelian)
      (fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian) := by
  intro U V f x T
  let A : AddCommGrpCat.{max u v} :=
    (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op ((Over.map f).obj T.unop))
  let B : AddCommGrpCat.{max u v} :=
    (𝒮.automorphismAddCommSheaf hAbelian
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj T
  refine ⟨?_, ?_⟩
  · letI : AddCommGroup A := by
      change AddCommGroup
        ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op ((Over.map f).obj T.unop)))
      infer_instance
    letI : AddCommGroup B := by
      change AddCommGroup
        ((𝒮.automorphismAddCommSheaf hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj T)
      infer_instance
    letI : AddCommGroup (automorphismSection (𝒮 := 𝒮) x ((Over.map f).obj T.unop)) :=
      automorphismSectionAddCommGroup (𝒮 := 𝒮) hAbelian x ((Over.map f).obj T.unop)
    letI : AddCommGroup
        (automorphismSection (𝒮 := 𝒮)
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x) T.unop) :=
      automorphismSectionAddCommGroup (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x) T.unop
    exact
      AddCommGrpCat.ofHom <|
        AddMonoidHom.mk'
          (fun a : A ↦
            (show B from
              ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app T)
                a))
          (by
            intro a b
            exact
              automorphismUnderlyingSheafBaseChangeIso_hom_map_add
                (𝒮 := 𝒮) hAbelian f x T a b)
  · intro b
    exact
      fixed_cover_absolute_glueing_sheafwise_transport_component_square_core
        (𝒮 := 𝒮) hGerbe hAbelian f x T b

/-- Helper for Lemma 8.11.8: the canonical additive map on terminal automorphism groups induced
by first restricting a section from `U/U` to the slice object `V/U`, and then applying the
canonical base-change comparison from `Aut(x)` to `Aut(f^*x)`. -/
private noncomputable def automorphism_terminal_base_change_hom
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :
    (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) ⟶
      (𝒮.automorphismAddCommSheaf hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
          (op (Over.mk (𝟙 V))) :=
  let r :
      (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) ⟶
        (𝒮.automorphismAddCommSheaf hAbelian x).1.obj
          (op ((Over.map f).obj (Over.mk (𝟙 V)))) :=
    (𝒮.automorphismAddCommSheaf hAbelian x).1.map
      (show op (Over.mk (𝟙 U)) ⟶ op ((Over.map f).obj (Over.mk (𝟙 V))) from
        (show (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) from
          Over.homMk ((𝟙 V) ≫ f)).op)
  let θ :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
      (op (Over.mk (𝟙 V)))
  letI : AddCommGroup (automorphismSection x (Over.mk (𝟙 U))) :=
    automorphismSectionAddCommGroup (𝒮 := 𝒮) hAbelian x (Over.mk (𝟙 U))
  letI : AddCommGroup
      (automorphismSection (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
        (Over.mk (𝟙 V))) :=
    automorphismSectionAddCommGroup (𝒮 := 𝒮) hAbelian
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x) (Over.mk (𝟙 V))
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun a ↦ θ (r.hom a))
      (by
        intro a b
        -- The slice restriction is already an additive-group morphism, and the remaining
        -- base-change comparison preserves addition by the Part01 component calculation.
        letI : AddCommGroup
            ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj
                (op (Over.mk (𝟙 V)))) := by
          change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian x).1.obj
            (op ((Over.map f).obj (Over.mk (𝟙 V)))))
          infer_instance
        letI : AddCommGroup
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
                (op (Over.mk (𝟙 V)))) := by
          change AddCommGroup ((𝒮.automorphismAddCommSheaf hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
              (op (Over.mk (𝟙 V))))
          infer_instance
        change θ (r.hom (a + b)) = θ (r.hom a) + θ (r.hom b)
        rw [show r.hom (a + b) = r.hom a + r.hom b from map_add r.hom a b]
        exact
          automorphismUnderlyingSheafBaseChangeIso_hom_map_add
            (𝒮 := 𝒮) hAbelian f x (op (Over.mk (𝟙 V))) (r.hom a) (r.hom b))

/-- Helper for Lemma 8.11.8: the source component square needed from the chosen-cover
construction.  It is the terminal-object specialization of the varying-`U` compatibility omitted
in Stacks, Tag `0CJY`: after the fixed chosen-cover transition `ρ_f` and the two canonical
comparisons `γ`, the resulting map is the underlying function of the canonical additive
restriction/base-change homomorphism. -/
private theorem fixed_cover_absolute_glueing_terminal_transport_component_square_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :
    ∀ b : (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U).1.obj (op (Over.mk (𝟙 U))),
      ((fixed_cover_absolute_glueing_comparison_map
            (𝒮 := 𝒮) hGerbe hAbelian
            (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.1.app
          (op (Over.mk (𝟙 V))))
        (GrothendieckTopology.absoluteGlueingToPresheafMap J
          (fixed_cover_underlying_automorphism_absolute_glueing
            (𝒮 := 𝒮) hGerbe hAbelian) f b) =
      (automorphism_terminal_base_change_hom (𝒮 := 𝒮) hAbelian f x).hom
        ((fixed_cover_absolute_glueing_comparison_map
          (𝒮 := 𝒮) hGerbe hAbelian x).hom.1.app (op (Over.mk (𝟙 U))) b) := by
  intro b
  -- Route correction: the terminal statement is not an independent source calculation.  It is
  -- the `T = V/V` specialization of the sheafwise `γ/ρ` square, after unfolding the terminal
  -- restriction map and the pinned additive base-change hom.
  let G :=
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
  let A :=
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x
  let T : (Over V)ᵒᵖ := op (Over.mk (𝟙 V))
  let mOver : op (Over.mk (𝟙 U)) ⟶ op ((Over.map f).obj (Over.mk (𝟙 V))) :=
    (show (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) from
      Over.homMk ((𝟙 V) ≫ f)).op
  let mMk : op (Over.mk (𝟙 U)) ⟶ op (Over.mk f) :=
    (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f).op
  let hT : (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f :=
    absolute_glueing_reconstruction_over_map_obj_terminal_eq f
  let qT : op (Over.mk f) = op ((Over.map f).obj (Over.mk (𝟙 V))) :=
    (congrArg op hT).symm
  have hinput :
      G.1.map mOver b =
        eqToHom (congrArg G.1.obj qT) (G.1.map mMk b) := by
    -- The direct map to the literal pulled terminal object is the terminal-object cast of the
    -- usual restriction to `Over.mk f`.
    have hm : mOver = mMk ≫ eqToHom qT := by
      apply Quiver.Hom.unop_inj
      apply Over.OverMorphism.ext
      simp [mOver, mMk]
    have hcast :
        G.1.map (eqToHom qT) (G.1.map mMk b) =
          eqToHom (congrArg G.1.obj qT) (G.1.map mMk b) := by
      simpa using congrFun (eqToHom_map G.1 qT) (G.1.map mMk b)
    calc
      G.1.map mOver b = G.1.map (mMk ≫ eqToHom qT) b := by
        rw [hm]
      _ = G.1.map (eqToHom qT) (G.1.map mMk b) := by
        simp [FunctorToTypes.map_comp_apply]
      _ = eqToHom (congrArg G.1.obj qT) (G.1.map mMk b) := hcast
  have hcomparison :
      ((fixed_cover_absolute_glueing_comparison_map
            (𝒮 := 𝒮) hGerbe hAbelian x).hom.1.app
          (op ((Over.map f).obj (Over.mk (𝟙 V)))) (G.1.map mOver b)) =
        A.1.map mOver
          ((fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian x).hom.1.app
            (op (Over.mk (𝟙 U))) b) := by
    -- Naturality of the local comparison moves the terminal restriction through `γ^U_x`.
    simpa [G, A, T, mOver, FunctorToTypes.map_comp_apply] using
      congrFun
        (((fixed_cover_absolute_glueing_comparison_map
          (𝒮 := 𝒮) hGerbe hAbelian x).hom.1).naturality mOver)
        b
  have hsheafwise :=
    fixed_cover_absolute_glueing_sheafwise_transport_component_square_core
      (𝒮 := 𝒮) hGerbe hAbelian f x T (G.1.map mOver b)
  rw [hcomparison] at hsheafwise
  rw [hinput] at hsheafwise
  simpa [GrothendieckTopology.absoluteGlueingToPresheafMap,
    GrothendieckTopology.absoluteGlueing_transition_app_terminal,
    fixed_cover_underlying_automorphism_absolute_glueing,
    automorphism_terminal_base_change_hom, G, A, T, mOver, mMk, hT, qT, hinput,
    automorphismUnderlyingSheaf, FunctorToTypes.map_comp_apply] using hsheafwise

/-- Helper for Lemma 8.11.8: the remaining source calculation at one terminal slice square.
For the fixed chosen-cover transition `ρ_f` and comparison maps `γ`, the induced terminal map,
after applying the two local comparisons, is the underlying function of the canonical additive
restriction/base-change homomorphism on automorphism groups. This is the source formula
`γ^V_{V,f^*x} ∘ ρ_f = γ^U_{U,x}` in the concrete chosen-cover package. -/
theorem fixed_cover_absolute_glueing_terminal_transport_component_square
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U) :
    ∃ g : (𝒮.automorphismAddCommSheaf hAbelian x).1.obj (op (Over.mk (𝟙 U))) ⟶
        (𝒮.automorphismAddCommSheaf hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).1.obj
            (op (Over.mk (𝟙 V))),
      ∀ b : (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U).1.obj (op (Over.mk (𝟙 U))),
        ((fixed_cover_absolute_glueing_comparison_map
              (𝒮 := 𝒮) hGerbe hAbelian
              (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)).hom.1.app
            (op (Over.mk (𝟙 V))))
          (GrothendieckTopology.absoluteGlueingToPresheafMap J
            (fixed_cover_underlying_automorphism_absolute_glueing
              (𝒮 := 𝒮) hGerbe hAbelian) f b) =
        g.hom
          ((fixed_cover_absolute_glueing_comparison_map
            (𝒮 := 𝒮) hGerbe hAbelian x).hom.1.app (op (Over.mk (𝟙 U))) b) := by
  -- Package the pinned source component square as the public existential transport predicate.
  refine ⟨automorphism_terminal_base_change_hom (𝒮 := 𝒮) hAbelian f x, ?_⟩
  exact
    fixed_cover_absolute_glueing_terminal_transport_component_square_core
      (𝒮 := 𝒮) hGerbe hAbelian f x

/-- Helper for Lemma 8.11.8: package the terminal component square above as the public
source-facing `γ/ρ` transport compatibility predicate for the fixed chosen-cover absolute
glueing. -/
theorem fixed_cover_absolute_glueing_terminal_transport_compatible
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    sourceAbsoluteGlueingTerminalRestrictionTransportCompatible
      (𝒮 := 𝒮) hAbelian
      (fixed_cover_underlying_automorphism_absolute_glueing (𝒮 := 𝒮) hGerbe hAbelian)
      (fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian) := by
  intro U V f x
  exact
    fixed_cover_absolute_glueing_terminal_transport_component_square
      (𝒮 := 𝒮) hGerbe hAbelian f x

/-- Helper for Lemma 8.11.8: the chosen-cover source absolute-glueing datum together with the
public terminal `γ/ρ` transport law.  The remaining proof obligation is exactly the source
calculation that the transition constructed from `fixed_cover_absolute_glueing_transition` is
compatible with the comparisons from `fixed_cover_absolute_glueing_comparison` at terminal slice
objects. -/
theorem exists_underlying_automorphism_absolute_glueing_with_terminal_transport
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ F : GrothendieckTopology.AbsoluteGlueing J,
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          F.obj U ≅ automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x,
        ∃ compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y,
          sourceAbsoluteGlueingTerminalRestrictionTransportCompatible
            (𝒮 := 𝒮) hAbelian F comparison := by
  refine ⟨fixed_cover_underlying_automorphism_absolute_glueing (𝒮 := 𝒮) hGerbe hAbelian,
    fixed_cover_absolute_glueing_comparison_map (𝒮 := 𝒮) hGerbe hAbelian,
    fixed_cover_absolute_glueing_comparison_map_conj (𝒮 := 𝒮) hGerbe hAbelian, ?_⟩
  exact
    fixed_cover_absolute_glueing_terminal_transport_compatible
      (𝒮 := 𝒮) hGerbe hAbelian

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
  -- Take the additive lift to be the canonical abelian automorphism sheaf itself; the forgetful
  -- comparison back to `A` is then exactly the inverse underlying comparison, and the lifted
  -- comparison is the identity.
  refine
    ⟨𝒮.automorphismAddCommSheaf hAbelian x,
      (sheafToPresheaf (J.over U) (Type (max u v))).mapIso comparison.symm,
      Iso.refl _, ?_⟩
  -- The lifted comparison is the identity, so the whiskered forgetful map is the identity, which
  -- agrees with `forgetIso.hom ≫ comparison.hom.1 = comparison.inv.1 ≫ comparison.hom.1 = 𝟙`.
  simp only [Iso.refl_hom, Functor.mapIso_hom, ObjectProperty.ι_map, Iso.symm_hom]
  exact (ObjectProperty.isoInv_hom_id_hom comparison).symm

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
          rw [← Category.assoc]
          exact congrArg
            (fun η ↦ η ≫ Functor.whiskerRight
              (automorphismAddCommSheafConj hAbelian φ).hom.1
              (forget AddCommGrpCat.{max u v}))
            (liftedCompatibility x)
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
  -- Forgetting the additive conjugation produces the underlying conjugation; this is the only
  -- bridge between the `AddCommGrpCat`-level and `Type`-level conjugations.
  have hconjForget :
      Functor.whiskerRight (automorphismAddCommSheafConj hAbelian φ).hom.1
          (forget AddCommGrpCat.{max u v}) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 := rfl
  -- Underlying-comparison conjugation law, read on natural transformations.
  have hcmp :
      comparisonx.hom.1 ≫ (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1 =
        comparisony.hom.1 := by
    have := congrArg (fun i ↦ i.hom.1) hcomparison
    simpa [ObjectProperty.FullSubcategory.comp_hom] using this
  -- The forgetful image of `liftedComparisony.inv`, post-composed with `forgetIsoy.hom`, collapses
  -- to the underlying inverse comparison of `y`.
  have hyi :
      Functor.whiskerRight liftedComparisony.inv.1 (forget AddCommGrpCat.{max u v}) ≫
          forgetIsoy.hom =
        comparisony.inv.1 := by
    have hwy : Functor.whiskerRight liftedComparisony.inv.1
          (forget AddCommGrpCat.{max u v}) ≫
        Functor.whiskerRight liftedComparisony.hom.1
          (forget AddCommGrpCat.{max u v}) = 𝟙 _ := by
      rw [← Functor.whiskerRight_comp, ObjectProperty.isoInv_hom_id_hom liftedComparisony]
      simp
    have e : forgetIsoy.hom =
        Functor.whiskerRight liftedComparisony.hom.1 (forget AddCommGrpCat.{max u v}) ≫
          comparisony.inv.1 := by
      rw [liftedCompatibilityy]
      erw [Category.assoc, ObjectProperty.isoHom_inv_id_hom comparisony]
      rw [Category.comp_id]
    rw [e]
    erw [← Category.assoc, hwy]
    rw [Category.id_comp]
  -- Assemble: distribute the forgetful functor over the common-owner composite and substitute.
  simp only [slice_addcomm_common_owner_iso, Iso.trans_hom, Iso.symm_hom,
    ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_comp, Category.assoc]
  rw [liftedCompatibilityx, hconjForget]
  -- Fully right-associate, collapse the `y`-tail via `hyi`, then the `x`-conjugation via `hcmp`.
  erw [Category.assoc, hyi]
  erw [reassoc_of% hcmp]
  erw [ObjectProperty.isoHom_inv_id_hom comparisony, Category.comp_id]

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
