import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_4.Index
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

/-- Generic owner-object cast: a natural transformation of `Type`-valued presheaves transports its
component across an object equality `h : A = B` by the induced casts on input/output. -/
private theorem app_obj_cast {D : Type (max u v)} [Category.{v} D]
    {ℱ 𝒢 : Dᵒᵖ ⥤ Type (max u v)} (ψ : ℱ ⟶ 𝒢) {A B : Dᵒᵖ} (h : A = B)
    (s : ℱ.obj A) :
    ψ.app A s =
      (congrArg 𝒢.obj h).mpr (ψ.app B (Eq.mp (congrArg ℱ.obj h) s)) := by
  cases h
  rfl

/-- Generic owner-object cast when the input section has already been transported to the source
owner. -/
private theorem app_obj_cast_mpr {D : Type (max u v)} [Category.{v} D]
    {ℱ 𝒢 : Dᵒᵖ ⥤ Type (max u v)} (ψ : ℱ ⟶ 𝒢) {A B : Dᵒᵖ} (h : A = B)
    (s : ℱ.obj B) :
    ψ.app A ((congrArg ℱ.obj h).mpr s) =
      (congrArg 𝒢.obj h).mpr (ψ.app B s) := by
  cases h
  rfl

private theorem sheaf_iso_hom_inv_app {D : Type (max u v)} [Category.{v} D]
    {K : GrothendieckTopology D} {ℱ 𝒢 : Sheaf K (Type (max u v))}
    (e : ℱ ≅ 𝒢) (A : Dᵒᵖ) (s : ℱ.1.obj A) :
    e.inv.1.app A (e.hom.1.app A s) = s := by
  change ((e.hom ≫ e.inv : ℱ ⟶ ℱ).1.app A) s = ((𝟙 ℱ : ℱ ⟶ ℱ).1.app A) s
  rw [e.hom_inv_id]

private theorem sheaf_iso_inv_hom_app {D : Type (max u v)} [Category.{v} D]
    {K : GrothendieckTopology D} {ℱ 𝒢 : Sheaf K (Type (max u v))}
    (e : ℱ ≅ 𝒢) (A : Dᵒᵖ) (s : 𝒢.1.obj A) :
    e.hom.1.app A (e.inv.1.app A s) = s := by
  change ((e.inv ≫ e.hom : 𝒢 ⟶ 𝒢).1.app A) s = ((𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app A) s
  rw [e.inv_hom_id]

/-- Helper for Lemma 8.11.8: postcomposing a sheaf morphism with an `eqToIso`
hom is exactly the dependent cast on component sections. -/
private theorem sheaf_comp_eqToIso_hom_app_cast {D : Type (max u v)} [Category.{v} D]
    {τ : GrothendieckTopology D} {ℰ ℱ 𝒢 : Sheaf τ (Type (max u v))}
    (ψ : ℰ ⟶ ℱ) (h : ℱ = 𝒢) (A : Dᵒᵖ) (s : ℰ.1.obj A) :
    ((ψ ≫ (eqToIso h).hom).1.app A) s =
      Eq.mp (congrArg (fun ℋ : Sheaf τ (Type (max u v)) => ℋ.1.obj A) h)
        (ψ.1.app A s) := by
  cases h
  rfl

/-- Helper for Lemma 8.11.8: precomposing with an `eqToIso` inverse is exactly the
dependent cast on component sections. -/
private theorem sheaf_eqToIso_inv_comp_app_cast {D : Type (max u v)} [Category.{v} D]
    {τ : GrothendieckTopology D} {ℱ 𝒢 ℋ : Sheaf τ (Type (max u v))}
    (h : ℱ = 𝒢) (ψ : ℱ ⟶ ℋ) (A : Dᵒᵖ) (s : 𝒢.1.obj A) :
    (((eqToIso h).inv ≫ ψ).1.app A) s =
      ψ.1.app A
        (Eq.mp (congrArg (fun ℐ : Sheaf τ (Type (max u v)) => ℐ.1.obj A) h.symm) s) := by
  cases h
  rfl

/-- Helper for Lemma 8.11.8: a self-cast of sheaf component sections is the identity. -/
private theorem sheaf_obj_cast_self {D : Type (max u v)} [Category.{v} D]
    {τ : GrothendieckTopology D} {ℱ : Sheaf τ (Type (max u v))}
    (h : ℱ = ℱ) (A : Dᵒᵖ) (s : ℱ.1.obj A) :
    Eq.mp (congrArg (fun ℋ : Sheaf τ (Type (max u v)) => ℋ.1.obj A) h) s = s := by
  cases h
  rfl

/-- Helper for Lemma 8.11.8: postcomposing a sheaf morphism with an `eqToHom`
is the dependent cast on component sections. -/
private theorem sheaf_comp_eqToHom_app_cast {D : Type (max u v)} [Category.{v} D]
    {τ : GrothendieckTopology D} {ℰ ℱ 𝒢 : Sheaf τ (Type (max u v))}
    (ψ : ℰ ⟶ ℱ) (h : ℱ = 𝒢) (A : Dᵒᵖ) (s : ℰ.1.obj A) :
    ((ψ ≫ eqToHom h).1.app A) s =
      Eq.mp (congrArg (fun ℋ : Sheaf τ (Type (max u v)) => ℋ.1.obj A) h)
        (ψ.1.app A s) := by
  cases h
  rfl

/-- Helper for Lemma 8.11.8: precomposing a sheaf morphism with an `eqToHom`
is the dependent cast on component sections. -/
private theorem sheaf_eqToHom_comp_app_cast {D : Type (max u v)} [Category.{v} D]
    {τ : GrothendieckTopology D} {ℱ 𝒢 ℋ : Sheaf τ (Type (max u v))}
    (h : ℱ = 𝒢) (ψ : 𝒢 ⟶ ℋ) (A : Dᵒᵖ) (s : ℱ.1.obj A) :
    ((eqToHom h ≫ ψ).1.app A) s =
      ψ.1.app A
        (Eq.mp (congrArg (fun ℐ : Sheaf τ (Type (max u v)) => ℐ.1.obj A) h) s) := by
  cases h
  rfl

/-- Evaluating the `pf.map g`-pullback of a sheaf morphism at an arbitrary slice object `W`
is the original morphism evaluated at the `Over.map g`-image of `W`. -/
private theorem pf_map_app_eq_image_app_obj {X Y : C} (g : X ⟶ Y)
    {ℱ 𝒢 : Sheaf (J.over Y) (Type (max u v))} (φ : ℱ ⟶ 𝒢) (W : Over X) :
    (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map φ).1.app (op W) =
      φ.1.app (op ((Over.map g).obj W)) := rfl

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
    exact chosen_cover_transport_transition_id_of_descent_identity
      (𝒮 := 𝒮) hGerbe hAbelian U
      (chosen_cover_descent_transition_iso_id_hom
        (𝒮 := 𝒮) hGerbe hAbelian U)
  · intro U V W f g
    rw [chosen_cover_transport_transition_comp_reduction]
    -- Worker F exposes the descent-side cocycle after `map_comp`; normalize the
    -- reduction goal to that component form before consuming it.
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
noncomputable def chosenCoverSliceComparisonOfDescentIso
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
noncomputable def chosen_cover_identity_pullback_comparison_descent_iso
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

/-- Helper for Lemma 8.11.8: the hom side of the sheaf-over-site triangle for composing a
pullback with the identity pullback. This is the local `ρ_id` shell used before the chosen-cover
component is compared. -/
private theorem overMapPullbackComp_hom_congr_comp_id_part12
    {U V : C} (f : V ⟶ U)
    (F : Sheaf (J.over U) (Type (max u v))) :
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).hom ≫
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).app F).hom =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) := by
  have h := congrArg (fun η => η.app F)
    (J.overMapPullback_comp_id (Type (max u v)) f)
  have h' :
      (J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).inv.app F ≫
          ((J.overMapPullback (Type (max u v)) f).map
            (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) =
        (J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).hom.app F := by
    simpa only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Category.comp_id] using h
  change
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).hom.app F) ≫
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).hom.app F) =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom))
  rw [← h']
  change
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).hom ≫
        ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).inv ≫
          ((J.overMapPullback (Type (max u v)) f).map
            (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom))
  rw [Iso.hom_inv_id_assoc]

/-- Helper for Lemma 8.11.8: when two chosen-cover arrow records have the same source and
propositionally equal arrows, the cover counit component followed by the local comparison is
transported by the corresponding `overMapPullbackCongr` shell. Keeping both records explicit
avoids rewriting under `chosen_gerbe_cover_object`. -/
theorem chosen_cover_component_tail_congr_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (f₀ f₁ : Y ⟶ U) (h01 : f₀ = f₁)
    (h₀ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₀)
    (h₁ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₁)
    (x : 𝒮.p.Fiber U) :
    ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₀, h₀⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₀, h₀⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁ x).inv =
    ((J.overMapPullbackCongr (Type (max u v)) h01).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).hom ≫
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₁, h₁⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₁, h₁⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁ x).inv := by
  cases h01
  have hp : h₀ = h₁ := Subsingleton.elim _ _
  cases hp
  simp [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso]
  rfl

/-- Helper for Lemma 8.11.8: the common-owner comparison for `B` and `z`, pulled through an
outer owner leg `r`, as an isomorphism between the two iterated pullbacks over `q`. -/
private noncomputable abbrev chosen_local_common_owner_pullback_isomorphism_part12
    (hGerbe : IsGerbe J 𝒮.p) {U V Z : C}
    {B z : 𝒮.p.Fiber U} (r : V ⟶ U) (q : Z ⟶ V)
    {K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q ≫ r := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p] (r ^*[canonicalPullbackChoice 𝒮.p] B) ≅
      q ^*[canonicalPullbackChoice 𝒮.p] (r ^*[canonicalPullbackChoice 𝒮.p] z) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (hc.pullbackCompComponentIso r q B).symm ≪≫
    chosen_local_common_owner_isomorphism (𝒮 := 𝒮) hGerbe (q ≫ r) g hg ≪≫
    hc.pullbackCompComponentIso r q z

/-- Helper for Lemma 8.11.8: after all three local choices are rewritten to the same owner `q`,
the conjugation for `A ⟶ q^* r^*B` followed by the pulled conjugation for `B ⟶ z` is the direct
conjugation for `A ⟶ q^* r^*z`. -/
private theorem chosen_local_common_owner_pullback_conjugation_comp_eq_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V Z : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U) (q : Z ⟶ V)
    {KAB : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] B)).Arrow}
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    {KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow}
    (gAB : Z ⟶ KAB.Y) (gBz : Z ⟶ KBz.Y) (gAz : Z ⟶ KAz.Y)
    (hgAB : gAB ≫ KAB.f = q := by cat_disch)
    (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (hgAz : gAz ≫ KAz.f = q := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAB hgAB).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_pullback_isomorphism_part12
          (𝒮 := 𝒮) hGerbe r q gBz hgBz).hom).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAz hgAz).hom).hom := by
  rw [← Iso.trans_hom, ← automorphismUnderlyingSheafConj_comp]
  exact congrArg Iso.hom
    (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      ((chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAB hgAB).hom ≫
        (chosen_local_common_owner_pullback_isomorphism_part12
          (𝒮 := 𝒮) hGerbe r q gBz hgBz).hom)
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe q gAz hgAz).hom)

/-- Helper for Lemma 8.11.8: a final common-owner arrow for
`A ⟶ q^* r^* z`, together with a pulled common-owner arrow for `B ⟶ z`, canonically supplies
the missing member of the chosen local cover for `A ⟶ q^* r^* B`. This is the common-refinement
member used before rewriting the left branch into two owner-normalized conjugation shells. -/
private theorem chosen_local_pullback_comp_common_refinement_mem_part12
    (hGerbe : IsGerbe J 𝒮.p)
    {U V Z : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U) (q : Z ⟶ V)
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    {KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow}
    (gBz : Z ⟶ KBz.Y) (gAz : Z ⟶ KAz.Y)
    (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (hgAz : gAz ≫ KAz.f = q := by cat_disch) :
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] B)) q := by
  let eAz :=
    chosen_local_common_owner_isomorphism
      (𝒮 := 𝒮) hGerbe q gAz hgAz
  let eBz :=
    chosen_local_common_owner_pullback_isomorphism_part12
      (𝒮 := 𝒮) hGerbe r q gBz hgBz
  exact ⟨eAz ≪≫ eBz.symm⟩

/-- Helper for Lemma 8.11.8: package the common-refinement member above as an arrow of the
chosen local cover for the left branch `A ⟶ q^* r^* B`. -/
private noncomputable def chosen_local_pullback_comp_common_refinement_arrow_part12
    (hGerbe : IsGerbe J 𝒮.p)
    {U V Z : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U) (q : Z ⟶ V)
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    {KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow}
    (gBz : Z ⟶ KBz.Y) (gAz : Z ⟶ KAz.Y)
    (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (hgAz : gAz ≫ KAz.f = q := by cat_disch) :
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] B)).Arrow :=
  ⟨Z, q,
    chosen_local_pullback_comp_common_refinement_mem_part12
      (𝒮 := 𝒮) hGerbe r q gBz gAz hgBz hgAz⟩

/-- Helper for Lemma 8.11.8: app-level form of the Part06 telescope for the pulled
`B ⟶ z` source shell, with the outer owner leg already recorded as `q ≫ r`. -/
private theorem chosen_local_srcShell_outer_pulled_eq_common_owner_app_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V Z : C} {B z : 𝒮.p.Fiber U} (r : V ⟶ U) (q : Z ⟶ V)
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    (gBz : Z ⟶ KBz.Y) (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (s : ((((J.pseudofunctorOver (Type (max u v))).map gBz.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map KBz.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian B))).1.obj T)) :
    let lhs :=
      ((J.pseudofunctorOver (Type (max u v))).map gBz.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KBz.f B ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe B z KBz).hom ≪≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KBz.f z).symm).hom);
    let hw : KBz.f.op.toLoc ≫ gBz.op.toLoc = (q ≫ r).op.toLoc :=
      by
        simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hgBz;
    let mB :=
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        KBz.f.op.toLoc gBz.op.toLoc (q ≫ r).op.toLoc hw).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian B);
    let bB :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (q ≫ r) B).hom;
    let c :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe (q ≫ r) gBz hgBz).hom).hom;
    let bZ :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (q ≫ r) z).inv;
    let mZ :=
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        KBz.f.op.toLoc gBz.op.toLoc (q ≫ r).op.toLoc hw).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian z);
    let rhs :=
      (((mB ≫ bB) ≫ c) ≫ bZ) ≫ mZ;
    (lhs.1.app T) s = (rhs.1.app T) s := by
  dsimp only
  have h :=
    chosen_local_srcShell_pulled_eq_common_owner
      (𝒮 := 𝒮) hGerbe hAbelian (q ≫ r) gBz hgBz
  exact congrFun (congrArg (fun m => m.1.app T) h) s

/-- Helper for Lemma 8.11.8: member-level/app-level version of the final common-owner
composition collapse. After the two left-branch conjugation shells have been normalized to the
same owner `q`, their componentwise composite is the direct `A ⟶ q^* r^* z` conjugation shell. -/
private theorem chosen_local_common_owner_pullback_conjugation_comp_app_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V Z : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U) (q : Z ⟶ V)
    {KAB : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] B)).Arrow}
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    {KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow}
    (gAB : Z ⟶ KAB.Y) (gBz : Z ⟶ KBz.Y) (gAz : Z ⟶ KAz.Y)
    (hgAB : gAB ≫ KAB.f = q := by cat_disch)
    (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (hgAz : gAz ≫ KAz.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (s : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (q ^*[canonicalPullbackChoice 𝒮.p] A)).1.obj T) :
    let lhs :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAB hgAB).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_pullback_isomorphism_part12
          (𝒮 := 𝒮) hGerbe r q gBz hgBz).hom).hom;
    let rhs :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAz hgAz).hom).hom;
    (lhs.1.app T) s = (rhs.1.app T) s := by
  dsimp only
  have h :=
    chosen_local_common_owner_pullback_conjugation_comp_eq_part12
      (𝒮 := 𝒮) hGerbe hAbelian r q gAB gBz gAz hgAB hgBz hgAz
  exact congrFun (congrArg (fun m => m.1.app T) h) s

/-- Helper for Lemma 8.11.8: specialized component collapse for the simultaneous common
refinement supplied by `chosen_local_pullback_comp_common_refinement_arrow_part12`. This packages
the `A ⟶ q^* r^* B` refinement arrow with identity owner leg, so the final component proof can
focus on the source-shell and base-change transport bookkeeping. -/
private theorem chosen_local_pullback_comp_common_refinement_collapse_app_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V Z : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U) (q : Z ⟶ V)
    {KBz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).Arrow}
    {KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow}
    (gBz : Z ⟶ KBz.Y) (gAz : Z ⟶ KAz.Y)
    (hgBz : gBz ≫ KBz.f = q ≫ r := by cat_disch)
    (hgAz : gAz ≫ KAz.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (s : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (q ^*[canonicalPullbackChoice 𝒮.p] A)).1.obj T) :
    let KAB :=
      chosen_local_pullback_comp_common_refinement_arrow_part12
        (𝒮 := 𝒮) hGerbe r q gBz gAz hgBz hgAz;
    let lhs :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q (K := KAB) (g := 𝟙 Z)
          (by simp [KAB, chosen_local_pullback_comp_common_refinement_arrow_part12])).hom).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_pullback_isomorphism_part12
          (𝒮 := 𝒮) hGerbe r q gBz hgBz).hom).hom;
    let rhs :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe q gAz hgAz).hom).hom;
    (lhs.1.app T) s = (rhs.1.app T) s := by
  dsimp only
  exact
    chosen_local_common_owner_pullback_conjugation_comp_app_part12
      (𝒮 := 𝒮) hGerbe hAbelian r q
      (KAB :=
        chosen_local_pullback_comp_common_refinement_arrow_part12
          (𝒮 := 𝒮) hGerbe r q gBz gAz hgBz hgAz)
      (KBz := KBz) (KAz := KAz)
      (𝟙 Z) gBz gAz
      (by simp [chosen_local_pullback_comp_common_refinement_arrow_part12])
      hgBz hgAz T s

/-- Helper for Lemma 8.11.8: after taking the `KAz` component of the descent functor in the
final target branch and pulling it further along a chosen refinement of the `B ⟶ z` local cover,
the `D.map` component is the concrete chosen-local source shell for `A ⟶ r^* z`, followed by the
pulled target base-change morphism. This is the narrow component-level bridge from the public
theorem's `D.map` target component to the app-level common-owner helpers. -/
private theorem chosen_local_pullback_comp_target_D_map_component_source_shell_app_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} {A : 𝒮.p.Fiber V} {B z : 𝒮.p.Fiber U}
    (r : V ⟶ U)
    (KAz : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).Arrow)
    (M : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).pullback
      (KAz.f ≫ r)).Arrow)
    (T : (Over M.Y)ᵒᵖ)
    (s : ((((J.pseudofunctorOver (Type (max u v))).map M.f.op.toLoc).toFunctor.obj
        (((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian A))).1.obj T)) :
    let S :=
      chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        A (r ^*[canonicalPullbackChoice 𝒮.p] z);
    let D := (localizedSheafToCoverDescentEquivalence (J := J) S).functor;
    let target :=
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        A (r ^*[canonicalPullbackChoice 𝒮.p] z)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv;
    let shell :=
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KAz.f A).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism
            (𝒮 := 𝒮) hGerbe A (r ^*[canonicalPullbackChoice 𝒮.p] z) KAz).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KAz.f
          (r ^*[canonicalPullbackChoice 𝒮.p] z)).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv;
    ((((J.pseudofunctorOver (Type (max u v))).map M.f.op.toLoc).toFunctor.map
        ((D.map target).hom KAz)).1.app T) s =
      ((((J.pseudofunctorOver (Type (max u v))).map M.f.op.toLoc).toFunctor.map
        shell).1.app T) s := by
  dsimp only
  let S :=
    chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)
  let D := (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  let target :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv
  let localShell :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KAz.f A).hom ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (chosen_local_isomorphism
          (𝒮 := 𝒮) hGerbe A (r ^*[canonicalPullbackChoice 𝒮.p] z) KAz).hom).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian KAz.f
        (r ^*[canonicalPullbackChoice 𝒮.p] z)).inv
  have hD :
      (D.map target).hom KAz =
        ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.map
          target := by
    simpa [D, S, target] using
      localizedSheafToCoverDescentEquivalence_functor_map_component
        (J := J) S target KAz
  have hLocal :
      ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.map
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            A (r ^*[canonicalPullbackChoice 𝒮.p] z)).hom =
        localShell := by
    simpa [S, localShell, localizedSheafToCoverDescentEquivalence_functor_map_component] using
      chosen_local_automorphism_iso_functor_map_eq_chosen_local_conjugation_component
        (𝒮 := 𝒮) hGerbe hAbelian A (r ^*[canonicalPullbackChoice 𝒮.p] z) KAz
  let F := ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor
  let a :=
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      A (r ^*[canonicalPullbackChoice 𝒮.p] z)).hom
  let b := (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv
  have hTarget :
      (D.map target).hom KAz =
        localShell ≫
          ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv := by
    calc
      (D.map target).hom KAz = F.map target := by
        simpa [F] using hD
      _ = F.map (a ≫ b) := by
        rfl
      _ = F.map a ≫ F.map b := by
        exact F.map_comp a b
      _ = localShell ≫ F.map b := by
        rw [hLocal]
      _ =
          localShell ≫
            ((J.pseudofunctorOver (Type (max u v))).map KAz.f.op.toLoc).toFunctor.map
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian r z).inv := by
        rfl
  exact congrFun
    (congrArg (fun φ => φ.1.app T)
      (congrArg
        (((J.pseudofunctorOver (Type (max u v))).map M.f.op.toLoc).toFunctor.map)
        hTarget)) s

/-- Helper for Lemma 8.11.8: composing a chosen-local comparison with the pullback of another
chosen-local comparison is the chosen-local comparison to the twice-pulled object, up to the
canonical base-change comparison. -/
theorem chosen_local_automorphism_iso_pullback_comp_part12
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) (x : 𝒮.p.Fiber U)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V).Arrow)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ f)).Arrow) :
  let A := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base
  let B := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I
  let z := I.f ^*[canonicalPullbackChoice 𝒮.p]
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      A (L.f ^*[canonicalPullbackChoice 𝒮.p] B)).hom ≫
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f B).inv ≫
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian B z).hom =
  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
      A (L.f ^*[canonicalPullbackChoice 𝒮.p] z)).hom ≫
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f z).inv := by
  let A := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base
  let B := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe V I
  let z := I.f ^*[canonicalPullbackChoice 𝒮.p]
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).obj x)
  change
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        A (L.f ^*[canonicalPullbackChoice 𝒮.p] B)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f B).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian B z).hom =
    (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        A (L.f ^*[canonicalPullbackChoice 𝒮.p] z)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f z).inv
  let S :=
    chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      A (L.f ^*[canonicalPullbackChoice 𝒮.p] z)
  let D := (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  haveI : D.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective D
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- NARROW DEFERRED: at this single final-cover component `K`, refine simultaneously by the
  -- pulled `B ⟶ z` cover and by
  -- `chosen_local_pullback_comp_common_refinement_arrow_part12`; then rewrite the two source
  -- shells with `chosen_local_srcShell_pulled_eq_common_owner` and collapse them with
  -- `chosen_local_common_owner_pullback_conjugation_comp_app_part12`.
  let SBz :=
    (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe B z).pullback
      (K.f ≫ L.f)
  let E := (localizedSheafToCoverDescentEquivalence (J := J) SBz).functor
  haveI : E.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) SBz).faithful
  apply Functor.map_injective E
  apply Pseudofunctor.DescentData.hom_ext
  intro M
  simp only [D, E, SBz, localizedSheafToCoverDescentEquivalence_functor_map_component,
    Functor.map_comp, Pseudofunctor.DescentData.comp_hom]
  apply Sheaf.hom_ext
  ext T s
  have hTarget :=
    chosen_local_pullback_comp_target_D_map_component_source_shell_app_part12
      (𝒮 := 𝒮) hGerbe hAbelian L.f K M T s
  let q : M.Y ⟶ L.base.Y := M.f ≫ K.f
  let KAB :=
    chosen_local_pullback_comp_common_refinement_arrow_part12
      (𝒮 := 𝒮) hGerbe L.f q
      (KBz := M.base) (KAz := K)
      (𝟙 M.Y) M.f
      (by simp [q, GrothendieckTopology.Cover.Arrow.base])
      (by simp [q])
  have hAB :=
    chosen_local_srcShell_outer_pulled_eq_common_owner_app_part12
      (𝒮 := 𝒮) hGerbe hAbelian (𝟙 L.base.Y) q
      (KBz := KAB) (𝟙 M.Y)
      (by simp [q, KAB, chosen_local_pullback_comp_common_refinement_arrow_part12])
      T s
  simpa [D, S] using hTarget.symm

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
  have key := congrArg
    (fun m => m.hom (chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L))
    (localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (𝟙 U))
      (pullback_cover_local_object_comparison_descent_iso (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) x))
  dsimp only [] at key
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component] at key
  exact key

/-- Helper for Lemma 8.11.8: after moving to the identity-pullback-cover component indexed by
`L`, the source component is the canonical `overMapPullbackId` transport followed by the fixed
chosen-cover local comparison. This is the remaining identity-pullback normalization frontier. -/
private theorem chosen_cover_identity_pullback_local_object_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (pullback_cover_local_object_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (𝟙 U) x
        (chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L)).hom =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).hom ≫
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv := by
  dsimp [pullback_cover_local_object_component_iso, pullback_cover_source_component_iso,
    chosen_cover_identity_pullback_arrow]
  let G :=
    chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
  let h01 : L.f ≫ 𝟙 U = L.f := by simp
  let h₀ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (L.f ≫ 𝟙 U) := by
    simpa using
      (chosen_cover_identity_pullback_arrow (𝒮 := 𝒮) hGerbe L).base.hf
  let L₀ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow :=
    ⟨L.Y, L.f ≫ 𝟙 U, h₀⟩
  have htail :=
    chosen_cover_component_tail_congr_part12
      (𝒮 := 𝒮) hGerbe hAbelian
      (f₀ := L.f ≫ 𝟙 U) (f₁ := L.f) h01 h₀ L.hf x
  have hcomp0 :=
    overMapPullbackComp_hom_congr_comp_id_part12
      (J := J) (f := L.f) G
  have hcongr :
      ((J.overMapPullbackCongr (Type (max u v))
        (by simp : L.f ≫ 𝟙 U = L.f)).app G).hom =
      ((J.overMapPullbackCongr (Type (max u v)) h01).app G).hom := by
    congr 1
  have hcomp :
      ((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫
          ((J.overMapPullbackCongr (Type (max u v)) h01).app G).hom =
        ((J.overMapPullback (Type (max u v)) L.f).map
          (((J.overMapPullbackId (Type (max u v)) U).app G).hom)) := by
    simpa [hcongr] using hcomp0
  change
    (((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L₀).hom) ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L₀)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv =
    ((J.overMapPullback (Type (max u v)) L.f).map
        (((J.overMapPullbackId (Type (max u v)) U).app G).hom)) ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv
  calc
    (((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L₀).hom) ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L₀)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv =
        ((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫
          (((J.overMapPullbackCongr (Type (max u v)) h01).app G).hom ≫
            (chosen_cover_underlying_automorphism_sheaf_cover_iso
              (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
            (chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv) := by
      simpa only [L₀, Category.assoc] using
        congrArg
          (fun m =>
            ((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫ m)
          htail
    _ = (((J.overMapPullbackComp (Type (max u v)) L.f (𝟙 U)).app G).hom ≫
          ((J.overMapPullbackCongr (Type (max u v)) h01).app G).hom) ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
        (chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv := by
      simp only [Category.assoc]
    _ = ((J.overMapPullback (Type (max u v)) L.f).map
          (((J.overMapPullbackId (Type (max u v)) U).app G).hom)) ≫
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L).hom ≫
        (chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv := by
      rw [hcomp]
      rfl
/-- Helper for Lemma 8.11.8: after identifying the unique identity-pullback-cover leg over `L`,
the pulled comparison to `x` factors through the fixed chosen-cover source component and the
local chosen-object comparison over `L.f`. -/
theorem chosen_cover_identity_pullback_component_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U)
    (L : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    -- canonical recast: post-refactor the RHS owner sits in the descent-component world over the
    -- `overMapPullbackId`-shell, the codomain in `pf.map L.f (autoSheaf x)`; bridge the domain by
    -- the `overMapPullbackId` shell and the codomain by the base-change iso (both forced) so this
    -- equals the LHS `pf.map L.f`-pulled comparison. Consumer-coherence with Part15 to confirm
    -- during Part15 migration.
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (q := 𝟙 U) x).hom) =
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((J.overMapPullbackId (Type (max u v)) U).app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)).hom ≫
        ((chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U L).hom) ≫
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv := by
  rw [chosen_cover_identity_pullback_component_hom]
  exact chosen_cover_identity_pullback_local_object_component_normalized
    (𝒮 := 𝒮) hGerbe hAbelian x L
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let Ī : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    (𝟙 I.Y.left) ≫ Ky.f = qI := by
  intro Ī qI Ky
  show 𝟙 I.Y.left ≫ (I.f.left ≫ (T.unop.hom ≫ K.f)) = I.Y.hom ≫ K.f
  rw [Category.id_comp, ← Category.assoc]
  exact congrArg (· ≫ K.f) (Over.w I.f)

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let Ī : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    op ((Over.map Ky.f).obj (Over.mk (𝟙 I.Y.left))) = op ((Over.map K.f).obj I.Y) := by
  intro Ī qI Ky
  have hk : (𝟙 I.Y.left) ≫ Ky.f = qI :=
    chosen_local_target_refinement_member_identity_leg_eq (𝒮 := 𝒮) hGerbe L K T I hImem
  exact (over_map_obj_mk_eq_op Ky.f (𝟙 I.Y.left) qI hk).trans
    (congrArg op (over_map_obj_mk_eq K.f I.Y.hom qI rfl).symm)
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let αI :=
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op α)
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app T) α) =
      ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op I.Y))
        αI := by
  intro αI
  exact (FunctorToTypes.naturality _ _
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1 I.f.op α).symm
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let Ī : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    -- canonical recast: quantify over the section in the Ky-pulled sheaf (the αI binder was the
    -- pre-refactor defeq image of `α`); consumer-coherence with Part14 to confirm during Part14 migration.
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj (op (Over.mk (𝟙 I.Y.left)))),
    ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s =
      (((chosen_local_automorphism_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s := by
  intro Ī Ky s
  exact congrFun (congrArg (fun m => m.1.app (op (Over.mk (𝟙 I.Y.left))))
    (chosen_local_automorphism_iso_functor_map_component (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y) Ky)) s
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let Ī : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    -- canonical owner-transport recast (∀ s over the Ky-pulled section; the two sides land in
    -- different owner coordinates, bridged by `over_map_obj_mk_eq_op`-casts on input/output, exactly
    -- as `pseudofunctor_over_map_app_eq_owner_transport`); consumer-coherence with Part14 to confirm
    -- during Part14 migration.
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj (op (Over.mk (𝟙 I.Y.left)))),
    ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s =
      (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
        (chosen_local_target_refinement_member_owner_obj_eq_op (𝒮 := 𝒮) hGerbe L K T I hImem)).mpr
      (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)).1.app
          (op I.Y))
        (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).1.obj
          (chosen_local_target_refinement_member_owner_obj_eq_op (𝒮 := 𝒮) hGerbe L K T I hImem)) s)) := by
  intro Ī Ky s
  rw [pf_map_app_eq_image_app_obj, pf_map_app_eq_image_app_obj]
  exact app_obj_cast
    ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom).1
    (chosen_local_target_refinement_member_owner_obj_eq_op (𝒮 := 𝒮) hGerbe L K T I hImem) s

/-- Transport-stable identity-owner adapter for a chosen-local common-owner shell.  Replacing the
owner arrow `K.f` by an equal arrow `q` only inserts the corresponding sheaf casts around the
same `g = 𝟙` common-owner conjugation. -/
private theorem chosen_local_common_owner_identity_transport_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x z : 𝒮.p.Fiber U}
    (K : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x z).Arrow)
    (q : K.Y ⟶ U) (hKf : K.f = q) (hg : (𝟙 K.Y) ≫ K.f = q) :
    let O : (Over K.Y)ᵒᵖ := op (Over.mk (𝟙 K.Y))
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x ≪≫
        eqToIso (congrArg (fun m : K.Y ⟶ U =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p] x)) hKf)
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z ≪≫
        eqToIso (congrArg (fun m : K.Y ⟶ U =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p] z)) hKf)
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj O),
    (((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f x).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe K.f (K := K) (g := 𝟙 K.Y) (by simp)).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f z).inv).1.app O)
        s =
      outBridge.inv.1.app O
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe q (K := K) (g := 𝟙 K.Y) hg).hom).hom).1.app O
          (inBridge.hom.1.app O s)) := by
  cases hKf
  have hg_eq : hg = (by simp : (𝟙 K.Y) ≫ K.f = K.f) := Subsingleton.elim _ _
  cases hg_eq
  dsimp only
  intro s
  rfl
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let Ī : ((chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).pullback (T.unop.hom ≫ K.f)).Arrow :=
      ⟨I.Y.left, I.f.left, hImem⟩
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let Ky :
        (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).Arrow :=
      Ī.base
    -- canonical recast: drop the mistyped `α`/`αI`; quantify over `s` in the descent-component
    -- input world `pf.map Ky.f (autoSheaf coverObj)`, then bridge both input and output into the
    -- common-owner conjugation world `autoSheaf (qI ^* _)` via the canonical base-change isos
    -- composed with the forced `Ky.f = qI` cast (`hKf`).
    let hKf : Ky.f = qI :=
      (Category.id_comp Ky.f).symm.trans
        (chosen_local_target_refinement_member_identity_leg_eq
          (𝒮 := 𝒮) hGerbe L K T I hImem)
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L) ≪≫
        eqToIso (congrArg (fun m : I.Y.left ⟶ L.Y =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))) hKf)
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) ≪≫
        eqToIso (congrArg (fun m : I.Y.left ⟶ L.Y =>
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (m ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y))) hKf)
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map Ky.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj (op (Over.mk (𝟙 I.Y.left)))),
    (((chosen_local_automorphism_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app
      (op (Over.mk (𝟙 I.Y.left))))
      s =
      outBridge.inv.1.app (op (Over.mk (𝟙 I.Y.left)))
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
              (chosen_local_target_refinement_member_identity_leg_eq
                (𝒮 := 𝒮) hGerbe L K T I hImem)).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left)))
          (inBridge.hom.1.app (op (Over.mk (𝟙 I.Y.left))) s)) := by
  intro Ī qI Ky hKf inBridge outBridge s
  let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
  have hlocal :
      (chosen_local_automorphism_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky =
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe Ky.f (K := Ky) (g := 𝟙 Ky.Y) (by simp)).hom).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv := by
    have hconj := congrArg Iso.hom
      (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y) Ky).hom
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe Ky.f (K := Ky) (g := 𝟙 Ky.Y) (by simp)).hom)
    simpa [chosen_local_automorphism_descent_iso] using
      congrArg
        (fun m =>
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫ m ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv)
        hconj
  change
    (((chosen_local_automorphism_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app O) s =
      outBridge.inv.1.app O
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := Ky) (g := 𝟙 I.Y.left)
              (chosen_local_target_refinement_member_identity_leg_eq
                (𝒮 := 𝒮) hGerbe L K T I hImem)).hom).hom).1.app O
          (inBridge.hom.1.app O s))
  have happ :
      (((chosen_local_automorphism_descent_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom.hom Ky).1.app O) s =
        (((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe Ky.f (K := Ky) (g := 𝟙 Ky.Y) (by simp)).hom).hom ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian Ky.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv).1.app O) s := by
    exact congrFun (congrArg (fun m => m.1.app O) hlocal) s
  rw [happ]
  exact chosen_local_common_owner_identity_transport_app
    (𝒮 := 𝒮) hGerbe hAbelian Ky qI hKf
      (chosen_local_target_refinement_member_identity_leg_eq
        (𝒮 := 𝒮) hGerbe L K T I hImem) s
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    -- canonical recast: drop the mistyped `α`/`αI`; quantify over a section `s` in the original
    -- `pf.map K.f (autoSheaf coverObj)` world, bridge it into the source conjugation composite's
    -- domain `autoSheaf (K.f ^* coverObj)` via `inBridge`, insert the forced middle base-change
    -- bridge `bIso` (so the composite actually composes after the refactor), and bridge the output
    -- back into the original `pf.map K.f (autoSheaf (L.f ^* y))` world via `cIso`.
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y)
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj T),
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y))).1.map I.f.op
        (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          bIso.inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)) ≫
          cIso.hom).1.app T)
          (inBridge.hom.1.app T s)) =
      (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
          bIso.inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)) ≫
          cIso.hom).1.app
        (op I.Y))
        (inBridge.hom.1.app (op I.Y)
          ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.map I.f.op s))) := by
  intro inBridge bIso cIso s
  exact (FunctorToTypes.naturality _ _
    (inBridge.hom ≫
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom) ≫
        bIso.inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)) ≫
        cIso.hom)).1 I.f.op s).symm
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- canonical recast: quantify over the section in the K.f-pulled `L.f^*x` sheaf (the αI/sourceI
    -- binders were the pre-refactor defeq image of `α`); both branches bridged by
    -- `automorphismUnderlyingSheafBaseChangeIso` (base change along L.f) on input/output and by
    -- `over_map_obj_mk_eq_op` owner transport on the output owner coordinate.
    ∀ sourceI : ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).1.obj (op I.Y)),
    ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom))).1.app
      (op I.Y))
      (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv).1.app
          (op I.Y))
        sourceI) =
      (congrArg (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).1.obj
          (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl)).mpr
        (((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
            (op (Over.mk qI)))
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv.1.app
            (op (Over.mk qI))
            (Eq.mp
              (congrArg
                ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj)
                (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl))
              sourceI))) := by
  intro qI sourceI
  exact app_obj_cast
    ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1
    (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl) sourceI
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    -- canonical recast: quantify over the section `s` in the K.f-pulled `coverObj` sheaf (the
    -- αI binder was its pre-refactor defeq image). `sourceI` is reconstructed from `s` by the
    -- input base-change `automorphismUnderlyingSheafBaseChangeIso K.f coverObj`, the conjugation
    -- comparison, and the output base-change-back `... K.f (L.f^*x)` so that the literal owner cast
    -- `over_map_obj_mk_eq_op K.f I.Y.hom qI rfl` of the prompt applies; the right branch carries the
    -- same base-change-back plus the `(𝟙 ≫ I.Y.hom) ≫ K.f = qI` owner transport.
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj (op I.Y)),
    let sourceI :=
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv.1.app (op I.Y)
        ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom).1.app
          (op I.Y))
          ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app (op I.Y) s)))
    Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj)
          (over_map_obj_mk_eq_op K.f I.Y.hom qI rfl))
        sourceI =
      Eq.mp
        (congrArg
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj)
          (over_map_obj_mk_eq_op K.f (𝟙 I.Y.left ≫ I.Y.hom) qI (by simp [qI])))
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv.1.app
          (op ((Over.map I.Y.hom).obj (Over.mk (𝟙 I.Y.left))))
          (((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                  (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                    (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
              (op (Over.mk (𝟙 I.Y.left))))
            ((congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (K.f ^*[canonicalPullbackChoice 𝒮.p]
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))).1.obj
                (over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom
                  (Category.id_comp I.Y.hom))).mpr
            ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom.1.app (op I.Y) s)))) := by
  intro qI s
  let inB :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)).hom
  let conj :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom
  let outB :=
    (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).inv
  let hI : op ((Over.map I.Y.hom).obj (Over.mk (𝟙 I.Y.left))) = op I.Y :=
    over_map_obj_mk_eq_op I.Y.hom (𝟙 I.Y.left) I.Y.hom
      (Category.id_comp I.Y.hom)
  let hK :=
    over_map_obj_mk_eq_op K.f I.Y.hom qI rfl
  let hK' :=
    over_map_obj_mk_eq_op K.f (𝟙 I.Y.left ≫ I.Y.hom) qI (by simp [qI])
  rw [pf_map_app_eq_image_app_obj]
  have hconj :=
    app_obj_cast_mpr conj.1 hI
      (inB.1.app (op I.Y) s)
  have hout :=
    app_obj_cast_mpr outB.1 hI
      (conj.1.app (op I.Y) (inB.1.app (op I.Y) s))
  dsimp only [inB, conj, outB] at hconj hout
  erw [hconj, hout]
  apply eq_of_heq
  simp only [eq_mp_eq_cast, eq_mpr_eq_cast]
  refine (heq_cast_iff_heq _ _ _).2 ?_
  refine (heq_cast_iff_heq _ _ _).2 ?_
  rfl
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
      (((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x))).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) ≫
      ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom := by
  intro qI pulledφ
  let M :=
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc I.Y.hom.op.toLoc qI.op.toLoc (by cat_disch)
  let B :=
    ((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≪≫
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
  let bcX :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] x)
  let bcY :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  have htarget :
      M.hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) =
        bcX.hom ≫ target ≫ B.inv := by
    simpa [M, B, bcX, target] using
      chosen_local_target_mapComp'_hom_eq_common_owner_target_iso_hom
        (𝒮 := 𝒮) hGerbe hAbelian qI (K := K) I.Y.hom (by simp [qI])
  have hfront :
      target ≫ B.inv ≫
          M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) =
        bcX.inv := by
    have hmul :
        bcX.hom ≫
            (target ≫ B.inv ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) =
          𝟙 _ := by
      calc
        bcX.hom ≫
            (target ≫ B.inv ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x))) =
            (bcX.hom ≫ target ≫ B.inv) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) := by
          simp only [Category.assoc]
        _ =
            M.hom.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫
              M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) := by
          exact congrArg
            (fun m =>
              m ≫ M.inv.toNatTrans.app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (L.f ^*[canonicalPullbackChoice 𝒮.p] x)))
            htarget.symm
        _ = 𝟙 _ := by
          simpa [M, Cat.Hom.toNatIso] using
            Iso.hom_inv_id_app (Cat.Hom.toNatIso M)
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    have hfront' :
        target ≫ B.inv ≫
            M.inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) =
          bcX.inv ≫ 𝟙 _ :=
      (Iso.eq_inv_comp bcX).mpr hmul
    simpa using hfront'
  have hpull :=
    automorphismUnderlyingSheafConj_pullbackFunctor_map
      (𝒮 := 𝒮) hAbelian qI pulledφ
  let pulledMap :=
    ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
  let pulledConj :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).map pulledφ)).hom
  let pulledConjIso :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
        (asIso pulledφ)).hom)).hom
  change target ≫ B.inv ≫
      M.inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫ pulledMap ≫ bcY.hom =
    pulledConj
  have hstep1 :
      target ≫ B.inv ≫
          M.inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)) ≫ pulledMap ≫ bcY.hom =
        bcX.inv ≫ pulledMap ≫ bcY.hom := by
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ pulledMap ≫ bcY.hom) hfront
  have hstep2a : bcX.inv ≫ pulledMap ≫ bcY.hom = pulledConjIso := by
    dsimp [pulledMap, pulledConjIso]
    rw [hpull]
    change bcX.inv ≫ (bcX.hom ≫ pulledConjIso ≫ bcY.inv) ≫ bcY.hom =
      pulledConjIso
    change (bcX.inv ≫ (bcX.hom ≫ pulledConjIso ≫ bcY.inv)) ≫ bcY.hom =
      pulledConjIso
    rw [← Category.assoc bcX.inv bcX.hom (pulledConjIso ≫ bcY.inv)]
    rw [bcX.inv_hom_id]
    rw [Category.id_comp]
    rw [Category.assoc, bcY.inv_hom_id, Category.comp_id]
  have hstep2 : bcX.inv ≫ pulledMap ≫ bcY.hom = pulledConj := by
    exact hstep2a.trans (by rfl)
  exact hstep1.trans hstep2
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
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x)).1.obj (op (Over.mk q))),
    ((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
      (op (Over.mk q))) s =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y).inv.1.app
        (op (Over.mk q))
        (Eq.mp
          (congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
            (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp)))
          (((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
              (op (Over.mk (𝟙 Z))))
            ((congrArg
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
                (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp))).mpr
              ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
                (op (Over.mk q)) s)))) := by
  intro pulledφ s
  have hnat :=
    automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian f φ
  have key := congrFun (congrArg (fun m => m.1.app (op (Over.mk q))) hnat) s
  refine key.trans ?_
  change (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y).inv.1.app
      (op (Over.mk q))
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom.1.app (op (Over.mk q))
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
          (op (Over.mk q)) s)) = _
  rw [pseudofunctor_over_map_app_eq_owner_transport (J := J) q
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom (𝟙 Z) q (by simp)
    ((congrArg
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
        (over_map_obj_mk_eq_op q (𝟙 Z) q (by simp))).mpr
      ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).hom.1.app
        (op (Over.mk q)) s))]
  simp only [eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq]
  congr 1

/-- Boundary-oriented form of `automorphismUnderlyingSheafConj_outer_app_eq_pulled_app`: after
moving a section from the `q`-owner into the literal `Over.mk q` owner and applying the outer
`f`-pulled conjugation, the two base-change isomorphisms cancel and the result is the pulled
conjugation along `q` at the literal identity owner. -/
private theorem automorphismUnderlyingSheafConj_outer_boundary_app
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y Z : C} {x y : 𝒮.p.Fiber U} (f : Y ⟶ U) (q : Z ⟶ Y) (φ : x ⟶ y) :
    let pulledφ :
        (f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor f).map φ
    ∀ z : ((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (f ^*[canonicalPullbackChoice 𝒮.p] x))).1.obj
        (op (Over.mk (𝟙 Z)))),
    Eq.mp
        (congrArg
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
          (over_map_obj_mk_eq_op q (𝟙 Z) q (Category.id_comp q)).symm)
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y).hom.1.app
          (op (Over.mk q))
          (((((J.pseudofunctorOver (Type (max u v))).map f.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
              (op (Over.mk q)))
            ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x).inv.1.app
              (op (Over.mk q))
              (Eq.mp
                (congrArg
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
                  (over_map_obj_mk_eq_op q (𝟙 Z) q (Category.id_comp q)))
                z)))) =
      (((((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
          (op (Over.mk (𝟙 Z))))
        z) := by
  intro pulledφ z
  let hq := over_map_obj_mk_eq_op q (𝟙 Z) q (Category.id_comp q)
  let bcX := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f x
  let bcY := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f y
  have houter :=
    automorphismUnderlyingSheafConj_outer_app_eq_pulled_app
      (𝒮 := 𝒮) hAbelian f q φ
      (bcX.inv.1.app (op (Over.mk q))
        (Eq.mp
          (congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj hq)
          z))
  rw [houter]
  rw [sheaf_iso_inv_hom_app bcY (op (Over.mk q))]
  rw [sheaf_iso_inv_hom_app bcX (op (Over.mk q))]
  apply eq_of_heq
  simp only [pulledφ, eq_mp_eq_cast, eq_mpr_eq_cast]
  repeat
    first
    | refine (cast_heq_iff_heq _ _ _).2 ?_
    | refine (heq_cast_iff_heq _ _ _).2 ?_
  apply Eq.heq
  apply congr_heq
  · rfl
  · exact (cast_heq _ _).trans (cast_heq _ _)
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p] (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        s =
      outBridge.inv.1.app (op (Over.mk (𝟙 I.Y.left)))
        (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_source_iso
                (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom) ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_common_owner_target_iso
                (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
                (by simp [qI])).hom).hom).1.app
          (op (Over.mk (𝟙 I.Y.left))))
          (inBridge.hom.1.app (op (Over.mk (𝟙 I.Y.left))) s)) := by
  intro qI inBridge outBridge s
  have h := congrArg
    (fun m => m.1.app (op (Over.mk (𝟙 I.Y.left))))
    (chosen_local_pulled_conjugation_eq_common_owner_middle
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := qI) (K := K) (g := I.Y.hom) (by simp [qI]))
  exact congrFun h s
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
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
      (L.f ^*[canonicalPullbackChoice 𝒮.p] y)) (I.f.left ≫ (T.unop.hom ≫ K.f))) :
    let qI : I.Y.left ⟶ L.Y := I.Y.hom ≫ K.f
    let pulledφ :
        (L.f ^*[canonicalPullbackChoice 𝒮.p] x) ⟶
          (L.f ^*[canonicalPullbackChoice 𝒮.p] y) :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor L.f).map φ
    let inBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L))
    let outBridge :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I.Y.hom
        (K.f ^*[canonicalPullbackChoice 𝒮.p] (L.f ^*[canonicalPullbackChoice 𝒮.p] x))
    let midBridge :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (chosen_local_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom) (by simp [qI])).hom).symm ≪≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).symm
    let bcLx := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f x
    let bcLy := automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian L.f y
    ∀ s : ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    let inner :=
      ((((J.pseudofunctorOver (Type (max u v))).map I.Y.hom.op.toLoc).toFunctor.map
            ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L)
                (L.f ^*[canonicalPullbackChoice 𝒮.p] x) K).hom).hom)).1.app
          (op (Over.mk (𝟙 I.Y.left))))
        s
    let lhsArg :=
      bcLx.inv.1.app (op (Over.mk qI))
        (Eq.mp
          (congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (L.f ^*[canonicalPullbackChoice 𝒮.p] x)).1.obj
            (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (Category.id_comp qI)))
          (midBridge.hom.1.app (op (Over.mk (𝟙 I.Y.left)))
            (outBridge.hom.1.app (op (Over.mk (𝟙 I.Y.left))) inner)))
    Eq.mp
        (congrArg
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).1.obj
          (over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (Category.id_comp qI)).symm)
        (bcLy.hom.1.app (op (Over.mk qI))
          (((((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
                ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom)).1.app
              (op (Over.mk qI)))
            lhsArg)) =
      (((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (chosen_local_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
              (by simp [qI])).hom).hom) ≫
        midBridge.hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app
        (op (Over.mk (𝟙 I.Y.left))))
      (inBridge.hom.1.app (op (Over.mk (𝟙 I.Y.left))) s) := by
  intro qI pulledφ inBridge outBridge midBridge bcLx bcLy s inner lhsArg
  let O : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left))
  let source :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe qI I.Y.hom (by simp [qI])).inv).hom
  let common :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let target :=
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (chosen_local_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe qI (K := K) (g := I.Y.hom)
        (by simp [qI])).hom).hom
  let shell := source ≫ common ≫ target
  let qPhi :=
    ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)
  let hq := over_map_obj_mk_eq_op qI (𝟙 I.Y.left) qI (Category.id_comp qI)
  have hinner :
      inner =
        outBridge.inv.1.app O
          (shell.1.app O (inBridge.hom.1.app O s)) := by
    simpa [O, source, common, target, shell, inBridge, outBridge, qI, Category.assoc] using
      (chosen_local_pulled_conjugation_eq_common_owner_middle_app
        (𝒮 := 𝒮) (x := x) (y := y) hGerbe hAbelian L K T I s)
  let z := midBridge.hom.1.app O (outBridge.hom.1.app O inner)
  have hz :
      z = midBridge.hom.1.app O
        (shell.1.app O (inBridge.hom.1.app O s)) := by
    dsimp [z]
    rw [hinner]
    rw [sheaf_iso_inv_hom_app outBridge O]
  have hboundary :=
    automorphismUnderlyingSheafConj_outer_boundary_app
      (𝒮 := 𝒮) hAbelian L.f qI φ z
  calc
    _ =
        (((((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian pulledφ).hom)).1.app O)
          z) := by
        simpa [z, lhsArg, bcLx, bcLy, hq, eq_mp_eq_cast, eq_mpr_eq_cast] using hboundary
    _ = _ := by
        rw [hz]
        simp [O, source, common, target, shell, Category.assoc]

end

end CategoryTheory
