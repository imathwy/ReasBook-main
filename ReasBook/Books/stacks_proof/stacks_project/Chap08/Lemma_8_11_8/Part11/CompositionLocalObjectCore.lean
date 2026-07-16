import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part11.CompositionLocalObjectRefinedAdapter

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: naturality of the composite-pullback shell after one further
pullback.  It moves a morphism on `C / U` through the `overMapPullbackComp` component and the
outer `mapComp'` inverse. -/
private theorem overMapPullbackComp_mapComp'_inv_naturality
    {U V Y Z : C} (f : V ⟶ U) (g : Y ⟶ V) (h : Z ⟶ Y)
    (F G : Sheaf (J.over U) (Type (max u v))) (a : F ⟶ G) :
    ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) g f).app F).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (g ≫ f).op.toLoc h.op.toLoc ((h ≫ g) ≫ f).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])).inv.toNatTrans.app F) ≫
      ((J.pseudofunctorOver (Type (max u v))).map ((h ≫ g) ≫ f).op.toLoc).toFunctor.map a =
    ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          ((J.overMapPullback (Type (max u v)) f).map a)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map h.op.toLoc).toFunctor.map
        (((J.overMapPullbackComp (Type (max u v)) g f).app G).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          (g ≫ f).op.toLoc h.op.toLoc ((h ≫ g) ≫ f).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])).inv.toNatTrans.app G) := by
  let P := J.pseudofunctorOver (Type (max u v))
  let Fh := (P.map h.op.toLoc).toFunctor
  let M :=
    P.mapComp' (g ≫ f).op.toLoc h.op.toLoc ((h ≫ g) ≫ f).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])
  have hM :
      Fh.map
          (((J.overMapPullback (Type (max u v)) (g ≫ f)).map a)) ≫
        M.inv.toNatTrans.app G =
      M.inv.toNatTrans.app F ≫
        ((P.map ((h ≫ g) ≫ f).op.toLoc).toFunctor.map a) := by
    simpa [P, Fh, M] using
      (P.mapComp'_inv_naturality (g ≫ f).op.toLoc h.op.toLoc
        ((h ≫ g) ≫ f).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc]) a)
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
        ((P.map ((h ≫ g) ≫ f).op.toLoc).toFunctor.map a) =
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
        rw [← Category.assoc]
        rw [← Fh.map_comp]
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

/-- Helper for Lemma 8.11.8: one pullback-cover component of the sheaf-level local-object
comparison is the corresponding component of the transported descent-data comparison. -/
private theorem chosen_cover_pullback_to_local_object_iso_pullback_cover_component_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
      ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian q y).hom) =
    (pullback_cover_local_object_comparison_descent_iso
      (𝒮 := 𝒮) hGerbe hAbelian q y).hom.hom L := by
  let S := chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q
  have hmap :=
    localizedSheafTransportIsoOfCoverDescentIso_functor_map (J := J)
      S
      (pullback_cover_local_object_comparison_descent_iso
        (𝒮 := 𝒮) hGerbe hAbelian q y)
  have hcomp := congrArg (fun m => m.hom L) hmap
  simpa [S, chosen_cover_pullback_to_local_object_iso,
    localizedSheafToCoverDescentEquivalence_functor_map_component] using hcomp

/-- Helper for Lemma 8.11.8: the previous component bridge with the transported descent-data
component expanded to its source `mapComp'` shell. -/
private theorem chosen_cover_pullback_to_local_object_iso_pullback_cover_component_hom_mapComp'_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    (L : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
      ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian q y).hom) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          q.op.toLoc L.f.op.toLoc (L.f ≫ q).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U L.base).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U L.base)
        (L.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian L.f y).inv := by
  rw [chosen_cover_pullback_to_local_object_iso_pullback_cover_component_hom
    (𝒮 := 𝒮) hGerbe hAbelian q y L]
  simp [pullback_cover_local_object_comparison_descent_iso,
    pullback_cover_local_object_component_iso,
    pullback_cover_source_component_iso,
    Pseudofunctor.DescentData.isoMk_hom_hom,
    Iso.trans_hom, Iso.symm_hom, Cat.Hom.toNatIso,
    mapComp'_inv_app_eq_mapComp]
  rfl

/-- Helper for Lemma 8.11.8: common refinement of the two pullback covers needed to compare the
`(g ≫ f)` and `g` mixed-cover components after fixing the chosen-cover arrow `K`. -/
private noncomputable abbrev mixed_cover_transport_common_refinement_cover
    (hGerbe : IsGerbe J 𝒮.p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow) : J.Cover K.Y :=
  chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (K.f ≫ I.f ≫ g ≫ f) ⊓
    chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (K.f ≫ I.f ≫ g)

/-- Helper for Lemma 8.11.8: view one arrow of the common refinement as an arrow of the
`U`-side pullback cover over `I.Y`. -/
private noncomputable def mixed_cover_transport_common_refinement_U_arrow
    (hGerbe : IsGerbe J 𝒮.p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    (R : (mixed_cover_transport_common_refinement_cover
      (𝒮 := 𝒮) hGerbe f g I K).Arrow) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ g ≫ f)).Arrow :=
  ⟨R.Y, R.f ≫ K.f, by
    have hmem :
        (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe
          (K.f ≫ I.f ≫ g ≫ f)) R.f := R.hf.1
    have hchosen :
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (R.f ≫ (K.f ≫ I.f ≫ g ≫ f)) :=
      (chosen_cover_pullback_cover_hom_mem_iff
        (𝒮 := 𝒮) hGerbe (K.f ≫ I.f ≫ g ≫ f) R.f).1 hmem
    change (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      ((R.f ≫ K.f) ≫ (I.f ≫ g ≫ f))
    simpa only [Category.assoc] using hchosen⟩

/-- Helper for Lemma 8.11.8: view one arrow of the common refinement as an arrow of the
`V`-side pullback cover over `I.Y`. -/
private noncomputable def mixed_cover_transport_common_refinement_V_arrow
    (hGerbe : IsGerbe J 𝒮.p)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    (R : (mixed_cover_transport_common_refinement_cover
      (𝒮 := 𝒮) hGerbe f g I K).Arrow) :
    (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe (I.f ≫ g)).Arrow :=
  ⟨R.Y, R.f ≫ K.f, by
    have hmem :
        (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe
          (K.f ≫ I.f ≫ g)) R.f := R.hf.2
    have hchosen :
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
          (R.f ≫ (K.f ≫ I.f ≫ g)) :=
      (chosen_cover_pullback_cover_hom_mem_iff
        (𝒮 := 𝒮) hGerbe (K.f ≫ I.f ≫ g) R.f).1 hmem
    change (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V)
      ((R.f ≫ K.f) ≫ (I.f ≫ g))
    simpa only [Category.assoc] using hchosen⟩

/-- Helper for Lemma 8.11.8: after one further localization to a common refinement, the two
mixed-cover component isomorphisms are exactly the corresponding pullbacks of the sheaf-level
local-object comparisons. -/
private theorem mixed_cover_secondary_cover_component_iso_refines_to_pullback_arrows
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    (R : (mixed_cover_transport_common_refinement_cover
      (𝒮 := 𝒮) hGerbe f g I K).Arrow) :
    let P := J.pseudofunctorOver (Type (max u v))
    let y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I
    let FR := (P.map R.f.op.toLoc).toFunctor
    let FK := (P.map K.f.op.toLoc).toFunctor
    FR.map ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I K).hom) =
      FR.map (FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f) y).hom)) ∧
    FR.map ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian g I K).hom) =
      FR.map (FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g) y).hom)) := by
  intro P y FR FK
  constructor
  · rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component,
      chosen_cover_pullback_to_local_object_component_iso_hom]
    rfl
  · rw [mixed_cover_secondary_cover_component_iso_eq_pullback_component,
      chosen_cover_pullback_to_local_object_component_iso_hom]
    rfl

/-- Helper for Lemma 8.11.8: normal form for the fixed-`K`, fixed-`R` local-object transport
component after both mixed-cover components have been rewritten to the generic
`chosen_cover_pullback_to_local_object_iso` comparison and the outer `FR.map` has been distributed.
This is the remaining narrow varying-`U` interface: all large constructions are named as
`FI/FK/FR`, and no mixed-cover transport shell remains in the statement. -/
private theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component_mixed_nf
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    (R : (mixed_cover_transport_common_refinement_cover
      (𝒮 := 𝒮) hGerbe f g I K).Arrow) :
    let P := J.pseudofunctorOver (Type (max u v))
    let AU := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let AV := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V
    let τ := chosen_cover_transport_transition
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)
    let y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I
    let FI := (P.map I.f.op.toLoc).toFunctor
    let FK := (P.map K.f.op.toLoc).toFunctor
    let FR := (P.map R.f.op.toLoc).toFunctor
    let aR := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
    let bR := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
    FR.map (FK.map (FI.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app AU))) ≫
      FR.map (FK.map
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app AU)) ≫
      FR.map (FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f) y).hom)) =
    FR.map (FK.map aR) ≫ FR.map (FK.map bR) ≫
      FR.map (FK.map ((chosen_cover_pullback_to_local_object_iso
        (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g) y).hom)) := by
  intro P AU AV τ y FI FK FR aR bR
  simpa only [Functor.map_comp, Category.assoc] using
    chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined_deferred
      (𝒮 := 𝒮) hGerbe hAbelian f g I K R.f

/-- Helper for Lemma 8.11.8: the fixed-`K` local-object transport component after pulling once
more to the common refinement of the `U`- and `V`-side mixed covers.  This is the narrow
associativity/naturality adapter for the varying-`U` source shell: all large components are named
as `FI/FK/FR`, and the two mixed-cover components are first reduced to the generic
pullback-to-local-object comparison normal forms. -/
private theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow)
    (K : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y).Arrow)
    (R : (mixed_cover_transport_common_refinement_cover
      (𝒮 := 𝒮) hGerbe f g I K).Arrow) :
    let P := J.pseudofunctorOver (Type (max u v))
    let AU := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U
    let AV := chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian V
    let τ := chosen_cover_transport_transition
      (𝒮 := 𝒮) hGerbe hAbelian (f := f)
      (chosen_cover_descent_transition_iso
        (𝒮 := 𝒮) hGerbe hAbelian f)
    let FI := (P.map I.f.op.toLoc).toFunctor
    let FK := (P.map K.f.op.toLoc).toFunctor
    let FR := (P.map R.f.op.toLoc).toFunctor
    let aR := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
    let bR := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
    FR.map (FK.map (FI.map
        ((J.overMapPullbackComp (Type (max u v)) g f).hom.app AU))) ≫
      FR.map (FK.map
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app AU)) ≫
      FR.map ((mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I K).hom) =
    FR.map (FK.map aR ≫ FK.map bR ≫
      (mixed_cover_secondary_cover_component_iso
        (𝒮 := 𝒮) hGerbe hAbelian g I K).hom) := by
  exact
    chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined_mixed_deferred
      (𝒮 := 𝒮) hGerbe hAbelian f g I K R.f

/-- Helper for Lemma 8.11.8: the local-object comparison transports the composite
pullback source shell to the source shell obtained by first transporting the `f`-transition and
then pulling along `I.f`.  This is the core sheaf-level comparison before pulling once more by a
secondary-cover arrow. -/
theorem chosen_cover_pullback_to_local_object_iso_transport_transition_component_core
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe W).Arrow) :
      (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          ((J.overMapPullbackComp (Type (max u v)) g f).hom.app
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
        ((J.overMapPullbackComp (Type (max u v)) I.f (g ≫ f)).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian U)) ≫
        (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g ≫ f)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom =
      (((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map
          (((J.overMapPullback (Type (max u v)) g).mapIso
            (chosen_cover_transport_transition
              (𝒮 := 𝒮) hGerbe hAbelian (f := f)
              (chosen_cover_descent_transition_iso
                (𝒮 := 𝒮) hGerbe hAbelian f))).hom) ≫
        ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app
          (chosen_cover_underlying_automorphism_sheaf
            (𝒮 := 𝒮) hGerbe hAbelian V)) ≫
    (chosen_cover_pullback_to_local_object_iso
          (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom)) := by
  let AU := chosen_cover_underlying_automorphism_sheaf
    (𝒮 := 𝒮) hGerbe hAbelian U
  let AV := chosen_cover_underlying_automorphism_sheaf
    (𝒮 := 𝒮) hGerbe hAbelian V
  let τ := chosen_cover_transport_transition
    (𝒮 := 𝒮) hGerbe hAbelian (f := f)
    (chosen_cover_descent_transition_iso
      (𝒮 := 𝒮) hGerbe hAbelian f)
  let FI := ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor
  have hnat :
      ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app
          ((J.overMapPullback (Type (max u v)) f).obj AU)) ≫
        ((J.overMapPullback (Type (max u v)) (I.f ≫ g)).map τ.hom) =
      FI.map (((J.overMapPullback (Type (max u v)) g).map τ.hom)) ≫
        ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV) := by
    simpa [AU, AV, τ, FI] using
      (((J.overMapPullbackComp (Type (max u v)) I.f g).hom.naturality τ.hom).symm)
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe I.Y
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) S).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) S).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) S).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  simp only [Functor.map_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  rw [← chosen_cover_pullback_to_local_object_component_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := I.f ≫ g ≫ f)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  rw [← mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian (g ≫ f) I K]
  let FK := ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor
  let aR := FI.map (((J.overMapPullback (Type (max u v)) g).mapIso τ).hom)
  let bR := ((J.overMapPullbackComp (Type (max u v)) I.f g).hom.app AV)
  let cR := (chosen_cover_pullback_to_local_object_iso
    (𝒮 := 𝒮) hGerbe hAbelian (I.f ≫ g)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I)).hom
  have hRsplit : FK.map (aR ≫ bR ≫ cR) =
      FK.map aR ≫ FK.map bR ≫ FK.map cR := by
    calc
      FK.map (aR ≫ bR ≫ cR) = FK.map (aR ≫ bR) ≫ FK.map cR := by
        exact FK.map_comp (aR ≫ bR) cR
      _ = (FK.map aR ≫ FK.map bR) ≫ FK.map cR := by
        rw [FK.map_comp aR bR]
      _ = FK.map aR ≫ FK.map bR ≫ FK.map cR := by
        simp only [Category.assoc]
  change _ = FK.map (aR ≫ bR ≫ cR)
  rw [hRsplit]
  rw [← chosen_cover_pullback_to_local_object_component_iso_hom
      (𝒮 := 𝒮) hGerbe hAbelian
      (q := I.f ≫ g)
      (y := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe W I) K]
  rw [← mixed_cover_secondary_cover_component_iso_eq_pullback_component
      (𝒮 := 𝒮) hGerbe hAbelian g I K]
  let T := mixed_cover_transport_common_refinement_cover
    (𝒮 := 𝒮) hGerbe f g I K
  haveI : (localizedSheafToCoverDescentEquivalence (J := J) T).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J) T).faithful
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J) T).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro R
  simp only [Functor.map_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component]
  simpa only [Functor.map_comp, Category.assoc] using
    chosen_cover_pullback_to_local_object_iso_transport_transition_component_refined
      (𝒮 := 𝒮) hGerbe hAbelian f g I K R

end CategoryTheory
