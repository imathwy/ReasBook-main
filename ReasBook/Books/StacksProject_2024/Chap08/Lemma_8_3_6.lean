import StacksProject_2024.Chap08.Definition_8_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

variable {p : S ⥤ C} (hc : PullbackChoice p)
variable {U : C} {𝒰 : SemiRepresentableFamily.Over U} [HasDescentPullbacks 𝒰]

/-- Helper for Lemma 8.3.6: the two overlap composites to `U` induce the same chosen pullback
object after transporting along `pr₀ ≫ f_i = pr₁ ≫ f_j`. -/
private theorem family_descent_functor_obj_overlap_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) X =
      hc.obj (𝒰.pr1 i i' ≫ (𝒰.obj i').hom) X := by
  simpa using congrArg (fun f ↦ hc.obj f X) (𝒰.pr0_map_eq_pr1_map i i')

/-- Helper for Lemma 8.3.6: the left overlap composite and the chosen overlap map induce the same
pullback object in the fiber over `U`. -/
private theorem family_descent_functor_obj_pr0_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pr0 i i' ≫ (𝒰.obj i).hom) X =
      hc.obj (𝒰.pairwisePullback i i').p X := by
  simpa using congrArg (fun f ↦ hc.obj f X) (𝒰.pr0_map i i')

/-- Helper for Lemma 8.3.6: the chosen overlap map and the right overlap composite induce the same
pullback object in the fiber over `U`. -/
private theorem family_descent_functor_obj_pr1_transport
    (X : p.Fiber U) (i i' : 𝒰.index) :
    hc.obj (𝒰.pairwisePullback i i').p X =
      hc.obj (𝒰.pr1 i i' ≫ (𝒰.obj i').hom) X := by
  simpa using (congrArg (fun f ↦ hc.obj f X) (𝒰.pr1_map i i')).symm

/-- Helper for Lemma 8.3.6: the overlap transport factors through the chosen overlap map. -/
private theorem family_descent_functor_obj_overlap_transport_eq
    (X : p.Fiber U) (i i' : 𝒰.index) :
    family_descent_functor_obj_overlap_transport (hc := hc) (𝒰 := 𝒰) X i i' =
      (family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i').trans
        (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
  apply Subsingleton.elim

/-- Helper for Lemma 8.3.6: the inverse component of the fiber pseudofunctor's flexible
composition comparison is the chosen pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
        (f.op.toLoc ≫ g.op.toLoc) (by simp)).inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).inv := by
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.6: the hom component of the fiber pseudofunctor's flexible composition
comparison is the chosen pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
        (f.op.toLoc ≫ g.op.toLoc) (by simp)).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  simp [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp]

/-- Helper for Lemma 8.3.6: on the left overlap leg, the localized opposite composite agrees with
the chosen pairwise-overlap map. -/
private theorem family_descent_functor_obj_pr0_map_toLoc
    (i i' : 𝒰.index) :
    (𝒰.obj i).hom.op.toLoc ≫ (𝒰.pr0 i i').op.toLoc =
      ((𝒰.pairwisePullback i i').p).op.toLoc := by
  simpa using congrArg (fun f ↦ f.op.toLoc) (𝒰.pr0_map i i')

/-- Helper for Lemma 8.3.6: on the right overlap leg, the localized opposite composite agrees
with the chosen pairwise-overlap map. -/
private theorem family_descent_functor_obj_pr1_map_toLoc
    (i i' : 𝒰.index) :
    (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc =
      ((𝒰.pairwisePullback i i').p).op.toLoc := by
  simpa using congrArg (fun f ↦ f.op.toLoc) (𝒰.pr1_map i i')

/-- Helper for Lemma 8.3.6: the left pullback-comparison iso on the pairwise overlap. -/
private noncomputable abbrev familyDescentFunctor_obj_pr0Comparison
    (i i' : 𝒰.index) :
    hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
      hc.fiberPseudofunctor.map (𝒰.obj i).hom.op.toLoc ≫
        hc.fiberPseudofunctor.map (𝒰.pr0 i i').op.toLoc :=
  hc.fiberPseudofunctor.mapComp'
    (𝒰.obj i).hom.op.toLoc
    (𝒰.pr0 i i').op.toLoc
    ((𝒰.pairwisePullback i i').p).op.toLoc
    (family_descent_functor_obj_pr0_map_toLoc (𝒰 := 𝒰) i i')

/-- Helper for Lemma 8.3.6: the right pullback-comparison iso on the pairwise overlap. -/
private noncomputable abbrev familyDescentFunctor_obj_pr1Comparison
    (i i' : 𝒰.index) :
    hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
      hc.fiberPseudofunctor.map (𝒰.obj i').hom.op.toLoc ≫
        hc.fiberPseudofunctor.map (𝒰.pr1 i i').op.toLoc :=
  hc.fiberPseudofunctor.mapComp'
    (𝒰.obj i').hom.op.toLoc
    (𝒰.pr1 i i').op.toLoc
    ((𝒰.pairwisePullback i i').p).op.toLoc
    (family_descent_functor_obj_pr1_map_toLoc (𝒰 := 𝒰) i i')

/-- Helper for Lemma 8.3.6: the overlap morphism of the canonical descent datum of `X` is the
owner-side `DescentData.ofObj` transition on the chosen overlap. -/
private theorem family_descent_functor_obj_hom_shell
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).obj X).hom i i' =
      ((familyDescentFunctor_obj_pr0Comparison (hc := hc) (𝒰 := 𝒰) i i').inv.toNatTrans.app X) ≫
        ((familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i').hom.toNatTrans.app X) := by
  rfl

/-- Helper for Lemma 8.3.6: the strict right-leg composition comparison evaluates to the Chapter
4 pullback-composition comparison in the fiber. -/
private theorem fiberPseudofunctor_mapComp_hom_app_eq_pullbackCompComponentIso_hom
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (X : p.Fiber U) :
    ((hc.fiberPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app X) =
      (hc.pullbackCompComponentIso f g X).hom := by
  -- The strict comparison is the `rfl` instance of the flexible `mapComp'` comparison.
  simpa [Pseudofunctor.mapComp'_eq_mapComp] using
    (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom (hc := hc)
      (f := f) (g := g) X)

/-- Helper for Lemma 8.3.6: the right overlap comparison splits into the equality transport from
the chosen overlap map to the strict composite, followed by the strict composition comparison. -/
private theorem family_descent_functor_obj_pr1Comparison_eq_map₂Iso_comp_mapComp
    (i i' : 𝒰.index) :
    familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i' =
      hc.fiberPseudofunctor.map₂Iso
          (eqToIso (by
            simpa using (family_descent_functor_obj_pr1_map_toLoc
              (𝒰 := 𝒰) i i').symm)) ≪≫
        hc.fiberPseudofunctor.mapComp (𝒰.obj i').hom.op.toLoc (𝒰.pr1 i i').op.toLoc := by
  -- This is the defining expansion of `mapComp'` specialized to the chosen overlap map.
  simp [familyDescentFunctor_obj_pr1Comparison, Pseudofunctor.mapComp']

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the left comparison for the chosen overlap is the Chapter 4
pullback-composition comparison followed by the transport from `pr₀ ≫ f_i` to the chosen overlap
map. -/
private theorem family_descent_functor_obj_pr0Comparison_inv_normalize
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor_obj_pr0Comparison (hc := hc) (𝒰 := 𝒰) i i').inv.toNatTrans.app X) =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
        eqToHom (family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
  -- Unfold the packaged left comparison and expose the transport from `(pr₀ ≫ f_i)^* X` to the
  -- chosen overlap pullback `pᵢᵢ'^* X`.
  simpa [familyDescentFunctor_obj_pr0Comparison,
    family_descent_functor_obj_pr0_map_toLoc, family_descent_functor_obj_pr0_transport] using
    (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv (hc := hc)
      (f := (𝒰.obj i).hom) (g := 𝒰.pr0 i i') X)

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the right comparison for the chosen overlap is the transport from the
chosen overlap map to `pr₁ ≫ f_j`, followed by the Chapter 4 pullback-composition comparison. -/
private theorem family_descent_functor_obj_pr1Comparison_hom_normalize
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor_obj_pr1Comparison (hc := hc) (𝒰 := 𝒰) i i').hom.toNatTrans.app X) =
      eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') ≫
        (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
  let transportIso :
      hc.fiberPseudofunctor.map ((𝒰.pairwisePullback i i').p).op.toLoc ≅
        hc.fiberPseudofunctor.map
          ((𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc) :=
    hc.fiberPseudofunctor.map₂Iso
      (eqToIso (show ((𝒰.pairwisePullback i i').p).op.toLoc =
          (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc from by
        simpa using (family_descent_functor_obj_pr1_map_toLoc
          (𝒰 := 𝒰) i i').symm))
  have htransport :
      transportIso.hom.toNatTrans.app X =
        eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') := by
    -- The equality-2-morphism component is exactly the transport between the two pullback objects.
    dsimp [transportIso]
    let hfg :
        ((𝒰.pairwisePullback i i').p).op.toLoc =
          (𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc := by
      simpa using (family_descent_functor_obj_pr1_map_toLoc (𝒰 := 𝒰) i i').symm
    have hmap :
        hc.fiberPseudofunctor.toPrelaxFunctor.map₂ (eqToHom hfg) =
          eqToHom (by rw [← hfg]) := by
      simpa using
        (PrelaxFunctor.map₂_eqToHom (F := hc.fiberPseudofunctor.toPrelaxFunctor)
          ((𝒰.pairwisePullback i i').p).op.toLoc
          ((𝒰.obj i').hom.op.toLoc ≫ (𝒰.pr1 i i').op.toLoc) hfg)
    simpa [hfg, PullbackChoice.fiberPseudofunctor, family_descent_functor_obj_pr1_transport] using
      congrArg (fun α ↦ α.toNatTrans.app X) hmap
  -- Route correction: unfold the actual flexible `mapComp'` shell here so the owner-side cast
  -- from the chosen overlap map to `(pr₁ ≫ f_j)` is exposed explicitly before normalization.
  rw [family_descent_functor_obj_pr1Comparison_eq_map₂Iso_comp_mapComp
    (hc := hc) (𝒰 := 𝒰) i i']
  -- After exposing the transport shell, evaluate the `map₂Iso` factor and the strict `mapComp`
  -- factor separately.
  change transportIso.hom.toNatTrans.app X ≫
      (hc.fiberPseudofunctor.mapComp (𝒰.obj i').hom.op.toLoc
        (𝒰.pr1 i i').op.toLoc).hom.toNatTrans.app X =
    eqToHom (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i') ≫
      (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom
  rw [htransport]
  rw [fiberPseudofunctor_mapComp_hom_app_eq_pullbackCompComponentIso_hom]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 8.3.6: the owner-side overlap isomorphism of the canonical descent datum has
the textbook underlying morphism. -/
private theorem family_descent_functor_obj_iso_hom
    (X : p.Fiber U) (i i' : 𝒰.index) :
    (((familyDescentFunctor hc 𝒰).obj X).iso i i').hom =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
        eqToHom (family_descent_functor_obj_overlap_transport
          (hc := hc) (𝒰 := 𝒰) X i i') ≫
        (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
  -- First rewrite the descent datum morphism to the common overlap shell.
  calc
    (((familyDescentFunctor hc 𝒰).obj X).iso i i').hom
      =
        (((hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
            eqToHom (family_descent_functor_obj_pr0_transport
              (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (eqToHom (family_descent_functor_obj_pr1_transport
              (hc := hc) (𝒰 := 𝒰) X i i') ≫
            (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom)) := by
          -- The two adapter lemmas identify the packaged `mapComp'` terms with the textbook
          -- pullback-composition comparisons on the left and right overlap legs.
          rw [DescentDatum.iso_hom, family_descent_functor_obj_hom_shell,
            family_descent_functor_obj_pr0Comparison_inv_normalize,
            family_descent_functor_obj_pr1Comparison_hom_normalize]
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          (eqToHom (family_descent_functor_obj_pr0_transport
              (hc := hc) (𝒰 := 𝒰) X i i') ≫
            eqToHom (family_descent_functor_obj_pr1_transport
              (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- Reassociate so the two transport morphisms become adjacent.
          simp
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          eqToHom
            ((family_descent_functor_obj_pr0_transport (hc := hc) (𝒰 := 𝒰) X i i').trans
              (family_descent_functor_obj_pr1_transport (hc := hc) (𝒰 := 𝒰) X i i')) ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- The two transports compose to the transport from `pr₀ ≫ f_i` to `pr₁ ≫ f_j`.
          rw [eqToHom_trans]
    _ =
        (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).inv ≫
          eqToHom (family_descent_functor_obj_overlap_transport
            (hc := hc) (𝒰 := 𝒰) X i i') ≫
          (hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X).hom := by
          -- Replace the composite transport through the chosen overlap by the direct overlap
          -- transport.
          rw [family_descent_functor_obj_overlap_transport_eq]

/-- Lemma 8.3.6: for the canonical descent datum attached to a global object `X`, the overlap
isomorphism on `U_i ×[U] U_j` is the composite of the inverse component of the
pullback-composition comparison, the transport along `pr₀ ≫ f_i = pr₁ ≫ f_j`, and the forward
component of the pullback-composition comparison. -/
theorem familyDescentFunctor_obj_iso
    (X : p.Fiber U) (i i' : 𝒰.index) :
    ((familyDescentFunctor hc 𝒰).obj X).iso i i' =
      (hc.pullbackCompComponentIso (𝒰.obj i).hom (𝒰.pr0 i i') X).symm ≪≫
        eqToIso (family_descent_functor_obj_overlap_transport (hc := hc) (𝒰 := 𝒰) X i i') ≪≫
        hc.pullbackCompComponentIso (𝒰.obj i').hom (𝒰.pr1 i i') X := by
  apply Iso.ext
  exact family_descent_functor_obj_iso_hom (hc := hc) (𝒰 := 𝒰) X i i'

end CategoryTheory
