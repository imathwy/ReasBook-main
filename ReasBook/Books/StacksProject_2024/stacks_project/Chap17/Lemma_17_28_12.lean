import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_21_6
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace TopCat.Sheaf AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X X' S S' : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.12:
- primary domain: base change for relative differentials in a commutative square of ringed spaces;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.d[_]`,
  `TopCat.Sheaf.relativeDifferentialDesc`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction:
  the Chapter 17 universal-differentials owner `TopCat.Sheaf.relativeDifferentialDesc`,
  specialized along the ringed-space inverse-image structure-sheaf morphism
  `inverseImageStructureSheafHomComm h` and then transposed across the pullback-pushforward
  adjunction for `toRingCatSheafHom f`;
- primitive data:
  only the four morphisms `f`, `g`, `h`, `h'` and the commutative square `CommSq f h' h g`;
- derived API:
  the ringed-space comparison map `pullbackDifferentialsComparison` and its sectionwise
  characterization/uniqueness.

Source/core/bridge triage:
- `source-facing`: the ringed-space map `c_f : f^* Ω[h] ⟶ Ω[h']`;
- `core/canonical`: `TopCat.Sheaf.relativeDifferentialDesc` and
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- `bridge/view`: the ringed-space pullback-pushforward adjunction for `toRingCatSheafHom f`.

The public ringed-space API should therefore expose only the comparison morphism and its
intrinsic sectionwise characterization, while keeping the pushed-forward derivation internal to the
construction. -/

variable (f : X' ⟶ X) (g : S' ⟶ S) (h : X ⟶ S) (h' : X' ⟶ S')

private abbrev pushedForwardDifferentialsSection
    (U : (Opens X)ᵒᵖ) : ModuleCat (X.presheaf.obj U) :=
  let U' := (Opens.map f.hom.base).op.obj U
  (ModuleCat.restrictScalars ((toRingCatSheafHom f).hom.app U).hom).obj (Ω[h'].val.obj U')

/-- Helper for Lemma 17.28.12: over each open of `X`, the pushed-forward cotangent section is
canonically a module over the pushed-forward structure-sheaf section ring. -/
private instance pushedForwardDifferentialsSection_sourceModule
    (U : (Opens X)ᵒᵖ) :
    Module (((TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj X'.ringCatSheaf).obj.obj U)
      ↑(Ω[h'].val.obj ((Opens.map f.hom.base).op.obj U)) := by
  change Module (X'.presheaf.obj ((Opens.map f.hom.base).op.obj U))
    ↑(Ω[h'].val.obj ((Opens.map f.hom.base).op.obj U))
  infer_instance

/-- Helper for Lemma 17.28.12: the commutative square identifies the underlying continuous maps
of the composites `f ≫ h` and `h' ≫ g`. -/
private theorem pullbackDifferentialsComparison_base_eq
    (sq : CommSq f h' h g) :
    f.hom.base ≫ h.hom.base = h'.hom.base ≫ g.hom.base := by
  simpa using congrArg (fun k ↦ k.hom.base) sq.w

/-- Helper for Lemma 17.28.12: transporting an adjunction across a right natural isomorphism
acts on transposes by postcomposition with that comparison map. -/
private theorem ofNatIsoRight_homEquiv_apply {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) {Z : C} {W : D}
    (g : F.obj Z ⟶ W) :
    ((adj.ofNatIsoRight iso).homEquiv Z W) g =
      adj.homEquiv Z W g ≫ iso.hom.app W := by
  -- Proof comment: unfold the transported adjunction so the right-side comparison becomes
  -- explicit on the transpose.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoRight, Category.assoc]

/-- Helper for Lemma 17.28.12: under the composite pullback-pushforward adjunction, inserting the
canonical `pullbackComp` comparison has identity mate on the pushforward side. -/
private theorem pullbackComp_hom_homEquiv
    {Y Z W : RingedSpace.{u}} (p : Y ⟶ Z) (q : Z ⟶ W)
    (m : ((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} q.hom.base).obj W.sheaf)) ⟶ Y.sheaf) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (p.hom.base ≫ q.hom.base)).homEquiv _ _)
      (((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) p.hom.base q.hom.base).inv.app
          W.sheaf) ≫
        m) =
      ((CategoryTheory.Adjunction.comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base)
          (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base)).homEquiv
        _ _) m := by
  -- Route correction: replace brittle unfolding of `pullbackComp` by the owner-level
  -- `leftAdjointCompIso` mate computation and keep the right-side comparison explicit.
  let adjpq :=
    TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (p.hom.base ≫ q.hom.base)
  let adjq :=
    TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base
  let adjp :=
    TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base
  let compAdj := CategoryTheory.Adjunction.comp adjq adjp
  let pushIter :=
    (TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base) ⋙
      (TopCat.Sheaf.pushforward CommRingCat.{u} q.hom.base)
  let α := (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) p.hom.base q.hom.base).inv
  let β : pushIter ⟶ TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base) :=
    (eqToIso
      (show TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base) =
          (TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base) ⋙
            (TopCat.Sheaf.pushforward CommRingCat.{u} q.hom.base) from rfl).symm).hom
  have hβ :
      CategoryTheory.conjugateEquiv compAdj adjpq α = β := by
    dsimp [compAdj, adjq, adjp, adjpq, α, β]
    exact CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base)
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base)
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (p.hom.base ≫ q.hom.base))
      (eqToIso
        (show TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base) =
            (TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base) ⋙
              (TopCat.Sheaf.pushforward CommRingCat.{u} q.hom.base) from rfl).symm)
  have hβunit :
      compAdj.unit.app W.sheaf ≫
          β.app
            ((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).obj
              ((TopCat.Sheaf.pullback CommRingCat.{u} q.hom.base).obj W.sheaf)) =
        adjpq.unit.app W.sheaf ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map
            (α.app W.sheaf) := by
    have hβunit' := CategoryTheory.unit_conjugateEquiv compAdj adjpq α W.sheaf
    rw [hβ] at hβunit'
    exact hβunit'
  have hmate :
      (adjpq.homEquiv W.sheaf Y.sheaf) (α.app W.sheaf ≫ m) =
        (compAdj.homEquiv W.sheaf Y.sheaf) m ≫ β.app Y.sheaf := by
    have h1 :
        (adjpq.homEquiv W.sheaf Y.sheaf) (α.app W.sheaf ≫ m) =
          adjpq.unit.app W.sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map
              (α.app W.sheaf ≫ m) := by
      exact CategoryTheory.Adjunction.homEquiv_unit
        (adj := adjpq) (f := α.app W.sheaf ≫ m)
    have h2 :
        adjpq.unit.app W.sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map
              (α.app W.sheaf ≫ m) =
          adjpq.unit.app W.sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map
              (α.app W.sheaf) ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map m := by
      simpa [Functor.map_comp, Category.assoc]
    have h3 :
        adjpq.unit.app W.sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map
              (α.app W.sheaf) ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map m =
          compAdj.unit.app W.sheaf ≫
            β.app
              ((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).obj
                ((TopCat.Sheaf.pullback CommRingCat.{u} q.hom.base).obj W.sheaf)) ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map m := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map m)
          hβunit.symm
    have h4 :
        compAdj.unit.app W.sheaf ≫
            β.app
              ((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).obj
                ((TopCat.Sheaf.pullback CommRingCat.{u} q.hom.base).obj W.sheaf)) ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} (p.hom.base ≫ q.hom.base)).map m =
          compAdj.unit.app W.sheaf ≫ pushIter.map m ≫ β.app Y.sheaf := by
      simpa [pushIter, Category.assoc] using
        congrArg (fun k ↦ compAdj.unit.app W.sheaf ≫ k) (β.naturality m).symm
    have h5 :
        compAdj.unit.app W.sheaf ≫ pushIter.map m ≫ β.app Y.sheaf =
          (compAdj.homEquiv W.sheaf Y.sheaf) m ≫ β.app Y.sheaf := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ β.app Y.sheaf)
          (CategoryTheory.Adjunction.homEquiv_unit (adj := compAdj) (f := m)).symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hβid : β.app Y.sheaf = 𝟙 _ := by
    rfl
  simpa [α, hβid] using hmate

/-- Helper for Lemma 17.28.12: the adjoint structure-sheaf morphism is compatible with
composition once the pullback along a composite is identified with the iterated pullback. -/
private theorem inverseImageStructureSheafHomComm_comp
    {Y Z W : RingedSpace.{u}} (p : Y ⟶ Z) (q : Z ⟶ W) :
    ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) p.hom.base q.hom.base).inv.app W.sheaf) ≫
      ((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).map
        (inverseImageStructureSheafHomComm q)) ≫
      inverseImageStructureSheafHomComm p =
    inverseImageStructureSheafHomComm (p ≫ q) := by
  -- Proof comment: compare both inverse-image composites after transposing to the pushforward
  -- side of the adjunction for the composite base map.
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (p.hom.base ≫ q.hom.base)).homEquiv _ _).injective
  -- Proof comment: the `pullbackComp` bridge turns the left transpose into the composite
  -- adjunction transpose, and then both sides simplify to the same pushforward map.
  rw [pullbackComp_hom_homEquiv]
  rw [CategoryTheory.Adjunction.comp_homEquiv]
  change
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base).homEquiv
          W.sheaf
          ((TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base).obj Y.sheaf))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).homEquiv
            ((TopCat.Sheaf.pullback CommRingCat.{u} q.hom.base).obj W.sheaf) Y.sheaf)
          (((TopCat.Sheaf.pullback CommRingCat.{u} p.hom.base).map
              (inverseImageStructureSheafHomComm q)) ≫
            inverseImageStructureSheafHomComm p)) =
    _
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base)
    (inverseImageStructureSheafHomComm q)
    (inverseImageStructureSheafHomComm p)]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base)
    (inverseImageStructureSheafHomComm q)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).homEquiv _ _)
      (inverseImageStructureSheafHomComm p))]
  let adjpq :=
    TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (p.hom.base ≫ q.hom.base)
  have hleft :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.hom.base).homEquiv
          (SheafedSpace.sheaf W) (SheafedSpace.sheaf Z))
        (inverseImageStructureSheafHomComm q) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} q.hom.base).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).homEquiv
              (SheafedSpace.sheaf Z) (SheafedSpace.sheaf Y))
            (inverseImageStructureSheafHomComm p)) =
        commRingSheafPushforwardMap (p ≫ q) := by
    apply ObjectProperty.hom_ext
    ext U x
    rfl
  have hright :
      (adjpq.homEquiv (SheafedSpace.sheaf W) (SheafedSpace.sheaf Y))
          (inverseImageStructureSheafHomComm (p ≫ q)) =
        commRingSheafPushforwardMap (p ≫ q) := by
    change
        (adjpq.homEquiv (SheafedSpace.sheaf W) (SheafedSpace.sheaf Y))
            ((adjpq.homEquiv (SheafedSpace.sheaf W) (SheafedSpace.sheaf Y)).symm
              (commRingSheafPushforwardMap (p ≫ q))) =
          commRingSheafPushforwardMap (p ≫ q)
    exact (adjpq.homEquiv (SheafedSpace.sheaf W) (SheafedSpace.sheaf Y)).apply_symm_apply
      (commRingSheafPushforwardMap (p ≫ q))
  exact hleft.trans hright.symm

/-- Helper for Lemma 17.28.12: after transporting both inverse-image composites to the common
source over `X'`, the commutative square identifies them. -/
private theorem pullbackDifferentialsComparison_inverseImage_eq
    (sq : CommSq f h' h g) :
    ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).inv.app
        S.sheaf) ≫
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
        (inverseImageStructureSheafHomComm h)) ≫
      inverseImageStructureSheafHomComm f =
    (eqToIso
        (congrArg
          (fun k ↦ (TopCat.Sheaf.pullback CommRingCat.{u} k).obj S.sheaf)
          (pullbackDifferentialsComparison_base_eq f g h h' sq))).hom ≫
      ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) h'.hom.base g.hom.base).inv.app
        S.sheaf) ≫
      ((TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).map
        (inverseImageStructureSheafHomComm g)) ≫
      inverseImageStructureSheafHomComm h' := by
  -- Proof comment: both composites are the inverse-image structure-sheaf map for the common base
  -- morphism; after rewriting to that owner map, only the explicit transport from `sq.w`
  -- remains.
  rw [inverseImageStructureSheafHomComm_comp (p := f) (q := h)]
  rw [inverseImageStructureSheafHomComm_comp (p := h') (q := g)]
  -- Route correction: make the source transport explicit and then collapse it by eliminating the
  -- square witness.
  apply ObjectProperty.hom_ext
  rcases sq with ⟨w⟩
  cases w
  ext U x
  rfl

/-- Helper for Lemma 17.28.12: the structure-sheaf map on sections factors through the
pullback-pushforward adjunction unit and the inverse-image structure-sheaf morphism. -/
private theorem toRingCatSheafHom_app_eq_inverseImageStructureSheafHomComm_app
    {Y Z : RingedSpace.{u}} (p : Y ⟶ Z) {U : (TopologicalSpace.Opens Z)ᵒᵖ}
    (t : Z.presheaf.obj U) :
    ((toRingCatSheafHom p).hom.app U) t =
      ((inverseImageStructureSheafHomComm p).hom.app
        ((TopologicalSpace.Opens.map p.hom.base).op.obj U))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).unit.app
            Z.sheaf).hom.app U) t) := by
  -- Proof comment: first rewrite the commutative-ring-valued structure-sheaf map by the
  -- adjunction unit formula, then forget to `RingCat`.
  have happ :
      ((commRingSheafPushforwardMap p).hom.app U) t =
        ((inverseImageStructureSheafHomComm p).hom.app
          ((TopologicalSpace.Opens.map p.hom.base).op.obj U))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).unit.app
              Z.sheaf).hom.app U) t) := by
    have happ' :
        ((commRingSheafPushforwardMap p).hom.app U) =
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base).unit.app
                Z.sheaf) ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base).map
                (inverseImageStructureSheafHomComm p)).hom.app U) := by
      simpa [inverseImageStructureSheafHomComm] using
        congrArg
          (fun k : (SheafedSpace.sheaf Z ⟶
              (TopCat.Sheaf.pushforward CommRingCat.{u} p.hom.base).obj (SheafedSpace.sheaf Y)) ↦
            k.hom.app U)
          (CategoryTheory.Adjunction.homEquiv_unit
            (adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.hom.base)
            (f := inverseImageStructureSheafHomComm p))
    exact congrArg (fun m ↦ m t) happ'
  simpa [toRingCatSheafHom, commRingSheafPushforwardMap] using happ

/-- Helper for Lemma 17.28.12: a base section over `U` transports canonically across the square
to a section of `h'⁻¹ 𝒪_{S'}` over `f^{-1}(U)`. -/
private noncomputable abbrev pullbackDifferentialsComparisonBaseSectionMap
    (sq : CommSq f h' h g) (U : (Opens X)ᵒᵖ) :
    ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf).obj.obj U ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).obj S'.sheaf).obj.obj
        ((Opens.map f.hom.base).op.obj U) :=
  let U' := (Opens.map f.hom.base).op.obj U
  let η :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf)).hom.app U)
  let e₁ :=
    ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).hom.app S.sheaf).hom.app
      U'
  let e₂ :=
    (eqToIso
      (congrArg
        (fun k ↦ (TopCat.Sheaf.pullback CommRingCat.{u} k).obj S.sheaf)
        (pullbackDifferentialsComparison_base_eq f g h h' sq))).hom.1.app U'
  let e₃ :=
    ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) h'.hom.base g.hom.base).inv.app S.sheaf).hom.app
      U'
  let e₄ :=
    ((TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).map
      (inverseImageStructureSheafHomComm g)).hom.app U'
  η ≫ e₁ ≫ e₂ ≫ e₃ ≫ e₄

/-- Helper for Lemma 17.28.12: after transporting a base section across the square, applying
`h'^\sharp` agrees sectionwise with first applying `h^\sharp` and then `f^\sharp`. -/
private theorem pullbackDifferentialsComparison_square_app
    (sq : CommSq f h' h g) {U : (Opens X)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf).obj.obj U) :
    let U' := (Opens.map f.hom.base).op.obj U
    ((toRingCatSheafHom f).hom.app U)
        (((inverseImageStructureSheafHomComm h).hom.app U) a) =
      ((inverseImageStructureSheafHomComm h').hom.app U')
        (pullbackDifferentialsComparisonBaseSectionMap f g h h' sq U a) := by
  let U' := (Opens.map f.hom.base).op.obj U
  let η :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf)).hom.app U) a
  -- Proof comment: rewrite `f^\sharp` through the adjunction unit so the left-hand side is
  -- expressed on the same iterated-pullback source as the base-section transport.
  rw [toRingCatSheafHom_app_eq_inverseImageStructureSheafHomComm_app (p := f)
    (((inverseImageStructureSheafHomComm h).hom.app U) a)]
  have hunit :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf)) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
            (inverseImageStructureSheafHomComm h)) =
      inverseImageStructureSheafHomComm h ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
          X.sheaf) := by
    -- Proof comment: this is unit naturality for the morphism `h^\sharp`.
    simpa [Functor.map_comp, Category.assoc] using
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.naturality
        (inverseImageStructureSheafHomComm h)).symm
  have hunit_app :
      (((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
            (inverseImageStructureSheafHomComm h))).hom.app U) η =
        (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
            X.sheaf).hom.app U)
          (((inverseImageStructureSheafHomComm h).hom.app U) a) := by
    exact congrArg (fun k ↦ k a) (congrArg (fun k ↦ k.hom.app U) hunit)
  rw [← hunit_app]
  have hcomp :
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
          (inverseImageStructureSheafHomComm h)) ≫
        inverseImageStructureSheafHomComm f =
      ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).hom.app
          S.sheaf) ≫
        (eqToIso
            (congrArg
              (fun k ↦ (TopCat.Sheaf.pullback CommRingCat.{u} k).obj S.sheaf)
              (pullbackDifferentialsComparison_base_eq f g h h' sq))).hom ≫
        ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) h'.hom.base g.hom.base).inv.app
          S.sheaf) ≫
        ((TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).map
          (inverseImageStructureSheafHomComm g)) ≫
        inverseImageStructureSheafHomComm h' := by
    -- Proof comment: move the common-source equality from the composite pullback back to the
    -- iterated pullback source by composing with the inverse `pullbackComp` comparison.
    calc
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
            (inverseImageStructureSheafHomComm h)) ≫
          inverseImageStructureSheafHomComm f =
        ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).hom.app
            S.sheaf) ≫
          ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).inv.app
            S.sheaf) ≫
          ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
            (inverseImageStructureSheafHomComm h)) ≫
          inverseImageStructureSheafHomComm f := by
            simpa [Category.assoc] using
              (congrArg
                (fun k ↦
                  k ≫
                    (((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
                        (inverseImageStructureSheafHomComm h)) ≫
                      inverseImageStructureSheafHomComm f))
                (Iso.hom_inv_id_app
                  (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base)
                  S.sheaf)).symm
      _ =
        ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base h.hom.base).hom.app
            S.sheaf) ≫
          (eqToIso
              (congrArg
                (fun k ↦ (TopCat.Sheaf.pullback CommRingCat.{u} k).obj S.sheaf)
                (pullbackDifferentialsComparison_base_eq f g h h' sq))).hom ≫
          ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) h'.hom.base g.hom.base).inv.app
            S.sheaf) ≫
          ((TopCat.Sheaf.pullback CommRingCat.{u} h'.hom.base).map
            (inverseImageStructureSheafHomComm g)) ≫
          inverseImageStructureSheafHomComm h' := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ ((TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base
                  h.hom.base).hom.app S.sheaf) ≫ k)
                (pullbackDifferentialsComparison_inverseImage_eq f g h h' sq)
  have hcomp_app := congrArg (fun k ↦ k η) (congrArg (fun k ↦ k.hom.app U') hcomp)
  -- Proof comment: evaluating the common-source equality at the transported base section gives
  -- exactly the sectionwise square formula.
  change
      (ConcreteCategory.hom
          ((((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
                (inverseImageStructureSheafHomComm h)) ≫
              inverseImageStructureSheafHomComm f).hom.app U')) η =
        (ConcreteCategory.hom ((inverseImageStructureSheafHomComm h').hom.app U'))
          (pullbackDifferentialsComparisonBaseSectionMap f g h h' sq U a)
  simpa [U', η, pullbackDifferentialsComparisonBaseSectionMap, Category.assoc] using hcomp_app

private theorem pullbackDifferentialsComparisonDerivationApp_d_map
    (sq : CommSq f h' h g) {U : (Opens X)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf).obj.obj U) :
    ((d[h']).app ((Opens.map f.hom.base).op.obj U)).d
        ((toRingCatSheafHom f).hom.app U
          ((inverseImageStructureSheafHomComm h).hom.app U a)) = 0 := by
  let U' := (Opens.map f.hom.base).op.obj U
  -- Rewrite the section so that `d[h']` sees an element coming from the base ring.
  rw [pullbackDifferentialsComparison_square_app f g h h' sq a]
  simpa [U'] using
    ((d[h']).app U').d_map
      (pullbackDifferentialsComparisonBaseSectionMap f g h h' sq U a)

private noncomputable abbrev pullbackDifferentialsComparisonDerivationApp
    (sq : CommSq f h' h g) (U : (Opens X)ᵒᵖ) :
    (pushedForwardDifferentialsSection f h' U).Derivation
      ((inverseImageStructureSheafHomComm h).hom.app U) :=
  let U' := (Opens.map f.hom.base).op.obj U
  let fSharpU := (toRingCatSheafHom f).hom.app U
  let _ : Module (X.presheaf.obj U) (Ω[h'].val.obj U') :=
    Module.compHom (Ω[h'].val.obj U') (fSharpU.hom)
  ModuleCat.Derivation.mk
    (fun t ↦
      show pushedForwardDifferentialsSection f h' U from
        ((d[h']).app U').d (fSharpU t))
    (by
      -- Additivity is inherited sectionwise from the universal derivation on `X'`.
      intro t₁ t₂
      change ((d[h']).app U').d (fSharpU (t₁ + t₂)) =
        ((d[h']).app U').d (fSharpU t₁) + ((d[h']).app U').d (fSharpU t₂)
      rw [show (ConcreteCategory.hom fSharpU) (t₁ + t₂) =
          (ConcreteCategory.hom fSharpU) t₁ + (ConcreteCategory.hom fSharpU) t₂ by
          exact fSharpU.hom.map_add t₁ t₂]
      simpa using ((d[h']).app U').d_add (fSharpU t₁) (fSharpU t₂))
    (by
      -- The Leibniz rule is the one for `d[h']`, viewed through restricted scalars.
      intro t₁ t₂
      change ((d[h']).app U').d (fSharpU (t₁ * t₂)) =
        t₁ • ((d[h']).app U').d (fSharpU t₂) + t₂ • ((d[h']).app U').d (fSharpU t₁)
      rw [show (ConcreteCategory.hom fSharpU) (t₁ * t₂) =
          (ConcreteCategory.hom fSharpU) t₁ * (ConcreteCategory.hom fSharpU) t₂ by
          exact fSharpU.hom.map_mul t₁ t₂]
      simpa using ((d[h']).app U').d_mul (fSharpU t₁) (fSharpU t₂))
    (by
      -- Use the sectionwise square identity to rewrite the argument into the image of the base
      -- map for `h'`.
      intro a
      exact pullbackDifferentialsComparisonDerivationApp_d_map f g h h' sq a)

private theorem pullbackDifferentialsComparisonDerivationApp_naturality
    (sq : CommSq f h' h g) {U V : (Opens X)ᵒᵖ} (ρ : U ⟶ V) (t : X.presheaf.obj U) :
    (pullbackDifferentialsComparisonDerivationApp f g h h' sq V).d (X.presheaf.map ρ t) =
      (((f _*).obj Ω[h']).val.map ρ)
        ((pullbackDifferentialsComparisonDerivationApp f g h h' sq U).d t) := by
  let U' := (Opens.map f.hom.base).op.obj U
  let V' := (Opens.map f.hom.base).op.obj V
  let fSharpU := (toRingCatSheafHom f).hom.app U
  let fSharpV := (toRingCatSheafHom f).hom.app V
  have hf :
      fSharpV (X.presheaf.map ρ t) =
        X'.presheaf.map ((Opens.map f.hom.base).op.map ρ) (fSharpU t) := by
    exact congrArg (fun k ↦ k t) <|
      congrArg RingCat.Hom.hom ((toRingCatSheafHom f).hom.naturality ρ)
  -- Rewrite the input by naturality of `f^\sharp`, then apply naturality of `d[h']`.
  change ((d[h']).app V').d (fSharpV (X.presheaf.map ρ t)) =
    (ConcreteCategory.hom (((f _*).obj Ω[h']).val.map ρ))
      ((pullbackDifferentialsComparisonDerivationApp f g h h' sq U).d t)
  rw [hf]
  simpa [U', V'] using (d[h']).d_map ((Opens.map f.hom.base).op.map ρ) (fSharpU t)

private noncomputable def pullbackDifferentialsComparisonDerivation
    (sq : CommSq f h' h g) :
    Der[inverseImageStructureSheafHomComm h ; (f _*).obj Ω[h']] :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ pullbackDifferentialsComparisonDerivationApp f g h h' sq U)
    (fun _ _ ρ t ↦
      pullbackDifferentialsComparisonDerivationApp_naturality f g h h' sq ρ t)

private noncomputable abbrev pullbackDifferentialsComparisonAdjoint
    (sq : CommSq f h' h g) :
    Ω[h] ⟶ (f _*).obj Ω[h'] :=
  TopCat.Sheaf.relativeDifferentialDesc (inverseImageStructureSheafHomComm h)
    (pullbackDifferentialsComparisonDerivation f g h h' sq)

-- Proof sketch: the commutative square identifies the composite
-- `\mathcal O_X \xrightarrow{f^\sharp} f_* \mathcal O_{X'} \xrightarrow{f_* d[h']}
-- f_* \Omega[h']` as an `S`-derivation on `\mathcal O_X`. Descend this derivation through the
-- universal property of `Ω[h]`, then transpose the resulting map `Ω[h] ⟶ f_* Ω[h']` across the
-- pullback-pushforward adjunction for `f`.
/-- The canonical base-change map on relative differentials associated to a commutative square of
ringed spaces. -/
noncomputable def pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    (f^*).obj Ω[h] ⟶ Ω[h'] :=
  ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv _ _).symm
    (pullbackDifferentialsComparisonAdjoint f g h h' sq)

/-- The source-facing sectionwise characterization property for the base-change morphism on
relative differentials. -/
def pullbackDifferentialsComparisonProperty
    (τ : (f^*).obj Ω[h] ⟶ Ω[h']) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    let U' := (Opens.map f.hom.base).op.obj U
    let fSharpU := (toRingCatSheafHom f).hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
          (toRingCatSheafHom f)).homEquiv _ _)
        τ).val.app U)
      (((d[h]).app U).d t) =
      ((d[h']).app U').d (fSharpU t)

-- Proof sketch: specialize the Chapter 18 characterization theorem along the opens-site bridge
-- and transport source/target through the equalities above.
/-- The canonical comparison morphism is characterized by sending `d_{X/S}(t)` to
`d_{X'/S'}(f^\sharp t)` after passage to the adjoint map `Ω_{X/S} → f_* Ω_{X'/S'}`. -/
theorem pullbackDifferentialsComparison_characterizing
    (sq : CommSq f h' h g) :
    pullbackDifferentialsComparisonProperty f h h'
      (pullbackDifferentialsComparison f g h h' sq) := by
  intro U t
  dsimp
  -- After applying adjunction, the comparison map is exactly the descended pushed-forward
  -- derivation.
  rw [show
      ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv _ _)
          (pullbackDifferentialsComparison f g h h' sq) =
        pullbackDifferentialsComparisonAdjoint f g h h' sq by
      simp [pullbackDifferentialsComparison]]
  -- The universal property of `Ω[h]` identifies the adjoint on generators with the defining
  -- derivation.
  calc
    (pullbackDifferentialsComparisonAdjoint f g h h' sq).val.app U
        (((d[h]).app U).d t) =
      (pullbackDifferentialsComparisonDerivation f g h h' sq).d t := by
        simpa [pullbackDifferentialsComparisonAdjoint] using
          congrArg (fun D ↦ D.d (X := U) t)
            (TopCat.Sheaf.relativeDifferentialDesc_fac (inverseImageStructureSheafHomComm h)
              (pullbackDifferentialsComparisonDerivation f g h h' sq))
    _ = ((d[h']).app ((Opens.map f.hom.base).op.obj U)).d
          ((toRingCatSheafHom f).hom.app U t) := by
        rfl

-- Proof sketch: transport the Chapter 18 uniqueness theorem along the same opens-site bridge.
/-- A morphism `f^* \Omega_{X/S} \to \Omega_{X'/S'}` is the canonical comparison morphism once its
adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on local sections. -/
theorem pullbackDifferentialsComparison_unique
    (sq : CommSq f h' h g)
    (τ : (f^*).obj Ω[h] ⟶ Ω[h'])
    (hτ : pullbackDifferentialsComparisonProperty f h h' τ) :
    τ = pullbackDifferentialsComparison f g h h' sq := by
  let adj :=
    ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)).homEquiv
      Ω[h] Ω[h'])
  -- Compare adjoints under the pullback-pushforward adjunction and then use that `Ω[h]` is
  -- generated by the universal derivation.
  apply adj.injective
  apply TopCat.Sheaf.relativeDifferential_postcomp_injective (inverseImageStructureSheafHomComm h)
  ext U t
  change ((((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _) τ).val.app U)
      (((d[h]).app U).d t) =
    ((((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom f)).homEquiv _ _)
        (pullbackDifferentialsComparison f g h h' sq)).val.app U)
      (((d[h]).app U).d t)
  exact Eq.trans (hτ (U := U) t)
    ((pullbackDifferentialsComparison_characterizing f g h h' sq (U := U) t).symm)

-- Proof sketch: existence is witnessed by the canonical specialized owner morphism above, and
-- uniqueness is the preceding theorem.
/-- Lemma 17.28.12: for a commutative square of ringed spaces
`X' \xrightarrow{f} X`, `S' \xrightarrow{g} S`, there exists a unique
`\mathcal O_{X'}`-module morphism
`c_f : f^* \Omega_{X/S} \to \Omega_{X'/S'}`
whose adjoint sends `d_{X/S}(t)` to `d_{X'/S'}(f^\sharp t)` on every local section `t` of
`\mathcal O_X`. -/
theorem existsUnique_pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    ∃! τ : (f^*).obj Ω[h] ⟶ Ω[h'],
      pullbackDifferentialsComparisonProperty f h h' τ := by
  refine ⟨pullbackDifferentialsComparison f g h h' sq, ?_, ?_⟩
  · exact pullbackDifferentialsComparison_characterizing f g h h' sq
  · intro τ hτ
    exact pullbackDifferentialsComparison_unique f g h h' sq τ hτ

end AlgebraicGeometry.RingedSpace
