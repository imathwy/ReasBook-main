import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
namespace StackInGroupoidsOver

/-- The canonical automorphism sheaf of an object of a fiber, obtained by specializing the
localized Hom-sheaf owner `Pseudofunctor.sheafHom` to endomorphisms. -/
noncomputable abbrev automorphismSheaf
    (𝒮 : StackInGroupoidsOver J) {U : C} (x : 𝒮.p.Fiber U) :
    Sheaf (J.over U) (Type (max u v)) :=
  Pseudofunctor.sheafHom (canonicalFiberPseudofunctor 𝒮.p) J x x

end StackInGroupoidsOver

notation "Aut[" 𝒮 "](" x ")" =>
  StackInGroupoidsOver.automorphismSheaf 𝒮 x

/-- Helper for Lemma 8.11.8: a composite `g ≫ f = gf` in `C` transports to the localized site as
`f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc` (the order flips under `op`).  Used as the coherence proof
argument of `mapComp'` cells throughout the refinement-member descent proofs. -/
theorem comp_toLoc_eq {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Y) (gf : X ⟶ Z) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  subst hgf
  simp [← Quiver.Hom.comp_toLoc, ← op_comp]

/-- Helper for Lemma 8.11.8: a functor distributes over a threefold composite.  Used to expand the
`mapComp'.hom ≫ map ≫ mapComp'.inv` shell after `pullHom` is unfolded under a descent functor. -/
theorem functor_map_threefold_comp {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {W X Y Z : D} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  rw [F.map_comp, F.map_comp]

/- 
Domain-style sampling for Lemma 8.11.8:
- primary domain: gerbes and their canonical automorphism sheaves on localized sites `C/U`;
- inspected owner-level declarations:
  `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`,
  `IsGerbe`,
  `canonicalFiberPseudofunctor`,
  `Pseudofunctor.overMapCompPresheafHomIso`,
  `Pseudofunctor.sheafHom`,
  `Sheaf.over`;
- best owner abstraction: the source-facing owner is the canonical automorphism sheaf
  `Aut[𝒮](x)`, i.e. the canonical hom sheaf
  `Pseudofunctor.sheafHom (canonicalFiberPseudofunctor 𝒮.p) J x x`, together with its intrinsic
  composition law on sections and the canonical conjugation isomorphisms induced by morphisms in
  the fiber;
- primitive data: only the canonical automorphism sheaves `Aut[𝒮](x)` themselves;
- derived API: the canonical `AddCommGrpCat`-valued lift of `Aut[𝒮](x)` obtained from that
  intrinsic composition law once it is commutative, and comparison isomorphisms from a global
  abelian-group sheaf `G` to those canonical localized automorphism sheaves.

Source/core/bridge triage:
- `source-facing`: `HasAbelianAutomorphismSheaves` and `IsGerbeBand`;
- `core/canonical`: fibers `𝒮.p.Fiber U`, `Pseudofunctor.sheafHom`, sheaves on `J.over U`, and
  the restriction owner `Sheaf.over`;
- `bridge/view`: the canonical conjugation isomorphisms
  `automorphismSheafConj` and `automorphismAddCommSheafConj`. -/

/-- Every canonical automorphism sheaf `Aut[𝒮](x)` is abelian for its intrinsic composition law on
sections over every object of every localized site `C/U`. This keeps the canonical automorphism
sheaf as the owner object and records abelianity directly on that owner, without introducing a
separate existentially chosen lift after forgetting to types. -/
def HasAbelianAutomorphismSheaves (𝒮 : StackInGroupoidsOver J) : Prop :=
  ∀ {U : C} (x : 𝒮.p.Fiber U) {T : Over U}
    (α β : (Aut[𝒮](x)).1.obj (op T)), α ≫ β = β ≫ α

noncomputable abbrev automorphismSectionObj {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :=
  T.hom ^*[canonicalPullbackChoice 𝒮.p] x

noncomputable abbrev automorphismSection {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Type (max u v) :=
  automorphismSectionObj x T ⟶ automorphismSectionObj x T

noncomputable instance automorphismSectionZero {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Zero (automorphismSection x T) where
  zero := 𝟙 _

noncomputable instance automorphismSectionAdd {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Add (automorphismSection x T) where
  add α β := α ≫ β

noncomputable instance automorphismSectionNeg {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Neg (automorphismSection x T) where
  neg α := by
    letI : IsGroupoid (𝒮.p.Fiber T.left) :=
      IsFibredInGroupoids.fiber_isGroupoid T.left
    let α' : automorphismSectionObj x T ⟶ automorphismSectionObj x T := α
    letI : IsIso α' := by infer_instance
    exact show automorphismSection x T from inv α'

noncomputable instance automorphismSectionAddCommGroup
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    AddCommGroup (automorphismSection x T) where
  zero_add α := Category.id_comp α
  add_zero α := Category.comp_id α
  add_assoc α β γ := Category.assoc α β γ
  add_comm α β := hAbelian x α β
  neg_add_cancel α := by
    letI : IsGroupoid (𝒮.p.Fiber T.left) :=
      IsFibredInGroupoids.fiber_isGroupoid T.left
    let α' : automorphismSectionObj x T ⟶ automorphismSectionObj x T := α
    letI : IsIso α' := by infer_instance
    simpa using IsIso.inv_hom_id α'
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable def automorphismAddCommPresheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (x : 𝒮.p.Fiber U) :
    (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj := fun T ↦ by
    let _ := automorphismSectionAddCommGroup hAbelian x T.unop
    exact AddCommGrpCat.of (automorphismSection x T.unop)
  map := fun {X Y} p ↦ by
    let _ := automorphismSectionAddCommGroup hAbelian x X.unop
    let _ := automorphismSectionAddCommGroup hAbelian x Y.unop
    exact
      AddCommGrpCat.ofHom <|
        AddMonoidHom.mk' ((Aut[𝒮](x)).1.map p) <| by
          let _ := automorphismSectionAddCommGroup hAbelian x X.unop
          let _ := automorphismSectionAddCommGroup hAbelian x Y.unop
          intro α β
          have hp : p.unop.left ≫ X.unop.hom = Y.unop.hom := by
            simpa using Over.w p.unop
          let F := canonicalFiberPseudofunctor 𝒮.p
          let a := X.unop.hom
          let b := Y.unop.hom
          let f := p.unop.left
          let compIso := F.mapComp' a.op.toLoc f.op.toLoc b.op.toLoc
            (by simpa [a, b, f, hp] using congrArg (fun k ↦ k.op.toLoc) hp)
          let compNatIso := Cat.Hom.toNatIso compIso
          let A := compNatIso.hom.app x
          let B := compNatIso.inv.app x
          let pullbackFunctor := (F.map f.op.toLoc).toFunctor
          have hBA0 : B ≫ A = 𝟙 _ := by
            simpa [A, B, compNatIso] using congr_app compNatIso.inv_hom_id x
          change A ≫ pullbackFunctor.map (α ≫ β) ≫ B =
            (A ≫ pullbackFunctor.map α ≫ B) ≫ (A ≫ pullbackFunctor.map β ≫ B)
          rw [Functor.map_comp]
          change A ≫ (pullbackFunctor.map α ≫ pullbackFunctor.map β) ≫ B =
            (A ≫ pullbackFunctor.map α ≫ B) ≫ (A ≫ pullbackFunctor.map β ≫ B)
          have hBA :
              B ≫ A ≫ (pullbackFunctor.map β ≫ B) = pullbackFunctor.map β ≫ B := by
            rw [← Category.assoc, hBA0, Category.id_comp]
            rfl
          calc
            A ≫ (pullbackFunctor.map α ≫ pullbackFunctor.map β) ≫ B
                = A ≫ pullbackFunctor.map α ≫ (pullbackFunctor.map β ≫ B) := by
                    simp [Category.assoc]
            _ = A ≫ pullbackFunctor.map α ≫ (B ≫ A ≫ (pullbackFunctor.map β ≫ B)) := by
                    rw [← hBA]
                    rfl
            _ = A ≫ pullbackFunctor.map α ≫ B ≫ A ≫ pullbackFunctor.map β ≫ B := by
                    simp
            _ = (A ≫ pullbackFunctor.map α ≫ B) ≫ (A ≫ pullbackFunctor.map β ≫ B) := by
                    simp
  map_id := by
    intro T
    apply AddCommGrpCat.ext
    intro α
    exact congr_fun ((Aut[𝒮](x)).1.map_id T) α
  map_comp := by
    intro T₁ T₂ T₃ p q
    apply AddCommGrpCat.ext
    intro α
    exact congr_fun ((Aut[𝒮](x)).1.map_comp p q) α

/-- The canonical sheaf of abelian groups underlying the automorphism sheaf `Aut[𝒮](x)` once the
intrinsic composition law is commutative. -/
noncomputable def StackInGroupoidsOver.automorphismAddCommSheaf
    (𝒮 : StackInGroupoidsOver J) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} (x : 𝒮.p.Fiber U) :
    Sheaf (J.over U) AddCommGrpCat.{max u v} where
  obj := automorphismAddCommPresheaf hAbelian x
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget
      (J.over U) (automorphismAddCommPresheaf hAbelian x) (forget AddCommGrpCat.{max u v})]
    simpa [automorphismAddCommPresheaf, automorphismSection, automorphismSectionObj] using
      (Aut[𝒮](x)).property

/-- Helper for Lemma 8.11.8: forget the additive structure on the canonical abelian
automorphism sheaf while keeping the underlying `Type`-valued sheaf on the slice site. -/
noncomputable def automorphismUnderlyingSheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (x : 𝒮.p.Fiber U) :
    Sheaf (J.over U) (Type (max u v)) where
  obj := (𝒮.automorphismAddCommSheaf hAbelian x).1 ⋙ forget AddCommGrpCat
  property := by
    -- The sheaf condition survives after forgetting from abelian groups to types.
    exact
      (Presheaf.isSheaf_iff_isSheaf_forget
        (J.over U) (𝒮.automorphismAddCommSheaf hAbelian x).1
        (forget AddCommGrpCat.{max u v})).1
        (𝒮.automorphismAddCommSheaf hAbelian x).property

/-- Helper for Lemma 8.11.8: conjugation on the canonical automorphism sheaf commutes with
restriction along a morphism in the localized site. -/
theorem automorphism_sheaf_conj_pull_naturality
    {U : C} {x y : 𝒮.p.Fiber U} (e : x ≅ y) {X Y : (Over U)ᵒᵖ} (g : X ⟶ Y)
    (α : Aut[𝒮](x).1.obj X) :
    let F := canonicalFiberPseudofunctor 𝒮.p
    ((F.map (Y.unop.hom.op.toLoc)).toFunctor.mapIso e).conj
      (pullHom α g.unop.left Y.unop.hom Y.unop.hom
        (by simpa using Over.w g.unop) (by simpa using Over.w g.unop)) =
    pullHom (((F.map (X.unop.hom.op.toLoc)).toFunctor.mapIso e).conj α)
      g.unop.left Y.unop.hom Y.unop.hom
      (by simpa using Over.w g.unop) (by simpa using Over.w g.unop) := by
  intro F
  -- Expand `pullHom` and both conjugations; the goal becomes two `mapComp'` naturality squares.
  -- The `delta`-expanded representation is defeq-but-not-`kabstract`-alignable with the lemmas, so
  -- we `show` the goal in the bundled form (re-folding the projection chain via `isDefEq`); then the
  -- specific `mapComp'` naturalities match: head `hom` cell w.r.t. `e.inv`, tail `inv` w.r.t. `e.hom`.
  have hp : g.unop.left ≫ X.unop.hom = Y.unop.hom := by simpa using Over.w g.unop
  have hcomp_eq : X.unop.hom.op.toLoc ≫ g.unop.left.op.toLoc = Y.unop.hom.op.toLoc := by
    simpa using congrArg (fun k ↦ k.op.toLoc) hp
  simp only [F]
  delta Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  simp only [Functor.map_conj]
  rw [Iso.conj_apply, Iso.conj_apply]
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp]
  show ((canonicalFiberPseudofunctor 𝒮.p).map Y.unop.hom.op.toLoc).toFunctor.map e.inv ≫
        (((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
              Y.unop.hom.op.toLoc hcomp_eq).hom.toNatTrans.app x ≫
          ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map α ≫
            ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
                  Y.unop.hom.op.toLoc hcomp_eq).inv.toNatTrans.app x) ≫
              ((canonicalFiberPseudofunctor 𝒮.p).map Y.unop.hom.op.toLoc).toFunctor.map e.hom =
      ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
            Y.unop.hom.op.toLoc hcomp_eq).hom.toNatTrans.app y ≫
        (((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor 𝒮.p).map X.unop.hom.op.toLoc).toFunctor.map e.inv) ≫
          ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map α ≫
            ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map
                (((canonicalFiberPseudofunctor 𝒮.p).map X.unop.hom.op.toLoc).toFunctor.map e.hom)) ≫
              ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
                    Y.unop.hom.op.toLoc hcomp_eq).inv.toNatTrans.app y
  simp only [Category.assoc]
  have hfront := (canonicalFiberPseudofunctor 𝒮.p).mapComp'_hom_naturality
    X.unop.hom.op.toLoc g.unop.left.op.toLoc Y.unop.hom.op.toLoc hcomp_eq e.inv
  have hback := (canonicalFiberPseudofunctor 𝒮.p).mapComp'_inv_naturality
    X.unop.hom.op.toLoc g.unop.left.op.toLoc Y.unop.hom.op.toLoc hcomp_eq e.hom
  -- `rw`/`simp`/`slice` cannot locate the `mapComp'` cells in the goal (a `kabstract` matching
  -- defect on `Cat.Hom₂.toNatTrans.app` under `respectTransparency false`), even though `hfront`/
  -- `hback` have exactly the goal's factor pairs as their LHS.  Close in term mode via `congrArg`
  -- (structural, no `kabstract`): rewrite the tail pair by `hback`, regroup, rewrite the head pair
  -- by `hfront`, regroup back.
  let A1 := ((canonicalFiberPseudofunctor 𝒮.p).map Y.unop.hom.op.toLoc).toFunctor.map e.inv
  let A2 := ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
    Y.unop.hom.op.toLoc hcomp_eq).hom.toNatTrans.app x
  let A3 := ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map α
  let B1 := ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
    Y.unop.hom.op.toLoc hcomp_eq).hom.toNatTrans.app y
  let B2 := ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map
    (((canonicalFiberPseudofunctor 𝒮.p).map X.unop.hom.op.toLoc).toFunctor.map e.inv)
  let B4 := ((canonicalFiberPseudofunctor 𝒮.p).map g.unop.left.op.toLoc).toFunctor.map
    (((canonicalFiberPseudofunctor 𝒮.p).map X.unop.hom.op.toLoc).toFunctor.map e.hom)
  let B5 := ((canonicalFiberPseudofunctor 𝒮.p).mapComp' X.unop.hom.op.toLoc g.unop.left.op.toLoc
    Y.unop.hom.op.toLoc hcomp_eq).inv.toNatTrans.app y
  exact (congrArg (fun m => A1 ≫ A2 ≫ A3 ≫ m) hback.symm).trans
    ((Category.assoc A1 A2 (A3 ≫ B4 ≫ B5)).symm.trans
      ((congrArg (fun m => m ≫ A3 ≫ B4 ≫ B5) hfront).trans
        (Category.assoc B1 B2 (A3 ≫ B4 ≫ B5))))

/-- Conjugation by a morphism in a fiber induces the canonical isomorphism
`Aut[𝒮](x) ≅ Aut[𝒮](y)` between automorphism sheaves. -/
noncomputable def automorphismSheafConj {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    Aut[𝒮](x) ≅ Aut[𝒮](y) := by
  let F := canonicalFiberPseudofunctor 𝒮.p
  let e : x ≅ y := asIso φ
  let homNat : (Aut[𝒮](x)).1 ⟶ (Aut[𝒮](y)).1 :=
    { app := fun f α ↦
        let g := f.unop.hom
        let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
        (pullbackFunctor.mapIso e).conj α
      naturality := by
        intro X Y g
        ext α
        -- Conjugation commutes with restriction pointwise on sections.
        simpa using automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e g α }
  let invNat : (Aut[𝒮](y)).1 ⟶ (Aut[𝒮](x)).1 :=
    { app := fun f α ↦
        let g := f.unop.hom
        let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
        (pullbackFunctor.mapIso e.symm).conj α
      naturality := by
        intro X Y g
        ext α
        -- The inverse comparison satisfies the same restriction compatibility.
        simpa using automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e.symm g α }
  refine
    { hom := Sheaf.homEquiv.symm homNat
      inv := Sheaf.homEquiv.symm invNat
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sheaf.hom_ext
    ext f α
    -- Pointwise, conjugation by `e` and `e.symm` cancels.
    let pullbackFunctor := (F.map (.toLoc f.unop.hom.op)).toFunctor
    change (pullbackFunctor.mapIso e.symm).conj ((pullbackFunctor.mapIso e).conj α) = α
    simpa using (Iso.symm_self_conj (α := pullbackFunctor.mapIso e) α)
  · apply Sheaf.hom_ext
    ext f α
    -- The reverse composite cancels by the same pointwise conjugation identity.
    let pullbackFunctor := (F.map (.toLoc f.unop.hom.op)).toFunctor
    change (pullbackFunctor.mapIso e).conj ((pullbackFunctor.mapIso e.symm).conj α) = α
    simpa using (Iso.self_symm_conj (α := pullbackFunctor.mapIso e) α)

/-- Conjugation by a morphism in a fiber induces the canonical isomorphism between the associated
abelian-group automorphism sheaves on the localized site `C/U`. -/
noncomputable def automorphismAddCommSheafConj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    𝒮.automorphismAddCommSheaf hAbelian x ≅
      𝒮.automorphismAddCommSheaf hAbelian y := by
  let F := canonicalFiberPseudofunctor 𝒮.p
  let e : x ≅ y := asIso φ
  let homNat : (𝒮.automorphismAddCommSheaf hAbelian x).1 ⟶
      (𝒮.automorphismAddCommSheaf hAbelian y).1 :=
    { app := fun T ↦
        let g := T.unop.hom
        let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
        let _ := automorphismSectionAddCommGroup hAbelian x T.unop
        let _ := automorphismSectionAddCommGroup hAbelian y T.unop
        AddCommGrpCat.ofHom <|
          AddMonoidHom.mk'
            (fun α ↦ (pullbackFunctor.mapIso e).conj α) <| by
              let _ := automorphismSectionAddCommGroup hAbelian x T.unop
              let _ := automorphismSectionAddCommGroup hAbelian y T.unop
              intro α β
              simpa [automorphismSectionAdd, automorphismSection, automorphismSectionObj] using
                (pullbackFunctor.mapIso e).conj_comp α β
      naturality := by
        intro X Y g
        apply AddCommGrpCat.ext
        intro α
        -- After forgetting the additive structure, this is the same restriction compatibility.
        simpa [automorphismAddCommPresheaf] using
          automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e g α }
  let invNat : (𝒮.automorphismAddCommSheaf hAbelian y).1 ⟶
      (𝒮.automorphismAddCommSheaf hAbelian x).1 :=
    { app := fun T ↦
        let g := T.unop.hom
        let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
        let _ := automorphismSectionAddCommGroup hAbelian y T.unop
        let _ := automorphismSectionAddCommGroup hAbelian x T.unop
        AddCommGrpCat.ofHom <|
          AddMonoidHom.mk'
            (fun α ↦ (pullbackFunctor.mapIso e.symm).conj α) <| by
              let _ := automorphismSectionAddCommGroup hAbelian y T.unop
              let _ := automorphismSectionAddCommGroup hAbelian x T.unop
              intro α β
              simpa [automorphismSectionAdd, automorphismSection, automorphismSectionObj] using
                (pullbackFunctor.mapIso e.symm).conj_comp α β
      naturality := by
        intro X Y g
        apply AddCommGrpCat.ext
        intro α
        -- The inverse comparison again reduces to the underlying type-valued statement.
        simpa [automorphismAddCommPresheaf] using
          automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e.symm g α }
  refine
    { hom := Sheaf.homEquiv.symm homNat
      inv := Sheaf.homEquiv.symm invNat
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sheaf.hom_ext
    ext T α
    -- Equality of sheaf maps is checked pointwise on the underlying automorphism groups.
    let pullbackFunctor := (F.map (.toLoc T.unop.hom.op)).toFunctor
    change (pullbackFunctor.mapIso e.symm).conj ((pullbackFunctor.mapIso e).conj α) = α
    simpa using (Iso.symm_self_conj (α := pullbackFunctor.mapIso e) α)
  · apply Sheaf.hom_ext
    ext T α
    -- The reverse composite is the same pointwise cancellation statement.
    let pullbackFunctor := (F.map (.toLoc T.unop.hom.op)).toFunctor
    change (pullbackFunctor.mapIso e).conj ((pullbackFunctor.mapIso e.symm).conj α) = α
    simpa using (Iso.self_symm_conj (α := pullbackFunctor.mapIso e) α)

/-- Helper for Lemma 8.11.8: forgetting the additive structure on
`automorphismAddCommSheafConj` gives the `Type`-valued conjugation morphism used on overlaps. -/
noncomputable def automorphismUnderlyingSheafConj_hom
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ⟶
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y :=
  Sheaf.homEquiv.symm <|
    Functor.whiskerRight
      (automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ).hom.1
      (forget AddCommGrpCat.{max u v})

/-- Helper for Lemma 8.11.8: under the abelianity hypothesis, inner conjugation acts trivially on
the canonical abelian automorphism sheaf. -/
theorem automorphism_addcomm_inner_conj_eq_refl
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {z : 𝒮.p.Fiber U} (β : z ⟶ z) :
    automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian β = Iso.refl _ := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext T α
  let F := canonicalFiberPseudofunctor 𝒮.p
  let e : z ≅ z := asIso β
  let g := T.unop.hom
  let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
  have hcomm :
      α ≫ (pullbackFunctor.mapIso e).hom = (pullbackFunctor.mapIso e).hom ≫ α := by
    -- Abelianity says every local automorphism commutes with the pulled-back inner automorphism.
    simpa [e] using hAbelian z α ((pullbackFunctor.mapIso e).hom)
  -- Pointwise, conjugation by a commuting automorphism is the identity.
  change (pullbackFunctor.mapIso e).inv ≫ α ≫ (pullbackFunctor.mapIso e).hom = α
  simpa [Category.assoc] using
    (congrArg (fun t ↦ (pullbackFunctor.mapIso e).inv ≫ t) hcomm).trans
      (Iso.inv_hom_id_assoc (pullbackFunctor.mapIso e) α)

/-- Helper for Lemma 8.11.8: conjugation on the canonical abelian automorphism sheaves is
functorial under composition in a fiber. -/
theorem automorphismAddCommSheafConj_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext T α
  let F := canonicalFiberPseudofunctor 𝒮.p
  let eφ : x ≅ y := asIso φ
  let eψ : y ≅ z := asIso ψ
  let ecomp : x ≅ z := asIso (φ ≫ ψ)
  let pullbackFunctor := (F.map (.toLoc T.unop.hom.op)).toFunctor
  let Eφ := pullbackFunctor.mapIso eφ
  let Eψ := pullbackFunctor.mapIso eψ
  -- Pointwise, conjugation by a composite is the composite of the conjugations: `mapIso` of the
  -- composite iso splits (`Functor.mapIso_trans`), then `Iso.trans_conj` distributes.
  have hcomp : ecomp = eφ ≪≫ eψ := Iso.ext rfl
  -- MATHEMATICALLY this is `Eφ.trans_conj Eψ α : (Eφ ≪≫ Eψ).conj α = Eψ.conj (Eφ.conj α)` after
  -- `Functor.mapIso_trans` splits `mapIso (eφ ≪≫ eψ)`.  BLOCKER (proof-level `sorry`): the goal,
  -- after `ext T α`, is in the `Sheaf.homEquiv.symm {app := …}.hom.app T α` representation, and
  -- `simpa` does not peel the `Sheaf.homEquiv.symm`/`AddCommGrpCat.ofHom`/`AddMonoidHom.mk'`
  -- wrappers down to the bare `Iso.conj` form, so the clean `Iso.trans_conj` term type-mismatches
  -- the wrapped goal.  Same representation-friction class as `automorphism_sheaf_conj_pull_naturality`.
  sorry

/-- Helper for Lemma 8.11.8: parallel fiber morphisms induce the same conjugation isomorphism on
the canonical abelian automorphism sheaves. -/
theorem automorphismAddCommSheafConj_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
      automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  let eφ : x ≅ y := asIso φ
  let β : y ⟶ y := eφ.inv ≫ ψ
  have hfactor : φ ≫ β = ψ := by
    -- In a groupoid fiber, any parallel map differs by an inner automorphism of the target.
    dsimp [β, eφ]
    simp
  -- Abelianity kills the inner automorphism, so only the endpoints matter.
  rw [← hfactor, automorphismAddCommSheafConj_comp]
  simp [automorphism_addcomm_inner_conj_eq_refl]

/-- Helper for Lemma 8.11.8: after forgetting the additive structure, inner conjugation still
acts trivially on the underlying `Type`-valued automorphism sheaf. -/
theorem automorphismUnderlyingSheafConj_hom_self
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {z : 𝒮.p.Fiber U} (β : z ⟶ z) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian β = 𝟙 _ := by
  -- Forget the additive structure pointwise and reuse the abelian inner-conjugation collapse.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphism_addcomm_inner_conj_eq_refl (𝒮 := 𝒮) hAbelian β))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure preserves the composition law for
the canonical automorphism-sheaf conjugation maps. -/
theorem automorphismUnderlyingSheafConj_hom_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ ≫
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ψ := by
  -- Compare the underlying section maps pointwise after forgetting the additive structure.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphismAddCommSheafConj_comp (𝒮 := 𝒮) hAbelian φ ψ))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure preserves the fact that parallel
fiber morphisms induce the same conjugation map on automorphism sheaves. -/
theorem automorphismUnderlyingSheafConj_hom_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ =
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ψ := by
  -- The `Type`-valued overlap morphisms inherit independence of the chosen local isomorphism.
  apply Sheaf.hom_ext
  ext T α
  simpa [automorphismUnderlyingSheafConj_hom] using
    congrFun
      (congrArg
        (fun i ↦
          (Functor.whiskerRight i.hom.1 (forget AddCommGrpCat.{max u v})).app T)
        (automorphismAddCommSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian φ ψ))
      α

/-- Helper for Lemma 8.11.8: forgetting the additive structure on
`automorphismAddCommSheafConj` still produces an isomorphism of the underlying `Type`-valued
automorphism sheaves. This is the componentwise owner needed for the secondary-cover overlap
descent route. -/
noncomputable def automorphismUnderlyingSheafConj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y where
  hom := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ
  inv := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv
  hom_inv_id := by
    -- Conjugating by `φ` and then by `φ⁻¹` is an inner automorphism, hence trivial in the
    -- abelian automorphism sheaf.
    calc
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv
          =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (φ ≫ (asIso φ).inv) := by
            symm
            exact
              automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian φ (asIso φ).inv
      _ = 𝟙 _ := by
        exact
          automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian
            (φ ≫ (asIso φ).inv)
  inv_hom_id := by
    -- The reverse composite is the same inner-conjugation collapse on the target object.
    calc
      automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian (asIso φ).inv ≫
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian φ
          =
        automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian ((asIso φ).inv ≫ φ) := by
            symm
            exact
              automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian (asIso φ).inv φ
      _ = 𝟙 _ := by
        exact
          automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian
            ((asIso φ).inv ≫ φ)

/-- Helper for Lemma 8.11.8: the underlying `Type`-valued conjugation isomorphism is literally
the identity on endomorphisms, because abelianity kills inner conjugation. -/
theorem automorphismUnderlyingSheafConj_self
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {z : 𝒮.p.Fiber U} (β : z ⟶ z) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian β = Iso.refl _ := by
  apply Iso.ext
  -- The new iso-level API reduces immediately to the already-proved hom-level triviality.
  exact automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian β

/-- Helper for Lemma 8.11.8: the underlying `Type`-valued conjugation isomorphisms compose in the
same way as the additive conjugation isomorphisms from which they are forgotten. -/
theorem automorphismUnderlyingSheafConj_comp
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y z : 𝒮.p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian (φ ≫ ψ) =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  -- Equality of the underlying isomorphisms is checked on their `hom` fields.
  exact automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian φ ψ

/-- Helper for Lemma 8.11.8: on the underlying `Type`-valued automorphism sheaf, the induced
conjugation isomorphism depends only on the endpoints of a local isomorphism. -/
theorem automorphismUnderlyingSheafConj_eq_of_parallel
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ ψ : x ⟶ y) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian ψ := by
  apply Iso.ext
  -- This is the iso-level packaging of the previously proved hom-level endpoint-independence.
  exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian φ ψ

/-- Helper for Lemma 8.11.8: forgetting the additive structure on the canonical abelian
automorphism sheaf recovers the original `Type`-valued automorphism sheaf `Aut[𝒮](x)`. -/
noncomputable def automorphismUnderlyingSheafIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (x : 𝒮.p.Fiber U) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x ≅ Aut[𝒮](x) := by
  let homNat :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1 ⟶ (Aut[𝒮](x)).1 :=
    { app := fun T α ↦ α
      naturality := by
        intro X Y g
        rfl }
  let invNat :
      (Aut[𝒮](x)).1 ⟶ (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1 :=
    { app := fun T α ↦ α
      naturality := by
        intro X Y g
        rfl }
  refine
    { hom := Sheaf.homEquiv.symm homNat
      inv := Sheaf.homEquiv.symm invNat
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sheaf.hom_ext
    ext T α
    rfl
  · apply Sheaf.hom_ext
    ext T α
    rfl

/-- Helper for Lemma 8.11.8: after identifying the forgotten abelian automorphism sheaf with
`Aut[𝒮](x)`, the forgotten conjugation isomorphism is the canonical `Type`-valued conjugation
isomorphism. -/
theorem automorphismUnderlyingSheafIso_conj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C}
    {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian x ≪≫
        automorphismSheafConj (𝒮 := 𝒮) φ =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ ≪≫
        automorphismUnderlyingSheafIso (𝒮 := 𝒮) hAbelian y := by
  apply Iso.ext
  -- Both sides are pointwise the same conjugation map after forgetting the additive structure.
  apply Sheaf.hom_ext
  ext T α
  rfl

/-- Helper for Lemma 8.11.8: after forgetting the additive structure, the underlying
conjugation isomorphism still commutes with restriction along morphisms in a localized site. This
is the owner-level bridge from the canonical `Aut[𝒮]` naturality statement to the
`automorphismUnderlyingSheaf` API used on the secondary cover. -/
theorem automorphismUnderlyingSheafConj_pull_naturality
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U : C} {x y : 𝒮.p.Fiber U} (e : x ≅ y) {X Y : (Over U)ᵒᵖ} (g : X ⟶ Y)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x).1.obj X) :
    let F := canonicalFiberPseudofunctor 𝒮.p
    ((F.map (Y.unop.hom.op.toLoc)).toFunctor.mapIso e).conj
      (pullHom α g.unop.left Y.unop.hom Y.unop.hom
        (by simpa using Over.w g.unop) (by simpa using Over.w g.unop)) =
    pullHom
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e.hom).hom.1.app X) α)
      g.unop.left Y.unop.hom Y.unop.hom
      (by simpa using Over.w g.unop) (by simpa using Over.w g.unop) := by
  -- Owner-level wrapper.  `convert … using 2` reduces this to `automorphism_sheaf_conj_pull_naturality
  -- e g α` (now PROVEN) up to one argument: the RHS conjugated automorphism is presented through the
  -- `automorphismUnderlyingSheafConj_hom = Sheaf.homEquiv.symm (whiskerRight … (forget))` wrapper,
  -- and the residual is the *true* computation
  --   `(automorphismUnderlyingSheafConj hAbelian e.hom).hom.val.app X α = ((F.map Xhom).mapIso e).conj α`.
  -- BLOCKER (proof-level `sorry`): collapsing the `Sheaf.homEquiv.symm`/`whiskerRight (forget)`
  -- wrapper down to the bare fibre conjugation needs the right `Sheaf.homEquiv`/`whiskerRight_app`
  -- computation lemmas (same wrapper friction as `automorphismAddCommSheafConj_comp`@400).
  convert automorphism_sheaf_conj_pull_naturality (𝒮 := 𝒮) e g α using 2
  sorry

/-- Base-change coherence `θ` for the canonical automorphism sheaf: pulling the (Type-valued)
automorphism sheaf of `x` back along `q` agrees with the automorphism sheaf of the fibre pullback
`q ^* x`.  Concretely this is mathlib's `Pseudofunctor.overMapCompPresheafHomIso` for the
`canonicalFiberPseudofunctor` (the underlying presheaf of `automorphismUnderlyingSheaf x` is exactly
`presheafHom x x`, the `AddCommGrp ⋙ forget` round-trip being the identity on `Type`), lifted from
presheaves to sheaves through the fully faithful `sheafToPresheaf`. -/
noncomputable def automorphismUnderlyingSheafBaseChangeIso
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Z : C} (q : Z ⟶ U) (x : 𝒮.p.Fiber U) :
    ((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian x) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).obj x) :=
  (fullyFaithfulSheafToPresheaf (J.over Z) (Type (max u v))).preimageIso
    ((canonicalFiberPseudofunctor 𝒮.p).overMapCompPresheafHomIso x x q)

/-- Helper for Lemma 8.11.8: pulling back the underlying conjugation morphism along `q`
is exactly conjugation by the pulled fiber isomorphism over `Z`. This is the thin transport
adapter needed when the source route reaches a pulled conjugation shell. -/
theorem automorphismUnderlyingSheafConj_pullbackFunctor_map
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} {x y : 𝒮.p.Fiber U} (q : Z ⟶ U) (φ : x ⟶ y) :
    ((J.pseudofunctorOver (Type (max u v))).map q.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian φ).hom) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q x).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor q).mapIso
            (asIso φ)).hom)).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian q y).inv := by
  -- Pulling the conjugation `conj φ` back along `q` is, through the base-change coherence `θ`,
  -- conjugation by the pulled fibre isomorphism over `Z`.  Pointwise (`ext T α`) both sides are the
  -- same conjugation by the pulled iso, transported by `θ`; the normalisation hits the residual
  -- `Iso.conj`/`Sheaf.homEquiv` wrapper friction.  See `book-build-landscape`.
  sorry

/-- A sheaf `G` of abelian groups is a band for the gerbe `𝒮` if its restriction to every
localized site `C/U` identifies, as a sheaf of abelian groups, with the
canonical abelian-group automorphism sheaf attached to each object `x` of the fiber over `U`, and
these identifications are compatible with canonical conjugation by morphisms in that fiber. -/
def IsGerbeBand (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
    ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj hAbelian φ = comparison y

/-- Helper for Lemma 8.11.8: fix once and for all one gerbe cover of each object of the base. -/
noncomputable def chosen_gerbe_cover
    (hGerbe : IsGerbe J 𝒮.p) (U : C) : J.Cover U :=
  Classical.choose (hGerbe.locally_inhabited U)

/-- Helper for Lemma 8.11.8: for the fixed chosen gerbe cover of `U`, choose one local object on
each cover arrow. -/
noncomputable def chosen_gerbe_cover_object
    (hGerbe : IsGerbe J 𝒮.p) (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    𝒮.p.Fiber I.Y :=
  Classical.choice ((Classical.choose_spec (hGerbe.locally_inhabited U)) I)

/-- Helper for Lemma 8.11.8: for any two objects in one fiber, choose a single secondary cover on
which they become isomorphic. This is the source-faithful local owner for overlap comparisons. -/
noncomputable def chosen_local_isomorphism_cover
    (hGerbe : IsGerbe J 𝒮.p) {U : C} (x y : 𝒮.p.Fiber U) : J.Cover U :=
  Classical.choose (hGerbe.locally_isomorphic x y)

/-- Helper for Lemma 8.11.8: on the chosen local-isomorphism cover, choose one local comparison
isomorphism between the two pulled-back fiber objects. -/
noncomputable def chosen_local_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U : C} (x y : 𝒮.p.Fiber U)
    (I : (chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe x y).Arrow) :
    I.f ^*[canonicalPullbackChoice 𝒮.p] x ≅
      I.f ^*[canonicalPullbackChoice 𝒮.p] y :=
  Classical.choice ((Classical.choose_spec (hGerbe.locally_isomorphic x y)) I)

/-- Helper for Lemma 8.11.8: on an overlap object of the fixed chosen cover, pull back the first
chosen local object to that overlap. This isolates the source proof's first local owner. -/
noncomputable abbrev local_overlap_source_object
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ : S.Arrow} (f₁ : Y ⟶ I₁.Y) :
    𝒮.p.Fiber Y :=
  f₁ ^*[canonicalPullbackChoice 𝒮.p] xS I₁

/-- Helper for Lemma 8.11.8: on the same overlap object, pull back the second chosen local
object. The source proof compares automorphism sheaves of these two overlap objects. -/
noncomputable abbrev local_overlap_target_object
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₂ : S.Arrow} (f₂ : Y ⟶ I₂.Y) :
    𝒮.p.Fiber Y :=
  f₂ ^*[canonicalPullbackChoice 𝒮.p] xS I₂

/-- Helper for Lemma 8.11.8: once the two local overlap objects are fixed, choose the secondary
cover on which they become isomorphic. This is the source-faithful owner for the overlap descent
step. -/
noncomputable abbrev local_overlap_isomorphism_cover
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    J.Cover Y :=
  chosen_local_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
    (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)

/-- Helper for Lemma 8.11.8: on the chosen secondary cover of an overlap object, pick the local
isomorphism between the two pulled-back cover objects. -/
noncomputable def local_overlap_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) :=
  chosen_local_isomorphism (𝒮 := 𝒮) hGerbe
    (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)
    (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)
    K

/-- Helper for Lemma 8.11.8: each chosen local isomorphism on the secondary overlap cover induces
the corresponding local conjugation isomorphism on the underlying automorphism sheaves. -/
noncomputable def local_overlap_conjugation_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)) ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)) :=
  -- The source proof's local comparison on the secondary cover is exactly conjugation by the
  -- chosen local isomorphism.
  automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
    (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K).hom

/-- Helper for Lemma 8.11.8: first pull the source automorphism sheaf from the fixed chosen cover
to the overlap object `Y`. This names the source sheaf before the secondary-cover descent step,
so later overlap proofs do not have to reopen the outer pullback shell. -/
noncomputable abbrev local_overlap_source_secondary_sheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ : S.Arrow} (f₁ : Y ⟶ I₁.Y) :
    Sheaf (J.over Y) (Type (max u v)) :=
  ((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.obj
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))

/-- Helper for Lemma 8.11.8: pull the target automorphism sheaf from the fixed chosen cover to the
same overlap object `Y`, mirroring `local_overlap_source_secondary_sheaf` on the target side. -/
noncomputable abbrev local_overlap_target_secondary_sheaf
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₂ : S.Arrow} (f₂ : Y ⟶ I₂.Y) :
    Sheaf (J.over Y) (Type (max u v)) :=
  ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.obj
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))

/-- Helper for Lemma 8.11.8: package the source sheaf on the overlap object as a descent datum on
the chosen secondary cover. This isolates the source side of the remaining `isoMk` square as a
concrete object of the descent-data category. -/
noncomputable abbrev local_overlap_source_secondary_descent_data
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f) :=
  (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f)).obj
    (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁))

/-- Helper for Lemma 8.11.8: package the target sheaf on the overlap object as a descent datum on
the same chosen secondary cover. With both sides named, the remaining blocker is a single
secondary-cover descent isomorphism rather than a repeated transport shell. -/
noncomputable abbrev local_overlap_target_secondary_descent_data
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f) :=
  (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun K :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow ↦ K.f)).obj
    (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂))

/-- Helper for Lemma 8.11.8: the `isoMk` square for the chosen local conjugation family
normalizes to the common pairwise-pullback conjugation map on the secondary cover. -/
theorem local_overlap_source_secondary_transition_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg₂)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) := by
  -- This descent datum is literally `toDescentData` applied to the source sheaf over `Y`.
  rfl

/-- Helper for Lemma 8.11.8: the target-side secondary-cover descent transition is the canonical
`toDescentData` comparison between the two pullback legs to the common owner `q`. -/
theorem local_overlap_target_secondary_transition_normalize
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    (local_overlap_target_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (by simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg₂)).hom.toNatTrans.app
          (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) := by
  -- The target descent datum is the same `toDescentData` owner applied to the target sheaf.
  rfl

/-- Helper for Lemma 8.11.8: the source object pulled back to the common owner `q` is identified
with the iterated pullback through one arrow of the secondary overlap cover. -/
noncomputable abbrev local_overlap_common_owner_source_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫
    hc.pullbackCompComponentIso K.f g
      (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)

/-- Helper for Lemma 8.11.8: the target object pulled back to the common owner `q` is identified
with the iterated pullback through the same secondary-cover arrow. -/
noncomputable abbrev local_overlap_common_owner_target_iso
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) ≅
      g ^*[canonicalPullbackChoice 𝒮.p]
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)) :=
  let hc := canonicalPullbackChoice 𝒮.p
  (eqToIso (by cases hg; rfl)) ≪≫
    hc.pullbackCompComponentIso K.f g
      (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)

/-- Helper for Lemma 8.11.8: one local comparison isomorphism on the secondary overlap cover can
be rewritten as an isomorphism between the common-owner pullbacks along `q`. -/
noncomputable abbrev local_overlap_common_owner_isomorphism
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) ≅
      q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) :=
  let hc := canonicalPullbackChoice 𝒮.p
  local_overlap_common_owner_source_iso (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg ≪≫
    (hc.pullbackFunctor g).mapIso
      (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K) ≪≫
    (local_overlap_common_owner_target_iso (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).symm

/-- Helper for Lemma 8.11.8: after rewriting the common-owner leg by `hg`, the inverse
`mapComp'` component of the canonical fiber pseudofunctor is exactly the inverse source-side
common-owner comparison isomorphism. This is the fiber-level half of the blocked sectionwise
transport normalization. -/
theorem local_overlap_common_owner_source_iso_inv_eq_mapComp'_inv_app
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).inv.toNatTrans.app
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁) =
      (local_overlap_common_owner_source_iso
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv := by
  -- Route correction: reduce the flexible `mapComp'` shell to the canonical pullback-composition
  -- comparison after substituting the common-owner equality `hg`.
  cases hg
  simpa [local_overlap_common_owner_source_iso] using
    (fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
      (hc := canonicalPullbackChoice 𝒮.p) K.f g
      (local_overlap_source_object (𝒮 := 𝒮) S xS f₁))

/-- Helper for Lemma 8.11.8: after rewriting the common-owner leg by `hg`, the hom `mapComp'`
component of the canonical fiber pseudofunctor is exactly the hom target-side common-owner
comparison isomorphism. This is the symmetric fiber-level transport normalization needed later on
the target half of the overlap square. -/
theorem local_overlap_common_owner_target_iso_hom_eq_mapComp'_hom_app
    (hGerbe : IsGerbe J 𝒮.p) {U Y : C}
    (S : J.Cover U) (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor 𝒮.p).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc
        (by
          simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
            congrArg Quiver.Hom.toLoc <| congrArg Quiver.Hom.op hg)).hom.toNatTrans.app
        (local_overlap_target_object (𝒮 := 𝒮) S xS f₂) =
      (local_overlap_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom := by
  -- The target-side common-owner comparison is the hom-side version of the same canonical
  -- pullback-composition package.
  cases hg
  simpa [local_overlap_common_owner_target_iso] using
    (fiberPseudofunctor_mapComp'_hom_app_eq_pullbackCompComponentIso_hom
      (hc := canonicalPullbackChoice 𝒮.p) K.f g
      (local_overlap_target_object (𝒮 := 𝒮) S xS f₂))

/-- Helper for Lemma 8.11.8: after both local overlap maps are rewritten to the same common owner
`q`, abelianity makes their induced conjugation maps equal because they are parallel morphisms. -/
theorem local_overlap_common_owner_conjugation_eq
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom =
      automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom := by
  -- Both rewritten overlap isomorphisms have the same source and target over `q`, so the
  -- endpoint-independence lemma for conjugation applies directly.
  simpa using
    automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
      (local_overlap_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom
      (local_overlap_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom

end CategoryTheory
