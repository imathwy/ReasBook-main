import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1

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

end CategoryTheory
