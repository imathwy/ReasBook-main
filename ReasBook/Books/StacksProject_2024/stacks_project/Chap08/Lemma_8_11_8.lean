import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_5
import StacksProject_2024.stacks_project.Chap08.Definition_8_11_1

-- Declarations for this item will be appended below by the statement pipeline.

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

private noncomputable abbrev automorphismSectionObj {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :=
  T.hom ^*[canonicalPullbackChoice 𝒮.p] x

private noncomputable abbrev automorphismSection {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Type (max u v) :=
  automorphismSectionObj x T ⟶ automorphismSectionObj x T

private noncomputable instance automorphismSectionZero {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Zero (automorphismSection x T) where
  zero := 𝟙 _

private noncomputable instance automorphismSectionAdd {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Add (automorphismSection x T) where
  add α β := α ≫ β

private noncomputable instance automorphismSectionNeg {U : C} (x : 𝒮.p.Fiber U) (T : Over U) :
    Neg (automorphismSection x T) where
  neg α := by
    letI : IsGroupoid (𝒮.p.Fiber T.left) :=
      IsFibredInGroupoids.fiber_isGroupoid T.left
    let α' : automorphismSectionObj x T ⟶ automorphismSectionObj x T := α
    letI : IsIso α' := by infer_instance
    exact show automorphismSection x T from inv α'

private noncomputable instance automorphismSectionAddCommGroup
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

private noncomputable def automorphismAddCommPresheaf
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

/-- Conjugation by a morphism in a fiber induces the canonical isomorphism
`Aut[𝒮](x) ≅ Aut[𝒮](y)` between automorphism sheaves. -/
noncomputable def automorphismSheafConj {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    Aut[𝒮](x) ≅ Aut[𝒮](y) := by
  let F := canonicalFiberPseudofunctor 𝒮.p
  let e : x ≅ y := asIso φ
  refine
    { hom := Sheaf.homEquiv.symm ?_
      inv := Sheaf.homEquiv.symm ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · refine
      { app := fun f α ↦
          let g := f.unop.hom
          let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
          (pullbackFunctor.mapIso e).conj α
        naturality := ?_ }
    intro X Y g
    ext α
    sorry
  · refine
      { app := fun f α ↦
          let g := f.unop.hom
          let pullbackFunctor := (F.map (.toLoc g.op)).toFunctor
          (pullbackFunctor.mapIso e.symm).conj α
        naturality := ?_ }
    intro X Y g
    ext α
    sorry
  · apply Sheaf.hom_ext
    ext f α
    sorry
  · apply Sheaf.hom_ext
    ext f α
    sorry

/-- Conjugation by a morphism in a fiber induces the canonical isomorphism between the associated
abelian-group automorphism sheaves on the localized site `C/U`. -/
noncomputable def automorphismAddCommSheafConj
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y) :
    𝒮.automorphismAddCommSheaf hAbelian x ≅
      𝒮.automorphismAddCommSheaf hAbelian y := by
  let F := canonicalFiberPseudofunctor 𝒮.p
  let e : x ≅ y := asIso φ
  let conjIso := automorphismSheafConj φ
  refine
    { hom := Sheaf.homEquiv.symm ?_
      inv := Sheaf.homEquiv.symm ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · refine
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
        naturality := ?_ }
    intro X Y g
    ext α
    simpa using congr_fun ((Sheaf.homEquiv conjIso.hom).naturality g) α
  · refine
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
        naturality := ?_ }
    intro X Y g
    ext α
    simpa using congr_fun ((Sheaf.homEquiv conjIso.inv).naturality g) α
  · apply Sheaf.hom_ext
    ext T α
    exact congr_fun (congr_app (congrArg Sheaf.homEquiv conjIso.hom_inv_id) T) α
  · apply Sheaf.hom_ext
    ext T α
    exact congr_fun (congr_app (congrArg Sheaf.homEquiv conjIso.inv_hom_id) T) α

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

-- Proof sketch: first use that in a gerbe any two local objects become locally isomorphic; since
-- the automorphism sheaves are abelian, conjugation is independent of the chosen local
-- isomorphism, so these local automorphism sheaves glue canonically on overlaps. Then use the
-- gluing lemmas for sheaves on the site and on its localizations to descend the resulting local
-- systems to a single global sheaf of abelian groups whose restriction to each `C/U` identifies
-- with the corresponding automorphism sheaf.
/-- Lemma 8.11.8: if `𝒮` is a gerbe over the site `(C, J)` and every automorphism sheaf
`Aut[𝒮](x)` is canonically abelian for its native composition law, then there exists a sheaf `𝒢`
of abelian groups on `C` whose restriction to each localized site `C/U` is identified with
the canonical abelian-group automorphism sheaf attached to `x`, compatibly with conjugation by
morphisms in the fiber over `U`. -/
theorem exists_gerbe_band_of_abelian_automorphism_sheaves
    (hGerbe : IsGerbe J 𝒮.p)
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := sorry

end CategoryTheory
