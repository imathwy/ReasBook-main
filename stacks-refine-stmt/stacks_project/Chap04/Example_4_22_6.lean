import Mathlib
import stacks_project.Chap04.Remark_4_22_7

open CategoryTheory Limits Opposite
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Example 4.22.6:
- primary domain: sequential inverse systems as source-facing models for morphisms in the
  pro-category of `C`.
- inspected owner-level declarations:
  `OrderHom.toFunctor`,
  `proObjectHomEquivLimitProSystemHomColimitFunctor`,
  `Types.sectionsEquiv`,
  `Types.limitEquivSections`,
  `Limits.colimitObjIsoColimitCompEvaluation`.
- best owner abstraction:
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.

Primitive-vs-derived split:
  `reindex.toFunctor.op ⋙ X ⟶ Y`.
- derived API: the level maps `X_{reindex(n)} ⟶ Y_n` and their compatibility squares.

Source/core/bridge triage:
- `source-facing`: `SequentialProObjectMorphismRep X Y`, consisting canonically of a reindexing
  order hom and the induced natural transformation of sequential inverse systems.
- `core/canonical`: the pro-object morphism type
  `(colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0})`
  between the associated sequential pro-objects, together with its plain-limit owner
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.
- `bridge/view`: the inverse-limit point `SequentialProObjectMorphismRep.toLimitHom`, built from
  the stagewise Hom-colimit classes via the canonical `Types.Limit.mk` constructor. -/

/-- A representative of a morphism between sequential inverse systems consists of a monotone
reindexing `m : ℕ → ℕ` together with compatible level maps `X_{m(n)} ⟶ Y_n`. -/
structure SequentialProObjectMorphismRep {C : Type u} [Category.{v} C] (X Y : ℕᵒᵖ ⥤ C) where
  reindex : ℕ →o ℕ
  hom : reindex.toFunctor.op ⋙ X ⟶ Y

namespace SequentialProObjectMorphismRep

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- The level map associated to a sequential representative at stage `n`. -/
abbrev map (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    X.obj (op (r.reindex n)) ⟶ Y.obj (op n) :=
  r.hom.app (op n)

/-- The naturality square for the level maps of a sequential representative. -/
theorem comm (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ} (h : n ≤ n') :
    CommSq (X.map (homOfLE (r.reindex.monotone h)).op) (r.map n') (r.map n)
      (Y.map (homOfLE h).op) := by
  refine CommSq.mk ?_
  simpa using r.hom.naturality (homOfLE h).op

/-- Build a sequential representative from its source-facing coordinate data. -/
private def ofMaps (reindex : ℕ →o ℕ)
    (map : ∀ n : ℕ, X.obj (op (reindex n)) ⟶ Y.obj (op n))
    (comm : ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE (reindex.monotone h)).op ≫ map n =
        map n' ≫ Y.map (homOfLE h).op) :
    SequentialProObjectMorphismRep X Y where
  reindex := reindex
  hom :=
    { app := fun n ↦ map n.unop
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using comm h }

/-- A natural transformation of sequential inverse systems gives the corresponding sequential
representative with identity reindexing. -/
def ofNatTrans (α : X ⟶ Y) : SequentialProObjectMorphismRep X Y :=
  ofMaps OrderHom.id
    (fun n ↦ α.app (op n))
    (fun _ _ h ↦ by
      exact α.naturality (homOfLE h).op)

/-- The canonical `ℕᵒᵖ` presentation of a sequential inverse system indexed by `OrderDual ℕ`. -/
abbrev ofOrderDualNat {C : Type u} [Category.{v} C] (F : OrderDual ℕ ⥤ C) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (fun n ↦ F.map (homOfLE (Nat.le_succ n)))

/-- A morphism of sequential inverse systems indexed by `OrderDual ℕ` gives the corresponding
sequential pro-object representative between their canonical `ℕᵒᵖ` presentations. -/
def ofOrderDualNatTrans {C : Type u} [Category.{v} C] {A B : OrderDual ℕ ⥤ C} (α : A ⟶ B) :
    SequentialProObjectMorphismRep (ofOrderDualNat A) (ofOrderDualNat B) :=
  ofNatTrans <|
    NatTrans.ofOpSequence
      (fun n ↦ α.app n)
      (fun n ↦ by
        simpa [ofOrderDualNat] using α.naturality (homOfLE (Nat.le_succ n)))

/-- The class in `colim_i Hom(X_i, Y_n)` represented by the `n`-th level map of a sequential
representative. -/
private noncomputable abbrev classOf (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    (proSystemHomColimitFunctor X).obj (Y.obj (op n)) :=
  (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))).inv <|
    colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
      (ULift.up (r.map n))

private theorem classOf_naturality (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ}
    (h : n ≤ n') :
    (proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n') = r.classOf n := by
  let τ :=
    ((Functor.whiskeringLeft ℕᵒᵖᵒᵖ Cᵒᵖ _).obj X.op).map
      (uliftYoneda.map (Y.map (homOfLE h).op))
  let eₙ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  let eₙ' := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n'))
  have hmap :
      colim.map τ
          (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
            (ULift.up (r.map n'))) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
          (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) :=
    Types.Colimit.ι_map_apply τ (op (op (r.reindex n'))) (ULift.up (r.map n'))
  have hcolim :
      colim.map τ (eₙ'.hom (r.classOf n')) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) := by
    calc
      colim.map τ (eₙ'.hom (r.classOf n')) =
          colim.map τ
            (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
              (ULift.up (r.map n'))) := by
                simp [classOf, eₙ']
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
            (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) := hmap
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
            (ULift.up (r.map n)) := by
              symm
              refine Types.colimit_sound (((homOfLE (r.reindex.monotone h)).op).op) ?_
              simp [τ, (r.comm h).w]
  have hleft :
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colim.map τ (eₙ'.hom (r.classOf n')) := by
    change
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colimMap ((X.op ⋙ uliftCoyoneda).whiskerLeft ((evaluation _ _).map (Y.map (homOfLE h).op)))
          (eₙ'.hom (r.classOf n'))
    simpa [eₙ, eₙ', proSystemHomColimitFunctor] using
      congrFun
        (colimit_map_colimitObjIsoColimitCompEvaluation_hom
          (X.op ⋙ uliftCoyoneda) (Y.map (homOfLE h).op)) (r.classOf n')
  have hright :
      colim.map τ (eₙ'.hom (r.classOf n')) = eₙ.hom (r.classOf n) := by
    exact hcolim.trans <| by simp [classOf, eₙ]
  exact eₙ.toEquiv.injective (hleft.trans hright)

/-- The inverse-limit presentation of the pro-object morphism represented by `r`. -/
private noncomputable def toLimitHom (r : SequentialProObjectMorphismRep X Y) :
    limit (Y ⋙ proSystemHomColimitFunctor X) :=
  Types.Limit.mk _ (fun n ↦ r.classOf n.unop) fun i j g ↦ by
    let h : j.unop ≤ i.unop := leOfHom g.unop
    simpa [h] using r.classOf_naturality h

/-- A sequential representative determines a morphism between the associated sequential
pro-objects. -/
noncomputable def toProObjectHom (r : SequentialProObjectMorphismRep X Y) :
    colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0} :=
  (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm r.toLimitHom

/-- Refining the source stages of a sequential representative along a larger monotone reindexing
does not change the underlying level maps in the Hom-colimits. -/
private theorem refine_comm
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) {n n' : ℕ} (h : n ≤ n') :
    X.map (homOfLE (reindex'.monotone h)).op ≫ (X.map (homOfLE (hle n)).op ≫ r.map n) =
      (X.map (homOfLE (hle n')).op ≫ r.map n') ≫ Y.map (homOfLE h).op := by
  sorry

/-- Enlarging the chosen source stage at each target level gives a canonical refinement of a
sequential representative. -/
private def refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    SequentialProObjectMorphismRep X Y :=
  ofMaps reindex'
    (fun n ↦ X.map (homOfLE (hle n)).op ≫ r.map n)
    (fun _ _ h ↦ refine_comm r reindex' hle h)

/-- The class represented at level `n` is unchanged by passing to a larger source stage. -/
private theorem classOf_refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) (n : ℕ) :
    (r.refine reindex' hle).classOf n = r.classOf n := by
  sorry

/-- Refinement does not change the represented inverse-limit point. -/
private theorem refine_toLimitHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toLimitHom = r.toLimitHom := by
  apply Types.limit_ext
  intro n
  simp [toLimitHom, r.classOf_refine reindex' hle n.unop]

/-- Refinement does not change the represented morphism between the associated pro-objects. -/
private theorem refine_toProObjectHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toProObjectHom = r.toProObjectHom := by
  simpa [toProObjectHom] using
    congrArg
      (fun η ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm η)
      (r.refine_toLimitHom reindex' hle)

/-- Two sequential representatives are equivalent when, after passing to a common monotone
refinement, their level maps agree. -/
def Equivalent (r₁ r₂ : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ reindex' : ℕ →o ℕ,
    ∃ h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n,
      ∃ h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n,
        ∀ n : ℕ,
          X.map (homOfLE (h₁ n)).op ≫ r₁.map n =
            X.map (homOfLE (h₂ n)).op ≫ r₂.map n

/-- The identity representative of a sequential inverse system. -/
def idRep (X : ℕᵒᵖ ⥤ C) : SequentialProObjectMorphismRep X X :=
  ofMaps OrderHom.id
    (fun n ↦ 𝟙 (X.obj (op n)))
    (fun _ _ h ↦ by simp)

/-- Compatibility of the composite representative with transition morphisms. -/
theorem compRep_comm
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
          (r.map (s.reindex n) ≫ s.map n) =
        (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
  intro n n' h
  calc
    X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
        (r.map (s.reindex n) ≫ s.map n) =
      (X.map (homOfLE (r.reindex.monotone (s.reindex.monotone h))).op ≫
          r.map (s.reindex n)) ≫ s.map n := by simp [Category.assoc]
    _ = (r.map (s.reindex n') ≫ Y.map (homOfLE (s.reindex.monotone h)).op) ≫ s.map n := by
      simp [Category.assoc, (r.comm (s.reindex.monotone h)).w]
    _ = r.map (s.reindex n') ≫
        (Y.map (homOfLE (s.reindex.monotone h)).op ≫ s.map n) := by
      simp [Category.assoc]
    _ = r.map (s.reindex n') ≫ (s.map n' ≫ Z.map (homOfLE h).op) := by
      simp [(s.comm h).w]
    _ = (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
      simp [Category.assoc]

/-- Composition of sequential representatives of pro-object morphisms. -/
def compRep
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    SequentialProObjectMorphismRep X Z :=
  ofMaps (r.reindex.comp s.reindex)
    (fun n ↦ r.map (s.reindex n) ≫ s.map n)
    (compRep_comm r s)

/-- A representative is a pro-isomorphism if it admits an inverse up to common-refinement
equivalence. -/
def IsProIsomorphism (r : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ s : SequentialProObjectMorphismRep Y X,
    Equivalent (compRep r s) (idRep X) ∧ Equivalent (compRep s r) (idRep Y)

/-- A pro-isomorphism induces a bijection on the Hom-colimit evaluation at every test object. -/
theorem isProIsomorphism_toProObjectHom_app_bijective
    {r : SequentialProObjectMorphismRep X Y} (hr : r.IsProIsomorphism) (Z : C) :
    Function.Bijective (r.toProObjectHom.app Z) := by
  sorry

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

-- Proof sketch: choose, for each `n`, a stage of `X` and a map to `Y_n` representing the `n`-th
-- Hom-colimit class of `η`; then enlarge inductively so the chosen stages are monotone and the
-- compatibility squares commute.
/-- Example 4.22.6: every morphism between the associated sequential pro-objects is represented by
a monotone reindexing and compatible level maps. -/
theorem exists_representative
    (η : colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0}) :
    ∃ r : SequentialProObjectMorphismRep X Y, r.toProObjectHom = η := by
  sorry

-- Proof sketch: one direction follows by refining both representatives to a common larger
-- monotone sequence and comparing the resulting stage maps; the converse uses that equality after
-- such a common refinement gives the same classes in every Hom-colimit.
/-- Companion to Example 4.22.6: two sequential representatives define the same pro-object
morphism exactly when, after passing to a common monotone refinement, their level maps become
equal. -/
theorem represents_eq_iff_equivalent
    (r₁ r₂ : SequentialProObjectMorphismRep X Y) :
    r₁.toProObjectHom = r₂.toProObjectHom ↔ r₁.Equivalent r₂ := by
  sorry

end

end CategoryTheory
