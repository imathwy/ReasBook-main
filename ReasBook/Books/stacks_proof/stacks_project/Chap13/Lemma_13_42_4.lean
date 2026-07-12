import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap04.Lemma_4_22_10
import StacksProject_2024.Chap12.Definition_12_31_2

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open SequentialProObjectMorphismRep
open scoped CategoryTheory ZeroObject

universe uC vC uD vD

namespace CategoryTheory

/-- Helper for Lemma 13.42.4: a diagram has pro-object value `X` when its Hom-colimit functor is
corepresented by `X`. -/
abbrev HasProObjectValue
    {I : Type uC} {C : Type uD} [Category.{vC} I] [Category.{vD} C]
    (M : I ⥤ C) (X : C) : Prop :=
  Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X)

namespace SequentialProObjectMorphismRep

variable {C : Type uD} [Category.{vD} C]

/-- Helper for Lemma 13.42.4: a natural transformation of sequential inverse systems gives the
identity-reindex representative on the associated pro-objects. -/
abbrev ofNatTrans {X Y : ℕᵒᵖ ⥤ C} (α : X ⟶ Y) :
    SequentialProObjectMorphismRep X Y where
  reindex := OrderHom.id
  hom := by
    simpa using α

/-- Helper for Lemma 13.42.4: an `OrderDual ℕ` natural transformation is first reindexed to the
canonical sequential tower and then packaged by `ofNatTrans`. -/
abbrev ofOrderDualNatTrans {X Y : OrderDual ℕ ⥤ C} (α : X ⟶ Y) :
    SequentialProObjectMorphismRep
      (((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙ X)
      (((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙ Y) :=
  ofNatTrans (Functor.whiskerLeft ((CategoryTheory.orderDualEquivalence ℕ).inverse) α)

end SequentialProObjectMorphismRep

/-
Domain-style sampling for Lemma 13.42.4:
- primary domain: sequential inverse systems in a pretriangulated category, viewed through the
  Chapter 4 owner for sequential pro-object morphisms and the Hom-colimit functor
  `X ↦ colimₙ Hom(-, X)`.
- inspected owner-level declarations:
  `HasProObjectValue`,
  `SequentialProObjectMorphismRep`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective`,
  `Functor.whiskerLeft`,
  `Triangle.π₁Toπ₂`.
- best owner abstraction: the sequential pro-object morphism represented by the first maps in the
  triangle system, obtained from `Functor.whiskerLeft T Triangle.π₁Toπ₂` via
  `SequentialProObjectMorphismRep.ofOrderDualNatTrans`; the source-facing owner statement is that
  this representative is a pro-isomorphism, and its evaluation on a test object is the canonical
  Hom-colimit map after passing to the standard `ℕᵒᵖ` presentation of the sequential system.
- primitive data: the triangle system `T`, the first-to-second natural transformation
  `Functor.whiskerLeft T Triangle.π₁Toπ₂`.
- derived API: the pro-isomorphism owner
  `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).IsProIsomorphism`, its evaluated
  morphism `(SequentialProObjectMorphismRep.ofOrderDualNatTrans ...).toProObjectHom.app X`, and
  the source-facing pro-zero condition `HasProObjectValue (T ⋙ Triangle.π₃) (0 : D)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, asserting that a pro-zero third term system forces the maps
  `Aₙ ⟶ Bₙ` to define a pro-isomorphism.
- `core/canonical`: `HasProObjectValue` and `SequentialProObjectMorphismRep`.
- `bridge/view`: `SequentialProObjectMorphismRep.ofOrderDualNatTrans` and
  `SequentialProObjectMorphismRep.toProObjectHom`. -/

section

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Helper for Lemma 13.42.4: exactness of a distinguished triangle at the middle term turns a
vanishing composite `T.mor₁ ≫ g = 0` into a factorization of `g` through `T.mor₂`. -/
private theorem existsFactorThroughThird_of_compFirst_eq_zero
    (T : Triangle D) (hT : T ∈ distTriang D)
    {X : D} (g : T.obj₂ ⟶ X) (hg : T.mor₁ ≫ g = 0) :
    ∃ u : T.obj₃ ⟶ X, T.mor₂ ≫ u = g := by
  -- Proof comment: this is exactly the `yoneda_exact₂` factorization at `Hom(T.obj₂, X)`.
  obtain ⟨u, hu⟩ := T.yoneda_exact₂ hT g hg
  exact ⟨u, hu.symm⟩

/-- Helper for Lemma 13.42.4: if the shifted connecting morphism vanishes, then the map out of
`T.obj₁` lifts along `T.mor₁`. -/
private theorem existsLiftAlongFirst_of_thirdShiftComp_eq_zero
    (T : Triangle D) (hT : T ∈ distTriang D)
    {X : D} (f : T.obj₁ ⟶ X)
    (hf : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0) :
    ∃ u : T.obj₂ ⟶ X, T.mor₁ ≫ u = f := by
  let S := shiftFunctor D (1 : ℤ)
  have hf' : T.mor₃ ≫ (-S.map f) = 0 := by
    rw [Preadditive.comp_neg, hf, neg_zero]
  obtain ⟨uShift, huShift⟩ := (T.rotate.rotate).yoneda_exact₂
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) (-S.map f) hf'
  obtain ⟨u, rfl⟩ := S.map_surjective uShift
  -- Proof comment: after unshifting the exactness factorization, the desired lift is the
  -- preimage `u : T.obj₂ ⟶ X` of the shifted factor.
  refine ⟨u, ?_⟩
  apply S.map_injective
  simpa [S, Functor.map_comp] using huShift.symm

/-- Helper for Lemma 13.42.4: applying `proSystemHomColimitFunctor` to a represented stage class
turns it into the class of the composite stage map. -/
private theorem stageClass_map
    {M : ℕᵒᵖ ⥤ D} {X W : D} {n : ℕ} (s : M.obj (op n) ⟶ X) (g : X ⟶ W) :
    (proSystemHomColimitFunctor M).map g
      ((colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) X).inv
        (colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up s))) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) W).inv
        (colimit.ι (M.op ⋙ uliftYoneda.obj W) (op (op n)) (ULift.up (s ≫ g))) := by
  -- Proof comment: move the functorial action of `g` across the evaluation/colimit comparison,
  -- then rewrite the transported generator by `colimit.ι_map`.
  have hmap :=
    CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
      (F := M.op ⋙ uliftCoyoneda.{0}) (f := g)
  have hmap' := congrFun hmap
    (colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up s))
  have hι := congrFun
    (CategoryTheory.Limits.colimit.ι_map
      ((M.op ⋙ uliftCoyoneda.{0}).whiskerLeft
        ((evaluation D (Type (max 0 vD))).map g))
      (op (op n)))
    (ULift.up s)
  have hι' :
      colimMap ((M.op ⋙ uliftCoyoneda.{0}).whiskerLeft
          ((evaluation D (Type (max 0 vD))).map g))
          (colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up s)) =
        colimit.ι (M.op ⋙ uliftYoneda.obj W) (op (op n)) (ULift.up (s ≫ g)) := by
    simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hι
  simpa using hmap'.trans
    (congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) W).inv hι')

/-- Helper for Lemma 13.42.4: the raw colimit class represented by a stage map. -/
private noncomputable abbrev representedClass
    {M : SequentialInverseSystem D} {X : D} {n : ℕ} (f : M.obj (op n) ⟶ X) :
    (proSystemHomColimitFunctor M).obj X :=
  (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) X).inv
    (colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up f))

/-- Helper for Lemma 13.42.4: evaluating `(ofNatTrans α).toProObjectHom` on a represented stage
class gives the represented class of the composite with the stage map `α.app (op n)`. -/
private theorem ofNatTrans_app_representedClass
    {A B : SequentialInverseSystem D} (α : A ⟶ B) {X : D} {n : ℕ}
    (g : B.obj (op n) ⟶ X) :
    ((ofNatTrans α).toProObjectHom.app X) (representedClass (M := B) g) =
      representedClass (M := A) (α.app (op n) ≫ g) := by
  -- Proof comment: `ofNatTrans α` is represented by the literal stage maps `α.app (op n)`, so
  -- the owner evaluation formula reduces definitionally on a represented generator.
  rfl

/-- Helper for Lemma 13.42.4: equality after passing to a common later stage gives equality of
represented colimit classes. -/
private theorem representedClass_eq_of_transition_eq
    {M : SequentialInverseSystem D} {X : D} {n n' k : ℕ}
    (hnk : n ≤ k) (hn'k : n' ≤ k)
    {f : M.obj (op n) ⟶ X} {g : M.obj (op n') ⟶ X}
    (hfg : M.transitionMap hnk ≫ f = M.transitionMap hn'k ≫ g) :
    representedClass (M := M) f = representedClass (M := M) g := by
  let e := colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) X
  apply e.toEquiv.injective
  -- Proof comment: move both represented classes to the raw Hom-colimit and transport them to
  -- the common later stage `k`.
  have hleft :
      e.hom (representedClass (M := M) f) =
        colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op k))
          (ULift.up (M.transitionMap hnk ≫ f)) := by
    calc
      e.hom (representedClass (M := M) f) =
          colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up f) := by
            simp [representedClass, e]
      _ =
          colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op k))
            (ULift.up (M.transitionMap hnk ≫ f)) := by
              refine Types.colimit_sound (((homOfLE hnk).op).op) ?_
              simp [SequentialInverseSystem.transitionMap]
  have hright :
      e.hom (representedClass (M := M) g) =
        colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op k))
          (ULift.up (M.transitionMap hn'k ≫ g)) := by
    calc
      e.hom (representedClass (M := M) g) =
          colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n'))
            (ULift.up g) := by
              simp [representedClass, e]
      _ =
          colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op k))
            (ULift.up (M.transitionMap hn'k ≫ g)) := by
              refine Types.colimit_sound (((homOfLE hn'k).op).op) ?_
              simp [SequentialInverseSystem.transitionMap]
  exact hleft.trans (hfg ▸ hright.symm)

/-- Helper for Lemma 13.42.4: every Hom-colimit class is represented by a concrete stage map. -/
private theorem exists_representedClass
    {M : SequentialInverseSystem D} {X : D}
    (z : (proSystemHomColimitFunctor M).obj X) :
    ∃ n : ℕ, ∃ f : M.obj (op n) ⟶ X, representedClass (M := M) f = z := by
  let e := colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) X
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective' (e.hom z)
  refine ⟨j.unop.unop, y.down, ?_⟩
  apply e.toEquiv.injective
  simpa [representedClass, e] using hy

/-- Helper for Lemma 13.42.4: equality of represented colimit classes is witnessed at a common
later stage. -/
private theorem exists_common_stage_of_representedClass_eq
    {M : SequentialInverseSystem D} {X : D} {n n' : ℕ}
    {f : M.obj (op n) ⟶ X} {g : M.obj (op n') ⟶ X}
    (hfg : representedClass (M := M) f = representedClass (M := M) g) :
    ∃ k : ℕ, ∃ hnk : n ≤ k, ∃ hn'k : n' ≤ k,
      M.transitionMap hnk ≫ f = M.transitionMap hn'k ≫ g := by
  let e := colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{0}) X
  have hcolim :
      colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n)) (ULift.up f) =
        colimit.ι (M.op ⋙ uliftYoneda.obj X) (op (op n')) (ULift.up g) := by
    simpa [representedClass, e] using congrArg e.hom hfg
  obtain ⟨k, ik, jk, hk⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (F := M.op ⋙ uliftYoneda.obj X)
      (colimit.isColimit (M.op ⋙ uliftYoneda.obj X))).mp hcolim
  refine ⟨k.unop.unop, leOfHom ik.unop.unop, leOfHom jk.unop.unop, ?_⟩
  -- Proof comment: unlift the filtered-colimit equality and read the structure maps as the
  -- sequential transition morphisms.
  simpa [SequentialInverseSystem.transitionMap, FunctorToTypes.map_comp_apply, Category.assoc] using
    congrArg ULift.down hk

/-- Helper for Lemma 13.42.4: transition morphisms in a sequential inverse system factor through
every intermediate stage. -/
private theorem transitionMap_factor
    {M : SequentialInverseSystem D} {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    M.transitionMap (Nat.le_trans hij hjk) =
      M.transitionMap hjk ≫ M.transitionMap hij := by
  have hcomp :
      (homOfLE (Nat.le_trans hij hjk)).op =
        (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap] using congrArg M.map hcomp

/-- Helper for Lemma 13.42.4: if an `OrderDual ℕ` diagram has pro-object value `0`, then every
stage transition eventually becomes zero. -/
private theorem eventuallyZeroTransition_of_hasProObjectValue_zero
    {M : OrderDual ℕ ⥤ D} (hM : HasProObjectValue M (0 : D)) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n ≤ m, M.map (homOfLE hnm) = 0 := by
  intro n
  obtain ⟨c, hcpt, hc⟩ :=
    (corepresentableBy_iff_exists_essentiallyConstant_limitCone (M := M) (0 : D)).1 hM
  rcases (isEssentiallyConstantCofilteredCone_iff c.cone).1 hc with ⟨i, σ, hσ⟩
  rcases hσ n with ⟨m, mi, mn, hmn⟩
  let hzeroObj : IsZero c.cone.pt := IsZero.of_iso (isZero_zero D) (eqToIso hcpt)
  have hzeroRet : σ.retraction = 0 := by
    exact hzeroObj.eq_of_tgt _ _
  have hzeroLeft : M.map mi ≫ σ.retraction = 0 := by
    exact hzeroObj.eq_of_tgt _ _
  have hzeroComp : M.map mi ≫ σ.retraction ≫ c.cone.π.app n = 0 := by
    simpa [Category.assoc] using
      (congrArg (fun t ↦ t ≫ c.cone.π.app n) hzeroLeft).trans zero_comp
  refine ⟨m, leOfHom mn, ?_⟩
  exact hmn.trans hzeroComp

/-- Helper for Lemma 13.42.4: after passing to a stage where the third transition map vanishes,
the first transition map lifts along the first arrow of that later distinguished triangle. -/
private theorem existsInverseStageLiftOfZeroThirdTransition
    {T : OrderDual ℕ ⥤ Triangle D}
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      ∃ u : (T.obj m).obj₂ ⟶ (T.obj n).obj₁,
        (T.obj m).mor₁ ≫ u = (T.map (homOfLE hnm)).hom₁ := by
  obtain ⟨m, hnm, hzero⟩ :=
    eventuallyZeroTransition_of_hasProObjectValue_zero (M := T ⋙ Triangle.π₃) h₃ n
  have hzero₃ : (T.map (homOfLE hnm)).hom₃ = 0 := by
    simpa using hzero
  have hshiftZero :
      (T.obj m).mor₃ ≫ ((T.map (homOfLE hnm)).hom₁)⟦(1 : ℤ)⟧' = 0 := by
    calc
      (T.obj m).mor₃ ≫ ((T.map (homOfLE hnm)).hom₁)⟦(1 : ℤ)⟧' =
          (T.map (homOfLE hnm)).hom₃ ≫ (T.obj n).mor₃ := by
            simpa using (T.map (homOfLE hnm)).comm₃
      _ = 0 := by simp [hzero₃]
  obtain ⟨u, hu⟩ :=
    existsLiftAlongFirst_of_thirdShiftComp_eq_zero (T := T.obj m)
      (hT m) ((T.map (homOfLE hnm)).hom₁) hshiftZero
  refine ⟨m, hnm, u, ?_⟩
  simpa using hu

/-- Helper for Lemma 13.42.4: `ofOrderDualNatTrans` is just `ofNatTrans` after the single
canonical reindexing from `OrderDual ℕ` to `ℕᵒᵖ`. -/
private theorem ofOrderDualNatTrans_def
    {X Y : OrderDual ℕ ⥤ D} (α : X ⟶ Y) :
    ofOrderDualNatTrans α =
      ofNatTrans
        (Functor.whiskerLeft ((CategoryTheory.orderDualEquivalence ℕ).inverse) α) := by
  -- Proof comment: this is only the definitional expansion of the abbreviation and gives a
  -- stable normal form for later rewrites.
  rfl

/-- Helper for Lemma 13.42.4: composition of sequential representatives matches composition of
their induced pro-object morphisms. -/
private theorem compRep_toProObjectHom
    {X Y Z : ℕᵒᵖ ⥤ D}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    (compRep r s).toProObjectHom = r.toProObjectHom ≫ s.toProObjectHom := by
  -- Proof comment: both sides evaluate represented stage classes by the same stagewise composite
  -- `r.map (s.reindex n) ≫ s.map n`, so the resulting natural transformations agree pointwise.
  ext W x
  rfl

/-- Helper for Lemma 13.42.4: an isomorphism on the owner-level pro-object morphism of
`ofNatTrans α` already yields a representative-level inverse witness. -/
private theorem ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom
    {X Y : SequentialInverseSystem D} (α : X ⟶ Y)
    (hαIso : IsIso (ofNatTrans α).toProObjectHom) :
    (ofNatTrans α).IsProIsomorphism := by
  let η := (ofNatTrans α).toProObjectHom
  rcases exists_representative (inv η) with ⟨s, hs⟩
  refine ⟨s, ?_, ?_⟩
  · -- Proof comment: the chosen representative of `inv η` is a left inverse in the pro-category,
    -- so the composite is equivalent to the identity representative on the source tower.
    apply (represents_eq_iff_equivalent (compRep (ofNatTrans α) s) (idRep X)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.hom_inv_id η
  · -- Proof comment: the same representative is also a right inverse, giving the target-side
    -- equivalence to the identity representative on the target tower.
    apply (represents_eq_iff_equivalent (compRep s (ofNatTrans α)) (idRep Y)).1
    rw [compRep_toProObjectHom]
    rw [hs]
    exact IsIso.inv_hom_id η

/-- Companion theorem: under the pro-zero hypothesis on `(Cₙ)`, the induced map
`colimₙ Hom(Bₙ, X) → colimₙ Hom(Aₙ, X)` is bijective for every test object `X`. -/
theorem triangleFirstToSecond_toProObjectHom_app_bijective_of_proZero_third
    {T : OrderDual ℕ ⥤ Triangle D}
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D))
    (X : D) :
    Function.Bijective
      ((ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).toProObjectHom.app X) :=
  let A : SequentialInverseSystem D :=
    ((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙ (T ⋙ Triangle.π₁)
  let B : SequentialInverseSystem D :=
    ((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙ (T ⋙ Triangle.π₂)
  let C : SequentialInverseSystem D :=
    ((CategoryTheory.orderDualEquivalence ℕ).inverse) ⋙ (T ⋙ Triangle.π₃)
  let αNat : A ⟶ B :=
    Functor.whiskerLeft ((CategoryTheory.orderDualEquivalence ℕ).inverse)
      (Functor.whiskerLeft T Triangle.π₁Toπ₂)
  let η := (ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).toProObjectHom.app X
  have hη :
      η = (ofNatTrans αNat).toProObjectHom.app X := by
    simp [η, αNat, ofOrderDualNatTrans_def]
  refine ⟨?_, ?_⟩
  · intro z₁ z₂ hz
    obtain ⟨i, f, rfl⟩ := exists_representedClass (M := B) z₁
    obtain ⟨j, g, rfl⟩ := exists_representedClass (M := B) z₂
    -- Proof comment: equality after applying `η` means the two composites through the first maps
    -- agree in the `A`-Hom colimit; pass to a common later stage and kill the remaining
    -- difference through the pro-zero third tower.
    have himage :
        representedClass (M := A) (αNat.app (op i) ≫ f) =
          representedClass (M := A) (αNat.app (op j) ≫ g) := by
      simpa [hη] using hz
    obtain ⟨k, hik, hjk, hk⟩ :=
      exists_common_stage_of_representedClass_eq (M := A) himage
    have hnat_i :
        A.transitionMap hik ≫ αNat.app (op i) =
          αNat.app (op k) ≫ B.transitionMap hik := by
      simpa [A, B, αNat, SequentialInverseSystem.transitionMap] using
        αNat.naturality (homOfLE hik).op
    have hnat_j :
        A.transitionMap hjk ≫ αNat.app (op j) =
          αNat.app (op k) ≫ B.transitionMap hjk := by
      simpa [A, B, αNat, SequentialInverseSystem.transitionMap] using
        αNat.naturality (homOfLE hjk).op
    have hk' :
        αNat.app (op k) ≫ (B.transitionMap hik ≫ f) =
          αNat.app (op k) ≫ (B.transitionMap hjk ≫ g) := by
      calc
        αNat.app (op k) ≫ (B.transitionMap hik ≫ f) =
            (A.transitionMap hik ≫ αNat.app (op i)) ≫ f := by
              rw [hnat_i]
              simp [Category.assoc]
        _ = A.transitionMap hik ≫ (αNat.app (op i) ≫ f) := by
              simp [Category.assoc]
        _ = A.transitionMap hjk ≫ (αNat.app (op j) ≫ g) := hk
        _ = (A.transitionMap hjk ≫ αNat.app (op j)) ≫ g := by
              simp [Category.assoc]
        _ = αNat.app (op k) ≫ (B.transitionMap hjk ≫ g) := by
              rw [hnat_j]
              simp [Category.assoc]
    let d : B.obj (op k) ⟶ X := B.transitionMap hik ≫ f - B.transitionMap hjk ≫ g
    have hd_zero : αNat.app (op k) ≫ d = 0 := by
      rw [Preadditive.comp_sub, sub_eq_zero]
      simpa [d, Category.assoc] using hk'
    have hd_zero' : (T.obj k).mor₁ ≫ d = 0 := by
      simpa [B, αNat, d] using hd_zero
    obtain ⟨u, hu⟩ :=
      existsFactorThroughThird_of_compFirst_eq_zero (T := T.obj k) (hT k) d hd_zero'
    obtain ⟨l, hkl, hzero⟩ :=
      eventuallyZeroTransition_of_hasProObjectValue_zero (M := T ⋙ Triangle.π₃) h₃ k
    have hzeroC : C.transitionMap hkl = 0 := by
      simpa [C, SequentialInverseSystem.transitionMap] using hzero
    have hcomm₂ :
        B.transitionMap hkl ≫ (T.obj k).mor₂ =
          (T.obj l).mor₂ ≫ C.transitionMap hkl := by
      simpa [B, C, SequentialInverseSystem.transitionMap] using
        (T.map (homOfLE hkl)).comm₂
    have hkill :
        B.transitionMap hkl ≫ d = 0 := by
      calc
        B.transitionMap hkl ≫ d =
            B.transitionMap hkl ≫ ((T.obj k).mor₂ ≫ u) := by rw [hu]
        _ = (B.transitionMap hkl ≫ (T.obj k).mor₂) ≫ u := by
              simp [Category.assoc]
        _ = ((T.obj l).mor₂ ≫ C.transitionMap hkl) ≫ u := by
              rw [hcomm₂]
        _ = 0 := by
              simp [hzeroC, Category.assoc]
    have hstage_eq :
        B.transitionMap (Nat.le_trans hik hkl) ≫ f =
          B.transitionMap (Nat.le_trans hjk hkl) ≫ g := by
      apply sub_eq_zero.mp
      calc
        B.transitionMap (Nat.le_trans hik hkl) ≫ f -
            B.transitionMap (Nat.le_trans hjk hkl) ≫ g =
              B.transitionMap hkl ≫ d := by
                simp [d, transitionMap_factor, Category.assoc, Preadditive.comp_sub]
        _ = 0 := hkill
    exact
      representedClass_eq_of_transition_eq (M := B)
        (hnk := Nat.le_trans hik hkl) (hn'k := Nat.le_trans hjk hkl) hstage_eq
  · intro z
    obtain ⟨n, f, rfl⟩ := exists_representedClass (M := A) z
    obtain ⟨m, hnm, u, hu⟩ :=
      existsInverseStageLiftOfZeroThirdTransition (T := T) hT h₃ n
    -- Proof comment: choose a late-stage lift of the source transition map through the first map
    -- of the distinguished triangle; the represented class of `u ≫ f` is then a preimage.
    refine ⟨representedClass (M := B) (u ≫ f), ?_⟩
    calc
      η (representedClass (M := B) (u ≫ f)) =
          representedClass (M := A) (αNat.app (op m) ≫ (u ≫ f)) := by
            simpa [hη] using
              ofNatTrans_app_representedClass (α := αNat) (X := X) (n := m) (u ≫ f)
      _ = representedClass (M := A) (A.transitionMap hnm ≫ f) := by
            congr 1
            simpa [A, αNat, Category.assoc] using hu
      _ = representedClass (M := A) f := by
            exact
              representedClass_eq_of_transition_eq (M := A)
                (hnk := Nat.le_refl m) (hn'k := hnm) (by simp)

/-- Lemma 13.42.4: for a sequential inverse system of distinguished triangles
`Aₙ ⟶ Bₙ ⟶ Cₙ ⟶ Aₙ⟦1⟧`, if the system `(Cₙ)` is essentially constant as a pro-object with value
`0`, then the maps `Aₙ ⟶ Bₙ` determine a pro-isomorphism between the pro-objects `(Aₙ)` and
`(Bₙ)`. -/
@[stacks 0G3C]
theorem triangleFirstToSecond_isProIsomorphism_of_proZero_third
    {T : OrderDual ℕ ⥤ Triangle D}
    (hT : ∀ n : ℕ, T.obj n ∈ distTriang D)
    (h₃ : HasProObjectValue (T ⋙ Triangle.π₃) (0 : D)) :
    (ofOrderDualNatTrans (Functor.whiskerLeft T Triangle.π₁Toπ₂)).IsProIsomorphism := by
  let αNat :=
    Functor.whiskerLeft ((CategoryTheory.orderDualEquivalence ℕ).inverse)
      (Functor.whiskerLeft T Triangle.π₁Toπ₂)
  let η := (ofNatTrans αNat).toProObjectHom
  letI : ∀ X : D, IsIso (η.app X) := fun X ↦
    (CategoryTheory.isIso_iff_bijective (η.app X)).2
      (triangleFirstToSecond_toProObjectHom_app_bijective_of_proZero_third (T := T) hT h₃ X)
  have hηIso : IsIso η := NatIso.isIso_of_isIso_app η
  -- Proof comment: once each Hom-colimit evaluation map is bijective, the owner morphism is an
  -- isomorphism of functors, and the Chapter 4 inverse-representative bridge upgrades that to a
  -- representative-level pro-isomorphism.
  simpa [SequentialProObjectMorphismRep.ofOrderDualNatTrans, αNat] using
    ofNatTrans_isProIsomorphism_of_isIso_toProObjectHom αNat hηIso

end

end CategoryTheory
