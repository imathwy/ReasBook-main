import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.LargeColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import StacksProject_2024.Chap18.Definition_18_4_1

open CategoryTheory
open CategoryTheory.Limits
open SimplicialObject.Augmented
open AlgebraicTopology
open Opposite
open scoped ZeroObject

noncomputable section

universe w u

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.9.4:
- primary domain: Čech simplicial objects and their alternating-face-map chain complexes in
  additive presheaves;
- sampled owner declarations:
  `ℤ_ G`,
  `FormalCoproduct.eval`,
  `alternatingFaceMapComplex`,
  `HomologicalComplex.homology`;
- best owner abstraction: the source-facing chain-complex owner
  `freeAbelianCechChainComplex family`, built from the Čech simplicial object by applying the
  chapter-18 free-abelian-presheaf owner whiskered to the presheaf category and then composed with
  `yoneda` before evaluating on the Čech nerve;
- primitive data: the family `family : ι → C`;
- derived API: the chain-complex owner `freeAbelianCechChainComplex family` and the
  positive-degree homology-vanishing theorem in successor-index form.

Source/core/bridge triage:
- `source-facing`: the vanishing of the positive-degree homology presheaves of the free-abelian
  Čech cover complex;
- `core/canonical`: `freeAbelianCechChainComplex family`;
- `bridge/view`: the internally inlined simplicial Čech object used to build
  `freeAbelianCechChainComplex family`. -/

private abbrev freeAbelianYoneda {C : Type u} [Category.{u} C] :
    C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

/-- Helper for Lemma 21.9.4: the set of lifts of `V` to the family `family`. -/
private def lift_index {C : Type u} [Category.{u} C] {U : C} {ι : Type w} (family : ι → Over U)
    (V : Over U) : Type (max u w) :=
  Σ i : ι, (V ⟶ family i)

/-- Helper for Lemma 21.9.4: forget a formal coproduct in `Type` to its indexing type. -/
private def formalCoproductIndexFunctor : FormalCoproduct.{w} (Type u) ⥤ Type (max u w) where
  obj X := ULift.{u} X.I
  map f x := ⟨f.f x.down⟩

/-- Helper for Lemma 21.9.4: the simplicial bar object on the lift set of `V`. -/
private abbrev liftBarSimplicialObject {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) (V : Over U) : SimplicialObject AddCommGrpCat.{max u w} :=
  ((FormalCoproduct.mk (lift_index family V) (fun _ ↦ (⊤_ (Type u)))).cech ⋙
    formalCoproductIndexFunctor ⋙ AddCommGrpCat.free)

/-- Helper for Lemma 21.9.4: the chain complex `ℤ[(lift_index family V)^{•+1}]`. -/
private abbrev liftBarChainComplex {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) (V : Over U) :
    ChainComplex AddCommGrpCat.{max u w} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat.{max u w}).obj (liftBarSimplicialObject family V)

/-- Helper for Lemma 21.9.4: maps into a product in `Over U` are the same as tuples of maps into
its factors. -/
private noncomputable def over_product_hom_equiv {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) (V : Over U) {α : Type*}
    [HasProductsOfShape α (Over U)] (f : α → ι) :
    (V ⟶ ∏ᶜ (family ∘ f)) ≃ ((a : α) → V ⟶ family (f a)) where
  -- The product projections extract the tuple of component morphisms.
  toFun g a := g ≫ Limits.Pi.π (family ∘ f) a
  -- The universal property of the product reassembles a tuple into a single morphism.
  invFun g := Limits.Pi.lift g
  left_inv g := by
    -- Two maps into a product agree once all projections agree.
    apply Limits.Pi.hom_ext
    intro a
    simpa using (Limits.Pi.lift_π (fun a ↦ g ≫ Limits.Pi.π (family ∘ f) a) a)
  right_inv g := by
    -- The reassembled map has the prescribed components by construction.
    funext a
    simpa using (Limits.Pi.lift_π g a)

/-- Helper for Lemma 21.9.4: a lift to a Čech power is the same as a tuple of lifts to the family.
-/
private noncomputable def lift_power_hom_equiv {C : Type u} [Category.{u} C] {U : C}
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) (V : Over U)
    {α : Type} [HasProductsOfShape α (Over U)] :
    (((FormalCoproduct.incl (Over U)).obj V) ⟶ (FormalCoproduct.mk ι family).power α) ≃
      (α → lift_index family V) := by
  -- First unwrap a map into the formal coproduct power as an index function together with a map
  -- into the corresponding product object.
  refine (FormalCoproduct.inclHomEquiv V ((FormalCoproduct.mk ι family).power α)).trans ?_
  refine
    { toFun := fun g a ↦
        ⟨g.1 a, (over_product_hom_equiv family V g.1 g.2) a⟩
      invFun := fun g ↦
        ⟨fun a ↦ (g a).1,
          (over_product_hom_equiv family V (fun a ↦ (g a).1)).symm (fun a ↦ (g a).2)⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨f, g⟩
    -- The index function is unchanged, and the product map is recovered by the universal
    -- property of the product in `Over U`.
    apply Sigma.ext
    · funext a
      rfl
    · simp
  · intro g
    -- Evaluating the reconstructed tuple at each component returns the original lift.
    funext a
    apply Sigma.ext
    · rfl
    · simpa using congrFun
        ((over_product_hom_equiv family V (fun a ↦ (g a).1)).right_inv
          (fun a ↦ (g a).2)) a

/-- Helper for Lemma 21.9.4: the `a`-th component of `lift_power_hom_equiv` is obtained by
projecting the Čech power with `powerπ a`. -/
private theorem lift_power_hom_equiv_apply_eq {C : Type u} [Category.{u} C] {U : C}
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) (V : Over U)
    {α : Type} [HasProductsOfShape α (Over U)]
    (k : ((FormalCoproduct.incl (Over U)).obj V) ⟶ (FormalCoproduct.mk ι family).power α)
    (a : α) :
    lift_power_hom_equiv family V k a =
      FormalCoproduct.inclHomEquiv V (FormalCoproduct.mk ι family)
        (k ≫ (FormalCoproduct.mk ι family).powerπ a) := by
  -- Both sides are the same pair: the chosen factor index and the induced map to that factor.
  apply Sigma.ext
  · rfl
  · rfl

/-- Helper for Lemma 21.9.4: the identification of lifts to a Čech power is natural under
reindexing the power by a map of indexing types. -/
private theorem lift_power_hom_equiv_natural {C : Type u} [Category.{u} C] {U : C}
    [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U) (V : Over U)
    {α β : Type} [HasProductsOfShape α (Over U)] [HasProductsOfShape β (Over U)]
    (g : α → β)
    (k : ((FormalCoproduct.incl (Over U)).obj V) ⟶ (FormalCoproduct.mk ι family).power β) :
    lift_power_hom_equiv family V (k ≫ (FormalCoproduct.mk ι family).mapPower g) =
      (lift_power_hom_equiv family V k) ∘ g := by
  -- Rewrite both tuple entries through the projection helper, so `mapPower_π` becomes the only
  -- remaining compatibility to check.
  funext a
  rw [lift_power_hom_equiv_apply_eq family V
      (k ≫ (FormalCoproduct.mk ι family).mapPower g) a]
  change
      FormalCoproduct.inclHomEquiv V (FormalCoproduct.mk ι family)
        ((k ≫ (FormalCoproduct.mk ι family).mapPower g) ≫ (FormalCoproduct.mk ι family).powerπ a) =
      lift_power_hom_equiv family V k (g a)
  rw [lift_power_hom_equiv_apply_eq family V k (g a)]
  have hπ :
      k ≫ (FormalCoproduct.mk ι family).mapPower g ≫ (FormalCoproduct.mk ι family).powerπ a =
        k ≫ (FormalCoproduct.mk ι family).powerπ (g a) := by
    -- The reindexing map commutes with the projection to the `a`-th factor.
    simpa [Category.assoc] using
      congrArg (fun m ↦ k ≫ m) (FormalCoproduct.mapPower_π (FormalCoproduct.mk ι family) g a)
  simpa [Category.assoc] using
    congrArg (FormalCoproduct.inclHomEquiv V (FormalCoproduct.mk ι family)) hπ

/-- Helper for Lemma 21.9.4: the bar complex on the lift set has zero positive homology. -/
private theorem liftBarChainComplex_homology_isZero_succ {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) (V : Over U) (i : ℕ) :
    IsZero ((liftBarChainComplex family V).homology (i + 1)) := by
  classical
  by_cases hEmpty : IsEmpty (lift_index family V)
  · -- In the empty case every positive-degree simplex set is empty, so the degree `(i + 1)` term
    -- of the bar complex is zero and hence its homology vanishes.
    have hX : IsZero ((liftBarChainComplex family V).X (i + 1)) := by
      let hInit :
          IsInitial (ULift.{u} (Fin (i + 2) → lift_index family V)) :=
        ((Types.initial_iff_empty _).2 inferInstance).some
      let hFree :
          IsZero (AddCommGrpCat.free.obj (ULift.{u} (Fin (i + 2) → lift_index family V))) :=
        (IsInitial.isInitialObj AddCommGrpCat.free _ hInit).isZero
      simpa [liftBarChainComplex, liftBarSimplicialObject, formalCoproductIndexFunctor] using hFree
    exact ((liftBarChainComplex family V).sc (i + 1)).isZero_homology_of_isZero_X₂ hX
  · -- In the nonempty case choose a lift and use the induced extra degeneracy to contract the
    -- bar complex onto the degree-zero augmentation.
    let s₀ : lift_index family V := Classical.choice (not_isEmpty_iff.mp hEmpty)
    let X :
        SimplicialObject.Augmented (FormalCoproduct.{max u w} (Type u)) :=
      ((FormalCoproduct.mk (lift_index family V) (fun _ ↦ (⊤_ (Type u)))).cech.augmentOfIsTerminal
        (FormalCoproduct.isTerminalIncl (⊤_ (Type u)) terminalIsTerminal))
    let ed : X.ExtraDegeneracy := by
      -- The chosen lift determines an extra degeneracy on the augmented Čech object.
      simpa [X] using
        (@FormalCoproduct.extraDegeneracyCech (Type u) _ _
          (FormalCoproduct.mk (lift_index family V) (fun _ ↦ (⊤_ (Type u))))
          (⊤_ (Type u))
          terminalIsTerminal
          s₀
          (𝟙 _))
    let X' :
        SimplicialObject.Augmented AddCommGrpCat.{max u w} :=
      (((SimplicialObject.Augmented.whiskering (FormalCoproduct.{max u w} (Type u))
          AddCommGrpCat.{max u w}).obj
        (formalCoproductIndexFunctor ⋙ AddCommGrpCat.free)).obj X)
    let ed' := ExtraDegeneracy.map ed (formalCoproductIndexFunctor ⋙ AddCommGrpCat.free)
    let e := ExtraDegeneracy.homotopyEquiv ed'
    let A := point.obj X'
    have hsingle :
        IsZero ((((ChainComplex.single₀ AddCommGrpCat.{max u w}).obj A).homology (i + 1))) :=
      (ChainComplex.exactAt_succ_single_obj A i).isZero_homology
    have hsingle' :
        IsZero
          ((((ChainComplex.single₀ AddCommGrpCat.{max u w}).obj
              (point.obj
                (((SimplicialObject.Augmented.whiskering (FormalCoproduct.{max u w} (Type u))
                    AddCommGrpCat.{max u w}).obj
                  (formalCoproductIndexFunctor ⋙ AddCommGrpCat.free)).obj
                  X))).homology
              (i + 1))) := by
      simpa [X', A] using hsingle
    have hbar :
      IsZero
          (((AlternatingFaceMapComplex.obj
              (drop.obj
                (((SimplicialObject.Augmented.whiskering (FormalCoproduct.{max u w} (Type u))
                    AddCommGrpCat.{max u w}).obj
                  (formalCoproductIndexFunctor ⋙ AddCommGrpCat.free)).obj
                  X))).homology
            (i + 1))) :=
      IsZero.of_iso hsingle' (isoOfQuasiIsoAt e.hom (i + 1))
    -- Transport the positive-degree vanishing across the quasi-isomorphism coming from the
    -- homotopy equivalence.
    simpa [liftBarChainComplex, liftBarSimplicialObject, X, X', A] using hbar

/-- Helper for Lemma 21.9.4: lifting a free abelian group across universes matches taking the
free abelian group on the lifted generating type. -/
private noncomputable def freeUliftIso (α : Type u) :
    (AddCommGrpCat.uliftFunctor.{w, u}).obj (AddCommGrpCat.free.obj α) ≅
      AddCommGrpCat.free.obj (ULift.{w} α) :=
  (((AddEquiv.ulift : ULift (FreeAbelianGroup α) ≃+ FreeAbelianGroup α)).trans
    (FreeAbelianGroup.equivOfEquiv (Equiv.ulift.symm : α ≃ ULift.{w} α))).toAddCommGrpIso

/-- Helper for Lemma 21.9.4: lifting an equivalence across `ULift` preserves the underlying
generator data. -/
private def uliftCongr {α β : Type (max u w)} (e : α ≃ β) :
    ULift.{u} α ≃ ULift.{u} β where
  toFun x := ⟨e x.down⟩
  invFun x := ⟨e.symm x.down⟩
  left_inv x := by
    cases x
    simp
  right_inv x := by
    cases x
    simp

/-- Helper for Lemma 21.9.4: after evaluating at a fixed object, one universe lift turns the
sigma-model above into the max-universe free abelian group on lifted generators. -/
private noncomputable def freeAbelianYonedaEvalObjUliftSigmaIso {C : Type u} [Category.{u} C]
    {U : C} [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    (V : Over U) (X : FormalCoproduct.{w} (Over U)) :
    (AddCommGrpCat.uliftFunctor.{w, u}).obj
        ((((FormalCoproduct.eval (Over U) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
            freeAbelianYoneda).obj X).obj (op V)) ≅
      AddCommGrpCat.free.obj (ULift.{u} (Σ i : X.I, V ⟶ X.obj i)) := by
  -- Route correction: the failed small-universe sigma packaging shows that the actual owner-level
  -- bridge must use the composite functor `evaluation ⋙ AddCommGrpCat.uliftFunctor`, so the large
  -- coproduct lives directly in `AddCommGrpCat.{max u w}` before we package it as one free group.
  -- TODO: prove this by applying `PreservesCoproduct.iso` to that composite functor, then package
  -- the resulting coproduct of `freeUliftIso` summands via `Types.coproductIso`.
  sorry

/-- Helper for Lemma 21.9.4: zero-ness descends from the universe lift of an abelian group. -/
private theorem isZero_of_uliftFunctor_obj {A : AddCommGrpCat.{u}}
    (hA : IsZero ((AddCommGrpCat.uliftFunctor.{w, u}).obj A)) : IsZero A := by
  -- The fully faithful universe lift detects when the identity morphism is zero.
  rw [IsZero.iff_id_eq_zero]
  apply (Functor.map_eq_zero_iff (AddCommGrpCat.uliftFunctor.{w, u})).1
  simpa using hA.eq_of_src (𝟙 ((AddCommGrpCat.uliftFunctor.{w, u}).obj A)) 0

/-- Source-faithful hypothesis layer for Lemma 21.9.4: for every tuple of indices in `family`,
the corresponding iterated fibre product over `U` exists. -/
class HasIteratedFiberProducts {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) : Prop where
  hasProduct : ∀ p : ℕ, ∀ f : Fin (p + 1) → ι, HasProduct (family ∘ f)

/-- Helper for Lemma 21.9.4: a global finite-product structure on `Over U` supplies the
tuplewise fibre products required by `HasIteratedFiberProducts family`. -/
instance hasIteratedFiberProducts_of_hasFiniteProducts {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasFiniteProducts (Over U)] :
    HasIteratedFiberProducts family where
  hasProduct p f := by infer_instance

/-- Helper for Lemma 21.9.4: the tuplewise product instance supplied by
`HasIteratedFiberProducts family`. -/
private abbrev familyHasProduct {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ)
    (f : Fin (p + 1) → ι) : HasProduct (family ∘ f) :=
  HasIteratedFiberProducts.hasProduct p f

/-- Helper for Lemma 21.9.4: maps into a fixed tuplewise fibre product are the same as tuples of
maps into the chosen factors. -/
private noncomputable def overFamilyProductHomEquiv {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) (V : Over U) (p : ℕ)
    (f : Fin (p + 1) → ι) [HasProduct (family ∘ f)] :
    (V ⟶ ∏ᶜ (family ∘ f)) ≃ ((a : Fin (p + 1)) → V ⟶ family (f a)) where
  -- The product projections extract the tuple of component morphisms.
  toFun g a := g ≫ Limits.Pi.π (family ∘ f) a
  -- The universal property of the chosen product reassembles a tuple into one morphism.
  invFun g := Limits.Pi.lift g
  left_inv g := by
    -- Two maps into the chosen iterated fibre product agree once all projections agree.
    apply Limits.Pi.hom_ext
    intro a
    simpa using
      (Limits.Pi.lift_π (f := family ∘ f) (fun a ↦ g ≫ Limits.Pi.π (family ∘ f) a) a)
  right_inv g := by
    -- Reassembling the tuple preserves each component by the universal property of the product.
    funext a
    simpa using (Limits.Pi.lift_π (f := family ∘ f) g a)

/-- Helper for Lemma 21.9.4: the `p`-fold Čech power of `family`, indexed by tuples of indices in
`family`, using only the tuplewise fibre products provided by `HasIteratedFiberProducts family`.
-/
private noncomputable def familyPower {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) :
    FormalCoproduct.{w} (Over U) where
  I := Fin (p + 1) → ι
  obj f := by
    letI := familyHasProduct family p f
    exact ∏ᶜ (family ∘ f)

/-- Helper for Lemma 21.9.4: a map `V ⟶ familyPower family p` is the same as a tuple of lifts of
`V` to the members of `family`. -/
private noncomputable def familyPowerLiftIndexEquiv {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) (V : Over U) :
    (Σ f : Fin (p + 1) → ι, (V ⟶ (familyPower family p).obj f)) ≃
      (Fin (p + 1) → lift_index family V) where
  -- First project a chosen summand map to its components in the iterated fiber product.
  toFun g a := by
    letI := familyHasProduct family p g.1
    exact ⟨g.1 a, (overFamilyProductHomEquiv family V p g.1 g.2) a⟩
  -- Conversely, rebuild the summand index together with the universal map into the product.
  invFun g := by
    let f : Fin (p + 1) → ι := fun a ↦ (g a).1
    letI := familyHasProduct family p f
    refine ⟨f, ?_⟩
    simpa [familyPower, f] using
      ((overFamilyProductHomEquiv family V p f).symm (fun a ↦ (g a).2))
  left_inv g := by
    -- The index function is unchanged, and the product morphism is recovered from its projections.
    rcases g with ⟨f, g⟩
    apply Sigma.ext
    · funext a
      rfl
    · letI := familyHasProduct family p f
      dsimp
      simpa [familyPower] using
        congrArg
          ((overFamilyProductHomEquiv family V p f).symm)
          ((overFamilyProductHomEquiv family V p f).right_inv fun a ↦
            (overFamilyProductHomEquiv family V p f g) a)
  right_inv g := by
    -- Projecting the reconstructed product map returns the original tuple of lifts.
    funext a
    apply Sigma.ext
    · rfl
    · let f : Fin (p + 1) → ι := fun a ↦ (g a).1
      letI := familyHasProduct family p f
      dsimp [f]
      simpa using congrFun
        ((overFamilyProductHomEquiv family V p f).right_inv (fun a ↦ (g a).2)) a

/-- Helper for Lemma 21.9.4: projection from the `p`-fold Čech power of `family` to the
`a`-th factor. -/
private noncomputable def familyPowerπ {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] (p : ℕ) (a : Fin (p + 1)) :
    familyPower family p ⟶ FormalCoproduct.mk ι family where
  f i := i a
  φ i := by
    letI := familyHasProduct family p i
    exact Pi.π (family ∘ i) a

/-- Helper for Lemma 21.9.4: reindexing a Čech power of `family` along a map of finite simplices.
-/
private noncomputable def familyMapPower {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] {p q : ℕ}
    (g : Fin (p + 1) → Fin (q + 1)) :
    familyPower family q ⟶ familyPower family p where
  f i := i ∘ g
  φ i := by
    letI := familyHasProduct family q i
    letI := familyHasProduct family p (i ∘ g)
    exact Pi.lift (fun a ↦ Pi.π (family ∘ i) (g a))

/-- Helper for Lemma 21.9.4: composing a map into a tuplewise fibre product with
`familyMapPower family g` reindexes the tuple of component lifts by `g`. -/
private theorem overFamilyProductHomEquiv_comp_familyMapPower {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    {p q : ℕ} (V : Over U) (g : Fin (p + 1) → Fin (q + 1))
    (f : Fin (q + 1) → ι) [HasProduct (family ∘ f)] [HasProduct (family ∘ (f ∘ g))]
    (k : V ⟶ (familyPower family q).obj f) (a : Fin (p + 1)) :
    ((overFamilyProductHomEquiv family V p (f ∘ g))
        (k ≫ (familyMapPower family g).φ f)) a =
      ((overFamilyProductHomEquiv family V q f) k) (g a) := by
  -- Unfold only the tuple-extraction maps, so the goal reduces to the projection formula for the
  -- `Pi.lift` defining `familyMapPower`.
  change
      (overFamilyProductHomEquiv family V p (f ∘ g)).toFun
          (k ≫ (familyMapPower family g).φ f) a =
        (overFamilyProductHomEquiv family V q f).toFun k (g a)
  simpa [overFamilyProductHomEquiv, familyMapPower, Category.assoc] using
    congrArg (fun t ↦ k ≫ t)
      (Limits.Pi.lift_π
        (f := family ∘ (f ∘ g))
        (fun b ↦ Limits.Pi.π (family ∘ f) (g b)) a)

/-- Helper for Lemma 21.9.4: the identification of lifts to `familyPower family p` is compatible
with reindexing the tuple of factors. -/
private theorem familyPowerLiftIndexEquiv_natural {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] {p q : ℕ}
    (g : Fin (p + 1) → Fin (q + 1)) (V : Over U)
    (k : Σ f : Fin (q + 1) → ι, (V ⟶ (familyPower family q).obj f)) :
    familyPowerLiftIndexEquiv family p V
        ⟨k.1 ∘ g, k.2 ≫ (familyMapPower family g).φ k.1⟩ =
      (familyPowerLiftIndexEquiv family q V k) ∘ g := by
  letI := familyHasProduct family q k.1
  letI := familyHasProduct family p (k.1 ∘ g)
  -- Compare the two functions componentwise; the first coordinate is definitionally reindexed,
  -- and the second coordinate is exactly the projection bridge above.
  funext a
  apply Sigma.ext
  · rfl
  · simpa [familyPowerLiftIndexEquiv] using
      overFamilyProductHomEquiv_comp_familyMapPower family V g k.1 k.2 a

/-- Helper for Lemma 21.9.4: the lift-index identification is compatible with the `j`-th Čech
face map. -/
private theorem familyPowerLiftIndexEquiv_face_natural {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] (V : Over U) (n : ℕ)
    (j : Fin (n + 2))
    (k : Σ f : Fin (n + 2) → ι, (V ⟶ (familyPower family (n + 1)).obj f)) :
    familyPowerLiftIndexEquiv family n V
        ⟨k.1 ∘ (SimplexCategory.δ j).toOrderHom,
          k.2 ≫ (familyMapPower family (SimplexCategory.δ j).toOrderHom).φ k.1⟩ =
      (familyPowerLiftIndexEquiv family (n + 1) V k) ∘ (SimplexCategory.δ j).toOrderHom := by
  -- This is the face-map specialization of the general reindexing lemma.
  simpa using
    familyPowerLiftIndexEquiv_natural family (SimplexCategory.δ j).toOrderHom V k

/-- Helper for Lemma 21.9.4: after evaluating the `p`-th Čech term at `V` and applying
`AddCommGrpCat.uliftFunctor`, one obtains the free abelian group on `ULift`ed tuples of lifts of
`V` to `family`. -/
private noncomputable def familyPowerEvalLiftTupleIso {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    (p : ℕ) (V : Over U) :
    (AddCommGrpCat.uliftFunctor.{w, u}).obj
        ((((FormalCoproduct.eval (Over U) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
            freeAbelianYoneda).obj (familyPower family p)).obj (op V)) ≅
      AddCommGrpCat.free.obj (ULift.{u} (Fin (p + 1) → lift_index family V)) := by
  -- Specialize the fixed-object sigma-model bridge to the `p`-th Čech power and then reindex the
  -- generator type by the already-established tuple-of-lifts equivalence.
  exact
    freeAbelianYonedaEvalObjUliftSigmaIso V (familyPower family p) ≪≫
      Functor.mapIso AddCommGrpCat.free
        (Equiv.toIso (uliftCongr (familyPowerLiftIndexEquiv family p V)))

/-- Helper for Lemma 21.9.4: the simplicial formal coproduct attached to `family`, built from its
iterated fibre products without assuming all finite products in `Over U`. -/
private noncomputable def familyCech {C : Type u} [Category.{u} C] {U : C} {ι : Type w}
    (family : ι → Over U) [HasIteratedFiberProducts family] :
    SimplicialObject (FormalCoproduct.{w} (Over U)) where
  obj n := familyPower family n.unop.len
  map f := familyMapPower family f.unop.toOrderHom
  map_id n := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    letI := familyHasProduct family _ i
    dsimp [familyMapPower]
    apply Pi.hom_ext
    intro a
    calc
      ((Pi.lift fun a ↦ Pi.π (family ∘ i) a) ≫
          𝟙 ((familyPower family (unop n).len).obj i)) ≫
          Pi.π (family ∘ i) a =
        (Pi.lift fun a ↦ Pi.π (family ∘ i) a) ≫ Pi.π (family ∘ i) a := by
          exact
            congrArg
              (fun t ↦ t ≫ Pi.π (family ∘ i) a)
              (Category.comp_id (Pi.lift (fun a ↦ Pi.π (family ∘ i) a)))
      _ = Pi.π (family ∘ i) a := by
        simpa using (Pi.lift_π (fun a ↦ Pi.π (family ∘ i) a) a)
      _ =
          𝟙 ((familyPower family (unop n).len).obj i) ≫ Pi.π (family ∘ i) a := by
            simp
  map_comp f g := by
    let fOrder := f.unop.toOrderHom
    let gOrder := g.unop.toOrderHom
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    letI := familyHasProduct family _ i
    letI := familyHasProduct family _ (i ∘ fOrder)
    letI := familyHasProduct family _ ((i ∘ fOrder) ∘ gOrder)
    letI :
        HasProduct
          (fun a ↦ (family ∘ i) (fOrder (gOrder a))) := by
      simpa [Function.comp_apply] using
        (familyHasProduct family _ ((i ∘ fOrder) ∘ gOrder))
    letI : HasProduct (fun a ↦ (family ∘ i) (fOrder a)) := by
      simpa [Function.comp_apply] using
        (familyHasProduct family _ (i ∘ fOrder))
    letI :
        HasProduct (fun a ↦ (family ∘ i ∘ fOrder) (gOrder a)) := by
      simpa [Function.comp_apply] using
        (familyHasProduct family _ ((i ∘ fOrder) ∘ gOrder))
    dsimp [familyMapPower]
    have hcomp :
        Pi.lift (fun a ↦
            Pi.π (family ∘ i) (fOrder (gOrder a))) =
          Pi.lift (fun a ↦ Pi.π (family ∘ i) (fOrder a)) ≫
            Pi.lift (fun a ↦
              Pi.π (family ∘ i ∘ fOrder) (gOrder a)) := by
      apply Pi.hom_ext
      intro a
      rw [Pi.lift_π]
      have hπ :
          (Pi.lift fun a ↦
              Pi.π (family ∘ i ∘ fOrder) (gOrder a)) ≫
            Pi.π (fun a ↦ (family ∘ i) (fOrder (gOrder a))) a =
            Pi.π (family ∘ i ∘ fOrder) (gOrder a) := by
        exact Pi.lift_π
          (fun a ↦ Pi.π (family ∘ i ∘ fOrder) (gOrder a))
          a
      have h₁ :
          Pi.π (family ∘ i) (fOrder (gOrder a)) =
            (Pi.lift fun a ↦ Pi.π (family ∘ i) (fOrder a)) ≫
              Pi.π (family ∘ i ∘ fOrder) (gOrder a) := by
        simpa using
          (Pi.lift_π (fun a ↦ Pi.π (family ∘ i) (fOrder a)) (gOrder a)).symm
      have h₂ :
          (Pi.lift fun a ↦ Pi.π (family ∘ i) (fOrder a)) ≫
            Pi.π (family ∘ i ∘ fOrder) (gOrder a) =
            ((Pi.lift fun a ↦ Pi.π (family ∘ i) (fOrder a)) ≫
              Pi.lift (fun a ↦ Pi.π (family ∘ i ∘ fOrder) (gOrder a))) ≫
              Pi.π (fun a ↦ (family ∘ i) (fOrder (gOrder a))) a := by
        simpa [Category.assoc] using
          (congrArg
            (fun t ↦
              (Pi.lift fun a ↦ Pi.π (family ∘ i) (fOrder a)) ≫ t)
            hπ).symm
      exact h₁.trans h₂
    calc
      Pi.lift (fun a ↦
          Pi.π (family ∘ i) (fOrder (gOrder a))) ≫
          eqToHom (by rfl) =
        Pi.lift (fun a ↦
          Pi.π (family ∘ i) (fOrder (gOrder a))) := by simp
      _ = _ := hcomp

/-- The chain complex of abelian presheaves obtained by applying the alternating face-map
construction to the simplicial free-abelian representable Čech object attached to `family`. -/
abbrev freeAbelianCechChainComplex {C : Type u} [Category.{u} C] {U : C}
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] :
    ChainComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (alternatingFaceMapComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (familyCech family ⋙
      (FormalCoproduct.eval.{w} (Over U) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)

/-- Helper for Lemma 21.9.4: the `j`-th face of the tuplewise Čech object is the expected
reindexing map between tuplewise fibre products. -/
private theorem familyCech_face_eq_familyMapPower {C : Type u} [Category.{u} C] {U : C}
    {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family] (n : ℕ)
    (j : Fin (n + 2)) :
    SimplicialObject.δ (familyCech family) j =
      familyMapPower family (SimplexCategory.δ j).toOrderHom := by
  -- The simplicial structure on `familyCech` was defined by `familyMapPower`, so the face map is
  -- exactly that reindexing morphism.
  rfl

/-- Helper for Lemma 21.9.4: the `j`-th face of the lifted bar simplicial object is free abelian
on tuple precomposition by the standard face injection. -/
private theorem liftBarSimplicialObject_face_eq_freePrecomp {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) (V : Over U) (n : ℕ) (j : Fin (n + 2)) :
    SimplicialObject.δ (liftBarSimplicialObject family V) j =
      AddCommGrpCat.free.map
        (fun t : ULift.{u} (Fin (n + 2) → lift_index family V) =>
          ⟨t.down ∘ (SimplexCategory.δ j).toOrderHom.toFun⟩) := by
  -- Route correction: normalize only the bar face maps entering the alternating differential,
  -- instead of proving full simplicial naturality for every simplex morphism.
  -- Unfolding the bar object shows that the face map is induced by precomposition on tuple
  -- indices, and `formalCoproductIndexFunctor` records exactly that underlying function.
  rfl

/-- Helper for Lemma 21.9.4: after evaluating the free-abelian Čech simplicial object at `V` and
applying the universe lift, the resulting simplicial abelian group is canonically the bar object
on the set of lifts of `V` to `family`. -/
private noncomputable def freeAbelianCechEvalLiftBarSimplicialIso {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u w})]
    (V : Over U) :
    (familyCech family ⋙
        (FormalCoproduct.eval.{w} (Over U) ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
          freeAbelianYoneda ⋙
        (evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op V) ⋙
        AddCommGrpCat.uliftFunctor.{w, u}) ≅
      liftBarSimplicialObject family V := by
  -- TODO: the component is `familyPowerEvalLiftTupleIso family n.unop.len V`; for naturality,
  -- rewrite both sides to `AddCommGrpCat.free.map` on tuple precomposition and close with
  -- `familyPowerLiftIndexEquiv_natural`.
  sorry

/-- Helper for Lemma 21.9.4: the evaluated-and-lifted free-abelian Čech chain complex at `V` is
canonically the bar chain complex on the lift set of `V`. -/
private noncomputable def freeAbelianCechEvalLiftBarChainIso {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u w})]
    [Limits.HasProducts AddCommGrpCat.{u}] (V : Over U) :
    (((AddCommGrpCat.uliftFunctor.{w, u}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((((evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (freeAbelianCechChainComplex family))) ≅
      liftBarChainComplex family V := by
  -- TODO: replace the unfinished full simplicial comparison by the face-level chain comparison
  -- from the current route-correction plan, built with `HomologicalComplex.Hom.isoOfComponents`.
  sorry

/-- Helper for Lemma 21.9.4: an additive presheaf is zero once all of its objectwise values are
zero. -/
private theorem presheaf_isZero_of_objectwise_isZero {C : Type u} [Category.{u} C]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (hF : ∀ X : Cᵒᵖ, IsZero (F.obj X)) : IsZero F := by
  let e : F ≅ (0 : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    NatIso.ofComponents
      (fun X ↦ (hF X).isoZero ≪≫ (Functor.zero_obj X).isoZero.symm)
      (fun {X Y} f ↦ by
        -- Each naturality square lands in the zero object of `AddCommGrpCat`, so both sides
        -- agree without unfolding the functorial zero map any further.
        apply (Functor.zero_obj Y).eq_of_tgt)
  -- Replace the presheaf by the zero presheaf through the componentwise zero isomorphism.
  exact (isZero_zero (Cᵒᵖ ⥤ AddCommGrpCat.{u})).of_iso e

-- Proof sketch: evaluate the chain complex on an object `V ⟶ U` of `Over U` and decompose the
-- resulting complex as a direct sum over maps `V ⟶ U` of bar-resolution complexes on the sets of
-- lifts to the cover. For each summand, choose a lift when the indexing set is nonempty and use
-- the induced extra degeneracy, equivalently the standard contracting homotopy on
-- `ℤ[S^{• + 1}]`, to kill positive homology.
/-- Lemma 21.9.4: the free-abelian Čech cover chain complex of a family with fixed target has zero
homology presheaves in every positive degree. -/
@[stacks 03AT]
theorem freeAbelianCechCoverChainComplex_homology_isZero_succ {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    (i : ℕ) :
    IsZero ((freeAbelianCechChainComplex family).homology (i + 1)) := by
  -- TODO: evaluate objectwise at `V : Over U`, transport homology through evaluation and the
  -- universe lift with `mapHomologyIso`, compare the resulting chain complex with
  -- `liftBarChainComplex family V` via `freeAbelianCechEvalLiftBarChainIso`, and finish using
  -- `liftBarChainComplex_homology_isZero_succ` plus `isZero_of_uliftFunctor_obj`.
  sorry

/-- Positive-degree companion to Lemma 21.9.4 in arbitrary-index form. -/
theorem freeAbelianCechCoverChainComplex_homology_isZero_of_pos {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    (i : ℕ) (hi : 0 < i) :
    IsZero ((freeAbelianCechChainComplex family).homology i) := by
  -- Rewrite the positive degree as a successor degree and reuse the source-facing theorem above.
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  simpa [Nat.succ_eq_add_one] using freeAbelianCechCoverChainComplex_homology_isZero_succ family j

/-- Typeclass form of Lemma 21.9.4: the positive-degree homology presheaves of the free-abelian
Čech cover chain complex are zero. -/
instance instIsZeroFreeAbelianCechCoverChainComplexHomologySucc {C : Type u} [Category.{u} C]
    {U : C} {ι : Type w} (family : ι → Over U) [HasIteratedFiberProducts family]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    (i : ℕ) :
    IsZero ((freeAbelianCechChainComplex family).homology (i + 1)) :=
  freeAbelianCechCoverChainComplex_homology_isZero_succ family i

end CategoryTheory
