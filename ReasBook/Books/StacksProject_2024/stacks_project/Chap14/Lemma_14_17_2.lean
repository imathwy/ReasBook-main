import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Types.Yoneda
import StacksProject_2024.stacks_project.Chap14.Definition_14_17_1
import StacksProject_2024.stacks_project.Chap14.Lemma_14_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.17.2:
- primary domain: representable presheaves obtained by restricting the simplicial mapping-object
  presheaf along constant simplicial objects;
- sampled owner-style declarations:
  `SimplicialObject.const`,
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`,
  `simplicialHomPresheaf`,
  `Functor.IsRepresentable`;
- best owner abstraction: the ambient owner is `simplicialHomPresheaf U V`, while the present file
  is only its `C`-indexed `bridge/view` specialization along `SimplicialObject.const`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, and the owner
  hypothesis that the simplicial copowers `U × W` exist for every simplicial object `W`;
- auxiliary source hypotheses: binary coproducts on `C`, degreewise finiteness of `U`, and a
  `0`-simplex of `U`, which only supply the owner hypothesis through
  `simplicialCopower_hasCoproducts_of_finite_nonempty_zero`;
- derived API: the representability statement for the constant-object restriction
  `(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` under the stronger source-facing
  hypotheses.

This file therefore deletes the parallel compatible-family model and reuses the upstream owner
construction directly. -/

variable {C : Type u} [Category.{v} C]

section Restriction

variable [HasBinaryCoproducts C]
variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

/-- Helper for Lemma 14.17.2: the source-proof indexing category is the category of simplices of
`U`, implemented explicitly as pairs `(Δ, u)` with `u ∈ U.obj Δ`. -/
private abbrev simplex_index (U : SSet.{w}) :=
  Σ Δ : SimplexCategoryᵒᵖ, U.obj Δ

/-- Helper for Lemma 14.17.2: morphisms in the simplex-indexing category are simplicial operators
carrying the chosen source simplex to the chosen target simplex. -/
private instance simplex_index_category : Category (simplex_index U) where
  Hom x y := { f : x.1 ⟶ y.1 // U.map f x.2 = y.2 }
  id x := ⟨𝟙 x.1, by simpa using (FunctorToTypes.map_id_apply U x.2)⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, by
    rw [FunctorToTypes.map_comp_apply, f.2, g.2]⟩

/-- Helper for Lemma 14.17.2: the source-proof diagram sends a simplex of `U` to the
corresponding simplicial degree of `V`. -/
private def simplex_index_diagram (U : SSet.{w}) (V : SimplicialObject C) :
    simplex_index U ⥤ C where
  obj x := V.obj x.1
  map f := V.map f.1
  map_id x := V.map_id x.1
  map_comp f g := V.map_comp f.1 g.1

/-- Helper for Lemma 14.17.2: the constant simplicial object on `X` inherits the coproducts
required to form the simplicial copower with `U`. -/
private instance const_hasCoproduct (X : C) :
    ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ ((SimplicialObject.const C).obj X).obj Δ) := by
  intro Δ
  letI : Nonempty (U.obj Δ) := nonempty_obj_of_nonempty_zero U Δ
  dsimp
  infer_instance

/-- Helper for Lemma 14.17.2: morphisms in the restricted mapping presheaf act by precomposing
with the induced map on simplicial copowers. -/
private theorem const_hom_presheaf_map_app
    {X Y : C} (f : X ⟶ Y)
    (γ : (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).obj (op Y))) :
    (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).map f.op γ) =
      simplicialCopowerHom U ((SimplicialObject.const C).map f) ≫ γ :=
  rfl

/-- Helper for Lemma 14.17.2: a compatible family on a constant source defines a cone on the
simplex-index diagram by evaluating at each chosen simplex. -/
private theorem compatibleFamily_const_to_simplex_index_cone_naturality
    {X : C}
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V)
    {x y : simplex_index U} (g : x ⟶ y) :
    𝟙 X ≫ F.1 y.1 y.2 =
      F.1 x.1 x.2 ≫ (simplex_index_diagram U V).map g := by
  -- Proof comment: compatibility for the constant simplicial source is exactly the cone
  -- naturality condition after rewriting the chosen target simplex using `g.2`.
  simpa [simplex_index_diagram, g.2] using (F.2 g.1 x.2)

/-- Helper for Lemma 14.17.2: a compatible family on a constant source gives a cone on the
simplex-index diagram. -/
private def compatibleFamily_const_to_simplex_index_cone
    (X : C)
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V) :
    (simplex_index_diagram U V).cones.obj (op X) :=
  { app := fun x ↦ F.1 x.1 x.2
    naturality := fun {x y} g ↦ by
      simpa using
        compatibleFamily_const_to_simplex_index_cone_naturality (U := U) (V := V) F g }

/-- Helper for Lemma 14.17.2: evaluating cone naturality on the canonical simplex arrow recovers
the compatibility condition on the associated family. -/
private theorem simplex_index_cone_to_compatibleFamily_isCompatible
    (X : C) (s : (simplex_index_diagram U V).cones.obj (op X)) :
    SimplicialCopowerHomFamily.IsCompatible
      (U := U) (V := (SimplicialObject.const C).obj X) (W := V)
      (fun Δ u ↦ s.app ⟨Δ, u⟩) := by
  intro Δ Δ' f u
  -- Proof comment: the defining arrow `(Δ, u) ⟶ (Δ', U.map f u)` in the simplex index category
  -- turns cone naturality into the required compatibility equation.
  simpa [simplex_index_diagram] using
    (s.naturality (⟨f, rfl⟩ :
      (⟨Δ, u⟩ : simplex_index U) ⟶ ⟨Δ', U.map f u⟩))

/-- Helper for Lemma 14.17.2: a cone on the simplex-index diagram yields the corresponding
compatible family of maps out of the constant source. -/
private def simplex_index_cone_to_compatibleFamily
    (X : C) (s : (simplex_index_diagram U V).cones.obj (op X)) :
    SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V :=
  ⟨fun Δ u ↦ s.app ⟨Δ, u⟩,
    simplex_index_cone_to_compatibleFamily_isCompatible (U := U) (V := V) X s⟩

/-- Helper for Lemma 14.17.2: cones with the same components on the simplex-index diagram are
equal. -/
private theorem simplex_index_cone_ext
    (X : C)
    {s t : (simplex_index_diagram U V).cones.obj (op X)}
    (h : ∀ x : simplex_index U, s.app x = t.app x) :
    s = t := by
  cases s with
  | mk sApp sNat =>
      cases t with
      | mk tApp tNat =>
          dsimp at h
          have hApp : sApp = tApp := funext h
          subst hApp
          have hNat : sNat = tNat := by
            apply Subsingleton.elim
          subst hNat
          rfl

/-- Helper for Lemma 14.17.2: converting a compatible family to a cone and back is the identity.
-/
private theorem simplex_index_compatibleFamily_left_inv
    (X : C)
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V) :
    simplex_index_cone_to_compatibleFamily (U := U) (V := V) X
        (compatibleFamily_const_to_simplex_index_cone (U := U) (V := V) X F) = F := by
  -- Proof comment: both compatible families have the same degreewise components, so extensionality
  -- on the subtype closes the argument.
  apply Subtype.ext
  funext Δ u
  simp [simplex_index_cone_to_compatibleFamily, compatibleFamily_const_to_simplex_index_cone]

/-- Helper for Lemma 14.17.2: converting a cone to a compatible family and back is the identity.
-/
private theorem simplex_index_compatibleFamily_right_inv
    (X : C) (s : (simplex_index_diagram U V).cones.obj (op X)) :
    compatibleFamily_const_to_simplex_index_cone (U := U) (V := V) X
        (simplex_index_cone_to_compatibleFamily (U := U) (V := V) X s) = s := by
  -- Proof comment: the reconstructed cone has exactly the same components and naturality fields.
  apply simplex_index_cone_ext (U := U) (V := V) X
  intro x
  simp [simplex_index_cone_to_compatibleFamily, compatibleFamily_const_to_simplex_index_cone]

/-- Helper for Lemma 14.17.2: for a constant simplicial source, compatible families into `V`
are exactly cones on the simplex-index diagram of `U`. -/
private def compatibleFamily_const_equiv_simplex_index_cones (X : C) :
    SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V ≃
      (simplex_index_diagram U V).cones.obj (op X) :=
  { toFun := compatibleFamily_const_to_simplex_index_cone (U := U) (V := V) X
    invFun := simplex_index_cone_to_compatibleFamily (U := U) (V := V) X
    left_inv := simplex_index_compatibleFamily_left_inv (U := U) (V := V) X
    right_inv := simplex_index_compatibleFamily_right_inv (U := U) (V := V) X }

/-- Helper for Lemma 14.17.2: precomposing a compatible family with `f : X ⟶ Y` acts degreewise
by composition on the left. -/
private theorem precompose_compatibleFamily_const_isCompatible
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj Y) V) :
    SimplicialCopowerHomFamily.IsCompatible
      (U := U) (V := (SimplicialObject.const C).obj X) (W := V)
      (fun Δ u ↦ f ≫ F.1 Δ u) := by
  intro Δ Δ' g u
  -- Proof comment: compatibility of `F` already gives the target equation; precompose it by `f`
  -- and reassociate.
  simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (F.2 g u)

/-- Helper for Lemma 14.17.2: the source-side action on compatible families induced by
`f : X ⟶ Y`. -/
private def precompose_compatibleFamily_const
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj Y) V) :
    SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj X) V :=
  ⟨fun Δ u ↦ f ≫ F.1 Δ u,
    precompose_compatibleFamily_const_isCompatible (U := U) (V := V) f F⟩

/-- Helper for Lemma 14.17.2: under the compatible-family equivalence for simplicial copowers, the
restricted presheaf map is the source-side precomposition map. -/
private theorem homToCompatibleFamily_const_naturality
    {X Y : C} (f : X ⟶ Y)
    (γ : (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).obj (op Y))) :
    (simplicialCopowerCompatibleFamilyCorepresentableBy U
        ((SimplicialObject.const C).obj X)).homEquiv
        ((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).map f.op) γ) =
      precompose_compatibleFamily_const (U := U) (V := V) f
        ((simplicialCopowerCompatibleFamilyCorepresentableBy U
          ((SimplicialObject.const C).obj Y)).homEquiv γ) := by
  -- Proof comment: both sides are the degreewise family obtained by restricting
  -- `simplicialCopowerHom U ((const C).map f) ≫ γ` along the coproduct injections.
  apply Subtype.ext
  funext Δ u
  rw [const_hom_presheaf_map_app]
  simp [precompose_compatibleFamily_const, simplicialCopowerHom_app]

/-- Helper for Lemma 14.17.2: the compatible-family/cone equivalence intertwines source-side
precomposition with the cone-functor action. -/
private theorem compatibleFamily_const_equiv_simplex_index_cones_naturality
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((SimplicialObject.const C).obj Y) V) :
    compatibleFamily_const_equiv_simplex_index_cones (U := U) (V := V) X
        (precompose_compatibleFamily_const (U := U) (V := V) f F) =
      (simplex_index_diagram U V).cones.map f.op
        (compatibleFamily_const_equiv_simplex_index_cones (U := U) (V := V) Y F) := by
  -- Proof comment: both cones have component `(Δ,u) ↦ f ≫ F(Δ,u)`, so they agree by extensionality.
  apply simplex_index_cone_ext (U := U) (V := V) X
  intro x
  rfl

/-- Helper for Lemma 14.17.2: the constant-source restriction of the mapping presheaf is naturally
isomorphic to the cone functor on the simplex-index diagram, objectwise after applying `ULift`. -/
private noncomputable def const_simplicial_hom_presheaf_ulift_objEquiv_cones (X : C) :
    ULift ((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).obj (op X))) ≃
      (simplex_index_diagram U V).cones.obj (op X) :=
  Equiv.ulift.trans
    (((simplicialCopowerCompatibleFamilyCorepresentableBy U
      ((SimplicialObject.const C).obj X)).homEquiv).trans
      (compatibleFamily_const_equiv_simplex_index_cones (U := U) (V := V) X))

/-- Helper for Lemma 14.17.2: the objectwise `ULift`-to-cones equivalence is natural in the
constant object. -/
private theorem const_simplicial_hom_presheaf_ulift_objEquiv_cones_naturality
    {X Y : C} (f : X ⟶ Y)
    (γ : ULift ((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).obj (op Y)))) :
    const_simplicial_hom_presheaf_ulift_objEquiv_cones (U := U) (V := V) X
        (((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}).map
          f.op) γ) =
      (simplex_index_diagram U V).cones.map f.op
        (const_simplicial_hom_presheaf_ulift_objEquiv_cones (U := U) (V := V) Y γ) := by
  -- Proof comment: remove the `ULift`, use the compatible-family naturality bridge, and then
  -- invoke the pointwise cone-family naturality already proved above.
  cases γ with
  | up γ =>
      change
        compatibleFamily_const_equiv_simplex_index_cones (U := U) (V := V) X
            ((simplicialCopowerCompatibleFamilyCorepresentableBy U
              ((SimplicialObject.const C).obj X)).homEquiv
              ((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).map f.op γ))) =
          (simplex_index_diagram U V).cones.map f.op
            (compatibleFamily_const_equiv_simplex_index_cones (U := U) (V := V) Y
              ((simplicialCopowerCompatibleFamilyCorepresentableBy U
                ((SimplicialObject.const C).obj Y)).homEquiv γ))
      rw [homToCompatibleFamily_const_naturality]
      exact compatibleFamily_const_equiv_simplex_index_cones_naturality
        (U := U) (V := V) f
        ((simplicialCopowerCompatibleFamilyCorepresentableBy U
          ((SimplicialObject.const C).obj Y)).homEquiv γ)

/-- Helper for Lemma 14.17.2: the component isomorphisms of the `ULift`ed restricted mapping
presheaf are natural in the opposite object variable. -/
private theorem const_simplicial_hom_presheaf_iso_cones_naturality
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}).map f) ≫
        (Equiv.toIso
          (const_simplicial_hom_presheaf_ulift_objEquiv_cones
            (U := U) (V := V) Y.unop)).hom) =
      (Equiv.toIso
          (const_simplicial_hom_presheaf_ulift_objEquiv_cones
            (U := U) (V := V) X.unop)).hom ≫
        (simplex_index_diagram U V).cones.map f := by
  ext γ
  -- Proof comment: after evaluating the natural-transformation square at `γ`, this is exactly
  -- the objectwise naturality statement for the corresponding morphism in `C`.
  exact const_simplicial_hom_presheaf_ulift_objEquiv_cones_naturality
    (U := U) (V := V) (X := Y.unop) (Y := X.unop) f.unop γ

/-- Helper for Lemma 14.17.2: the constant-source restriction of the mapping presheaf is naturally
isomorphic to the cone functor on the simplex-index diagram. -/
private noncomputable def const_simplicial_hom_presheaf_iso_cones :
    (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}) ≅
      (simplex_index_diagram U V).cones :=
  NatIso.ofComponents
    (fun X ↦
      Equiv.toIso
        (const_simplicial_hom_presheaf_ulift_objEquiv_cones
          (U := U) (V := V) X.unop))
    (fun {_} {_} f ↦ const_simplicial_hom_presheaf_iso_cones_naturality
      (U := U) (V := V) f)

/-- Helper for Lemma 14.17.2: the simplex category is countable, indexed by the length of a
simplex. -/
private def simplexCategoryOpposite_equiv_nat : SimplexCategoryᵒᵖ ≃ ℕ where
  toFun Δ := Δ.unop.len
  invFun n := op ⦋n⦌
  left_inv Δ := by
    simpa using congrArg Opposite.op (SimplexCategory.mk_len Δ.unop)
  right_inv n := rfl

/-- Helper for Lemma 14.17.2: the simplex category is countable, indexed by the length of a
simplex. -/
private instance simplexCategoryOpposite_countable : Countable SimplexCategoryᵒᵖ := by
  exact Countable.of_equiv ℕ (simplexCategoryOpposite_equiv_nat.symm)

/-- Helper for Lemma 14.17.2: the simplex-indexing category of a degreewise finite simplicial set
is countable. -/
private instance simplex_index_countable : Countable (simplex_index U) := by
  -- Proof comment: the source-proof object set is literally the sigma type of simplices of `U`,
  -- so countability follows from countability of `SimplexCategoryᵒᵖ` and each finite fiber.
  change Countable (Sigma fun Δ : SimplexCategoryᵒᵖ ↦ U.obj Δ)
  infer_instance

/-- Helper for Lemma 14.17.2: hom-sets in the simplex-indexing category are countable because
they are subtypes of the corresponding simplex-operator hom-sets. -/
private instance simplex_index_hom_countable (x y : simplex_index U) : Countable (x ⟶ y) := by
  -- Proof comment: by definition, morphisms are a subtype of morphisms in `SimplexCategoryᵒᵖ`,
  -- and those hom-sets are finite, hence countable.
  change Countable { f : x.1 ⟶ y.1 // U.map f x.2 = y.2 }
  letI : Countable (x.1 ⟶ y.1) :=
    Countable.of_equiv (y.1.unop ⟶ x.1.unop) (opEquiv x.1 y.1).symm
  infer_instance

/-- Helper for Lemma 14.17.2: once objects and hom-sets are countable, the simplex-index category
itself is a countable category. -/
private instance simplex_index_countableCategory : CountableCategory (simplex_index U) where
  countableObj := inferInstance
  countableHom _ _ := inferInstance

/-- Helper for Lemma 14.17.2: countable limits provide a limit for the simplex-index diagram once
the countability witnesses for the indexing category and its hom-sets are in place. -/
private theorem simplex_index_diagram_hasLimit [HasCountableLimits C] :
    HasLimit (simplex_index_diagram U V) := by
  -- Proof comment: `HasCountableLimits` supplies limits for any countable indexing category, and
  -- the preceding instances show that the simplex-index category is countable.
  infer_instance

/-- Lemma 14.17.2: assume `C` has binary coproducts and countable limits, and that `U` is
degreewise finite with a `0`-simplex. Then the presheaf `X ↦ Mor_{Simp(C)}(X × U, V)` is
representable. In Lean this presheaf is the constant-object restriction
`(SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V` of the owner presheaf
`simplicialHomPresheaf U V`. -/
theorem simplicialHomPresheaf_const_isRepresentable
    [HasCountableLimits C] :
    ((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := by
  -- Route correction: instead of assembling cones directly from simplicial morphisms, first pass
  -- through the compatible-family equivalence from Lemma 14.13.2 and then identify those
  -- compatible families with cones on the simplex-index diagram.
  have hRep :
      ((((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w})).IsRepresentable := by
    -- Proof comment: `simplex_index U` is countable with countable hom-sets, so countable limits
    -- provide a limit of the source-proof simplex diagram; the cone functor is then represented by
    -- that limit.
    letI : HasLimit (simplex_index_diagram U V) := simplex_index_diagram_hasLimit (U := U) (V := V)
    exact
      ((Limits.IsLimit.representableBy (limit.isLimit (simplex_index_diagram U V))).ofIso
        (const_simplicial_hom_presheaf_iso_cones (U := U) (V := V)).symm).isRepresentable
  -- Proof comment: descend representability from the universe-lifted restricted presheaf.
  exact (Functor.isRepresentable_comp_uliftFunctor_iff
    (F := ((SimplicialObject.const C).op ⋙ simplicialHomPresheaf U V))).mp hRep

attribute [instance] simplicialHomPresheaf_const_isRepresentable

end Restriction

end CategoryTheory
