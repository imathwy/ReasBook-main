import StacksProject_2024.stacks_project.Chap14.Definition_14_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 14.13.2:
- primary domain: simplicial copowers and their hom universal property, expressed degreewise by
  coproducts and functorially in the target simplicial object;
- sampled same-kind owner declarations:
  `simplicialCopower`,
  `simplicialCopower_map`,
  `Functor.CorepresentableBy`,
  `uliftCoyoneda.obj (op (U × V))`,
  `Limits.Sigma.ι_desc`,
  `SimplicialObject.hom_ext`;
- core/canonical owner in the chapter: `simplicialCopower`;
- primitive data: an objectwise family `F Δ u : V.obj Δ ⟶ W.obj Δ`;
- bridge/view data: the compatibility predicate on such families;
- derived API: the compatible-family functor in the target variable `W`, packaged by the
  canonical corepresentability owner `Functor.CorepresentableBy`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma identifies maps out of `U × V` with compatible simplex-indexed
  degreewise families, naturally in the target simplicial object;
- `core/canonical`: the owner object `simplicialCopower`;
- `bridge/view`: the compatibility predicate and the compatible-family functor in this file;
- `core/canonical` owner for the universal property packaging: `Functor.CorepresentableBy`.

The refinement therefore keeps the source-facing compatible-family functor public, packages the
universal property by the canonical corepresentability owner, and uses the canonical
`CorepresentableBy.equivUliftCoyonedaIso` directly when that `uliftCoyoneda` isomorphism is
needed, rather than keeping a parallel specialized wrapper as public API. -/

section

variable (U : SSet.{w}) (V W : SimplicialObject C)

/-- A simplex-indexed degreewise family of morphisms from `V` to `W` over the simplicial set `U`.
-/
abbrev SimplicialCopowerHomFamily :=
  ∀ Δ : SimplexCategoryᵒᵖ, U.obj Δ → (V.obj Δ ⟶ W.obj Δ)

namespace SimplicialCopowerHomFamily

/-- The simplicial compatibility condition on a simplex-indexed degreewise family of morphisms. -/
def IsCompatible (F : SimplicialCopowerHomFamily U V W) : Prop :=
  ∀ ⦃Δ Δ' : SimplexCategoryᵒᵖ⦄ (f : Δ ⟶ Δ') (u : U.obj Δ),
    V.map f ≫ F Δ' (U.map f u) = F Δ u ≫ W.map f

-- Proof sketch: this is immediate from unfolding `SimplicialCopowerHomFamily.IsCompatible`.
/-- A simplex-indexed degreewise family is compatible exactly when it satisfies the displayed
simplicial commutativity condition. -/
theorem isCompatible_iff
    (F : SimplicialCopowerHomFamily U V W) :
    F.IsCompatible ↔
      ∀ ⦃Δ Δ' : SimplexCategoryᵒᵖ⦄ (f : Δ ⟶ Δ') (u : U.obj Δ),
        V.map f ≫ F Δ' (U.map f u) = F Δ u ≫ W.map f :=
  Iff.rfl

/-- Compatible simplex-indexed degreewise families of morphisms. -/
abbrev Compatible :=
  { F : SimplicialCopowerHomFamily U V W // F.IsCompatible }

end SimplicialCopowerHomFamily

end

section

variable (U : SSet.{w}) (V : SimplicialObject C)

open SimplicialCopowerHomFamily

private def postcomposeFamily
    {W W' : SimplicialObject C} (g : W ⟶ W')
    (F : Compatible U V W) :
    SimplicialCopowerHomFamily U V W' :=
  fun Δ u ↦ F.1 Δ u ≫ g.app Δ

private theorem postcomposeCompatibleFamily_isCompatible
    {W W' : SimplicialObject C} (g : W ⟶ W')
    (F : Compatible U V W) :
    (postcomposeFamily U V g F).IsCompatible := by
  intro Δ Δ' f u
  -- Proof comment: compose the compatibility relation for `F` with `g.app Δ'` and rewrite
  -- the right-hand side using the naturality square for `g`.
  calc
    V.map f ≫ (postcomposeFamily U V g F) Δ' (U.map f u)
        = V.map f ≫ F.1 Δ' (U.map f u) ≫ g.app Δ' := by
            rfl
    _ = F.1 Δ u ≫ W.map f ≫ g.app Δ' := by
          simpa [Category.assoc] using
            congrArg (fun t => t ≫ g.app Δ') (F.2 f u)
    _ = F.1 Δ u ≫ g.app Δ ≫ W'.map f := by
          simpa [Category.assoc] using
            congrArg (fun t => F.1 Δ u ≫ t) (g.naturality f)
    _ = (postcomposeFamily U V g F) Δ u ≫ W'.map f := by
          simp [postcomposeFamily, Category.assoc]

private def postcomposeCompatibleFamily
    {W W' : SimplicialObject C} (g : W ⟶ W')
    (F : Compatible U V W) :
    Compatible U V W' :=
  ⟨postcomposeFamily U V g F, postcomposeCompatibleFamily_isCompatible U V g F⟩

/-- The functor sending a target simplicial object `W` to the compatible simplex-indexed families
of degreewise morphisms `V.obj Δ ⟶ W.obj Δ` appearing in Equation (14.13.0.1). -/
def simplicialCopowerCompatibleFamilyFunctor :
    SimplicialObject C ⥤ Type (max w v) where
  obj W := Compatible U V W
  map g := postcomposeCompatibleFamily U V g
  map_id W := by
    funext F
    apply Subtype.ext
    funext Δ u
    simp [postcomposeCompatibleFamily, postcomposeFamily]
  map_comp g h := by
    funext F
    apply Subtype.ext
    funext Δ u
    simp [postcomposeCompatibleFamily, postcomposeFamily]

end

section

variable (U : SSet.{w}) (V W : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ V.obj Δ)]

open SimplicialCopowerHomFamily

/-- A morphism `U × V ⟶ W` determines an objectwise family of component
morphisms by precomposing with the coproduct injections in each simplicial degree. -/
private def homToFamily (f : U × V ⟶ W) :
    SimplicialCopowerHomFamily U V W :=
  fun Δ u ↦ Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ f.app Δ

-- Proof sketch: use the naturality of `f`, unfold `simplicialCopower_map`, and compare both
-- sides after precomposing with the coproduct injection indexed by `u`.
/-- The family induced by a morphism out of `U × V` satisfies the simplicial
compatibility condition. -/
private theorem homToFamily_isCompatible (f : U × V ⟶ W) :
    (homToFamily U V W f).IsCompatible := by
  intro Δ Δ' σ u
  -- Proof comment: precompose the naturality equation of `f` with the coproduct injection
  -- indexed by `u`, then normalize the coproduct map of `U × V`.
  have h :=
    congrArg
      (fun t =>
        Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ t)
      (f.naturality σ)
  simpa [homToFamily, simplicialCopower_map, Category.assoc] using h

/-- The canonical compatible family associated to a morphism out of `U × V`. -/
private def homToCompatibleFamily (f : U × V ⟶ W) : Compatible U V W :=
  ⟨homToFamily U V W f, homToFamily_isCompatible U V W f⟩

-- Proof sketch: compare both sides after precomposing with every coproduct injection
-- `Sigma.ι _ u`; the compatibility condition in `F.2` is exactly the required naturality square.
/-- A compatible objectwise family of morphisms assembles into a morphism of simplicial objects
from `U × V` to `W`. -/
private theorem compatibleFamilyToHom_commSq
    (F : Compatible U V W)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    CommSq ((U × V).map f) (Limits.Sigma.desc (fun u ↦ F.1 Δ u))
      (Limits.Sigma.desc (fun u ↦ F.1 Δ' u)) (W.map f) := by
  refine CommSq.mk ?_
  -- Proof comment: the source is a coproduct, so it suffices to compare both composites after
  -- precomposing with each coproduct injection.
  apply Limits.Sigma.hom_ext
  intro u
  calc
    Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ (U × V).map f ≫ Limits.Sigma.desc (fun v ↦ F.1 Δ' v)
        = V.map f ≫ Sigma.ι (fun _ : U.obj Δ' ↦ V.obj Δ') (U.map f u) ≫
            Limits.Sigma.desc (fun v ↦ F.1 Δ' v) := by
            have h :=
              congrArg
                (fun t => t ≫ Limits.Sigma.desc (fun v : U.obj Δ' ↦ F.1 Δ' v))
                (Sigma.ι_comp_map' (p := U.map f) (q := fun _ ↦ V.map f) u)
            simpa [simplicialCopower_map, Category.assoc] using h
    _ = V.map f ≫ F.1 Δ' (U.map f u) := by
          simpa [Category.assoc] using
            congrArg
              (fun t => V.map f ≫ t)
              (Sigma.ι_desc (fun v : U.obj Δ' ↦ F.1 Δ' v) (U.map f u))
    _ = F.1 Δ u ≫ W.map f := F.2 f u
    _ = Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ Limits.Sigma.desc (fun v ↦ F.1 Δ v) ≫ W.map f := by
          symm
          simpa [Category.assoc] using
            congrArg
              (fun t => t ≫ W.map f)
              (Sigma.ι_desc (fun v : U.obj Δ ↦ F.1 Δ v) u)

/-- A compatible objectwise family of morphisms defines a morphism
`U × V ⟶ W` by the coproduct universal property in each simplicial degree. -/
private def compatibleFamilyToHom (F : Compatible U V W) :
    U × V ⟶ W :=
  { app := fun Δ ↦ Limits.Sigma.desc (fun u ↦ F.1 Δ u)
    naturality := fun {_} {_} f ↦
      (compatibleFamilyToHom_commSq U V W F f).w }

-- Proof sketch: two morphisms out of `U × V` are equal if their components on
-- each simplicial degree agree, and each degreewise map out of a coproduct is determined by its
-- composites with the coproduct injections.
/-- Reassembling the compatible family extracted from a morphism recovers the original morphism. -/
private theorem compatibleFamilyToHom_left_inv
    (f : U × V ⟶ W) :
    compatibleFamilyToHom U V W (homToCompatibleFamily U V W f) = f := by
  -- Proof comment: compare the two simplicial morphisms degreewise, then use coproduct
  -- extensionality in each degree.
  apply SimplicialObject.hom_ext
  intro Δ
  apply Limits.Sigma.hom_ext
  intro u
  simpa [compatibleFamilyToHom, homToCompatibleFamily, homToFamily] using
    (Sigma.ι_desc (fun v : U.obj Δ ↦ Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) v ≫ f.app Δ) u)

-- Proof sketch: a compatible family is recovered from the assembled morphism by evaluating the
-- coproduct desc map on each injection `Sigma.ι _ u`.
/-- Extracting the compatible family from the assembled morphism recovers the original family. -/
private theorem compatibleFamilyToHom_right_inv
    (F : Compatible U V W) :
    homToCompatibleFamily U V W (compatibleFamilyToHom U V W F) = F := by
  apply Subtype.ext
  -- Proof comment: evaluating the reassembled map on the `u`-summand gives back the original
  -- family component by the coproduct-desc computation rule.
  funext Δ u
  simpa [homToCompatibleFamily, homToFamily, compatibleFamilyToHom] using
    (Sigma.ι_desc (fun v : U.obj Δ ↦ F.1 Δ v) u)

/-- Postcomposing a morphism `U × V ⟶ W₁` with `g : W₁ ⟶ W₂` corresponds to postcomposing the
associated compatible family degreewise. -/
private theorem homToCompatibleFamily_comp
    {W₁ W₂ : SimplicialObject C} (g : W₁ ⟶ W₂) (f : U × V ⟶ W₁) :
    homToCompatibleFamily U V W₂ (f ≫ g) =
      (simplicialCopowerCompatibleFamilyFunctor U V).map g (homToCompatibleFamily U V W₁ f) := by
  apply Subtype.ext
  funext Δ u
  simp [homToCompatibleFamily, homToFamily, simplicialCopowerCompatibleFamilyFunctor,
    postcomposeCompatibleFamily, postcomposeFamily, Category.assoc]

/-- Lemma 14.13.2 in canonical owner form: the compatible-family functor is corepresented by
`U × V`. -/
noncomputable def simplicialCopowerCompatibleFamilyCorepresentableBy :
    (simplicialCopowerCompatibleFamilyFunctor U V).CorepresentableBy (U × V) where
  homEquiv {W} :=
    { toFun := homToCompatibleFamily U V W
      invFun := compatibleFamilyToHom U V W
      left_inv := compatibleFamilyToHom_left_inv U V W
      right_inv := compatibleFamilyToHom_right_inv U V W }
  homEquiv_comp g f := homToCompatibleFamily_comp U V g f

/-- Evaluating the canonical compatible family attached to `f : U × V ⟶ W` amounts to
precomposing `f.app Δ` with the coproduct injection indexed by `u`. -/
@[simp] theorem simplicialCopowerCompatibleFamilyCorepresentableBy_homEquiv_apply
    (f : U × V ⟶ W) (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    ((simplicialCopowerCompatibleFamilyCorepresentableBy (U := U) (V := V)).homEquiv f).1 Δ u =
      Sigma.ι (fun _ : U.obj Δ ↦ V.obj Δ) u ≫ f.app Δ := by
  -- Proof comment: the `homEquiv` was defined by the family extracted from `f`, so evaluation is
  -- exactly the coproduct-injection formula.
  rfl

end

end CategoryTheory
