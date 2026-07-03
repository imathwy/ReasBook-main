import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_13_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ V.obj Δ)]

/- Domain-style sampling for Definition 14.13.1:
- primary domain: simplicial objects built degreewise from simplicial-set-indexed coproducts;
- inspected same-kind owner API:
  `CategoryTheory.Limits.Sigma.map'`,
  `CategoryTheory.Limits.Sigma.map'_id_id`,
  `CategoryTheory.Limits.Sigma.map'_comp_map'`,
  `CategoryTheory.Limits.sigmaFunctor`,
  `CategoryTheory.Limits.Sigma.ι_desc`;
- best owner abstraction:
  the source-facing owner is the simplicial-set action `U × V`, while the degreewise coproduct
  objects and reindexing maps come directly from the canonical coproduct API;
- primitive-vs-derived split:
  primitive data are the simplicial set `U`, the simplicial object `V`, and the degreewise
  coproduct hypotheses;
  the term objects, structure maps, and their identity/composition laws are derived from
  `∐`, `Sigma.map'`, and the canonical coproduct lemmas.

Source/core/bridge triage:
- `source-facing`: the simplicial-set-indexed product `U × V`;
- `core/canonical`: the degreewise coproduct owner API `∐`, `Sigma.map'`, and its functoriality
  lemmas;
- `bridge/view`: the object and map formulas recorded below for `U × V`. -/

/-- Definition 14.13.1: assuming the displayed coproducts exist in each simplicial degree, the
product `U × V` of a simplicial set `U` and a simplicial object `V` is the simplicial copower
whose term in degree `Δ` is the coproduct of copies of `V.obj Δ` indexed by the simplices of `U`
in degree `Δ`, and whose structure maps are induced by the maps of `U` on indices and the maps of
`V` on each summand. -/
def simplicialCopower : SimplicialObject C where
  obj Δ := ∐ (fun _ : U.obj Δ ↦ V.obj Δ)
  map f := Sigma.map' (U.map f) (fun _ ↦ V.map f)
  map_id := by
    intro Δ
    rw [Functor.map_id, Functor.map_id]
    exact (Sigma.map'_id_id : Sigma.map' id (fun _ : U.obj Δ ↦ 𝟙 (V.obj Δ)) = 𝟙 _)
  map_comp := by
    intro Δ₀ Δ₁ Δ₂ σ τ
    apply Sigma.hom_ext
    intro x
    simp [Functor.map_comp, Category.assoc]

/-- Textbook notation for the simplicial-set-indexed product `U × V`. -/
scoped[Simplicial] infixr:70 " × " => simplicialCopower

/-- The degree-`Δ` term of `U × V` is the coproduct of copies of `V.obj Δ` indexed by the
simplices of `U` in degree `Δ`. -/
@[simp] theorem simplicialCopower_obj (Δ : SimplexCategoryᵒᵖ) :
    (U × V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ) :=
  rfl

/-- The structure map of `U × V` along `f` is the coproduct morphism obtained
by applying `V.map f` on each summand and reindexing the target summand by `U.map f`. -/
@[simp] theorem simplicialCopower_map {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (U × V).map f =
      Sigma.map' (U.map f) (fun _ ↦ V.map f) :=
  rfl

section Truncated

variable {n : ℕ}
variable (U : SSet.Truncated n) (V : SimplicialObject.Truncated C n)
variable [∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ V.obj Δ)]

/-- The truncated simplicial-set-indexed product `U × V` in `Δ_{≤ n}`. Degreewise it is the
coproduct of copies of `V.obj Δ` indexed by the simplices of `U` in degree `Δ`, with structure
maps induced by the truncated simplicial operators of `U` and `V`. -/
def truncatedSimplicialCopower : SimplicialObject.Truncated C n where
  obj Δ := ∐ (fun _ : U.obj Δ ↦ V.obj Δ)
  map f := Sigma.map' (U.map f) (fun _ ↦ V.map f)
  map_id := by
    intro Δ
    rw [Functor.map_id, Functor.map_id]
    exact (Sigma.map'_id_id : Sigma.map' id (fun _ : U.obj Δ ↦ 𝟙 (V.obj Δ)) = 𝟙 _)
  map_comp := by
    intro Δ₀ Δ₁ Δ₂ σ τ
    apply Sigma.hom_ext
    intro x
    simp [Functor.map_comp, Category.assoc]

/-- The degree-`Δ` term of the truncated copower `U × V`. -/
@[simp] theorem truncatedSimplicialCopower_obj (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (truncatedSimplicialCopower U V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ) :=
  rfl

/-- The structure map of the truncated copower `U × V` along `f`. -/
@[simp] theorem truncatedSimplicialCopower_map {Δ Δ' : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : Δ ⟶ Δ') :
    (truncatedSimplicialCopower U V).map f =
      Sigma.map' (U.map f) (fun _ ↦ V.map f) :=
  rfl

end Truncated

end CategoryTheory

/-! ### Lemma_14_13_2 (from Chap14) -/
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
    (postcomposeFamily U V g F).IsCompatible := sorry

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
    (homToFamily U V W f).IsCompatible := sorry

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
      (Limits.Sigma.desc (fun u ↦ F.1 Δ' u)) (W.map f) := sorry

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
    compatibleFamilyToHom U V W (homToCompatibleFamily U V W f) = f := sorry

-- Proof sketch: a compatible family is recovered from the assembled morphism by evaluating the
-- coproduct desc map on each injection `Sigma.ι _ u`.
/-- Extracting the compatible family from the assembled morphism recovers the original family. -/
private theorem compatibleFamilyToHom_right_inv
    (F : Compatible U V W) :
    homToCompatibleFamily U V W (compatibleFamilyToHom U V W F) = F := sorry

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

end

end CategoryTheory

/-! ### Lemma_14_13_3 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.13.3:
- primary domain: functoriality bridges for the simplicial copower owner `simplicialCopower`;
- sampled same-kind declarations:
  `simplicialCopower`,
  `simplicialCopower_map`,
  `simplicialCopowerCompatibleFamilyFunctor`,
  `Functor.const`,
  `Sigma.map'`,
  `CommSq`;
- best owner abstractions:
  the chapter owner `simplicialCopower`, organized first as the fixed-`U` functor
  `simplicialCopowerFunctor U : SimplicialObject C ⥤ SimplicialObject C`,
  then as the fixed-`X` functor
  `simplicialCopowerIndexFunctor X : SSet ⥤ SimplicialObject C`;
- primitive data:
  in the simplicial-object variable, a morphism `f : W ⟶ W'` together with the degreewise
  coproducts defining `U × W` and `U × W'`;
  in the simplicial-set variable, a morphism `a : U ⟶ V` together with the degreewise coproducts
  defining `U × X` and `V × X`;
- derived API:
  the pairwise object-variable bridge map `simplicialCopowerHom U f`, the pairwise reindexing
  bridge map `simplicialCopowerIndexHom X a`, the fixed-`U` functor
  `simplicialCopowerFunctor U`, the fixed-`X` functor `simplicialCopowerIndexFunctor X`,
  the object-variable projection naturality theorem `simplicialCopowerProjection_naturality U`,
  the owner-facing natural transformation `simplicialCopowerProjectionNatTrans U`,
  and the fixed-`X` bridge `simplicialCopowerProjectionIndexNatTrans X`.

Source/core/bridge triage:
- `source-facing`: Lemma 14.13.3 is the bifunctorial simplicial copower construction
  `(U, X) ↦ U × X`, together with the canonical projection `U × X ⟶ X`;
- `core/canonical`: the fixed-`U` owner `simplicialCopowerFunctor U` and the fixed-`X` owner
  `simplicialCopowerIndexFunctor X`;
- `bridge/view`: the pairwise maps `simplicialCopowerHom U f` and
  `simplicialCopowerIndexHom X a`, which preserve the weaker source-faithful coproduct
  hypotheses on only the objects that actually occur. A bundled
  `SSet ⥤ SimplicialObject C ⥤ SimplicialObject C` owner is intentionally not exposed here,
  because it would force a stronger global coproduct hypothesis than the chapter’s fixed-`U` and
  fixed-`(U, X)` APIs actually use. -/

section ObjectVariable

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w})
variable {W W' W₁ W₂ W₃ : SimplicialObject C}

/-- Naturality of the canonical map induced by a simplicial morphism on simplicial copowers. -/
private theorem simplicialCopowerHom_naturality
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W'.obj Δ)]
    (f : W ⟶ W') {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (U × W).map σ ≫ Limits.Sigma.map (fun _ : U.obj Δ₂ ↦ f.app Δ₂) =
      Limits.Sigma.map (fun _ : U.obj Δ₁ ↦ f.app Δ₁) ≫ (U × W').map σ := sorry

/-- The morphism of simplicial copowers induced by a simplicial morphism in the simplicial-object
variable. -/
def simplicialCopowerHom
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W'.obj Δ)]
    (f : W ⟶ W') :
    U × W ⟶ U × W' where
  app Δ := Limits.Sigma.map (fun _ : U.obj Δ ↦ f.app Δ)
  naturality := fun {_ _} σ ↦ simplicialCopowerHom_naturality U f σ

/-- The component in simplicial degree `Δ` of the object-variable bridge map on simplicial
copowers. -/
@[simp]
theorem simplicialCopowerHom_app
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W'.obj Δ)]
    (f : W ⟶ W') (Δ : SimplexCategoryᵒᵖ) :
    (simplicialCopowerHom U f).app Δ =
      Limits.Sigma.map (fun _ : U.obj Δ ↦ f.app Δ) :=
  rfl

-- Proof sketch: both transformations are determined by their components on each coproduct summand,
-- where the statement reduces to the identity components of `f`.
/-- Identity law for the functoriality of `W ↦ U × W`. -/
private theorem simplicialCopowerHom_id
    (W : SimplicialObject C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W.obj Δ)]
    :
    simplicialCopowerHom U (𝟙 W) = 𝟙 (U × W) := sorry

-- Proof sketch: compare components in each simplicial degree and on each coproduct summand; the
-- result is the functoriality of the natural transformation components.
/-- Composition law for the functoriality of `W ↦ U × W`. -/
private theorem simplicialCopowerHom_comp
    (W₁ W₂ W₃ : SimplicialObject C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W₁.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W₂.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ W₃.obj Δ)]
    (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) :
    simplicialCopowerHom U (f ≫ g) = simplicialCopowerHom U f ≫ simplicialCopowerHom U g := sorry

end ObjectVariable

section ObjectVariableFunctor

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w})

variable
    [∀ X : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]

/-- Under fixed-`U` degreewise coproduct hypotheses, the simplicial copower construction
`X ↦ U × X` is a functor. -/
def simplicialCopowerFunctor : SimplicialObject C ⥤ SimplicialObject C where
  obj X := U × X
  map f := simplicialCopowerHom U f
  map_id := fun X ↦ simplicialCopowerHom_id U X
  map_comp := fun f g ↦ simplicialCopowerHom_comp U _ _ _ f g

end ObjectVariableFunctor

section IndexVariable

variable {C : Type u} [Category.{v} C]
variable {U V U₁ U₂ U₃ : SSet.{w}}
variable (X : SimplicialObject C)

/-- Naturality of the degreewise coproduct map induced by a simplicial-set morphism. -/
private theorem simplicialCopowerIndexHom_app_naturality
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    (a : U ⟶ V) {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (U × X).map σ ≫ Sigma.map' (a.app Δ₂) (fun _ ↦ 𝟙 (X.obj Δ₂)) =
      Sigma.map' (a.app Δ₁) (fun _ ↦ 𝟙 (X.obj Δ₁)) ≫ (V × X).map σ := sorry

/-- The morphism of simplicial copowers induced by a morphism of simplicial sets in the indexing
variable. -/
def simplicialCopowerIndexHom
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    (a : U ⟶ V) :
    U × X ⟶ V × X where
  app Δ := Sigma.map' (a.app Δ) (fun _ ↦ 𝟙 (X.obj Δ))
  naturality := fun {_ _} σ ↦ simplicialCopowerIndexHom_app_naturality X a σ

/-- The component in simplicial degree `Δ` of the reindexing morphism on simplicial copowers. -/
@[simp]
theorem simplicialCopowerIndexHom_app
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    (a : U ⟶ V) (Δ : SimplexCategoryᵒᵖ) :
    (simplicialCopowerIndexHom X a).app Δ =
      Sigma.map' (a.app Δ) (fun _ ↦ 𝟙 (X.obj Δ)) :=
  rfl

-- Proof sketch: after precomposing with any coproduct injection, both composites are the
-- structure morphism `X.map σ`, because the projection is the identity on each summand.
/-- Naturality of the canonical projection from a simplicial copower to its simplicial-object
variable. -/
private theorem simplicialCopowerProjection_app_naturality
    (U : SSet.{w})
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    (U × X).map σ ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 (X.obj Δ₂)) =
      Limits.Sigma.desc (fun _ ↦ 𝟙 (X.obj Δ₁)) ≫ X.map σ := sorry

/-- The canonical projection `U × X ⟶ X` from the simplicial copower to its simplicial-object
variable. In each simplicial degree it is the coproduct map that is the identity on every
summand. -/
def simplicialCopowerProjection
    (U : SSet.{w})
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)] :
    U × X ⟶ X where
  app Δ := Limits.Sigma.desc (fun _ ↦ 𝟙 (X.obj Δ))
  naturality := fun {_ _} σ ↦ simplicialCopowerProjection_app_naturality X U σ

/-- The component in simplicial degree `Δ` of the canonical projection `U × X ⟶ X`. -/
@[simp]
theorem simplicialCopowerProjection_app
    (U : SSet.{w})
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    (Δ : SimplexCategoryᵒᵖ) :
    (simplicialCopowerProjection X U).app Δ =
      Limits.Sigma.desc (fun _ ↦ 𝟙 (X.obj Δ)) :=
  rfl

-- Proof sketch: in each simplicial degree, precompose both composites with each coproduct
-- injection `Sigma.ι _ u`; both sides reduce to `f.app Δ`.
/-- The canonical projections `U × X ⟶ X` are natural in the simplicial-object variable. -/
theorem simplicialCopowerProjection_naturality
    (U : SSet.{w}) {X Y : SimplicialObject C}
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ Y.obj Δ)]
    (f : X ⟶ Y) :
    CommSq (simplicialCopowerHom U f) (simplicialCopowerProjection X U)
      (simplicialCopowerProjection Y U) f := sorry

section ProjectionNatTrans

variable (U : SSet.{w})

variable
    [∀ Y : SimplicialObject C, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ Y.obj Δ)]

/-- The canonical projections `U × X ⟶ X` assemble into a natural transformation from the
object-variable copower functor to the identity functor. -/
def simplicialCopowerProjectionNatTrans :
    simplicialCopowerFunctor U ⟶ 𝟭 (SimplicialObject C) where
  app Y := simplicialCopowerProjection Y U
  naturality := fun {_ _} f ↦ (simplicialCopowerProjection_naturality U f).w

end ProjectionNatTrans

-- Proof sketch: compare both composites in simplicial degree `Δ` after precomposing with each
-- coproduct summand indexed by `u : U.obj Δ`; the statement reduces to the naturality square of
-- `f`.
/-- Lemma 14.13.3 in bridge form: reindexing a simplicial copower along a simplicial-set map fits
into the canonical commutative square in the simplicial-object variable. -/
theorem simplicialCopowerIndexHom_naturality
    {X Y : SimplicialObject C}
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ Y.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ Y.obj Δ)]
    (a : U ⟶ V) (f : X ⟶ Y) :
    CommSq (simplicialCopowerHom U f) (simplicialCopowerIndexHom X a)
      (simplicialCopowerIndexHom Y a) (simplicialCopowerHom V f) := sorry

-- Proof sketch: evaluate the reindexing morphism on each simplicial degree; it is the identity
-- coproduct map because the indexing map is the identity on `U`.
/-- Identity law for reindexing simplicial copowers in the simplicial-set variable. -/
theorem simplicialCopowerIndexHom_id
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    :
    simplicialCopowerIndexHom X (𝟙 U) = 𝟙 (U × X) := sorry

-- Proof sketch: evaluate in each simplicial degree and use the composition law for the
-- reindexing maps on coproducts.
/-- Composition law for reindexing simplicial copowers in the simplicial-set variable. -/
theorem simplicialCopowerIndexHom_comp
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U₁.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U₂.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U₃.obj Δ ↦ X.obj Δ)]
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) :
    simplicialCopowerIndexHom X (a ≫ b) =
      simplicialCopowerIndexHom X a ≫ simplicialCopowerIndexHom X b := sorry

-- Proof sketch: in each simplicial degree, both composites are the coproduct desc map that is the
-- identity on every summand, so compare after precomposing with the coproduct injections.
/-- Bridge/view: the canonical projection `U × X ⟶ X` is natural in the simplicial-set variable.
-/
theorem simplicialCopowerProjection_index_naturality
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : V.obj Δ ↦ X.obj Δ)]
    (a : U ⟶ V) :
    CommSq (simplicialCopowerIndexHom X a) (simplicialCopowerProjection X U)
      (simplicialCopowerProjection X V) (𝟙 X) := sorry

variable
    [∀ U : SSet.{w}, ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun _ : U.obj Δ ↦ X.obj Δ)]

-- Proof sketch: identities and compositions in the simplicial-set variable are checked
-- componentwise on the bundled reindexing morphisms `simplicialCopowerIndexHom`.
/-- Under fixed-`X` degreewise coproduct hypotheses, the simplicial copower construction
`U ↦ U × X` is a functor. -/
def simplicialCopowerIndexFunctor : SSet.{w} ⥤ SimplicialObject C where
  obj U := U × X
  map a := simplicialCopowerIndexHom X a
  map_id := fun _ ↦ simplicialCopowerIndexHom_id X
  map_comp := fun a b ↦ simplicialCopowerIndexHom_comp X a b

/-- Bridge/view: the canonical projections `U × X ⟶ X` assemble into a natural transformation
from the simplicial-set-variable copower functor to the constant functor at `X`. -/
def simplicialCopowerProjectionIndexNatTrans :
    simplicialCopowerIndexFunctor X ⟶ (Functor.const SSet.{w}).obj X where
  app U := simplicialCopowerProjection X U
  naturality := fun {_ _} a ↦ (simplicialCopowerProjection_index_naturality X a).w

end IndexVariable

end CategoryTheory

/-! ### Lemma_14_13_4 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open Opposite
open SimplexCategory
open SimplexCategory.Truncated
open SimplexCategory.Truncated.Hom
open SSet.stdSimplex
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.13.4:
- primary domain: simplicial copowers indexed by the standard simplex and their truncated
  restriction to `Δ_{≤ n}`;
- sampled same-kind declarations:
  `simplicialCopower`,
  `truncatedSimplicialCopower`,
  `simplicialCopowerCompatibleFamilyCorepresentableBy`,
  `SSet.truncation`,
  `evaluationAdjunctionRight`,
  `SSet.stdSimplex.map_apply`;
- best owner abstraction:
  the untruncated clause is owned by the chapter copower `simplicialCopower`; for the truncated
  clause, the right abstraction is the truncated chapter owner `truncatedSimplicialCopower`,
  specialized to the restricted standard simplex `(SSet.truncation n).obj (Δ[k])`, rather than
  `truncation n` of the full copower, which would force irrelevant higher-degree coproduct
  hypotheses;
- primitive data: the object `X`, the standard simplex `Δ[k]`, and for the truncated clause only
  the simplices of `Δ[k]` in truncated degrees;
- derived API: the identity simplex `objEquiv.symm (𝟙 ⦋k⦌)`, evaluation at the top truncated
  simplex `op ⦋k, hk⦌ₙ`, and the induced equivalences with maps `X ⟶ V_k`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma fixes the source simplicial set to `Δ[k]`;
  `core/canonical`: `simplicialCopower`, `truncatedSimplicialCopower`, `SSet.truncation`, and the
  representable-simplex owner `SSet.yonedaEquiv`;
  `bridge/view`: this file specializes the full copower owner to `Δ[k]`, and in the truncated
  clause specializes the truncated copower owner to the genuinely truncated source object with the
  same source-facing simplices in degrees `≤ n`. -/

variable {C : Type u} [Category.{v} C]

private instance constStdSimplexHasCoproduct (k : ℕ) (X : C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X)] :
    ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct
        (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ ((const C).obj X).obj Δ) := by
  intro Δ
  dsimp
  infer_instance

section StdSimplexProduct

variable (k : ℕ) (X : C)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X)]

private noncomputable def stdSimplexCompatibleFamilyEquiv (V : SimplicialObject C) :
    SimplicialCopowerHomFamily.Compatible (Δ[k]) ((const C).obj X) V ≃
      (X ⟶ V _⦋k⦌) :=
  { toFun := fun F ↦
      F.1 (op ⦋k⦌) (objEquiv.symm (𝟙 ⦋k⦌))
    invFun := fun f ↦
      ⟨fun Δ u ↦ f ≫ V.map (objEquiv u).op, by
        intro Δ Δ' φ u
        simp [SSet.stdSimplex.map_apply, Category.assoc]⟩
    left_inv := by
      intro F
      apply Subtype.ext
      funext Δ u
      simpa [SSet.stdSimplex.map_apply, Category.assoc] using
        (F.2 ((objEquiv u).op) (objEquiv.symm (𝟙 ⦋k⦌))).symm
    right_inv := by
      intro f
      simp }

/-- Lemma 14.13.4 (1): morphisms from `Δ[k] × X` to a simplicial object `V` are canonically in
bijection with morphisms from `X` to the degree-`k` term `V_k`. This is the specialization of
`Δ[k] × X`, followed by evaluation at the identity simplex. -/
noncomputable def stdSimplexProductHomEquiv (V : SimplicialObject C) :
    (((Δ[k] : SSet.{w}) × (const C).obj X) ⟶ V) ≃ (X ⟶ V _⦋k⦌) :=
  (simplicialCopowerCompatibleFamilyCorepresentableBy
      (Δ[k]) ((const C).obj X)).homEquiv.trans
    (stdSimplexCompatibleFamilyEquiv k X V)

-- Proof sketch: this is immediate from the definition of `stdSimplexProductHomEquiv`.
/-- The canonical bijection sends `γ : Δ[k] × X ⟶ V` to the restriction of `γ_k` to the coproduct
summand indexed by `𝟙_[k]`. -/
theorem stdSimplexProductHomEquiv_apply (V : SimplicialObject C)
    (γ : ((Δ[k] : SSet.{w}) × (const C).obj X) ⟶ V) :
    stdSimplexProductHomEquiv k X V γ =
      Sigma.ι (fun _ : (Δ[k] : SSet.{w}).obj (op ⦋k⦌) ↦ X) (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k⦌) := by
  change stdSimplexCompatibleFamilyEquiv k X V
      (((simplicialCopowerCompatibleFamilyCorepresentableBy
        (Δ[k]) ((const C).obj X)).homEquiv γ)) =
    Sigma.ι (fun _ : (Δ[k] : SSet.{w}).obj (op ⦋k⦌) ↦ X) (objEquiv.symm (𝟙 ⦋k⦌)) ≫
      γ.app (op ⦋k⦌)
  rfl

end StdSimplexProduct

section TruncatedStdSimplexProduct

variable {n k : ℕ} (hk : k ≤ n) (X : C)
variable (W : SimplicialObject.Truncated C n)

private instance truncatedStdSimplexConstHasCoproduct (n k : ℕ) (X : C)
    [∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
      HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)] :
    ∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
      HasCoproduct
        (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X).obj Δ) := by
  intro Δ
  simpa using
    (inferInstance :
      HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X))

variable [∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
  HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)]

/-- The truncated simplicial operator determined by a simplex of `Δ[k]`. -/
private def truncatedStdSimplexSimplexMap (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ) :
    op ⦋k, hk⦌ₙ ⟶ Δ :=
  (tr (objEquiv u) (unop Δ).property hk).op

private def truncatedStdSimplexProductHomEquivToFun
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    X ⟶ W _⦋k, hk⦌ₙ :=
  Sigma.ι
      (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
      (objEquiv.symm (𝟙 ⦋k⦌)) ≫
    γ.app (op ⦋k, hk⦌ₙ)

private def truncatedStdSimplexProductHomEquivInvApp
    (f : X ⟶ W _⦋k,hk⦌ₙ)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).obj Δ ⟶
      W.obj Δ :=
  Limits.Sigma.desc (fun u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦
    f ≫ W.map (truncatedStdSimplexSimplexMap hk Δ u))

-- Proof sketch: compare both composites on each coproduct summand. Naturality of the family comes
-- from composing the simplex represented by `u` with the truncated simplicial operator and then
-- applying functoriality of `W`.
private theorem truncatedStdSimplexProductHomEquivInv_naturality
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    ∀ {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (φ : Δ₁ ⟶ Δ₂),
      CommSq
        ((truncatedSimplicialCopower
            ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map φ)
        (truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₁)
        (truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₂)
        (W.map φ) := by
  intro Δ₁ Δ₂ φ
  sorry

private def truncatedStdSimplexProductHomEquivInv
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
      W where
  app Δ := truncatedStdSimplexProductHomEquivInvApp hk X W f Δ
  naturality := fun {_ _} φ ↦
    (truncatedStdSimplexProductHomEquivInv_naturality hk X W f φ).w

-- Proof sketch: extensionality on morphisms in the truncated functor category reduces the claim to
-- equality on each truncated degree, where coproduct extensionality and the standard simplex
-- identities recover the original components of `γ`.
private theorem truncatedStdSimplexProductHomEquiv_left_inv
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    truncatedStdSimplexProductHomEquivInv hk X W
        (truncatedStdSimplexProductHomEquivToFun hk X W γ) =
      γ := sorry

-- Proof sketch: at each truncated degree the reconstructed map sends the summand indexed by a
-- simplex `u : [m] → [k]` to `f` followed by `W(u)`. Evaluating at the identity simplex yields `f`.
private theorem truncatedStdSimplexProductHomEquiv_right_inv
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    truncatedStdSimplexProductHomEquivToFun hk X W
        (truncatedStdSimplexProductHomEquivInv hk X W f) =
      f := sorry

/-- Lemma 14.13.4 (2): for `n ≥ k`, morphisms from the direct truncated standard-simplex copower
to an `n`-truncated simplicial object `W` are canonically in bijection with morphisms from `X` to
the degree-`k` term `W_k`. This source object is the `Δ_{≤ n}`-level version of `Δ[k] × X`, so
its existence only uses coproducts in truncated degrees. -/
noncomputable def truncatedStdSimplexProductHomEquiv :
    (truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
      W) ≃
      (X ⟶ W _⦋k, hk⦌ₙ) :=
  { toFun := fun γ ↦
      truncatedStdSimplexProductHomEquivToFun hk X W γ
    invFun := fun f ↦
      truncatedStdSimplexProductHomEquivInv hk X W f
    left_inv := truncatedStdSimplexProductHomEquiv_left_inv hk X W
    right_inv := truncatedStdSimplexProductHomEquiv_right_inv hk X W }

-- Proof sketch: this is immediate from the definition of
-- `truncatedStdSimplexProductHomEquiv`.
/-- The truncated canonical bijection sends `γ` to the restriction of its degree-`k` component to
the coproduct summand indexed by `𝟙_[k]`. -/
theorem truncatedStdSimplexProductHomEquiv_apply
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    truncatedStdSimplexProductHomEquiv hk X W γ =
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
          (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k, hk⦌ₙ) := by
  change truncatedStdSimplexProductHomEquivToFun hk X W γ =
    Sigma.ι
        (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
        (objEquiv.symm (𝟙 ⦋k⦌)) ≫
      γ.app (op ⦋k, hk⦌ₙ)
  unfold truncatedStdSimplexProductHomEquivToFun
  simp

end TruncatedStdSimplexProduct

end CategoryTheory
