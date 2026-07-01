import stacks_project.Chap14.Definition_14_13_1

-- Declarations for this item will be appended below by the statement pipeline.

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
