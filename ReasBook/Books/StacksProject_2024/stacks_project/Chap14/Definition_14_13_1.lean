import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

-- Declarations for this item will be appended below by the statement pipeline.

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
    simpa only [Functor.map_id] using
      (Sigma.map'_id_id (f := fun _ : U.obj Δ ↦ V.obj Δ))
  map_comp := by
    intro Δ₀ Δ₁ Δ₂ σ τ
    apply Sigma.hom_ext
    intro x
    simp

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
    simpa only [Functor.map_id] using
      (Sigma.map'_id_id (f := fun _ : U.obj Δ ↦ V.obj Δ))
  map_comp := by
    intro Δ₀ Δ₁ Δ₂ σ τ
    apply Sigma.hom_ext
    intro x
    simp

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
