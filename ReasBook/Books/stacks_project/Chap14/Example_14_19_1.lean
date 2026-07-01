import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Example 14.19.1:
- primary domain: simplicial objects modeling `cosk₀`, equivalently the Čech nerve of the terminal
  map out of `X`;
- sampled owner API:
  `cechNerveTerminalFrom`,
  `CechNerveTerminalFrom.iso`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the file's main item is `source-facing`, since it constructs the explicit
  simplicial object `n ↦ X^(n + 1)` under the weaker hypothesis that only those self-products of
  `X` exist. Under stronger global finite-product hypotheses, the canonical owner is
  `cechNerveTerminalFrom X`, and when the right Kan extensions exist the further `core/canonical`
  owner is `Truncated.cosk 0`.
- source/core/bridge triage:
  `source-facing`: the explicit self-product model and its degree-zero universal property;
  `core/canonical`: `cechNerveTerminalFrom X` and `Truncated.cosk 0`;
  `bridge/view`: under `[HasFiniteProducts C]`, the canonical isomorphism
  `CechNerveTerminalFrom.iso X` together with the definitional identification below, since
  mathlib's owner `cechNerveTerminalFrom X` is the same self-product simplicial object up to the
  product-instance choices.
- primitive data: the degreewise products `∏ᶜ (fun _ : Fin (n + 1) ↦ X)` and the reindexing maps
  induced by simplex operators;
- derived API: the projection formula, the bridge to `cechNerveTerminalFrom X`, and the bijection
  with degree-zero morphisms. -/

section SelfProduct

variable {C : Type u} [Category.{v} C]
variable (X : C)
variable [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) ↦ X)]

/-- The simplicial object whose `n`-simplices are the `(n + 1)`-fold self-product of `X`. -/
noncomputable def zeroCoskeletonSelfProduct : SimplicialObject C where
  obj Δ := ∏ᶜ fun _ : Fin (Δ.unop.len + 1) ↦ X
  map f := Pi.lift fun i ↦ Pi.π _ ((f.unop).toOrderHom i)
  map_id := by
    intro Δ
    apply Pi.hom_ext
    intro i
    simpa using
      (Pi.lift_π (fun j ↦ Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) j) i)
  map_comp := by
    intro Δ₁ Δ₂ Δ₃ f g
    apply Pi.hom_ext
    intro i
    rw [Category.assoc]
    simp only [Pi.lift_π]
    simp [unop_comp, SimplexCategory.comp_toOrderHom]

-- Proof sketch: the structure map in simplicial degree `f` is defined by `Pi.lift`; composing
-- with the `i`-th target projection simply selects the source projection indexed by
-- `(f.unop).toOrderHom i`.
/-- The map on a simplex operator in `zeroCoskeletonSelfProduct X` is characterized by its effect
on the product projections. -/
@[simp, reassoc]
theorem zeroCoskeletonSelfProduct_map_π
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (i : Fin (Δ'.unop.len + 1)) :
    (zeroCoskeletonSelfProduct X).map f ≫
        Pi.π (fun _ : Fin (Δ'.unop.len + 1) ↦ X) i =
      Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) ((f.unop).toOrderHom i) := by
  simpa [zeroCoskeletonSelfProduct] using
    (Pi.lift_π (fun j ↦ Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) ((f.unop).toOrderHom j)) i)

-- Proof sketch: a simplicial morphism into `zeroCoskeletonSelfProduct X` is determined by its
-- degree-zero component because every higher component is forced by the projection formulas from
-- `zeroCoskeletonSelfProduct_map_π`; conversely, a map `V₀ ⟶ X` induces compatible maps
-- `Vₙ ⟶ X^{n + 1}` by precomposing with the simplicial operators `[0] ⟶ [n]`.
/-- Example 14.19.1: if the nonempty finite self-products of `X` exist, then the simplicial object
with `n`-simplices `X^(n + 1)` has the universal property of `cosk₀(X)`: for every simplicial
object `V`, taking the degree-zero component gives the canonical bijection between morphisms
`V ⟶ zeroCoskeletonSelfProduct X` and morphisms `V₀ ⟶ X`. -/
noncomputable def zeroCoskeletonSelfProductHomEquiv
    (V : SimplicialObject C) :
    (V ⟶ zeroCoskeletonSelfProduct X) ≃ (V _⦋0⦌ ⟶ X) where
  toFun f := f.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0
  invFun g :=
    { app := fun Δ ↦
        Pi.lift fun i ↦ V.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op ≫ g
      naturality := sorry }
  left_inv := sorry
  right_inv := sorry

end SelfProduct

section SelfProductBridge

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (X : C)

local instance (n : ℕ) : HasProduct (fun _ : Fin (n + 1) ↦ X) := by
  infer_instance

/-- Under finite products, the explicit self-product model of Example 14.19.1 is canonically
isomorphic to the mathlib owner `cechNerveTerminalFrom X`. -/
noncomputable def zeroCoskeletonSelfProductIsoCechNerveTerminalFrom :
    zeroCoskeletonSelfProduct X ≅ cechNerveTerminalFrom X :=
  Iso.refl _

end SelfProductBridge

end CategoryTheory
