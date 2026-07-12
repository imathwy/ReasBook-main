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
/-- Helper for Example 14.19.1: the simplicial morphism reconstructed from a degree-zero map has
in degree `Δ` the product map whose `i`-th coordinate reads off the `i`-th vertex of `Δ`. -/
noncomputable def zeroCoskeletonSelfProductHomFromZeroApp
    {V : SimplicialObject C} (g : V _⦋0⦌ ⟶ X) (Δ : SimplexCategoryᵒᵖ) :
    V.obj Δ ⟶ (zeroCoskeletonSelfProduct X).obj Δ :=
  Pi.lift fun i ↦ V.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op ≫ g

/-- Helper for Example 14.19.1: the reconstructed degreewise maps are natural in the simplex
variable, so they assemble to a simplicial morphism. -/
theorem zeroCoskeletonSelfProductHomFromZero_naturality
    {V : SimplicialObject C} (g : V _⦋0⦌ ⟶ X)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    V.map f ≫ zeroCoskeletonSelfProductHomFromZeroApp X g Δ' =
      zeroCoskeletonSelfProductHomFromZeroApp X g Δ ≫ (zeroCoskeletonSelfProduct X).map f := by
  -- Compare both maps after postcomposing with each target projection.
  apply Pi.hom_ext
  intro i
  -- Both coordinates are induced by the same composite `[0] ⟶ Δ.unop`.
  calc
    (V.map f ≫ zeroCoskeletonSelfProductHomFromZeroApp X g Δ') ≫
        Pi.π (fun _ : Fin (Δ'.unop.len + 1) ↦ X) i =
      V.map f ≫ (V.map (SimplexCategory.const ⦋0⦌ Δ'.unop i).op ≫ g) := by
          rw [Category.assoc]
          simpa [zeroCoskeletonSelfProductHomFromZeroApp] using
            congrArg (fun k ↦ V.map f ≫ k)
              (Pi.lift_π
                (fun j : Fin (Δ'.unop.len + 1) ↦
                  V.map (SimplexCategory.const ⦋0⦌ Δ'.unop j).op ≫ g) i)
    _ =
        V.map (f ≫ (SimplexCategory.const ⦋0⦌ Δ'.unop i).op) ≫ g := by
          rw [Functor.map_comp, Category.assoc]
    _ = V.map (SimplexCategory.const ⦋0⦌ Δ.unop ((f.unop).toOrderHom i)).op ≫ g := by
          have hconst :
              f ≫ (SimplexCategory.const ⦋0⦌ Δ'.unop i).op =
                (SimplexCategory.const ⦋0⦌ Δ.unop ((f.unop).toOrderHom i)).op := by
            exact congrArg Quiver.Hom.op (SimplexCategory.const_comp ⦋0⦌ f.unop i)
          rw [hconst]
    _ =
      (zeroCoskeletonSelfProductHomFromZeroApp X g Δ ≫ (zeroCoskeletonSelfProduct X).map f) ≫
        Pi.π (fun _ : Fin (Δ'.unop.len + 1) ↦ X) i := by
          rw [Category.assoc, zeroCoskeletonSelfProduct_map_π]
          simpa [zeroCoskeletonSelfProductHomFromZeroApp] using
            (Pi.lift_π
              (fun j : Fin (Δ.unop.len + 1) ↦
                V.map (SimplexCategory.const ⦋0⦌ Δ.unop j).op ≫ g)
              ((f.unop).toOrderHom i)).symm

/-- Helper for Example 14.19.1: a degree-zero map determines a simplicial morphism into the
self-product model by taking all vertex pullbacks in every degree. -/
noncomputable def zeroCoskeletonSelfProductHomFromZero
    (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) :
    V ⟶ zeroCoskeletonSelfProduct X where
  app := zeroCoskeletonSelfProductHomFromZeroApp X g
  naturality := fun {_} {_} f ↦
    zeroCoskeletonSelfProductHomFromZero_naturality (X := X) (V := V) g f

/-- Helper for Example 14.19.1: evaluating the reconstructed simplicial morphism in degree `0`
and projecting to the unique factor recovers the original map. -/
theorem zeroCoskeletonSelfProductHomFromZero_app_zero_pi
    (V : SimplicialObject C) (g : V _⦋0⦌ ⟶ X) :
    (zeroCoskeletonSelfProductHomFromZero X V g).app (op ⦋0⦌) ≫
      Pi.π (fun _ : Fin 1 ↦ X) 0 = g := by
  -- The unique projection from the one-fold product picks out the unique coordinate.
  calc
    (zeroCoskeletonSelfProductHomFromZero X V g).app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0 =
      V.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op ≫ g := by
          simpa [zeroCoskeletonSelfProductHomFromZero, zeroCoskeletonSelfProductHomFromZeroApp]
            using
              (Pi.lift_π
                (fun i : Fin 1 ↦ V.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ i).op ≫ g) 0)
    _ = g := by
          -- The only map `[0] ⟶ [0]` is the identity, so the coordinate is exactly `g`.
          have hconst : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
            simpa using (eq_const_of_zero (𝟙 ⦋0⦌)).symm
          have hop : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = 𝟙 (op ⦋0⦌) := by
            exact congrArg Quiver.Hom.op hconst
          rw [hop]
          simp

/-- Helper for Example 14.19.1: a simplicial morphism into the self-product model is uniquely
determined by its degree-zero component. -/
theorem zeroCoskeletonSelfProductHomFromZero_left_inv
    (V : SimplicialObject C) (γ : V ⟶ zeroCoskeletonSelfProduct X) :
    zeroCoskeletonSelfProductHomFromZero X V
        (γ.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0) =
      γ := by
  -- Two simplicial morphisms are equal once all degreewise product projections agree.
  apply SimplicialObject.hom_ext
  intro Δ
  apply Pi.hom_ext
  intro i
  -- Naturality along the vertex map `[0] ⟶ Δ.unop` transports the degree-zero coordinate.
  have hγ := γ.naturality (SimplexCategory.const ⦋0⦌ Δ.unop i).op
  calc
    (zeroCoskeletonSelfProductHomFromZero X V
          (γ.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0)).app Δ ≫
        Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) i =
      V.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op ≫
        (γ.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0) := by
          simpa [zeroCoskeletonSelfProductHomFromZero, zeroCoskeletonSelfProductHomFromZeroApp]
            using
              (Pi.lift_π
                (fun j : Fin (Δ.unop.len + 1) ↦
                  V.map (SimplexCategory.const ⦋0⦌ Δ.unop j).op ≫
                    (γ.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0)) i)
    _ = γ.app Δ ≫ (zeroCoskeletonSelfProduct X).map (SimplexCategory.const ⦋0⦌ Δ.unop i).op ≫
          Pi.π (fun _ : Fin 1 ↦ X) 0 := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ Pi.π (fun _ : Fin 1 ↦ X) 0) hγ
    _ = γ.app Δ ≫ Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) i := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ γ.app Δ ≫ k)
              (zeroCoskeletonSelfProduct_map_π (X := X)
                ((SimplexCategory.const ⦋0⦌ Δ.unop i).op) (0 : Fin 1))

/-- Example 14.19.1: if the nonempty finite self-products of `X` exist, then the simplicial object
with `n`-simplices `X^(n + 1)` has the universal property of `cosk₀(X)`: for every simplicial
object `V`, taking the degree-zero component gives the canonical bijection between morphisms
`V ⟶ zeroCoskeletonSelfProduct X` and morphisms `V₀ ⟶ X`. -/
@[stacks 0182]
noncomputable def zeroCoskeletonSelfProductHomEquiv
    (V : SimplicialObject C) :
    (V ⟶ zeroCoskeletonSelfProduct X) ≃ (V _⦋0⦌ ⟶ X) where
  toFun f := f.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0
  invFun := zeroCoskeletonSelfProductHomFromZero X V
  left_inv := zeroCoskeletonSelfProductHomFromZero_left_inv X V
  right_inv := zeroCoskeletonSelfProductHomFromZero_app_zero_pi X V

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
