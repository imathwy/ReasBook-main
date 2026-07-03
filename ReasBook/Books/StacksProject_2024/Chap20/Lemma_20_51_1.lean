import Mathlib
import StacksProject_2024.Chap13.Definition_13_33_1
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap20.Definition_20_49_1

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local instance ringedSpaceSheafModulesAbelian : Abelian (RingedSpace.Modules X) :=
  inferInstance

local instance ringedSpaceSheafModulesHasDerivedCategory :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- The inverse system of derived duals
`\cdots \to K_{n + 1}^\vee \to K_n^\vee` attached to a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(\mathcal O_X)`. -/
abbrev ringedSpaceDerivedDualInverseSystem
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    ℕᵒᵖ ⥤ DMod :=
  @Functor.ofOpSequence DMod _ (fun n ↦ (ihom (K n)).obj (𝟙_ DMod))
    (fun n ↦ (MonoidalClosed.pre (f n)).app (𝟙_ DMod))

-- Proof sketch: unfold `ringedSpaceDerivedDualInverseSystem`; `Functor.ofOpSequence` is defined
-- so that evaluation at `op n` returns the `n`-th object of the underlying sequence.
/-- The `n`-th object of the dual inverse system is the derived dual `K_n^\vee`. -/
theorem ringedSpaceDerivedDualInverseSystem_obj
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    (ringedSpaceDerivedDualInverseSystem K f).obj (op n) =
      (ihom (K n)).obj (𝟙_ DMod) := sorry

/-- The inverse system
`\cdots \to E \otimes_{\mathcal O_X}^{\mathbf L} K_{n + 1}^\vee
\to E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`
obtained by tensoring the dual inverse system stagewise with a fixed object `E`. -/
abbrev ringedSpaceDerivedDualTensorInverseSystem
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    ℕᵒᵖ ⥤ DMod :=
  @Functor.ofOpSequence DMod _ (fun n ↦ E ⊗ (ihom (K n)).obj (𝟙_ DMod))
    (fun n ↦ E ◁ (MonoidalClosed.pre (f n)).app (𝟙_ DMod))

-- Proof sketch: unfold `ringedSpaceDerivedDualTensorInverseSystem`; by construction of
-- `Functor.ofOpSequence`, the object at `op n` is exactly the `n`-th tensor-dual stage.
/-- The `n`-th object of the tensor-dual inverse system is
`E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`. -/
theorem ringedSpaceDerivedDualTensorInverseSystem_obj
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    (ringedSpaceDerivedDualTensorInverseSystem E K f).obj (op n) =
      E ⊗ (ihom (K n)).obj (𝟙_ DMod) := sorry

-- Proof sketch: apply Lemma `20.50.5` termwise to identify
-- `E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee` with `R\mathcal H\!\mathit{om}(K_n, E)`.
-- The homotopy-colimit triangle for `Khocolim` then turns, under `R\mathcal H\!\mathit{om}(-, E)`,
-- into the Milnor triangle defining a derived limit of the inverse system of these terms.
/-- Lemma 20.51.1: if `Khocolim` is a homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(\mathcal O_X)`, then for every `E ∈ D(\mathcal O_X)` the derived
internal Hom `R\mathcal H\!\mathit{om}(Khocolim, E)` is a derived limit of the inverse system
`n ↦ E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`, where `K_n^\vee` is the derived dual of
`K_n`. -/
theorem ringedSpaceDerivedInternalHom_isDerivedLimit_of_homotopyColimit
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasColimitsOfShape (Discrete ℕ) DMod]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (g : ∐ K ⟶ Khocolim)
    (δ : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g δ ∈ distTriang DMod)
    (E : DMod) :
    IsDerivedLimit
      (ringedSpaceDerivedDualTensorInverseSystem E K f)
      ((ihom Khocolim).obj E) := sorry

end

end AlgebraicGeometry.RingedSpace
