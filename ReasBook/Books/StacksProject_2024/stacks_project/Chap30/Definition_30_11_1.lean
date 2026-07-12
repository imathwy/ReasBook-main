import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap30.Lemma_30_9_1
import StacksProject_2024.Chap30.Definition_30_11_1_Scheme

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

private theorem finiteStalkOfIsFinitePresentation
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := by
  sorry

instance stalkModuleCat_finite
    (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) :
    Module.Finite (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := by
  let _ : ℱ.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation (X := X) ℱ).mp inferInstance
  exact finiteStalkOfIsFinitePresentation ℱ x

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.Scheme.Modules`,
-- `AlgebraicGeometry.instIsNoetherianRingCarrierStalkCommRingCatPresheafOfIsLocallyNoetherian`,
-- and `Module.supportDim`; the source definitions are therefore best exposed directly as
-- stalkwise depth conditions for coherent `\mathcal O_X`-modules.

/-- Definition 30.11.1 (1): a coherent `\mathcal O_X`-module `ℱ` has depth `k` at a point `x`
if `depth_{\mathcal O_{X, x}}(\mathcal F_x) = k`. -/
def hasDepthAt (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) : Prop :=
  moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k

/-- Unfold the depth-at-a-point condition for a coherent `\mathcal O_X`-module. -/
theorem hasDepthAt_def (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) :
    hasDepthAt ℱ x k =
      (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k) :=
  rfl

/-- Unfold the depth-at-a-point condition for a coherent `\mathcal O_X`-module. -/
@[simp] theorem hasDepthAt_iff (ℱ : X.Modules) [ℱ.IsCoherent] (x : X) (k : ℕ) :
    hasDepthAt ℱ x k ↔
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) = k :=
  Iff.rfl

/-- Definition 30.11.1 (3): a coherent `\mathcal O_X`-module `ℱ` satisfies `(S_k)` if for every
point `x` the depth of the stalk `\mathcal F_x` over `\mathcal O_{X, x}` is at least
`min (k, dim (Supp(\mathcal F_x)))`. -/
def satisfiesSerreConditionS (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) : Prop :=
  ∀ x : X,
    WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
      min (k : WithBot ℕ∞)
        (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))

/-- Unfold the stalkwise `(S_k)` condition for a coherent `\mathcal O_X`-module. -/
theorem satisfiesSerreConditionS_def
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) :
    satisfiesSerreConditionS ℱ k =
      (∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x))) :=
  rfl

/-- Unfold the stalkwise `(S_k)` condition for a coherent `\mathcal O_X`-module. -/
@[simp] theorem satisfiesSerreConditionS_iff
    (ℱ : X.Modules) [ℱ.IsCoherent] (k : ℕ) :
    satisfiesSerreConditionS ℱ k ↔
      ∀ x : X,
        WithBot.some (moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) : ℕ∞) ≥
          min (k : WithBot ℕ∞)
            (Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

attribute [local instance] AlgebraicGeometry.Scheme.Modules.structureSheaf_isCoherent

private theorem moduleDepth_structureSheaf_stalk (x : X) :
    moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒪X x) =
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  simpa using
    moduleDepth_eq_of_equiv
      (RingedSpace.unitStalkLinearEquiv (X := X.toRingedSpace) x)

omit [IsLocallyNoetherian X] in
private theorem supportDim_structureSheaf_stalk (x : X) :
    Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat 𝒪X x) =
      Module.supportDim (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  simpa using
    Module.supportDim_eq_of_equiv
      (RingedSpace.unitStalkLinearEquiv (X := X.toRingedSpace) x)

/-- Scheme depth is the coherent-module depth predicate for the structure sheaf. -/
theorem hasDepthAt_iff_structureSheaf (x : X) (k : ℕ) :
    hasDepthAt X x k ↔ Scheme.Modules.hasDepthAt (ℱ := 𝒪X) x k :=
by
  rw [hasDepthAt, Scheme.Modules.hasDepthAt, moduleDepth_structureSheaf_stalk (X := X) x]

/-- Scheme property `(S_k)` is the coherent-module `(S_k)` predicate for the structure sheaf. -/
theorem satisfiesSerreConditionS_iff_structureSheaf (k : ℕ) :
    satisfiesSerreConditionS X k ↔ Scheme.Modules.satisfiesSerreConditionS (ℱ := 𝒪X) k :=
by
  rw [satisfiesSerreConditionS_def, Scheme.Modules.satisfiesSerreConditionS_def]
  constructor
  · intro h
    intro x
    rw [moduleDepth_structureSheaf_stalk (X := X) x, supportDim_structureSheaf_stalk (X := X) x]
    exact h x
  · intro h
    intro x
    rw [← moduleDepth_structureSheaf_stalk (X := X) x,
      ← supportDim_structureSheaf_stalk (X := X) x]
    exact h x

end AlgebraicGeometry.Scheme
