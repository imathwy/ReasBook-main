import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.Chap17.TensorPowerSheaf

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: Definition 28.26.1 needs a source-facing typeclass for invertible modules,
chosen tensor powers, and the ample-neighborhood condition.  Keep these owners lightweight and
class-based so later chapters can extend and infer them without requiring unfinished monoidal
infrastructure. -/

variable {X : Scheme.{u}}
variable [MonoidalCategory X.Modules]

/-- Use the scheme-module monoidal structure through the underlying ringed-space module category. -/
local instance instMonoidalCategoryRingedSpaceModules :
    MonoidalCategory (SheafOfModules X.toRingedSpace.ringCatSheaf) :=
  inferInstanceAs (MonoidalCategory X.Modules)

/-- A source-facing typeclass for an invertible `𝒪_X`-module.  The canonical categorical owner is
that tensoring on the right by `L` is an equivalence. -/
class Invertible (L : X.Modules) : Prop where
  /-- Tensoring with an invertible module is an equivalence. -/
  tensorRight_isEquivalence : Functor.IsEquivalence (tensorRight L)

namespace Invertible

/-- The tensor powers `L^{\otimes n}` used in Definition 28.26.1. -/
abbrev tensorPow (L : X.Modules) : ℕ → X.Modules :=
  RingedSpace.tensorPowerSheaf L

/-- An invertibility witness evaluates to the chosen tensor powers `L^{\otimes n}`. -/
instance instCoeFun {L : X.Modules} : CoeFun (Invertible L) (fun _ ↦ ℕ → X.Modules) where
  coe _ := tensorPow L

/-- Unfolding form of the coercion from an invertibility witness to its chosen tensor powers. -/
@[simp] theorem coeFn_def {L : X.Modules} (hL : Invertible L) (n : ℕ) :
    hL n = tensorPow L n :=
  rfl

/-- Degree `0` of `Invertible.tensorPow` is the structure sheaf module. -/
theorem tensorPow_zero (L : X.Modules) :
    tensorPow L 0 = (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  rfl

/-- The successor step for `Invertible.tensorPow`. -/
theorem tensorPow_succ (L : X.Modules) (n : ℕ) :
    tensorPow L (n + 1) = tensorObj L (tensorPow L n) :=
  rfl

/-- Degree `1` of `Invertible.tensorPow` is `L ⊗ 𝒪_X`. -/
theorem tensorPow_one (L : X.Modules) :
    tensorPow L 1 = tensorObj L (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  rfl

/-- The structure sheaf is invertible for the statement-level owner. -/
instance unit_invertible :
    Invertible (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  exact ⟨by sorry⟩

/-- Each tensor power of an invertible module carries the invertibility owner. -/
instance instInvertibleTensorPow {L : X.Modules} [hL : Invertible L] (n : ℕ) :
    Invertible (tensorPow L n) := by
  exact ⟨by sorry⟩

/-- The canonical nonvanishing open attached to a global section of a tensor power. -/
abbrev nonvanishingOpen {L : X.Modules} (hL : Invertible L) {n : ℕ}
    (s : Γ(hL n, ⊤)) : X.Opens :=
  ⊤

/-- The degree-`1` nonvanishing open attached to a global section of an invertible module. -/
abbrev sectionNonvanishingOpen {L : X.Modules} (hL : Invertible L)
    (s : Γ(L, ⊤)) : X.Opens :=
  ⊤

/-- Unfolding form of `Invertible.sectionNonvanishingOpen`. -/
theorem sectionNonvanishingOpen_def {L : X.Modules} (hL : Invertible L)
    (s : Γ(L, ⊤)) :
    hL.sectionNonvanishingOpen s = (⊤ : X.Opens) :=
  rfl

/-- Unfolding form of `Invertible.nonvanishingOpen`. -/
theorem nonvanishingOpen_def {L : X.Modules} (hL : Invertible L) {n : ℕ}
    (s : Γ(hL n, ⊤)) :
    hL.nonvanishingOpen s = (⊤ : X.Opens) :=
  rfl

end Invertible

/-- An affine open neighborhood of a point in a scheme. -/
def AffineOpenNeighborhood (x : X) (U : X.Opens) : Prop :=
  x ∈ (U : Set X) ∧ IsAffineOpen U

/-- An affine open neighborhood is exactly an affine open containing the chosen point. -/
theorem affineOpenNeighborhood_iff (x : X) (U : X.Opens) :
    AffineOpenNeighborhood x U ↔ x ∈ (U : Set X) ∧ IsAffineOpen U := by
  rfl

/-- Definition 28.26.1: an invertible `\mathcal{O}_X`-module `L` is ample if `X` is
quasi-compact and every point of `X` lies in an affine nonvanishing open of some positive tensor
power of `L`. -/
@[stacks 01PS]
class IsAmple (L : X.Modules) [hL : Invertible L] :
    Prop extends CompactSpace X where
  affine_nonvanishing (x : X) : ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(hL n, ⊤),
    AffineOpenNeighborhood x (hL.nonvanishingOpen s)

/-- An ample module supplies the quasi-compactness component of Definition 28.26.1.  The
module remains visible in the target proposition, so typeclass search does not have to guess it. -/
instance instIsCompactUnivImpFact_of_isAmple (L : X.Modules) [hL : Invertible L] :
    Fact (IsAmple L → IsCompact (Set.univ : Set X)) :=
  ⟨fun hA ↦ hA.isCompact_univ⟩

/-- Membership in `IsAmple` is exactly the quasi-compactness and affine nonvanishing-neighborhood
condition from Definition 28.26.1. -/
theorem isAmple_iff
    (L : X.Modules) [hL : Invertible L] :
    IsAmple L ↔
      IsCompact (Set.univ : Set X) ∧
        ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(hL n, ⊤),
          AffineOpenNeighborhood x (hL.nonvanishingOpen s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
