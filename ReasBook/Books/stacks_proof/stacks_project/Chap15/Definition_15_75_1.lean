import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.StacksAttribute

noncomputable section

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

attribute [local instance] HasDerivedCategory.standard

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

namespace CochainComplex

/-- A cochain complex of `R`-modules is bounded finite projective if it is bounded on both sides
and each term is a finite projective `R`-module. -/
class IsBoundedFiniteProjective (L : Cpx) : Prop where
  /-- The complex is bounded on both sides. -/
  bounded : ∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b
  /-- Each term is a finite `R`-module. -/
  finite (n : ℤ) : Module.Finite R (L.X n)
  /-- Each term is a projective `R`-module. -/
  projective (n : ℤ) : Module.Projective R (L.X n)

/-- A bounded finite-projective complex is exactly a bounded complex with termwise finite
projective terms. -/
theorem isBoundedFiniteProjective_iff (L : Cpx) :
    IsBoundedFiniteProjective L ↔
      (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) ∧
        (∀ n : ℤ, Module.Finite R (L.X n)) ∧
          ∀ n : ℤ, Module.Projective R (L.X n) := by
  constructor
  · intro h
    exact ⟨h.bounded, h.finite, h.projective⟩
  · rintro ⟨hbounded, hfinite, hprojective⟩
    exact ⟨hbounded, hfinite, hprojective⟩

/-- Terms of a bounded finite projective complex are finite modules. -/
instance (L : Cpx) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Finite R (L.X n) :=
  h.finite n

/-- Terms of a bounded finite projective complex are projective modules. -/
instance (L : Cpx) [h : IsBoundedFiniteProjective L] (n : ℤ) :
    Module.Projective R (L.X n) :=
  h.projective n

end CochainComplex

namespace DerivedCategory

/-- Definition 15.75.1 (1): An object of `D(R)` is perfect if it is isomorphic in the derived
category to a bounded cochain complex of finite projective `R`-modules. -/
@[stacks 0657]
def IsPerfect (K : DMod) : Prop :=
  ∃ (L : Cpx) (_ : K ≅ Q.obj L),
    CochainComplex.IsBoundedFiniteProjective L

instance isPerfect_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsPerfect : ObjectProperty DMod) where
  of_iso e hK := by
    rcases hK with ⟨L, hL, hfinite⟩
    exact ⟨L, e.symm ≪≫ hL, hfinite⟩

end DerivedCategory

namespace ModuleCat

/-- Definition 15.75.1 (2): An `R`-module is perfect if its degree-zero complex is a perfect
object of `D(R)`. -/
@[stacks 0657]
abbrev IsPerfect (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPerfect ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)

end ModuleCat
