import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: module isomorphisms after adjoining finite free summands;
- sampled owner declarations: `Module.Free`, `Module.Finite`, `LinearEquiv.prodCongr`, and
  `Module.Free.pi`;
- best owner abstraction: the source-facing owners here are `StablyIsomorphic` and `StablyFree`,
  while finite generation is already canonically owned by `Module.Finite`;
- primitive vs. derived: stable isomorphism and stable freeness are primitive content of this
  item, but "finite stably free" is only the conjunction of two existing owners and should stay a
  downstream combination rather than a separate wrapper class.
-/

/-- Definition 15.3.1: two `R`-modules are stably isomorphic if there exist `m, n ≥ 0` such that
`M ⊕ R^{\oplus m}` and `N ⊕ R^{\oplus n}` are isomorphic as `R`-modules, modeled in Lean by the
product modules `M × (Fin m → R)` and `N × (Fin n → R)`. -/
@[stacks 0BC3]
def StablyIsomorphic : Prop :=
  ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- An `R`-module is stably free if it is stably isomorphic to a free module. -/
class StablyFree : Prop where
  exists_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      StablyIsomorphic R M F

/-- Stable isomorphism is reflexive. -/
-- Proof sketch: take `m = n = 0`; then the added finite free summands are trivial, and the
-- resulting linear equivalence is induced by the identity equivalence on `M`.
theorem stablyIsomorphic_refl : StablyIsomorphic R M M :=
  ⟨0, 0, ⟨LinearEquiv.refl R (M × (Fin 0 → R))⟩⟩

/-- Every free module is stably free. -/
instance stablyFree_of_free [Module.Free R M] : StablyFree R M where
  exists_free := by
    refine ⟨ULift.{max u v} M, inferInstance, inferInstance, inferInstance, ?_⟩
    refine ⟨0, 0, ⟨?_⟩⟩
    exact LinearEquiv.prodCongr ULift.moduleEquiv.symm (LinearEquiv.refl R (Fin 0 → R))

end

end Module

open CategoryTheory

section

variable (R : Type u) [Ring R]

/-- The object property of finite stably free `R`-modules in `ModuleCat R`. -/
abbrev finiteStablyFreeModuleProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Finite R M ∧ Module.StablyFree R M

end
