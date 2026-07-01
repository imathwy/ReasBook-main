import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Defs

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: duality in `ModuleCat R`, comparing an abstract exact pairing with the canonical
  module-dual owner of `M`;
- sampled owner declarations:
  `Definition 4.43.5` (`ExactPairing Y X` for a left dual `Y` of `X`),
  `MonoidalClosed.curry`,
  `Module.Dual`,
  `ModuleCat.homLinearEquiv`,
  `CategoryTheory.rightDualIso`,
  `BraidedCategory.exactPairing_swap`;
- best owner abstraction: the comparison from a chosen left dual is canonically the curried
  evaluation morphism into the internal Hom to the tensor unit; the module-theoretic codomain
  `Module.Dual R M = Hom_R(M, R)` is the canonical owner view of that internal-Hom object in
  `ModuleCat R`;
- primitive data: the ambient commutative ring, the two `R`-modules, and the exact pairing
  instance `[ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]`;
- derived API: the internal Hom object `(ihom (ModuleCat.of R M)).obj (𝟙_ (ModuleCat R))`, the
  currying map from the evaluation pairing, and the resulting comparison morphism to the canonical
  dual owner.

Source/core/bridge triage:
- `source-facing`: the textbook map from a left dual of `M` to `Hom_R(M, R)`;
- `core/canonical`: `MonoidalClosed.curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M))`;
- `bridge/view`: `ExactPairing.toModuleDual`, the thin codomain-change bridge from the canonical
  curried evaluation morphism to the module-dual owner `Module.Dual R M`.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ModuleCat
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [ExactPairing (ModuleCat.of R N) (ModuleCat.of R M)]

namespace ExactPairing

/-- The canonical morphism from a left dual `N` of `M` to the canonical module dual
`Module.Dual R M = Hom_R(M, R)`, obtained by currying the evaluation pairing and then identifying
the internal Hom to the tensor unit with `Module.Dual R M`. This is the inverse of the textbook
map `e`. -/
abbrev toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M) :=
  curry (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) ≫
    ((homLinearEquiv :
        (ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R)) ≃ₗ[R] Module.Dual R M).toModuleIso.hom)

-- Proof sketch: choose a finite free module surjecting onto `M`, lift the coevaluation through
-- it, and use the triangle identity to factor `𝟙_M` through that finite free module; this gives
-- finite projectivity of `M`.
/-- Lemma 15.73.1 (1): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`M` is a finite projective `R`-module. -/
theorem exactPairing_source_finite_projective :
    Module.Finite R M ∧ Module.Projective R M := sorry

-- Proof sketch: apply the same argument as for `M` after swapping the exact pairing in the
-- symmetric monoidal category `ModuleCat R`.
/-- Lemma 15.73.1 (2): if `N` is a left dual of `M` in the monoidal category of `R`-modules, then
`N` is a finite projective `R`-module. -/
theorem exactPairing_target_finite_projective :
    Module.Finite R N ∧ Module.Projective R N := sorry

-- Proof sketch: specialize the canonical hom-set equivalence of Lemma `4.43.6` to
-- `Z = 𝟙_(ModuleCat R)` and `Z' = 𝟙_(ModuleCat R)`, then identify maps out of and into the tensor
-- unit with `Module.Dual R M` and `N`.
/-- Lemma 15.73.1 (3): the canonical morphism `N ⟶ Module.Dual R M` obtained from the evaluation
pairing is an isomorphism; equivalently, the textbook map
`e : Hom_R(M, R) → N` given by `φ ↦ (φ ⊗ 1)(η)` is bijective. -/
theorem isIso_toModuleDual :
    IsIso (toModuleDual : ModuleCat.of R N ⟶ ModuleCat.of R (Module.Dual R M)) := sorry

attribute [instance] isIso_toModuleDual

-- Proof sketch: `toModuleDual` is obtained by currying the evaluation pairing and then
-- identifying the internal-Hom object to the tensor unit with `Module.Dual R M`, so evaluation
-- on `m` is literally the original pairing.
/-- Lemma 15.73.1 (4): for `n : N` and `m : M`, evaluating the functional
`toModuleDual n : Module.Dual R M` at `m` recovers the exact-pairing evaluation on
`m ⊗ n`; equivalently, this is the inverse of the textbook map `e` applied to `n` and then
evaluated at `m`. -/
theorem toModuleDual_apply (n : N) (m : M) :
    (ε_ (ModuleCat.of R N) (ModuleCat.of R M)) (m ⊗ₜ[R] n) =
      toModuleDual n m := by
  rfl

end ExactPairing

end
