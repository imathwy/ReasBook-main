import Mathlib
import stacks_project.Chap10.Definition_10_14_1
import stacks_project.Chap10.Remark_10_133_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PrincipalParts TensorProduct
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

/-
Domain triage:
* primary domain: principal parts and their behavior under base change;
* sampled owner API:
  `principal_parts_module`,
  `principalPartsBaseChangeMap`,
  `tensorBaseChangeModuleMap`,
  `IsBaseChange`,
  `TensorProduct.isBaseChange`,
  `IsBaseChange.equiv`;
* source-facing layer here: principal parts commute with base change along the pushout square
  `A → B`, `A → A'`, `B → B ⊗[A] A'`;
* core/canonical owner: `IsBaseChange B' (principalPartsBaseChangeMap k
  (tensorBaseChangeModuleMap M))`;
* bridge/view: the later textbook model `M ⊗[A] A'`, obtained from the owner tensor by
  `Algebra.IsPushout.cancelBaseChange` and tensor symmetry; the lifted tensor map and its
  bijectivity are derived API from the owner abstraction.

Primitive data are the canonical base-change map `M → (B ⊗[A] A') ⊗[B] M` and the upstream owner
`principalPartsBaseChangeMap`; the comparison on principal parts is controlled canonically by the
owner predicate `IsBaseChange`, while the lifted tensor map and its bijectivity are derived API.
-/

variable {A B A' : Type u}
variable [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A']

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.right_isScalarTower

variable {M : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

local notation "B'" => B ⊗[A] A'
local notation "M'" => B' ⊗[B] M

-- Proof sketch: identify `P^{k}_{B'⁄A'}(M')` as the base change of `P^{k}_{B⁄A}(M)` along
-- `B → B'` via the owner-level predicate `IsBaseChange` applied to the canonical comparison map
-- `principalPartsBaseChangeMap k (tensorBaseChangeModuleMap M)`.
/-- Owner-level base-change form of Lemma 10.133.8: the canonical principal-parts comparison map
realizes `P^k_{B'⁄A'}(M')` as the base change of `P^k_{B⁄A}(M)` along `B → B'`. -/
theorem principalPartsBaseChangeMap_isBaseChange (k : ℕ) :
    IsBaseChange B' (principalPartsBaseChangeMap k (tensorBaseChangeModuleMap M) :
      P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M')) := by
  sorry

-- The source-facing tensor-product formulation is the derived bijectivity statement attached to
-- the owner-level base-change theorem above.
/-- Lemma 10.133.8: the canonical lifted principal-parts base-change map is bijective. -/
theorem principal_parts_module_base_change_bijective (k : ℕ) :
    Function.Bijective
      (((principalPartsBaseChangeMap k (tensorBaseChangeModuleMap M)).liftBaseChange B') :
        B' ⊗[B] P^{k}_{B⁄A}(M) →ₗ[B'] P^{k}_{B'⁄A'}(M')) := by
  sorry
