import Mathlib
import StacksProject_2024.stacks_project.Chap11.Lemma_11_4_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/- Domain-style sampling for Lemma 11.4.10:
- primary domain: Azumaya algebras and finite-dimensional central simple algebras over a field;
- sampled owner declarations:
  `CSA`,
  `AlgHom.mulLeftRight`,
  `IsAzumaya`,
  `IsAzumaya.AlgHom.mulLeftRight_bij`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: the `core/canonical` owner is the typeclass `IsAzumaya k A`; this file
  is a `source-facing` bridge from a central simple algebra `A : CSA k` to that owner;
- primitive data: only the central simple algebra `A : CSA k`;
- derived API: the `IsAzumaya k A` instance and the source-facing theorem `CSA.isAzumaya`.

Source/core/bridge triage:
- `source-facing`: every finite central simple `k`-algebra is Azumaya over `k`;
- `core/canonical`: `IsAzumaya k A`;
- `bridge/view`: bijectivity of the canonical left-right action map `AlgHom.mulLeftRight k A`. -/

private theorem mulLeftRight_bijective :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let f : (A ⊗[k] Aᵐᵒᵖ) →ₗ[k] Module.End k A := (AlgHom.mulLeftRight k A).toLinearMap
  haveI : IsSimpleRing (A ⊗[k] Aᵐᵒᵖ) := by
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor
  have h_inj : Function.Injective f := by
    exact RingHom.injective (AlgHom.mulLeftRight k A).toRingHom
  have h_op : Module.finrank k Aᵐᵒᵖ = Module.finrank k A := by
    simpa using
      (LinearEquiv.finrank_eq (MulOpposite.opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ)).symm
  have h_finrank :
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ) = Module.finrank k (Module.End k A) := by
    calc
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ)
          = Module.finrank k A * Module.finrank k A := by
              rw [Module.finrank_tensorProduct, h_op]
      _ = Module.finrank k (Module.End k A) := by
            symm
            simpa using (Module.finrank_linearMap k k A A)
  have h_surj : Function.Surjective (AlgHom.mulLeftRight k A) := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp h_inj
  exact ⟨h_inj, h_surj⟩

instance instIsAzumaya : IsAzumaya k A where
  bij := mulLeftRight_bijective A

-- Proof sketch: Lemma 11.4.8 makes `A ⊗[k] Aᵐᵒᵖ` simple, so the canonical left-right action map
-- `AlgHom.mulLeftRight k A` is injective; source and target have the same `k`-dimension, hence it
-- is bijective. This is the owner-level Azumaya equivalence attached to the central simple algebra
-- `A`.
/-- Lemma 11.4.10: a finite central simple `k`-algebra is Azumaya over `k`. -/
theorem isAzumaya : IsAzumaya k A := inferInstance

end CSA
