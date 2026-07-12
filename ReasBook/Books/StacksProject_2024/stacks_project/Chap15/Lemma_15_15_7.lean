import Mathlib.LinearAlgebra.Dual.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/- Domain-style sampling:
- primary domain: quotient duality and annihilator calculus for submodules of finite free modules;
- sampled owner declarations of the same kind:
  `Module.Free.chooseBasis`,
  `Submodule.dualQuotEquivDualAnnihilator`,
  `Submodule.dualAnnihilator_eq_bot_iff'`,
  `LinearMap.ker_dualMap_eq_dualAnnihilator_range`;
- best owner abstraction: the source-facing theorem should be stated for an intrinsic endomorphism
  `φ : M →ₗ[R] M` of a finite free module `M`, while
  `Submodule.dualQuotEquivDualAnnihilator` is the canonical owner identifying the dual of a
  quotient with the dual annihilator of the defining submodule;
- source/core/bridge triage:
  `source-facing`: every `R`-linear functional on the cokernel of an injective endomorphism of a
    finite free module is zero;
  `core/canonical`: the owner-side vanishing statement
    `(LinearMap.range φ).dualAnnihilator = ⊥`;
  `bridge/view`: `Submodule.dualQuotEquivDualAnnihilator` and
    `Submodule.dualAnnihilator_eq_bot_iff'`.

Primitive data are only the endomorphism `φ` and the finite free owner data on `M`; its range is
derived from `φ`. The quotient-dual vanishing statement is derived API from the
quotient/annihilator owner layer, so this file should keep only the source-facing theorem public
and use the owner-level equality internally as a bridge.
-/

-- Proof sketch: `Submodule.dualQuotEquivDualAnnihilator` identifies the dual of the quotient by
-- `LinearMap.range φ` with the dual annihilator of `LinearMap.range φ`. The private owner-side
-- bridge below shows that annihilator is `⊥`, so the quotient dual is a subsingleton and every
-- functional is zero.
private theorem range_dualAnnihilator_eq_bot_of_injective_free_endomorphism
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    (LinearMap.range φ).dualAnnihilator = ⊥ := by
  -- Route correction: the intended proof passes through local injectivity of the transpose map
  -- from Lemma 15.15.6, then globalizes that kernel computation via the coordinate-dual helpers
  -- above.
  -- TODO: reintroduce the source-faithful transpose/localization argument once a compilable owner
  -- of Lemma 15.15.6 is available in the dependency closure.
  sorry

/-- Lemma 15.15.7: if `φ : M → M` is an injective endomorphism of a finite free `R`-module, then
every `R`-linear functional on its cokernel is zero. -/
theorem quotient_range_dual_eq_zero_of_injective_free_endomorphism
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) (f : Module.Dual R (M ⧸ LinearMap.range φ)) :
    f = 0 := by
  -- First collapse the owner-side dual annihilator of the image to `⊥`.
  have hRange : (LinearMap.range φ).dualAnnihilator = ⊥ :=
    range_dualAnnihilator_eq_bot_of_injective_free_endomorphism φ hφ
  -- Then the quotient dual is a subsingleton via the canonical quotient/annihilator equivalence.
  have hsub : Subsingleton (Module.Dual R (M ⧸ LinearMap.range φ)) := by
    simpa using (Submodule.dualAnnihilator_eq_bot_iff').mp hRange
  exact hsub.elim f 0

end
