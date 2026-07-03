import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: module duality, torsion quotients, and reflexivity of finite modules over a PID;
- sampled owner declarations:
  `Module.Dual.eval`,
  `Submodule.torsion`,
  `Submodule.dualQuotEquivDualAnnihilator`,
  `Module.free_of_finite_type_torsion_free'`,
  `Module.IsReflexive.of_finite_of_free`;
- best owner abstraction: the canonical owner object is the evaluation map `Module.Dual.eval`,
  and the intrinsic source-facing reduction is through the torsion quotient
  `M ⧸ Submodule.torsion R M`; over a PID this quotient is canonically finite free, so reflexivity
  is controlled by `Module.IsReflexive`;
- primitive data: the commutative domain `R`, the principal-ideal-ring structure on `R`, and the
  finite `R`-module `M`;
- derived API: surjectivity of the source-facing evaluation map is a consequence of the canonical
  identification of `Dual R M` with the dual of the torsion-free quotient, together with
  reflexivity of that finite free quotient.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that the canonical map `M → Mᘁᘁ` is surjective for a
  finite module over a discrete valuation ring;
- `core/canonical`: `Module.Dual.eval`, `Submodule.torsion`, and `Module.IsReflexive`;
- `bridge/view`: `Submodule.dualQuotEquivDualAnnihilator` identifies `Dual R M` with the dual of
  the torsion-free quotient, and `Module.Dual.eval_naturality` compares the evaluation maps across
  the quotient.
-/

section

open Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsPrincipalIdealRing R] [Module.Finite R M] in
private theorem dual_mem_dualAnnihilator_torsion (φ : Dual R M) :
    φ ∈ (Submodule.torsion R M).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro x hx
  rcases hx with ⟨a, hax⟩
  have ha0 : (a : R) ≠ 0 := nonZeroDivisors.ne_zero a.2
  have hax' : a • φ x = 0 := by
    simpa [map_smul] using congrArg φ hax
  exact (smul_eq_zero_iff_right ha0).mp hax'

omit [IsPrincipalIdealRing R] [Module.Finite R M] in
private theorem dualMap_mkQ_torsion_bijective :
    Function.Bijective
      (((Submodule.torsion R M).mkQ : M →ₗ[R] M ⧸ Submodule.torsion R M).dualMap) := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (Submodule.torsion R M).mkQ_surjective, ?_⟩
  intro φ
  refine
    ⟨(Submodule.torsion R M).dualQuotEquivDualAnnihilator.symm
        ⟨φ, dual_mem_dualAnnihilator_torsion φ⟩, ?_⟩
  ext x
  exact
    (Submodule.torsion R M).dualQuotEquivDualAnnihilator_symm_apply_mk
      ⟨φ, dual_mem_dualAnnihilator_torsion φ⟩ x

-- Proof sketch: quotient `M` by its torsion submodule. Every linear form on `M` vanishes on
-- torsion, so `Dual R M` is canonically identified with the dual of `M / M_tors` via
-- `Submodule.dualQuotEquivDualAnnihilator`. The quotient is torsion free, hence finite free over a
-- PID and therefore reflexive by `Module.IsReflexive.of_finite_of_free`. Naturality of
-- `Module.Dual.eval` with respect to the quotient map then transports surjectivity back to `M`.
/-- Lemma 15.23.3, stated at the canonical PID owner layer: for a finite module over a principal
ideal domain, the canonical map `M → Hom_R(Hom_R(M, R), R)` is surjective. The discrete valuation
ring case is the immediate specialization. -/
theorem eval_surjective_of_isPrincipalIdealRing :
    Function.Surjective (Dual.eval R M) := by
  -- The proved bridge lemmas above reduce the theorem to the torsion-free quotient
  -- `M ⧸ Submodule.torsion R M`, which is finite free over a PID and hence reflexive.
  -- Transporting surjectivity of the quotient evaluation map back across
  -- `Submodule.dualQuotEquivDualAnnihilator` and `Module.Dual.eval_naturality` yields the claim.
  sorry

end
