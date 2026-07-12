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

/-- Helper for Lemma 15.23.3: the quotient by the torsion submodule is reflexive because over a
principal ideal domain it is finite, torsion free, and therefore free. -/
private theorem torsion_quotient_is_reflexive :
    IsReflexive R (M ⧸ Submodule.torsion R M) := by
  -- The quotient by torsion is torsion free, so the PID structure theorem makes it free.
  letI : Module.Free R (M ⧸ Submodule.torsion R M) := Module.free_of_finite_type_torsion_free'
  -- Finite free modules are reflexive.
  exact Module.IsReflexive.of_finite_of_free (R := R) (M := M ⧸ Submodule.torsion R M)

/-- Helper for Lemma 15.23.3: once the torsion quotient is reflexive, its canonical evaluation map
is surjective. -/
private theorem torsion_quotient_eval_surjective :
    Function.Surjective (Dual.eval R (M ⧸ Submodule.torsion R M)) := by
  -- Reflexivity upgrades the quotient evaluation map to a bijection.
  letI : IsReflexive R (M ⧸ Submodule.torsion R M) := torsion_quotient_is_reflexive (R := R)
    (M := M)
  exact (bijective_dual_eval R (M ⧸ Submodule.torsion R M)).surjective

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
  let q : M →ₗ[R] M ⧸ Submodule.torsion R M := (Submodule.torsion R M).mkQ
  have hqDual : Function.Bijective q.dualMap := by
    -- Every functional on `M` factors uniquely through the quotient by torsion.
    simpa [q] using (dualMap_mkQ_torsion_bijective (R := R) (M := M))
  let eDual : Dual R (M ⧸ Submodule.torsion R M) ≃ₗ[R] Dual R M :=
    LinearEquiv.ofBijective q.dualMap hqDual
  -- First solve the problem on the torsion-free quotient, where finite-free reflexivity applies.
  have hQuotEval :
      Function.Surjective (Dual.eval R (M ⧸ Submodule.torsion R M)) :=
    torsion_quotient_eval_surjective (R := R) (M := M)
  intro ψ
  let ψQ : Dual R (Dual R (M ⧸ Submodule.torsion R M)) := eDual.dualMap ψ
  obtain ⟨y, hy⟩ := hQuotEval ψQ
  -- Lift the chosen quotient element back to `M` and compare evaluations through the dual map.
  obtain ⟨x, hxq⟩ := (Submodule.torsion R M).mkQ_surjective y
  refine ⟨x, ?_⟩
  ext φ
  let phiQ : Dual R (M ⧸ Submodule.torsion R M) := eDual.symm φ
  have hφ : q.dualMap phiQ = φ := by
    -- The transported functional `phiQ` is exactly the preimage of `φ` under the dual equivalence.
    change eDual phiQ = φ
    exact eDual.apply_symm_apply φ
  have hψQ : ψQ phiQ = ψ (eDual phiQ) := rfl
  have heDual : eDual phiQ = φ := eDual.apply_symm_apply φ
  calc
    Dual.eval R M x φ = φ x := rfl
    _ = (q.dualMap phiQ) x := by rw [hφ]
    _ = phiQ (q x) := by rw [LinearMap.dualMap_apply]
    _ = phiQ y := by rw [hxq]
    _ = ψQ phiQ := by
      simpa using congrArg (fun f => f phiQ) hy
    _ = ψ (eDual phiQ) := hψQ
    _ = ψ φ := by rw [heDual]

end
