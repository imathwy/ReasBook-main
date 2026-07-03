import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Data.PNat.Basic
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The finite-stage `I^n`-torsion submodule of `M`, i.e. the source-facing finite ideal-power
torsion owner underlying the chapter notation `M[I^n]`. -/
abbrev powerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    Submodule R M :=
  Submodule.torsionBySet R M ↑(I ^ n)

end Ideal

namespace IdealPowerTorsion

open Lean Elab Term Meta

variable {R : Type u} [CommRing R]

/- Source-facing notation for finite and infinite power torsion submodules. The index can be an
ideal `I`, giving `M[I^n]` and `M[I^∞]`, or an element `f`, giving the principal specializations
`M[f^n]` and `M[f^∞]`. The notation is a thin bridge to the canonical owners
`Submodule.torsionBySet`, `Ideal.primaryComponent`, `Submodule.torsionBy`, and
`Submodule.torsion'`; the implementation support stays confined to the
`IdealPowerTorsion` namespace. -/
syntax:lead term:max noWs "[" term:max "^" term:max "]" : term
syntax:lead term:max noWs "[" term:max "^∞]" : term

private def elabFinitePowerTorsion
    (M a n : TSyntax `term) : TermElabM Expr := do
  let aExpr ← elabTerm a none
  let aType ← inferType aExpr
  if aType.isAppOf ``Ideal then
    elabTerm (← `((Ideal.powerTorsion $a $M $n))) none
  else
    elabTerm (← `((Submodule.torsionBy _ $M ($a ^ $n)))) none

private def elabInfinitePowerTorsion
    (M a : TSyntax `term) : TermElabM Expr := do
  let aExpr ← elabTerm a none
  let aType ← inferType aExpr
  if aType.isAppOf ``Ideal then
    elabTerm (← `((($a).primaryComponent $M))) none
  else
    elabTerm (← `((Submodule.torsion' _ $M (Submonoid.powers $a)))) none

@[term_elab IdealPowerTorsion.«term__[_^_]»] private def elabTermFinitePowerTorsion : TermElab
  | stx, _ => elabFinitePowerTorsion ⟨stx[0]⟩ ⟨stx[2]⟩ ⟨stx[4]⟩

@[term_elab IdealPowerTorsion.«term__[_^∞]»] private def elabTermInfinitePowerTorsion : TermElab
  | stx, _ => elabInfinitePowerTorsion ⟨stx[0]⟩ ⟨stx[2]⟩

end IdealPowerTorsion

namespace Module

open scoped DirectSum
open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]

section

/- 
Domain-style sampling pass for Definition 15.89.1.

Primary domain: commutative algebra of ideal-power torsion modules.

Sampled owner declarations:
* `Submodule.torsionBySet` from mathlib's torsion-submodule API;
* `Ideal.primaryComponent` and `Ideal.primaryComponent_mem` from mathlib's primary-component API;
* `Module.IsTorsion'` and `Submodule.isTorsion'_iff_torsion'_eq_top` from mathlib's
  powers-torsion API.

Best owner abstraction: the source-facing module predicate should be the chapter owner
`Module.IsIdealPowerTorsion I M`, with its core owner given directly by `Ideal.primaryComponent`
and its source-facing theorem surface written using the chapter notation `M[I^n]`, `M[I^∞]`,
`M[f^n]`, and `M[f^∞]`.
-/

/-- Definition 15.89.1 (1): an `R`-module is `I`-power torsion if every element is annihilated by
some positive power of the ideal `I`, equivalently if `M[I^∞] = ⊤`. -/
abbrev IsIdealPowerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  (M[I^∞] : Submodule R M) = ⊤

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The predicate `IsIdealPowerTorsion I` means that each module element is killed by some
positive power of `I`. -/
theorem isIdealPowerTorsion_iff (I : Ideal R) :
    IsIdealPowerTorsion I M ↔
      ∀ x : M, ∃ n : ℕ+, ∀ a : ↥(I ^ (n : ℕ)), (a : R) • x = 0 := by
  constructor
  · intro hM x
    have hx : x ∈ (M[I^∞] : Submodule R M) := by
      rw [hM]
      exact Submodule.mem_top
    rw [Ideal.primaryComponent_mem] at hx
    obtain ⟨n, hn⟩ := hx
    rw [Submodule.mem_torsionBySet_iff] at hn
    refine ⟨⟨n + 1, Nat.succ_pos n⟩, fun a ↦ ?_⟩
    exact hn ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) a.2⟩
  · intro hM
    refine Submodule.eq_top_iff'.2 fun x ↦ ?_
    rw [Ideal.primaryComponent_mem]
    obtain ⟨n, hn⟩ := hM x
    exact ⟨(n : ℕ), by simpa [Submodule.mem_torsionBySet_iff] using hn⟩

/-- The quotient `R ⧸ I^n` is `I`-power torsion. -/
theorem isIdealPowerTorsion_quotient_pow (I : Ideal R) (n : ℕ) :
    IsIdealPowerTorsion I (R ⧸ (I ^ n)) := sorry

/-- Linear-equivalent modules have the same `I`-power torsion property. -/
theorem isIdealPowerTorsion_iff_of_linearEquiv
    (I : Ideal R) {N : Type*} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) :
    IsIdealPowerTorsion I M ↔ IsIdealPowerTorsion I N := sorry

/-- A direct sum of `I`-power torsion modules is `I`-power torsion. -/
theorem isIdealPowerTorsion_directSum
    (I : Ideal R) {ι : Type*} {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    (hA : ∀ i, IsIdealPowerTorsion I (A i)) :
    IsIdealPowerTorsion I (⨁ i, A i) := sorry

/-- Definition 15.89.1 (2): specializing to the principal ideal `(f)` identifies the chapter
notation `M[(f)^∞]` with the canonical `f`-power torsion submodule. -/
theorem primaryComponent_principalIdeal_eq_fPowerTorsion (f : R) :
    (M[(principalIdeal f)^∞] : Submodule R M) = M[f^∞] := by
  ext x
  constructor
  · intro hx
    have hx₀ :
        ∃ n, x ∈ Submodule.torsionBySet R M ↑(principalIdeal f ^ n) := by
      simpa using (Ideal.primaryComponent_mem M (principalIdeal f) x).1 hx
    rcases hx₀ with ⟨n, hx⟩
    have hx' : x ∈ Submodule.torsionBy R M (f ^ n) := by
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx
    rw [Submodule.mem_torsionBy_iff] at hx'
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, hx'⟩
  · rintro ⟨⟨a, ha⟩, hx⟩
    rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨n, hn⟩
    have hx' : x ∈ Submodule.torsionBy R M (f ^ n) := by
      rw [Submodule.mem_torsionBy_iff]
      exact hn.symm ▸ hx
    refine (Ideal.primaryComponent_mem M (principalIdeal f) x).2 ?_
    exact ⟨n, by
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'⟩

/-- Definition 15.89.1 (2): specializing to the principal ideal `(f)` recovers mathlib's
canonical `f`-power torsion predicate `Module.IsTorsion' M (Submonoid.powers f)`. -/
theorem isIdealPowerTorsion_principalIdeal_iff (f : R) :
    IsIdealPowerTorsion (principalIdeal f) M ↔ IsTorsion' M (Submonoid.powers f) := by
  rw [IsIdealPowerTorsion, primaryComponent_principalIdeal_eq_fPowerTorsion]
  simpa using (Submodule.isTorsion'_iff_torsion'_eq_top (Submonoid.powers f)).symm

end

end Module
