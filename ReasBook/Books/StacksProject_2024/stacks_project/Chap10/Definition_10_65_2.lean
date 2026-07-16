import StacksProject_2024.stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w

section

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]
variable (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-
Domain triage:
- primary domain: associated primes under residue-field base change;
- `source-facing`: the set `relativeAssassin R S N` from the textbook definition;
- `core/canonical`: the chapter owner `associatedPrimesOfModule` together with mathlib's fiber
  ring `Ideal.Fiber`;
- `bridge/view`: the standard tensor comparison between the textbook module
  `N ⊗[R] κ(q ∩ R)` and the canonical fiber module `((q ∩ R).Fiber S) ⊗[S] N`.

The only primitive public data here is the source-facing set itself. The fiber presentation is a
derived companion view, so the bridge should stay private and as small as possible.
-/

/-- Definition 10.65.2: for a ring map `R → S` and an `S`-module `N`, the relative assassin
`Ass_{S/R}(N)` is the set of primes `𝔮 ∈ Spec(S)` such that `𝔮` is textbook-associated to
`N ⊗[R] κ(𝔮 ∩ R)`. -/
def relativeAssassin : Set (PrimeSpectrum S) :=
  { q | q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] (q.asIdeal.under R).ResidueField) }

/-- A point `q : Spec(S)` belongs to `relativeAssassin` exactly when its underlying ideal is
textbook-associated to `N ⊗[R] κ(q ∩ R)`. -/
@[simp] theorem mem_relativeAssassin_iff (q : PrimeSpectrum S) :
    q ∈ relativeAssassin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] (q.asIdeal.under R).ResidueField) :=
  Iff.rfl

end

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

private noncomputable def relativeAssassinFiberLinearEquiv (q : PrimeSpectrum S) :
    ((q.asIdeal.under R).Fiber S) ⊗[S] N ≃ₗ[S] N ⊗[R] (q.asIdeal.under R).ResidueField :=
  let p := q.asIdeal.under R
  TensorProduct.comm S (p.Fiber S) N ≪≫ₗ
    congr (LinearEquiv.refl S N)
      (Algebra.TensorProduct.commRight R S p.ResidueField).symm.toLinearEquiv
      ≪≫ₗ
    cancelBaseChange R S S N p.ResidueField

/-- The fiber-module model gives an equivalent membership criterion for `relativeAssassin`. -/
theorem mem_relativeAssassin_iff_fiber (q : PrimeSpectrum S) :
    q ∈ relativeAssassin R S N ↔
      q.asIdeal ∈ associatedPrimesOfModule S (((q.asIdeal.under R).Fiber S) ⊗[S] N) := by
  let p := q.asIdeal.under R
  rw [mem_relativeAssassin_iff]
  simpa using
    (show q.asIdeal ∈ associatedPrimesOfModule S (N ⊗[R] p.ResidueField) ↔
        q.asIdeal ∈ associatedPrimesOfModule S ((p.Fiber S) ⊗[S] N) from by
      rw [← LinearEquiv.associatedPrimesOfModule_eq S ((p.Fiber S) ⊗[S] N)
        (relativeAssassinFiberLinearEquiv q)])

end
