import StacksProject_2024.Chap15.Lemma_15_88_5_Bridge

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 15.88.5:
- primary domain: derived module objects on the chaotic ringed site attached to a sequential
  inverse system of commutative rings;
- sampled owner declarations:
  `sequentialRingSystem`,
  `SeqRingMod`,
  `DerivedModuleTower`,
  `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.Realization`;
- best owner abstraction: the chapter owner `DerivedCategory (SeqRingMod A ρ)` together with the
  bridge/view owner `DerivedModuleTower A ρ` from `Lemma_15_88_5_Bridge.lean`;
- primitive data: the inverse-system functor `sequentialRingSystem A ρ` and the compatible tower
  `DerivedModuleTower A ρ`;
- derived API: only the realization-existence statement below, phrased directly in terms of the
  bridge owner declarations already defined upstream.

Source/core/bridge triage:
- `source-facing`: the existence of an object of
  `D(Mod(ℕ, (A_n))) = D(SeqRingMod A ρ)`
  realizing prescribed stagewise derived data;
- `core/canonical`: `DerivedCategory (SeqRingMod A ρ)`;
- `bridge/view`: `DerivedModuleTower`, `sequentialRingedModuleTransitionFunctor`,
  `DerivedModuleTower.ofDerivedObject`, and
  `DerivedModuleTower.Realization`.

This file is source-facing only: the tower bridge/view API now lives in
`Lemma_15_88_5_Bridge.lean`, and the theorem below reuses that owner-level bridge directly. -/

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [CategoryWithHomology (SeqRingMod A ρ)]

namespace DerivedModuleTower

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

-- Proof sketch: represent the desired object of
-- `D(naturalNumbersRingedModules (sequentialRingSystem A ρ))` by a complex of module sheaves on
-- the chaotic site of `ℕ`, choose right-fraction representatives of the transition morphisms
-- `φ_n`, and inductively modify the representing complex so that its stagewise evaluations realize
-- the given `K_n` with the prescribed compatibility.
/-- Lemma 15.88.5: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, objects
`K_n ∈ D(A_n)` together with compatible transition maps
`φ_n : K_{n + 1} ⟶ K_n` viewed in `D(A_{n + 1})` by restriction of scalars, encoded here by a
compatible tower `T`, there exists an object of `D(Mod(ℕ, (A_n)))` whose stagewise evaluations
recover the stages of `T` compatibly with its tower maps, together with compatible stagewise
identifications. -/
theorem exists_realization
    (T : DerivedModuleTower A ρ) : ∃ (M : DModSeq), Nonempty (T.Realization M) := sorry

end DerivedModuleTower

end
