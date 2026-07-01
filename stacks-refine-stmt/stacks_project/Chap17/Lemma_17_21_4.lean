import stacks_project.Chap10.Lemma_10_13_2
import stacks_project.Chap17.Lemma_17_21_1

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.21.4:
- primary domain: symmetric and exterior power exact sequences of `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `symmetricPowerMap`,
  `exteriorPowerMap`,
  `symmetricPowerLeftTensorMap`,
  `exteriorPowerLeftTensorMap`,
  `ShortComplex.ShortExact`,
  `symmetric_power_exact_of_exact`,
  `exterior_power_exact_of_exact`;
- best owner abstraction:
  the source-facing owner is a short complex in `RingedSpace.Modules X` built from the canonical
  sheaf owners `Symm[n]` and `Λ^[n]` together with their canonical sheaf-level comparison maps
  from `Lemma_17_21_1`; the module-theoretic exactness theorems from Chapter 10 are only the
  proof bridge;
- primitive-vs-derived split:
  primitive data are a short complex `S : ShortComplex ModX` and a degree `n : ℕ`;
  derived API consists of the sheaf-level power-operation maps already owned by
  `Lemma_17_21_1`, and the resulting short exact sequences.

Source/core/bridge triage:
- `source-facing`: the two exact sequences of sheaves
  `S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃ ⟶ 0`
  and
  `S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃ ⟶ 0`;
- `core/canonical`: `Symm[n]`, `Λ^[n]`, `symmetricPowerMap`, `exteriorPowerMap`,
  `symmetricPowerLeftTensorMap`, `exteriorPowerLeftTensorMap`, and
  `ShortComplex.ShortExact`;
- `bridge/view`: the reduction to the module-valued exactness owners
  `symmetric_power_exact_of_exact` and `exterior_power_exact_of_exact`. -/

-- Proof sketch: the sectionwise composite is the canonical module-theoretic composite
-- `M₂ ⊗ Sym^n(M₁) → Sym^(n + 1)(M₁) → Sym^(n + 1)(M)` associated to `S.f(U)` and `S.g(U)`, which
-- vanishes by exactness in Chapter 10 after sheafifying.
/-- The canonical short complex
`S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃`
attached to a short complex `S` of `\mathcal O_X`-modules. -/
noncomputable def symmetricPowerSequence
    (S : ShortComplex ModX) (n : ℕ) :
    ShortComplex ModX :=
  ShortComplex.mk
    (symmetricPowerLeftTensorMap n S.f)
    (symmetricPowerMap (n + 1) S.g)
    (by sorry)

-- Proof sketch: the sectionwise composite is the canonical module-theoretic composite
-- `M₂ ⊗ ⋀^n(M₁) → ⋀^(n + 1)(M₁) → ⋀^(n + 1)(M)` associated to `S.f(U)` and `S.g(U)`, which
-- vanishes by exactness in Chapter 10 after sheafifying.
/-- The canonical short complex
`S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃`
attached to a short complex `S` of `\mathcal O_X`-modules. -/
noncomputable def exteriorPowerSequence
    (S : ShortComplex ModX) (n : ℕ) :
    ShortComplex ModX :=
  ShortComplex.mk
    (exteriorPowerLeftTensorMap n S.f)
    (exteriorPowerMap (n + 1) S.g)
    (by sorry)

section

variable {S : ShortComplex ModX}

-- Proof sketch: after passing to the stalk at each point, the sequence identifies with the
-- module-theoretic symmetric-power exact sequence from Lemma `10.13.2`; exactness of sheaves of
-- modules is detected stalkwise.
/-- Lemma 17.21.4 (1), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Symm[n] S.X₂ ⟶ Symm[n + 1] S.X₂ ⟶ Symm[n + 1] S.X₃ ⟶ 0`
is short exact in `RingedSpace.Modules X`. -/
theorem symmetricPowerSequence_shortExact
    (hS : S.ShortExact) (n : ℕ) :
    (symmetricPowerSequence S n).ShortExact := by
  sorry

-- Proof sketch: the same stalkwise reduction identifies the exterior-power sequence with the
-- module-theoretic exact sequence from Lemma `10.13.2`.
/-- Lemma 17.21.4 (2), stated in degree `n + 1`: for a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of `\mathcal O_X`-modules, the canonical sequence
`S.X₁ ⊗ Λ^[n] S.X₂ ⟶ Λ^[n + 1] S.X₂ ⟶ Λ^[n + 1] S.X₃ ⟶ 0`
is short exact in `RingedSpace.Modules X`. -/
theorem exteriorPowerSequence_shortExact
    (hS : S.ShortExact) (n : ℕ) :
    (exteriorPowerSequence S n).ShortExact := by
  sorry

end

end AlgebraicGeometry.RingedSpace
