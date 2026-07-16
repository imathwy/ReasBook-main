import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `Scheme.IdealSheafData.support` is the canonical closed-subscheme owner. The
-- source-side annihilation condition for sheaves is a uniform affine-open section criterion, so
-- this file owns that predicate and uses `moduleSupport` for the support side.

/-- A module sheaf is annihilated by a power of an ideal sheaf when one exponent annihilates all
affine-open section modules. -/
def IsAnnihilatedByIdealPowerOnAffineOpens (I : X.IdealSheafData) (ℱ : X.Modules) : Prop :=
  ∃ n : ℕ, ∀ U : X.affineOpens,
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) (Γ(ℱ, U.1))) = ⊥

/-- Unfold the affine-open ideal-power annihilation predicate for module sheaves. -/
theorem isAnnihilatedByIdealPowerOnAffineOpens_iff
    (I : X.IdealSheafData) (ℱ : X.Modules) :
    IsAnnihilatedByIdealPowerOnAffineOpens I ℱ ↔
      ∃ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) (Γ(ℱ, U.1))) = ⊥ := by
  rfl

/-- The affine-open ideal-power annihilation condition is equivalently a uniform annihilator-ideal
bound on all affine-open section modules. -/
theorem isAnnihilatedByIdealPowerOnAffineOpens_iff_pow_le_annihilator
    (I : X.IdealSheafData) (ℱ : X.Modules) :
    IsAnnihilatedByIdealPowerOnAffineOpens I ℱ ↔
      ∃ n : ℕ, ∀ U : X.affineOpens,
        I.ideal U ^ n ≤ Module.annihilator (Γ(X, U.1)) (Γ(ℱ, U.1)) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, fun U ↦ ?_⟩
    rw [← Submodule.annihilator_top]
    exact (Submodule.le_annihilator_iff).2 (hn U)
  · rintro ⟨n, hn⟩
    refine ⟨n, fun U ↦ ?_⟩
    rw [← Submodule.annihilator_top] at hn
    exact (Submodule.le_annihilator_iff).1 (hn U)

section

variable [IsNoetherian X]

/-- Lemma 30.10.2: let `X` be a Noetherian scheme, let `ℱ` be a coherent `\mathcal O_X`-module,
and let `I : X.IdealSheafData` be the quasi-coherent ideal sheaf defining a closed subscheme
`Z ⊆ X`. Then some power of `I` annihilates `ℱ` if and only if the support of `ℱ` is contained
set-theoretically in `Z`; the left side is the source-facing affine-open form of the sheaf
identity `\mathcal I^n \mathcal F = 0`. -/
theorem exists_pow_affineOpenIdeal_smul_eq_bot_iff_support_subset
    (ℱ : X.Modules) [ℱ.IsCoherent] (I : X.IdealSheafData) :
    IsAnnihilatedByIdealPowerOnAffineOpens I ℱ ↔
    moduleSupport ℱ ⊆ (I.support : Set X) := sorry

/-- Lemma 30.10.2, annihilator-owner form: the support of a coherent module sheaf is contained in
the closed subscheme defined by `I` if and only if one power of `I(U)` is contained in the
annihilator of `Γ(U, ℱ)` for every affine open `U`. -/
theorem exists_pow_affineOpenIdeal_le_annihilator_iff_support_subset
    (ℱ : X.Modules) [ℱ.IsCoherent] (I : X.IdealSheafData) :
    (∃ n : ℕ, ∀ U : X.affineOpens,
      I.ideal U ^ n ≤ Module.annihilator (Γ(X, U.1)) (Γ(ℱ, U.1))) ↔
    moduleSupport ℱ ⊆ (I.support : Set X) := by
  rw [← isAnnihilatedByIdealPowerOnAffineOpens_iff_pow_le_annihilator]
  exact exists_pow_affineOpenIdeal_smul_eq_bot_iff_support_subset ℱ I

end

end AlgebraicGeometry.Scheme.Modules
