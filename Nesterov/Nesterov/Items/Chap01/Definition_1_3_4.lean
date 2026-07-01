import Mathlib.Tactic.Recall
import Nesterov.Chap01.Definition_1_3_4

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Coord" => Fin n → ℝ
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ
local notation "coordBox" => Set.Icc (0 : Coord) 1

/- Definition 1.3.4 lies in the finite-dimensional box-Lipschitz domain.

Relevant owner-style declarations sampled before refining:
* `LipschitzOnWith` in mathlib, the canonical owner of set-restricted Lipschitz continuity;
* `linftyLipschitzClass` in `Nesterov/Chap01/Definition_1_3_4.lean`, the chapter owner of the
  textbook class `𝒫∞[n, L]`;
* `mem_linftyLipschitzClass_iff_lipschitzOnWith` in the same file, the canonical bridge from the
  source-facing `ℓ∞` statement on `B_n` to `LipschitzOnWith`;
* `zeroOneBox` and `EuclideanSpace.linftyNorm` in `Nesterov/Chap01/Definition_1_3_1.lean` and
  `Nesterov/Chap01/Definition_1_3_2.lean`, the upstream chapter owners for the box and `ℓ∞` norm.

Best owner abstraction:
* source-facing owner: `linftyLipschitzClass n L`, with notation `𝒫∞[n, L]`;
* core/canonical owner: `LipschitzOnWith L (f ∘ coordEquiv.symm) coordBox`.

Primitive data:
* the Lipschitz constant `L`;
* the objective `f : EuclideanSpace ℝ (Fin n) → ℝ`.

Derived API:
* the pointwise textbook estimate on `zeroOneBox n`;
* the canonical bridge to `LipschitzOnWith`;
* the pointwise consequence `abs_sub_le_mul_linftyNorm`.

Source/core/bridge triage:
* source-facing: `𝒫∞[n, L]`;
* core/canonical: `LipschitzOnWith`;
* bridge/view: `mem_linftyLipschitzClass_iff_lipschitzOnWith`.

This item therefore reuses the exact chapter owner directly instead of keeping a parallel local
copy of the same box-Lipschitz definition and its companion API. -/

/- Definition 1.3.4: the textbook class `𝒫∞[n, L]` is the chapter owner
`linftyLipschitzClass n L`. -/
recall linftyLipschitzClass (n : ℕ) (L : NNReal) :
    Set (EuclideanSpace ℝ (Fin n) → ℝ)

/- Membership in `𝒫∞[n, L]` is exactly the textbook `ℓ∞`-Lipschitz estimate on `B_n`. -/
recall mem_linftyLipschitzClass_iff {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔
      ∀ x ∈ zeroOneBox n, ∀ y ∈ zeroOneBox n, |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞

/- Membership in `𝒫∞[n, L]` is equivalent to the canonical coordinate-cube owner
`LipschitzOnWith`. -/
recall mem_linftyLipschitzClass_iff_lipschitzOnWith {L : NNReal} {f : E → ℝ} :
    f ∈ 𝒫∞[n, L] ↔ LipschitzOnWith L (f ∘ (coordEquiv).symm) coordBox

/- Any objective in `𝒫∞[n, L]` satisfies the defining oscillation bound at box points. -/
recall abs_sub_le_mul_linftyNorm
    {L : NNReal} {f : E → ℝ} (hf : f ∈ 𝒫∞[n, L])
    {x y : E} (hx : x ∈ zeroOneBox n) (hy : y ∈ zeroOneBox n) :
    |f x - f y| ≤ (L : ℝ) * ‖x - y‖∞

end
