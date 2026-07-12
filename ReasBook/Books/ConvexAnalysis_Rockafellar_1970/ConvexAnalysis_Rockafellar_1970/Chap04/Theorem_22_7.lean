import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_22_6

-- Declarations for this item will be appended below by the statement pipeline.

open Function
open scoped Rockafellar

noncomputable section

section

variable {ι : Type*}
variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜]
variable [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Tucker's complementarity theorem for a finite-coordinate subspace
  `L ⊆ 𝕜^ι`.
- `core/canonical`: the owner abstractions are `Submodule 𝕜 (ι → 𝕜)` for the subspace, a
  pairing-level annihilator `Lᗮₚ` via `HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜`, and
  `Function.support` for coordinate support.
- `bridge/view`: coordinatewise strict-positivity/vanishing exclusivity is kept as a derived bridge
  from the source-facing support-complement owner.

Domain-style sampling used here:
- `HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜` as the primitive pairing owner for `Lᗮₚ`;
- `Submodule 𝕜 (ι → 𝕜)` and `Submodule.pairingOrthogonal` (`ᗮₚ`) from the chapter owner layer;
- `Function.support` from the canonical support API recalled in `Text 22.3.11`;
- `Submodule.IsPositiveIntervalSeparatorOn` and
  `subspace_interval_annihilator_alternative` from `Theorem_22_6`.

Primitive data vs derived API:
- primitive inputs: a subspace `L : Submodule 𝕜 (ι → 𝕜)` and vectors `z zstar : ι → 𝕜`;
- source-facing owner: `Submodule.IsTuckerPair` with primitive membership, nonnegativity, and
  support-complement data;
- derived API: coordinatewise strict-positivity/vanishing bridge lemmas and the theorem interface
  where left-support uniqueness is primitive while right-support uniqueness is a derived bridge.

Layer target: `source-facing`, stated directly with the canonical subspace, pairing-annihilator,
and support owners rather than through an auxiliary package.

Abstraction checks for this item:
- Codomain/ambient layer: owner-side declarations are at the intrinsic pairing layer
  (`Submodule 𝕜 (ι → 𝕜)` and `Lᗮₚ`) parameterized by `HasLinearPairing`, not tied to an
  inner-product-model owner.
- Scalar structure: helper owners and support lemmas stay at primitive
  `[CommSemiring 𝕜] [Preorder 𝕜]`; only the existence theorem specializes to the finite-coordinate
  dot-product pairing and uses the stronger ordered-field assumptions inherited from `Theorem_22_6`.
- Topology: no ambient-closure/interior owner appears here, so there is no intrinsic-vs-ambient
  topology upgrade to perform in this item.
-/

namespace Submodule

/-- A pair `(z, zstar)` realizes Tucker complementarity for `L` when `z ∈ L`, `zstar ∈ Lᗮₚ`, both
vectors are pointwise nonnegative, and their supports are complementary. -/
def IsTuckerPair
    (L : Submodule 𝕜 (ι → 𝕜)) (z zstar : ι → 𝕜) : Prop :=
  z ∈ L ∧ zstar ∈ Lᗮₚ ∧ 0 ≤ z ∧ 0 ≤ zstar ∧
    IsCompl (support z) (support zstar)

end Submodule

scoped[Rockafellar] notation:50 z " ⟂ₜ[" L "] " zstar:50 =>
  Submodule.IsTuckerPair (L := L) z zstar

end

section

variable {ι : Type*}
variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜]
variable [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]

namespace Submodule

namespace IsTuckerPair

variable {L : Submodule 𝕜 (ι → 𝕜)} {z zstar w wstar : ι → 𝕜} {i : ι}

/-- A Tucker pair has left vector in the subspace owner. -/
theorem mem_left (h : z ⟂ₜ[L] zstar) : z ∈ L :=
  h.1

/-- A Tucker pair has right vector in the pairing orthogonal owner. -/
theorem mem_right (h : z ⟂ₜ[L] zstar) : zstar ∈ Lᗮₚ :=
  h.2.1

/-- A Tucker pair has pointwise nonnegative left vector. -/
theorem left_nonneg (h : z ⟂ₜ[L] zstar) : 0 ≤ z :=
  h.2.2.1

/-- A Tucker pair has pointwise nonnegative right vector. -/
theorem right_nonneg (h : z ⟂ₜ[L] zstar) : 0 ≤ zstar :=
  h.2.2.2.1

/-- In a Tucker pair, the two supports are complementary in the canonical lattice owner. -/
theorem support_isCompl (h : z ⟂ₜ[L] zstar) :
    IsCompl (support z) (support zstar) :=
  h.2.2.2.2

/-- The support of `z` is the complement of the support of `zstar` in a Tucker pair. -/
theorem support_left_eq_compl_right (h : z ⟂ₜ[L] zstar) :
    support z = (support zstar)ᶜ := by
  simpa using h.support_isCompl.eq_compl

/-- The support of `zstar` is the complement of the support of `z` in a Tucker pair. -/
theorem support_right_eq_compl_left (h : z ⟂ₜ[L] zstar) :
    support zstar = (support z)ᶜ := by
  simpa using h.support_isCompl.compl_eq.symm

/-- Bridge constructor: the coordinatewise textbook condition implies the canonical owner data of
a Tucker pair. -/
theorem of_coordwise
    (hzL : z ∈ L)
    (hzstarL : zstar ∈ Lᗮₚ)
    (hcoord : ∀ i, (0 < z i ∧ zstar i = 0) ∨ (z i = 0 ∧ 0 < zstar i)) :
    z ⟂ₜ[L] zstar := by
  refine ⟨hzL, hzstarL, ?_, ?_, ?_⟩
  · intro j
    rcases hcoord j with hzj | hzstarj
    · exact le_of_lt hzj.1
    · simp [hzstarj.1]
  · intro j
    rcases hcoord j with hzj | hzstarj
    · simp [hzj.2]
    · exact le_of_lt hzstarj.2
  · have hsupport : support z = (support zstar)ᶜ := by
      ext j
      rcases hcoord j with hzj | hzstarj
      · constructor
        · intro _
          simp [mem_support, hzj.2]
        · intro _
          exact mem_support.mpr hzj.1.ne'
      · constructor
        · intro hj
          exact False.elim <| (mem_support.mp hj) hzstarj.1
        · intro hj
          exact False.elim <| hj (mem_support.mpr hzstarj.2.ne')
    simpa [hsupport] using (isCompl_compl : IsCompl (support zstar) (support zstar)ᶜ).symm

/-- Equality of left supports between two Tucker complementarity pairs forces equality of right
supports as well. -/
theorem support_right_eq_of_support_left_eq
    (hz : z ⟂ₜ[L] zstar)
    (hw : w ⟂ₜ[L] wstar)
    (hleft : support w = support z) :
    support wstar = support zstar := by
  rw [hw.support_right_eq_compl_left, hz.support_right_eq_compl_left, hleft]

end IsTuckerPair

end Submodule

end

section

variable {ι : Type*}
variable {𝕜 : Type*} [CommSemiring 𝕜] [LinearOrder 𝕜]
variable [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]

namespace Submodule

namespace IsTuckerPair

variable {L : Submodule 𝕜 (ι → 𝕜)} {z zstar : ι → 𝕜} {i : ι}

/-- In a Tucker complementarity pair over a linear order, each coordinate has exactly one strict
positive entry and one zero entry. -/
theorem coordwise (h : z ⟂ₜ[L] zstar) :
    ∀ i, (0 < z i ∧ zstar i = 0) ∨ (z i = 0 ∧ 0 < zstar i) := by
  intro j
  by_cases hj : j ∈ support z
  · left
    refine ⟨lt_of_le_of_ne (h.left_nonneg j) (mem_support.mp hj).symm, ?_⟩
    have hj' : j ∉ support zstar := by
      simpa [h.support_left_eq_compl_right] using hj
    by_contra hzstarj
    exact hj' (mem_support.mpr hzstarj)
  · right
    refine ⟨?_, ?_⟩
    · by_contra hzj
      exact hj (mem_support.mpr hzj)
    · have hjstar : j ∈ support zstar := by
        simpa [h.support_right_eq_compl_left] using hj
      exact lt_of_le_of_ne (h.right_nonneg j) (mem_support.mp hjstar).symm

/-- In a Tucker complementarity pair over a linear order, a coordinate belongs to the support of
`z` exactly when it is strictly positive. -/
theorem mem_support_left_iff (h : z ⟂ₜ[L] zstar) :
    i ∈ support z ↔ 0 < z i := by
  constructor
  · intro hi
    rcases h.coordwise i with hzi | hzstari
    · exact hzi.1
    · exact False.elim <| (mem_support.mp hi) hzstari.1
  · intro hzi
    exact mem_support.mpr hzi.ne'

/-- In a Tucker complementarity pair over a linear order, a coordinate belongs to the support of
`zstar` exactly when it is strictly positive. -/
theorem mem_support_right_iff (h : z ⟂ₜ[L] zstar) :
    i ∈ support zstar ↔ 0 < zstar i := by
  constructor
  · intro hi
    rcases h.coordwise i with hzi | hzstari
    · exact False.elim <| (mem_support.mp hi) hzi.2
    · exact hzstari.2
  · intro hzstari
    exact mem_support.mpr hzstari.ne'

end IsTuckerPair

end Submodule

end

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Submodule

/-!
Upstream-first scalar note:
- The theorem-level scalar bundle here is intentionally aligned with
  `subspace_interval_annihilator_alternative` from `Theorem_22_6`, which is the first upstream
  source for the Chapter 22 interval alternative used in the existence argument.
- The pairing argument is specialized here by the finite-coordinate dot-product instance coming
  from `[Fintype ι]`.
-/

-- Proof sketch: for each coordinate, apply Theorem 22.6 with intervals
-- `Iᵢ = [0, ∞)` for `i ≠ k` and `Iₖ = (0, ∞)` to obtain the exclusive alternative that exactly one
-- of `L` or `Lᗮₚ` contains a nonnegative vector positive at that coordinate. Summing the witnesses
-- over the two complementary index sets yields a pair `(z, zstar)` with complementary supports,
-- and the same coordinatewise alternative shows that any other such pair has the same supports.
/-- Theorem 22.7: for a subspace `L ⊆ 𝕜^ι`, there exist nonnegative vectors `z ∈ L` and
`zstar ∈ Lᗮₚ` whose supports are complementary; the support of `z` is uniquely determined among all
such pairs. -/
theorem exists_tucker_complementarity_pair_with_unique_left_support
    (L : Submodule 𝕜 (ι → 𝕜)) :
    ∃ z zstar, z ⟂ₜ[L] zstar ∧
      ∀ w wstar, w ⟂ₜ[L] wstar →
        support w = support z := sorry

/-- Bridge form of Theorem 22.7: uniqueness of the right support is derived from uniqueness of the
left support together with support complementarity. -/
theorem exists_tucker_complementarity_pair_with_unique_supports
    (L : Submodule 𝕜 (ι → 𝕜)) :
    ∃ z zstar, z ⟂ₜ[L] zstar ∧
      ∀ w wstar, w ⟂ₜ[L] wstar →
        support w = support z ∧ support wstar = support zstar := by
  rcases exists_tucker_complementarity_pair_with_unique_left_support L with
      ⟨z, zstar, hz, hleft_unique⟩
  refine ⟨z, zstar, hz, ?_⟩
  intro w wstar hw
  refine ⟨hleft_unique w wstar hw, ?_⟩
  exact hz.support_right_eq_of_support_left_eq hw (hleft_unique w wstar hw)

end Submodule

end
