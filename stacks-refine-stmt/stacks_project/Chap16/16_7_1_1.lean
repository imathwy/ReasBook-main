import Mathlib
import stacks_project.Chap16.Definition_16_2_3

/- Domain-style sampling for `16_7_1_1`:
- primary domain: strict-standard elements of a finitely presented algebra and the tail
  ideal-membership clause extracted from a chosen witness;
- sampled owner API:
  `Algebra.IsStrictlyStandard`,
  `Algebra.Presentation.IsStrictlyStandardElement`,
  `Algebra.Presentation.tailRelationCondition`,
  `Algebra.Presentation.tailRelationCondition_iff_sigma`;
- best owner abstraction: the presentation-level owner
  `Algebra.Presentation.IsStrictlyStandardElement`, with the numbered equation recovered from the
  intrinsic owner `P.tailRelationCondition (algebraMap R A π) hcₘ` via the canonical base-ring
  lift of `π`;
- primitive data: a chosen strict-standard witness
  `P.IsStrictlyStandardElement (algebraMap R A π)`;
- derived API: the literal presentation-ring equation in `16.7.1.1` is the
  `IsStrictlyStandardElement.exists_baseRing_tail_clause` consequence of that witness, while the
  bridge theorem `tailRelationCondition_iff_baseRing` remains only a companion view refining the
  intrinsic tail-condition owner.

Source/core/bridge triage:
- `source-facing`: equation `16.7.1.1`, obtained after choosing a strict-standard witness for the
  image of `π`;
- `core/canonical`: `Algebra.Presentation.IsStrictlyStandardElement` together with
  `Algebra.Presentation.tailRelationCondition`;
- `bridge/view`: `tailRelationCondition_iff_baseRing` rewrites the intrinsic tail condition as the
  literal base-ring-lift equation in the chosen presentation ring.
-/

open MvPolynomial
open Algebra.Presentation

namespace Algebra.Presentation

section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m c : ℕ}

/-- For an element of `A` coming from `R`, the intrinsic tail relation condition is equivalent to
the literal presentation-ring equation obtained by multiplying each tail relation by the canonical
base-ring lift of that element. -/
theorem tailRelationCondition_iff_baseRing
    (P : Presentation R A (Fin n) (Fin m))
    (π : R) (hcₘ : c ≤ m) :
    P.tailRelationCondition (algebraMap R A π) hcₘ ↔
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π * P.relation (tailRelationIndex hcₘ j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  constructor
  · rintro ⟨a₀, ha₀, htail⟩ j
    let r : P.Ring := P.relation (tailRelationIndex hcₘ j)
    have hπ : algebraMap P.Ring A (algebraMap R P.Ring π) = algebraMap R A π := by
      exact (congrFun (congr_arg DFunLike.coe (IsScalarTower.algebraMap_eq R P.Ring A)) π).symm
    have hk : algebraMap R P.Ring π - a₀ ∈ P.ker := by
      rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub]
      rw [show aeval P.val (algebraMap R P.Ring π) = algebraMap R A π by
        rw [← P.algebraMap_apply]
        exact hπ]
      rw [show aeval P.val a₀ = algebraMap R A π by
        rw [← P.algebraMap_apply]
        exact ha₀]
      rw [sub_eq_zero]
    have hr : r ∈ P.ker := by
      dsimp [r]
      exact P.relation_mem_ker _
    have hsq : (algebraMap R P.Ring π - a₀) * r ∈ P.ker ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hk hr
    have hdecomp :
        algebraMap R P.Ring π * r = a₀ * r + (algebraMap R P.Ring π - a₀) * r := by
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ (htail j) (Ideal.mem_sup_right hsq)
  · intro h
    refine ⟨algebraMap R P.Ring π, ?_, h⟩
    exact (congrFun (congr_arg DFunLike.coe (IsScalarTower.algebraMap_eq R P.Ring A)) π).symm

end

end Algebra.Presentation

namespace Algebra.Presentation

section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m : ℕ}
variable {π : R}

/-- 16.7.1.1: after choosing a strict-standard witness for the image of `π` in the presentation
`P`, the second displayed clause can be written with the literal base-ring lift of `π` in the
chosen presentation ring. -/
theorem IsStrictlyStandardElement.exists_baseRing_tail_clause
    {P : Presentation R A (Fin n) (Fin m)}
    (hπ : P.IsStrictlyStandardElement (algebraMap R A π)) :
    ∃ (c : ℕ) (hcₘ : c ≤ m),
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π * P.relation (tailRelationIndex hcₘ j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  rcases hπ with ⟨c, hcₘ, _, _, hTail⟩
  refine ⟨c, hcₘ, ?_⟩
  exact (P.tailRelationCondition_iff_baseRing π hcₘ).1 hTail

end

end Algebra.Presentation
