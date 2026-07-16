import Mathlib
import StacksProject_2024.stacks_project.Chap16.Definition_16_2_3

/- Domain-style sampling for `16_7_1_1`:
- primary domain: strict-standard elements of finitely presented algebras and the tail
  ideal-membership clause appearing in their presentation witnesses;
- sampled owner API:
  `Algebra.IsStrictlyStandard`,
  `Algebra.Presentation.IsStrictlyStandardElement`,
  `Algebra.Presentation.tailRelationCondition`,
  `Algebra.Presentation.tailRelationCondition_iff_sigma`;
- best owner abstraction: the source-facing statement should stay on the global owner
  `Algebra.IsStrictlyStandard`, while the presentation-level bridge
  `Algebra.Presentation.tailRelationCondition_iff_baseRing` converts the intrinsic tail-condition
  owner to the literal base-ring-lift equation used in the text;
- primitive data: a strict-standard witness
  `P.IsStrictlyStandardElement (algebraMap R A π)` coming from the global owner
  `IsStrictlyStandard R (algebraMap R A π)`;
- derived API: the literal presentation-ring equation in `16.7.1.1` is recovered by applying the
  bridge theorem `tailRelationCondition_iff_baseRing` to the tail-condition component of that
  witness.

Source/core/bridge triage:
- `source-facing`: the existence of a finite presentation witnessing
  `IsStrictlyStandard R (algebraMap R A π)` whose tail clause has the literal base-ring form from
  `16.7.1.1`;
- `core/canonical`: `Algebra.IsStrictlyStandard`,
  `Algebra.Presentation.IsStrictlyStandardElement`, together with
  `Algebra.Presentation.tailRelationCondition`;
- `bridge/view`: `tailRelationCondition_iff_baseRing` rewrites the intrinsic tail condition as the
  literal base-ring-lift equation in the chosen presentation ring.
-/

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
  have hπ : algebraMap P.Ring A (algebraMap R P.Ring π) = algebraMap R A π := by
    simpa using (DFunLike.congr_fun (IsScalarTower.algebraMap_eq R P.Ring A) π).symm
  constructor
  · rintro ⟨a₀, ha₀, htail⟩ j
    let r : P.Ring := P.relation (tailRelationIndex hcₘ j)
    have hk : algebraMap R P.Ring π - a₀ ∈ P.ker := by
      rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub]
      simpa [P.algebraMap_apply, ha₀] using sub_eq_zero.mpr (hπ.trans ha₀.symm)
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
    exact ⟨algebraMap R P.Ring π, hπ, h⟩

end

end Algebra.Presentation

namespace Algebra

section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {π : R}

/-- 16.7.1.1: if the image of `π` in `A` is strictly standard over `R`, then some finite
presentation witnessing that strict standardness has the second displayed clause written with the
literal base-ring lift of `π` in the presentation ring. -/
theorem IsStrictlyStandard.exists_presentation_baseRing_tail_clause
    (hπ : IsStrictlyStandard R (algebraMap R A π)) :
    ∃ (n m : ℕ) (P : Presentation R A (Fin n) (Fin m)) (c : ℕ) (hcₘ : c ≤ m),
      ∀ j : Fin (m - c),
        algebraMap R P.Ring π * P.relation (tailRelationIndex hcₘ j) ∈
          P.leadingRelationIdeal hcₘ + P.ker ^ 2 := by
  rcases hπ with ⟨n, m, P, hP⟩
  rcases hP with ⟨c, hcₘ, _, _, hTail⟩
  exact ⟨n, m, P, c, hcₘ, (P.tailRelationCondition_iff_baseRing π hcₘ).1 hTail⟩

end

end Algebra
