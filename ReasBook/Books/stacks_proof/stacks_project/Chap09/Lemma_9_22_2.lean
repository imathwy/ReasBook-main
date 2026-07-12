import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable (M : IntermediateField K L)
variable [Normal K L] [Normal K M]

/-
Domain-style sampling:
* primary domain: restriction morphisms between Galois groups and the Krull topology;
* sampled owner declarations:
  `AlgEquiv.restrictNormalHom`,
  `AlgEquiv.restrictNormalHom_surjective`,
  `InfiniteGalois.restrictNormalHom_continuous`,
  `galoisTowerRestrictionShortExact`;
* best owner abstraction: the canonical restriction homomorphism
  `AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)`;
* primitive data: a field tower `K ⟶ M ⟶ L` and normality of `L/K` and `M/K`;
* derived API: surjectivity and continuity are the canonical theorem-level consequences above.

Layer triage:
* `source-facing`: Lemma 9.22.2 states that the canonical restriction map is surjective and
  continuous;
* `core/canonical`: `AlgEquiv.restrictNormalHom`;
* `bridge/view`: the source-facing statement is the conjunction of the two canonical owner-level
  facts `AlgEquiv.restrictNormalHom_surjective` and
  `InfiniteGalois.restrictNormalHom_continuous`.

The source text assumes both extensions are Galois, but separability is redundant for these two
canonical properties, so the public context is lowered to the primitive normality hypotheses.
-/
-- Proof sketch: use the canonical restriction homomorphism `AlgEquiv.restrictNormalHom M`;
-- surjectivity is exactly `AlgEquiv.restrictNormalHom_surjective M`, and continuity is exactly
-- `InfiniteGalois.restrictNormalHom_continuous M`.
/-- Lemma 9.22.2: for a tower `L/M/K` with `L/K` and `M/K` normal, the canonical restriction map
`Gal(L / K) → Gal(M / K)` is surjective and continuous for the Krull topologies. -/
@[stacks 0BMK]
theorem restrictNormalHom_surjective_and_continuous :
    Function.Surjective (AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)) ∧
      Continuous (AlgEquiv.restrictNormalHom M : Gal(L / K) →* Gal(M / K)) := by
  constructor
  · -- The algebraic half is exactly the standard surjectivity theorem for restriction.
    exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L)
  · -- The topological half is exactly the standard continuity theorem for restriction.
    exact InfiniteGalois.restrictNormalHom_continuous (k := K) (K := L) M

end
