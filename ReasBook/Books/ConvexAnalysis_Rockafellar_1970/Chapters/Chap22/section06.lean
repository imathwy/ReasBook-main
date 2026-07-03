import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_22_6 (from Chap04) -/
open scoped BigOperators Pointwise Rockafellar

noncomputable section

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [CommSemiring 𝕜] [Preorder 𝕜]

local notation "𝕜>0" => Set.Ioi (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 22.6 is Rockafellar's interval alternative for a finite-coordinate
  subspace `L ⊆ 𝕜^ι`.
- `core/canonical`: the owner abstractions are `Submodule 𝕜 (ι → 𝕜)`, a pairing-level
  annihilator `Lᗮₚ` via `HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜`, the witness-level separator owner
  `L.IsPositiveIntervalSeparatorOn I zstar` together with its owner-side set
  `L.positiveIntervalSeparatorsOn I`, `Set.OrdConnected` for intervalhood, and the
  chapter owner set `Submodule.elementary`.
- `bridge/view`: the textbook finite-coordinate dot-product reading remains a specialization of this
  pairing-level owner, not a second public owner for the present theorem.

Domain-style sampling used here:
- `HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜` as the primitive pairing owner for `Lᗮₚ`;
- `Submodule 𝕜 (ι → 𝕜)` together with `Submodule.pairingOrthogonal` (`ᗮₚ`);
- `Submodule.IsPositiveIntervalSeparatorOn` as the primitive owner-level separator predicate and
  `Submodule.positiveIntervalSeparatorsOn` as its owner-set surface;
- `Set.OrdConnected` as the chapter owner abstraction for intervals;
- `Submodule.elementary` from `Text_22_3_12`;
- `Submodule.eq_span_elementary` from Lemma 22.5 as the canonical generation result cited
  by the proof sketch of clause (2).

Primitive data vs derived API:
- primitive inputs: a subspace `L : Submodule 𝕜 (ι → 𝕜)` and an interval family `I : ι → Set 𝕜`;
- derived API: the owner-side separator set `L.positiveIntervalSeparatorsOn I` and the two
  textbook alternatives built from it;
- theorem-level side conditions: intervalhood via `Set.OrdConnected`, and interval nonemptiness,
  since `Set.OrdConnected` alone also allows `∅`.

Layer target: `source-facing`, stated directly on the canonical `Submodule` owner.

Abstraction checks for this item:
- Pairing owner layer: the separator owner is stated directly on the canonical pairing-level
  annihilator owner `Lᗮₚ`, rather than tied to a specific coordinate realization.
- Codomain/ambient layer: the separator owner below only needs scalar multiplication of sets and
  strict-order positivity in the codomain, so it is defined at the primitive
  `[CommSemiring 𝕜] [Preorder 𝕜]` layer instead of the theorem-level ordered-field layer.
- Scalar structure: clause (1) and clause (2) are both kept at the chapter ordered-field layer.
  Although the separator owner itself is primitive at `[CommSemiring 𝕜] [Preorder 𝕜]`, the current
  upstream theorem route for witness extraction has not yet supplied a validated weaker scalar-order
  dependency for the elementary-selection statement.
- Topology (intrinsic vs ambient): no ambient topology owner (`closure`, `interior`, relative
  openness/closedness) appears in this statement family; intervalhood is expressed by the
  order-intrinsic owner `Set.OrdConnected`, so no intrinsic-topology reformulation is applicable.
-/

namespace Submodule

/-- A vector `zstar` is a positive interval separator for `L` and `I` when it belongs
to `Lᗮₚ` and its interval combination is strictly positive. -/
def IsPositiveIntervalSeparatorOn
    [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]
    (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜) (zstar : ι → 𝕜) : Prop :=
  zstar ∈ Lᗮₚ ∧
    (∑ i, zstar i • I i : Set 𝕜) ⊆ 𝕜>0

/-- Owner-side separator set for Theorem 22.6: vectors in `Lᗮₚ` whose interval combination is
strictly positive. -/
def positiveIntervalSeparatorsOn
    [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]
    (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜) : Set (ι → 𝕜) :=
  L.IsPositiveIntervalSeparatorOn I

@[simp] theorem mem_positiveIntervalSeparatorsOn
    [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]
    (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜) (zstar : ι → 𝕜) :
    zstar ∈ L.positiveIntervalSeparatorsOn I ↔
      L.IsPositiveIntervalSeparatorOn I zstar :=
  Iff.rfl

/-- The owner-side separator set is nonempty exactly when there exists a separator witness. -/
theorem nonempty_positiveIntervalSeparatorsOn_iff
    [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]
    (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜) :
    (L.positiveIntervalSeparatorsOn I).Nonempty ↔
      ∃ zstar : ι → 𝕜, L.IsPositiveIntervalSeparatorOn I zstar :=
  Iff.rfl

namespace IsPositiveIntervalSeparatorOn

variable [HasLinearPairing (ι → 𝕜) (ι → 𝕜) 𝕜]
variable {L : Submodule 𝕜 (ι → 𝕜)} {I : ι → Set 𝕜}
variable {zstar : ι → 𝕜}

/-- A positive interval separator belongs to the pairing annihilator. -/
theorem mem_pairingOrthogonal
    (h : L.IsPositiveIntervalSeparatorOn I zstar) :
    zstar ∈ Lᗮₚ :=
  h.1

/-- A positive interval separator has strictly positive interval sum. -/
theorem interval_sum_subset_Ioi
    (h : L.IsPositiveIntervalSeparatorOn I zstar) :
    (∑ i, zstar i • I i : Set 𝕜) ⊆ 𝕜>0 :=
  h.2

end IsPositiveIntervalSeparatorOn

end Submodule

section IntervalAlternative

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜)

/-!
Scalar-layer justification for Theorem 22.6 (1):
- This clause is the chapter interval alternative and keeps the upstream ordered-field layer used
  for strict interval positivity and interval geometry.
- Topology check: not applicable (no ambient closure/interior owners).
-/

/-- Theorem 22.6 (1): for a subspace `L` of `𝕜^ι` and intervals `I i`, either `L` contains a
vector whose `i`th coordinate lies in `I i`, or there is a positive interval
separator, but not both. -/
-- Proof sketch: prove incompatibility by pairing a feasible vector with an annihilator separator,
-- then use the Chapter 22 interval argument to obtain one of the two alternatives.
theorem subspace_interval_annihilator_alternative
    (hI : ∀ i, Set.OrdConnected (I i))
    (hI_nonempty : ∀ i, (I i).Nonempty) :
    Xor'
      (∃ z ∈ L, ∀ i, z i ∈ I i)
      (L.positiveIntervalSeparatorsOn I).Nonempty := sorry

end IntervalAlternative

section ElementaryIntervalSeparator

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable (L : Submodule 𝕜 (ι → 𝕜)) (I : ι → Set 𝕜)

/-!
Scalar-layer justification for the elementary-witness theorem:
- The statement only reduces an existing separator witness to one that is elementary in `Lᗮₚ`,
  but this file currently has no upstream-certified extraction argument at a weaker scalar-order
  layer than the chapter interval alternative.
- Therefore the public theorem intentionally keeps the same ordered-field assumptions as clause (1),
  while the separator owner itself remains defined at the weaker primitive layer above.
-/

/-- Theorem 22.6 (2): whenever the positive annihilator-separator alternative holds, the
separating vector may be chosen elementary in `Lᗮₚ`. -/
-- Proof sketch: decompose a separating vector in `Lᗮₚ` into elementary vectors using the support
-- generation result `Submodule.eq_span_elementary`, and retain one elementary summand that
-- still gives a strictly positive interval combination.
theorem positive_annihilator_interval_separator_can_be_chosen_elementary
    (hsep : (L.positiveIntervalSeparatorsOn I).Nonempty) :
    ((Lᗮₚ).elementary ∩ L.positiveIntervalSeparatorsOn I).Nonempty := sorry

end ElementaryIntervalSeparator

end
