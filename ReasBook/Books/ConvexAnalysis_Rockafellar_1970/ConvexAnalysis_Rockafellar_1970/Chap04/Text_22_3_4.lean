import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_3

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X] [FiniteDimensional R X]
  [AddCommMonoid Y] [Module R Y]
  [TopologicalSpace (Y × R)] [Bornology (Y × R)]
  [HasPairing X Y R] [HasPairingAddRight X Y R] [HasPairingSMulRight X Y R]
variable {I : Type u}

local notation "solutionSet[" a "]" =>
  ((LinearConstraintRelation.leFeasible (X := X) a (fun _ : I ↦ (0 : R))) : Set X)
local notation "coefficientSet[" a "]" =>
  (Set.range (fun i : I ↦ (a i, (0 : R))) : Set (Y × R))

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.3.4 is the homogeneous indexed-family specialization of the infinite
  linear-inequality consequence criterion from Text 22.3.3.
- `core/canonical`: the indexed homogeneous weak system owner is
  `LinearConstraintRelation.leFeasible a (fun _ ↦ (0 : R))`, and the closed/bounded hypothesis is
  stated on the canonical coefficient owner `coefficientSet[a]` used by the indexed bridge
  theorem from Text 22.3.3.
- `bridge/view`: the theorem remains on the homogeneous-feasible-set owner and target half-space
  owner `closedHalfSpaceLE a0 0`; only the vacuous scalar inequality is discarded from the
  certificate conclusion.

Domain-style sampling used here:
- `LinearConstraintRelation.leFeasible`;
- `LinearConstraintRelation.mem_leFeasible`;
- `closedHalfSpaceLE`;
- `indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate`;
- `Finsupp.sum` and `weights.support.card`.

Primitive data vs derived API:
- primitive inputs: the indexed coefficient family `a : I → Y` and the target vector `a0 : Y`;
- primitive coefficient owner: `coefficientSet[a]`;
- primitive owner object: `solutionSet[a]`;
- derived API: the equivalence between homogeneous consequence and a finitely supported conic
  combination of support cardinality at most `Module.finrank R X`. The general scalar inequality
  is derived and vacuous in this homogeneous case, so it does not remain in the public theorem
  surface.

Layer target: `source-facing`. This file records the homogeneous theorem itself, not a new wrapper
around the certificate data already used in the preceding indexed theorem.
-/

-- Proof sketch: apply
-- `indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate` to the
-- homogeneous scalar family `fun _ ↦ (0 : R)`. The scalar inequality in the resulting finitely
-- supported certificate simplifies to `0 ≤ 0`, leaving the usual nonnegative
-- conic-combination conclusion with the same support bound.
/-- Text 22.3.4, stated on the canonical ambient owner: for a closed bounded family of vectors in
a pairing `⟪·, ·⟫ₚ : X × Y → R` over an ordered division ring `R`, with
finite-dimensional primal space
`X`, whose canonical
homogeneous feasible set is
full-dimensional (`affineSpan R _ = ⊤`), the homogeneous inequality `⟪a₀, x⟫ ≤ 0` is a
consequence of the system `⟪aᵢ, x⟫ ≤ 0` if and only if `a₀` is a nonnegative linear combination
of at most `Module.finrank R X` vectors from the family. -/
theorem indexed_homogeneous_consequence_iff_exists_dualCaratheodory_conicCombination
    (a : I → Y) (a0 : Y)
    (hclosed : IsClosed (coefficientSet[a]))
    (hbounded : Bornology.IsBounded (coefficientSet[a]))
    (hfull : affineSpan R (solutionSet[a]) = ⊤) :
    solutionSet[a] ⊆ closedHalfSpaceLE a0 (0 : R) ↔
      ∃ weights : I →₀ R,
        weights.support.card ≤ Module.finrank R X ∧
          (∀ i : I, 0 ≤ weights i) ∧
            weights.sum (fun i w ↦ w • a i) = a0 := by
  have hindexed :
      solutionSet[a] ⊆ closedHalfSpaceLE a0 (0 : R) ↔
        ∃ weights : I →₀ R,
          weights.support.card ≤ Module.finrank R X ∧
            (∀ i : I, 0 ≤ weights i) ∧
              weights.sum (fun i w ↦ w • a i) = a0 ∧
              weights.sum (fun i w ↦ w * (0 : R)) ≤ (0 : R) :=
    indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
      a (fun _ ↦ (0 : R)) a0 (0 : R) hclosed hbounded hfull
  constructor
  · intro hsubset
    rcases hindexed.mp hsubset with ⟨weights, hcard, hnonneg, hsum, _hscalar⟩
    exact ⟨weights, hcard, hnonneg, hsum⟩
  · rintro ⟨weights, hcard, hnonneg, hsum⟩
    refine hindexed.mpr ⟨weights, hcard, hnonneg, hsum, ?_⟩
    simp

end
