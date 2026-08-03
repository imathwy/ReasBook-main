import Integer.Chapters.Chap09.section_9_3.ch9_sec9_3_proposition_9_13

open Set

section Proposition915

universe u

variable {α : Type u}

-- Semantic recall: mathlib's canonical orbit owner is `MulAction.orbit`, but Proposition 9.15
-- is phrased over the source orbit family `𝒪_a`, so this file keeps that family explicit instead
-- of identifying it with a stronger stabilizer-based orbit partition.

/-- `hasOrbitMeetingFixedZero orbitFamily node x` means that some orbit `O ∈ 𝒪_a` attached to
`node` meets the variables fixed to `0` at `node` and also contains a coordinate where the binary
solution `x` takes the value `1`. -/
def hasOrbitMeetingFixedZero
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (x : α → Bool) : Prop :=
  ∃ O ∈ orbitFamily, (O ∩ node.fixedZero).Nonempty ∧ ∃ i ∈ O, x i = true

/-- Unfolding `hasOrbitMeetingFixedZero` yields an orbit `O ∈ 𝒪_a` whose intersection with the
variables fixed to `0` at `node` is nonempty and which also contains a `1`-coordinate of `x`. -/
theorem hasOrbitMeetingFixedZero_iff
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (x : α → Bool) :
    hasOrbitMeetingFixedZero orbitFamily node x ↔
      ∃ O ∈ orbitFamily, (O ∩ node.fixedZero).Nonempty ∧ ∃ i ∈ O, x i = true :=
  Iff.rfl

/-- Canonical Chapter 9.13 solution-set reformulation of Proposition 9.15 for the actual
enumeration-tree left-of relation and source orbit family `𝒪_a`, with the Chapter 9.3
orbital-fixing branch rule made explicit as `hOrbitalFixing`: if a feasible solution `x̄` at node
`N_a` has a `1` in some orbit `O ∈ 𝒪_a` that also meets `F_a^0`, then `x̄` already lies in the
left-isomorphic solution set of `N_a`. -/
theorem mem_left_isomorphic_solution_set_of_orbit_meeting_fixed_zero
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (hOrbitalFixing :
      ∀ ⦃x O i⦄, x ∈ node.solutions → O ∈ orbitFamily →
        (O ∩ node.fixedZero).Nonempty → i ∈ O → x i = true →
          ∃ nodeLeft, leftOf nodeLeft node ∧
            ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y)
    (x : α → Bool)
    (hx : x ∈ node.solutions)
    (hOrbit : hasOrbitMeetingFixedZero orbitFamily node x) :
    x ∈ left_isomorphic_solution_set Γ leftOf node := sorry

/-- Proposition 9.15. Consider a node `N_a` of the enumeration tree. If `x̄` is a solution in
node `N_a` such that there exists an orbit `O ∈ 𝒪_a` satisfying `O ∩ F_a^0 ≠ ∅` and containing
an index `i` with `x̄ i = 1`, then there exists a node `N_b` to the left of `N_a` containing a
solution isomorphic to `x̄`. In Lean, the ambient Chapter 9.3 orbital-fixing branch rule is made
explicit by `hOrbitalFixing`. -/
theorem left_node_contains_isomorphic_solution_of_orbit_meeting_fixed_zero
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (hOrbitalFixing :
      ∀ ⦃x O i⦄, x ∈ node.solutions → O ∈ orbitFamily →
        (O ∩ node.fixedZero).Nonempty → i ∈ O → x i = true →
          ∃ nodeLeft, leftOf nodeLeft node ∧
            ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y)
    (x : α → Bool)
    (hx : x ∈ node.solutions)
    (hOrbit : hasOrbitMeetingFixedZero orbitFamily node x) :
    ∃ nodeLeft, leftOf nodeLeft node ∧
      ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y := sorry

end Proposition915
