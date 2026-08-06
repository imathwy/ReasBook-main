import Mathlib.Topology.Homotopy.Basic

universe u

open scoped unitInterval

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: mathlib provides `ContinuousMap.HomotopyRel`,
-- `ContinuousMap.HomotopicRel`, and the unit interval `I`, but no bundled NDR-pair owner was
-- found in the current environment.

/-- Data witnessing that `A ⊆ X` is an NDR-pair. -/
structure NDRPair (A : Set X) where
  /-- The control map `u : X → I`. -/
  control : C(X, I)
  /-- The endpoint map `x ↦ h(x, 1)` of the deformation. -/
  retract : C(X, X)
  /-- The homotopy `h` starts at `ContinuousMap.id X` and is fixed on `A` at all times. -/
  homotopy : (ContinuousMap.id X).HomotopyRel retract A
  /-- The zero set of the control map is exactly `A`. -/
  zeroSet_eq : control ⁻¹' ({0} : Set I) = A
  /-- If `u x < 1`, then the endpoint `h(x, 1)` lies in `A`. -/
  endpoint_mem : ∀ x, control x < 1 → retract x ∈ A

/-- Definition 6.4.1. A subspace `A ⊆ X` is an NDR-pair if it admits a witness `NDRPair A`. -/
def IsNDRPair (A : Set X) : Prop :=
  ∃ u : C(X, I), ∃ r : C(X, X),
    (ContinuousMap.id X).HomotopicRel r A ∧
      u ⁻¹' ({0} : Set I) = A ∧
      ∀ x, u x < 1 → r x ∈ A

/-- A subspace is an NDR-pair exactly when it admits the source-level control map, endpoint map,
and relative homotopy data. -/
theorem isNDRPair_iff_exists {A : Set X} :
    IsNDRPair A ↔
      ∃ u : C(X, I), ∃ r : C(X, X),
        (ContinuousMap.id X).HomotopicRel r A ∧
          u ⁻¹' ({0} : Set I) = A ∧
          ∀ x, u x < 1 → r x ∈ A :=
  Iff.rfl

/-- An NDR-pair subspace is closed. -/
theorem IsNDRPair.isClosed {A : Set X} (hA : IsNDRPair A) : IsClosed A := by
  rcases hA with ⟨u, r, hrel, hzero, hendpoint⟩
  simpa [hzero] using (isClosed_singleton : IsClosed ({0} : Set I)).preimage u.continuous

namespace NDRPair

/-- An NDR-pair witness can be evaluated as its endpoint map `X → X`. -/
instance {A : Set X} : CoeFun (NDRPair A) (fun _ ↦ X → X) where
  coe h := h.retract

/-- Evaluating an NDR-pair witness agrees with evaluating its endpoint map. -/
@[simp]
theorem coe_apply {A : Set X} (h : NDRPair A) (x : X) : h x = h.retract x := rfl

/-- The control map of an NDR-pair witness vanishes exactly on `A`. -/
theorem control_eq_zero_iff {A : Set X} (h : NDRPair A) (x : X) :
    h.control x = 0 ↔ x ∈ A := by
  change x ∈ h.control ⁻¹' ({0} : Set I) ↔ x ∈ A
  simp [h.zeroSet_eq]

/-- The endpoint map of an NDR-pair witness lands in `A` whenever `control x < 1`. -/
theorem retract_mem_of_control_lt_one {A : Set X} (h : NDRPair A) {x : X}
    (hx : h.control x < 1) : h.retract x ∈ A :=
  h.endpoint_mem x hx

/-- The endpoint map of an NDR-pair witness fixes `A` pointwise. -/
theorem eqOn {A : Set X} (h : NDRPair A) : Set.EqOn h.retract id A := by
  intro x hx
  simpa using (h.homotopy.fst_eq_snd hx).symm

/-- The endpoint map of an NDR-pair witness fixes each point of `A`. -/
theorem retract_eq_self {A : Set X} (h : NDRPair A) {x : X} (hx : x ∈ A) :
    h.retract x = x :=
  h.eqOn hx

/-- An NDR-pair witness yields the corresponding existential property. -/
theorem toIsNDRPair {A : Set X} (h : NDRPair A) : IsNDRPair A :=
  ⟨h.control, h.retract, ⟨h.homotopy⟩, h.zeroSet_eq, h.endpoint_mem⟩

end NDRPair

/-- The existential formulation is equivalent to the existence of a bundled NDR-pair witness. -/
theorem isNDRPair_iff_nonempty_ndrPair {A : Set X} :
    IsNDRPair A ↔ Nonempty (NDRPair A) := by
  constructor
  · rintro ⟨u, r, hrel, hzero, hendpoint⟩
    rcases hrel with ⟨homotopy⟩
    exact ⟨⟨u, r, homotopy, hzero, hendpoint⟩⟩
  · rintro ⟨h⟩
    exact h.toIsNDRPair
