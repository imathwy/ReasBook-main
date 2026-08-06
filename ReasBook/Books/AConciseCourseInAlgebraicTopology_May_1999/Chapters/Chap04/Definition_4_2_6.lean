import Mathlib.Topology.Homotopy.Basic

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: mathlib provides `ContinuousMap.Homotopy` and `ContinuousMap.HomotopyRel`
-- for homotopies fixed on a subset, but no bundled deformation-retract notion was found in the
-- current environment.

/-- Definition 4.2.6. A subspace `A ⊆ X` is a deformation retract if there is a homotopy from
`ContinuousMap.id X` to a map whose image is contained in `A`, and this homotopy fixes `A` at all
times. -/
def IsDeformationRetract (A : Set X) : Prop :=
  ∃ r : C(X, X), (ContinuousMap.id X).HomotopicRel r A ∧ Set.range r ⊆ A

/-- A subspace is a deformation retract exactly when it admits an endpoint map and a homotopy from
`ContinuousMap.id X` to that map that is fixed on `A` and ends in `A`. -/
theorem isDeformationRetract_iff_exists {A : Set X} :
    IsDeformationRetract A ↔
      ∃ r : C(X, X), (ContinuousMap.id X).HomotopicRel r A ∧ ∀ x, r x ∈ A := by
  constructor
  · rintro ⟨r, hrel, hrange⟩
    exact ⟨r, hrel, fun x ↦ hrange ⟨x, rfl⟩⟩
  · rintro ⟨r, hrel, hA⟩
    exact ⟨r, hrel, by
      rintro y ⟨x, hxy⟩
      rw [← hxy]
      exact hA x⟩

/-- Data witnessing that a subspace `A ⊆ X` is a deformation retract of `X`. -/
structure DeformationRetract (A : Set X) where
  /-- The endpoint map of the deformation. -/
  retract : C(X, X)
  /-- The homotopy from `ContinuousMap.id X` to the endpoint map, fixed on `A` at all times. -/
  homotopy : (ContinuousMap.id X).HomotopyRel retract A
  /-- The time-`1` image of the deformation is contained in `A`. -/
  range_subset : Set.range retract ⊆ A

namespace DeformationRetract

/-- Build a deformation retract witness from a pointwise proof that the endpoint map lands in
`A`. -/
def ofMem {A : Set X} (retract : C(X, X)) (homotopy : (ContinuousMap.id X).HomotopyRel retract A)
    (retract_mem : ∀ x, retract x ∈ A) : DeformationRetract A where
  retract := retract
  homotopy := homotopy
  range_subset := by
    rintro y ⟨x, rfl⟩
    exact retract_mem x

/-- A deformation retract witness can be evaluated as its endpoint map `X → X`. -/
instance {A : Set X} : CoeFun (DeformationRetract A) (fun _ ↦ X → X) where
  coe h := h.retract

/-- Evaluating a deformation retract witness agrees with evaluating its endpoint map. -/
@[simp]
theorem coe_apply {A : Set X} (h : DeformationRetract A) (x : X) :
    h x = h.retract x := rfl

/-- The endpoint map of a deformation retract takes values in the retract subset. -/
theorem retract_mem {A : Set X} (h : DeformationRetract A) (x : X) : h.retract x ∈ A :=
  h.range_subset ⟨x, rfl⟩

/-- The endpoint map of a deformation retract fixes `A` pointwise. -/
theorem eqOn {A : Set X} (h : DeformationRetract A) : Set.EqOn h.retract id A := by
  intro x hx
  simpa using (h.homotopy.fst_eq_snd hx).symm

/-- The endpoint map of a deformation retract fixes the subspace pointwise. -/
theorem retract_eq_self {A : Set X} (h : DeformationRetract A) {x : X} (hx : x ∈ A) :
    h.retract x = x :=
  DeformationRetract.eqOn h hx

/-- A deformation retract witness yields a relative homotopy from `ContinuousMap.id X` to its
endpoint map. -/
theorem homotopicRel {A : Set X} (h : DeformationRetract A) :
    (ContinuousMap.id X).HomotopicRel h.retract A :=
  ⟨h.homotopy⟩

/-- A deformation retract witness determines the corresponding source-level property. -/
theorem toIsDeformationRetract {A : Set X} (h : DeformationRetract A) : IsDeformationRetract A :=
  ⟨h.retract, h.homotopicRel, h.range_subset⟩

/-- A deformation retract witness determines the corresponding source-level property. -/
theorem isDeformationRetract {A : Set X} (h : DeformationRetract A) : IsDeformationRetract A :=
  h.toIsDeformationRetract

end DeformationRetract

/-- The existential formulation is equivalent to the existence of a bundled deformation retract
witness. -/
theorem isDeformationRetract_iff_nonempty_deformationRetract {A : Set X} :
    IsDeformationRetract A ↔ Nonempty (DeformationRetract A) := by
  constructor
  · rintro ⟨r, hrel, hrange⟩
    rcases hrel with ⟨homotopy⟩
    refine ⟨DeformationRetract.ofMem r homotopy ?_⟩
    intro x
    exact hrange ⟨x, rfl⟩
  · rintro ⟨h⟩
    exact h.toIsDeformationRetract
