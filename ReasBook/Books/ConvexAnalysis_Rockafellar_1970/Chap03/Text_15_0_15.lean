import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-!
Source/core/bridge triage:
- `source-facing`: Text 15.0.15 gives the `0/1` distance formula for the discrete metric.
- `core/canonical`: the primitive owner is `PseudoEMetricSpace.discrete`; separation and
  real-valued distance are bridge layers.
- `derived/bridge`: `EMetricSpace.discrete`, `PseudoMetricSpace.discrete`, and
  `MetricSpace.discrete`.
- `bridge/view`: coordinate-model textbook displays are specializations of this same owner-level
statement.
- Primitive data vs derived API: the primitive data is exactly the `0/1` extended-distance
formula with symmetry and triangle laws; separation and the real-valued metric interface are
derived bridges.
- Layer target: `core/canonical`, with a primitive `PseudoEMetricSpace` owner and derived
  `EMetricSpace`/`MetricSpace` bridges.
-/

namespace PseudoEMetricSpace

/-- Text 15.0.15 at the primitive owner layer: the discrete pseudo-extended metric. -/
@[reducible] noncomputable def discrete (α : Type u) : PseudoEMetricSpace α := by
  classical
  refine
    { edist := fun x y ↦ if x = y then 0 else 1
      edist_self := fun x ↦ by simp
      edist_comm := fun x y ↦ by
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy, Ne.symm hxy]
      edist_triangle := fun x y z ↦ by
        by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;> simp_all }

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The primitive `0/1` formula for the discrete extended metric. -/
@[simp] theorem edist_discrete (x y : α) :
    (PseudoEMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  rfl

/-- The discrete extended metric takes only finite values. -/
@[simp] theorem edist_discrete_ne_top (x y : α) :
    (PseudoEMetricSpace.discrete α).edist x y ≠ ⊤ := by
  by_cases hxy : x = y <;> simp [edist_discrete, hxy]

end

end PseudoEMetricSpace

namespace EMetricSpace

/-- Text 15.0.15 at the separated owner layer, derived from
`PseudoEMetricSpace.discrete`. -/
@[reducible] noncomputable def discrete (α : Type u) : EMetricSpace α := by
  classical
  refine
    { PseudoEMetricSpace.discrete α with
      eq_of_edist_eq_zero := ?_ }
  intro x y hxy
  by_cases h : x = y
  · exact h
  · have hne : (PseudoEMetricSpace.discrete α).edist x y ≠ 0 := by
      simp [PseudoEMetricSpace.edist_discrete, h]
    exact (hne hxy).elim

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The `0/1` formula for `EMetricSpace.discrete`. -/
@[simp] theorem edist_discrete (x y : α) :
    (EMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  rfl

/-- The separated discrete extended metric still takes only finite values. -/
@[simp] theorem edist_discrete_ne_top (x y : α) :
    (EMetricSpace.discrete α).edist x y ≠ ⊤ := by
  simpa [EMetricSpace.edist_discrete] using
    (PseudoEMetricSpace.edist_discrete_ne_top (α := α) x y)

end

end EMetricSpace

namespace PseudoMetricSpace

/-- The real-valued pseudometric bridge for Text 15.0.15. -/
@[reducible] noncomputable def discrete (α : Type u) : PseudoMetricSpace α := by
  exact @PseudoEMetricSpace.toPseudoMetricSpace α (PseudoEMetricSpace.discrete α)
    (fun x y ↦ PseudoEMetricSpace.edist_discrete_ne_top (α := α) x y)

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- The `0/1` formula at the pseudometric bridge layer. -/
@[simp] theorem dist_discrete (x y : α) :
    (PseudoMetricSpace.discrete α).dist x y = if x = y then 0 else 1 := by
  letI : PseudoMetricSpace α := PseudoMetricSpace.discrete α
  change (EDist.edist x y).toReal = if x = y then 0 else 1
  rw [PseudoEMetricSpace.edist_discrete (α := α) x y]
  by_cases hxy : x = y <;> simp [hxy]

/-- The corresponding extended-distance form at the pseudometric bridge layer. -/
@[simp] theorem edist_discrete (x y : α) :
    (PseudoMetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  letI : PseudoMetricSpace α := PseudoMetricSpace.discrete α
  change edist x y = if x = y then 0 else 1
  exact PseudoEMetricSpace.edist_discrete (α := α) x y

end

end PseudoMetricSpace

namespace MetricSpace

/-- Text 15.0.15: the canonical discrete metric on any carrier `α`, with distance `0` on the
diagonal and `1` off the diagonal. -/
@[reducible]
noncomputable def discrete (α : Type u) : MetricSpace α := by
  exact @EMetricSpace.toMetricSpace α (EMetricSpace.discrete α)
    (fun x y ↦ EMetricSpace.edist_discrete_ne_top (α := α) x y)

section

attribute [local instance] Classical.decEq

variable {α : Type u}

/-- Text 15.0.15 at the canonical owner layer: under the discrete metric on any carrier `α`,
the distance is exactly the `0/1` formula. Coordinate-model textbook displays are obtained by
specialization of this same theorem. -/
@[simp] theorem dist_discrete (x y : α) :
    (MetricSpace.discrete α).dist x y = if x = y then 0 else 1 := by
  letI : MetricSpace α := MetricSpace.discrete α
  change dist x y = if x = y then 0 else 1
  have hedist : edist x y = if x = y then 0 else 1 := by
    exact EMetricSpace.edist_discrete (α := α) x y
  rw [dist_edist, hedist]
  by_cases hxy : x = y <;> simp [hxy]

/-- The corresponding extended-distance form of `MetricSpace.dist_discrete`. -/
@[simp] theorem edist_discrete (x y : α) :
    (MetricSpace.discrete α).edist x y = if x = y then 0 else 1 := by
  letI : MetricSpace α := MetricSpace.discrete α
  change edist x y = if x = y then 0 else 1
  exact EMetricSpace.edist_discrete (α := α) x y

end

end MetricSpace
