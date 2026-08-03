module

public import Topology_Munkres_2000.Book.Exercise_58_10.Homotopy
public import Topology_Munkres_2000.Book.Exercise_58_10.Reflection

public section

/-- An integer-valued degree assignment for continuous self-maps of the standard `n`-sphere,
with the homotopy, composition, and normalization laws of the exercise. -/
structure SphereDegree (n : ℕ) where
  /-- The integer assigned to each continuous self-map of the standard sphere. -/
  toFun : C(StandardSphere n, StandardSphere n) → ℤ
  /-- Homotopic sphere self-maps have the same degree. -/
  homotopy {h k : C(StandardSphere n, StandardSphere n)}
    (homotopic : h.Homotopic k) : toFun h = toFun k
  /-- Degree is multiplicative under composition. -/
  comp (h k : C(StandardSphere n, StandardSphere n)) :
    toFun (h.comp k) = toFun h * toFun k
  /-- The identity sphere map has degree one. -/
  id : toFun (ContinuousMap.id (StandardSphere n)) = 1
  /-- Every constant sphere map has degree zero. -/
  const (x : StandardSphere n) : toFun (ContinuousMap.const (StandardSphere n) x) = 0
  /-- Reflection in the last coordinate has degree negative one. -/
  reflection : toFun (StandardSphere.reflection n) = -1

namespace SphereDegree

/-- Build a sphere degree assignment from a function satisfying the exercise laws. -/
def ofFunction {n : ℕ} (degree : C(StandardSphere n, StandardSphere n) → ℤ)
    (homotopy : ∀ {h k}, h.Homotopic k → degree h = degree k)
    (comp : ∀ h k, degree (h.comp k) = degree h * degree k)
    (id : degree (ContinuousMap.id (StandardSphere n)) = 1)
    (const : ∀ x, degree (ContinuousMap.const (StandardSphere n) x) = 0)
    (reflection : degree (StandardSphere.reflection n) = -1) : SphereDegree n :=
  { toFun := degree
    homotopy := homotopy
    comp := comp
    id := id
    const := const
    reflection := reflection }

/-- Evaluate a sphere degree assignment on a continuous sphere self-map. -/
@[expose]
def eval {n : ℕ} (degree : SphereDegree n)
    (h : C(StandardSphere n, StandardSphere n)) : ℤ :=
  degree.toFun h

/-- The source notation `deg h`, with the chosen sphere-degree assignment made explicit. -/
scoped notation:arg "deg[" degree "] " h:arg => eval degree h

/-- Evaluation of a sphere degree assignment is evaluation of its stored function. -/
@[simp]
theorem eval_eq {n : ℕ} (degree : SphereDegree n)
    (h : C(StandardSphere n, StandardSphere n)) : deg[degree] h = degree.toFun h := rfl

/-- The defining laws of a sphere degree assignment, in source-facing form. -/
theorem spec {n : ℕ} (degree : SphereDegree n) :
    (∀ {h k : C(StandardSphere n, StandardSphere n)},
        h.Homotopic k → deg[degree] h = deg[degree] k) ∧
      (∀ h k : C(StandardSphere n, StandardSphere n),
        deg[degree] (h.comp k) = deg[degree] h * deg[degree] k) ∧
      deg[degree] (ContinuousMap.id (StandardSphere n)) = 1 ∧
      (∀ x : StandardSphere n,
        deg[degree] (ContinuousMap.const (StandardSphere n) x) = 0) ∧
      deg[degree] (StandardSphere.reflection n) = -1 :=
  ⟨degree.homotopy, degree.comp, degree.id, degree.const, degree.reflection⟩

/-- Helper for Exercise 58.10: reflection in any coordinate has degree negative one. -/
theorem coordinateReflection_eq_negOne {n : ℕ} (degree : SphereDegree n)
    (i : Fin (n + 1)) :
    deg[degree] (StandardSphere.coordinateReflection n i) = -1 := by
  -- Multiplicativity and the involution law show that the coordinate swap has square degree one.
  have swapDegree_square :
      deg[degree] (StandardSphere.coordinateSwap n i) *
          deg[degree] (StandardSphere.coordinateSwap n i) = 1 := by
    calc
      deg[degree] (StandardSphere.coordinateSwap n i) *
          deg[degree] (StandardSphere.coordinateSwap n i) =
          deg[degree] ((StandardSphere.coordinateSwap n i).comp
            (StandardSphere.coordinateSwap n i)) :=
        (degree.comp _ _).symm
      _ = deg[degree] (ContinuousMap.id (StandardSphere n)) :=
        congrArg (eval degree) (StandardSphere.coordinateSwap_comp_self n i)
      _ = 1 := degree.id
  -- Conjugating the distinguished reflection contributes the swap degree twice, hence cancels.
  rw [StandardSphere.coordinateReflection_def, degree.spec.2.1, degree.spec.2.1,
    degree.spec.2.2.2.2]
  calc
    deg[degree] (StandardSphere.coordinateSwap n i) *
        (-1 * deg[degree] (StandardSphere.coordinateSwap n i)) =
        -(deg[degree] (StandardSphere.coordinateSwap n i) *
          deg[degree] (StandardSphere.coordinateSwap n i)) := by ring
    _ = -1 := congrArg Neg.neg swapDegree_square

/-- Helper for Exercise 58.10: the degree of a list of coordinate reflections is negative one
raised to the length of the list. -/
theorem coordinateReflections_eq_pow {n : ℕ} (degree : SphereDegree n)
    (indices : List (Fin (n + 1))) :
    deg[degree] (StandardSphere.coordinateReflections n indices) =
      (-1 : ℤ) ^ indices.length := by
  -- Each recursive composition contributes one factor of negative one.
  induction indices with
  | nil =>
      rw [StandardSphere.coordinateReflections_nil]
      exact degree.id
  | cons i indices ih =>
      rw [StandardSphere.coordinateReflections_cons, degree.spec.2.1,
        coordinateReflection_eq_negOne, ih, List.length_cons, pow_succ']

/-- The antipodal map of `Sⁿ` has degree `(-1) ^ (n + 1)`. -/
theorem antipodal_eq {n : ℕ} (degree : SphereDegree n) :
    deg[degree] (StandardSphere.antipodal n) = (-1 : ℤ) ^ (n + 1) := by
  -- Reflecting the complete coordinate list is the antipodal map and has `n + 1` factors.
  calc
    deg[degree] (StandardSphere.antipodal n) =
        deg[degree] (StandardSphere.coordinateReflections n
          (List.ofFn fun i : Fin (n + 1) ↦ i)) :=
      congrArg (eval degree) (StandardSphere.coordinateReflections_all_eq_antipodal n).symm
    _ = (-1 : ℤ) ^ (List.ofFn fun i : Fin (n + 1) ↦ i).length :=
      coordinateReflections_eq_pow degree _
    _ = (-1 : ℤ) ^ (n + 1) := by rw [List.length_ofFn]

end SphereDegree
