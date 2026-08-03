module

public import Mathlib.Topology.Subpath

public section

open Function unitInterval

universe u

/-- Helper for Theorem 51.3: equal paths are path-homotopic. -/
lemma pathHomotopic_of_eq {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}
    {p q : Path x₀ x₁} (h : p = q) : Path.Homotopic p q := by
  -- Replace the second path by the first and use reflexivity of path homotopy.
  subst q
  exact Path.Homotopic.refl p

/-- Helper for Theorem 51.3: casting a full subpath back to the original endpoints
recovers the original path. -/
lemma subpathEndpointCast_eq_self {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}
    (f : Path x₀ x₁) (s t : unitInterval) (hsource : x₀ = f s) (htarget : x₁ = f t)
    (hs : s = 0) (ht : t = 1) :
    (f.subpath s t).cast hsource htarget = f := by
  -- Normalize the subpath parameters to the endpoints of the unit interval.
  subst s
  subst t
  -- Path extensionality avoids exposing the proof fields in the two endpoint casts.
  rw [Path.subpath_zero_one]
  ext parameter
  rfl

/-- Helper for Theorem 51.3: the endpoint-cast concatenation of successive subpaths
is path-homotopic to the original path. -/
lemma concatSubpathsCast_homotopic {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}
    (f : Path x₀ x₁) {n : ℕ} (a : Fin (n + 1) → unitInterval)
    (h_start : a 0 = 0) (h_end : a (Fin.last n) = 1) :
    Path.Homotopic
      ((Path.concat (f ∘ a) (fun i ↦ f.subpath (a i.castSucc) (a i.succ))).cast
        ((congrArg f h_start).trans f.source).symm
        ((congrArg f h_end).trans f.target).symm)
      f := by
  -- Use the canonical homotopy from the concatenation to the full subpath.
  have concatenationHomotopy := Path.Homotopic.concat_subpath f a
  -- Transport both paths to the fixed endpoints, then normalize the full subpath.
  have castHomotopy := concatenationHomotopy.pathCast
    ((congrArg f h_start).trans f.source).symm
    ((congrArg f h_end).trans f.target).symm
  have normalizedSubpath :
      (f.subpath (a 0) (a (Fin.last n))).cast
        ((congrArg f h_start).trans f.source).symm
        ((congrArg f h_end).trans f.target).symm = f :=
    subpathEndpointCast_eq_self f (a 0) (a (Fin.last n))
      ((congrArg f h_start).trans f.source).symm
      ((congrArg f h_end).trans f.target).symm h_start h_end
  have subpathHomotopy : Path.Homotopic
      ((f.subpath (a 0) (a (Fin.last n))).cast
        ((congrArg f h_start).trans f.source).symm
        ((congrArg f h_end).trans f.target).symm)
      f := pathHomotopic_of_eq normalizedSubpath
  exact castHomotopy.trans subpathHomotopy

/-- Theorem 51.3: A path class equals the class of the concatenation of its successive
affine subpaths. The source assumes that `a` is strictly increasing, but
`Path.Homotopic.concat_subpath` shows that only the endpoint conditions are needed. -/
theorem pathClass_eq_concatSubpaths {X : Type u} [TopologicalSpace X] {x₀ x₁ : X}
    (f : Path x₀ x₁) {n : ℕ} (a : Fin (n + 1) → unitInterval)
    (h_start : a 0 = 0) (h_end : a (Fin.last n) = 1) :
    (⟦f⟧ : Path.Homotopic.Quotient x₀ x₁) =
      ⟦(Path.concat (f ∘ a) (fun i ↦ f.subpath (a i.castSucc) (a i.succ))).cast
        ((congrArg f h_start).trans f.source).symm
        ((congrArg f h_end).trans f.target).symm⟧ := by
  -- Quotient equality is exactly path homotopy; reverse the structural homotopy.
  exact Path.Homotopic.Quotient.eq.mpr
    (concatSubpathsCast_homotopic f a h_start h_end).symm
