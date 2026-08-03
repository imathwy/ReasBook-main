import Mathlib
import BauschkeLean.Chap02.Definition_2_23
import BauschkeLean.Chap02.Example_2_57
import BauschkeLean.Chap17.Proposition_17_10

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 17.11: coercing a real-valued function through `toEReal` turns strict
convexity on `Set.univ` into the owner-level strict convexity notion, and conversely. -/
lemma strictlyConvex_toEReal_iff_strictConvexOn_univ
    {f : H → ℝ} :
    ERealFunction.StrictlyConvex f.toEReal ↔ StrictConvexOn ℝ Set.univ f := by
  constructor
  · intro hstrict
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ hxy a b ha hb hab
    have hb_eq : b = 1 - a := by
      linarith
    have ha_lt_one : a < 1 := by
      linarith
    -- Convert the owner-level strict Jensen inequality back to the real-valued one.
    have hineq :
        (((f (a • x + b • y) : ℝ) : EReal)) <
          (((a * f x + b * f y : ℝ) : EReal)) := by
      simpa [Function.effectiveDomain_toEReal, Function.toEReal_apply, EReal.coe_mul,
        EReal.coe_add, hb_eq] using
        hstrict (x := x) (by simp) (y := y) (by simp) hxy (α := a) ha ha_lt_one
    exact_mod_cast hineq
  · intro hstrict x _ y _ hxy a ha ha1
    -- Apply strict convexity of the real-valued function and cast the result to `EReal`.
    have hineq :
        f (a • x + (1 - a) • y) < a * f x + (1 - a) * f y := by
      simpa [smul_eq_mul] using
        hstrict.2 (x := x) (by simp) (y := y) (by simp) hxy ha (sub_pos.mpr ha1) (by ring)
    have hineqE :
        (((f (a • x + (1 - a) • y) : ℝ) : EReal)) <
          (((a * f x + (1 - a) * f y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hineqE

/-- Helper for Example 17.11: Example 2.57 identifies the Gâteaux derivative field of the
quadratic form `x ↦ ⟪x, A x⟫_ℝ` on all of `H`. -/
lemma quadratic_form_hasGateauxDerivativeOn_univ
    (A : H →L[ℝ] H) :
    HasGateauxDerivativeOn (fun x : H ↦ ⟪x, A x⟫_ℝ)
      (fun x ↦ InnerProductSpace.toDual ℝ H ((A + A.adjoint) x)) Set.univ := by
  have hquadratic :
      HasGateauxDerivativeOn (fun x : H ↦ ⟪A x, x⟫_ℝ)
        (fun x ↦ InnerProductSpace.toDual ℝ H ((A + A.adjoint) x)) Set.univ := by
    intro x hx
    -- Example 2.57 computes the Fréchet derivative of the same quadratic form at `u = 0`.
    have hfun : (fun z : H ↦ ⟪A z, z⟫_ℝ) = quadratic_affine_functional A (0 : H) := by
      funext z
      simp [quadratic_affine_functional]
    rw [hfun]
    simpa using (quadratic_affine_functional_hasFDerivAt A (0 : H) x).hasGateauxDerivativeAt
  -- Commute the real inner product to match the textbook normalization `⟪x, A x⟫`.
  simpa [real_inner_comm] using hquadratic

/-- Helper for Example 17.11: for a linear field represented via `toDual`, strict Gâteaux
monotonicity on `Set.univ` is exactly strict monotonicity of the underlying operator. -/
lemma strictGateauxDerivativeMonotoneOn_toDual_iff_isStrictlyMonotone
    (B : H →L[ℝ] H) :
    ERealFunction.StrictGateauxDerivativeMonotoneOn
        (fun x ↦ InnerProductSpace.toDual ℝ H (B x)) Set.univ ↔
      B.toLinearMap.IsStrictlyMonotone := by
  constructor
  · intro hmono z hz
    -- Evaluate the pairwise monotonicity inequality against the pair `(z, 0)`.
    have hpair :
        0 <
          ((InnerProductSpace.toDual ℝ H (B z)) -
            (InnerProductSpace.toDual ℝ H (B 0))) (z - 0) :=
      hmono z (by simp) 0 (by simp) hz
    simpa [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply] using hpair
  · intro hmono x _ y _ hxy
    let z : H := x - y
    have hz : z ≠ 0 := sub_ne_zero.mpr hxy
    have hpair : 0 < ⟪B z, z⟫_ℝ := hmono z hz
    have hpair' : ⟪B y, x - y⟫_ℝ < ⟪B x, x - y⟫_ℝ := by
      -- Expand the quadratic form of `x - y` into the corresponding endpoint pairing inequality.
      simpa [z, map_sub, inner_sub_left, sub_pos] using hpair
    -- Rewrite the single-vector quadratic form as the monotonicity pairing of the field.
    simpa [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply] using hpair'

/-- Example 17.11: for a bounded linear operator `A` on a real Hilbert space, the quadratic form
`x ↦ ⟪x, A x⟫_ℝ` is strictly convex on `H` if and only if the symmetric part `A + A†` is strictly
monotone. -/
theorem quadraticForm_strictConvexOn_univ_iff_symmetricPart_isStrictlyMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      (A + A.adjoint).toLinearMap.IsStrictlyMonotone := by
  let q : H → ℝ := fun x ↦ ⟪x, A x⟫_ℝ
  let DT : H → H →L[ℝ] ℝ := fun x ↦ InnerProductSpace.toDual ℝ H ((A + A.adjoint) x)
  have hproper : ERealFunction.IsProper q.toEReal.asEReal := by
    refine ⟨?_, ?_⟩
    · -- The `toEReal` owner of a real-valued function never attains `-∞`.
      intro x
      simp [Function.asEReal_apply, Function.toEReal_apply]
    · -- Any point witnesses nonempty domain because `q` is finite everywhere.
      refine ⟨0, ?_⟩
      simp [ERealFunction.dom, Function.asEReal_apply, Function.toEReal_apply]
  have hDT :
      HasGateauxDerivativeOn (fun x ↦ ((q.toEReal x : EReal).toReal)) DT
        (ERealFunction.effectiveDomain q.toEReal) := by
    -- Example 2.57 gives the derivative field of the finite-valued quadratic owner on all of `H`.
    simpa [q, DT, Function.effectiveDomain_toEReal, Function.toEReal_apply] using
      quadratic_form_hasGateauxDerivativeOn_univ (A := A)
  have hopen : IsOpen (ERealFunction.effectiveDomain q.toEReal) := by
    simp [Function.effectiveDomain_toEReal]
  have hconv : Convex ℝ (ERealFunction.effectiveDomain q.toEReal) := by
    simpa [Function.effectiveDomain_toEReal] using convex_univ
  -- Combine the `toEReal` bridge, the strict-support criterion, and the monotonicity rewrite.
  calc
    StrictConvexOn ℝ Set.univ q ↔ ERealFunction.StrictlyConvex q.toEReal := by
      simpa [q] using
        (strictlyConvex_toEReal_iff_strictConvexOn_univ (f := q)).symm
    _ ↔ ERealFunction.StrictGateauxSupportInequalityOn q.toEReal DT := by
      simpa [q, DT, Function.effectiveDomain_toEReal] using
        ERealFunction.strictlyConvex_iff_strictGateauxSupportInequalityOn_of_open_convex_effectiveDomain
          q.toEReal DT hproper hopen hconv hDT
    _ ↔ ERealFunction.StrictGateauxDerivativeMonotoneOn DT
          (ERealFunction.effectiveDomain q.toEReal) := by
      simpa [q, DT, Function.effectiveDomain_toEReal] using
        ERealFunction.strict_support_iff_strict_monotone_of_open_convex_effectiveDomain
          q.toEReal DT hproper hopen hconv hDT
    _ ↔ ERealFunction.StrictGateauxDerivativeMonotoneOn DT Set.univ := by
      simp [DT, Function.effectiveDomain_toEReal]
    _ ↔ (A + A.adjoint).toLinearMap.IsStrictlyMonotone := by
      simpa [DT] using
        strictGateauxDerivativeMonotoneOn_toDual_iff_isStrictlyMonotone (B := A + A.adjoint)
