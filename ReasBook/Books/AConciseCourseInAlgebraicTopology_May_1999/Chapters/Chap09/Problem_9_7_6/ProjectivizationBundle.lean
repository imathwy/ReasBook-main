import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Projectivization.Basic

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Problem_9_7_6

variable (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜]

/-- Helper for Problem 9.7.6: the standard projective chart where the `n`th coordinate is
nonzero. -/
def projectivizationCoordinateBaseSet (n : ℕ) : Set (ℙ 𝕜 (ℕ →₀ 𝕜)) :=
  {x | Projectivization.lift
      (fun v : { w : ℕ →₀ 𝕜 // w ≠ 0 } ↦ v.1 n ≠ 0)
      (fun a b t h ↦ by
        apply propext
        constructor
        · intro ha hb
          apply ha
          have hcoord : a.1 n = t * b.1 n := by
            simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
          simpa [hb] using hcoord
        · intro hb
          have ht : t ≠ 0 := by
            intro ht
            apply a.2
            simpa [h, ht] using h
          intro ha
          have hcoord : a.1 n = t * b.1 n := by
            simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
          have hmul : t * b.1 n = 0 := by
            simpa [ha] using hcoord
          exact hb ((mul_eq_zero.mp hmul).resolve_left ht))
      x}

/-- Helper for Problem 9.7.6: a projective point represented by `v` lies in the `n`th coordinate
chart exactly when the representative has nonzero `n`th coordinate. -/
theorem mk_mem_projectivizationCoordinateBaseSet_iff
    (n : ℕ) (v : ℕ →₀ 𝕜) (hv : v ≠ 0) :
    Projectivization.mk 𝕜 v hv ∈ projectivizationCoordinateBaseSet 𝕜 n ↔
      v n ≠ 0 := by
  -- Evaluate the descended predicate on the chosen representative.
  simp [projectivizationCoordinateBaseSet, Projectivization.lift_mk]

/-- Helper for Problem 9.7.6: the subtype-valued quotient map version of the chart membership
test. -/
theorem mk'_mem_projectivizationCoordinateBaseSet_iff
    (n : ℕ) (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) :
    Projectivization.mk' 𝕜 v ∈ projectivizationCoordinateBaseSet 𝕜 n ↔
      v.1 n ≠ 0 := by
  -- This is the previous representative test specialized to `Projectivization.mk'`.
  simpa [Projectivization.mk'_eq_mk] using
    mk_mem_projectivizationCoordinateBaseSet_iff (𝕜 := 𝕜) n v.1 v.2

/-- Helper for Problem 9.7.6: normalize a nonzero vector by dividing through its `n`th
coordinate. -/
def projectivizationCoordinateNormalize (n : ℕ)
    (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) : ℕ →₀ 𝕜 :=
  (v.1 n)⁻¹ • v.1

/-- Helper for Problem 9.7.6: coordinate normalization is constant on projective equivalence
classes. -/
theorem projectivizationCoordinateNormalize_eq_of_projectiveEq
    (n : ℕ) (a b : { w : ℕ →₀ 𝕜 // w ≠ 0 }) (t : 𝕜)
    (h : (a : ℕ →₀ 𝕜) = t • (b : ℕ →₀ 𝕜)) :
    projectivizationCoordinateNormalize 𝕜 n a =
      projectivizationCoordinateNormalize 𝕜 n b := by
  -- Split according to whether the chosen coordinate already vanishes.
  by_cases hb : b.1 n = 0
  · have ha : a.1 n = 0 := by
      have hcoord : a.1 n = t * b.1 n := by
        simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
      simpa [hb] using hcoord
    simp [projectivizationCoordinateNormalize, ha, hb]
  · have ht : t ≠ 0 := by
      intro ht
      apply a.2
      simpa [h, ht] using h
    have hcoord : a.1 n = t * b.1 n := by
      simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
    rw [projectivizationCoordinateNormalize, projectivizationCoordinateNormalize, hcoord, h,
      smul_smul]
    have hscalar : (t * b.1 n)⁻¹ * t = (b.1 n)⁻¹ := by
      field_simp [ht, hb]
    rw [hscalar]

/-- Helper for Problem 9.7.6: on the `n`th chart, normalization forces the `n`th coordinate to be
`1`. -/
theorem projectivizationCoordinateNormalize_apply
    (n : ℕ) (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) (hv : v.1 n ≠ 0) :
    projectivizationCoordinateNormalize 𝕜 n v n = 1 := by
  -- Evaluate the scaled vector at the normalizing coordinate.
  simp [projectivizationCoordinateNormalize, hv]

/-- Helper for Problem 9.7.6: normalization stays nonzero on the coordinate chart. -/
theorem projectivizationCoordinateNormalize_nonzero
    (n : ℕ) (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) (hv : v.1 n ≠ 0) :
    projectivizationCoordinateNormalize 𝕜 n v ≠ 0 := by
  -- The normalized vector still has `n`th coordinate equal to `1`.
  intro hzero
  have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) hzero
  simpa [projectivizationCoordinateNormalize_apply (𝕜 := 𝕜) n v hv] using hcoord

/-- Helper for Problem 9.7.6: multiplying the normalized representative back by the original
`n`th coordinate recovers the initial vector. -/
theorem smul_projectivizationCoordinateNormalize
    (n : ℕ) (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) (hv : v.1 n ≠ 0) :
    v.1 n • projectivizationCoordinateNormalize 𝕜 n v = v.1 := by
  -- Cancel the chosen coordinate pointwise after expanding the normalization.
  ext m
  simp [projectivizationCoordinateNormalize, hv, mul_assoc]

/-- Helper for Problem 9.7.6: on the coordinate chart, the normalized representative defines the
same projective point as the original vector. -/
theorem mk_projectivizationCoordinateNormalize_eq
    (n : ℕ) (v : { w : ℕ →₀ 𝕜 // w ≠ 0 }) (hv : v.1 n ≠ 0) :
    Projectivization.mk 𝕜
        (projectivizationCoordinateNormalize 𝕜 n v)
        (projectivizationCoordinateNormalize_nonzero (𝕜 := 𝕜) n v hv) =
      Projectivization.mk' 𝕜 v := by
  -- The original vector is obtained from the normalized one by scaling with `v n`.
  apply (Projectivization.mk_eq_mk_iff' 𝕜
      (projectivizationCoordinateNormalize 𝕜 n v) (v : ℕ →₀ 𝕜)
      (projectivizationCoordinateNormalize_nonzero (𝕜 := 𝕜) n v hv) v.2).2
  refine ⟨(v.1 n)⁻¹, ?_⟩
  ext m
  simp [projectivizationCoordinateNormalize, hv, mul_assoc]

end Problem_9_7_6
