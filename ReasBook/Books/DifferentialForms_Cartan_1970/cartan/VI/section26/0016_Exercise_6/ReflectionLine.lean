import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0013_Corollary_II_2_extra_5»
import DifferentialForms_Cartan_1970.VI.section26.«0015_Exercise_5»

open scoped ComplexConjugate
open EuclideanGeometry

noncomputable section

/-- Helper for Exercise 6: the canonical affine parametrization of `reflection_line c t hc`
straightens that line to the real axis. -/
theorem preimage_reflection_line_eq_real_axis
    {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    let v : ℂ := u + Complex.I * star c
    let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
    A ⁻¹' (reflection_line c t hc : Set ℂ) = {ζ : ℂ | ζ.im = 0} := by
  dsimp
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
  have hvsub : v - u = Complex.I * star c := by
    -- The affine step from `u` to `v` is exactly the chosen normal direction.
    simp [u, v]
  have huv : u ≠ v := by
    -- The line is nondegenerate because its second endpoint is displaced by `I * conj c`.
    intro huv_eq
    have hdiff : v - u = 0 := by
      simp [huv_eq]
    have hzero : Complex.I * star c = 0 := by
      simpa [hvsub] using hdiff
    have hstar : star c = 0 := by
      exact (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero
    exact hc (by simpa using hstar)
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Unfold the textbook line model into the affine span of its two defining points.
    simp [reflection_line, u, v]
  -- Replace the packaged reflection line by its explicit affine-span presentation.
  simpa [hline, u, v, A, hvsub] using preimage_affine_line_eq_real_axis_of_ne huv

/-- Helper for Exercise 6: after the same affine straightening, complex conjugation should agree
with Euclidean reflection across `reflection_line c t hc`. -/
theorem reflection_line_straightening_intertwines_conj
    {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    let v : ℂ := u + Complex.I * star c
    let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
    ∀ ζ : ℂ, A (conj ζ) = reflection (reflection_line c t hc) (A ζ) := by
  dsimp
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  let A : ℂ → ℂ := fun ζ ↦ u + (v - u) * ζ
  have hvsub : v - u = Complex.I * star c := by
    -- The affine chart direction is the chosen imaginary tangent to the reflection line.
    simp [u, v]
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Unfold the textbook reflection line into the affine line through the chosen base points.
    simp [reflection_line, u, v]
  intro ζ
  let n : ℂ := (-(ζ.im : ℝ)) • star c
  have hbase_mem_line : A (ζ.re : ℂ) ∈ (line[ℝ, u, v] : Set ℂ) := by
    -- The real part parameterizes points on the straightened line.
    simpa [A, hvsub, vadd_eq_add, smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
      (smul_vsub_vadd_mem_affineSpan_pair (ζ.re) u v)
  have hbase_mem : A (ζ.re : ℂ) ∈ (reflection_line c t hc : Set ℂ) := by
    simpa [hline] using hbase_mem_line
  have hnormal_line : n ∈ (line[ℝ, u, v] : AffineSubspace ℝ ℂ).directionᗮ := by
    -- The normal vector is a real multiple of `star c`, which is orthogonal to the line direction
    -- `Complex.I * star c`.
    refine Submodule.smul_mem _ _ ?_
    rw [direction_affineSpan, vectorSpan_pair_rev,
      Submodule.mem_orthogonal_singleton_iff_inner_left]
    simpa [hvsub, smul_eq_mul, mul_comm] using
      (real_inner_I_smul_self (𝕜 := ℂ) (E := ℂ) (x := star c))
  have hnormal : n ∈ (reflection_line c t hc).directionᗮ := by
    simpa [hline] using hnormal_line
  have hsplit : ∀ η : ℂ, A η = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
    intro η
    -- Split the affine chart into its real-axis point plus the normal displacement.
    have haux :
        A ((η.re : ℂ) + (η.im : ℂ) * Complex.I) = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
      calc
        A ((η.re : ℂ) + (η.im : ℂ) * Complex.I)
            = u + (Complex.I * star c) * ((η.re : ℂ) + (η.im : ℂ) * Complex.I) := by
                simp [A, hvsub]
        _ = u + (Complex.I * star c) * (η.re : ℂ) +
              ((Complex.I * star c) * ((η.im : ℂ) * Complex.I)) := by
                ring
        _ = u + (Complex.I * (η.re : ℂ) * star c) +
              ((Complex.I * Complex.I) * ((η.im : ℂ) * star c)) := by
                ring
        _ = u + (Complex.I * star c) * (η.re : ℂ) - ((η.im : ℂ) * star c) := by
                simp [Complex.I_mul_I, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
        _ = ((-(η.im : ℝ)) • star c) +ᵥ A (η.re : ℂ) := by
                simp [A, hvsub, vadd_eq_add, sub_eq_add_neg, smul_eq_mul, add_assoc,
                  add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    simpa [Complex.re_add_im] using haux
  have hreflect :
      reflection (reflection_line c t hc) (A ζ) = -n +ᵥ A (ζ.re : ℂ) := by
    -- Reflecting flips exactly the orthogonal normal component and fixes the base point on the
    -- line.
    rw [hsplit ζ]
    exact reflection_orthogonal_vadd hbase_mem hnormal
  -- Route correction: rather than unfolding reflection globally, compare both sides through the
  -- same line point `A ζ.re` and opposite normal vectors.
  calc
    A (conj ζ) = ((-((conj ζ).im : ℝ)) • star c) +ᵥ A ((conj ζ).re : ℂ) := hsplit (conj ζ)
    _ = -n +ᵥ A (ζ.re : ℂ) := by
      simp [n, Complex.conj_re, Complex.conj_im]
    _ = reflection (reflection_line c t hc) (A ζ) := hreflect.symm
