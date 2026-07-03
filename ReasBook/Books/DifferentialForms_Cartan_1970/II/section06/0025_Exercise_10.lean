import Mathlib
import cartan.II.section06.«0015_Remark_II_2_extra_6»

open scoped ComplexConjugate

-- Declarations for this item will be appended below by the statement pipeline.

/-
This file has one `bridge/view` theorem and one source-facing exercise theorem.
The owner abstraction for reflection is `schwarzReflection` from
`0015_Remark_II_2_extra_6`; we keep only the textbook bridge back to the raw
formula `z ↦ conj (u (conj z))`.
-/
/-- Helper for Exercise 10: the hypothesis of being real-valued on the real-axis slice can be
rewritten as conjugation invariance at every point of the domain with zero imaginary part. -/
lemma conj_apply_eq_of_zero_im {D : Set ℂ} {u : ℂ → ℂ}
    (hu_real : ∀ x : ℝ, (x : ℂ) ∈ D → conj (u (x : ℂ)) = u (x : ℂ)) :
    ∀ z ∈ D, z.im = 0 → conj (u z) = u z := by
  intro z hz hz_im
  -- Replace the complex point on the real axis by its real part, where the hypothesis applies.
  have hz_eq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hz_im]
  simpa [hz_eq] using hu_real z.re (by simpa [hz_eq] using hz)

/-- Helper for Exercise 10: once a function is fixed by Schwarz reflection on a conjugation-stable
domain, the piecewise reflection formula collapses to `conj (u (conj z)) = u z` everywhere on the
domain. -/
lemma conj_comp_conj_eq_of_schwarz_reflection_fixed {D : Set ℂ} {u : ℂ → ℂ}
    (hfix : Set.EqOn u (schwarzReflection u) D) (hD_symm : Set.MapsTo conj D D)
    (haxis : ∀ z ∈ D, z.im = 0 → conj (u z) = u z) :
    Set.EqOn (fun z ↦ conj (u (conj z))) u D := by
  intro z hz
  by_cases hz_neg : z.im < 0
  · -- On the lower half-plane, the reflected formula is exactly the definition of Schwarz reflection.
    simpa [schwarzReflection_apply_of_neg_im (f := u) (z := z) hz_neg] using (hfix hz).symm
  · have hz_nonneg : 0 ≤ z.im := le_of_not_gt hz_neg
    by_cases hz_zero : z.im = 0
    · -- On the real axis, `conj z = z`, so the boundary condition gives the required equality.
      have hz_conj : conj z = z := by
        apply Complex.ext <;> simp [hz_zero]
      simpa [hz_conj] using haxis z hz hz_zero
    · -- In the upper half-plane, apply the fixed-point identity at `conj z`, which lies below the axis.
      have hz_pos : 0 < z.im := lt_of_le_of_ne hz_nonneg (Ne.symm hz_zero)
      have hconj_mem : conj z ∈ D := hD_symm hz
      have hconj_neg : (conj z).im < 0 := by
        simpa [Complex.conj_im] using (neg_neg_iff_pos.mpr hz_pos)
      have hconj_eval : u (conj z) = conj (u z) := by
        calc
          u (conj z) = schwarzReflection u (conj z) := hfix hconj_mem
          _ = conj (u z) := by
            simpa [Complex.conj_conj] using
              schwarzReflection_apply_of_neg_im (f := u) (z := conj z) hconj_neg
      simpa [Complex.conj_conj] using congrArg conj hconj_eval

/-- Helper for Exercise 10: a holomorphic function on a connected open set symmetric with respect
to complex conjugation that is real-valued on the real-axis slice agrees with its reflected
conjugate on the whole domain. -/
-- Proof sketch: apply the upstream Schwarz reflection extension theorem to `u`, then rewrite the
-- resulting piecewise reflection back to the raw formula `z ↦ conj (u (conj z))`.
theorem eqOn_conj_comp_conj_of_real_values_on_real_axis {D : Set ℂ} {u : ℂ → ℂ}
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hD_symm : Set.MapsTo conj D D) (hu : DifferentiableOn ℂ u D)
    (hu_real : ∀ x : ℝ, (x : ℂ) ∈ D → conj (u (x : ℂ)) = u (x : ℂ)) :
    Set.EqOn (fun z ↦ conj (u (conj z))) u D := by
  -- First move the real-axis hypothesis into the boundary form expected by Schwarz reflection.
  have haxis : ∀ z ∈ D, z.im = 0 → conj (u z) = u z :=
    conj_apply_eq_of_zero_im hu_real
  have hu_cont : ContinuousOn u (D ∩ {z : ℂ | 0 ≤ z.im}) :=
    (hu.mono (by
      intro z hz
      exact hz.1)).continuousOn
  have hu_upper : DifferentiableOn ℂ u (D ∩ {z : ℂ | 0 < z.im}) := by
    refine hu.mono ?_
    intro z hz
    exact hz.1
  -- The reflection theorem identifies `u` with its Schwarz reflection on all of `D`.
  have hfix : Set.EqOn u (schwarzReflection u) D := by
    refine eqOn_schwarzReflection_of_differentiableOn hD_open hD_connected hD_symm
      hu_cont hu_upper haxis hu ?_
    intro z hz
    rfl
  -- Now rewrite the piecewise reflected extension back to the raw conjugate-reflection formula.
  exact conj_comp_conj_eq_of_schwarz_reflection_fixed hfix hD_symm haxis

/-- Exercise 10: if `f = g + I h` on a connected open set symmetric with respect to the real axis,
and `g` and `h` are holomorphic there with real values on the real-axis slice `D ∩ ℝ`, then the
reflected conjugate of `f` is `g - I h` on `D`. -/
-- Proof sketch: apply
-- `eqOn_conj_comp_conj_of_real_values_on_real_axis` to `g` and `h`, obtaining
-- `conj (g (conj z)) = g z` and `conj (h (conj z)) = h z` on `D`. Then conjugate the identity
-- `f z = g z + I * h z`, use `conj I = -I`, and substitute those reflected formulas.
theorem conjugate_split_eqOn {D : Set ℂ} {f g h : ℂ → ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hD_symm : Set.MapsTo conj D D)
    (hg : DifferentiableOn ℂ g D) (hh : DifferentiableOn ℂ h D)
    (hg_real : ∀ x : ℝ, (x : ℂ) ∈ D → conj (g (x : ℂ)) = g (x : ℂ))
    (hh_real : ∀ x : ℝ, (x : ℂ) ∈ D → conj (h (x : ℂ)) = h (x : ℂ))
    (hfg : Set.EqOn f (fun z ↦ g z + Complex.I * h z) D) :
    Set.EqOn (fun z ↦ conj (f (conj z))) (fun z ↦ g z - Complex.I * h z) D := by
  -- Route correction: use the same Schwarz-reflection invariant for `g` and `h`, then conjugate
  -- the decomposition of `f` at the reflected point `conj z`.
  have hg_reflect : Set.EqOn (fun z ↦ conj (g (conj z))) g D :=
    eqOn_conj_comp_conj_of_real_values_on_real_axis hD_open hD_connected hD_symm hg hg_real
  have hh_reflect : Set.EqOn (fun z ↦ conj (h (conj z))) h D :=
    eqOn_conj_comp_conj_of_real_values_on_real_axis hD_open hD_connected hD_symm hh hh_real
  intro z hz
  -- Evaluate the decomposition at `conj z`, which remains in the domain by symmetry.
  have hconj_mem : conj z ∈ D := hD_symm hz
  have hfg_conj : f (conj z) = g (conj z) + Complex.I * h (conj z) := hfg hconj_mem
  -- Conjugating this identity and using the reflected formulas for `g` and `h` gives the claim.
  calc
    conj (f (conj z)) = conj (g (conj z) + Complex.I * h (conj z)) := by
      simpa using congrArg conj hfg_conj
    _ = g z - Complex.I * h z := by
      simp [sub_eq_add_neg, hg_reflect hz, hh_reflect hz]
