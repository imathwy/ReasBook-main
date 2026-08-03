import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Example_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Example 13.8: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Example 13.8: coercing evenness to `EReal` lets us rewrite `φ t` as `φ |t|`. -/
lemma even_apply_norm_eq
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ) (t : ℝ) :
    (φ t : EReal) = (φ |t| : EReal) := by
  -- Split on the sign of `t` to rewrite `|t|` either as `t` or as `-t`.
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simpa using congrArg (fun y : Set.Ioi (⊥ : EReal) ↦ (y : EReal)) (hφ_even t).symm

/-- Helper for Example 13.8: every nontrivial real inner-product space contains a unit vector. -/
lemma exists_unit_vector [Nontrivial H] :
    ∃ e : H, ‖e‖ = 1 := by
  -- Normalize any nonzero vector to obtain a unit vector.
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  refine ⟨‖v‖⁻¹ • v, ?_⟩
  simpa using normalized_norm_eq_one hv

/-- Helper for Example 13.8: each radial affine defect is controlled by the scalar conjugate at
the norm of the dual variable. -/
lemma radial_affine_defect_le_scalar_conjugate
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (x u : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal)) ≤ φ.asEReal∗ ‖u‖ := by
  -- Compare the inner product with `‖x‖ * ‖u‖`, then test the scalar conjugate at `t = ‖x‖`.
  have hinner :
      (((⟪x, u⟫_ℝ : ℝ) : EReal) : EReal) ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal) : EReal) := by
    exact_mod_cast real_inner_le_norm x u
  rw [conjugate_apply]
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal))
      ≤ (((‖x‖ * ‖u‖ : ℝ) : EReal) - (φ ‖x‖ : EReal)) :=
        EReal.sub_le_sub hinner le_rfl
    _ = (((⟪‖x‖, ‖u‖⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal)) := by
      have hscalar : ⟪(‖x‖ : ℝ), ‖u‖⟫_ℝ = ‖x‖ * ‖u‖ := by
        simp [real_inner_eq_mul]
      rw [hscalar]
    _ ≤ ⨆ t : ℝ, ((⟪t, ‖u‖⟫_ℝ : ℝ) : EReal) - φ.asEReal t := by
      simpa [Function.asEReal_apply] using
        (le_iSup (fun t : ℝ ↦ ((⟪t, ‖u‖⟫_ℝ : ℝ) : EReal) - φ.asEReal t) ‖x‖)

/-- Helper for Example 13.8: in a subsingleton space, the radial conjugate identity requires
that `0` minimize `φ`. -/
theorem conjugate_comp_norm_eq_comp_norm_conjugate_of_even_of_subsingleton
    [Subsingleton H] (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ_min : ∀ t : ℝ, (φ 0 : EReal) ≤ φ t) :
    (φ ∘ (norm : H → ℝ)).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) := by
  funext u
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  -- Collapse the ambient space to the origin and compare the two scalar suprema directly.
  simp only [Function.comp_apply, norm_zero]
  apply le_antisymm
  · rw [conjugate_apply, conjugate_apply]
    refine iSup_le ?_
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    -- The radial supremum contains the scalar competitor at `t = 0`.
    simpa [Function.comp_apply, Function.asEReal_apply] using
      (le_iSup (fun t : ℝ ↦ ((⟪t, (0 : ℝ)⟫_ℝ : ℝ) : EReal) - φ.asEReal t) (0 : ℝ))
  · rw [conjugate_apply, conjugate_apply]
    refine iSup_le ?_
    intro t
    -- The minimizing property of `0` bounds every scalar defect by the radial value at `x = 0`.
    calc
      (((⟪t, (0 : ℝ)⟫_ℝ : ℝ) : EReal) - φ.asEReal t)
        ≤ (((⟪(0 : H), (0 : H)⟫_ℝ : ℝ) : EReal) - ((φ ∘ norm).asEReal (0 : H))) := by
          exact
            EReal.sub_le_sub (by simp) (by simpa [Function.asEReal_apply] using hφ_min t)
      _ ≤ ⨆ x : H, ((⟪x, (0 : H)⟫_ℝ : ℝ) : EReal) - ((φ ∘ norm).asEReal x) := by
          exact
            le_iSup (fun x : H ↦ ((⟪x, (0 : H)⟫_ℝ : ℝ) : EReal) - ((φ ∘ norm).asEReal x))
              (0 : H)

/-- Helper for Example 13.8: the scalar affine defects are realized by radial witnesses in every
nontrivial space. -/
lemma scalar_conjugate_le_radial_conjugate_of_even [Nontrivial H]
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ) (u : H) :
    φ.asEReal∗ ‖u‖ ≤ ((φ ∘ (norm : H → ℝ)).asEReal∗) u := by
  -- Route correction: the reverse inequality is proved by explicit ray witnesses, not by trying
  -- to commute conjugation with composition abstractly.
  rw [conjugate_apply]
  refine iSup_le ?_
  intro t
  by_cases hu : u = 0
  · -- When `u = 0`, any unit vector gives a ray of norm `|t|`.
    obtain ⟨e, he⟩ := (exists_unit_vector : ∃ e : H, ‖e‖ = 1)
    let x : H := |t| • e
    have hxnorm : ‖x‖ = |t| := by
      -- Compute the norm of the radial witness from the unit-vector normalization.
      dsimp [x]
      rw [norm_smul, he, Real.norm_of_nonneg (abs_nonneg t)]
      simp
    have hterm :
        (((⟪t, ‖u‖⟫_ℝ : ℝ) : EReal) - (φ t : EReal)) =
          (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal)) := by
      -- Both affine defects reduce to `-φ |t|` after rewriting by evenness.
      subst hu
      rw [show (φ t : EReal) = (φ |t| : EReal) by
          simpa using even_apply_norm_eq φ hφ_even t]
      simp [x, hxnorm]
    calc
      (((⟪t, ‖u‖⟫_ℝ : ℝ) : EReal) - (φ t : EReal))
        = (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal)) := hterm
      _ ≤ ((φ ∘ (norm : H → ℝ)).asEReal∗) u := by
        rw [conjugate_apply]
        exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - ((φ ∘ norm).asEReal y)) x
  · -- When `u ≠ 0`, align the witness with the normalized direction of `u`.
    let x : H := |t| • (‖u‖⁻¹ • u)
    have hxnorm : ‖x‖ = |t| := by
      -- The witness lies on the ray through `u` with prescribed radius `|t|`.
      dsimp [x]
      rw [norm_smul, normalized_norm_eq_one hu, Real.norm_of_nonneg (abs_nonneg t)]
      simp
    have hinner :
        ⟪x, u⟫_ℝ = |t| * ‖u‖ := by
      -- The normalized direction attains the Cauchy-Schwarz bound with `u`.
      dsimp [x]
      rw [real_inner_smul_left, normalized_inner_eq_norm hu]
    have hmul :
        t * ‖u‖ ≤ |t| * ‖u‖ := by
      exact mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg u)
    have hmul_ereal :
        (((t * ‖u‖ : ℝ) : EReal) : EReal) ≤ (((|t| * ‖u‖ : ℝ) : EReal) : EReal) := by
      exact_mod_cast hmul
    calc
      (((⟪t, ‖u‖⟫_ℝ : ℝ) : EReal) - (φ t : EReal))
        = (((t * ‖u‖ : ℝ) : EReal) - (φ t : EReal)) := by
          have hscalar : ⟪(t : ℝ), ‖u‖⟫_ℝ = t * ‖u‖ := by
            simp [real_inner_eq_mul]
          rw [hscalar]
      _ ≤ (((|t| * ‖u‖ : ℝ) : EReal) - (φ t : EReal)) :=
        EReal.sub_le_sub hmul_ereal le_rfl
      _ = (((|t| * ‖u‖ : ℝ) : EReal) - (φ |t| : EReal)) := by
        rw [even_apply_norm_eq φ hφ_even t]
      _ = (((⟪x, u⟫_ℝ : ℝ) : EReal) - (φ ‖x‖ : EReal)) := by
        simp [hinner, hxnorm, x]
      _ ≤ ((φ ∘ (norm : H → ℝ)).asEReal∗) u := by
        rw [conjugate_apply]
        exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - ((φ ∘ norm).asEReal y)) x

/-- Helper for Example 13.8: the radial conjugate identity on every nontrivial branch. -/
theorem conjugate_comp_norm_eq_comp_norm_conjugate_of_even_of_nontrivial
    [Nontrivial H] (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ) :
    (φ ∘ (norm : H → ℝ)).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) := by
  funext u
  -- The source proof splits into the universal upper bound and the ray-witness lower bound.
  simp only [Function.comp_apply]
  apply le_antisymm
  · rw [conjugate_apply]
    refine iSup_le ?_
    intro x
    exact radial_affine_defect_le_scalar_conjugate (H := H) φ x u
  · exact scalar_conjugate_le_radial_conjugate_of_even (H := H) φ hφ_even u

/-- Example 13.8: Let `φ : ℝ → ]-∞,+∞]` be even. Then `(φ ∘ ‖·‖)^* = φ^* ∘ ‖·‖`. In the
zero-dimensional branch, the source proof uses the additional premise that `0` minimizes `φ`. -/
theorem conjugate_comp_norm_eq_comp_norm_conjugate_of_even_all_spaces
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ)
    (hφ_subsingleton_min : Subsingleton H → ∀ t : ℝ, (φ 0 : EReal) ≤ φ t) :
    (φ ∘ (norm : H → ℝ)).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) := by
  by_cases hH : Subsingleton H
  · letI : Subsingleton H := hH
    -- On the zero-dimensional branch, the extra minimizing hypothesis is exactly the missing input.
    exact
      conjugate_comp_norm_eq_comp_norm_conjugate_of_even_of_subsingleton (H := H) φ
        (hφ_subsingleton_min hH)
  · letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    -- Otherwise the textbook ray-witness proof applies verbatim.
    exact conjugate_comp_norm_eq_comp_norm_conjugate_of_even_of_nontrivial (H := H) φ hφ_even

/-- Helper for Example 13.8: on nontrivial spaces, the unsuffixed radial conjugate API is the
usual two-argument theorem used downstream. -/
theorem conjugate_comp_norm_eq_comp_norm_conjugate_of_even
    [Nontrivial H] (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ) :
    (φ ∘ (norm : H → ℝ)).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) := by
  -- Route correction: keep the public theorem as the nontrivial wrapper, while the textbook
  -- entry itself is the all-spaces statement with an explicit zero-dimensional hypothesis.
  exact conjugate_comp_norm_eq_comp_norm_conjugate_of_even_of_nontrivial (H := H) φ hφ_even

end ERealFunction
