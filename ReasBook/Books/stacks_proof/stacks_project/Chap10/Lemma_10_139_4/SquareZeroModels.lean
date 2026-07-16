import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_139_4.BasicQuotients

open Algebra
open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

include hσ

/-- Helper for Lemma 10.139.4: formal smoothness gives a section of the completion projection
`AdicCompletion (ker σ) S → R`. -/
theorem smooth_section_completion_has_section :
    ∃ s : R →ₐ[R] AdicCompletion (RingHom.ker σ) S,
      (AdicCompletion.kerProj
          (smooth_section_sigma_surjective (R := R) (S := S) (σ := σ) hσ)).comp s =
        AlgHom.id R R := by
  -- The target `R` is formally smooth over itself, so the completion projection splits.
  exact Algebra.FormallySmooth.exists_kerProj_comp_eq_id
    (R := R) (A := R) (S := S) (f := σ)
    (smooth_section_sigma_surjective (R := R) (S := S) (σ := σ) hσ)

/-- Helper for Lemma 10.139.4: `I / I²` carries the opposite `R`-action induced by commutativity,
so it can serve as the square-zero summand in `TrivSqZeroExt`. -/
instance smooth_section_cotangent_opModule :
    Module Rᵐᵒᵖ (RingHom.ker σ).Cotangent :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

/-- Helper for Lemma 10.139.4: the left and right `R`-actions on `I / I²` coincide. -/
instance smooth_section_cotangent_isCentralScalar :
    IsCentralScalar R (RingHom.ker σ).Cotangent where
  op_smul_eq_smul _ _ := rfl

/-- Helper for Lemma 10.139.4: the natural reduction map `S / I² → S / I` for `I = ker σ`. -/
noncomputable def smooth_section_secondQuotToQuot :
    (S ⧸ (RingHom.ker σ) ^ 2) →ₐ[R] (S ⧸ RingHom.ker σ) :=
  Ideal.Quotient.factorₐ R <| by
    simpa [pow_two] using
      (show (RingHom.ker σ) * (RingHom.ker σ) ≤ RingHom.ker σ from Ideal.mul_le_right)

/-- Helper for Lemma 10.139.4: the kernel of `S / I² → S / I` is exactly the cotangent ideal
inside `S / I²`. This is the quotient-level form of the source statement that the kernel is
`I / I²`. -/
theorem smooth_section_secondQuot_ker_eq_cotangentIdeal :
    RingHom.ker (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)).toRingHom =
      (RingHom.ker σ).cotangentIdeal := by
  -- Unwinding the quotient map shows that vanishing in `S / I` is exactly membership in `I`.
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [smooth_section_secondQuotToQuot, Ideal.mk_mem_cotangentIdeal] using
    (show Ideal.Quotient.mk (RingHom.ker σ) x = 0 ↔ σ x = 0 by
      rw [Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker])

/-- Helper for Lemma 10.139.4: the cotangent summand in `S / I²` has square zero. -/
theorem smooth_section_cotangentToQuotientSquare_mul_eq_zero
    (x y : (RingHom.ker σ).Cotangent) :
    (RingHom.ker σ).cotangentToQuotientSquare x *
        (RingHom.ker σ).cotangentToQuotientSquare y = 0 := by
  -- Both cotangent classes lift to kernel elements, and products of such lifts land in `I²`.
  obtain ⟨x, rfl⟩ := (RingHom.ker σ).toCotangent_surjective x
  obtain ⟨y, rfl⟩ := (RingHom.ker σ).toCotangent_surjective y
  rw [Ideal.toCotangent_to_quotient_square, Ideal.toCotangent_to_quotient_square]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr <| by
    simpa [pow_two] using Ideal.mul_mem_mul x.2 y.2

/-- Helper for Lemma 10.139.4: reducing `S / I²` modulo `I` kills the cotangent summand. -/
theorem smooth_section_secondQuotToQuot_cotangentToQuotientSquare_eq_zero
    (x : (RingHom.ker σ).Cotangent) :
    smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)
      ((RingHom.ker σ).cotangentToQuotientSquare x) = 0 := by
  -- The cotangent summand is represented by an element of `I`, which vanishes in `S / I`.
  obtain ⟨x, rfl⟩ := (RingHom.ker σ).toCotangent_surjective x
  change Ideal.Quotient.mk (RingHom.ker σ) x = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr x.2

/-- Helper for Lemma 10.139.4: every class in `S / I²` splits as its scalar part from `R` plus a
unique cotangent contribution. This is the source decomposition `S / I² = φ(R) ⊕ I / I²`. -/
theorem smooth_section_secondQuot_eq_scalar_add_cotangent
    (x : S ⧸ (RingHom.ker σ) ^ 2) :
    ∃ y : (RingHom.ker σ).Cotangent,
      algebraMap R (S ⧸ (RingHom.ker σ) ^ 2)
          (((smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
              (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))) x) +
        (RingHom.ker σ).cotangentToQuotientSquare y = x := by
  let ρ : (S ⧸ (RingHom.ker σ) ^ 2) →ₐ[R] R :=
    (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
      (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))
  let z : S ⧸ (RingHom.ker σ) ^ 2 := x - algebraMap R _ (ρ x)
  have hz_quot :
      smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ) x =
        algebraMap R (S ⧸ RingHom.ker σ) (ρ x) := by
    -- Compare both classes after identifying `S / I` with `R` via the section.
    apply (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ).injective
    simp [ρ]
  have hz_mem :
      z ∈ (RingHom.ker σ).cotangentIdeal := by
    -- The residual term dies in `S / I`, so it lies in the cotangent ideal.
    have hzker : z ∈
        RingHom.ker (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)).toRingHom := by
      rw [RingHom.mem_ker]
      simp [z, hz_quot]
    rw [smooth_section_secondQuot_ker_eq_cotangentIdeal (R := R) (S := S) (σ := σ) hσ] at hzker
    exact hzker
  let y : (RingHom.ker σ).Cotangent :=
    (RingHom.ker σ).cotangentEquivIdeal.symm ⟨z, hz_mem⟩
  have hy :
      (RingHom.ker σ).cotangentToQuotientSquare y = z := by
    -- Translate the chosen element of the cotangent ideal back through the canonical equivalence.
    change ↑((RingHom.ker σ).cotangentEquivIdeal y) = z
    simpa [y] using congrArg Subtype.val
      ((RingHom.ker σ).cotangentEquivIdeal.apply_symm_apply ⟨z, hz_mem⟩)
  refine ⟨y, ?_⟩
  -- Substitute the residual cotangent term back into the scalar-plus-residual decomposition.
  calc
    algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) (ρ x) +
        (RingHom.ker σ).cotangentToQuotientSquare y =
      algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) (ρ x) + z := by rw [hy]
    _ = x := by
      simp [z, sub_eq_add_neg, add_left_comm]

/-- Helper for Lemma 10.139.4: the second-order quotient `S / I²` is the split square-zero
extension of `R` by `I / I²`, where `I = ker σ`. This is the target-side source decomposition
`S / I² = φ(R) ⊕ I / I²`. -/
noncomputable def smooth_section_trivSqZero_algEquiv_kerSquareQuot :
    TrivSqZeroExt R (RingHom.ker σ).Cotangent ≃ₐ[R] (S ⧸ (RingHom.ker σ) ^ 2) := by
  let F : TrivSqZeroExt R (RingHom.ker σ).Cotangent →ₐ[R] S ⧸ (RingHom.ker σ) ^ 2 :=
    TrivSqZeroExt.liftEquivOfComm
      ⟨(RingHom.ker σ).cotangentToQuotientSquare,
        smooth_section_cotangentToQuotientSquare_mul_eq_zero (R := R) (S := S) (σ := σ) hσ⟩
  -- Route correction: package the split square-zero model through the source decomposition
  -- `S / I² = φ(R) ⊕ I / I²`, so the remaining work is a flat bijectivity proof on the scalar and
  -- cotangent coordinates rather than repeated transport normalization.
  refine AlgEquiv.ofBijective F ⟨?_, ?_⟩
  · intro x y hxy
    suffices hker_zero : ∀ z : TrivSqZeroExt R (RingHom.ker σ).Cotangent, F z = 0 → z = 0 by
      have hzero : F (x - y) = 0 := by
        simpa [map_sub, hxy]
      exact sub_eq_zero.mp (hker_zero (x - y) hzero)
    intro z hz
    have hsum :
        algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) z.fst +
            (RingHom.ker σ).cotangentToQuotientSquare z.snd = 0 := by
      -- Expand `z` into its scalar and cotangent coordinates, then use `F z = 0`.
      calc
        algebraMap R (S ⧸ (RingHom.ker σ) ^ 2) z.fst +
            (RingHom.ker σ).cotangentToQuotientSquare z.snd =
          F (TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd) := by
            simp [F, map_add, TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inl,
              TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply]
        _ = F z := by rw [TrivSqZeroExt.inl_fst_add_inr_snd_eq]
        _ = 0 := hz
    have hfst_quot : algebraMap R (S ⧸ RingHom.ker σ) z.fst = 0 := by
      -- Reducing modulo `I` kills the cotangent part and leaves only the scalar coordinate.
      have := congrArg (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ)) hsum
      simpa [map_add,
        smooth_section_secondQuotToQuot_cotangentToQuotientSquare_eq_zero
          (R := R) (S := S) (σ := σ) hσ] using this
    have hfst : z.fst = 0 := by
      -- The section identifies `S / I` with `R`, so the scalar coordinate already vanishes in `R`.
      have := congrArg (smooth_section_quotientKerAlgEquiv (R := R) (S := S) (σ := σ) hσ)
        hfst_quot
      simpa using this
    have hsnd_zero :
        (RingHom.ker σ).cotangentToQuotientSquare z.snd = 0 := by
      -- Once the scalar coordinate is zero, the residual cotangent term must vanish too.
      simpa [hfst] using hsum
    have hsnd : z.snd = 0 :=
      (RingHom.ker σ).cotangentToQuotientSquare_injective hsnd_zero
    ext <;> simp [hfst, hsnd]
  · intro x
    obtain ⟨y, hy⟩ :=
      smooth_section_secondQuot_eq_scalar_add_cotangent (R := R) (S := S) (σ := σ) hσ x
    refine ⟨TrivSqZeroExt.inl (((smooth_section_quotientKerAlgEquiv
        (R := R) (S := S) (σ := σ) hσ).toAlgHom.comp
          (smooth_section_secondQuotToQuot (R := R) (S := S) (σ := σ))) x) +
        TrivSqZeroExt.inr y, ?_⟩
    -- The decomposition lemma directly gives a preimage under the forward map `F`.
    simpa [F, map_add, TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inl,
      TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply] using hy

section

omit [CommRing S] [Algebra R S] [Algebra.Smooth R S] σ hσ

/-- Helper for Lemma 10.139.4: each polynomial variable lies in the variable ideal. -/
theorem idealOfVars_variable_mem {d : ℕ} (i : Fin d) :
    MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R := by
  -- The variable ideal is generated by the variables themselves.
  simpa [MvPolynomial.idealOfVars] using
    (Ideal.subset_span (Set.mem_range_self i) :
      MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R)

/-- Helper for Lemma 10.139.4: the product of two variable classes vanishes modulo `J²`. -/
theorem idealOfVars_truncTwo_variable_mul_eq_zero {d : ℕ} (i j : Fin d) :
    (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) *
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X j) = 0 := by
  -- The product `X i * X j` already lies in `J²`, so its class is zero in the quotient.
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pow_two]
  exact Ideal.mul_mem_mul
    (idealOfVars_variable_mem (R := R) i)
    (idealOfVars_variable_mem (R := R) j)

/-- Helper for Lemma 10.139.4: evaluation at the square-zero variable classes sends `J²` to zero,
so it descends from `P` to `P / J²`. -/
theorem idealOfVars_trivSqZero_descends_aeval {d : ℕ}
    (p : MvPolynomial (Fin d) R)
    (hp : p ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) :
    MvPolynomial.aeval
        (fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R))) p =
      (0 : TrivSqZeroExt R (Fin d → R)) := by
  let Fraw : MvPolynomial (Fin d) R →ₐ[R] TrivSqZeroExt R (Fin d → R) :=
    MvPolynomial.aeval fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R))
  have hJker_comap :
      MvPolynomial.idealOfVars (Fin d) R ≤
        Ideal.comap Fraw.toRingHom (TrivSqZeroExt.kerIdeal R (Fin d → R)) := by
    -- Each generator `X i` lands in the kernel ideal of the projection to the scalar part.
    rw [MvPolynomial.idealOfVars]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change Fraw (MvPolynomial.X i) ∈
      RingHom.ker (TrivSqZeroExt.fstHom R R (Fin d → R)).toRingHom
    rw [RingHom.mem_ker]
    simp [Fraw]
  have hJker :
      Ideal.map Fraw.toRingHom (MvPolynomial.idealOfVars (Fin d) R) ≤
        TrivSqZeroExt.kerIdeal R (Fin d → R) := by
    exact (Ideal.map_le_iff_le_comap).2 hJker_comap
  have hJsq :
      Ideal.map Fraw.toRingHom ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) ≤
        (TrivSqZeroExt.kerIdeal R (Fin d → R)) ^ 2 := by
    -- Squaring preserves the containment into the square-zero ideal.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hJker 2
  have hp_image :
      Fraw p ∈ (TrivSqZeroExt.kerIdeal R (Fin d → R)) ^ 2 := by
    exact hJsq <| Ideal.mem_map_of_mem _ hp
  -- The kernel ideal of the scalar projection is square-zero.
  simpa [Fraw, TrivSqZeroExt.kerIdeal_sq] using hp_image

/-- Helper for Lemma 10.139.4: the classes of the variables define the canonical linear map from
the free module `Fin d → R` into `P / J²`. -/
noncomputable abbrev idealOfVars_truncTwo_variable_linearMap {d : ℕ} :
    (Fin d → R) →ₗ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  (Pi.basisFun R (Fin d)).constr R fun i ↦
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)

/-- Helper for Lemma 10.139.4: the canonical linear map into `P / J²` expands in the quotient
classes of the variables. -/
theorem idealOfVars_truncTwo_variable_linearMap_apply {d : ℕ} (x : Fin d → R) :
    idealOfVars_truncTwo_variable_linearMap (R := R) x =
      ∑ i, x i •
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i) := by
  -- The standard basis on `Fin d → R` records the coefficients of the quotient variable classes.
  rw [idealOfVars_truncTwo_variable_linearMap]
  rw [(Pi.basisFun R (Fin d)).constr_apply R
    (fun i ↦ Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) x]
  simp [Pi.basisFun_repr, Finsupp.sum_fintype]

/-- Helper for Lemma 10.139.4: the canonical linear map sends the `i`th basis vector to the class
of `X i` in `P / J²`. -/
theorem idealOfVars_truncTwo_variable_linearMap_basis {d : ℕ} (i : Fin d) :
    idealOfVars_truncTwo_variable_linearMap (R := R) (Pi.single i (1 : R)) =
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i) := by
  -- This is exactly how `Basis.constr` is defined on the standard basis vectors.
  rw [← Pi.basisFun_apply]
  simp [idealOfVars_truncTwo_variable_linearMap]

/-- Helper for Lemma 10.139.4: the image of the canonical linear map into `P / J²` has square
zero, because all pairwise products of variable classes vanish modulo `J²`. -/
theorem idealOfVars_trivSqZero_variable_linear_square_zero {d : ℕ}
    (x y : Fin d → R) :
    idealOfVars_truncTwo_variable_linearMap (R := R) x *
        idealOfVars_truncTwo_variable_linearMap (R := R) y = 0 := by
  -- Expand in the quotient variable basis and kill each pairwise product separately.
  rw [idealOfVars_truncTwo_variable_linearMap_apply, idealOfVars_truncTwo_variable_linearMap_apply,
    Finset.sum_mul]
  refine Finset.sum_eq_zero ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero ?_
  intro j _
  rw [smul_mul_assoc, mul_smul_comm, idealOfVars_truncTwo_variable_mul_eq_zero, smul_zero,
    smul_zero]

/-- Helper for Lemma 10.139.4: the descended evaluation map from `P / J²` to the split
square-zero model sends each variable class to the corresponding basis vector. -/
noncomputable def idealOfVars_trivSqZero_toAlgHom {d : ℕ} :
    MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 →ₐ[R]
      TrivSqZeroExt R (Fin d → R) :=
  Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    (MvPolynomial.aeval fun i : Fin d ↦ TrivSqZeroExt.inr (Pi.single i (1 : R)))
    (idealOfVars_trivSqZero_descends_aeval (R := R))

/-- Helper for Lemma 10.139.4: the descended forward map on `P / J²` sends the `i`th variable
class to the `i`th square-zero basis vector. -/
theorem idealOfVars_trivSqZero_toAlgHom_variable {d : ℕ} (i : Fin d) :
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
  -- The quotient map still evaluates each variable to the chosen square-zero basis vector.
  have hcomp :=
    AlgHom.congr_fun
      (Ideal.Quotient.liftₐ_comp ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
        (MvPolynomial.aeval fun j : Fin d ↦ TrivSqZeroExt.inr (Pi.single j (1 : R)))
        (idealOfVars_trivSqZero_descends_aeval (R := R)))
      (MvPolynomial.X i)
  simpa [idealOfVars_trivSqZero_toAlgHom] using hcomp

/-- Helper for Lemma 10.139.4: the split square-zero extension maps back to `P / J²` through the
linear map spanned by the variable classes. -/
noncomputable def idealOfVars_trivSqZero_fromAlgHom {d : ℕ} :
    TrivSqZeroExt R (Fin d → R) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  TrivSqZeroExt.liftEquivOfComm
    (R' := R)
    (A := MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)
    ⟨idealOfVars_truncTwo_variable_linearMap (R := R),
      idealOfVars_trivSqZero_variable_linear_square_zero (R := R)⟩

/-- Helper for Lemma 10.139.4: the inverse square-zero map sends `inr x` to the linear combination
of variable classes with coefficients `x`. -/
theorem idealOfVars_trivSqZero_fromAlgHom_inr {d : ℕ} (x : Fin d → R) :
    idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d) (TrivSqZeroExt.inr x) =
      idealOfVars_truncTwo_variable_linearMap (R := R) x := by
  -- The universal square-zero map restricts to the chosen linear map on the nilpotent summand.
  simp [idealOfVars_trivSqZero_fromAlgHom]

/-- Helper for Lemma 10.139.4: the square-zero coordinates `Pi.single i 1` reconstruct the
corresponding basis vector under the standard basis of `Fin d → R`. -/
theorem idealOfVars_trivSqZero_toAlgHom_linear {d : ℕ} (x : Fin d → R) :
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (idealOfVars_truncTwo_variable_linearMap (R := R) x) =
      TrivSqZeroExt.inr x := by
  -- Expand in the quotient variable basis and reassemble the vector in the square-zero summand.
  have hsum : ∑ i, x i • (Pi.single i (1 : R) : Fin d → R) = x := by
    ext i
    simpa [Pi.single_apply, mul_comm]
  rw [idealOfVars_truncTwo_variable_linearMap_apply]
  calc
    idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
        (∑ i, x i •
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      ∑ i, x i •
        idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) := by
        simp [map_sum]
    _ = ∑ i, x i • TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [idealOfVars_trivSqZero_toAlgHom_variable]
    _ = TrivSqZeroExt.inr (∑ i, x i • (Pi.single i (1 : R) : Fin d → R)) := by
      simp_rw [← TrivSqZeroExt.inr_smul]
      simpa using
        (TrivSqZeroExt.inr_sum (R := R) (M := Fin d → R) Finset.univ
          (fun i ↦ x i • (Pi.single i (1 : R) : Fin d → R))).symm
    _ = TrivSqZeroExt.inr x := by rw [hsum]

/-- Helper for Lemma 10.139.4: the two square-zero model maps on `P / J²` are inverse. -/
theorem idealOfVars_trivSqZero_fromAlgHom_comp_toAlgHom {d : ℕ} :
    (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d)).comp
        (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) := by
  -- Two maps out of the quotient agree once they agree on the polynomial variables.
  refine Ideal.Quotient.algHom_ext _ ?_
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [AlgHom.comp_apply, idealOfVars_trivSqZero_toAlgHom_variable,
    idealOfVars_trivSqZero_fromAlgHom_inr]

/-- Helper for Lemma 10.139.4: the two square-zero model maps on `P / J²` are inverse. -/
theorem idealOfVars_trivSqZero_toAlgHom_comp_fromAlgHom {d : ℕ} :
    (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d)).comp
        (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d)) =
      AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
  -- Two algebra maps out of the trivial square-zero extension agree once they agree on every
  -- square-zero generator `inr x`.
  apply TrivSqZeroExt.algHom_ext
  intro x
  rw [AlgHom.comp_apply, idealOfVars_trivSqZero_fromAlgHom_inr,
    idealOfVars_trivSqZero_toAlgHom_linear]
  simp

/-- Helper for Lemma 10.139.4: the source second-order quotient `P / J²` is the split square-zero
extension of `R` by the free module on the variables. -/
noncomputable abbrev idealOfVars_trivSqZero_algEquiv_truncTwo {d : ℕ} :
    (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) ≃ₐ[R]
      TrivSqZeroExt R (Fin d → R) :=
  AlgEquiv.ofAlgHom
    (idealOfVars_trivSqZero_toAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_fromAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_toAlgHom_comp_fromAlgHom (R := R) (d := d))
    (idealOfVars_trivSqZero_fromAlgHom_comp_toAlgHom (R := R) (d := d))

/-- Helper for Lemma 10.139.4: the explicit source-side square-zero equivalence sends the `i`th
variable class to the `i`th split square-zero basis vector. -/
theorem idealOfVars_trivSqZero_algEquiv_truncTwo_variable {d : ℕ} (i : Fin d) :
    idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
      TrivSqZeroExt.inr (Pi.single i (1 : R)) := by
  -- This is the computation rule inherited from the descended evaluation map.
  exact idealOfVars_trivSqZero_toAlgHom_variable (R := R) (d := d) i

end

/-- Helper for Lemma 10.139.4: the chosen basis identifies the standard coordinate vector
`Pi.single i 1` with the `i`th basis element in the cotangent module. -/
theorem basis_equivFun_symm_single {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) (i : Fin d) :
    b.equivFun.symm (Pi.single i (1 : R)) = b i := by
  -- The inverse coordinate map sends the standard basis vector back to the corresponding basis
  -- element.
  rw [b.equivFun_symm_apply]
  simp [Pi.single_apply]

/-- Helper for Lemma 10.139.4: the target-side square-zero equivalence sends `inr x` to the
cotangent class in `S / (ker σ)^2`. -/
theorem smooth_section_trivSqZero_algEquiv_kerSquareQuot_inr
    (x : (RingHom.ker σ).Cotangent) :
    smooth_section_trivSqZero_algEquiv_kerSquareQuot (R := R) (S := S) (σ := σ) hσ
        (TrivSqZeroExt.inr x) =
      (RingHom.ker σ).cotangentToQuotientSquare x := by
  -- Unfold the forward square-zero model only on the nilpotent summand.
  simp [smooth_section_trivSqZero_algEquiv_kerSquareQuot, TrivSqZeroExt.liftEquivOfComm_apply,
    TrivSqZeroExt.lift_apply_inr]

/-- Helper for Lemma 10.139.4: at truncation level `2`, the actual polynomial map agrees with the
composite through the explicit source and target split square-zero models. -/
theorem trunc_two_model_comparison_variable {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i)
    (i : Fin d) :
    (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom))
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
        Ideal.Quotient.mk ((RingHom.ker σ) ^ 2) ((f i : RingHom.ker σ) : S) := by
  -- Track the single variable class through the source model, the basis transport, and the
  -- target model until it becomes the quotient class of the chosen kernel lift.
  calc
    (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom))
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2) (MvPolynomial.X i)) =
        (RingHom.ker σ).cotangentToQuotientSquare
          (b.equivFun.symm (Pi.single i (1 : R))) := by
          rw [AlgHom.comp_apply, AlgHom.comp_apply]
          calc
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ)
                ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap)
                  ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d))
                    (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ 2)
                      (MvPolynomial.X i)))) =
                (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                  (R := R) (S := S) (σ := σ) hσ)
                    ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap)
                      (TrivSqZeroExt.inr (Pi.single i (1 : R)))) := by
                      congr 2
                      exact idealOfVars_trivSqZero_algEquiv_truncTwo_variable (R := R) (d := d) i
            _ = (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                  (R := R) (S := S) (σ := σ) hσ)
                    (TrivSqZeroExt.inr (b.equivFun.symm (Pi.single i (1 : R)))) := by
                      rw [TrivSqZeroExt.map_inr]
                      rfl
            _ = (RingHom.ker σ).cotangentToQuotientSquare
                  (b.equivFun.symm (Pi.single i (1 : R))) := by
                    rw [smooth_section_trivSqZero_algEquiv_kerSquareQuot_inr]
    _ = (RingHom.ker σ).cotangentToQuotientSquare (b i) := by
      rw [basis_equivFun_symm_single (R := R) (S := S) (σ := σ) (hσ := hσ) b i]
    _ = Ideal.Quotient.mk ((RingHom.ker σ) ^ 2) ((f i : RingHom.ker σ) : S) := by
      rw [← hf i, Ideal.toCotangent_to_quotient_square]
      rfl

/-- Helper for Lemma 10.139.4: at level `2`, quotient extensionality upgrades the variable
comparison to equality of the full truncation map with the square-zero-model composite. -/
theorem trunc_two_algHom_via_trivSqZero_models {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i) :
    cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2 =
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
        ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
          (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom) := by
  -- Compare the two quotient maps on polynomial variables; the `R`-algebra structure handles
  -- constants automatically, so `MvPolynomial.algHom_ext` reduces everything to the generator case.
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
  -- On `X i`, both maps land in the quotient class of the chosen kernel lift `f i`.
  simpa [cotangent_lift_truncated_map, cotangent_lift_polynomial_map] using
    (trunc_two_model_comparison_variable (R := R) (S := S) (σ := σ) hσ b f hf i).symm

/-- Helper for Lemma 10.139.4: transporting across the chosen basis and back is the identity on
the two split square-zero models. -/
theorem trivSqZero_map_basis_transport_cancel {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) :
    ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
      (TrivSqZeroExt.map b.equivFun.symm.toLinearMap) =
        AlgHom.id R (TrivSqZeroExt R (Fin d → R))) ∧
      ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
        (TrivSqZeroExt.map b.equivFun.toLinearMap) =
          AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)) := by
  have hsource :
      b.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap =
        (LinearMap.id : (Fin d → R) →ₗ[R] Fin d → R) := by
    ext x j
    simp
  have htarget :
      b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap =
        (LinearMap.id :
          (RingHom.ker σ).Cotangent →ₗ[R] (RingHom.ker σ).Cotangent) := by
    ext x
    simp
  constructor
  · -- Compose the forward and backward basis transports on the source square-zero model.
    calc
      (TrivSqZeroExt.map b.equivFun.toLinearMap).comp
          (TrivSqZeroExt.map b.equivFun.symm.toLinearMap) =
        TrivSqZeroExt.map (b.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap) := by
          rw [← TrivSqZeroExt.map_comp_map]
      _ = TrivSqZeroExt.map (LinearMap.id : (Fin d → R) →ₗ[R] Fin d → R) := by
        rw [hsource]
      _ = AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
        rw [TrivSqZeroExt.map_id]
  · -- Compose the backward and forward basis transports on the target square-zero model.
    calc
      (TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
          (TrivSqZeroExt.map b.equivFun.toLinearMap) =
        TrivSqZeroExt.map (b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap) := by
          rw [← TrivSqZeroExt.map_comp_map]
      _ = TrivSqZeroExt.map
          (LinearMap.id :
            (RingHom.ker σ).Cotangent →ₗ[R] (RingHom.ker σ).Cotangent) := by
        rw [htarget]
      _ = AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent) := by
        rw [TrivSqZeroExt.map_id]

/-- Helper for Lemma 10.139.4: the explicit split square-zero models give the actual inverse to
the truncation map `Ψtrunc 2`. -/
noncomputable def trunc_two_inverse_via_trivSqZero_models {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent) :
    S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 :=
  ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).symm.toAlgHom).comp
    ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom))

/-- Helper for Lemma 10.139.4: in the level-`2` model comparison, the target-side transport
`eS2.symm ≫ eS2` cancels after one controlled reassociation. -/
theorem trunc_two_target_transport_cancel {d : ℕ}
    (φ : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2 →ₐ[R]
      TrivSqZeroExt R (RingHom.ker σ).Cotangent) :
    ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
        (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom).comp
      (((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp φ) =
        φ := by
  let e :=
    smooth_section_trivSqZero_algEquiv_kerSquareQuot (R := R) (S := S) (σ := σ) hσ
  have he :
      (e.symm.toAlgHom.comp e.toAlgHom) =
        AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent) := by
    simpa [e] using (AlgEquiv.symm_comp (R := R) e)
  -- Reassociate only the exact middle factor so the square-zero equivalence cancels on the nose.
  calc
    e.symm.toAlgHom.comp (e.toAlgHom.comp φ) =
      (e.symm.toAlgHom.comp e.toAlgHom).comp φ := by
            rw [← AlgHom.comp_assoc]
    _ = (AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)).comp φ := by
          rw [he]
    _ = φ := by
          rw [AlgHom.id_comp]

/-- Helper for Lemma 10.139.4: in the level-`2` model comparison, the source-side transport
`eP2 ≫ eP2.symm` cancels after one controlled reassociation. -/
theorem trunc_two_source_transport_cancel {d : ℕ}
    (ψ : S ⧸ (RingHom.ker σ) ^ 2 →ₐ[R] TrivSqZeroExt R (Fin d → R)) :
    ((idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)).toAlgHom).comp
      (((idealOfVars_trivSqZero_algEquiv_truncTwo
          (R := R) (d := d)).symm.toAlgHom).comp ψ) =
        ψ := by
  let e := idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)
  have he :
      (e.toAlgHom.comp e.symm.toAlgHom) =
        AlgHom.id R (TrivSqZeroExt R (Fin d → R)) := by
    simpa [e] using (AlgEquiv.comp_symm (R := R) e)
  -- Reassociate only the exact middle factor so the source square-zero equivalence cancels.
  calc
    e.toAlgHom.comp (e.symm.toAlgHom.comp ψ) =
      (e.toAlgHom.comp e.symm.toAlgHom).comp ψ := by
            rw [← AlgHom.comp_assoc]
    _ =
        (AlgHom.id R (TrivSqZeroExt R (Fin d → R))).comp ψ := by
            rw [he]
    _ = ψ := by
          rw [AlgHom.id_comp]

/-- Helper for Lemma 10.139.4: the explicit square-zero-model inverse is inverse to the actual
truncation map at level `2`. -/
theorem trunc_two_inverse_via_trivSqZero_models_spec {d : ℕ}
    (b : Module.Basis (Fin d) R (RingHom.ker σ).Cotangent)
    (f : Fin d → RingHom.ker σ)
    (hf : ∀ i, (RingHom.ker σ).toCotangent (f i) = b i) :
    ((trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b).comp
        (cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2) =
      AlgHom.id R
        (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2)) ∧
      ((cotangent_lift_truncated_map (R := R) (S := S) (σ := σ) f 2).comp
        (trunc_two_inverse_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b) =
      AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2)) := by
  obtain ⟨hsourceBasis, htargetBasis⟩ :=
    trivSqZero_map_basis_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ) b
  constructor
  · -- Rewrite the actual truncation map through the explicit source and target square-zero models.
    rw [trunc_two_algHom_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b f hf]
    rw [trunc_two_inverse_via_trivSqZero_models]
    -- Reassociate to expose the exact `eS2.symm ≫ eS2` middle factor, then the basis transport.
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
    rw [trunc_two_target_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ)]
    calc
      ((idealOfVars_trivSqZero_algEquiv_truncTwo
          (R := R) (d := d)).symm.toAlgHom).comp
          ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
            ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
              (idealOfVars_trivSqZero_algEquiv_truncTwo
                (R := R) (d := d)).toAlgHom)) =
        ((idealOfVars_trivSqZero_algEquiv_truncTwo
            (R := R) (d := d)).symm.toAlgHom).comp
          (((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
              (TrivSqZeroExt.map b.equivFun.symm.toLinearMap)).comp
            (idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).toAlgHom) := by
              rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      _ = ((idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).symm.toAlgHom).comp
            ((AlgHom.id R (TrivSqZeroExt R (Fin d → R))).comp
              (idealOfVars_trivSqZero_algEquiv_truncTwo
                (R := R) (d := d)).toAlgHom) := by
              rw [hsourceBasis]
      _ = ((idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).symm.toAlgHom).comp
            (idealOfVars_trivSqZero_algEquiv_truncTwo
              (R := R) (d := d)).toAlgHom := by
              rw [AlgHom.id_comp]
      _ = AlgHom.id R
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ 2) := by
              simpa using
                (AlgEquiv.symm_comp
                  (R := R)
                  (idealOfVars_trivSqZero_algEquiv_truncTwo (R := R) (d := d)))
  · -- Repeat the same comparison in the opposite direction, cancelling the source model first.
    rw [trunc_two_algHom_via_trivSqZero_models (R := R) (S := S) (σ := σ) hσ b f hf]
    rw [trunc_two_inverse_via_trivSqZero_models]
    -- Reassociate to expose the exact `eP2 ≫ eP2.symm` middle factor, then the basis transport.
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc]
    rw [trunc_two_source_transport_cancel (R := R) (S := S) (σ := σ) (hσ := hσ)]
    calc
      ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
          (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
          ((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
            ((TrivSqZeroExt.map b.equivFun.toLinearMap).comp
              (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom)) =
        ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
            (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
          (((TrivSqZeroExt.map b.equivFun.symm.toLinearMap).comp
              (TrivSqZeroExt.map b.equivFun.toLinearMap)).comp
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) := by
              rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      _ = ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
            ((AlgHom.id R (TrivSqZeroExt R (RingHom.ker σ).Cotangent)).comp
              (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom) := by
              rw [htargetBasis]
      _ = ((smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).toAlgHom).comp
            (smooth_section_trivSqZero_algEquiv_kerSquareQuot
              (R := R) (S := S) (σ := σ) hσ).symm.toAlgHom := by
              rw [AlgHom.id_comp]
      _ = AlgHom.id R (S ⧸ (RingHom.ker σ) ^ 2) := by
              simpa using
                (AlgEquiv.comp_symm
                  (R := R)
                  (smooth_section_trivSqZero_algEquiv_kerSquareQuot
                    (R := R) (S := S) (σ := σ) hσ))

end SmoothSection

end
