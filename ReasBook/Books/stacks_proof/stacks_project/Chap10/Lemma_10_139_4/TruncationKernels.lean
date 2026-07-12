import Mathlib
import StacksProject_2024.Chap10.Lemma_10_139_4.SquareZeroModels

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

/-- Helper for Lemma 10.139.4: for any ideal `K`, the transition ideal `K^n / K^(n + 1)` in
`A / K^(n + 1)` has square zero once `n > 0`. -/
theorem quotient_pow_transition_square_zero
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    (Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n)) ^ 2 = ⊥ := by
  -- The square is the image of `K^(2n)`, and `2n ≥ n + 1` for positive `n`.
  rw [pow_two, ← Ideal.map_mul, ← pow_add]
  have hle : n + 1 ≤ n + n := by
    omega
  exact eq_bot_mono
    (Ideal.map_mono (Ideal.pow_le_pow_right hle))
    (Ideal.map_quotient_self _)

/-- Helper for Lemma 10.139.4: the kernel of the quotient transition `A / K^(n + 1) → A / K^n`
is the image of `K^n` in `A / K^(n + 1)`. -/
theorem factorPow_kernel_eq_map_pow
    {A : Type*} [CommRing A] (K : Ideal A) (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n)) =
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- This is the quotient-power kernel description specialized to successive powers.
  simpa [Ideal.Quotient.factorPow] using
    (Ideal.Quotient.factor_ker (I := K ^ (n + 1)) (J := K ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n)))

/-- Helper for Lemma 10.139.4: for any ideal `K`, the kernel of the quotient transition
`A / K^(n + 1) → A / K^n` is nilpotent. -/
theorem factorPow_transition_kernel_isNilpotent
    {A : Type*} [CommRing A] (K : Ideal A) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow K (Nat.le_succ n))) := by
  -- The transition kernel is the image of `K^n`, and its square vanishes in `A / K^(n + 1)`.
  refine ⟨2, ?_⟩
  rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
    (A := A) (K := K) (n := n)]
  simpa using
    quotient_pow_transition_square_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := A) (K := K) (n := n) hn

/-- Helper for Lemma 10.139.4: the kernel of the transition
`P / J^(n + 1) → P / J^n` is square-zero, so it is nilpotent. -/
theorem truncation_transition_kernel_mul_eq_zero {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    {x y : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)}
    (hx :
      x ∈ RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)))
    (hy :
      y ∈ RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))) :
    x * y = 0 := by
  have hx' :
      x ∈ Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
    ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    -- The transition kernel is exactly the image of the previous power `J^n`.
    rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R)
      (K := MvPolynomial.idealOfVars (Fin d) R) (n := n)] at hx
    exact hx
  have hy' :
      y ∈ Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
    ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
    -- The same kernel description applies to the second factor.
    rw [factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R)
      (K := MvPolynomial.idealOfVars (Fin d) R) (n := n)] at hy
    exact hy
  have hxy :
      x * y ∈
        (Ideal.map
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
          ((MvPolynomial.idealOfVars (Fin d) R) ^ n)) ^ 2 := by
    -- Products of kernel elements lie in the square of the transition ideal.
    rw [pow_two]
    exact Ideal.mul_mem_mul hx' hy'
  have hsq :
      (Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        ((MvPolynomial.idealOfVars (Fin d) R) ^ n)) ^ 2 = ⊥ := by
    -- The image ideal is square-zero because `2n ≥ n + 1` for positive `n`.
    simpa using
      quotient_pow_transition_square_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
        (A := MvPolynomial (Fin d) R)
        (K := MvPolynomial.idealOfVars (Fin d) R) (n := n) hn
  have hzero_mem :
      x * y ∈
        (⊥ :
          Ideal
            (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))) := by
    simpa [hsq] using hxy
  -- Passing to the quotient by `J^(n + 1)` kills every element of the square of the transition
  -- ideal, so the product vanishes.
  simpa using hzero_mem

/-- Helper for Lemma 10.139.4: reducing `A / K^(m + 1)` directly to `A / K` has kernel equal to
the image of `K` in `A / K^(m + 1)`. -/
theorem factorPow_to_one_kernel_eq_map
    {A : Type*} [CommRing A] (K : Ideal A) (m : ℕ) :
    RingHom.ker
      (Ideal.Quotient.factorPow K (Nat.succ_le_of_lt (Nat.succ_pos m))) =
        Ideal.map (Ideal.Quotient.mk (K ^ (m + 1))) K := by
  -- This is the power-transition kernel formula specialized to reduction all the way to level `1`.
  rw [RingHom.ker_eq_comap_bot]
  have hmap : Ideal.map (Ideal.Quotient.mk (K ^ 1)) K = ⊥ := by
    rw [pow_one]
    exact Ideal.map_quotient_self K
  rw [← hmap]
  simpa [pow_one] using
    (Ideal.map_mk_comap_factorPow (I := K) (a := 1) (b := m + 1)
      (Nat.succ_pos 0) (Nat.succ_le_of_lt (Nat.succ_pos m)))

/-- Helper for Lemma 10.139.4: if an endomorphism of `P / J^(n + 1)` becomes the identity after
reducing modulo `J^n`, then the error on each variable class lies in the transition kernel. -/
theorem truncation_selfmap_variable_error_mem_kernel {d : ℕ} {n : ℕ}
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i) ∈
      RingHom.ker
        (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) := by
  -- Apply the quotient transition to the variable error and use that `α` fixes the lower
  -- truncation to see that the error reduces to zero.
  rw [RingHom.mem_ker]
  calc
    Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i))) -
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) := by
          simp
    _ =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
          (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) := by
          -- Evaluate the identity `q ∘ α = q` on the variable class.
          have hαi :=
            congrArg
              (fun β =>
                β
                  (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                    (MvPolynomial.X i)))
              hα
          simpa [AlgHom.comp_apply] using congrArg
            (fun z =>
              z - Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)
                (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i))) hαi
    _ = 0 := sub_self _

/-- Helper for Lemma 10.139.4: each variable class in `P / J^(n + 1)` comes from the image of the
variable ideal `J`. -/
theorem truncation_variable_class_mem_idealOfVars_image {d n : ℕ} (i : Fin d) :
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  -- The quotient class of `X i` is the image of the corresponding generator of `J`.
  simpa [MvPolynomial.idealOfVars] using
    (Ideal.mem_map_of_mem
      (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
      (Ideal.subset_span (Set.mem_range_self i) :
        MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R))

/-- Helper for Lemma 10.139.4: the variable error already lands in the image of the variable ideal
`J`, which is the descent condition needed for the correction map. -/
theorem truncation_selfmap_variable_error_mem_idealOfVars_image {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  have hmem :
      α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) ∈
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n) := by
    -- First identify the transition kernel with the image of `J ^ n`.
    rw [← factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
    exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα i
  -- Since `n > 0`, the previous power `J ^ n` lies inside `J`.
  exact
    (Ideal.map_mono
      (show J ^ n ≤ J from by
        simpa [pow_one] using (Ideal.pow_le_pow_right (I := J) hn)))
      hmem

/-- Helper for Lemma 10.139.4: the corrected image of each variable still lies in the image of the
variable ideal `J`. -/
theorem truncation_selfmap_correction_variable_mem_idealOfVars_image
    {d : ℕ} {n : ℕ} (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  -- Both the variable class and its correction error lie in the image of `J`.
  exact sub_mem
    (truncation_variable_class_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) i)
    (truncation_selfmap_variable_error_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα i)

/-- Helper for Lemma 10.139.4: the variable-wise correction evaluation sends the variable ideal
into the visible image of `J` in `P / J^(n + 1)`. -/
theorem truncation_selfmap_correction_map_idealOfVars_le_visible {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    Ideal.map
        (MvPolynomial.aeval
          (fun i : Fin d ↦
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                (MvPolynomial.X i) -
              (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)) -
                Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)))).toRingHom
        (MvPolynomial.idealOfVars (Fin d) R) ≤
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        (MvPolynomial.idealOfVars (Fin d) R) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let F :
      MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))
  -- Route correction: the descent proof should pass through ideal containment `map F J ≤ map mk J`
  -- rather than a large direct `aeval` computation on `J^(n + 1)`.
  rw [Ideal.map_le_iff_le_comap]
  change Ideal.span (Set.range MvPolynomial.X) ≤
    Ideal.comap F.toRingHom (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J)
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change F (MvPolynomial.X i) ∈ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J
  simpa [F, J] using
    truncation_selfmap_correction_variable_mem_idealOfVars_image
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα i

/-- Helper for Lemma 10.139.4: the variable-wise correction evaluation sends `J^(n + 1)` to zero,
so it descends to an endomorphism of `P / J^(n + 1)`. -/
theorem truncation_selfmap_correction_descends {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    ∀ x : MvPolynomial (Fin d) R, x ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →
      MvPolynomial.aeval
          (fun i : Fin d ↦
            Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                (MvPolynomial.X i) -
              (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i)) -
                Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
                  (MvPolynomial.X i))) x = 0 := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let F :
      MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))
  have hJ :
      Ideal.map F.toRingHom J ≤
        Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J := by
    -- First place every corrected variable image back inside the visible image of `J`.
    simpa [F, J] using
      truncation_selfmap_correction_map_idealOfVars_le_visible
        (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
  have hpow :
      Ideal.map F.toRingHom (J ^ (n + 1)) ≤
        (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    -- Raising the containment to the `(n + 1)`st power follows from `map_pow`.
    simpa [Ideal.map_pow] using Ideal.pow_right_mono hJ (n + 1)
  have hvisible_zero :
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) = ⊥ := by
    -- The visible ideal to the `(n + 1)`st power is the image of `J^(n + 1)`, hence zero.
    calc
      (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) =
          Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ (n + 1)) := by
            rw [Ideal.map_pow]
      _ = ⊥ := Ideal.map_quotient_self _
  intro x hx
  have hx_map : F x ∈ (Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) J) ^ (n + 1) := by
    exact hpow (Ideal.mem_map_of_mem F.toRingHom hx)
  have hx_zero :
      F x ∈
        (⊥ :
          Ideal (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))) := by
    simpa [hvisible_zero] using hx_map
  simpa [F, J] using hx_zero

/-- Helper for Lemma 10.139.4: correcting each variable by its error defines the quotient
endomorphism suggested by the source proof. -/
noncomputable def truncation_selfmap_correction {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) :=
  Ideal.Quotient.liftₐ ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (MvPolynomial.aeval fun i : Fin d ↦
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)))
    (truncation_selfmap_correction_descends
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα)

/-- Helper for Lemma 10.139.4: the correction endomorphism still reduces to the identity modulo
`J^n`. -/
theorem truncation_selfmap_correction_factorPow_comp {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp
        (truncation_selfmap_correction
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα) =
      Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let q :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →ₐ[R]
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))
  -- Route correction: the correction map is determined by its variable values, and modulo `J^n`
  -- the source error term on each variable already lies in the transition kernel.
  have hq :
      q.comp
          (truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα) =
        q := by
    apply Ideal.Quotient.algHom_ext (R₁ := R)
      (A := MvPolynomial (Fin d) R) (I := J ^ (n + 1))
      (S := MvPolynomial (Fin d) R ⧸ J ^ n)
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    let err :
        MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
      α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)
    have hcorr :
        truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
            (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) =
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) - err := by
      -- Evaluate the quotient lift on the generator `X i`.
      have hcomp :
          (truncation_selfmap_correction
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα).comp
              (Ideal.Quotient.mkₐ R (J ^ (n + 1))) =
            MvPolynomial.aeval fun j : Fin d ↦
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
                (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
                  Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) := by
        simpa [truncation_selfmap_correction] using
          (Ideal.Quotient.liftₐ_comp (J ^ (n + 1))
            (MvPolynomial.aeval fun j : Fin d ↦
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
                (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
                  Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)))
            (truncation_selfmap_correction_descends
              (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα))
      simpa [err] using AlgHom.congr_fun hcomp (MvPolynomial.X i)
    have herr_zero : q err = 0 := by
      -- The source hypothesis `q ∘ α = q` says exactly that the variable error dies modulo `J^n`.
      exact RingHom.mem_ker.mp <|
        truncation_selfmap_variable_error_mem_kernel
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) α hα
          i
    -- After reducing modulo `J^n`, only the original variable class remains.
    calc
      q
          (truncation_selfmap_correction
            (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
            (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i))) =
        q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i) - err) := by
          rw [hcorr]
      _ = q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) - q err := by
          simp [q]
      _ = q (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X i)) := by
          simp [herr_zero]
  exact congrArg AlgHom.toRingHom hq

/-- Helper for Lemma 10.139.4: once the variable errors lie in the transition kernel, their
pairwise products vanish because that kernel is square-zero. -/
theorem truncation_selfmap_variable_error_mul_eq_zero {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i j : Fin d) :
    (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i)) *
      (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X j)) -
        Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X j)) = 0 := by
  -- Each variable error lies in the square-zero transition kernel, so their product vanishes.
  apply truncation_transition_kernel_mul_eq_zero (R := R) (S := S) (σ := σ) (hσ := hσ)
    (d := d) (n := n) hn
  · exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα i
  · exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) α hα j

/-- Helper for Lemma 10.139.4: any endomorphism reducing to the identity modulo `J^n` differs
from the identity by an element of the transition piece `J^n / J^(n + 1)` on every input. -/
theorem truncation_selfmap_sub_mem_transition_image {d : ℕ} {n : ℕ}
    (γ : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hγ :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp γ =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (y : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) :
    γ y - y ∈
      Ideal.map
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)))
        ((MvPolynomial.idealOfVars (Fin d) R) ^ n) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let q :
      MvPolynomial (Fin d) R ⧸ J ^ (n + 1) →+*
        MvPolynomial (Fin d) R ⧸ J ^ n :=
    Ideal.Quotient.factorPow J (Nat.le_succ n)
  -- The hypothesis `q ∘ γ = q` says exactly that `γ y - y` lands in the transition kernel.
  rw [← factorPow_kernel_eq_map_pow (R := R) (S := S) (σ := σ) (hσ := hσ)
    (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
  rw [RingHom.mem_ker]
  have hy := congrArg (fun β ↦ β y) hγ
  calc
    q (γ y - y) = q (γ y) - q y := by simp [q]
    _ = q y - q y := by simpa [q, AlgHom.comp_apply] using congrArg (fun z ↦ z - q y) hy
    _ = 0 := sub_self _

/-- Helper for Lemma 10.139.4: substituting `Xᵢ + eᵢ` with all `eᵢ ∈ J^n` changes every
polynomial by an element of `J^n`. -/
theorem idealOfVars_aeval_X_add_highPower_sub_mem {d n : ℕ}
    (e : Fin d → MvPolynomial (Fin d) R)
    (he : ∀ i, e i ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    (p : MvPolynomial (Fin d) R) :
    (MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i) p - p ∈
      (MvPolynomial.idealOfVars (Fin d) R) ^ n := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let H : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i
  change H p - p ∈ J ^ n
  -- Induct over polynomial construction; multiplying by a variable only adds terms carrying one
  -- high-order error, hence still in `J^n`.
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [H]
  | add p q hp hq =>
      have hcalc : H (p + q) - (p + q) = (H p - p) + (H q - q) := by
        simp [map_add]
        abel
      rw [hcalc]
      exact Ideal.add_mem (J ^ n) hp hq
  | mul_X p i hp =>
      have hcalc : H (p * MvPolynomial.X i) - p * MvPolynomial.X i =
          (H p - p) * (MvPolynomial.X i + e i) + p * e i := by
        simp [H, map_mul]
        ring
      rw [hcalc]
      exact Ideal.add_mem (J ^ n)
        (Ideal.mul_mem_right _ _ hp)
        (Ideal.mul_mem_left _ _ (he i))

/-- Helper for Lemma 10.139.4: substituting `Xᵢ + eᵢ`, with high-order errors, preserves the
variable ideal. -/
theorem idealOfVars_aeval_X_add_highPower_map_le {d n : ℕ}
    (hn : 0 < n)
    (e : Fin d → MvPolynomial (Fin d) R)
    (he : ∀ i, e i ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ n) :
    Ideal.map (MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i).toRingHom
        (MvPolynomial.idealOfVars (Fin d) R) ≤
      MvPolynomial.idealOfVars (Fin d) R := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let H : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i
  rw [Ideal.map_le_iff_le_comap]
  change MvPolynomial.idealOfVars (Fin d) R ≤ Ideal.comap H.toRingHom J
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change H (MvPolynomial.X i) ∈ J
  have hXi : MvPolynomial.X i ∈ J := by
    simpa [J, MvPolynomial.idealOfVars] using
      (Ideal.subset_span (Set.mem_range_self i) :
        MvPolynomial.X i ∈ MvPolynomial.idealOfVars (Fin d) R)
  have heiJ : e i ∈ J := by
    exact (show J ^ n ≤ J from by
      simpa [pow_one] using (Ideal.pow_le_pow_right (I := J) hn)) (he i)
  -- The substituted variable is the original variable plus a term still lying in `J`.
  simpa [H, J] using Ideal.add_mem J hXi heiJ

/-- Helper for Lemma 10.139.4: on `J^m`, substituting `Xᵢ + eᵢ` with `eᵢ ∈ J^n` changes the
polynomial by an element of `J^(n + m - 1)`. -/
theorem idealOfVars_aeval_X_add_highPower_sub_mem_pow {d n m : ℕ}
    (hn : 2 ≤ n)
    (e : Fin d → MvPolynomial (Fin d) R)
    (he : ∀ i, e i ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ n)
    {p : MvPolynomial (Fin d) R}
    (hp : p ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ m) :
    (MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i) p - p ∈
      (MvPolynomial.idealOfVars (Fin d) R) ^ (n + m - 1) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let H : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hH_all : ∀ p : MvPolynomial (Fin d) R, H p - p ∈ J ^ n := by
    intro p
    exact idealOfVars_aeval_X_add_highPower_sub_mem
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) e he p
  have hHmap : Ideal.map H.toRingHom J ≤ J :=
    idealOfVars_aeval_X_add_highPower_map_le
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn0 e he
  have hHpow_mem :
      ∀ {i : ℕ} {x : MvPolynomial (Fin d) R}, x ∈ J ^ i → H x ∈ J ^ i := by
    intro i x hx
    have hxmap : H x ∈ Ideal.map H.toRingHom (J ^ i) := Ideal.mem_map_of_mem H.toRingHom hx
    have hpow : Ideal.map H.toRingHom (J ^ i) ≤ J ^ i := by
      simpa [Ideal.map_pow] using Ideal.pow_right_mono hHmap i
    exact hpow hxmap
  change H p - p ∈ J ^ (n + m - 1)
  change p ∈ J ^ m at hp
  -- Induct through the power filtration. Multiplication by one more element of `J` raises the
  -- error order by one, while the global `J^n` error estimate handles the new left factor.
  refine Submodule.pow_induction_on_left' (M := J)
    (C := fun i x hx ↦ H x - x ∈ J ^ (n + i - 1))
    (fun r ↦ ?_)
    (fun x y i hx hy hxprop hyprop ↦ ?_)
    (fun a ha i x hx hxprop ↦ ?_)
    hp
  · exact (Ideal.pow_le_pow_right (I := J) (show n - 1 ≤ n by omega)) (hH_all r)
  · change H (x + y) - (x + y) ∈ J ^ (n + i - 1)
    have hcalc : H (x + y) - (x + y) = (H x - x) + (H y - y) := by
      simp [map_add]
      abel
    rw [hcalc]
    exact Ideal.add_mem (J ^ (n + i - 1)) hxprop hyprop
  · change H (a * x) - a * x ∈ J ^ (n + (i + 1) - 1)
    have hcalc : H (a * x) - a * x = (H a - a) * H x + a * (H x - x) := by
      simp [map_mul]
      ring
    rw [hcalc]
    apply Ideal.add_mem
    · have hleft : (H a - a) * H x ∈ J ^ n * J ^ i :=
        Ideal.mul_mem_mul (hH_all a) (hHpow_mem hx)
      have hexp : n + (i + 1) - 1 = n + i := by omega
      rw [hexp, pow_add]
      exact hleft
    · have hright : a * (H x - x) ∈ J ^ 1 * J ^ (n + i - 1) := by
        simpa [pow_one] using Ideal.mul_mem_mul ha hxprop
      have hexp : n + (i + 1) - 1 = 1 + (n + i - 1) := by omega
      rw [hexp, pow_add]
      exact hright

/-- Helper for Lemma 10.139.4: an endomorphism of `P / J^(n+1)` that is the identity modulo
`J^n` fixes the transition image `J^n / J^(n+1)` pointwise. -/
theorem truncation_selfmap_mk_eq_mk_of_mem_idealOfVars_pow {d n : ℕ}
    (hn : 2 ≤ n)
    (γ : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hγ :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp γ =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    {p : MvPolynomial (Fin d) R}
    (hp : p ∈ (MvPolynomial.idealOfVars (Fin d) R) ^ n) :
    γ (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) p) =
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) p := by
  classical
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let mk : MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.mk (J ^ (n + 1))
  have herr_mem : ∀ i : Fin d,
      γ (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i) ∈ Ideal.map mk (J ^ n) := by
    intro i
    rw [← factorPow_kernel_eq_map_pow
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
    exact truncation_selfmap_variable_error_mem_kernel
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) γ hγ i
  have herr_exists : ∀ i : Fin d, ∃ e : MvPolynomial (Fin d) R,
      e ∈ J ^ n ∧ mk e = γ (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i) := by
    intro i
    exact (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp (herr_mem i)
  choose e heJ heq using herr_exists
  let H : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval fun i : Fin d ↦ MvPolynomial.X i + e i
  have hγH : γ.comp (Ideal.Quotient.mkₐ R (J ^ (n + 1))) =
      (Ideal.Quotient.mkₐ R (J ^ (n + 1))).comp H := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    have herr : mk (e i) = γ (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i) := heq i
    -- The chosen representative `eᵢ` records the variable error of `γ`.
    calc
      (γ.comp (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) (MvPolynomial.X i) =
          γ (mk (MvPolynomial.X i)) := by rfl
      _ = mk (MvPolynomial.X i) + mk (e i) := by
        rw [herr]
        abel
      _ = ((Ideal.Quotient.mkₐ R (J ^ (n + 1))).comp H) (MvPolynomial.X i) := by
        simp [H, mk]
  have hsub : H p - p ∈ J ^ (n + n - 1) := by
    exact idealOfVars_aeval_X_add_highPower_sub_mem_pow
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) (m := n) hn e heJ hp
  have hsub' : H p - p ∈ J ^ (n + 1) := by
    exact (Ideal.pow_le_pow_right (I := J) (show n + 1 ≤ n + n - 1 by omega)) hsub
  -- Repackage `γ` as the high-order substitution and then kill the resulting
  -- `J^(n+1)` difference in the quotient.
  calc
    γ (mk p) = ((γ.comp (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) p) := by rfl
    _ = (((Ideal.Quotient.mkₐ R (J ^ (n + 1))).comp H) p) := by rw [hγH]
    _ = mk (H p) := by rfl
    _ = mk p := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hsub'

/-- Helper for Lemma 10.139.4: the correction endomorphism sends each variable to the variable
minus its transition error. -/
theorem truncation_selfmap_correction_variable {d : ℕ} {n : ℕ}
    (hn : 0 < n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n))
    (i : Fin d) :
    truncation_selfmap_correction
        (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα
        (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
          (MvPolynomial.X i)) =
      Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) (MvPolynomial.X i) -
        (α (Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) -
          Ideal.Quotient.mk ((MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
            (MvPolynomial.X i)) := by
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  -- Evaluate the quotient lift defining the correction on the generator `Xᵢ`.
  have hcomp :
      (truncation_selfmap_correction
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα).comp
          (Ideal.Quotient.mkₐ R (J ^ (n + 1))) =
        MvPolynomial.aeval fun j : Fin d ↦
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
            (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) := by
    simpa [truncation_selfmap_correction] using
      (Ideal.Quotient.liftₐ_comp (J ^ (n + 1))
        (MvPolynomial.aeval fun j : Fin d ↦
          Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j) -
            (α (Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)) -
              Ideal.Quotient.mk (J ^ (n + 1)) (MvPolynomial.X j)))
        (truncation_selfmap_correction_descends
          (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α hα))
  simpa [J] using AlgHom.congr_fun hcomp (MvPolynomial.X i)

/-- Helper for Lemma 10.139.4: the variable-wise correction is a two-sided inverse to any
self-map of `P / J^(n+1)` that reduces to the identity modulo `J^n`. -/
theorem truncation_selfmap_correction_comp_self {d : ℕ} {n : ℕ}
    (hn : 2 ≤ n)
    (α : MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1) →ₐ[R]
      MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1))
    (hα :
      (Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)).comp α =
        Ideal.Quotient.factorPow (MvPolynomial.idealOfVars (Fin d) R) (Nat.le_succ n)) :
    (truncation_selfmap_correction
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα).comp α =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) ∧
      α.comp
        (truncation_selfmap_correction
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα) =
        AlgHom.id R
          (MvPolynomial (Fin d) R ⧸ (MvPolynomial.idealOfVars (Fin d) R) ^ (n + 1)) := by
  classical
  let J : Ideal (MvPolynomial (Fin d) R) := MvPolynomial.idealOfVars (Fin d) R
  let mk : MvPolynomial (Fin d) R →+* MvPolynomial (Fin d) R ⧸ J ^ (n + 1) :=
    Ideal.Quotient.mk (J ^ (n + 1))
  let β :=
    truncation_selfmap_correction
      (R := R) (S := S) (σ := σ) (hσ := hσ)
      (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα
  have hβ :
      (Ideal.Quotient.factorPow J (Nat.le_succ n)).comp β =
        Ideal.Quotient.factorPow J (Nat.le_succ n) := by
    simpa [J, β] using
      truncation_selfmap_correction_factorPow_comp
        (R := R) (S := S) (σ := σ) (hσ := hσ)
        (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα
  have hfixα :
      ∀ {p : MvPolynomial (Fin d) R}, p ∈ J ^ n → α (mk p) = mk p := by
    intro p hp
    exact truncation_selfmap_mk_eq_mk_of_mem_idealOfVars_pow
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn α
      (by simpa [J] using hα) (by simpa [J] using hp)
  have hfixβ :
      ∀ {p : MvPolynomial (Fin d) R}, p ∈ J ^ n → β (mk p) = mk p := by
    intro p hp
    exact truncation_selfmap_mk_eq_mk_of_mem_idealOfVars_pow
      (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) hn β
      (by simpa [J] using hβ) (by simpa [J] using hp)
  have herr_exists : ∀ i : Fin d, ∃ e : MvPolynomial (Fin d) R,
      e ∈ J ^ n ∧ mk e = α (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i) := by
    intro i
    have herr_mem :
        α (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i) ∈ Ideal.map mk (J ^ n) := by
      rw [← factorPow_kernel_eq_map_pow
        (R := R) (S := S) (σ := σ) (hσ := hσ)
        (A := MvPolynomial (Fin d) R) (K := J) (n := n)]
      exact truncation_selfmap_variable_error_mem_kernel
        (R := R) (S := S) (σ := σ) (hσ := hσ) (d := d) (n := n) α
        (by simpa [J] using hα) i
    exact (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp herr_mem
  constructor
  · apply Ideal.Quotient.algHom_ext (R₁ := R)
      (A := MvPolynomial (Fin d) R) (I := J ^ (n + 1))
      (S := MvPolynomial (Fin d) R ⧸ J ^ (n + 1))
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases herr_exists i with ⟨e, heJ, heq⟩
    have hβX :
        β (mk (MvPolynomial.X i)) =
          mk (MvPolynomial.X i) - (α (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i)) := by
      simpa [J, β, mk] using
        truncation_selfmap_correction_variable
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα i
    have hβerr : β (mk e) = mk e := hfixβ heJ
    have hαX : α (mk (MvPolynomial.X i)) = mk (MvPolynomial.X i) + mk e := by
      rw [heq]
      abel
    have hβX' : β (mk (MvPolynomial.X i)) = mk (MvPolynomial.X i) - mk e := by
      rw [hβX, ← heq]
    -- On variables, `β` subtracts the transition error of `α`, and `β` fixes that error.
    calc
      ((β.comp α).comp (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) (MvPolynomial.X i) =
          β (mk (MvPolynomial.X i) + mk e) := by
            exact congrArg β hαX
      _ = β (mk (MvPolynomial.X i)) + β (mk e) := by simp
      _ = (mk (MvPolynomial.X i) - mk e) + mk e := by
            rw [hβX', hβerr]
      _ = ((AlgHom.id R (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))).comp
          (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) (MvPolynomial.X i) := by
            abel
  · apply Ideal.Quotient.algHom_ext (R₁ := R)
      (A := MvPolynomial (Fin d) R) (I := J ^ (n + 1))
      (S := MvPolynomial (Fin d) R ⧸ J ^ (n + 1))
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases herr_exists i with ⟨e, heJ, heq⟩
    have hβX :
        β (mk (MvPolynomial.X i)) =
          mk (MvPolynomial.X i) - (α (mk (MvPolynomial.X i)) - mk (MvPolynomial.X i)) := by
      simpa [J, β, mk] using
        truncation_selfmap_correction_variable
          (R := R) (S := S) (σ := σ) (hσ := hσ)
          (d := d) (n := n) (lt_of_lt_of_le (by norm_num) hn) α hα i
    have hαerr : α (mk e) = mk e := hfixα heJ
    have hβX' : β (mk (MvPolynomial.X i)) = mk (MvPolynomial.X i) - mk e := by
      rw [hβX, ← heq]
    have hαX : α (mk (MvPolynomial.X i)) = mk (MvPolynomial.X i) + mk e := by
      rw [heq]
      abel
    -- The other composite is symmetric: `α` fixes the transition error subtracted by `β`.
    calc
      ((α.comp β).comp (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) (MvPolynomial.X i) =
          α (mk (MvPolynomial.X i) - mk e) := by
            exact congrArg α hβX'
      _ = α (mk (MvPolynomial.X i)) - α (mk e) := by simp
      _ = (mk (MvPolynomial.X i) + mk e) - mk e := by
            rw [hαX, hαerr]
      _ = ((AlgHom.id R (MvPolynomial (Fin d) R ⧸ J ^ (n + 1))).comp
          (Ideal.Quotient.mkₐ R (J ^ (n + 1)))) (MvPolynomial.X i) := by
            abel

end SmoothSection

end
