import stacks_proof.stacks_project.Chap10.Lemma_10_70_3.BaseChangeMap

open HomogeneousLocalization
open IsLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.70.3: the mapped power ideal `Ideal.map (algebraMap R S) (I ^ n)` is the
ideal spanned by the literal images of elements of `I ^ n`. -/
private theorem mappedIdealPower_eq_span_range
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (n : ℕ) :
    Ideal.map (algebraMap R S) (I ^ n) =
      Ideal.span (Set.range fun y : ↥(I ^ n) ↦ algebraMap R S y.1) := by
  -- Rewrite the mapped ideal as the span of the literal images of elements of `I ^ n`.
  calc
    Ideal.map (algebraMap R S) (I ^ n) =
        Ideal.map (algebraMap R S) (Ideal.span (((I ^ n : Ideal R) : Set R))) := by
          rw [Ideal.span_eq]
    _ = Ideal.span ((algebraMap R S) '' (((I ^ n : Ideal R) : Set R))) := by
          rw [Ideal.map_span]
    _ = Ideal.span (Set.range fun y : ↥(I ^ n) ↦ algebraMap R S y.1) := by
          congr 1
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨y, hy⟩, rfl⟩
          · rintro ⟨y, rfl⟩
            exact ⟨y, y.2, rfl⟩

/-- Helper for Lemma 10.70.3: the mapped ideal `Ideal.map (algebraMap R S) I` is spanned by
the literal images of elements of `I`. -/
private theorem mappedIdeal_eq_span_range
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) :
    Ideal.map (algebraMap R S) I =
      Ideal.span (Set.range fun y : I ↦ algebraMap R S y.1) := by
  calc
    Ideal.map (algebraMap R S) I =
        Ideal.map (algebraMap R S) (Ideal.span (((I : Ideal R) : Set R))) := by
          rw [Ideal.span_eq]
    _ = Ideal.span ((algebraMap R S) '' (((I : Ideal R) : Set R))) := by
          rw [Ideal.map_span]
    _ = Ideal.span (Set.range fun y : I ↦ algebraMap R S y.1) := by
          congr 1
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨y, hy⟩, rfl⟩
          · rintro ⟨y, rfl⟩
            exact ⟨y, y.2, rfl⟩

/-- Helper for Lemma 10.70.3: every element of the extended ideal `IS` comes from a tensor in
`S ⊗[R] I` under the multiplication map. -/
theorem mappedIdealElement_exists_tensorLift
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R)
    (x : Ideal.map (algebraMap R S) I) :
    ∃ t : S ⊗[R] I,
      (Algebra.TensorProduct.rid R R S).toLinearMap
          ((LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R))) t) = x.1 := by
  have hxSpan :
      (x : S) ∈ Ideal.span (Set.range fun y : I ↦ algebraMap R S y.1) := by
    have hxMap : (x : S) ∈ Ideal.map (algebraMap R S) I := x.2
    simpa [mappedIdeal_eq_span_range (S := S) I] using hxMap
  rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hxSpan with ⟨c, hc⟩
  refine ⟨Finset.sum c.support fun y ↦ c y ⊗ₜ[R] y, ?_⟩
  -- Expand the chosen finite tensor expression and collapse it back to the span presentation of
  -- `x`.
  calc
    (Algebra.TensorProduct.rid R R S).toLinearMap
        ((LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R)))
          (Finset.sum c.support fun y ↦ c y ⊗ₜ[R] y)) =
      ∑ y ∈ c.support,
        (Algebra.TensorProduct.rid R R S).toLinearMap
          ((LinearMap.lTensor S (Submodule.subtype (I.restrictScalars R))) (c y ⊗ₜ[R] y)) := by
            simp
    _ = ∑ y ∈ c.support, c y * algebraMap R S (y : R) := by
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          simp [LinearMap.lTensor_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
            Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
    _ = x.1 := by
          simpa [Finsupp.sum] using hc

set_option maxHeartbeats 1000000 in
/-- Helper for Lemma 10.70.3: every target basic fraction `x / b` comes from the tensor
comparison map. -/
theorem affineBlowupChart_target_basicFraction_surjective
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ x : J, ∃ z : S ⊗[R] R[I / a],
      tensorToAffineBlowupAlgebra S I a z = affineBlowupChartBasicFraction J b x := by
  intro J b x
  have hxSpan :
      (x : S) ∈ Ideal.span (Set.range fun y : I ↦ algebraMap R S y.1) := by
    have hxMap : (x : S) ∈ Ideal.map (algebraMap R S) I := by
      simpa [J] using x.2
    simpa [mappedIdeal_eq_span_range (S := S) I] using hxMap
  rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hxSpan with ⟨c, hc⟩
  let z : S ⊗[R] R[I / a] :=
    ∑ y ∈ c.support, c y ⊗ₜ[R] affineBlowupChartBasicFraction I a y
  have hmul :
      tensorToAffineBlowupAlgebra S I a z *
          algebraMap S S[J / b] b.1 =
        algebraMap S S[J / b] x.1 := by
    have hyFrac (y : I) :
        affineBlowupChartBasicFraction J b (mappedIdealElement I y) *
            algebraMap S S[J / b] b.1 =
          algebraMap S S[J / b] (algebraMap R S y.1) := by
      simpa [mappedIdealElement] using
        affineBlowupChart_basicFraction_mul_parameter J b (mappedIdealElement I y)
    -- Push the finite tensor expansion through the comparison map and clear the common
    -- denominator `b`.
    calc
      tensorToAffineBlowupAlgebra S I a z * algebraMap S S[J / b] b.1 =
        (∑ y ∈ c.support,
            algebraMap S S[J / b] (c y) *
              affineBlowupChartBasicFraction J b (mappedIdealElement I y)) *
          algebraMap S S[J / b] b.1 := by
            simp [z, J, b, map_sum, tensorToAffineBlowupAlgebra_tmul_basicFraction]
      _ =
        ∑ y ∈ c.support,
          (algebraMap S S[J / b] (c y) *
              affineBlowupChartBasicFraction J b (mappedIdealElement I y)) *
            algebraMap S S[J / b] b.1 := by
              rw [Finset.sum_mul]
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y) *
            (affineBlowupChartBasicFraction J b (mappedIdealElement I y) *
              algebraMap S S[J / b] b.1) := by
              refine Finset.sum_congr rfl fun y hy ↦ by
                ring
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y) *
            algebraMap S S[J / b] (algebraMap R S y.1) := by
              refine Finset.sum_congr rfl fun y hy ↦ ?_
              simpa using congrArg (fun q : S[J / b] ↦ algebraMap S S[J / b] (c y) * q) (hyFrac y)
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y * algebraMap R S y.1) := by
            refine Finset.sum_congr rfl fun y hy ↦ by
              rw [← map_mul]
      _ = algebraMap S S[J / b] (∑ y ∈ c.support, c y * algebraMap R S y.1) := by
            rw [map_sum]
      _ = algebraMap S S[J / b] x.1 := by
            simpa [Finsupp.sum] using congrArg (algebraMap S S[J / b]) hc
  have htarget :
      affineBlowupChartBasicFraction J b x * algebraMap S S[J / b] b.1 =
        algebraMap S S[J / b] x.1 := by
    simpa using affineBlowupChart_basicFraction_mul_parameter J b x
  have hreg :
      IsRegular (algebraMap S S[J / b] b.1) :=
    affineBlowupChart_isRegular J b
  have hzero :
      algebraMap S S[J / b] b.1 *
          (tensorToAffineBlowupAlgebra S I a z - affineBlowupChartBasicFraction J b x) = 0 := by
    have hmul' :
        algebraMap S S[J / b] b.1 * tensorToAffineBlowupAlgebra S I a z =
          algebraMap S S[J / b] b.1 * affineBlowupChartBasicFraction J b x := by
      calc
        algebraMap S S[J / b] b.1 * tensorToAffineBlowupAlgebra S I a z =
            tensorToAffineBlowupAlgebra S I a z * algebraMap S S[J / b] b.1 := by
              rw [mul_comm]
        _ = affineBlowupChartBasicFraction J b x * algebraMap S S[J / b] b.1 := hmul.trans htarget.symm
        _ = algebraMap S S[J / b] b.1 * affineBlowupChartBasicFraction J b x := by
              rw [mul_comm]
    rw [mul_sub]
    exact sub_eq_zero.mpr hmul'
  refine ⟨z, ?_⟩
  exact sub_eq_zero.mp (hreg.1 (by simpa using hzero))

set_option maxHeartbeats 1000000 in
/-- Helper for Lemma 10.70.3: every normalized target fraction `y / b^n` with `y ∈ J ^ n` comes
from the tensor comparison map. -/
theorem affineBlowupChart_target_powerFraction_surjective
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) (n : ℕ) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    ∀ x : ↥(J ^ n), ∃ z : S ⊗[R] R[I / a],
      tensorToAffineBlowupAlgebra S I a z = affineBlowupChartPowerFraction J b n x := by
  intro J b x
  let yJ : ↥(I ^ n) → ↥(J ^ n) := fun y ↦
    ⟨algebraMap R S y.1, by
      simpa [J, Ideal.map_pow] using
        (Ideal.mem_map_of_mem (algebraMap R S) y.2 :
          algebraMap R S y.1 ∈ Ideal.map (algebraMap R S) (I ^ n))⟩
  have hxSpan :
      (x : S) ∈ Ideal.span (Set.range fun y : ↥(I ^ n) ↦ algebraMap R S y.1) := by
    have hxMap : (x : S) ∈ Ideal.map (algebraMap R S) (I ^ n) := by
      simpa [J, Ideal.map_pow] using x.2
    simpa [mappedIdealPower_eq_span_range (S := S) I n] using hxMap
  rcases Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hxSpan with ⟨c, hc⟩
  let z : S ⊗[R] R[I / a] :=
    ∑ y ∈ c.support, c y ⊗ₜ[R] affineBlowupChartPowerFraction I a n y
  refine ⟨z, ?_⟩
  have hmul :
      tensorToAffineBlowupAlgebra S I a z *
          (algebraMap S S[J / b] b.1) ^ n =
        algebraMap S S[J / b] x.1 := by
    -- Push the finite tensor expansion through the comparison map and then clear the common
    -- denominator `b^n`.
    calc
      tensorToAffineBlowupAlgebra S I a z *
          (algebraMap S S[J / b] b.1) ^ n =
        (∑ y ∈ c.support,
            algebraMap S S[J / b] (c y) *
              affineBlowupChartPowerFraction J b n (yJ y)) *
          (algebraMap S S[J / b] b.1) ^ n := by
            simp [z, J, b, yJ, map_sum, tensorToAffineBlowupAlgebra_tmul_powerFraction]
      _ =
        ∑ y ∈ c.support,
          (algebraMap S S[J / b] (c y) *
              affineBlowupChartPowerFraction J b n (yJ y)) *
            (algebraMap S S[J / b] b.1) ^ n := by
              rw [Finset.sum_mul]
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y) *
            (affineBlowupChartPowerFraction J b n (yJ y) *
              (algebraMap S S[J / b] b.1) ^ n) := by
              refine Finset.sum_congr rfl fun y hy ↦ by
                ring
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y) *
            algebraMap S S[J / b] (algebraMap R S y.1) := by
              refine Finset.sum_congr rfl fun y hy ↦ ?_
              simpa [yJ] using
                congrArg
                  (fun q : S[J / b] ↦ algebraMap S S[J / b] (c y) * q)
                  (affineBlowupChart_fraction_mul_parameter_pow J b n (yJ y))
      _ =
        ∑ y ∈ c.support,
          algebraMap S S[J / b] (c y * algebraMap R S y.1) := by
            refine Finset.sum_congr rfl fun y hy ↦ by
              rw [← map_mul]
      _ = algebraMap S S[J / b] (∑ y ∈ c.support, c y * algebraMap R S y.1) := by
            rw [map_sum]
      _ = algebraMap S S[J / b] x.1 := by
            simpa [Finsupp.sum] using congrArg (algebraMap S S[J / b]) hc
  have htarget :
      affineBlowupChartPowerFraction J b n x *
          (algebraMap S S[J / b] b.1) ^ n =
        algebraMap S S[J / b] x.1 := by
    simpa using affineBlowupChart_fraction_mul_parameter_pow J b n x
  have hreg :
      IsRegular (algebraMap S S[J / b] b.1) :=
    affineBlowupChart_isRegular J b
  have hzero :
      (algebraMap S S[J / b] b.1) ^ n *
          (tensorToAffineBlowupAlgebra S I a z - affineBlowupChartPowerFraction J b n x) = 0 := by
    have hmul' :
        (algebraMap S S[J / b] b.1) ^ n * tensorToAffineBlowupAlgebra S I a z =
          (algebraMap S S[J / b] b.1) ^ n * affineBlowupChartPowerFraction J b n x := by
      calc
        (algebraMap S S[J / b] b.1) ^ n * tensorToAffineBlowupAlgebra S I a z =
            tensorToAffineBlowupAlgebra S I a z * (algebraMap S S[J / b] b.1) ^ n := by
              rw [mul_comm]
        _ = affineBlowupChartPowerFraction J b n x * (algebraMap S S[J / b] b.1) ^ n :=
              hmul.trans htarget.symm
        _ = (algebraMap S S[J / b] b.1) ^ n * affineBlowupChartPowerFraction J b n x := by
              rw [mul_comm]
    rw [mul_sub]
    exact sub_eq_zero.mpr hmul'
  exact sub_eq_zero.mp ((IsRegular.pow n hreg).1 (by simpa using hzero))

/-- Helper for Lemma 10.70.3: every source element annihilated by a power of the distinguished
tensor parameter already lies in the kernel of the base-change map. -/
theorem exists_pow_mul_eq_zero_mem_ker_tensorToAffineBlowupAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    (∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0) →
      x ∈ RingHom.ker (tensorToAffineBlowupAlgebra S I a).toRingHom := by
  intro hx
  rcases hx with ⟨n, hn⟩
  -- Map the annihilating relation to the target chart, where the image of `a` is regular.
  rw [RingHom.mem_ker]
  have hzero :
      (algebraMap S
          (affineBlowupChart
            (Ideal.map (algebraMap R S) I) (mappedIdealElement I a))
          (algebraMap R S a.1)) ^ n *
        tensorToAffineBlowupAlgebra S I a x = 0 := by
    -- The tensor comparison map is multiplicative and sends the distinguished tensor parameter to
    -- the distinguished target parameter.
    have hparam :
        (tensorToAffineBlowupAlgebra S I a).toRingHom
            (algebraMap R (S ⊗[R] R[I / a]) a.1) =
          algebraMap S
            (affineBlowupChart
              (Ideal.map (algebraMap R S) I) (mappedIdealElement I a))
            (algebraMap R S a.1) := by
      simpa using tensorToAffineBlowupAlgebra_parameter_image S I a
    have hmap :
        (tensorToAffineBlowupAlgebra S I a).toRingHom
            ((algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x) =
          (tensorToAffineBlowupAlgebra S I a).toRingHom 0 := by
      exact congrArg (tensorToAffineBlowupAlgebra S I a).toRingHom hn
    rw [map_mul, map_pow, hparam] at hmap
    simpa using hmap
  have hreg :
      IsRegular
        (algebraMap S
          (affineBlowupChart
            (Ideal.map (algebraMap R S) I) (mappedIdealElement I a))
          (algebraMap R S a.1)) :=
    affineBlowupChart_isRegular
      (Ideal.map (algebraMap R S) I) (mappedIdealElement I a)
  apply (IsRegular.pow n hreg).1
  simpa using hzero

end
