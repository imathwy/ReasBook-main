import Mathlib
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_15_1 (from Chap10) -/
/- Lemma 10.15.1: the textbook implication
`I * J ≤ 𝔭 → I ≤ 𝔭 ∨ J ≤ 𝔭` for a prime ideal `𝔭` is the forward direction of the
canonical theorem `Ideal.IsPrime.mul_le`, which states the equivalent condition
`I * J ≤ 𝔭 ↔ I ≤ 𝔭 ∨ J ≤ 𝔭`. -/
recall Ideal.IsPrime.mul_le

/-! ### Lemma_10_15_2_Prime_avoidance (from Chap10) -/
/- Lemma 10.15.2 (Prime avoidance): the canonical prime avoidance theorem states that if an ideal
is contained in the union of finitely many ideals and all but at most two of them are prime, then
it is contained in one of those ideals. Applied contrapositively to `J`, this yields an element of
`J` lying outside every `I_i`. -/
recall Ideal.subset_union_prime

/-! ### Lemma_10_15_3 (from Chap10) -/
universe u v

open scoped Pointwise

private theorem vadd_ideal_subset_iff {R : Type u} [CommRing R] {x : R} {I J : Ideal R} :
    (x +ᵥ (I : Set R)) ⊆ (J : Set R) ↔ x ∈ J ∧ I ≤ J := by
  constructor
  · intro h
    have hxJ : x ∈ J := h <| Set.mem_vadd_set.2 ⟨0, I.zero_mem, by simp⟩
    refine ⟨hxJ, ?_⟩
    intro y hyI
    have hxy : x + y ∈ J := by
      refine h <| Set.mem_vadd_set.2 ⟨y, hyI, ?_⟩
      simp [vadd_eq_add]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using J.sub_mem hxy hxJ
  · rintro ⟨hxJ, hIJ⟩ z hz
    rcases Set.mem_vadd_set.1 hz with ⟨y, hyI, rfl⟩
    simpa [vadd_eq_add] using J.add_mem hxJ (hIJ hyI)

/-- Lemma 10.15.3 (Tag 0EHL): if each prime ideal in a finite family does not contain the coset
`x + I`, then one translate `x + y` with `y ∈ I` avoids all of them simultaneously. -/
-- Proof sketch: argue by induction on the number of prime ideals, as in the textbook proof.
-- Remove redundant inclusions among the primes, separate those that contain `x` from those that do
-- not, choose `y ∈ I` outside the next prime, and multiply it by an element lying in the earlier
-- primes but not in that next prime. This lets one enlarge the set of avoided primes step by step.
theorem exists_mem_ideal_add_not_mem_finset_primes
    {R : Type u} [CommRing R] {ι : Type v} {x : R} {I : Ideal R} (s : Finset ι)
    (p : ι → Ideal R) (hp : ∀ i ∈ s, (p i).IsPrime)
    (hx : ∀ i ∈ s, ¬ (x +ᵥ (I : Set R)) ⊆ (p i : Set R)) :
    ∃ y ∈ I, ∀ i ∈ s, x + y ∉ p i := by
  classical
  have havoid : ∀ i ∈ s, x ∈ p i → ¬ I ≤ p i := by
    intro i hi hxi hIp
    exact hx i hi <| (vadd_ideal_subset_iff.2 ⟨hxi, hIp⟩)
  let t : Finset ι := s.filter fun i ↦ ∀ j ∈ s, p i ≤ p j → p j ≤ p i
  let a : Finset ι := t.filter fun i ↦ x ∈ p i
  let b : Finset ι := t.filter fun i ↦ x ∉ p i
  let P : Ideal R := ∏ j ∈ b, p j
  let J : Ideal R := I * P
  have ht_mem : ∀ {i : ι}, i ∈ t → i ∈ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have ht_max : ∀ {i : ι}, i ∈ t → ∀ j ∈ s, p i ≤ p j → p j ≤ p i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hs_le_maximal : ∀ i ∈ s, ∃ j ∈ t, p i ≤ p j := by
    intro i hi
    let si : Finset ι := s.filter fun j ↦ p i ≤ p j
    have hsi : si.Nonempty := ⟨i, by simp [si, hi]⟩
    obtain ⟨j, hj⟩ := si.exists_maximalFor p hsi
    refine ⟨j, ?_, (Finset.mem_filter.mp hj.1).2⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp hj.1).1
    · intro k hk hjk
      exact hj.2 (Finset.mem_filter.mpr ⟨hk, (Finset.mem_filter.mp hj.1).2.trans hjk⟩) hjk
  have hJ_not_le : ∀ i ∈ a, ¬ J ≤ p i := by
    intro i hi
    have hit : i ∈ t := (Finset.mem_filter.mp hi).1
    have his : i ∈ s := ht_mem hit
    have hxi : x ∈ p i := (Finset.mem_filter.mp hi).2
    obtain ⟨y, hyI, hy_not_mem⟩ : ∃ y ∈ I, y ∉ p i := by
      simpa [SetLike.le_def, Set.not_subset] using havoid i his hxi
    have hwitness : ∃ w ∈ P, w ∉ p i := by
      have hz : ∀ j ∈ b, ∃ z ∈ p j, z ∉ p i := by
        intro j hj
        have hjt : j ∈ t := (Finset.mem_filter.mp hj).1
        have hjs : j ∈ s := ht_mem hjt
        have hxj : x ∉ p j := (Finset.mem_filter.mp hj).2
        have hnot_le : ¬ p j ≤ p i := by
          intro hji
          have hij : p i ≤ p j := ht_max hjt i his hji
          exact hxj (hij hxi)
        simpa [SetLike.le_def, Set.not_subset] using hnot_le
      let z : ι → R := fun j ↦ if hj : j ∈ b then Classical.choose (hz j hj) else 1
      have hz_mem : ∀ j ∈ b, z j ∈ p j := by
        intro j hj
        simp [z, hj, (Classical.choose_spec (hz j hj)).1]
      have hz_not : ∀ j ∈ b, z j ∉ p i := by
        intro j hj
        simp [z, hj, (Classical.choose_spec (hz j hj)).2]
      refine ⟨∏ j ∈ b, z j, ?_, ?_⟩
      · dsimp [P]
        exact Ideal.prod_mem_prod fun j hj ↦ hz_mem j hj
      · have hpi : (p i).IsPrime := hp i his
        letI : (p i).IsPrime := hpi
        intro hprod
        have hprod' : ∏ j ∈ b, z j ∈ p i := by
          simpa using hprod
        have hprod_iff : (∏ j ∈ b, z j ∈ p i) ↔ ∃ j ∈ b, z j ∈ p i := by
          simpa using
            (show (∏ j ∈ b, z j ∈ p i) ↔ ∃ j ∈ b, z j ∈ p i from Ideal.IsPrime.prod_mem_iff)
        rcases hprod_iff.1 hprod' with ⟨j, hj, hzj⟩
        exact hz_not j hj (by simpa using hzj)
    obtain ⟨w, hwP, hw_not_mem⟩ := hwitness
    intro hJle
    have hmul_mem : y * w ∈ J := by
      dsimp [J]
      exact Ideal.mul_mem_mul hyI hwP
    have hmul : y * w ∈ p i := hJle hmul_mem
    have hpi : (p i).IsPrime := hp i his
    letI : (p i).IsPrime := hpi
    exact hpi.mem_or_mem hmul |>.elim hy_not_mem hw_not_mem
  have hy_exists : ∃ y ∈ J, ∀ i ∈ a, y ∉ p i := by
    by_cases ha : a.Nonempty
    · obtain ⟨i₀, hi₀⟩ := ha
      have hnot_subset : ¬ ((J : Set R) ⊆ ⋃ i ∈ (↑a : Set ι), p i) := by
        intro hsubset
        obtain ⟨i, hi, hle⟩ :=
          (Ideal.subset_union_prime i₀ i₀
            fun i hi _ _ ↦ hp i (ht_mem ((Finset.mem_filter.mp hi).1))).mp hsubset
        exact hJ_not_le i hi hle
      obtain ⟨y, hyJ, hyunion⟩ := Set.not_subset.mp hnot_subset
      refine ⟨y, hyJ, ?_⟩
      intro i hi hyi
      exact hyunion <| Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hyi⟩⟩
    · refine ⟨0, J.zero_mem, ?_⟩
      intro i hi
      exact (ha ⟨i, hi⟩).elim
  obtain ⟨y, hyJ, hyavoid⟩ := hy_exists
  have hyI : y ∈ I := by
    have hJI : J ≤ I := by
      dsimp [J]
      exact Ideal.mul_le_right
    exact hJI hyJ
  refine ⟨y, hyI, ?_⟩
  intro i hi
  obtain ⟨j, hjt, hij⟩ := hs_le_maximal i hi
  have hxy_not_j : x + y ∉ p j := by
    by_cases hxj : x ∈ p j
    · have hja : j ∈ a := Finset.mem_filter.mpr ⟨hjt, hxj⟩
      intro hxy
      have hyj : y ∈ p j := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (p j).sub_mem hxy hxj
      exact hyavoid j hja hyj
    · have hjb : j ∈ b := Finset.mem_filter.mpr ⟨hjt, hxj⟩
      have hyP : y ∈ P := by
        have hJP : J ≤ P := by
          dsimp [J]
          exact Ideal.mul_le_left
        exact hJP hyJ
      have hybInf : y ∈ b.inf p := (show P ≤ b.inf p by
          dsimp [P]
          exact Ideal.prod_le_inf) hyP
      have hyj : y ∈ p j := (show b.inf p ≤ p j from Finset.inf_le hjb) hybInf
      intro hxy
      have hxpj : x ∈ p j := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (p j).sub_mem hxy hyj
      exact hxj hxpj
  intro hxy
  exact hxy_not_j (hij hxy)

/-! ### Lemma_10_15_4_Chinese_remainder (from Chap10) -/
open Function
open Ideal
open scoped BigOperators

universe u

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Fintype ι] (I : ι → Ideal R)

/-- Lemma 10.15.4 (Chinese remainder) (1): for pairwise comaximal ideals `I_i`, the product
`∏ i, I i` equals their intersection `⨅ i, I i`. -/
-- Proof sketch: this is `Ideal.prod_eq_iInf_of_pairwise_isCoprime` on `Finset.univ`.
theorem chinese_remainder_prod_eq_iInf
    (hI : Pairwise (IsCoprime on I)) :
    ∏ i, I i = ⨅ i, I i := by
  classical
  simpa using
    (show ∏ i ∈ (Finset.univ : Finset ι), I i = ⨅ i ∈ (Finset.univ : Finset ι), I i from
      prod_eq_iInf_of_pairwise_isCoprime
        (by
          intro i _ j _ hij
          exact hI hij))

/-- Lemma 10.15.4 (Chinese remainder) (2): for pairwise comaximal ideals `I_i`, the quotient by
their product is canonically isomorphic to the product of the quotients `R ⧸ I i`. -/
noncomputable def chinese_remainder_quotient_pi_ring_equiv
    (hI : Pairwise (IsCoprime on I)) :
    R ⧸ ∏ i, I i ≃+* ∀ i, R ⧸ I i :=
  (quotEquivOfEq (chinese_remainder_prod_eq_iInf I hI)).trans
    (quotientInfRingEquivPiQuotient I hI)

/-- The canonical Chinese remainder equivalence sends the class of `x` to the tuple of its classes
in the quotients `R ⧸ I i`. -/
@[simp]
theorem chinese_remainder_quotient_pi_ring_equiv_apply_mk
    (hI : Pairwise (IsCoprime on I)) (x : R) :
    chinese_remainder_quotient_pi_ring_equiv I hI (Ideal.Quotient.mk (∏ i, I i) x) =
      fun i ↦ Ideal.Quotient.mk (I i) x := by
  simpa [chinese_remainder_quotient_pi_ring_equiv, quotientInfRingEquivPiQuotient] using
    quotientInfToPiQuotient_mk I x

end

/-! ### Lemma_10_15_5 (from Chap10) -/
universe u

open Matrix

section

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- Helper for Lemma 10.15.5: the adjugate of a chosen `m × m` row submatrix yields a left witness
for its determinant. -/
lemma adjugate_projection_mul_eq_row_minor_smul_one
    (A : Matrix (Fin n) (Fin m) R) (e : Fin m ↪ Fin n) :
    ((A.submatrix e id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e id)) * A =
      (A.submatrix e id).det • (1 : Matrix (Fin m) (Fin m) R) := by
  -- First project `A` to the chosen rows, then use the adjugate identity on that square matrix.
  rw [Matrix.mul_assoc]
  have hproj :
      ((1 : Matrix (Fin n) (Fin n) R).submatrix e id) * A = A.submatrix e id := by
    simpa using Matrix.one_submatrix_mul e (Equiv.refl (Fin n)) A
  rw [hproj]
  simpa using Matrix.adjugate_mul (A.submatrix e id)

/-- Helper for Lemma 10.15.5: every maximal minor of `A` gives an explicit matrix `B` with
`B * A = det(minor) • 1`. -/
lemma exists_mul_eq_smul_one_of_maximal_minor
    (A : Matrix (Fin n) (Fin m) R) (e₁ : Fin m ↪ Fin n) (e₂ : Fin m ↪ Fin m) :
    ∃ B : Matrix (Fin m) (Fin n) R, B * A = (A.submatrix e₁ e₂).det • 1 := by
  let σ : Fin m ≃ Fin m :=
    Equiv.ofBijective e₂ ((Finite.injective_iff_bijective (f := e₂)).mp e₂.injective)
  let B : Matrix (Fin m) (Fin n) R :=
    (↑(Equiv.Perm.sign σ) : R) •
      ((A.submatrix e₁ id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e₁ id))
  refine ⟨B, ?_⟩
  have hdet :
      (A.submatrix e₁ e₂).det =
        (↑(Equiv.Perm.sign σ) : R) * (A.submatrix e₁ id).det := by
    -- Permuting the columns of the square submatrix changes the determinant by the sign.
    simpa [σ, Matrix.submatrix_submatrix, Function.comp_id]
      using Matrix.det_permute' σ (A.submatrix e₁ id)
  -- Scale the standard adjugate witness by the same sign appearing in the determinant comparison.
  calc
    B * A =
        (↑(Equiv.Perm.sign σ) : R) •
          (((A.submatrix e₁ id).adjugate * ((1 : Matrix (Fin n) (Fin n) R).submatrix e₁ id)) * A) := by
      simp [B, Matrix.smul_mul]
    _ =
        (↑(Equiv.Perm.sign σ) : R) •
          ((A.submatrix e₁ id).det • (1 : Matrix (Fin m) (Fin m) R)) := by
      rw [adjugate_projection_mul_eq_row_minor_smul_one]
    _ = ((↑(Equiv.Perm.sign σ) : R) * (A.submatrix e₁ id).det) • (1 : Matrix (Fin m) (Fin m) R) := by
      rw [smul_smul]
    _ = (A.submatrix e₁ e₂).det • (1 : Matrix (Fin m) (Fin m) R) := by
      rw [hdet]

/-- Helper for Lemma 10.15.5: when `m ≤ n`, extend `B` by zero rows so that
`minorIdeal_mul_left_le` applies to `det (B * A)`. -/
lemma det_mul_mem_minorIdeal_of_le
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (h : m ≤ n) :
    Matrix.det (B * A) ∈ minorIdeal m A := by
  let C : Matrix (Fin n) (Fin n) R :=
    fun i j ↦ if hi : (i : ℕ) < m then B ⟨i, hi⟩ j else 0
  have hsub : C.submatrix (Fin.castLEEmb h) (Equiv.refl (Fin n)) = B := by
    -- On the first `m` rows, the zero-row extension is exactly `B`.
    ext i j
    simp [C]
  have htop : (C * A).submatrix (Fin.castLEEmb h) (Function.Embedding.refl (Fin m)) = B * A := by
    -- Restricting the product back to those rows recovers the square matrix `B * A`.
    rw [Matrix.submatrix_mul C A (Fin.castLEEmb h) (Equiv.refl (Fin n))
      (Function.Embedding.refl (Fin m))
      (Equiv.refl (Fin n)).bijective]
    rw [hsub]
    have hA : A.submatrix (Equiv.refl (Fin n)) (Function.Embedding.refl (Fin m)) = A := by
      ext i j
      rfl
    rw [hA]
  have hdet : Matrix.det (B * A) ∈ minorIdeal m (C * A) := by
    -- This determinant is one of the `m × m` minors of the extended product.
    have hminor :=
      Matrix.det_submatrix_mem_minorIdeal m (C * A) (Fin.castLEEmb h) (Function.Embedding.refl _)
    rw [htop] at hminor
    exact hminor
  -- Left multiplication by the square extension `C` cannot enlarge the `m`-minor ideal.
  exact Matrix.minorIdeal_mul_left_le m C A hdet

/-- Lemma 10.15.5: if `f ∈ I_(m)(A)` for an `n × m` matrix `A`, then some `m × n` matrix `B`
satisfies `B * A = f • 1`. When `m ≤ n`, these are exactly the maximal minors; when `m > n`,
`I_(m)(A) = ⊥`, so no separate inequality hypothesis is needed. -/
-- Proof sketch: write `f` as a finite `R`-linear combination of `m × m` minors. For each chosen
-- row submatrix use its adjugate matrix, extend it back to an `m × n` matrix, and sum these
-- contributions to obtain a matrix `B` whose product with `A` is `f • 1`.
theorem exists_mul_eq_smul_one_of_mem_minorIdeal
    (A : Matrix (Fin n) (Fin m) R) {f : R} (hf : f ∈ minorIdeal m A) :
    ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1 := by
  let P : R → Prop := fun g ↦ ∃ B : Matrix (Fin m) (Fin n) R, B * A = g • 1
  have hgen :
      ∀ x ∈ Set.range (fun p : (Fin m ↪ Fin n) × (Fin m ↪ Fin m) ↦ (A.submatrix p.1 p.2).det),
        P x := by
    intro x hx
    rcases hx with ⟨⟨e₁, e₂⟩, rfl⟩
    -- Each generator is handled by the explicit adjugate construction above.
    exact exists_mul_eq_smul_one_of_maximal_minor A e₁ e₂
  have hzero : P 0 := by
    -- The zero scalar is realized by the zero matrix.
    refine ⟨0, ?_⟩
    simp
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    rcases hx with ⟨Bx, hBx⟩
    rcases hy with ⟨By, hBy⟩
    refine ⟨Bx + By, ?_⟩
    -- Adding witnesses adds the resulting scalar matrices.
    rw [Matrix.add_mul, hBx, hBy, add_smul]
  have hsmul : ∀ a x, P x → P (a * x) := by
    intro a x hx
    rcases hx with ⟨B, hB⟩
    refine ⟨a • B, ?_⟩
    -- Scaling the witness scales the scalar on the right-hand side.
    rw [Matrix.smul_mul, hB, smul_smul]
  unfold Matrix.minorIdeal at hf
  -- The admissible scalars form a submodule containing the generating set of `minorIdeal m A`.
  exact Submodule.span_induction (p := fun x _ ↦ P x) hgen hzero
    (fun x y _ _ hx hy ↦ hadd x y hx hy) (fun a x _ hx ↦ hsmul a x hx) hf

/-- Matrix-level form of Lemma 10.15.5: a left inverse up to the scalar `f` forces `f ^ m` to lie
in the maximal-minor ideal of `A`. In the Stacks Project wording this is membership in the ideal
generated by the `m × m` row minors, which agrees with `I_(m)(A)`. This is the atomic
determinantal statement from which the existential formulation follows immediately. -/
-- Route correction: `minorIdeal_mul_left_le` only applies directly after extending a rectangular
-- left factor to a square one. When `n < m`, the clean route is instead the rectangular
-- characteristic-polynomial identity `charpoly_mul_comm_of_le`.
theorem pow_mem_minorIdeal_of_mul_eq_smul_one
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (B : Matrix (Fin m) (Fin n) R) (hBA : B * A = f • 1) :
    f ^ m ∈ minorIdeal m A := by
  by_cases hmn : m ≤ n
  · have hdet : Matrix.det (B * A) ∈ minorIdeal m A :=
      det_mul_mem_minorIdeal_of_le A B hmn
    -- For a scalar matrix, the determinant is exactly the required power `f ^ m`.
    simpa [hBA, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] using hdet
  · have hlt : n < m := Nat.lt_of_not_ge hmn
    have hchar :
        (B * A).charpoly = Polynomial.X ^ (m - n) * (A * B).charpoly := by
      simpa [Fintype.card_fin] using
        Matrix.charpoly_mul_comm_of_le B A (by simpa [Fintype.card_fin] using hlt.le)
    have hcoeff : (B * A).charpoly.coeff 0 = 0 := by
      -- A positive power of `X` kills the constant coefficient.
      rw [hchar, Polynomial.coeff_X_pow_mul']
      simp [Nat.not_le_of_gt (Nat.sub_pos_of_lt hlt)]
    have hdetZero : Matrix.det (B * A) = 0 := by
      -- The determinant is the constant term of the characteristic polynomial up to sign.
      rw [Matrix.det_eq_sign_charpoly_coeff, hcoeff]
      simp
    have hpowZero : f ^ m = 0 := by
      -- Rewrite the determinant of `B * A` using the scalar-matrix hypothesis.
      simpa [hBA, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] using hdetZero
    simpa [hpowZero] using (show 0 ∈ minorIdeal m A from Ideal.zero_mem _)

/-- Existential companion to `pow_mem_minorIdeal_of_mul_eq_smul_one`. -/
theorem pow_mem_minorIdeal_of_exists_mul_eq_smul_one
    (A : Matrix (Fin n) (Fin m) R) {f : R}
    (hBA : ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1) :
    f ^ m ∈ minorIdeal m A := by
  rcases hBA with ⟨B, hB⟩
  -- Unpack the witness and apply the matrix-level statement.
  exact pow_mem_minorIdeal_of_mul_eq_smul_one A B hB

end

/-! ### Lemma_10_15_6 (from Chap10) -/
open Matrix

variable {R : Type _} [CommRing R] {m l : ℕ}

/-- The lower block of `A * A.toRows₁.adjugate` is given entrywise by determinants of the
row-replacement matrices obtained from the top square block. In the Stacks Project formulation,
this is the determinant of the corresponding maximal minor, up to sign. -/
theorem lowerBlock_mul_adjugate_apply (A : Matrix (Fin m ⊕ Fin l) (Fin m) R)
    (i : Fin l) (j : Fin m) :
    (A.toRows₂ * A.toRows₁.adjugate) i j = (A.toRows₁.updateRow j (A.toRows₂ i)).det := by
  calc
    (A.toRows₂ * A.toRows₁.adjugate) i j = (A.toRows₂ i ᵥ* A.toRows₁.adjugate) j := by
      simp [vecMul, mul_apply, dotProduct]
    _ = (A.toRows₁ᵀ.adjugate *ᵥ A.toRows₂ i) j := by
      rw [← adjugate_transpose, ← mulVec_transpose]
    _ = (A.toRows₁ᵀ.cramer (A.toRows₂ i)) j := by
      simpa using (congr_fun (cramer_eq_adjugate_mulVec A.toRows₁ᵀ (A.toRows₂ i)).symm j)
    _ = (A.toRows₁.updateRow j (A.toRows₂ i)).det := by
      simpa using cramer_transpose_apply A.toRows₁ (A.toRows₂ i) j

/-- Lemma 10.15.6: multiplying a block matrix by the adjugate of its top square block yields a
row-partitioned matrix whose top block is `det(A₁) • 1`; the companion theorem
`lowerBlock_mul_adjugate_apply` identifies the lower block entries with the row-replacement
determinants from the textbook statement. -/
theorem mul_adjugate_top_block_eq_fromRows (A : Matrix (Fin m ⊕ Fin l) (Fin m) R) :
    A * A.toRows₁.adjugate =
      fromRows (A.toRows₁.det • 1)
        (A.toRows₂ * A.toRows₁.adjugate) := by
  simpa [fromRows_toRows, A.toRows₁.mul_adjugate] using
    (fromRows_mul A.toRows₁ A.toRows₂ A.toRows₁.adjugate)

/-! ### Lemma_10_15_7 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R] [Nontrivial R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.15.7: if an `R`-module `M` is generated by fewer than `n` elements, encoded
canonically as `(⊤ : Submodule R M).spanRank < n`, then every `R`-linear map
`R^{\oplus n} → M` has nonzero kernel. This is the source-facing bridge from the
generation hypothesis to the owner `rank`/`spanRank` comparison API. -/
theorem linearMap_ker_ne_bot_of_spanRank_lt
    {n : ℕ} (hgen : (⊤ : Submodule R M).spanRank < n) (f : (Fin n → R) →ₗ[R] M) :
    LinearMap.ker f ≠ ⊥ := by
  intro hker
  have hrank : n ≤ Module.rank R M :=
    Module.le_rank_iff_exists_linearMap.2 ⟨f, LinearMap.ker_eq_bot.mp hker⟩
  exact (not_lt_of_ge (hrank.trans Submodule.rank_le_spanRank) hgen).elim

end

/-! ### Lemma_10_15_8 (from Chap10) -/
universe u

section

variable {R : Type u} [Semiring R] [InvariantBasisNumber R]

/- Lemma 10.15.8, `core/canonical` layer for the invariant-basis-number owner abstraction:
over a semiring with invariant basis number, if `R^{\oplus n}` and `R^{\oplus m}` are isomorphic
as `R`-modules, then `n = m`.

This is exactly the canonical derived theorem `eq_of_fin_equiv` for the owner class
`InvariantBasisNumber`; it specializes to the source-text case of a nonzero commutative ring by
typeclass inference. -/
recall eq_of_fin_equiv

end
