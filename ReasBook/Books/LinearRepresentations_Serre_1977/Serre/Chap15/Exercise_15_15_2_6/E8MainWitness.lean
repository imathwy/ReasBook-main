import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonModTwoRank

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

namespace E8ReflectionMainWitness

local notation "W8" => Fin 8 → ℤ

/-- The simple reflection matrix attached to the `i`-th simple root of the Bourbaki `E₈`
Cartan matrix, in the simple-root basis. -/
def reflectionMatrix (i : Fin 8) : Matrix (Fin 8) (Fin 8) ℤ :=
  1 - Matrix.of fun r c => if r = i then CartanMatrix.E₈ c i else 0

/-- The integral simple reflection attached to the `i`-th simple root of type `E₈`. -/
def simpleReflection (i : Fin 8) : Module.End ℤ W8 :=
  Matrix.toLin' (reflectionMatrix i)

/-- The standard basis vector in the simple-root lattice. -/
def basisVector (i : Fin 8) : W8 :=
  Pi.basisFun ℤ (Fin 8) i

/-- The simple reflection formula on the simple-root basis. -/
theorem simpleReflection_basisVector (i c : Fin 8) :
    simpleReflection i (basisVector c) =
      basisVector c - CartanMatrix.E₈ c i • basisVector i := by
  ext r
  simp [simpleReflection, basisVector, reflectionMatrix, Matrix.toLin'_apply]
  by_cases h : r = i
  · subst r
    simp
  · simp [h]

/-- An explicit integer inverse of the Bourbaki `E₈` Cartan matrix. -/
def cartanInverse : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
     5, 8, 10, 15, 12, 9, 6, 3;
     7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6;
     8, 12, 16, 24, 20, 15, 10, 5;
     6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3;
     2, 3, 4, 6, 5, 4, 3, 2]

/-- The displayed inverse is a left inverse of the `E₈` Cartan matrix. -/
theorem cartanInverse_mul_cartan : cartanInverse * CartanMatrix.E₈ = 1 := by
  decide

/-- The Cartan functional attached to the `i`-th simple reflection. -/
def cartanFunctional (i : Fin 8) (x : W8) : ℤ :=
  ∑ c, CartanMatrix.E₈ c i * x c

/-- The simple reflection formula on an arbitrary vector of the simple-root lattice. -/
theorem simpleReflection_apply (i : Fin 8) (x : W8) :
    simpleReflection i x = x - cartanFunctional i x • basisVector i := by
  ext r
  simp [simpleReflection, reflectionMatrix, cartanFunctional, basisVector,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  by_cases h : r = i
  · subst r
    simp
  · simp [h]

/-- The displacement under a simple reflection is a multiple of the reflected simple root. -/
theorem simpleReflection_apply_sub (i : Fin 8) (x : W8) :
    simpleReflection i x - x = -(cartanFunctional i x) • basisVector i := by
  rw [simpleReflection_apply]
  ext r
  simp [basisVector]

/-- The inverse Cartan matrix recovers the coordinates from the Cartan functionals. -/
theorem cartanInverse_cartanFunctional_coord (x : W8) (r : Fin 8) :
    ∑ i, cartanInverse r i * cartanFunctional i x = x r := by
  calc
    ∑ i, cartanInverse r i * cartanFunctional i x =
        (cartanInverse.mulVec (CartanMatrix.E₈.transpose.mulVec x)) r := by
          simp [cartanFunctional, Matrix.mulVec, dotProduct]
    _ = ((cartanInverse * CartanMatrix.E₈.transpose).mulVec x) r := by
          rw [Matrix.mulVec_mulVec]
    _ = ((cartanInverse * CartanMatrix.E₈).mulVec x) r := by
          rw [CartanMatrix.E₈_transpose]
    _ = x r := by
          rw [cartanInverse_mul_cartan]
          simp

/-- If every Cartan functional is divisible by `p`, then every coordinate is divisible by `p`. -/
theorem dvd_coord_of_forall_dvd_cartanFunctional
    (p : ℕ) [Fact p.Prime] (x : W8)
    (h : ∀ i : Fin 8, (p : ℤ) ∣ cartanFunctional i x) :
    ∀ r : Fin 8, (p : ℤ) ∣ x r := by
  intro r
  rw [← cartanInverse_cartanFunctional_coord x r]
  refine Finset.dvd_sum ?_
  intro i _
  exact dvd_mul_of_dvd_right (h i) (cartanInverse r i)

/-- If all coordinates are divisible by `p`, then the vector lies in `pE`. -/
theorem mem_prime_mul_of_forall_dvd_coord
    (p : ℕ) [Fact p.Prime] (x : W8)
    (h : ∀ r : Fin 8, (p : ℤ) ∣ x r) :
    x ∈ (Representation.primeIdeal p • (⊤ : Submodule ℤ W8)) := by
  rw [Representation.primeIdeal, Submodule.ideal_span_singleton_smul]
  let y : W8 := fun r => Classical.choose (h r)
  refine ⟨y, by simp, ?_⟩
  ext r
  have hr := Classical.choose_spec (h r)
  simpa [y, Pi.smul_apply] using hr.symm

/-- Bézout in the form needed to invert a nonzero scalar modulo a prime. -/
theorem exists_int_bezout_of_prime_not_dvd
    (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    ∃ u v : ℤ, u * a + v * (p : ℤ) = 1 := by
  have hgcd : Int.gcd a (p : ℤ) = 1 := by
    have hdvd_p_int : (Int.gcd a (p : ℤ) : ℤ) ∣ (p : ℤ) :=
      Int.gcd_dvd_right a (p : ℤ)
    have hdvd_p_nat : Int.gcd a (p : ℤ) ∣ p :=
      Int.natCast_dvd_natCast.1 hdvd_p_int
    have hcases := (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd_p_nat
    rcases hcases with h1 | hp
    · exact h1
    · exfalso
      apply ha
      have hgdvda : (Int.gcd a (p : ℤ) : ℤ) ∣ a :=
        Int.gcd_dvd_left a (p : ℤ)
      rw [hp] at hgdvda
      exact hgdvda
  refine ⟨a.gcdA (p : ℤ), a.gcdB (p : ℤ), ?_⟩
  have hbez := Int.gcd_eq_gcd_ab a (p : ℤ)
  rw [hgcd] at hbez
  ring_nf at hbez ⊢
  exact hbez.symm

/-- Row `0` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row0 :
    ∀ j : Fin 8, (reflectionMatrix (0 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (0 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `1` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row1 :
    ∀ j : Fin 8, (reflectionMatrix (1 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (1 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `2` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row2 :
    ∀ j : Fin 8, (reflectionMatrix (2 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (2 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `3` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row3 :
    ∀ j : Fin 8, (reflectionMatrix (3 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (3 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `4` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row4 :
    ∀ j : Fin 8, (reflectionMatrix (4 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (4 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `5` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row5 :
    ∀ j : Fin 8, (reflectionMatrix (5 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (5 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `6` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row6 :
    ∀ j : Fin 8, (reflectionMatrix (6 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (6 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- Row `7` of the concrete `E₈` Coxeter relations. -/
theorem reflectionMatrix_relations_row7 :
    ∀ j : Fin 8, (reflectionMatrix (7 : Fin 8) * reflectionMatrix j) ^
        CoxeterMatrix.E₈ (7 : Fin 8) j = 1 := by
  intro j
  fin_cases j <;> decide

/-- The concrete `E₈` reflection matrices satisfy the Coxeter relations. -/
theorem reflectionMatrix_relations :
    ∀ i j : Fin 8, (reflectionMatrix i * reflectionMatrix j) ^ CoxeterMatrix.E₈ i j = 1 := by
  intro i
  fin_cases i
  · exact reflectionMatrix_relations_row0
  · exact reflectionMatrix_relations_row1
  · exact reflectionMatrix_relations_row2
  · exact reflectionMatrix_relations_row3
  · exact reflectionMatrix_relations_row4
  · exact reflectionMatrix_relations_row5
  · exact reflectionMatrix_relations_row6
  · exact reflectionMatrix_relations_row7

/-- The simple integral reflections are liftable from the Coxeter presentation of type `E₈`. -/
theorem simpleReflection_liftable : CoxeterMatrix.E₈.IsLiftable simpleReflection := by
  intro i j
  change ((Matrix.toLin' (reflectionMatrix i) * Matrix.toLin' (reflectionMatrix j)) ^
    CoxeterMatrix.E₈ i j = 1)
  rw [Module.End.mul_eq_comp]
  rw [← Matrix.toLin'_mul]
  rw [← Matrix.toLin'_pow]
  rw [reflectionMatrix_relations]
  exact Matrix.toLin'_one

/-- The integral reflection representation of the Coxeter group of type `E₈`, on the
simple-root lattice. -/
noncomputable def representation :
    Representation ℤ CoxeterMatrix.E₈.Group W8 :=
  CoxeterMatrix.E₈.toCoxeterSystem.lift ⟨simpleReflection, simpleReflection_liftable⟩

/-- On Coxeter simple generators, the representation is the corresponding simple reflection. -/
theorem representation_apply_simple (i : Fin 8) :
    representation (CoxeterMatrix.E₈.simple i) = simpleReflection i := by
  simpa [representation] using
    (CoxeterSystem.lift_apply_simple
      (cs := CoxeterMatrix.E₈.toCoxeterSystem)
      (f := simpleReflection) simpleReflection_liftable i)

/-- A nonzero prime-reduction class has a nonzero Cartan functional modulo `p`. -/
theorem exists_not_dvd_cartanFunctional_of_class_ne_zero
    (p : ℕ) [Fact p.Prime] {x : W8}
    (hx : prime_reduction_class (ρ := representation) p x ≠ 0) :
    ∃ i : Fin 8, ¬ (p : ℤ) ∣ cartanFunctional i x := by
  by_contra h
  push Not at h
  have hcoord : ∀ r : Fin 8, (p : ℤ) ∣ x r :=
    dvd_coord_of_forall_dvd_cartanFunctional p x h
  have hxmem : x ∈ (Representation.primeIdeal p • (⊤ : Submodule ℤ W8)) :=
    mem_prime_mul_of_forall_dvd_coord p x hcoord
  exact hx ((prime_reduction_class_eq_zero_iff_mem_prime_mul
    (ρ := representation) p x).2 hxmem)

/-- The canonical class of a `p`-multiple is zero in the prime reduction. -/
theorem prime_reduction_class_prime_smul
    (p : ℕ) [Fact p.Prime] (x : W8) :
    prime_reduction_class (ρ := representation) p ((p : ℤ) • x) = 0 := by
  apply (prime_reduction_class_eq_zero_iff_mem_prime_mul
    (ρ := representation) p ((p : ℤ) • x)).2
  apply mem_prime_mul_of_forall_dvd_coord
  intro r
  exact ⟨x r, by simp [Pi.smul_apply]⟩

/-- The canonical class map as an additive homomorphism. -/
def primeReductionClassAddHom (p : ℕ) [Fact p.Prime] :
    W8 →+ (representation.primeStableLattice p).reduction where
  toFun := prime_reduction_class (ρ := representation) p
  map_zero' := by
    apply (prime_reduction_class_eq_zero_iff_mem_prime_mul
      (ρ := representation) p (0 : W8)).2
    apply mem_prime_mul_of_forall_dvd_coord
    intro r
    exact dvd_zero (p : ℤ)
  map_add' := by
    intro x y
    exact prime_reduction_class_add (ρ := representation) p x y

/-- The canonical class map respects integer scalar multiplication. -/
theorem prime_reduction_class_zsmul_current
    (p : ℕ) [Fact p.Prime] (m : ℤ) (x : W8) :
    prime_reduction_class (ρ := representation) p (m • x) =
      m • prime_reduction_class (ρ := representation) p x := by
  simpa [primeReductionClassAddHom] using
    (primeReductionClassAddHom p).map_zsmul x m

/-- The canonical class map respects subtraction. -/
theorem prime_reduction_class_sub_current
    (p : ℕ) [Fact p.Prime] (x y : W8) :
    prime_reduction_class (ρ := representation) p (x - y) =
      prime_reduction_class (ρ := representation) p x -
        prime_reduction_class (ρ := representation) p y := by
  rw [sub_eq_add_neg, prime_reduction_class_add, prime_reduction_class_neg]
  rfl

/-- Residue-field scalar multiplication on an integral reduction class has an integral
representative. -/
theorem prime_reduction_class_residue_smul_exists_int_current
    (p : ℕ) [Fact p.Prime]
    (c : IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
    (x : W8) :
    ∃ m : ℤ,
      c • prime_reduction_class (ρ := representation) p x =
        prime_reduction_class (ρ := representation) p (m • x) := by
  let e :
      ℤ ⧸ Representation.primeIdeal p ≃+*
        Localization.AtPrime (Representation.primeIdeal p) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p)) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal (Representation.primeIdeal p)
      (Localization.AtPrime (Representation.primeIdeal p))
  obtain ⟨m, hm⟩ := Ideal.Quotient.mk_surjective (I := Representation.primeIdeal p) (e.symm c)
  refine ⟨m, ?_⟩
  let z : (representation.primeStableLattice p).toSubmodule :=
    ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1,
      Submodule.mem_top⟩
  have hc :
      c =
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
          (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
    calc
      c = e (e.symm c) := by simp [e]
      _ = e (Ideal.Quotient.mk (Representation.primeIdeal p) m) := by rw [hm]
      _ =
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
            (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m) := by
            simp [e]
  have hsmul :=
    (StableLattice.reduction_smul_mk
      (L := representation.primeStableLattice p)
      (a := algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) m)
      (y := z))
  change c • (Submodule.Quotient.mk z : (representation.primeStableLattice p).reduction) =
    prime_reduction_class (ρ := representation) p (m • x)
  rw [hc]
  refine hsmul.trans ?_
  unfold prime_reduction_class
  congr 1

/-- Subrepresentations are closed under the underlying integer additive action. -/
theorem Subrepresentation.zsmul_mem
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    {z : (representation.primeStableLattice p).reduction}
    (hz : z ∈ U) (m : ℤ) :
    m • z ∈ U := by
  simpa using U.toSubmodule.toAddSubgroup.zsmul_mem hz m

/-- Membership in `pE` forces every coordinate to be divisible by `p`. -/
theorem dvd_coord_of_mem_prime_mul
    (p : ℕ) [Fact p.Prime] {x : W8}
    (hx : x ∈ (Representation.primeIdeal p • (⊤ : Submodule ℤ W8))) :
    ∀ r : Fin 8, (p : ℤ) ∣ x r := by
  rw [Representation.primeIdeal, Submodule.ideal_span_singleton_smul] at hx
  rcases hx with ⟨y, _, hy⟩
  intro r
  rw [← hy]
  exact ⟨y r, by simp [Pi.smul_apply]⟩

/-- Standard basis classes are nonzero in every prime reduction. -/
theorem prime_reduction_class_basis_ne_zero
    (p : ℕ) [Fact p.Prime] (i : Fin 8) :
    prime_reduction_class (ρ := representation) p (basisVector i) ≠ 0 := by
  intro hzero
  have hmem : basisVector i ∈
      (Representation.primeIdeal p • (⊤ : Submodule ℤ W8)) :=
    (prime_reduction_class_eq_zero_iff_mem_prime_mul
      (ρ := representation) p (basisVector i)).1 hzero
  have hi : (p : ℤ) ∣ (1 : ℤ) := by
    simpa [basisVector] using dvd_coord_of_mem_prime_mul p hmem i
  exact (Fact.out : p.Prime).not_dvd_one (Int.natCast_dvd_natCast.1 hi)

/-- A nonzero scalar multiple of a standard basis class generates that basis class modulo `p`. -/
theorem basis_mem_of_int_smul_basis_mem
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    (i : Fin 8) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hmem : prime_reduction_class (ρ := representation) p (a • basisVector i) ∈ U) :
    prime_reduction_class (ρ := representation) p (basisVector i) ∈ U := by
  obtain ⟨u, v, huv⟩ := exists_int_bezout_of_prime_not_dvd p a ha
  let ei := prime_reduction_class (ρ := representation) p (basisVector i)
  have ha_mem : a • ei ∈ U := by
    rw [← prime_reduction_class_zsmul_current]
    exact hmem
  have hu_mem : u • (a • ei) ∈ U :=
    Subrepresentation.zsmul_mem p U ha_mem u
  have hp_zero : (p : ℤ) • ei = 0 := by
    rw [← prime_reduction_class_zsmul_current]
    exact prime_reduction_class_prime_smul p (basisVector i)
  have hv_mem : v • ((p : ℤ) • ei) ∈ U := by
    rw [hp_zero]
    exact U.toSubmodule.toAddSubgroup.zsmul_mem U.toSubmodule.zero_mem v
  have hcomb : (u * a + v * (p : ℤ)) • ei ∈ U := by
    have hsum :
        (u * a + v * (p : ℤ)) • ei =
          u • (a • ei) + v • ((p : ℤ) • ei) := by
      rw [add_smul]
      congr 1
      · rw [smul_smul]
      · change (v * (p : ℤ)) • ei = v • ((p : ℤ) • ei)
        rw [smul_smul]
    rw [hsum]
    exact U.toSubmodule.add_mem hu_mem hv_mem
  simpa [ei, huv] using hcomb

/-- Along an edge of the `E₈` Dynkin diagram, membership of one basis class propagates to the
neighboring basis class. -/
theorem basis_mem_of_cartan_edge
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    {i j : Fin 8} (hij : CartanMatrix.E₈ i j = -1)
    (hi : prime_reduction_class (ρ := representation) p (basisVector i) ∈ U) :
    prime_reduction_class (ρ := representation) p (basisVector j) ∈ U := by
  let σ := (representation.primeStableLattice p).reductionRepresentation
  have hact_mem :
      σ (CoxeterMatrix.E₈.simple j)
          (prime_reduction_class (ρ := representation) p (basisVector i)) ∈ U :=
    U.apply_mem_toSubmodule (CoxeterMatrix.E₈.simple j) hi
  have hact :
      σ (CoxeterMatrix.E₈.simple j)
          (prime_reduction_class (ρ := representation) p (basisVector i)) =
        prime_reduction_class (ρ := representation) p (simpleReflection j (basisVector i)) := by
    rw [prime_reduction_class_map (ρ := representation) p]
    rw [representation_apply_simple]
  have hdiff_mem :
      prime_reduction_class (ρ := representation) p (simpleReflection j (basisVector i)) -
          prime_reduction_class (ρ := representation) p (basisVector i) ∈ U := by
    simpa [hact] using U.toSubmodule.sub_mem hact_mem hi
  have hdiff :
      prime_reduction_class (ρ := representation) p (simpleReflection j (basisVector i)) -
          prime_reduction_class (ρ := representation) p (basisVector i) =
        prime_reduction_class (ρ := representation) p (basisVector j) := by
    rw [← prime_reduction_class_sub_current]
    rw [simpleReflection_basisVector, hij]
    simp [sub_eq_add_neg]
  simpa [hdiff] using hdiff_mem

/-- From any one standard basis class, the connected `E₈` diagram generates all basis classes. -/
theorem all_basis_mem_of_basis_mem
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    (i : Fin 8)
    (hi : prime_reduction_class (ρ := representation) p (basisVector i) ∈ U) :
    ∀ j : Fin 8, prime_reduction_class (ρ := representation) p (basisVector j) ∈ U := by
  fin_cases i
  · have h0 := hi
    have h2 := basis_mem_of_cartan_edge p U (i := (0 : Fin 8)) (j := (2 : Fin 8)) (by decide) h0
    have h3 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (3 : Fin 8)) (by decide) h2
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h4 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (4 : Fin 8)) (by decide) h3
    have h5 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (5 : Fin 8)) (by decide) h4
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h1 := hi
    have h3 := basis_mem_of_cartan_edge p U (i := (1 : Fin 8)) (j := (3 : Fin 8)) (by decide) h1
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h4 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (4 : Fin 8)) (by decide) h3
    have h5 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (5 : Fin 8)) (by decide) h4
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h2 := hi
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h3 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (3 : Fin 8)) (by decide) h2
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h4 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (4 : Fin 8)) (by decide) h3
    have h5 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (5 : Fin 8)) (by decide) h4
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h3 := hi
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h4 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (4 : Fin 8)) (by decide) h3
    have h5 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (5 : Fin 8)) (by decide) h4
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h4 := hi
    have h3 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (3 : Fin 8)) (by decide) h4
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h5 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (5 : Fin 8)) (by decide) h4
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h5 := hi
    have h4 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (4 : Fin 8)) (by decide) h5
    have h3 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (3 : Fin 8)) (by decide) h4
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h6 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (6 : Fin 8)) (by decide) h5
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h6 := hi
    have h5 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (5 : Fin 8)) (by decide) h6
    have h4 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (4 : Fin 8)) (by decide) h5
    have h3 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (3 : Fin 8)) (by decide) h4
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    have h7 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (7 : Fin 8)) (by decide) h6
    intro j; fin_cases j <;> assumption
  · have h7 := hi
    have h6 := basis_mem_of_cartan_edge p U (i := (7 : Fin 8)) (j := (6 : Fin 8)) (by decide) h7
    have h5 := basis_mem_of_cartan_edge p U (i := (6 : Fin 8)) (j := (5 : Fin 8)) (by decide) h6
    have h4 := basis_mem_of_cartan_edge p U (i := (5 : Fin 8)) (j := (4 : Fin 8)) (by decide) h5
    have h3 := basis_mem_of_cartan_edge p U (i := (4 : Fin 8)) (j := (3 : Fin 8)) (by decide) h4
    have h1 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (1 : Fin 8)) (by decide) h3
    have h2 := basis_mem_of_cartan_edge p U (i := (3 : Fin 8)) (j := (2 : Fin 8)) (by decide) h3
    have h0 := basis_mem_of_cartan_edge p U (i := (2 : Fin 8)) (j := (0 : Fin 8)) (by decide) h2
    intro j; fin_cases j <;> assumption

/-- If a subrepresentation contains all standard basis classes, it is the whole reduction. -/
theorem subrepresentation_eq_top_of_forall_basis_mem
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    (hbasis : ∀ i : Fin 8,
      prime_reduction_class (ρ := representation) p (basisVector i) ∈ U) :
    U = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  change U.toSubmodule = (⊤ : Submodule
    (IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
    (representation.primeStableLattice p).reduction)
  rw [eq_top_iff]
  intro z hzTop
  rcases Submodule.Quotient.mk_surjective
      (representation.primeStableLattice p).maximalIdealSubmodule z with ⟨zloc, rfl⟩
  clear hzTop
  refine (LocalizedModule.induction_on
    (β := fun w =>
      ∀ hwtop,
        (Submodule.Quotient.mk
          (⟨w, hwtop⟩ : (representation.primeStableLattice p).toSubmodule) :
            (representation.primeStableLattice p).reduction) ∈ U)
    ?_ (zloc : LocalizedModule.AtPrime (Representation.primeIdeal p) W8)) zloc.property
  intro x s hwtop
  let c : IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)) :=
    (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
      (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s)
  let xclass := prime_reduction_class (ρ := representation) p x
  let target : (representation.primeStableLattice p).reduction :=
    Submodule.Quotient.mk
      (⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s,
        Submodule.mem_top⟩ : (representation.primeStableLattice p).toSubmodule)
  have hxclass_mem : xclass ∈ U := by
    have hxsum : x = ∑ i, x i • basisVector i := by
      ext r
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single r]
      · simp [basisVector]
      · intro b _ hb
        simp [basisVector, hb]
      · intro hr
        simp at hr
    change prime_reduction_class (ρ := representation) p x ∈ U
    rw [hxsum]
    change primeReductionClassAddHom p (∑ i, x i • basisVector i) ∈ U
    rw [map_sum]
    refine Submodule.sum_mem U.toSubmodule ?_
    intro i _
    change prime_reduction_class (ρ := representation) p (x i • basisVector i) ∈ U
    rw [prime_reduction_class_zsmul_current]
    exact
      Subrepresentation.zsmul_mem p U (hbasis i) (x i)
  have hc_x :
      c • target = xclass := by
    unfold c target
    let y : (representation.primeStableLattice p).toSubmodule :=
      ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s,
        Submodule.mem_top⟩
    refine (StableLattice.reduction_smul_mk
      (L := representation.primeStableLattice p)
      (a := algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (s : ℤ))
      (y := y)).trans ?_
    unfold xclass prime_reduction_class
    congr 1
    ext
    change
      (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (s : ℤ)) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s =
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1
    change
      Localization.mk (s : ℤ) (1 : (Representation.primeIdeal p).primeCompl) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s =
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1
    rw [LocalizedModule.mk_smul_mk]
    convert LocalizedModule.mk_cancel (S := (Representation.primeIdeal p).primeCompl) s x using 2
    ext
    simp
  have hc_target_mem : c • target ∈ U := by
    rw [hc_x]
    exact hxclass_mem
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hs_mem :
        (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p)) := by
      exact (Ideal.Quotient.eq_zero_iff_mem).1 hc0
    have hs_prime :
        (s : ℤ) ∈ Representation.primeIdeal p := by
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime (Representation.primeIdeal p))
        (Representation.primeIdeal p) (s : ℤ)).1 hs_mem
    exact s.2 hs_prime
  have htarget_mem : target ∈ U :=
    (U.toSubmodule.smul_mem_iff hc_ne).1 hc_target_mem
  exact htarget_mem

/-- Every nonzero vector in a subrepresentation of a prime reduction has a nonzero integral
canonical representative after clearing a denominator. -/
theorem exists_integral_class_mem_ne_zero_of_mem_ne_zero
    (p : ℕ) [Fact p.Prime]
    (U : Subrepresentation ((representation.primeStableLattice p).reductionRepresentation))
    {z : (representation.primeStableLattice p).reduction}
    (hz : z ∈ U) (hz0 : z ≠ 0) :
    ∃ x : W8,
      prime_reduction_class (ρ := representation) p x ∈ U ∧
        prime_reduction_class (ρ := representation) p x ≠ 0 := by
  rcases Submodule.Quotient.mk_surjective
      (representation.primeStableLattice p).maximalIdealSubmodule z with ⟨zloc, rfl⟩
  refine (LocalizedModule.induction_on
    (β := fun w =>
      ∀ hwtop,
        (Submodule.Quotient.mk
          (⟨w, hwtop⟩ : (representation.primeStableLattice p).toSubmodule) :
            (representation.primeStableLattice p).reduction) ∈ U →
        (Submodule.Quotient.mk
          (⟨w, hwtop⟩ : (representation.primeStableLattice p).toSubmodule) :
            (representation.primeStableLattice p).reduction) ≠ 0 →
        ∃ x : W8,
          prime_reduction_class (ρ := representation) p x ∈ U ∧
            prime_reduction_class (ρ := representation) p x ≠ 0)
    ?_ (zloc : LocalizedModule.AtPrime (Representation.primeIdeal p) W8))
    zloc.property hz hz0
  intro x s hwtop hz_mem hz_ne
  let c : IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)) :=
    (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p))))
      (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s)
  let target : (representation.primeStableLattice p).reduction :=
    Submodule.Quotient.mk
      (⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s, hwtop⟩ :
        (representation.primeStableLattice p).toSubmodule)
  have hc_x :
      c • target = prime_reduction_class (ρ := representation) p x := by
    unfold c target prime_reduction_class
    let y : (representation.primeStableLattice p).toSubmodule :=
      ⟨LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s, hwtop⟩
    refine (StableLattice.reduction_smul_mk
      (L := representation.primeStableLattice p)
      (a := algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (s : ℤ))
      (y := y)).trans ?_
    congr 1
    ext
    change
      (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) (s : ℤ)) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s =
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1
    change
      Localization.mk (s : ℤ) (1 : (Representation.primeIdeal p).primeCompl) •
          LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x s =
        LocalizedModule.mk (S := (Representation.primeIdeal p).primeCompl) x 1
    rw [LocalizedModule.mk_smul_mk]
    convert LocalizedModule.mk_cancel (S := (Representation.primeIdeal p).primeCompl) s x using 2
    ext
    simp
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hs_mem :
        (algebraMap ℤ (Localization.AtPrime (Representation.primeIdeal p)) s) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime (Representation.primeIdeal p)) := by
      exact (Ideal.Quotient.eq_zero_iff_mem).1 hc0
    have hs_prime :
        (s : ℤ) ∈ Representation.primeIdeal p := by
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime (Representation.primeIdeal p))
        (Representation.primeIdeal p) (s : ℤ)).1 hs_mem
    exact s.2 hs_prime
  refine ⟨x, ?_, ?_⟩
  · rw [← hc_x]
    exact U.toSubmodule.smul_mem c hz_mem
  · intro hxzero
    have htarget_zero : target = 0 := by
      -- If the numerator class is zero, then the numerator is already in `pW8`; the localization
      -- bridge kills the represented class with the original denominator directly.
      have hx_mem :
          x ∈ (Representation.primeIdeal p • (⊤ : Submodule ℤ W8)) :=
        (prime_reduction_class_eq_zero_iff_mem_prime_mul
          (ρ := representation) p x).1 hxzero
      apply (Submodule.Quotient.mk_eq_zero _).2
      simpa [target] using
        localized_mk_mem_maximalIdealSubmodule_of_mem_prime_mul_denom
          (ρ := representation) p s hx_mem
    exact hz_ne htarget_zero

/-- The concrete integral reflection representation of type `E₈` has irreducible reductions at
every prime. -/
theorem hasSimplePrimeReductions :
    representation.HasSimplePrimeReductions := by
  intro p hp
  let σ := (representation.primeStableLattice p).reductionRepresentation
  letI : Nontrivial (Subrepresentation σ) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro hbot_top
    have hsub :
        (⊥ : Subrepresentation σ).toSubmodule =
          (⊤ : Subrepresentation σ).toSubmodule :=
      congrArg Subrepresentation.toSubmodule hbot_top
    have hbmem :
        prime_reduction_class (ρ := representation) p (basisVector 0) ∈
          (⊥ : Subrepresentation σ).toSubmodule := by
      have htopmem :
          prime_reduction_class (ρ := representation) p (basisVector 0) ∈
            (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
      simpa [hsub] using htopmem
    have hbzero :
        prime_reduction_class (ρ := representation) p (basisVector 0) = 0 := by
      simpa using hbmem
    exact prime_reduction_class_basis_ne_zero p 0 hbzero
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  have hUsub : U.toSubmodule ≠ (⊥ : Submodule
      (IsLocalRing.ResidueField (Localization.AtPrime (Representation.primeIdeal p)))
      (representation.primeStableLattice p).reduction) := by
    intro hsub
    apply hU
    apply Subrepresentation.toSubmodule_injective
    exact hsub
  rcases (Submodule.ne_bot_iff U.toSubmodule).1 hUsub with ⟨z, hzU, hz0⟩
  rcases exists_integral_class_mem_ne_zero_of_mem_ne_zero p U hzU hz0 with
    ⟨x, hxU, hx0⟩
  rcases exists_not_dvd_cartanFunctional_of_class_ne_zero p hx0 with ⟨i, hi⟩
  have hact_mem :
      σ (CoxeterMatrix.E₈.simple i)
          (prime_reduction_class (ρ := representation) p x) ∈ U :=
    U.apply_mem_toSubmodule (CoxeterMatrix.E₈.simple i) hxU
  have hact :
      σ (CoxeterMatrix.E₈.simple i)
          (prime_reduction_class (ρ := representation) p x) =
        prime_reduction_class (ρ := representation) p (simpleReflection i x) := by
    rw [prime_reduction_class_map (ρ := representation) p]
    rw [representation_apply_simple]
  have hdiff_mem :
      prime_reduction_class (ρ := representation) p (simpleReflection i x) -
          prime_reduction_class (ρ := representation) p x ∈ U := by
    simpa [hact] using U.toSubmodule.sub_mem hact_mem hxU
  have hdiff :
      prime_reduction_class (ρ := representation) p (simpleReflection i x) -
          prime_reduction_class (ρ := representation) p x =
        prime_reduction_class (ρ := representation) p
          (-(cartanFunctional i x) • basisVector i) := by
    rw [← prime_reduction_class_sub_current]
    rw [simpleReflection_apply_sub]
  have hnot_dvd_neg : ¬ (p : ℤ) ∣ -(cartanFunctional i x) := by
    intro hneg
    exact hi (by simpa using hneg)
  have hbasis_i :
      prime_reduction_class (ρ := representation) p (basisVector i) ∈ U :=
    basis_mem_of_int_smul_basis_mem p U i hnot_dvd_neg (by
      simpa [hdiff] using hdiff_mem)
  exact subrepresentation_eq_top_of_forall_basis_mem p U
    (all_basis_mem_of_basis_mem p U i hbasis_i)

theorem finrank_lattice : Module.finrank ℤ W8 = 8 := by
  simp

end E8ReflectionMainWitness

/-- Exercise 15-15.2-6(e): the Coxeter group of type `E₈` has a rank-eight integral reflection
representation whose reductions modulo every prime are irreducible. -/
theorem exists_e8_reflection_representation_with_simple_prime_reductions :
    ∃ ρ : Representation ℤ CoxeterMatrix.E₈.Group (Fin 8 → ℤ),
      ρ.HasSimplePrimeReductions ∧
        Module.finrank ℤ (Fin 8 → ℤ) = 8 ∧
          ∀ i : Fin 8,
            ρ (CoxeterMatrix.E₈.simple i) =
              E8ReflectionMainWitness.simpleReflection i := by
  refine ⟨E8ReflectionMainWitness.representation, ?_, ?_, ?_⟩
  · exact E8ReflectionMainWitness.hasSimplePrimeReductions
  · exact E8ReflectionMainWitness.finrank_lattice
  · intro i
    exact E8ReflectionMainWitness.representation_apply_simple i

#print axioms exists_e8_reflection_representation_with_simple_prime_reductions
