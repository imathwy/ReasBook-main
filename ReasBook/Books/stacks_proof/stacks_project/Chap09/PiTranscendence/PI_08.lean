import Mathlib
import StacksProject_2024.Chap09.PiTranscendence.PI_05
import StacksProject_2024.Chap09.PiTranscendence.PI_06

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

section

variable {P : ℤ[X]} {n : ℕ} {a : Fin n → ℂ}

/-- Helper for Theorem PI-08: the powerset sum of polynomial evaluations splits into the zero and
nonzero subset-sum contributions. -/
lemma sum_powerset_aeval_split_zero_nonzero (g : ℤ[X]) :
    (((Finset.univ : Finset (Fin n)).powerset).sum fun S ↦ aeval (S.sum a) g) =
      Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g) +
        Finset.sum (nonzeroSumSubsets a) (fun S ↦ aeval (S.sum a) g) := by
  -- Proof comment: split the powerset by whether the subset sum vanishes.
  simpa [zeroSumSubsets, nonzeroSumSubsets] using
    (Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Fin n)).powerset)
      (fun S : Finset (Fin n) ↦ S.sum a = 0)
      (fun S ↦ aeval (S.sum a) g)).symm

/-- Helper for Theorem PI-08: the zero-sum contribution is always an integer after scaling by the
prescribed power of `P.leadingCoeff`. -/
lemma exists_integer_scaled_zero_sum_contribution (g : ℤ[X]) :
    ∃ Z0 : ℤ,
      ((P.leadingCoeff ^ g.natDegree : ℂ) *
          Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g) = (Z0 : ℂ)) := by
  let Z0 : ℤ := P.leadingCoeff ^ g.natDegree * (((zeroSumSubsets a).card : ℤ) * g.eval (0 : ℤ))
  refine ⟨Z0, ?_⟩
  -- Proof comment: every zero-sum subset contributes the common value `g(0)`.
  calc
    ((P.leadingCoeff ^ g.natDegree : ℂ) *
        Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g))
        = ((P.leadingCoeff ^ g.natDegree : ℂ) *
            Finset.sum (zeroSumSubsets a)
              (fun _ ↦ (Int.castRingHom ℂ) (g.eval (0 : ℤ)))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hsum : S.sum a = 0 := (Finset.mem_filter.mp hS).2
            rw [hsum]
            simpa using
              (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := (0 : ℤ)) g)
    _ = ((P.leadingCoeff ^ g.natDegree : ℂ) *
          (((zeroSumSubsets a).card : ℂ) * (Int.castRingHom ℂ) (g.eval (0 : ℤ)))) := by
            simp
    _ = (Z0 : ℂ) := by
            simp [Z0, Int.cast_mul, Int.cast_pow]

/-- Helper for Theorem PI-08: scaling the chosen root enumeration by `P.leadingCoeff` produces the
canonical root multiset of `P.integralNormalization`. -/
lemma scaled_root_enumeration_integralNormalization
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (hP : P ≠ 0) :
    (List.ofFn (fun i ↦ (P.leadingCoeff : ℂ) * a i) : Multiset ℂ) =
      (P.integralNormalization).aroots ℂ := by
  have hIntInj : Function.Injective (Int.castRingHom ℂ) := by
    -- Proof comment: integer coefficients embed faithfully into `ℂ`.
    intro x y hxy
    exact Int.cast_injective hxy
  have hLC : (P.leadingCoeff : ℂ) ≠ 0 := by
    -- Proof comment: the nonzero polynomial hypothesis gives a nonzero scaling factor.
    exact_mod_cast (leadingCoeff_ne_zero.mpr hP)
  have hLCmap : (P.map (Int.castRingHom ℂ)).leadingCoeff = (P.leadingCoeff : ℂ) := by
    -- Proof comment: after mapping coefficients to `ℂ`, the leading coefficient is unchanged.
    simpa using Polynomial.leadingCoeff_map_of_injective hIntInj P
  calc
    (List.ofFn (fun i ↦ (P.leadingCoeff : ℂ) * a i) : Multiset ℂ)
        = Multiset.map (fun z : ℂ ↦ (P.leadingCoeff : ℂ) * z) (List.ofFn a) := by
            -- Proof comment: rewrite the scaled enumeration as the image of the original one.
            simp_rw [← Fin.univ_val_map]
            simpa [Function.comp] using
              (Multiset.map_map (fun z : ℂ ↦ (P.leadingCoeff : ℂ) * z) a Finset.univ.val).symm
    _ = Multiset.map (fun z : ℂ ↦ (P.leadingCoeff : ℂ) * z) (P.aroots ℂ) := by
          rw [ha]
    _ = ((P.map (Int.castRingHom ℂ)).scaleRoots ((P.leadingCoeff : ℂ))).roots := by
          -- Proof comment: `scaleRoots` transports each complex root by multiplication with the
          -- scaling factor.
          rw [aroots_def]
          symm
          exact roots_scaleRoots (P.map (Int.castRingHom ℂ)) (isUnit_iff_ne_zero.mpr hLC)
    _ = (((P.map (Int.castRingHom ℂ)).integralNormalization *
            Polynomial.C ((P.leadingCoeff : ℂ))).roots) := by
          -- Proof comment: replace the scaled polynomial by the product coming from
          -- `integralNormalization`.
          have hnorm :
              ((P.map (Int.castRingHom ℂ)).scaleRoots
                  (P.map (Int.castRingHom ℂ)).leadingCoeff).roots =
                (((P.map (Int.castRingHom ℂ)).integralNormalization *
                    Polynomial.C ((P.map (Int.castRingHom ℂ)).leadingCoeff)).roots) := by
              exact congrArg Polynomial.roots
                (integralNormalization_mul_C_leadingCoeff (P.map (Int.castRingHom ℂ))).symm
          simpa [hLCmap] using hnorm
    _ = ((P.map (Int.castRingHom ℂ)).integralNormalization).roots := by
          -- Proof comment: multiplication by a nonzero scalar polynomial does not change roots.
          rw [mul_comm, roots_C_mul _ hLC]
    _ = (P.integralNormalization).aroots ℂ := by
          -- Proof comment: map `integralNormalization` back to the canonical `aroots` view.
          simpa [aroots_def] using congrArg Polynomial.roots
            (integralNormalization_map (Int.castRingHom ℂ) P hLC)

/-- Helper for Theorem PI-08: each elementary symmetric polynomial in the scaled roots evaluates to
an integer in `ℂ`. -/
lemma scaled_esymm_values_are_integers
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (hP : P ≠ 0) (i : Fin n) :
    ∃ z : ℤ,
      MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
        (MvPolynomial.esymm (Fin n) ℤ (i.1 + 1)) = (z : ℂ) := by
  have hn_card : n = (P.aroots ℂ).card := by
    -- Proof comment: the chosen `Fin n`-enumeration has exactly the same cardinality as
    -- `P.aroots ℂ`.
    simpa using congrArg Multiset.card ha
  have hn : P.natDegree = n := by
    -- Proof comment: over `ℂ`, the canonical root multiset has cardinality `P.natDegree`.
    rw [← IsAlgClosed.card_aroots_eq_natDegree (B := ℂ) (p := P)]
    exact hn_card.symm
  let m : ℕ := i.1 + 1
  have hm : m ≤ n := by
    -- Proof comment: the `(i.1 + 1)`-st elementary symmetric polynomial is within range.
    dsimp [m]
    exact Nat.succ_le_of_lt i.2
  let q : ℂ[X] := (P.integralNormalization).map (Int.castRingHom ℂ)
  have hmonic : q.Monic := by
    -- Proof comment: `integralNormalization` is monic, and monicity is preserved by coefficient
    -- maps.
    dsimp [q]
    exact (monic_integralNormalization hP).map (Int.castRingHom ℂ)
  have hqnat : q.natDegree = n := by
    -- Proof comment: the mapped integral normalization has the same degree as `P`.
    dsimp [q]
    rw [(monic_integralNormalization hP).natDegree_map (Int.castRingHom ℂ)]
    rw [natDegree_integralNormalization, hn]
  have hqcoeff : q.coeff (n - m) = ((-1 : ℂ) ^ m) * q.roots.esymm m := by
    -- Proof comment: Vieta expresses the relevant coefficient of the monic polynomial `q` in
    -- terms of the `m`-th elementary symmetric polynomial of its roots.
    have hsplit : q.Splits := IsAlgClosed.splits q
    have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits hsplit
      (k := n - m) (by simp [hqnat])
    rw [hmonic.leadingCoeff, one_mul, hqnat, Nat.sub_sub_self hm] at hcoeff
    exact hcoeff
  have hsign : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
    -- Proof comment: the sign factor from Vieta is self-inverse.
    calc
      ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = (((-1 : ℂ) ^ m) ^ 2) := by ring
      _ = (-1 : ℂ) ^ (m * 2) := by rw [pow_mul]
      _ = 1 := by simp
  have hesymm_q : q.roots.esymm m = ((-1 : ℂ) ^ m) * q.coeff (n - m) := by
    -- Proof comment: multiply Vieta's identity by the same sign once more to solve for the
    -- elementary symmetric polynomial.
    calc
      q.roots.esymm m = (1 : ℂ) * q.roots.esymm m := by simp
      _ = (((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m)) * q.roots.esymm m := by rw [hsign]
      _ = ((-1 : ℂ) ^ m) * (((-1 : ℂ) ^ m) * q.roots.esymm m) := by ring
      _ = ((-1 : ℂ) ^ m) * q.coeff (n - m) := by rw [← hqcoeff]
  refine ⟨(-1 : ℤ) ^ m * (P.integralNormalization).coeff (n - m), ?_⟩
  calc
    MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
        (MvPolynomial.esymm (Fin n) ℤ m)
        = ((List.ofFn (fun k ↦ (P.leadingCoeff : ℂ) * a k) : Multiset ℂ).esymm m) := by
            -- Proof comment: `aeval` of the elementary symmetric polynomial is multiset
            -- elementary-symmetric evaluation on the scaled roots.
            simpa using
              (MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := Fin n) (R := ℤ) (S := ℂ)
                (n := m) (f := fun k ↦ (P.leadingCoeff : ℂ) * a k))
    _ = (((P.integralNormalization).aroots ℂ).esymm m) := by
          -- Proof comment: replace the scaled root list by the canonical root multiset from the
          -- previous helper.
          rw [scaled_root_enumeration_integralNormalization (P := P) (a := a) ha hP]
    _ = q.roots.esymm m := by
          -- Proof comment: return to the ordinary roots of the mapped polynomial `q`.
          simp [q, aroots_def]
    _ = (((-1 : ℂ) ^ m) * q.coeff (n - m)) := hesymm_q
    _ = (((-1 : ℤ) ^ m * (P.integralNormalization).coeff (n - m) : ℤ) : ℂ) := by
          -- Proof comment: the relevant coefficient of `q` is the complex image of the
          -- corresponding integer coefficient of `P.integralNormalization`.
          dsimp [q]
          simp [Polynomial.coeff_map, Int.cast_mul, Int.cast_pow]

/-- Helper for Theorem PI-08: renaming the subset-linear form `∑ i ∈ S, X i` reindexes it by the
image subset. -/
lemma rename_subset_sum_X_image (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    MvPolynomial.rename e (∑ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin n) ℤ) =
      ∑ j ∈ S.image e, MvPolynomial.X j := by
  -- Proof comment: `rename` commutes with finite sums, and the permutation simply reindexes the
  -- subset by its image.
  calc
    MvPolynomial.rename e (∑ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin n) ℤ)
        = ∑ i ∈ S, MvPolynomial.X (e i) := by
            simp [map_sum]
    _ = ∑ j ∈ S.image e, MvPolynomial.X j := by
          simpa using
            (Finset.sum_image (s := S) (f := e) (g := fun j : Fin n ↦ (MvPolynomial.X j :
              MvPolynomial (Fin n) ℤ)) e.injective.injOn).symm

/-- Helper for Theorem PI-08: package the total powerset expression as one explicit symmetric
mv-polynomial whose evaluation at the scaled roots gives the denominator-cleared total sum. -/
lemma scaled_total_powerset_mvpolynomial_isSymmetric_and_aeval (g : ℤ[X]) :
    ∃ A : MvPolynomial (Fin n) ℤ,
      A.IsSymmetric ∧
        MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k) A =
          ((P.leadingCoeff ^ g.natDegree : ℂ) *
            Finset.sum ((Finset.univ : Finset (Fin n)).powerset)
              (fun S ↦ Polynomial.aeval (S.sum a) g)) := by
  let term_g : Finset (Fin n) → MvPolynomial (Fin n) ℤ :=
    fun S ↦ Polynomial.eval₂ MvPolynomial.C (∑ i ∈ S, MvPolynomial.X i) (g.scaleRoots P.leadingCoeff)
  let A : MvPolynomial (Fin n) ℤ :=
    Finset.sum ((Finset.univ : Finset (Fin n)).powerset) term_g
  have hrename_term :
      ∀ e : Equiv.Perm (Fin n), ∀ S : Finset (Fin n),
        MvPolynomial.rename e (term_g S) = term_g (S.image e) := by
    intro e S
    -- Proof comment: transport the polynomial evaluation through `rename`, then normalize the
    -- renamed subset-linear form with `rename_subset_sum_X_image`.
    dsimp [term_g]
    calc
      MvPolynomial.rename e
          (Polynomial.eval₂ MvPolynomial.C (∑ i ∈ S, MvPolynomial.X i)
            (g.scaleRoots P.leadingCoeff))
          =
            Polynomial.eval₂ ((MvPolynomial.rename e).toRingHom.comp MvPolynomial.C)
              (MvPolynomial.rename e (∑ i ∈ S, MvPolynomial.X i))
              (g.scaleRoots P.leadingCoeff) := by
                simpa using
                  (Polynomial.hom_eval₂ (f := MvPolynomial.C)
                    (g := (MvPolynomial.rename e).toRingHom)
                    (p := g.scaleRoots P.leadingCoeff)
                    (x := ∑ i ∈ S, MvPolynomial.X i))
      _ = Polynomial.eval₂ MvPolynomial.C
            (MvPolynomial.rename e (∑ i ∈ S, MvPolynomial.X i))
            (g.scaleRoots P.leadingCoeff) := by
              congr 1
              ext z
              simp
      _ = term_g (S.image e) := by
            rw [rename_subset_sum_X_image (e := e) (S := S)]
  have hA_symmetric : A.IsSymmetric := by
    intro e
    -- Proof comment: reindex the powerset by the permutation image; `powerset_image` and
    -- `univ.image e = univ` give the required invariance.
    calc
      MvPolynomial.rename e A
          = Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ term_g (S.image e)) := by
              dsimp [A]
              simp_rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro S hS
              exact hrename_term e S
      _ = Finset.sum
            (((Finset.univ : Finset (Fin n)).powerset).image
              (fun S : Finset (Fin n) ↦ S.image e))
            term_g := by
            symm
            exact Finset.sum_image
              (s := (Finset.univ : Finset (Fin n)).powerset)
              (f := term_g)
              (g := fun S : Finset (Fin n) ↦ S.image e)
              (Finset.image_injective e.injective).injOn
      _ = Finset.sum (((Finset.univ : Finset (Fin n)).image e).powerset) term_g := by
            rw [← Finset.powerset_image (s := (Finset.univ : Finset (Fin n))) (f := e)]
      _ = Finset.sum ((Finset.univ : Finset (Fin n)).powerset) term_g := by
            simp
      _ = A := by
            rfl
  have hterm_eval :
      ∀ S : Finset (Fin n),
        MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k) (term_g S) =
          ((P.leadingCoeff ^ g.natDegree : ℂ) * Polynomial.aeval (S.sum a) g) := by
    intro S
    -- Proof comment: evaluating each term at the scaled roots is exactly the
    -- `scaleRoots_eval₂_mul` denominator-clearing identity.
    dsimp [term_g]
    calc
      MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
          (Polynomial.eval₂ MvPolynomial.C (∑ i ∈ S, MvPolynomial.X i)
            (g.scaleRoots P.leadingCoeff))
          =
            Polynomial.eval₂
              (((MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)).toRingHom).comp
                MvPolynomial.C)
              (MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
                (∑ i ∈ S, MvPolynomial.X i))
              (g.scaleRoots P.leadingCoeff) := by
                simpa using
                  (Polynomial.hom_eval₂ (f := MvPolynomial.C)
                    (g := (MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)).toRingHom)
                    (p := g.scaleRoots P.leadingCoeff)
                    (x := ∑ i ∈ S, MvPolynomial.X i))
      _ = Polynomial.eval₂ (Int.castRingHom ℂ)
            (MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
              (∑ i ∈ S, MvPolynomial.X i))
            (g.scaleRoots P.leadingCoeff) := by
              congr 1
              ext z
              simp
      _ = Polynomial.eval₂ (Int.castRingHom ℂ)
            ((P.leadingCoeff : ℂ) * S.sum a) (g.scaleRoots P.leadingCoeff) := by
              congr 2
              calc
                MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
                    (∑ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin n) ℤ)
                    = ∑ i ∈ S, ((P.leadingCoeff : ℂ) * a i) := by
                        simp
                _ = (P.leadingCoeff : ℂ) * S.sum a := by
                      rw [← Finset.mul_sum]
      _ = ((P.leadingCoeff ^ g.natDegree : ℂ) * Polynomial.aeval (S.sum a) g) := by
            simpa [Polynomial.aeval_def] using
              (Polynomial.scaleRoots_eval₂_mul
                (p := g) (f := Int.castRingHom ℂ) (r := S.sum a) (s := P.leadingCoeff))
  refine ⟨A, hA_symmetric, ?_⟩
  -- Proof comment: evaluate the packaged symmetric polynomial termwise and then factor out the
  -- common power of `P.leadingCoeff`.
  calc
    MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k) A
        = Finset.sum ((Finset.univ : Finset (Fin n)).powerset)
            (fun S ↦ MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k) (term_g S)) := by
              dsimp [A]
              simp
    _ = Finset.sum ((Finset.univ : Finset (Fin n)).powerset)
          (fun S ↦ ((P.leadingCoeff ^ g.natDegree : ℂ) * Polynomial.aeval (S.sum a) g)) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            exact hterm_eval S
    _ = ((P.leadingCoeff ^ g.natDegree : ℂ) *
          Finset.sum ((Finset.univ : Finset (Fin n)).powerset)
            (fun S ↦ Polynomial.aeval (S.sum a) g)) := by
          rw [Finset.mul_sum]

/-- Helper for Theorem PI-08: the total powerset sum should be handled by the symmetric-polynomial
route from PI-06 together with Vieta for `P.integralNormalization`. -/
lemma exists_integer_scaled_total_powerset_subset_sum_aeval
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) (hP : P ≠ 0) (g : ℤ[X]) :
    ∃ Z : ℤ,
      ((P.leadingCoeff ^ g.natDegree : ℂ) *
          Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ aeval (S.sum a) g) =
            (Z : ℂ)) := by
  -- Route correction: package the total powerset sum as one symmetric mv-polynomial, factor it
  -- through elementary symmetric polynomials via PI-06, and then evaluate at the integer-valued
  -- scaled elementary symmetric data supplied by Vieta.
  obtain ⟨A, hA_symm, hA_eval⟩ :=
    scaled_total_powerset_mvpolynomial_isSymmetric_and_aeval (P := P) (a := a) (g := g)
  obtain ⟨B, hB⟩ := exists_esymm_polynomial_of_isSymmetric n A hA_symm
  choose z hz using
    (fun i : Fin n ↦ scaled_esymm_values_are_integers (P := P) (a := a) ha hP i)
  let Z : ℤ := MvPolynomial.aeval z B
  refine ⟨Z, ?_⟩
  -- Proof comment: composing `aeval` with the PI-06 factorization replaces each elementary
  -- symmetric value by its integer witness `z i`, and then `aeval_algebraMap_apply` moves the
  -- remaining integer polynomial evaluation into `ℂ`.
  calc
    ((P.leadingCoeff ^ g.natDegree : ℂ) *
        Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ aeval (S.sum a) g))
        = MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k) A := by
            rw [hA_eval]
    _ = MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
          (MvPolynomial.aeval (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℤ (i.1 + 1)) B) := by
            rw [hB]
    _ = MvPolynomial.aeval
          (fun i : Fin n ↦
            MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
              (MvPolynomial.esymm (Fin n) ℤ (i.1 + 1))) B := by
            simpa using
              (MvPolynomial.comp_aeval_apply
                (f := fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℤ (i.1 + 1))
                (φ := MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k))
                (p := B))
    _ = MvPolynomial.aeval (fun i : Fin n ↦ (z i : ℂ)) B := by
          have hzfun :
              (fun i : Fin n ↦
                MvPolynomial.aeval (fun k ↦ (P.leadingCoeff : ℂ) * a k)
                  (MvPolynomial.esymm (Fin n) ℤ (i.1 + 1))) =
                fun i : Fin n ↦ (z i : ℂ) := by
            funext i
            exact hz i
          rw [hzfun]
    _ = (Z : ℂ) := by
          simpa [Z] using (MvPolynomial.aeval_algebraMap_apply (A := ℤ) (B := ℂ) z B)

/- Domain-style sampling for PI-08:
- primary domain: denominator clearing for the canonical finite sum of integer-polynomial
  evaluations over the nonzero subset-sum family attached to a chosen enumeration of `P.aroots ℂ`;
- sampled owner declarations:
  `Polynomial.aeval`,
  `Polynomial.leadingCoeff`,
  `nonzeroSumSubsets`,
  `Finset.sum`;
- best owner abstraction: the canonical source-facing sum
  `(nonzeroSumSubsets a).sum (fun S ↦ aeval (S.sum a) g)`, with denominator clearing expressed
  directly by a power of `P.leadingCoeff` rather than by an auxiliary enumeration or duplicate
  denominator witness;
- primitive data: the integer `Zg` and the exponent `eg`;
- derived API: nonzeroness of `P.leadingCoeff ^ eg` and the uniform bound
  `eg ≤ K * (g.natDegree + 1)`.

Source/core/bridge triage:
- `source-facing`: the existence of integers clearing the subset-sum evaluation denominator by a
  power of `P.leadingCoeff`;
- `core/canonical`: `Polynomial.aeval`, `Polynomial.leadingCoeff`, and the canonical finite set
  `nonzeroSumSubsets a` from `PI_05`;
- `bridge/view`: the uniform bound on the exponent for each `g`;
- `layer`: `source-facing`.
-/

-- Semantic recall note: `lean_leansearch` was unavailable in this environment; this statement
-- follows the local root-enumeration, subset-sum splitting, and `Polynomial.aeval` API.

/-- Theorem PI-08: in the setting of Lemma PI-05 and Theorem PI-07, there is a constant `K`
depending only on the original polynomial `P` and the chosen root enumeration `a` such that, for
every `g ∈ ℤ[X]`, one can clear denominators in the canonical finite sum
`∑ S in nonzeroSumSubsets a, Polynomial.aeval (S.sum a) g` by multiplying with a nonzero power of
`P.leadingCoeff`, with exponent bounded by `K * (g.natDegree + 1)`. -/
theorem exists_uniform_leadingCoeff_power_denominator_control_for_subset_sum_aeval
    {P : ℤ[X]} {n : ℕ} {a : Fin n → ℂ}
    (ha : (List.ofFn a : Multiset ℂ) = P.aroots ℂ) :
    ∃ K : ℕ,
      ∀ g : ℤ[X], ∃ Zg : ℤ, ∃ eg : ℕ,
          P.leadingCoeff ^ eg ≠ 0 ∧
          ((P.leadingCoeff ^ eg : ℂ) * ((nonzeroSumSubsets a).sum fun S ↦ aeval (S.sum a) g) =
            (Zg : ℂ)) ∧
          eg ≤ K * (g.natDegree + 1) := by
  by_cases hP : P = 0
  · -- Proof comment: if `P = 0`, then the chosen root enumeration is empty, so the nonzero part
    -- of the powerset sum vanishes identically.
    refine ⟨1, ?_⟩
    intro g
    have hzero_roots : (List.ofFn a : Multiset ℂ) = 0 := by
      simpa [hP] using ha
    have hn : n = 0 := by
      simpa using congrArg Multiset.card hzero_roots
    subst hn
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · simp
    · have hnonzero : nonzeroSumSubsets a = ∅ := by
        simp [nonzeroSumSubsets]
      simpa [hnonzero]
    · simp
  · -- Route correction: reduce the nonzero case to the total powerset sum and the easy zero-sum
    -- contribution, leaving only the symmetric-polynomial denominator-clearing bridge.
    refine ⟨1, ?_⟩
    intro g
    obtain ⟨Z, hZ⟩ :=
      exists_integer_scaled_total_powerset_subset_sum_aeval (P := P) (a := a) ha hP g
    obtain ⟨Z0, hZ0⟩ :=
      exists_integer_scaled_zero_sum_contribution (P := P) (a := a) g
    refine ⟨Z - Z0, g.natDegree, ?_, ?_, ?_⟩
    · -- Proof comment: the scaling denominator is a nonzero power of the nonzero leading
      -- coefficient.
      exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hP)
    · -- Proof comment: split the full powerset sum into its zero and nonzero parts, then subtract
      -- the already-integral zero contribution.
      have hsplit :
          ((P.leadingCoeff ^ g.natDegree : ℂ) *
              Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ aeval (S.sum a) g)) =
            ((P.leadingCoeff ^ g.natDegree : ℂ) *
                Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g)) +
              ((P.leadingCoeff ^ g.natDegree : ℂ) *
                Finset.sum (nonzeroSumSubsets a) (fun S ↦ aeval (S.sum a) g)) := by
        rw [sum_powerset_aeval_split_zero_nonzero (a := a) g, mul_add]
      calc
        ((P.leadingCoeff ^ g.natDegree : ℂ) *
            Finset.sum (nonzeroSumSubsets a) (fun S ↦ aeval (S.sum a) g))
            = (((P.leadingCoeff ^ g.natDegree : ℂ) *
                Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g)) +
                  ((P.leadingCoeff ^ g.natDegree : ℂ) *
                    Finset.sum (nonzeroSumSubsets a) (fun S ↦ aeval (S.sum a) g))) -
                ((P.leadingCoeff ^ g.natDegree : ℂ) *
                  Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g)) := by
                    ring
        _ = ((P.leadingCoeff ^ g.natDegree : ℂ) *
              Finset.sum ((Finset.univ : Finset (Fin n)).powerset) (fun S ↦ aeval (S.sum a) g)) -
                ((P.leadingCoeff ^ g.natDegree : ℂ) *
                  Finset.sum (zeroSumSubsets a) (fun S ↦ aeval (S.sum a) g)) := by
                    rw [← hsplit]
        _ = ((Z : ℂ) - (Z0 : ℂ)) := by rw [hZ, hZ0]
        _ = ((Z - Z0 : ℤ) : ℂ) := by norm_num
    · simpa using Nat.le_succ g.natDegree

end
