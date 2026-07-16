import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_3.AdamsCalculus

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k] [Algebra ℚ k]
variable {G : Type u} [Group G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

local instance : CharZero k := algebraRat.charZero (R := k)

theorem trace_pow_restrict_eigenline
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) (m : ℕ) :
    LinearMap.trace k (Submodule.span k ({v} : Set V))
      ((A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)) ^ (m + 1)) =
        μ ^ (m + 1) := by
  let W : Submodule k V := Submodule.span k ({v} : Set V)
  have hpow :
      ((A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)) ^ (m + 1)) =
        μ ^ (m + 1) • (LinearMap.id : W →ₗ[k] W) := by
    -- Powers preserve the scalar action because the whole restricted operator is already `μ • id`.
    rw [eigenline_restrict_eq_smul_id (A := A) hμ, smul_pow]
    simp
  have hfin : Module.finrank k W = 1 := by
    simpa [W] using finrank_span_singleton hv
  have htrace :
      LinearMap.trace k W (μ ^ (m + 1) • LinearMap.id) =
        μ ^ (m + 1) * (Module.finrank k W : k) := by
    simp [LinearMap.trace_id]
  -- Apply trace to the scalar-identity formula and evaluate `trace id = finrank`.
  exact
    (congrArg (LinearMap.trace k W) hpow).trans <|
      by rw [htrace, hfin]; simp

/-- Helper for Exercise 9-9.1-3: the characteristic roots of the restriction to the line spanned
by an eigenvector consist exactly of the eigenvalue. -/
theorem roots_charpoly_restrict_eigenline
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) :
    ((A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)).charpoly).roots = {μ} := by
  let W : Submodule k V := Submodule.span k ({v} : Set V)
  have hchar :
      (A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)).charpoly =
        (Polynomial.X - Polynomial.C μ : Polynomial k) := by
    -- The restricted action is `μ • id`, so its characteristic polynomial is the one-dimensional
    -- scalar factor `X - μ`.
    calc
      (A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)).charpoly
          = (μ • (1 : W →ₗ[k] W)).charpoly := by
              simpa [Module.End.one_eq_id] using
                congrArg LinearMap.charpoly (eigenline_restrict_eq_smul_id (A := A) hμ)
      _ = (((0 : W →ₗ[k] W) - (-μ) • 1).charpoly) := by
            congr 1
            ext x
            simp
      _ = ((0 : W →ₗ[k] W).charpoly).comp (Polynomial.X + Polynomial.C (-μ)) := by
            simpa using (LinearMap.charpoly_sub_smul (0 : W →ₗ[k] W) (-μ))
      _ = (Polynomial.X : Polynomial k).comp (Polynomial.X - Polynomial.C μ) := by
            rw [LinearMap.charpoly_zero, finrank_span_singleton hv]
            simp [sub_eq_add_neg]
      _ = (Polynomial.X - Polynomial.C μ : Polynomial k) := by simp
  rw [hchar, Polynomial.roots_X_sub_C]

/-- Helper for Exercise 9-9.1-3: over an algebraically closed field, the trace of a positive power
of an endomorphism is the sum of the corresponding powers of the characteristic roots. -/
theorem trace_pow_eq_sum_charpoly_roots_pow_isAlgClosed
    [IsAlgClosed k] {W : Type v} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (B : W →ₗ[k] W) (m : ℕ) :
    LinearMap.trace k W (B ^ (m + 1)) =
      ((B.charpoly.roots.map fun μ ↦ μ ^ (m + 1)).sum) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (W : Type v) [AddCommGroup W] [Module k W] [FiniteDimensional k W],
      Module.finrank k W = n →
      ∀ (B : W →ₗ[k] W) (m : ℕ),
        LinearMap.trace k W (B ^ (m + 1)) =
          ((B.charpoly.roots.map fun μ ↦ μ ^ (m + 1)).sum)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih W _ _ _ hWfin B m
    by_cases hzero : n = 0
    · haveI : Subsingleton W := Module.finrank_zero_iff.mp (hWfin.trans hzero)
      have hB : B = 0 := by
        ext x
        exact Subsingleton.elim _ _
      -- In dimension `0`, both the trace and the root multiset vanish.
      rw [hB]
      simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
      haveI : Nontrivial W := (Module.finrank_pos_iff).1 (by rwa [hWfin])
      obtain ⟨μ, hμ⟩ : ∃ μ : k, Module.End.HasEigenvalue B μ :=
        Module.End.exists_eigenvalue B
      obtain ⟨v, hv⟩ : ∃ v, Module.End.HasEigenvector B μ v := hμ.exists_hasEigenvector
      let L : Submodule k W := Submodule.span k ({v} : Set W)
      have hL :
          L ≤ L.comap B := span_singleton_le_comap_of_eigenvector
            (V := W) (A := B) (hμ := hv.apply_eq_smul)
      have hLfin : Module.finrank k L = 1 := by
        simpa [L] using finrank_span_singleton hv.2
      have hQlt : Module.finrank k (W ⧸ L) < n := by
        have hsum :
            Module.finrank k (W ⧸ L) + Module.finrank k L = n := by
          simpa [hWfin] using
            (Submodule.finrank_quotient_add_finrank (R := k) (M := W) L)
        omega
      have htraceQ :
          LinearMap.trace k (W ⧸ L) ((L.mapQ L B hL) ^ (m + 1)) =
            ((((L.mapQ L B hL).charpoly).roots.map fun ν ↦ ν ^ (m + 1)).sum) := by
        exact
          ih (Module.finrank k (W ⧸ L)) hQlt (W ⧸ L) rfl
            (L.mapQ L B hL) m
      have htraceL :
          LinearMap.trace k L ((B.restrict hL) ^ (m + 1)) = μ ^ (m + 1) := by
        simpa [L] using
          trace_pow_restrict_eigenline
            (V := W) (A := B) (v := v) (μ := μ) hv.2 hv.apply_eq_smul m
      have hrootsL :
          ((B.restrict hL).charpoly).roots = {μ} := by
        simpa [L] using
          roots_charpoly_restrict_eigenline
            (V := W) (A := B) (v := v) (μ := μ) hv.2 hv.apply_eq_smul
      have hroots :
          B.charpoly.roots =
            ((B.restrict hL).charpoly).roots + ((L.mapQ L B hL).charpoly).roots := by
        rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (V := W) (f := B) (W := L) hL,
          Polynomial.roots_mul]
        exact mul_ne_zero
          (LinearMap.charpoly_monic (B.restrict hL)).ne_zero
          (LinearMap.charpoly_monic (L.mapQ L B hL)).ne_zero
      -- Split the trace across the stable line and quotient, then identify the two root multisets.
      calc
        LinearMap.trace k W (B ^ (m + 1))
            = LinearMap.trace k L ((B.restrict hL) ^ (m + 1)) +
                LinearMap.trace k (W ⧸ L) ((L.mapQ L B hL) ^ (m + 1)) := by
                  exact
                    trace_pow_eq_trace_restrict_pow_add_trace_mapQ_pow
                      (V := W) (A := B) (W := L) hL m
        _ = μ ^ (m + 1) +
              ((((L.mapQ L B hL).charpoly).roots.map fun ν ↦ ν ^ (m + 1)).sum) := by
                rw [htraceL, htraceQ]
        _ = ((B.charpoly.roots.map fun ν ↦ ν ^ (m + 1)).sum) := by
              rw [hroots, Multiset.map_add, Multiset.sum_add, hrootsL]
              simp
  simpa using hP (Module.finrank k W) W rfl B m

/-- Helper for Exercise 9-9.1-3: over an algebraically closed field, Newton's identity for the
reversed characteristic polynomial is obtained by evaluating the universal elementary-symmetric
recurrence on the characteristic roots of `-A`. -/
theorem neg_charpoly_reverse_coeff_newton_isAlgClosed
    [IsAlgClosed k] (A : V →ₗ[k] V) (n : ℕ) :
    ((n + 1 : k) * ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1)))) =
      Finset.sum (Finset.antidiagonal n) fun p ↦
        ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
          (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1)))) := by
  classical
  let r : Multiset k := ((-A).charpoly).roots
  have hesymm :
      ∀ m : ℕ,
        (MvPolynomial.eval (fun i : r.ToType ↦ i.1))
            (MvPolynomial.esymm r.ToType k m) =
          r.esymm m := by
    intro m
    -- Route correction: use the dedicated `MvPolynomial`-to-`Multiset` adapter before applying
    -- the root-multiset Newton identity.
    simpa [r] using mvPolynomial_eval_esymm_to_multiset_esymm (k := k) (r := r) m
  have hNewton :
      ((n + 1 : k) * r.esymm (n + 1)) =
        (-1 : k) ^ (n + 2) *
          ∑ x ∈ Finset.antidiagonal n,
            (-1 : k) ^ x.1 * ((∑ i : r.ToType, i.1 ^ (x.2 + 1)) * r.esymm x.1) := by
    -- Evaluate the universal Newton identity on the root multiset, viewed as a finite type with
    -- multiplicity.
    simpa [r, MvPolynomial.psum, hesymm] using
      (eval_esymm_newton_family (k := k) (σ := r.ToType) (f := fun i : r.ToType ↦ i.1) n)
  have htrace (m : ℕ) :
      ∑ i : r.ToType, i.1 ^ (m + 1) =
        (-1 : k) ^ (m + 1) * LinearMap.trace k V (A ^ (m + 1)) := by
    -- Replace the explicit root sum by the trace of `(-A)^(m+1)`, then pull out the scalar sign.
    calc
      ∑ i : r.ToType, i.1 ^ (m + 1) = (r.map fun μ ↦ μ ^ (m + 1)).sum := by
        symm
        exact multiset_map_sum_eq_sum_toType (m := r) (f := fun μ ↦ μ ^ (m + 1))
      _ = LinearMap.trace k V ((-A) ^ (m + 1)) := by
        symm
        simpa [r] using
          (trace_pow_eq_sum_charpoly_roots_pow_isAlgClosed (k := k) (W := V) (B := -A) m)
      _ = (-1 : k) ^ (m + 1) * LinearMap.trace k V (A ^ (m + 1)) := by
        -- `-A` is `(-1) • A`, so its positive powers contribute a scalar factor `(-1)^(m+1)`.
        calc
          LinearMap.trace k V ((-A) ^ (m + 1))
              = LinearMap.trace k V (((-1 : k) • A) ^ (m + 1)) := by simp
          _ = LinearMap.trace k V (((-1 : k) ^ (m + 1)) • (A ^ (m + 1))) := by
                rw [smul_pow]
          _ = (-1 : k) ^ (m + 1) * LinearMap.trace k V (A ^ (m + 1)) := by
                simpa using
                  (LinearMap.trace_smul ((-1 : k) ^ (m + 1)) (A ^ (m + 1)))
  have hcoeff (m : ℕ) :
      ((((-A).charpoly.reverse : Polynomial k).coeff m)) = (-1 : k) ^ m * r.esymm m := by
    -- The reversed characteristic-polynomial coefficients are the signed elementary symmetric
    -- functions of the roots.
    simpa [r] using
      (neg_charpoly_reverse_coeff_eq_signed_esymm_roots (k := k) (V := V) (A := A) m)
  have hsign0 : (-1 : k) ^ (n + 1) * (-1 : k) ^ (n + 2) = -1 := by
    -- The two consecutive sign powers collapse to a single minus sign.
    rw [← pow_add]
    have hodd : n + 1 + (n + 2) = 2 * (n + 1) + 1 := by
      omega
    rw [hodd, pow_add, pow_mul]
    simp
  -- Multiply the universal identity by the extra sign converting `e_m` into the reversed
  -- characteristic coefficient, then normalize each term using the trace identity above.
  calc
    ((n + 1 : k) * ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1))))
        = (-1 : k) ^ (n + 1) * ((n + 1 : k) * r.esymm (n + 1)) := by
            rw [hcoeff (n + 1)]
            ring
    _ = (-1 : k) ^ (n + 1) *
          ((-1 : k) ^ (n + 2) *
            ∑ x ∈ Finset.antidiagonal n,
              (-1 : k) ^ x.1 * ((∑ i : r.ToType, i.1 ^ (x.2 + 1)) * r.esymm x.1)) := by
            rw [hNewton]
    _ = Finset.sum (Finset.antidiagonal n) fun p ↦
          ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
            (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1)))) := by
          let S : k :=
            ∑ x ∈ Finset.antidiagonal n,
              (-1 : k) ^ x.1 * ((∑ i : r.ToType, i.1 ^ (x.2 + 1)) * r.esymm x.1)
          have hsign :
              (-1 : k) ^ (n + 1) * ((-1 : k) ^ (n + 2) * S) = -S := by
            calc
              (-1 : k) ^ (n + 1) * ((-1 : k) ^ (n + 2) * S)
                  = (((-1 : k) ^ (n + 1) * (-1 : k) ^ (n + 2)) * S) := by ring
              _ = (-1 : k) * S := by rw [hsign0]
              _ = -S := by simp
          rw [show
              (-1 : k) ^ (n + 1) *
                  ((-1 : k) ^ (n + 2) *
                    ∑ x ∈ Finset.antidiagonal n,
                      (-1 : k) ^ x.1 *
                        ((∑ i : r.ToType, i.1 ^ (x.2 + 1)) * r.esymm x.1)) =
                -S by simpa [S] using hsign]
          have hnegS :
              -S =
                ∑ p ∈ Finset.antidiagonal n,
                  -(((-1 : k) ^ p.1) * ((∑ i : r.ToType, i.1 ^ (p.2 + 1)) * r.esymm p.1)) := by
            simp [S]
          rw [hnegS]
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [hcoeff p.1, htrace p.2]
          -- The remaining sign bookkeeping is a single scalar identity in the coefficient field.
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (show
              -1 *
                  (((-1 : k) ^ p.1) *
                    (((-1 : k) ^ (p.2 + 1) * LinearMap.trace k V (A ^ (p.2 + 1))) *
                      r.esymm p.1)) =
                (((-1 : k) ^ p.1 * r.esymm p.1) *
                  (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1)))) by
              rw [pow_succ]
              ring)

theorem neg_charpoly_reverse_coeff_newton
    (A : V →ₗ[k] V) (n : ℕ) :
    ((n + 1 : k) * ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1)))) =
      Finset.sum (Finset.antidiagonal n) fun p ↦
        ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
          (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1)))) := by
  -- Route correction: descend the algebraically closed Newton identity along base change to
  -- `AlgebraicClosure k` once the sign-normalized algebraically closed statement is available.
  let K := AlgebraicClosure k
  have hK :
      ((n + 1 : K) *
          ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff (n + 1)))) =
        Finset.sum (Finset.antidiagonal n) fun p ↦
          ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff p.1) *
            (((-1 : K) ^ p.2) *
              LinearMap.trace K (TensorProduct k K V) ((A.baseChange K) ^ (p.2 + 1)))) := by
    -- The algebraically closed theorem applies directly after base changing `A`.
    simpa [K] using
      (neg_charpoly_reverse_coeff_newton_isAlgClosed
        (k := K) (V := TensorProduct k K V) (A := A.baseChange K) n)
  apply (FaithfulSMul.algebraMap_injective k K)
  -- Map the target identity into `K`; every term becomes the corresponding base-changed term.
  calc
    algebraMap k K
        (((n + 1 : k) * ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1)))))
        = ((n + 1 : K) *
            ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff (n + 1)))) := by
              calc
                algebraMap k K
                    (((n + 1 : k) * ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1)))))
                    = (algebraMap k K (n + 1 : k)) *
                        algebraMap k K ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1))) := by
                          rw [map_mul]
                _ = ((n + 1 : K) *
                      algebraMap k K ((((-A).charpoly.reverse : Polynomial k).coeff (n + 1)))) := by
                      simp
                _ = ((n + 1 : K) *
                      ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff (n + 1)))) := by
                      rw [coeff_neg_charpoly_reverse_baseChange (A := A) (m := n + 1)]
    _ = Finset.sum (Finset.antidiagonal n) fun p ↦
          ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff p.1) *
            (((-1 : K) ^ p.2) *
              LinearMap.trace K (TensorProduct k K V) ((A.baseChange K) ^ (p.2 + 1)))) := by
            exact hK
    _ = algebraMap k K
          (Finset.sum (Finset.antidiagonal n) fun p ↦
            ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
              (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1))))) := by
            calc
              Finset.sum (Finset.antidiagonal n) (fun p ↦
                  ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff p.1) *
                    (((-1 : K) ^ p.2) *
                      LinearMap.trace K (TensorProduct k K V) ((A.baseChange K) ^ (p.2 + 1)))))
                  = Finset.sum (Finset.antidiagonal n) (fun p ↦
                      algebraMap k K
                        ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
                          (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1))))) := by
                        refine Finset.sum_congr rfl ?_
                        intro p hp
                        -- Each summand is transported coefficientwise and tracewise through base
                        -- change.
                        symm
                        calc
                          algebraMap k K
                              ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
                                (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1))))
                              = (algebraMap k K ((((-A).charpoly.reverse : Polynomial k).coeff p.1))) *
                                  ((algebraMap k K (((-1 : k) ^ p.2))) *
                                    algebraMap k K (LinearMap.trace k V (A ^ (p.2 + 1)))) := by
                                      rw [map_mul, map_mul]
                          _ = (algebraMap k K ((((-A).charpoly.reverse : Polynomial k).coeff p.1))) *
                                (((-1 : K) ^ p.2) *
                                  algebraMap k K (LinearMap.trace k V (A ^ (p.2 + 1)))) := by
                                rw [map_pow, map_neg, map_one]
                          _ = ((((-(A.baseChange K)).charpoly.reverse : Polynomial K).coeff p.1) *
                                (((-1 : K) ^ p.2) *
                                  LinearMap.trace K (TensorProduct k K V)
                                    ((A.baseChange K) ^ (p.2 + 1)))) := by
                                rw [coeff_neg_charpoly_reverse_baseChange (A := A) (m := p.1),
                                  trace_pow_baseChange (A := A) (m := p.2)]
              _ = algebraMap k K
                    (Finset.sum (Finset.antidiagonal n) fun p ↦
                      ((((-A).charpoly.reverse : Polynomial k).coeff p.1) *
                        (((-1 : k) ^ p.2) * LinearMap.trace k V (A ^ (p.2 + 1))))) := by
                    rw [map_sum]

end

end Representation
