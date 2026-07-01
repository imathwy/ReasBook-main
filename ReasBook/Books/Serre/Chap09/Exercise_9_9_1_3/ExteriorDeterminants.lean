import Serre.Chap09.Exercise_9_9_1_3.PrincipalMinors

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse
    (A : V →ₗ[k] V) (n : ℕ) :
    LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A) =
      (((-A).charpoly.reverse : Polynomial k).coeff n) := by
  cases n with
  | zero =>
      -- Degree `0` is the scalar owner: both sides are the constant term `1`.
      rw [trace_exteriorPower_map_zero]
      simp [Polynomial.coeff_zero_reverse, LinearMap.charpoly_monic]
  | succ n =>
      cases n with
      | zero =>
          -- Degree `1` is the ordinary trace term.
          rw [trace_exteriorPower_map_one]
          let b := Module.Free.chooseBasis k V
          rw [LinearMap.trace_eq_matrix_trace k b, ← LinearMap.charpoly_toMatrix (-A) b,
            Matrix.reverse_charpoly, Matrix.coeff_charpolyRev_eq_neg_trace]
          simp
      | succ n =>
          by_cases hle : n.succ.succ ≤ Module.finrank k V
          · have htraceSum :=
              trace_exteriorPower_map_eq_sum_principal_submatrix_det (A := A) (n := n.succ.succ)
            let b : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
            have hcoeffBlocks :=
              coeff_det_one_add_X_smul_eq_sum_principal_minor_det
                (M := LinearMap.toMatrix b b A) (m := n.succ.succ)
            have hnegM : LinearMap.toMatrix b b (-A) = -LinearMap.toMatrix b b A := by
              -- `toMatrix` is additive, so negating the operator negates every matrix entry.
              ext i j
              simp [LinearMap.toMatrix_apply]
            -- The high-degree branch is now exactly the determinant coefficient formula for the
            -- matrix model of `A`.
            calc
              LinearMap.trace k (⋀[k]^n.succ.succ V) (exteriorPower.map n.succ.succ A)
                  = ∑ s : Set.powersetCard (Fin (Module.finrank k V)) n.succ.succ,
                      Matrix.det (Matrix.of fun i j ↦
                        (LinearMap.toMatrix b b A) ((Set.powersetCard.ofFinEmbEquiv.symm s) i)
                          ((Set.powersetCard.ofFinEmbEquiv.symm s) j) :
                            Matrix (Fin n.succ.succ) (Fin n.succ.succ) k) := by
                        simpa [b] using htraceSum
              _ = (Matrix.det
                    (1 + (Polynomial.X : Polynomial k) •
                      (LinearMap.toMatrix b b A).map Polynomial.C)).coeff n.succ.succ := by
                    symm
                    simpa [b] using hcoeffBlocks
              _ = (((-A).charpoly.reverse : Polynomial k).coeff n.succ.succ) := by
                    rw [← LinearMap.charpoly_toMatrix (-A) b, Matrix.reverse_charpoly, hnegM]
                    simp [Matrix.charpolyRev, sub_eq_add_neg, matrix_map_C_neg]
          · have hlt : Module.finrank k V < n.succ.succ := lt_of_not_ge hle
            rw [trace_exteriorPower_map_eq_zero_of_finrank_lt (A := A) hlt,
              coeff_neg_charpoly_reverse_eq_zero_of_finrank_lt (A := A) hlt]

/-- Helper for Exercise 9-9.1-3: restricting to the line spanned by an eigenvector turns the
operator into scalar multiplication by the eigenvalue. -/
theorem eigenline_restrict_eq_smul_id
    (A : V →ₗ[k] V) {v : V} {μ : k} (hμ : A v = μ • v) :
    A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ) =
      μ •
        (LinearMap.id :
          Submodule.span k ({v} : Set V) →ₗ[k] Submodule.span k ({v} : Set V)) := by
  -- Every vector on the eigenline is a scalar multiple of the chosen eigenvector, so `A`
  -- acts by the same scalar on the whole restricted owner.
  ext w
  rcases Submodule.mem_span_singleton.mp w.2 with ⟨c, hc⟩
  calc
    A (w : V) = A (c • v) := by rw [hc]
    _ = μ • (c • v) := by simp [hμ, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = μ • (w : V) := by rw [hc]

/-- Helper for Exercise 9-9.1-3: the geometric series with ratio `μ` is inverse to the linear
factor `1 - μX`. -/
theorem geometric_series_mul_one_sub_C_mul_X
    (μ : k) :
    PowerSeries.mk (fun n : ℕ ↦ μ ^ n) * (1 - PowerSeries.C μ * PowerSeries.X) = 1 := by
  -- Rescale the universal identity `(1 + X + X^2 + ...) * (1 - X) = 1` by `X ↦ μX`.
  have h :=
    congrArg (PowerSeries.rescale μ) (PowerSeries.mk_one_mul_one_sub_eq_one (S := k))
  have hmk :
      PowerSeries.rescale μ (PowerSeries.mk (1 : ℕ → k)) =
        PowerSeries.mk (fun n : ℕ ↦ μ ^ n) := by
    -- Coefficientwise, rescaling multiplies the constant `1` by `μ^n`.
    ext n
    simp [PowerSeries.coeff_rescale]
  simpa [hmk] using h

/-- Helper for Exercise 9-9.1-3: the characteristic polynomial of the restriction to the line
spanned by a nonzero eigenvector is exactly `X - μ`. -/
theorem charpoly_restrict_eigenline_eq_X_sub_C
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) :
    (A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)).charpoly =
      (Polynomial.X - Polynomial.C μ : Polynomial k) := by
  let W : Submodule k V := Submodule.span k ({v} : Set V)
  -- Rewrite the restricted operator as the scalar homothety `μ • id` on the eigenline.
  calc
    (A.restrict (span_singleton_le_comap_of_eigenvector (A := A) hμ)).charpoly
        = (μ • (1 : W →ₗ[k] W)).charpoly := by
            simpa [W, Module.End.one_eq_id] using
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
    _ = (Polynomial.X - Polynomial.C μ : Polynomial k) := by
          simp

/-- Helper for Exercise 9-9.1-3: the reversal of the linear factor `X - μ` is the determinant
factor `1 - μX` viewed as a power series. -/
theorem reverse_X_sub_C_as_powerSeries
    (μ : k) :
    ((((Polynomial.X - Polynomial.C μ).reverse : Polynomial k) : PowerSeries k)) =
      1 - PowerSeries.C μ * PowerSeries.X := by
  -- Compare coefficients: only degrees `0` and `1` survive for the reverse of a linear
  -- polynomial.
  ext n
  cases n with
  | zero =>
      simp [Polynomial.coeff_zero_reverse]
  | succ n =>
      cases n with
      | zero =>
          simp [Polynomial.coeff_one_reverse]
      | succ n =>
          have hdeg :
              ((Polynomial.X - Polynomial.C μ : Polynomial k).reverse).natDegree <
                n.succ.succ := by
            calc
              ((Polynomial.X - Polynomial.C μ : Polynomial k).reverse).natDegree
                  ≤ (Polynomial.X - Polynomial.C μ : Polynomial k).natDegree :=
                    (Polynomial.X - Polynomial.C μ : Polynomial k).reverse_natDegree_le
              _ = 1 := Polynomial.natDegree_X_sub_C μ
              _ < n.succ.succ := by
                    omega
          simp [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- Helper for Exercise 9-9.1-3: after choosing a nonzero eigenvector, the rescaled exterior trace
series factors into the linear term `1 - μX` times the quotient exterior trace series. -/
theorem rescale_exterior_trace_series_factor_span_singleton_mapQ
    (A : V →ₗ[k] V) {v : V} {μ : k} (hv : v ≠ 0) (hμ : A v = μ • v) :
    let L : Submodule k V := Submodule.span k ({v} : Set V)
    let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
    PowerSeries.rescale (-1 : k)
      (PowerSeries.mk
        (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) =
      (1 - PowerSeries.C μ * PowerSeries.X) *
        PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (⋀[k]^n (V ⧸ L))
                (exteriorPower.map n (L.mapQ L A hL)))) := by
  dsimp
  let L : Submodule k V := Submodule.span k ({v} : Set V)
  let hL : L ≤ L.comap A := span_singleton_le_comap_of_eigenvector (A := A) hμ
  let B : V ⧸ L →ₗ[k] V ⧸ L := L.mapQ L A hL
  have hA :
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A))) =
        (((A).charpoly.reverse : Polynomial k) : PowerSeries k) := by
    -- Identify the exterior trace coefficients with `(-A).charpoly.reverse`, then undo the sign
    -- change `T ↦ -T`.
    calc
      PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A)))
          = PowerSeries.rescale (-1 : k)
              ((((-A).charpoly.reverse : Polynomial k) : PowerSeries k)) := by
                ext n
                simp [trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse]
      _ = (((A).charpoly.reverse : Polynomial k) : PowerSeries k) := by
            simpa using rescale_neg_charpoly_reverse (A := A)
  have hB :
      PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦
            LinearMap.trace k (⋀[k]^n (V ⧸ L))
              (exteriorPower.map n B))) =
        (((B).charpoly.reverse : Polynomial k) : PowerSeries k) := by
    -- The same determinant/exterior comparison applies to the quotient endomorphism.
    calc
      PowerSeries.rescale (-1 : k)
          (PowerSeries.mk
            (fun n ↦
              LinearMap.trace k (⋀[k]^n (V ⧸ L))
                (exteriorPower.map n B)))
          = PowerSeries.rescale (-1 : k)
              ((((-B).charpoly.reverse : Polynomial k) : PowerSeries k)) := by
                ext n
                simp [trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse]
      _ = (((B).charpoly.reverse : Polynomial k) : PowerSeries k) := by
            simpa using rescale_neg_charpoly_reverse (A := B)
  have hchar : A.charpoly = (Polynomial.X - Polynomial.C μ) * B.charpoly := by
    -- Factor the characteristic polynomial through the invariant eigenline and the quotient.
    rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f := A) (W := L) (hW := hL)]
    rw [charpoly_restrict_eigenline_eq_X_sub_C (A := A) (hv := hv) (hμ := hμ)]
  -- Reverse the characteristic-polynomial factorization and rewrite the linear factor as
  -- `1 - μX`.
  calc
    PowerSeries.rescale (-1 : k)
        (PowerSeries.mk
          (fun n ↦ LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A)))
        = (((A).charpoly.reverse : Polynomial k) : PowerSeries k) := hA
    _ = (((((Polynomial.X - Polynomial.C μ) * B.charpoly).reverse : Polynomial k) :
          PowerSeries k)) := by
            rw [hchar]
    _ = ((((B.charpoly).reverse * (Polynomial.X - Polynomial.C μ).reverse : Polynomial k) :
          PowerSeries k)) := by
            rw [Polynomial.reverse_mul_of_domain, mul_comm]
    _ = ((((B.charpoly).reverse : Polynomial k) : PowerSeries k) *
          ((((Polynomial.X - Polynomial.C μ).reverse : Polynomial k) : PowerSeries k))) := by
            simp
    _ = ((((B.charpoly).reverse : Polynomial k) : PowerSeries k) *
          (1 - PowerSeries.C μ * PowerSeries.X)) := by
            rw [reverse_X_sub_C_as_powerSeries]
    _ = (1 - PowerSeries.C μ * PowerSeries.X) *
          PowerSeries.rescale (-1 : k)
            (PowerSeries.mk
              (fun n ↦
                LinearMap.trace k (⋀[k]^n (V ⧸ L))
                  (exteriorPower.map n B))) := by
            rw [hB, mul_comm]

end

end Representation
