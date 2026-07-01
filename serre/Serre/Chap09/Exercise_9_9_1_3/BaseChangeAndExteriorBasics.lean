import Mathlib
import Serre.Chap11.Theorem_11_11_2_1
import Serre.RepresentationTheory.SymmetricExterior
import Serre.Chap09.Exercise_9_9_1_3.FiniteSetReindexing

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

theorem trace_pow_eq_trace_restrict_pow_add_trace_mapQ_pow
    (A : V →ₗ[k] V) (W : Submodule k V) (hW : W ≤ W.comap A) (m : ℕ) :
    LinearMap.trace k V (A ^ (m + 1)) =
      LinearMap.trace k W ((A.restrict hW) ^ (m + 1)) +
        LinearMap.trace k (V ⧸ W) ((W.mapQ W A hW) ^ (m + 1)) := by
  let hWpow : W ≤ W.comap (A ^ (m + 1)) := W.le_comap_pow_of_le_comap hW (m + 1)
  -- Apply the existing trace decomposition to `A^(m+1)` and then rewrite the restricted and
  -- quotient powers into the corresponding powers of the induced maps.
  calc
    LinearMap.trace k V (A ^ (m + 1))
        = LinearMap.trace k W ((A ^ (m + 1)).restrict hWpow) +
            LinearMap.trace k (V ⧸ W) (W.mapQ W (A ^ (m + 1)) hWpow) := by
              exact
                trace_eq_trace_restrict_add_trace_mapQ
                  (f := A ^ (m + 1)) (W := W) (hW := hWpow)
    _ = LinearMap.trace k W ((A.restrict hW) ^ (m + 1)) +
          LinearMap.trace k (V ⧸ W) ((W.mapQ W A hW) ^ (m + 1)) := by
          rw [Module.End.pow_restrict, Submodule.mapQ_pow]
/-- Helper for Exercise 9-9.1-3: after base change to the algebraic closure, the reversed
characteristic polynomial of `-A` is obtained by mapping coefficients through the algebra map. -/
theorem neg_charpoly_reverse_baseChange
    (A : V →ₗ[k] V) :
    (((-(A.baseChange (AlgebraicClosure k))).charpoly.reverse :
        Polynomial (AlgebraicClosure k))) =
      Polynomial.map (algebraMap k (AlgebraicClosure k))
        (((-A).charpoly.reverse : Polynomial k)) := by
  -- Route correction: descend coefficient identities from a polynomial equality first, and only
  -- then extract the needed coefficients.
  rw [show -(A.baseChange (AlgebraicClosure k)) =
      LinearMap.baseChange (AlgebraicClosure k) (-A) by simp]
  rw [LinearMap.charpoly_baseChange]
  symm
  exact
    polynomial_reverse_map (f := algebraMap k (AlgebraicClosure k))
      (hf := FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)) ((-A).charpoly)
/-- Helper for Exercise 9-9.1-3: substituting into `evalNegHom` is the same as substituting the
negated series. -/
theorem subst_evalNeg_eq_subst_neg
    {A : Type*} [CommRing A] [Algebra ℚ A] (f g : PowerSeries A)
    (hg : PowerSeries.HasSubst g) :
    (PowerSeries.evalNegHom f).subst g = f.subst (-g) := by
  -- Route correction: rewrite `evalNegHom` as rescaling by `-1`, then compose substitutions.
  rw [show PowerSeries.evalNegHom f = PowerSeries.rescale (-1 : A) f by
    ext n
    simp [PowerSeries.evalNegHom, PowerSeries.coeff_rescale]]
  rw [PowerSeries.rescale_eq_subst]
  rw [PowerSeries.subst_comp_subst_apply (ha := PowerSeries.HasSubst.smul_X' (-1 : A))
    (hb := hg)]
  -- The inner substitution sends `-X` to `-g`.
  congr 1
  rw [PowerSeries.subst_smul hg (-1 : A), PowerSeries.subst_X hg]
  simp
/-- Helper for Exercise 9-9.1-3: on the `0`th exterior power, every endomorphism acts as the
identity, so the trace is `1`. -/
theorem trace_exteriorPower_map_zero
    (A : V →ₗ[k] V) :
    LinearMap.trace k (⋀[k]^0 V) (exteriorPower.map 0 A) = 1 := by
  let e : ⋀[k]^0 V ≃ₗ[k] k := exteriorPower.zeroEquiv k V
  have hconj : e.conj (exteriorPower.map 0 A) = (LinearMap.id : k →ₗ[k] k) := by
    -- Naturality of `zeroEquiv` identifies the `0`th exterior-power action with the identity map.
    apply LinearMap.ext
    intro y
    have h :=
      congrArg (fun f : ⋀[k]^0 V →ₗ[k] k => f (e.symm y))
        (exteriorPower.zeroEquiv_naturality (R := k) (M := V) (N := V) A)
    simpa [LinearEquiv.conj_apply, e] using h
  -- Conjugate maps have the same trace, so we can compute on the scalar owner `k`.
  rw [← LinearMap.trace_conj' (exteriorPower.map 0 A) e, hconj, LinearMap.trace_id]
  simp
/-- Helper for Exercise 9-9.1-3: summing a mapped multiset agrees with summing the same function
over the multiplicity-aware finite type attached to that multiset. -/
theorem multiset_map_sum_eq_sum_toType
    {α : Type*} [DecidableEq α] (m : Multiset α) (f : α → k) :
    (m.map f).sum = ∑ x : m.ToType, f x.1 := by
  -- Route correction: replace the old roots-to-powers bookkeeping by the canonical `ToType`
  -- enumeration of a multiset, which keeps multiplicities explicit.
  calc
    (m.map f).sum = (m.toEnumFinset.val.map fun x ↦ f x.1).sum := by
      -- Enumerating the multiset and then mapping `f` gives the same mapped multiset.
      nth_rewrite 1 [← Multiset.map_toEnumFinset_fst (m := m)]
      rw [Multiset.map_map]
      rfl
    _ = ∑ x : m.ToType, f x.1 := by
      -- `toEnumFinset` and `ToType` are equivalent multiplicity-aware enumerations.
      simpa using (Multiset.sum_toEnumFinset (m := m) (f := fun a _ ↦ f a))
/-- Helper for Exercise 9-9.1-3: on the `1`st exterior power, the induced endomorphism is
conjugate to the original endomorphism. -/
theorem trace_exteriorPower_map_one
    (A : V →ₗ[k] V) :
    LinearMap.trace k (⋀[k]^1 V) (exteriorPower.map 1 A) = LinearMap.trace k V A := by
  let e : ⋀[k]^1 V ≃ₗ[k] V := exteriorPower.oneEquiv k V
  have hconj : e.conj (exteriorPower.map 1 A) = A := by
    -- Naturality of `oneEquiv` turns the first exterior-power action back into `A`.
    apply LinearMap.ext
    intro y
    have h :=
      congrArg (fun f : ⋀[k]^1 V →ₗ[k] V => f (e.symm y))
        (exteriorPower.oneEquiv_naturality (R := k) (M := V) (N := V) A)
    simpa [LinearEquiv.conj_apply, e] using h
  -- Trace is invariant under conjugation.
  rw [← LinearMap.trace_conj' (exteriorPower.map 1 A) e, hconj]
/-- Helper for Exercise 9-9.1-3: evaluating the universal elementary symmetric polynomial on the
multiplicity-aware finite type attached to a multiset recovers the corresponding multiset
elementary symmetric sum. -/
theorem mvPolynomial_eval_esymm_to_multiset_esymm
    [DecidableEq k]
    (r : Multiset k) (m : ℕ) :
    (MvPolynomial.eval (fun i : r.ToType ↦ i.1))
        (MvPolynomial.esymm r.ToType k m) =
      r.esymm m := by
  -- Replace the universal elementary symmetric polynomial by the multiset version indexed by the
  -- same multiplicity-aware finite type.
  simpa [MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.aeval_esymm_eq_multiset_esymm
      (R := k) (S := k) (σ := r.ToType) m (fun i : r.ToType ↦ i.1))
/-- Helper for Exercise 9-9.1-3: after base change to the algebraic closure, the reversed
characteristic-polynomial coefficients are obtained by mapping the original coefficients. -/
theorem coeff_neg_charpoly_reverse_baseChange
    (A : V →ₗ[k] V) (m : ℕ) :
    (((-(A.baseChange (AlgebraicClosure k))).charpoly.reverse :
        Polynomial (AlgebraicClosure k)).coeff m) =
      algebraMap k (AlgebraicClosure k)
        ((((-A).charpoly.reverse : Polynomial k).coeff m)) := by
  -- Extract coefficients from the polynomial-level base-change identity.
  simpa [Polynomial.coeff_map] using
    congrArg
      (fun p : Polynomial (AlgebraicClosure k) => p.coeff m)
      (neg_charpoly_reverse_baseChange (A := A))
/-- Helper for Exercise 9-9.1-3: evaluating the universal Newton identity on a finite family of
scalars produces the scalar recurrence needed for the root-multiset computation. -/
theorem eval_esymm_newton_family
    {σ : Type*} [Fintype σ] (f : σ → k) (n : ℕ) :
    ((n + 1 : k) * (MvPolynomial.eval f) (MvPolynomial.esymm σ k (n + 1))) =
      (-1 : k) ^ (n + 2) *
        ∑ x ∈ Finset.antidiagonal n,
          (-1 : k) ^ x.1 *
            ((∑ i, f i ^ (x.2 + 1)) * (MvPolynomial.eval f) (MvPolynomial.esymm σ k x.1)) := by
  -- Specialize the universal Newton identity to the scalar family `f` by evaluating every
  -- symmetric polynomial at the coordinates of `f`.
  simpa [MvPolynomial.psum, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ k (n + 1))
/-- Helper for Exercise 9-9.1-3: base change to the algebraic closure preserves the trace of every
positive power of an endomorphism. -/
theorem trace_pow_baseChange
    (A : V →ₗ[k] V) (m : ℕ) :
    LinearMap.trace (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) V)
      ((A.baseChange (AlgebraicClosure k)) ^ (m + 1)) =
        algebraMap k (AlgebraicClosure k) (LinearMap.trace k V (A ^ (m + 1))) := by
  -- First rewrite the power of the base-changed map as the base change of the power, then apply
  -- the standard trace-compatibility theorem.
  rw [← LinearMap.baseChange_pow (R := k) (A := AlgebraicClosure k) (M := V) (f := A)
      (n := m + 1)]
  simpa using
    (LinearMap.trace_baseChange (f := A ^ (m + 1)) (A := AlgebraicClosure k))
/-- Helper for Exercise 9-9.1-3: the span of an eigenvector is stable under the operator. -/
theorem span_singleton_le_comap_of_eigenvector
    (A : V →ₗ[k] V) {v : V} {μ : k} (hμ : A v = μ • v) :
    Submodule.span k ({v} : Set V) ≤ (Submodule.span k ({v} : Set V)).comap A := by
  intro w hw
  rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
  -- The image of a scalar multiple of an eigenvector is again a scalar multiple of that vector.
  change A (c • v) ∈ Submodule.span k ({v} : Set V)
  simpa [hμ, smul_smul] using
    Submodule.smul_mem (Submodule.span k ({v} : Set V)) (c * μ)
      (Submodule.subset_span (by simp))
/-- Helper for Exercise 9-9.1-3: if `n` is larger than the dimension of `V`, the `n`th exterior
power is zero-dimensional, so the induced trace vanishes. -/
theorem trace_exteriorPower_map_eq_zero_of_finrank_lt
    (A : V →ₗ[k] V) {n : ℕ} (hn : Module.finrank k V < n) :
    LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n A) = 0 := by
  have hfinrank : Module.finrank k (⋀[k]^n V) = 0 := by
    simpa [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hn]
  haveI : Subsingleton (⋀[k]^n V) := Module.finrank_zero_iff.mp hfinrank
  -- In a zero-dimensional space, every linear map is zero.
  have hzero : exteriorPower.map n A = 0 := Subsingleton.elim _ _
  simpa [hzero]
/-- Helper for Exercise 9-9.1-3: the trace of a scalar homothety on a symmetric power is the
expected scalar `μ^n` times the dimension of that symmetric power. -/
theorem trace_symmetricPower_map_smul_id
    (n : ℕ) (μ : k) :
    LinearMap.trace k (SymmetricPower k (Fin n) V)
        (SymmetricPower.map n (μ • (LinearMap.id : V →ₗ[k] V))) =
      μ ^ n * Module.finrank k (SymmetricPower k (Fin n) V) := by
  -- Rewrite the induced map as a scalar multiple of the identity, then compute its trace.
  rw [symmetricPower_map_smul_id (V := V) (n := n) (μ := μ)]
  rw [(LinearMap.trace k (SymmetricPower k (Fin n) V)).map_smul, LinearMap.trace_id]
  simp [smul_eq_mul]
/-- Helper for Exercise 9-9.1-3: pointwise evaluation of character-valued power series commutes
with rescaling the variable by a scalar in the coefficient field. -/
theorem map_eval_rescale
    (f : PowerSeries (G → k)) (a : k) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) (PowerSeries.rescale (fun _ ↦ a) f) =
      PowerSeries.rescale a (PowerSeries.map (Pi.evalRingHom _ s) f) := by
  -- Compare coefficients directly: both operations multiply degree `n` by the same scalar `a ^ n`
  -- and then evaluate the resulting function at `s`.
  ext n
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
/-- Helper for Exercise 9-9.1-3: evaluating a polynomial at the power-series variable `-X`
agrees with first composing the polynomial with `-X` and then coercing to power series. -/
theorem aeval_neg_X_coe_eq_comp (p : Polynomial k) :
    Polynomial.aeval (((-Polynomial.X : Polynomial k) : PowerSeries k)) p =
      ((p.comp (-Polynomial.X) : Polynomial k) : PowerSeries k) := by
  -- Transport polynomial evaluation across the canonical polynomial-to-power-series algebra map.
  simpa [Polynomial.comp_eq_aeval] using
    congrArg (fun h : Polynomial k →ₐ[k] PowerSeries k => h p)
      (Polynomial.aeval_algHom (Polynomial.coeToPowerSeries.algHom k) (-Polynomial.X))
/-- Helper for Exercise 9-9.1-3: coefficients above the dimension of `V` vanish in the reversed
characteristic polynomial. -/
theorem coeff_neg_charpoly_reverse_eq_zero_of_finrank_lt
    (A : V →ₗ[k] V) {n : ℕ} (hn : Module.finrank k V < n) :
    (((-A).charpoly.reverse : Polynomial k).coeff n) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hdeg : ((-A).charpoly).natDegree < n := by
    simpa [LinearMap.charpoly_natDegree] using hn
  exact lt_of_le_of_lt ((-A).charpoly.reverse_natDegree_le) hdeg
/-- Helper for Exercise 9-9.1-3: the determinant-model series coming from a reversed characteristic
polynomial always has constant coefficient `1`, hence is invertible as a power series. -/
theorem constantCoeff_charpoly_reverse_powerSeries
    (A : V →ₗ[k] V) :
    PowerSeries.constantCoeff ((((A).charpoly.reverse : Polynomial k) : PowerSeries k)) = 1 := by
  -- The constant coefficient of the reversed characteristic polynomial is its leading coefficient,
  -- and characteristic polynomials are monic.
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Polynomial.coeff_zero_reverse, LinearMap.charpoly_monic]

end

end Representation
