import Mathlib
import stacks_project.Chap05.Lemma_5_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix MvPolynomial PrimeSpectrum

universe u

noncomputable section

section

variable (k : Type u) [CommRing k]

private def nodeCoordinateRingIdeal :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {X 0 * X 1}

/-- The coordinate ring `k[x, y] / (xy)` of the node from Example 10.35.23. -/
abbrev nodeCoordinateRing :=
  MvPolynomial (Fin 2) k ⧸ nodeCoordinateRingIdeal k

/- Layering for this item:
* primary domain: affine schemes through prime spectra of quotient coordinate rings;
* source-facing: the named irreducible components of the two affine schemes in Example 10.35.23;
* core/canonical owner abstraction: `PrimeSpectrum.zeroLocus` and `irreducibleComponents`,
  together with `Matrix.mvPolynomialX` for the generic matrix coordinates;
* primitive local data: the two quotient coordinate rings and the defining ideals cutting out the
  relevant closed loci;
* derived API: the named closed subsets attached to those defining equations.

Same-domain owner sampling used here:
* `irreducibleComponents` and `irreducibleComponents_eq_maximals_closed`
  (`stacks_project/Chap05/Definition_5_8_1.lean`);
* `minimalPrimes.equivIrreducibleComponents` (`stacks_project/Chap10/Lemma_10_26_1.lean`);
* `PrimeSpectrum.zeroLocus`;
* `Matrix.mvPolynomialX`.
-/

private def nodeCoordinate (i : Fin 2) : nodeCoordinateRing k :=
  Ideal.Quotient.mk (nodeCoordinateRingIdeal k) (X i)

/-- The `x`-axis in `Spec(k[x, y] / (xy))`, i.e. the closed subset cut out by `y = 0`. -/
def nodeXAxis : Set (PrimeSpectrum (nodeCoordinateRing k)) :=
  zeroLocus ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))

/-- The `y`-axis in `Spec(k[x, y] / (xy))`, i.e. the closed subset cut out by `x = 0`. -/
def nodeYAxis : Set (PrimeSpectrum (nodeCoordinateRing k)) :=
  zeroLocus ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))

private def matrixProductPolynomialMatrix (s : Fin 2) :
    Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  (mvPolynomialX (Fin 2) (Fin 2) k).map (rename fun ij ↦ (s, ij.1, ij.2))

private def matrixProductCoordinateRingIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 0 * matrixProductPolynomialMatrix k 1) ij.1 ij.2

/-- The coordinate ring of pairs of `2 × 2` matrices satisfying `XY = 0`. -/
abbrev matrixProductCoordinateRing :=
  MvPolynomial (Fin 2 × Fin 2 × Fin 2) k ⧸ matrixProductCoordinateRingIdeal k

private def matrixProductGenericMatrix (s : Fin 2) :
    Matrix (Fin 2) (Fin 2) (matrixProductCoordinateRing k) :=
  (matrixProductPolynomialMatrix k s).map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))

private def matrixProductEntryIdeal (s : Fin 2) :
    Ideal (matrixProductCoordinateRing k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦ (matrixProductGenericMatrix k s) ij.1 ij.2

private def matrixProductDeterminantIdeal : Ideal (matrixProductCoordinateRing k) :=
  Ideal.span <| Set.range fun s : Fin 2 ↦ (matrixProductGenericMatrix k s).det

/-- The closed subset of `Spec(R)` for `R = matrixProductCoordinateRing k` defined by `Y = 0`. -/
def matrixProductYZeroComponent : Set (PrimeSpectrum (matrixProductCoordinateRing k)) :=
  zeroLocus (matrixProductEntryIdeal k 1 : Set (matrixProductCoordinateRing k))

/-- The closed subset of `Spec(R)` for `R = matrixProductCoordinateRing k` defined by
`det X = 0` and `det Y = 0`. -/
def matrixProductDeterminantZeroComponent : Set (PrimeSpectrum (matrixProductCoordinateRing k)) :=
  zeroLocus (matrixProductDeterminantIdeal k : Set (matrixProductCoordinateRing k))

/-- The closed subset of `Spec(R)` for `R = matrixProductCoordinateRing k` defined by `X = 0`. -/
def matrixProductXZeroComponent : Set (PrimeSpectrum (matrixProductCoordinateRing k)) :=
  zeroLocus (matrixProductEntryIdeal k 0 : Set (matrixProductCoordinateRing k))

end

section

variable (k : Type u) [CommRing k] [IsDomain k]

/-- Helper for Example 10.35.23: the defining relation of the node quotient is `xy = 0`. -/
private theorem node_coordinate_mul_eq_zero :
    nodeCoordinate k 0 * nodeCoordinate k 1 = 0 := by
  -- Unfold the quotient coordinates and use the defining generator of the quotient ideal.
  change Ideal.Quotient.mk (nodeCoordinateRingIdeal k) (X 0 * X 1) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- Helper for Example 10.35.23: the relation ideal `(xy)` is contained in each coordinate-axis
ideal of the polynomial ring. -/
private theorem nodeCoordinateRingIdeal_le_axisIdeal (i : Fin 2) :
    nodeCoordinateRingIdeal k ≤ Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k)) := by
  -- The single generator `xy` is divisible by either coordinate variable.
  rw [nodeCoordinateRingIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  fin_cases i
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- Helper for Example 10.35.23: after quotienting by `(xy)`, the image of the coordinate-axis
ideal is exactly the principal ideal generated by the corresponding coordinate class. -/
private theorem node_axis_ideal_map_eq (i : Fin 2) :
    Ideal.map (Ideal.Quotient.mk (nodeCoordinateRingIdeal k))
      (Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k))) =
      Ideal.span ({nodeCoordinate k i} : Set (nodeCoordinateRing k)) := by
  -- Mapping the singleton generator through the quotient map gives the corresponding quotient
  -- coordinate.
  rw [Ideal.map_span]
  simpa [nodeCoordinate]

/-- Helper for Example 10.35.23: the image of each coordinate-axis ideal in the node coordinate
ring is prime. -/
private theorem node_axis_ideal_isPrime (i : Fin 2) :
    (Ideal.span ({nodeCoordinate k i} : Set (nodeCoordinateRing k))).IsPrime := by
  have hp : (Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k))).IsPrime := by
    -- In the polynomial ring, each coordinate variable is a prime element.
    have hXi : (X i : MvPolynomial (Fin 2) k) ≠ 0 := by
      simpa using (MvPolynomial.X_ne_zero (σ := Fin 2) (R := k) i)
    exact (Ideal.span_singleton_prime hXi).2
      (MvPolynomial.X_prime (R := k) (σ := Fin 2) (i := i))
  have hle :
      nodeCoordinateRingIdeal k ≤ Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k)) := by
    simpa using nodeCoordinateRingIdeal_le_axisIdeal (k := k) i
  let p : Ideal (MvPolynomial (Fin 2) k) :=
    Ideal.span ({X i} : Set (MvPolynomial (Fin 2) k))
  let _ : p.IsPrime := hp
  have hmap : (Ideal.map (Ideal.Quotient.mk (nodeCoordinateRingIdeal k)) p).IsPrime := by
    exact Ideal.isPrime_map_quotientMk_of_isPrime hle
  simpa [p, node_axis_ideal_map_eq (k := k) i] using hmap

/-- Helper for Example 10.35.23: distinct variables of `k[x, y]` do not lie in each other's
principal ideals. -/
private theorem polynomial_variable_not_mem_span_other_variable
    {i j : Fin 2} (hij : i ≠ j) :
    (X i : MvPolynomial (Fin 2) k) ∉ Ideal.span ({X j} : Set (MvPolynomial (Fin 2) k)) := by
  intro hx
  have hx' :
      (X i : MvPolynomial (Fin 2) k) ∈
        Ideal.span (MvPolynomial.X '' ({j} : Set (Fin 2))) := by
    simpa [Set.image_singleton] using hx
  rw [MvPolynomial.mem_ideal_span_X_image] at hx'
  rcases hx' (Finsupp.single i 1) (by simp) with ⟨ℓ, hℓ, hpow⟩
  have hℓ' : ℓ = j := by simpa using hℓ
  subst hℓ'
  simpa [hij] using hpow

/-- Helper for Example 10.35.23: on the node quotient, the class of `x` does not lie in the ideal
cutting out the `x`-axis. -/
private theorem node_x_not_mem_xAxisIdeal :
    nodeCoordinate k 0 ∉ Ideal.span ({nodeCoordinate k 1} : Set (nodeCoordinateRing k)) := by
  -- Pull ideal membership back to the polynomial ring, where monomial support detects it.
  rw [← node_axis_ideal_map_eq (k := k) 1]
  intro hx
  have hx' :
      (X 0 : MvPolynomial (Fin 2) k) ∈ Ideal.span ({X 1} : Set (MvPolynomial (Fin 2) k)) := by
    simpa [nodeCoordinate] using
      (Ideal.mem_quotient_iff_mem (nodeCoordinateRingIdeal_le_axisIdeal (k := k) 1)).1 hx
  exact polynomial_variable_not_mem_span_other_variable (k := k) (i := 0) (j := 1) (by decide) hx'

/-- Helper for Example 10.35.23: on the node quotient, the class of `y` does not lie in the ideal
cutting out the `y`-axis. -/
private theorem node_y_not_mem_yAxisIdeal :
    nodeCoordinate k 1 ∉ Ideal.span ({nodeCoordinate k 0} : Set (nodeCoordinateRing k)) := by
  -- Pull ideal membership back to the polynomial ring, where monomial support detects it.
  rw [← node_axis_ideal_map_eq (k := k) 0]
  intro hy
  have hy' :
      (X 1 : MvPolynomial (Fin 2) k) ∈ Ideal.span ({X 0} : Set (MvPolynomial (Fin 2) k)) := by
    simpa [nodeCoordinate] using
      (Ideal.mem_quotient_iff_mem (nodeCoordinateRingIdeal_le_axisIdeal (k := k) 0)).1 hy
  exact polynomial_variable_not_mem_span_other_variable (k := k) (i := 1) (j := 0) (by decide) hy'

/-- Helper for Example 10.35.23: the closed subset defined by `y = 0` in the node coordinate ring
is irreducible. -/
private theorem nodeXAxis_isIrreducible :
    IsIrreducible (nodeXAxis k) := by
  -- Rewrite the axis as a zero locus of a prime ideal in the quotient ring.
  have hprime : (Ideal.span ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))).IsPrime :=
    node_axis_ideal_isPrime (k := k) 1
  have hrad :
      (Ideal.span ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))).IsRadical :=
    hprime.isRadical
  rw [nodeXAxis, ← PrimeSpectrum.zeroLocus_span]
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ hrad).2 hprime

/-- Helper for Example 10.35.23: the closed subset defined by `x = 0` in the node coordinate ring
is irreducible. -/
private theorem nodeYAxis_isIrreducible :
    IsIrreducible (nodeYAxis k) := by
  -- Rewrite the axis as a zero locus of a prime ideal in the quotient ring.
  have hprime : (Ideal.span ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))).IsPrime :=
    node_axis_ideal_isPrime (k := k) 0
  have hrad :
      (Ideal.span ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))).IsRadical :=
    hprime.isRadical
  rw [nodeYAxis, ← PrimeSpectrum.zeroLocus_span]
  exact (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical _ hrad).2 hprime

/-- Helper for Example 10.35.23: the generic point of the `x`-axis lies on that axis but not on the
`y`-axis. -/
private theorem node_xAxis_has_off_yAxis_point :
    ∃ p : PrimeSpectrum (nodeCoordinateRing k), p ∈ nodeXAxis k ∧ p ∉ nodeYAxis k := by
  let p : PrimeSpectrum (nodeCoordinateRing k) :=
    ⟨Ideal.span ({nodeCoordinate k 1} : Set (nodeCoordinateRing k)),
      node_axis_ideal_isPrime (k := k) 1⟩
  refine ⟨p, ?_, ?_⟩
  · -- The prime `(y)` contains `y`, so it lies on the `x`-axis.
    simpa [p, nodeXAxis, PrimeSpectrum.mem_zeroLocus]
      using (Ideal.subset_span (by simp) :
        nodeCoordinate k 1 ∈ Ideal.span ({nodeCoordinate k 1} : Set (nodeCoordinateRing k)))
  · -- The same prime does not contain `x`.
    simpa [p, nodeYAxis, PrimeSpectrum.mem_zeroLocus] using node_x_not_mem_xAxisIdeal (k := k)

/-- Helper for Example 10.35.23: the generic point of the `y`-axis lies on that axis but not on the
`x`-axis. -/
private theorem node_yAxis_has_off_xAxis_point :
    ∃ p : PrimeSpectrum (nodeCoordinateRing k), p ∈ nodeYAxis k ∧ p ∉ nodeXAxis k := by
  let p : PrimeSpectrum (nodeCoordinateRing k) :=
    ⟨Ideal.span ({nodeCoordinate k 0} : Set (nodeCoordinateRing k)),
      node_axis_ideal_isPrime (k := k) 0⟩
  refine ⟨p, ?_, ?_⟩
  · -- The prime `(x)` contains `x`, so it lies on the `y`-axis.
    simpa [p, nodeYAxis, PrimeSpectrum.mem_zeroLocus]
      using (Ideal.subset_span (by simp) :
        nodeCoordinate k 0 ∈ Ideal.span ({nodeCoordinate k 0} : Set (nodeCoordinateRing k)))
  · -- The same prime does not contain `y`.
    simpa [p, nodeXAxis, PrimeSpectrum.mem_zeroLocus] using node_y_not_mem_yAxisIdeal (k := k)

-- Proof sketch: irreducible components of `Spec` correspond to minimal primes via
-- `minimalPrimes.equivIrreducibleComponents`. For `k[x, y]/(xy)` over a domain, the minimal
-- primes are the images of `(x)` and `(y)`.
/-- Example 10.35.23 (1): `Spec(k[x, y]/(xy))` has two irreducible components, namely the `x`-axis
and the `y`-axis. -/
@[stacks 00GF]
theorem nodeCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (nodeCoordinateRing k)) =
      {nodeXAxis k, nodeYAxis k} :=
  by
    classical
    -- Follow the source proof by covering the node with the two coordinate axes.
    refine irreducibleComponents_eq_of_finite_irreducible_closed_cover
      {nodeXAxis k, nodeYAxis k} ?_ ?_ ?_ ?_ ?_
    · simpa using Set.finite_insert (nodeXAxis k) (Set.finite_singleton (nodeYAxis k))
    · ext p
      constructor
      · intro _
        simp
      · intro _
        have hxy : nodeCoordinate k 0 * nodeCoordinate k 1 ∈ p.asIdeal := by
          simpa [node_coordinate_mul_eq_zero (k := k)] using (p.asIdeal.zero_mem :
            (0 : nodeCoordinateRing k) ∈ p.asIdeal)
        have hor : p ∈ nodeXAxis k ∨ p ∈ nodeYAxis k := by
          rcases p.isPrime.mem_or_mem hxy with hx | hy
          · right
            simpa [nodeYAxis, PrimeSpectrum.mem_zeroLocus] using hx
          · left
            simpa [nodeXAxis, PrimeSpectrum.mem_zeroLocus] using hy
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hor
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl
      · simpa [nodeXAxis] using PrimeSpectrum.isClosed_zeroLocus
          ({nodeCoordinate k 1} : Set (nodeCoordinateRing k))
      · simpa [nodeYAxis] using PrimeSpectrum.isClosed_zeroLocus
          ({nodeCoordinate k 0} : Set (nodeCoordinateRing k))
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl
      · exact nodeXAxis_isIrreducible (k := k)
      · exact nodeYAxis_isIrreducible (k := k)
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl
      · rintro hsubset
        obtain ⟨p, hpX, hpY⟩ := node_xAxis_has_off_yAxis_point (k := k)
        have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeXAxis k}) := hsubset hpX
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ nodeXAxis k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl
        · exact False.elim (htNe rfl)
        · exact hpY hpt
      · rintro hsubset
        obtain ⟨p, hpY, hpX⟩ := node_yAxis_has_off_xAxis_point (k := k)
        have hpUnion : p ∈ ⋃₀ ({nodeXAxis k, nodeYAxis k} \ {nodeYAxis k}) := hsubset hpY
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem : t = nodeXAxis k ∨ t = nodeYAxis k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ nodeYAxis k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl
        · exact hpX hpt
        · exact False.elim (htNe rfl)

end

section

variable (k : Type u) [Field k]

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `Y = 0` stratum before
passing to the quotient coordinate ring. -/
private def matrixProductAmbientYIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 1) ij.1 ij.2

/-- Helper for Example 10.35.23: the ambient ideal cutting out the `X = 0` stratum before
passing to the quotient coordinate ring. -/
private def matrixProductAmbientXIdeal :
    Ideal (MvPolynomial (Fin 2 × Fin 2 × Fin 2) k) :=
  Ideal.span <| Set.range fun ij : Fin 2 × Fin 2 ↦
    (matrixProductPolynomialMatrix k 0) ij.1 ij.2

/-- Helper for Example 10.35.23: the embedding of the `X`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
private def matrixProductXVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (0, ij.1, ij.2)

/-- Helper for Example 10.35.23: the embedding of the `Y`-coordinates into the ambient polynomial
ring of `(X, Y)`. -/
private def matrixProductYVariableEmbedding :
    Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2 := fun ij ↦ (1, ij.1, ij.2)

/-- Helper for Example 10.35.23: the `X`-coordinate embedding is injective. -/
private theorem matrixProductXVariableEmbedding_injective :
    Function.Injective (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a b h
    simpa [matrixProductXVariableEmbedding] using h

/-- Helper for Example 10.35.23: the `Y`-coordinate embedding is injective. -/
private theorem matrixProductYVariableEmbedding_injective :
    Function.Injective (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a b h
    simpa [matrixProductYVariableEmbedding] using h

/-- Helper for Example 10.35.23: keeping only the `X`-variables kills the `Y`-variables. -/
private def matrixProductKeepX :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductXVariableEmbedding_injective

/-- Helper for Example 10.35.23: keeping only the `Y`-variables kills the `X`-variables. -/
private def matrixProductKeepY :
    MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →ₐ[k] MvPolynomial (Fin 2 × Fin 2) k :=
  MvPolynomial.killCompl matrixProductYVariableEmbedding_injective

/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `Y = 0` in
the ambient polynomial ring. -/
private theorem matrixProductCoordinateRingIdeal_le_ambientYIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientYIdeal k := by
  -- Each entry of `XY` is a sum of terms with a `Y`-coordinate factor.
  rw [matrixProductCoordinateRingIdeal, matrixProductAmbientYIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  simp only [matrixProductPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨(0, j), by simp [matrixProductPolynomialMatrix]⟩)
  · exact Ideal.mul_mem_left _ _
      (Ideal.subset_span ⟨(1, j), by simp [matrixProductPolynomialMatrix]⟩)

/-- Helper for Example 10.35.23: the defining relations `XY = 0` already vanish modulo `X = 0` in
the ambient polynomial ring. -/
private theorem matrixProductCoordinateRingIdeal_le_ambientXIdeal :
    matrixProductCoordinateRingIdeal k ≤ matrixProductAmbientXIdeal k := by
  -- Each entry of `XY` is a sum of terms with an `X`-coordinate factor.
  rw [matrixProductCoordinateRingIdeal, matrixProductAmbientXIdeal]
  refine Ideal.span_le.mpr ?_
  intro f hf
  rcases hf with ⟨⟨i, j⟩, rfl⟩
  simp only [matrixProductPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨(i, 0), by simp [matrixProductPolynomialMatrix]⟩)
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨(i, 1), by simp [matrixProductPolynomialMatrix]⟩)

/-- Helper for Example 10.35.23: if no `Y`-coordinate occurs in a monomial, then that monomial is
supported on the `X`-coordinate embedding. -/
private theorem matrixProduct_support_subset_xEmbedding_of_no_y
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (1, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a ha
    rcases a with ⟨s, i, j⟩
    fin_cases s
    · exact ⟨(i, j), by simp [matrixProductXVariableEmbedding]⟩
    · have hs : m (1, i, j) ≠ 0 := by
        simpa using Finsupp.mem_support_iff.mp ha
      exact False.elim (hs (hm (i, j)))

/-- Helper for Example 10.35.23: if no `X`-coordinate occurs in a monomial, then that monomial is
supported on the `Y`-coordinate embedding. -/
private theorem matrixProduct_support_subset_yEmbedding_of_no_x
    {m : (Fin 2 × Fin 2 × Fin 2) →₀ ℕ}
    (hm : ∀ ij : Fin 2 × Fin 2, m (0, ij.1, ij.2) = 0) :
    ↑m.support ⊆ Set.range (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
  by
    intro a ha
    rcases a with ⟨s, i, j⟩
    fin_cases s
    · have hs : m (0, i, j) ≠ 0 := by
        simpa using Finsupp.mem_support_iff.mp ha
      exact False.elim (hs (hm (i, j)))
    · exact ⟨(i, j), by simp [matrixProductYVariableEmbedding]⟩

/-- Helper for Example 10.35.23: killing the `Y`-variables has kernel exactly the ambient
`Y = 0` ideal. -/
private theorem matrixProductKeepX_ker :
    RingHom.ker (matrixProductKeepX k) = matrixProductAmbientYIdeal k := by
  classical
  have hYrange :
      Set.range (fun ij : Fin 2 × Fin 2 ↦ (matrixProductPolynomialMatrix k 1) ij.1 ij.2) =
        MvPolynomial.X ''
          Set.range
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      refine ⟨(1, i, j), ⟨(i, j), rfl⟩, ?_⟩
      simp [matrixProductPolynomialMatrix, matrixProductYVariableEmbedding]
    · intro hz
      rcases hz with ⟨a, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      exact ⟨(i, j), by simp [matrixProductPolynomialMatrix, matrixProductYVariableEmbedding]⟩
  apply le_antisymm
  · intro f hf
    -- Route correction: compute the kernel by support control, matching the source proof that
    -- every surviving monomial must involve a `Y`-variable.
    rw [RingHom.mem_ker] at hf
    rw [matrixProductAmbientYIdeal, hYrange, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hmY
    have hmYzero : ∀ ij : Fin 2 × Fin 2, m (1, ij.1, ij.2) = 0 := by
      intro ij
      by_contra hij
      exact hmY ⟨(1, ij.1, ij.2), ⟨ij, rfl⟩, hij⟩
    have hsupp :
        ↑m.support ⊆
          Set.range
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
      matrixProduct_support_subset_xEmbedding_of_no_y hmYzero
    let mx : (Fin 2 × Fin 2) →₀ ℕ :=
      m.comapDomain
        (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2)
        matrixProductXVariableEmbedding_injective.injOn
    have hcoeff_zero : (matrixProductKeepX k f).coeff mx = 0 := by
      simpa [hf, mx]
    have hmap :
        Finsupp.mapDomain
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) mx =
          m := by
      exact Finsupp.mapDomain_comapDomain
        (f := matrixProductXVariableEmbedding)
        matrixProductXVariableEmbedding_injective m hsupp
    have hcoeff :
        (matrixProductKeepX k f).coeff mx = f.coeff m := by
      -- Read the killed-complement coefficient back on the ambient monomial supported only on `X`.
      rw [matrixProductKeepX, MvPolynomial.coeff_killCompl, hmap]
    rw [hcoeff] at hcoeff_zero
    exact (Finsupp.mem_support_iff.mp hm) hcoeff_zero
  · intro f hf
    rw [matrixProductAmbientYIdeal] at hf
    -- Each `Y`-generator is killed by `matrixProductKeepX`, so the whole span lies in the kernel.
    exact (Ideal.span_le.mpr (by
      intro z hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      show (matrixProductKeepX k) ((matrixProductPolynomialMatrix k 1) i j) = 0
      fin_cases i <;> fin_cases j <;>
        simp [matrixProductKeepX, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
          MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductXVariableEmbedding]
    )) hf

/-- Helper for Example 10.35.23: killing the `X`-variables has kernel exactly the ambient
`X = 0` ideal. -/
private theorem matrixProductKeepY_ker :
    RingHom.ker (matrixProductKeepY k) = matrixProductAmbientXIdeal k := by
  classical
  have hXrange :
      Set.range (fun ij : Fin 2 × Fin 2 ↦ (matrixProductPolynomialMatrix k 0) ij.1 ij.2) =
        MvPolynomial.X ''
          Set.range
            (matrixProductXVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      refine ⟨(0, i, j), ⟨(i, j), rfl⟩, ?_⟩
      simp [matrixProductPolynomialMatrix]
    · intro hz
      rcases hz with ⟨a, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      exact ⟨(i, j), by simp [matrixProductPolynomialMatrix, matrixProductXVariableEmbedding]⟩
  apply le_antisymm
  · intro f hf
    -- Route correction: the symmetric kernel computation again follows the support criterion,
    -- now detecting monomials that must involve an `X`-variable.
    rw [RingHom.mem_ker] at hf
    rw [matrixProductAmbientXIdeal, hXrange, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hmX
    have hmXzero : ∀ ij : Fin 2 × Fin 2, m (0, ij.1, ij.2) = 0 := by
      intro ij
      by_contra hij
      exact hmX ⟨(0, ij.1, ij.2), ⟨ij, rfl⟩, hij⟩
    have hsupp :
        ↑m.support ⊆
          Set.range
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) :=
      matrixProduct_support_subset_yEmbedding_of_no_x hmXzero
    let my : (Fin 2 × Fin 2) →₀ ℕ :=
      m.comapDomain
        (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2)
        matrixProductYVariableEmbedding_injective.injOn
    have hcoeff_zero : (matrixProductKeepY k f).coeff my = 0 := by
      simpa [hf, my]
    have hmap :
        Finsupp.mapDomain
            (matrixProductYVariableEmbedding : Fin 2 × Fin 2 → Fin 2 × Fin 2 × Fin 2) my =
          m := by
      exact Finsupp.mapDomain_comapDomain
        (f := matrixProductYVariableEmbedding)
        matrixProductYVariableEmbedding_injective m hsupp
    have hcoeff :
        (matrixProductKeepY k f).coeff my = f.coeff m := by
      -- Read the killed-complement coefficient back on the ambient monomial supported only on `Y`.
      rw [matrixProductKeepY, MvPolynomial.coeff_killCompl, hmap]
    rw [hcoeff] at hcoeff_zero
    exact (Finsupp.mem_support_iff.mp hm) hcoeff_zero
  · intro f hf
    rw [matrixProductAmbientXIdeal] at hf
    -- Each `X`-generator is killed by `matrixProductKeepY`, so the whole span lies in the kernel.
    exact (Ideal.span_le.mpr (by
      intro z hz
      rcases hz with ⟨⟨i, j⟩, rfl⟩
      show (matrixProductKeepY k) ((matrixProductPolynomialMatrix k 0) i j) = 0
      fin_cases i <;> fin_cases j <;>
        simp [matrixProductKeepY, matrixProductPolynomialMatrix, Matrix.mvPolynomialX_apply,
          MvPolynomial.rename_X, MvPolynomial.killCompl, matrixProductYVariableEmbedding]
    )) hf

/-- Helper for Example 10.35.23: the ambient `Y = 0` ideal is prime because its quotient is a
polynomial ring in the `X`-coordinates. -/
private theorem matrixProductAmbientYIdeal_isPrime :
    (matrixProductAmbientYIdeal k).IsPrime := by
  -- The `Y = 0` ambient ideal is exactly the kernel of the retraction to the `X`-polynomial ring.
  rw [← matrixProductKeepX_ker (k := k)]
  exact RingHom.ker_isPrime (matrixProductKeepX k)

/-- Helper for Example 10.35.23: the ambient `X = 0` ideal is prime because its quotient is a
polynomial ring in the `Y`-coordinates. -/
private theorem matrixProductAmbientXIdeal_isPrime :
    (matrixProductAmbientXIdeal k).IsPrime := by
  -- The `X = 0` ambient ideal is exactly the kernel of the retraction to the `Y`-polynomial ring.
  rw [← matrixProductKeepY_ker (k := k)]
  exact RingHom.ker_isPrime (matrixProductKeepY k)

/-- Helper for Example 10.35.23: the image of the ambient `Y = 0` ideal in the quotient coordinate
ring is exactly the entry ideal defining `matrixProductYZeroComponent`. -/
private theorem matrixProductAmbientYIdeal_map_eq :
    Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))
      (matrixProductAmbientYIdeal k) = matrixProductEntryIdeal k 1 := by
  -- TODO: map the ambient generators through the quotient map and identify them with the `Y`
  -- entries of the generic matrix.
  sorry

/-- Helper for Example 10.35.23: the image of the ambient `X = 0` ideal in the quotient coordinate
ring is exactly the entry ideal defining `matrixProductXZeroComponent`. -/
private theorem matrixProductAmbientXIdeal_map_eq :
    Ideal.map (Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k))
      (matrixProductAmbientXIdeal k) = matrixProductEntryIdeal k 0 := by
  -- TODO: map the ambient generators through the quotient map and identify them with the `X`
  -- entries of the generic matrix.
  sorry

/-- Helper for Example 10.35.23: each entry ideal in the matrix-product coordinate ring is prime. -/
private theorem matrixProductEntryIdeal_isPrime (s : Fin 2) :
    (matrixProductEntryIdeal k s).IsPrime := by
  -- TODO: push primeness of the ambient entry ideal through the quotient map using the containment
  -- `matrixProductCoordinateRingIdeal ≤ matrixProductAmbientEntryIdeal`.
  sorry

/-- Helper for Example 10.35.23: both axis-type components are irreducible because they are zero
loci of prime ideals. -/
private theorem matrix_product_entry_component_irreducible (s : Fin 2) :
    IsIrreducible (zeroLocus (matrixProductEntryIdeal k s : Set (matrixProductCoordinateRing k))) := by
  -- TODO: once `matrixProductEntryIdeal_isPrime` is available, apply the standard irreducible
  -- zero-locus criterion for radical prime ideals.
  sorry

/-- Helper for Example 10.35.23: in the matrix-product coordinate ring the universal relation is
`XY = 0`. -/
private theorem matrixProductGenericMatrix_mul_eq_zero :
    matrixProductGenericMatrix k 0 * matrixProductGenericMatrix k 1 = 0 := by
  -- Each entry of the product is one of the generators of the defining quotient ideal.
  ext i j
  change Ideal.Quotient.mk (matrixProductCoordinateRingIdeal k)
      ((matrixProductPolynomialMatrix k 0 * matrixProductPolynomialMatrix k 1) i j) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x00_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 0 0 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₁₁ det(Y)` through the two first-row relations of `XY = 0`.
  calc
    X 0 0 * Y.det = (X * Y) 0 0 * Y 1 1 - (X * Y) 0 1 * Y 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x01_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 0 1 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₁₂ det(Y)` through the two first-row relations of `XY = 0`.
  calc
    X 0 1 * Y.det = (X * Y) 0 1 * Y 0 0 - (X * Y) 0 0 * Y 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x10_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 1 0 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₂₁ det(Y)` through the two second-row relations of `XY = 0`.
  calc
    X 1 0 * Y.det = (X * Y) 1 0 * Y 1 1 - (X * Y) 1 1 * Y 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `x`-entry annihilates `det(Y)` inside the quotient. -/
private theorem matrixProduct_x11_mul_detY_eq_zero :
    (matrixProductGenericMatrix k 0) 1 1 * (matrixProductGenericMatrix k 1).det = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `x₂₂ det(Y)` through the two second-row relations of `XY = 0`.
  calc
    X 1 1 * Y.det = (X * Y) 1 1 * Y 0 0 - (X * Y) 1 0 * Y 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y00_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 0 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₁₁` through the first-column relations of `XY = 0`.
  calc
    X.det * Y 0 0 = X 1 1 * (X * Y) 0 0 - X 0 1 * (X * Y) 1 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y01_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 1 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₁₂` through the second-column relations of `XY = 0`.
  calc
    X.det * Y 0 1 = X 1 1 * (X * Y) 0 1 - X 0 1 * (X * Y) 1 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y10_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 0 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₂₁` through the first-column relations of `XY = 0`.
  calc
    X.det * Y 1 0 = X 0 0 * (X * Y) 1 0 - X 1 0 * (X * Y) 0 0 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every `y`-entry annihilates `det(X)` inside the quotient. -/
private theorem matrixProduct_detX_mul_y11_eq_zero :
    (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 1 = 0 := by
  let X := matrixProductGenericMatrix k 0
  let Y := matrixProductGenericMatrix k 1
  have hXY : X * Y = 0 := by
    simpa [X, Y] using matrixProductGenericMatrix_mul_eq_zero (k := k)
  -- Express `det(X) y₂₂` through the second-column relations of `XY = 0`.
  calc
    X.det * Y 1 1 = X 0 0 * (X * Y) 1 1 - X 1 0 * (X * Y) 0 1 := by
      simp [X, Y, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 0 := by simp [hXY]

/-- Helper for Example 10.35.23: every prime of the matrix-product coordinate ring lies either on
`Y = 0`, on `X = 0`, or on the determinant component. -/
private theorem matrix_product_prime_lies_in_axis_or_determinant_component
    (p : PrimeSpectrum (matrixProductCoordinateRing k)) :
    p ∈ matrixProductYZeroComponent k ∨
      p ∈ matrixProductDeterminantZeroComponent k ∨
      p ∈ matrixProductXZeroComponent k := by
  by_cases hY : p ∈ matrixProductYZeroComponent k
  · exact Or.inl hY
  by_cases hX : p ∈ matrixProductXZeroComponent k
  · exact Or.inr (Or.inr hX)
  have hY' : ∃ ij : Fin 2 × Fin 2, (matrixProductGenericMatrix k 1) ij.1 ij.2 ∉ p.asIdeal := by
    by_contra hcontra
    apply hY
    rw [matrixProductYZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductEntryIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨ij, rfl⟩
    by_contra hz'
    exact hcontra ⟨ij, hz'⟩
  have hX' : ∃ ij : Fin 2 × Fin 2, (matrixProductGenericMatrix k 0) ij.1 ij.2 ∉ p.asIdeal := by
    by_contra hcontra
    apply hX
    rw [matrixProductXZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductEntryIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨ij, rfl⟩
    by_contra hz'
    exact hcontra ⟨ij, hz'⟩
  obtain ⟨ijY, hijY⟩ := hY'
  obtain ⟨ijX, hijX⟩ := hX'
  have hdetX : (matrixProductGenericMatrix k 0).det ∈ p.asIdeal := by
    rcases ijY with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    ·
      have hy00 : (matrixProductGenericMatrix k 1) 0 0 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 0 ∈
            p.asIdeal := by
        simpa [matrixProduct_detX_mul_y00_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy00
    ·
      have hy01 : (matrixProductGenericMatrix k 1) 0 1 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 0 1 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y01_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy01
    ·
      have hy10 : (matrixProductGenericMatrix k 1) 1 0 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 0 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y10_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy10
    ·
      have hy11 : (matrixProductGenericMatrix k 1) 1 1 ∉ p.asIdeal := by
        simpa using hijY
      have hmul :
          (matrixProductGenericMatrix k 0).det * (matrixProductGenericMatrix k 1) 1 1 ∈
            p.asIdeal := by
        simpa [mul_comm, matrixProduct_detX_mul_y11_eq_zero (k := k)] using
          (p.asIdeal.zero_mem : (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_right hy11
  have hdetY : (matrixProductGenericMatrix k 1).det ∈ p.asIdeal := by
    rcases ijX with ⟨i, j⟩
    fin_cases i <;> fin_cases j
    ·
      have hx00 : (matrixProductGenericMatrix k 0) 0 0 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 0 0 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x00_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx00
    ·
      have hx01 : (matrixProductGenericMatrix k 0) 0 1 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 0 1 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x01_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx01
    ·
      have hx10 : (matrixProductGenericMatrix k 0) 1 0 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 1 0 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x10_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx10
    ·
      have hx11 : (matrixProductGenericMatrix k 0) 1 1 ∉ p.asIdeal := by
        simpa using hijX
      have hmul :
          (matrixProductGenericMatrix k 0) 1 1 * (matrixProductGenericMatrix k 1).det ∈
            p.asIdeal := by
        simpa [matrixProduct_x11_mul_detY_eq_zero (k := k)] using (p.asIdeal.zero_mem :
          (0 : matrixProductCoordinateRing k) ∈ p.asIdeal)
      exact (p.isPrime.mem_or_mem hmul).resolve_left hx11
  -- Once both determinants lie in `p`, the point lies on the determinant component.
  exact Or.inr (Or.inl (by
    rw [matrixProductDeterminantZeroComponent, PrimeSpectrum.mem_zeroLocus]
    rw [matrixProductDeterminantIdeal]
    refine Ideal.span_le.mpr ?_
    intro z hz
    rcases hz with ⟨s, rfl⟩
    fin_cases s
    · simpa using hdetX
    · simpa using hdetY))

/-- Helper for Example 10.35.23: the generic point of the `Y = 0` component is the prime ideal
generated by the `Y`-entries. -/
private def matrixProductYZeroGenericPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) :=
  ⟨matrixProductEntryIdeal k 1, matrixProductEntryIdeal_isPrime (k := k) 1⟩

/-- Helper for Example 10.35.23: the generic point of the `X = 0` component is the prime ideal
generated by the `X`-entries. -/
private def matrixProductXZeroGenericPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) :=
  ⟨matrixProductEntryIdeal k 0, matrixProductEntryIdeal_isPrime (k := k) 0⟩

/-- Helper for Example 10.35.23: the `x₁₁`-coordinate survives modulo the ambient `Y = 0` ideal. -/
private theorem matrixProduct_x00_not_mem_ambientYIdeal :
    (matrixProductPolynomialMatrix k 0) 0 0 ∉ matrixProductAmbientYIdeal k := by
  -- TODO: push forward along `matrixProductKeepX`; the image is the nonzero variable `X (0, 0)`.
  sorry

/-- Helper for Example 10.35.23: the `y₁₁`-coordinate survives modulo the ambient `X = 0` ideal. -/
private theorem matrixProduct_y00_not_mem_ambientXIdeal :
    (matrixProductPolynomialMatrix k 1) 0 0 ∉ matrixProductAmbientXIdeal k := by
  -- TODO: push forward along `matrixProductKeepY`; the image is the nonzero variable `X (0, 0)`.
  sorry

/-- Helper for Example 10.35.23: the determinant polynomial of `X` survives modulo the ambient
`Y = 0` ideal. -/
private theorem matrixProduct_detX_not_mem_ambientYIdeal :
    (matrixProductPolynomialMatrix k 0).det ∉ matrixProductAmbientYIdeal k := by
  -- TODO: push forward along `matrixProductKeepX` and evaluate the resulting determinant at the
  -- identity matrix to obtain the value `1`.
  sorry

/-- Helper for Example 10.35.23: the determinant polynomial of `Y` survives modulo the ambient
`X = 0` ideal. -/
private theorem matrixProduct_detY_not_mem_ambientXIdeal :
    (matrixProductPolynomialMatrix k 1).det ∉ matrixProductAmbientXIdeal k := by
  -- TODO: push forward along `matrixProductKeepY` and evaluate the resulting determinant at the
  -- identity matrix to obtain the value `1`.
  sorry

/-- Helper for Example 10.35.23: the generic `Y = 0` point does not lie on the determinant or
`X = 0` components. -/
private theorem matrixProductYZeroGenericPoint_off_other_components :
    matrixProductYZeroGenericPoint k ∈ matrixProductYZeroComponent k ∧
      matrixProductYZeroGenericPoint k ∉ matrixProductDeterminantZeroComponent k ∧
      matrixProductYZeroGenericPoint k ∉ matrixProductXZeroComponent k := by
  -- TODO: use the generic point of the prime entry ideal and pull back determinant/entry
  -- membership to the ambient polynomial ring.
  sorry

/-- Helper for Example 10.35.23: the generic `X = 0` point does not lie on the determinant or
`Y = 0` components. -/
private theorem matrixProductXZeroGenericPoint_off_other_components :
    matrixProductXZeroGenericPoint k ∈ matrixProductXZeroComponent k ∧
      matrixProductXZeroGenericPoint k ∉ matrixProductDeterminantZeroComponent k ∧
      matrixProductXZeroGenericPoint k ∉ matrixProductYZeroComponent k := by
  -- TODO: use the generic point of the prime entry ideal and pull back determinant/entry
  -- membership to the ambient polynomial ring.
  sorry

/-- Helper for Example 10.35.23: the concrete rank-one pair
`X = [[1,0],[1,0]]`, `Y = [[0,0],[1,0]]` determines a prime-spectrum point of the quotient ring. -/
private def matrixProductDeterminantWitnessPoint :
    PrimeSpectrum (matrixProductCoordinateRing k) := by
  let φ :
      MvPolynomial (Fin 2 × Fin 2 × Fin 2) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) fun a : Fin 2 × Fin 2 × Fin 2 ↦
      match a with
      | (0, 0, 0) => 1
      | (0, 0, 1) => 0
      | (0, 1, 0) => 1
      | (0, 1, 1) => 0
      | (1, 0, 0) => 0
      | (1, 0, 1) => 0
      | (1, 1, 0) => 1
      | (1, 1, 1) => 0
  have hφ :
      matrixProductCoordinateRingIdeal k ≤ RingHom.ker φ := by
    -- The chosen point satisfies the defining matrix equation `XY = 0`.
    rw [matrixProductCoordinateRingIdeal]
    refine Ideal.span_le.mpr ?_
    intro f hf
    rcases hf with ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp [φ, matrixProductPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  let ψ : matrixProductCoordinateRing k →+* k :=
    Ideal.Quotient.lift (matrixProductCoordinateRingIdeal k) φ hφ
  exact ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩

/-- Helper for Example 10.35.23: the rank-one witness point lies on the determinant component but
avoids the two axis components. -/
private theorem matrixProductDeterminantWitnessPoint_off_axes :
    matrixProductDeterminantWitnessPoint k ∈ matrixProductDeterminantZeroComponent k ∧
      matrixProductDeterminantWitnessPoint k ∉ matrixProductYZeroComponent k ∧
      matrixProductDeterminantWitnessPoint k ∉ matrixProductXZeroComponent k := by
  -- TODO: complete the explicit evaluation-on-the-quotient calculation for the rank-one witness
  -- point, using the quotient homomorphism in `matrixProductDeterminantWitnessPoint` to show that
  -- both determinants map to `0` while `y₂₁` and `x₁₁` map to `1`.
  sorry

/-- Helper for Example 10.35.23: the determinant component is irreducible.
The intended proof follows the source rank-one-chart argument on the basic opens where an
`X`-coordinate is invertible, then takes the closure of their irreducible union. -/
private theorem matrix_product_determinant_component_irreducible :
    IsIrreducible (matrixProductDeterminantZeroComponent k) := by
  -- TODO: prove irreducibility by the source-faithful chart analysis on the four `X`-entry basic
  -- opens, then show their union is dense in the determinant component.
  sorry

-- Proof sketch: irreducible components of `Spec` correspond to minimal primes via
-- `minimalPrimes.equivIrreducibleComponents`. For the matrix-product quotient, the orbit analysis
-- in the text isolates the three strata `Y = 0`, `det X = det Y = 0`, and `X = 0`; one shows
-- that the corresponding quotient ideals are prime and exhaust the minimal primes.

/-- Example 10.35.23 (2): the affine scheme of pairs of `2 × 2` matrices satisfying `XY = 0` has three
irreducible components, namely `Y = 0`, `det X = det Y = 0`, and `X = 0`. -/
theorem matrixProductCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (matrixProductCoordinateRing k)) =
      {matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
        matrixProductXZeroComponent k} :=
  by
    classical
    -- Follow the source proof by the finite closed cover coming from the three orbit types.
    refine irreducibleComponents_eq_of_finite_irreducible_closed_cover
      {matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
        matrixProductXZeroComponent k} ?_ ?_ ?_ ?_ ?_
    · simpa using Set.toFinite
        ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
          matrixProductXZeroComponent k} :
          Set (Set (PrimeSpectrum (matrixProductCoordinateRing k))))
    · ext p
      constructor
      · intro _
        simp
      · intro _
        rcases matrix_product_prime_lies_in_axis_or_determinant_component (k := k) p with hp | hp | hp
        · simp [hp]
        · simp [hp]
        · simp [hp]
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl | rfl
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductYZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductEntryIdeal k 1 : Set (matrixProductCoordinateRing k))
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductDeterminantZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductDeterminantIdeal k : Set (matrixProductCoordinateRing k))
      · -- Unfold the component definition and use that zero loci are closed.
        rw [matrixProductXZeroComponent]
        exact PrimeSpectrum.isClosed_zeroLocus
          (matrixProductEntryIdeal k 0 : Set (matrixProductCoordinateRing k))
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl | rfl
      · simpa [matrixProductYZeroComponent] using
          matrix_product_entry_component_irreducible (k := k) 1
      · exact matrix_product_determinant_component_irreducible (k := k)
      · simpa [matrixProductXZeroComponent] using
          matrix_product_entry_component_irreducible (k := k) 0
    · intro Z hZ
      simp at hZ
      rcases hZ with rfl | rfl | rfl
      · rintro hsubset
        obtain ⟨hpY, hpDet, hpX⟩ := matrixProductYZeroGenericPoint_off_other_components (k := k)
        have hpUnion :
            matrixProductYZeroGenericPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductYZeroComponent k}) := hsubset hpY
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductYZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact False.elim (htNe rfl)
        · exact hpDet hpt
        · exact hpX hpt
      · rintro hsubset
        obtain ⟨hpDet, hpY, hpX⟩ := matrixProductDeterminantWitnessPoint_off_axes (k := k)
        have hpUnion :
            matrixProductDeterminantWitnessPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductDeterminantZeroComponent k}) := hsubset hpDet
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductDeterminantZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact hpY hpt
        · exact False.elim (htNe rfl)
        · exact hpX hpt
      · rintro hsubset
        obtain ⟨hpX, hpDet, hpY⟩ := matrixProductXZeroGenericPoint_off_other_components (k := k)
        have hpUnion :
            matrixProductXZeroGenericPoint k ∈
              ⋃₀ ({matrixProductYZeroComponent k, matrixProductDeterminantZeroComponent k,
                matrixProductXZeroComponent k} \ {matrixProductXZeroComponent k}) := hsubset hpX
        rcases Set.mem_sUnion.mp hpUnion with ⟨t, ht, hpt⟩
        have htMem :
            t = matrixProductYZeroComponent k ∨
              t = matrixProductDeterminantZeroComponent k ∨
              t = matrixProductXZeroComponent k := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ht.1
        have htNe : t ≠ matrixProductXZeroComponent k := by
          simpa [Set.mem_singleton_iff] using ht.2
        rcases htMem with rfl | rfl | rfl
        · exact hpY hpt
        · exact hpDet hpt
        · exact False.elim (htNe rfl)

end
