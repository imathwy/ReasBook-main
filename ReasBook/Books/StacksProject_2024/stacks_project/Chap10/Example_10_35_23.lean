import Mathlib

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

-- Proof sketch: irreducible components of `Spec` correspond to minimal primes via
-- `minimalPrimes.equivIrreducibleComponents`. For `k[x, y]/(xy)` over a domain, the minimal
-- primes are the images of `(x)` and `(y)`.
/-- Example 10.35.23 (1): `Spec(k[x, y]/(xy))` has two irreducible components, namely the `x`-axis
and the `y`-axis. -/
@[stacks 00GF]
theorem nodeCoordinateRing_irreducibleComponents :
    irreducibleComponents (PrimeSpectrum (nodeCoordinateRing k)) =
      {nodeXAxis k, nodeYAxis k} :=
  sorry

end

section

variable (k : Type u) [Field k]

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
  sorry

end
