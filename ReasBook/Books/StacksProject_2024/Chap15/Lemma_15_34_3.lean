import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u

namespace KaehlerDifferential

section

variable {k k' K K' : Type u}
variable [Field k] [Field k'] [Field K] [Field K']
variable [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
variable [IsScalarTower k k' K'] [IsScalarTower k K K']
variable [Algebra.FiniteType k k'] [Algebra.FiniteType K K']

variable (k k' K K')

/-- The canonical comparison map
`K' ⊗[K] Ω[K⁄k] → Ω[K'⁄k']` induced by the commutative square of field extensions. -/
noncomputable abbrev baseFieldComparison :
    K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] :=
  (KaehlerDifferential.map k k' K' K').comp (KaehlerDifferential.mapBaseChange k K K')

-- Proof sketch: compare the two Jacobi-Zariski exact sequences for
-- `k ⊆ k' ⊆ K'` and `k ⊆ K ⊆ K'`. The kernel and cokernel identify with subquotients of the
-- finite-dimensional vector spaces `Ω[k'⁄k]` and `Ω[K'⁄K]`, whose finite dimensionality comes
-- from Cartier's equality.
/-- The kernel of the comparison map on Kähler differentials is finite-dimensional over `K'`. -/
theorem finiteDimensional_ker_baseFieldComparison :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := sorry

-- Proof sketch: use the same pair of Jacobi-Zariski exact sequences as for the kernel statement.
-- The cokernel is a quotient of a finite-dimensional term in those exact sequences, so it is
-- finite-dimensional.
/-- The cokernel of the comparison map on Kähler differentials is finite-dimensional over `K'`. -/
theorem finiteDimensional_cokernel_baseFieldComparison :
    FiniteDimensional K' (Ω[K'⁄k'] ⧸ LinearMap.range (baseFieldComparison k k' K K')) := sorry

end

end KaehlerDifferential

namespace Algebra

section

variable {k k' K K' : Type u}
variable [Field k] [Field k'] [Field K] [Field K']
variable [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
variable [IsScalarTower k k' K'] [IsScalarTower k K K']
variable [Algebra.FiniteType k k'] [Algebra.FiniteType K K']

/- Domain triage:
* primary domain: Kähler differentials and first cotangent homology for a commutative square of
  finitely generated field extensions;
* sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `H1Cotangent.map`,
  - `H1Cotangent.exact_map_δ`,
  - `field_jacobi_zariski_left_injective`;
* best owner abstraction: the primitive data are the two canonical comparison maps obtained by
  composing the owner maps on `Ω` and `H1Cotangent`; kernel/cokernel finite-dimensionality and the
  Euler-characteristic identity are derived API;
* layer triage:
  - `source-facing`: the Euler-characteristic formula for this square of field extensions;
  - `core/canonical`: the owner maps on `Ω` and `H1Cotangent`, together with the Jacobi-Zariski
    exactness theorems from the Jacobi-Zariski sequence;
  - `bridge/view`: the two named comparison composites below.

The public surface should therefore speak directly in terms of these canonical comparison maps and
their kernels, ranges, and finranks, rather than re-expanding rank computations on the same owner
data.
-/

namespace H1Cotangent

variable (k k' K K')

/-- The canonical comparison map
`K' ⊗[K] H1Cotangent k K → H1Cotangent k' K'` induced by extension of scalars from `K` to `K'`
followed by change of base field from `k` to `k'`. -/
noncomputable abbrev baseFieldComparison :
    K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k' K' :=
  (H1Cotangent.map k k' K' K').comp
    (LinearMap.liftBaseChange K' (H1Cotangent.map k k K K'))

-- Proof sketch: compare the Jacobi-Zariski exact sequences for the two towers of fields and read
-- off the kernel of the cotangent-homology comparison as a subquotient of the finite-dimensional
-- spaces appearing in Lemma `15.34.1`.
/-- The kernel of the comparison map on first cotangent homology is finite-dimensional over `K'`. -/
theorem finiteDimensional_ker_baseFieldComparison :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := sorry

-- Proof sketch: the same exact sequences show that the cokernel of the cotangent-homology
-- comparison is a subquotient of the finite-dimensional endpoint terms, hence is finite-dimensional.
/-- The cokernel of the comparison map on first cotangent homology is finite-dimensional over
`K'`. -/
theorem finiteDimensional_cokernel_baseFieldComparison :
    FiniteDimensional K' (H1Cotangent k' K' ⧸ LinearMap.range (baseFieldComparison k k' K K')) :=
  sorry

end H1Cotangent

-- Proof sketch: compare the two Jacobi-Zariski exact sequences for
-- `k ⊆ k' ⊆ K'` and `k ⊆ K ⊆ K'`. The kernels and cokernels of this comparison map identify with
-- subquotients of the finite-dimensional vector spaces `Ω[k'⁄k]`, `Ω[K'⁄K]`, `H1Cotangent k k'`,
-- and `H1Cotangent K K'`, whose finite dimensionality comes from Cartier's equality.
/-- Lemma 15.34.3: for a commutative square of field extensions with `k' / k` and `K' / K`
finitely generated, the alternating sum of the kernel and cokernel dimensions of the canonical
comparison maps on Kähler differentials and first cotangent homology equals
`trdeg_k(k') - trdeg_K(K')`. -/
theorem baseFieldComparison_eulerCharacteristic_eq_trdeg_sub_trdeg :
    Int.ofNat (Module.finrank K' (LinearMap.ker (KaehlerDifferential.baseFieldComparison k k' K K'))) -
      Int.ofNat
        (Module.finrank K'
          (Ω[K'⁄k'] ⧸ LinearMap.range (KaehlerDifferential.baseFieldComparison k k' K K'))) -
      Int.ofNat (Module.finrank K' (LinearMap.ker (H1Cotangent.baseFieldComparison k k' K K'))) +
      Int.ofNat
        (Module.finrank K'
          (H1Cotangent k' K' ⧸ LinearMap.range (H1Cotangent.baseFieldComparison k k' K K'))) =
      Int.ofNat (Cardinal.toNat (Algebra.trdeg k k')) -
        Int.ofNat (Cardinal.toNat (Algebra.trdeg K K')) := sorry

end

end Algebra
