import Mathlib
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_34_1_Cartier_equality (from Chap15) -/
universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.FiniteType k K]

/- Domain triage:
* primary domain: Kähler differentials and the first homology of the naive cotangent complex for
  finitely generated field extensions;
* sampled owner declarations:
  - `KaehlerDifferential.finite`,
  - `Algebra.H1Cotangent`,
  - the canonical instance `Module.Finite K (H1Cotangent k K)`,
  - `Algebra.trdeg`;
* best owner abstraction: the primitive data are the canonical modules `Ω[K⁄k]` and
  `H1Cotangent k K`; their finite-dimensionality over the field `K` is derived API obtained from
  the upstream `Module.Finite` owners, not separate public owner data for this item. The finite
  presentation bridge belongs only inside a later proof and not in the file-level public context;
* layer triage:
  - `source-facing`: Cartier's equality itself;
  - `core/canonical`: `Ω[K⁄k]` and `H1Cotangent k K`;
  - `bridge/view`: the explicit finite-dimensional and `finrank` consequences over `K`.

This file therefore keeps the source-facing equality directly on the canonical owners and deletes
the redundant helper wrappers that only repackage their finite-dimensional consequences. -/

-- Proof sketch: pick a global complete intersection presentation
-- `k[x₁, ..., xₙ] / (f₁, ..., f_c)` of `K`, identify `Ω[K⁄k]` and `H¹(L_{K/k})` with the cokernel
-- and kernel of the resulting two-term complex `K^c → K^n`, and compute the Euler
-- characteristic `n - c` as the transcendence degree of `K / k`.
/-- Lemma 15.34.1 (Cartier equality): for a finitely generated field extension `K / k`, the
transcendence degree of `K` over `k` equals, in `ℤ`, the difference between the dimensions of
`Ω[K⁄k]` and `H¹(L_{K/k})`. -/
theorem cartier_equality :
    Int.ofNat (Cardinal.toNat (trdeg k K)) =
      Module.finrank K Ω[K⁄k] - Module.finrank K (H1Cotangent k K) := sorry

end

end Algebra

/-! ### Lemma_15_34_2 (from Chap15) -/
open scoped TensorProduct

noncomputable section

universe u

namespace Algebra

section

variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/- Domain triage:
* primary domain: the Jacobi-Zariski sequence for a tower of field extensions `K → L → M`;
* sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`,
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `KaehlerDifferential.map_surjective`;
* best owner abstraction: the source-facing sequence is already organized by the canonical owner
  maps `H1Cotangent.map`, `H1Cotangent.δ`, `KaehlerDifferential.mapBaseChange`, and
  `KaehlerDifferential.map`, so the middle exactness and terminal surjectivity belong directly to
  those owners rather than to a new local wrapper;
* primitive data vs. derived API:
  - primitive data: the tower of fields `K → L → M`;
  - derived API: the Jacobi-Zariski exactness/surjectivity on the owner maps, plus the extra
    left-injectivity that is special to the field case;
* layer triage:
  - `source-facing`: Lemma `15.34.2`, namely the same Jacobi-Zariski sequence with zero terms
    adjoined on the left and right;
  - `core/canonical`: the four owner exactness/surjectivity theorems listed above;
  - `bridge/view`: no extra bridge is needed beyond the left-injectivity theorem below.

The old `FieldJacobiZariskiExactSequenceWithZeroEnds` structure duplicated owner declarations
without adding new mathematical data, so this file is refined to direct recall/use of the
canonical owners and one theorem for the genuinely new left edge.
-/

/- Lemma 15.34.2: the middle part
`H₁(L_{M/K}) → H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K]`
is exactly `Algebra.H1Cotangent.exact_map_δ` specialized to the tower `K → L → M`. -/
recall Algebra.H1Cotangent.exact_map_δ

/- Lemma 15.34.2: the next part
`H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K] → Ω[M⁄K]`
is exactly `Algebra.H1Cotangent.exact_δ_mapBaseChange`. -/
recall Algebra.H1Cotangent.exact_δ_mapBaseChange

/- Lemma 15.34.2: the Kähler-differential tail
`M ⊗[L] Ω[L⁄K] → Ω[M⁄K] → Ω[M⁄L]`
is exactly `KaehlerDifferential.exact_mapBaseChange_map`. -/
recall KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 15.34.2: the terminal map `Ω[M⁄K] → Ω[M⁄L]` is the canonical surjective map
`KaehlerDifferential.map_surjective`. -/
recall KaehlerDifferential.map_surjective

-- Proof sketch: combine the left-extended Jacobi-Zariski exact sequence for filtered colimits of
-- local complete intersections with the Stacks result that a field extension is a filtered colimit
-- of global complete intersections. Over a field extension, tensoring with `M` is exact, so the
-- leftmost base-changed map is injective and the whole displayed sequence is exact.
/-- Lemma 15.34.2: for field extensions `M/L/K`, the leftmost map
`H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K})`
in the Jacobi-Zariski sequence is injective. Together with the recalled canonical exactness and
surjectivity results above, this is the source-facing exact sequence
`0 → H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K}) → H₁(L_{M/L}) → Ω[L⁄K] ⊗[L] M → Ω[M⁄K] → Ω[M⁄L] → 0`. -/
theorem field_jacobi_zariski_left_injective :
    Function.Injective (LinearMap.liftBaseChange M (H1Cotangent.map K K L M)) := sorry

end

end Algebra

/-! ### Lemma_15_34_3 (from Chap15) -/
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
