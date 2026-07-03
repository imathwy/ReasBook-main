import StacksProject_2024.Chap15.Remark_15_96_5
import StacksProject_2024.Chap15.«15_96_5_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex
open ModFSquared.Nat

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: the Berthelot-Ogus reduction complex from Remark `15.96.5` and its comparison
  with the canonical Bockstein cohomology complex;
- sampled owner declarations:
  `BerthelotOgusEtaReduction.Nat.toHomology`,
  `bockstein_factorization_naturality`,
  `modfCohomologyBocksteinComplex`,
  `QuasiIso`;
- best owner abstraction:
  `source-facing`: the scalar-restricted bounded-below bridge reduction complex
    `CochainComplex.reduceModIdealA (principalIdeal f) (η[f] M)`;
  `core/canonical`: the target complex `modfCohomologyBocksteinComplex f M hM`;
  `bridge/view`: the source-owned comparison map
    `BerthelotOgusEtaReduction.Nat.toModfCohomologyBocksteinComplex` and its quasi-isomorphism;
- primitive data vs derived API: the primitive source data are the owner declarations from Remark
  `15.96.5`. The target Bockstein complex is derived, so this file should state only the canonical
  comparison map to that target. -/

namespace BerthelotOgusEtaReduction
namespace Nat

-- Proof sketch: use the canonical reduction complex from Remark `15.96.5`. The quotient by its
-- acyclic boundary subcomplex identifies degreewise with the homology of `K^\bullet / fK^\bullet`,
-- and the induced differential on those quotients is the canonical Bockstein differential from
-- `15.96.5.2`; equivalently, this is the bounded-below source-facing specialization of the
-- factorization square from `15.96.5.1`. Hence the quotient map gives a quasi-isomorphism from
-- the canonical reduction complex to `modfCohomologyBocksteinComplex f M hM`.
/-- The canonical quotient maps
`(η_f M)^i / f(η_f M)^i ⟶ H^i(M^\bullet / fM^\bullet)` intertwine the differential on the
reduced Berthelot-Ogus complex with the Berthelot-Ogus Bockstein differential. -/
theorem toHomology_comm_bockstein
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) (i : ℕ) :
    CommSq
      (toHomology f M i)
      ((reduceModIdealA (principalIdeal f) (η[f] M)).d i (i + 1))
      (bockstein f M i hM)
      (toHomology f M (i + 1)) := by
  sorry

/-- The canonical comparison morphism from the Berthelot-Ogus reduction complex to the Bockstein
cohomology complex. -/
def toModfCohomologyBocksteinComplex
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    reduceModIdealA (principalIdeal f) (η[f] M) ⟶ modfCohomologyBocksteinComplex f M hM where
  f i := by
    simpa only [modfCohomologyBocksteinComplex_X] using toHomology f M i
  comm' i j hij := by
    rcases hij with rfl
    simpa only [modfCohomologyBocksteinComplex_d] using
      (toHomology_comm_bockstein f M hM i).w

/-- Lemma 15.96.6: let `A` be a ring, let `f ∈ A`, and let `K^\bullet` be a cochain complex of
`A`-modules on which multiplication by `f` is injective in every degree. Then
the scalar-restricted `A`-linear view of the canonical Berthelot-Ogus reduction complex
`η_f K^\bullet / f(η_f K^\bullet)` from Remark `15.96.5` is quasi-isomorphic to the canonical
Bockstein cohomology complex `H^\bullet(K^\bullet / fK^\bullet)` of `15.96.5.2`, via the
canonical comparison map. -/
theorem toModfCohomologyBocksteinComplex_quasiIso
    (f : A) (M : NatModuleCochainComplex A)
    (hM : IsTermwiseFTorsionFree f M) :
    QuasiIso (toModfCohomologyBocksteinComplex f M hM) := by
  sorry

end Nat
end BerthelotOgusEtaReduction

end
