import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import stacks_project.Chap15.«15_91_9_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/- Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for a single localization, expressed through the
  canonical module Cech short complex and its cycles object;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `ShortComplex.moduleCatToCycles`,
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`,
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`;
- best owner abstraction: the source-facing replacement module `\tilde M = H^0(Can(M))` should be
  exposed as the cycles object of the canonical owner
  `beauvilleLaszloModuleCechSequence R' M f`, and the canonical map `M → \tilde M` should reuse
  `ShortComplex.moduleCatToCycles` directly;
- primitive data vs derived API: the primitive data are the module Cech short complex and its
  canonical map to cycles; the replacement module, its glueability, the induced base-change and
  localization bijectivity, and the surjectivity conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the replacement module `\tilde M = H^0(Can(M))` and the canonical map
  `M → \tilde M` from Remark `15.91.17`;
- `core/canonical`: `beauvilleLaszloModuleCechSequence`, `ShortComplex.moduleCatToCycles`, and
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`;
- `bridge/view`: the induced maps after tensoring with `R'` and localizing away from `f`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {f : R}

-- Proof sketch: Theorem `15.91.16` identifies the single-localization glueing datum `Can(M)` with
-- the Beauville-Laszlo datum of `\tilde M = H^0(Can(M))`, so `\tilde M` is glueable for the
-- pair `(R → R', f)`.
/-- Remark 15.91.17: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the replacement
module `\tilde M = H^0(Can(M))`, i.e. the cycles object
`(beauvilleLaszloModuleCechSequence R' M f).cycles`, is glueable. -/
theorem beauvilleLaszloModuleCechH0_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R'
      (beauvilleLaszloModuleCechSequence R' M f).cycles
      f).ShortExact := by
  sorry

-- Proof sketch: Theorem `15.91.16` says the canonical map `M → H^0(Can(M))` reconstructs the
-- same Beauville-Laszlo glueing datum after tensoring with `R'`.
/-- The canonical map `M → \tilde M = H^0(Can(M))`, namely
`(beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles`, becomes bijective after base
change to `R'`. -/
theorem beauvilleLaszloModuleCechH0Map_baseChange_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (((beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles).baseChange R') := by
  sorry

-- Proof sketch: The same Beauville-Laszlo equivalence identifies the localized components of
-- `Can(M)` and `Can(\tilde M)`, so localizing the canonical map away from `f` gives a bijection.
/-- The canonical map `M → \tilde M` from Remark 15.91.17 becomes bijective after localizing away
from `f`. -/
theorem beauvilleLaszloModuleCechH0Map_localizedAway_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (LocalizedModule.map
        (Submonoid.powers f)
        (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles) := by
  sorry

-- Proof sketch: for a glueing pair, the module Cech sequence for `M` is exact in the middle; the
-- canonical map to cycles is therefore surjective by
-- `ShortComplex.exact_iff_surjective_moduleCatToCycles`.
/-- Remark 15.91.17: for a Beauville-Laszlo glueing pair, the canonical map `M → \tilde M` is
surjective. -/
theorem beauvilleLaszloModuleCechH0Map_surjective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Surjective (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles := by
  sorry

end
