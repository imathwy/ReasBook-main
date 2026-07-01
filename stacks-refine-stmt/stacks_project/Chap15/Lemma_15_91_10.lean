import Mathlib
import stacks_project.Chap15.Lemma_15_90_3
import stacks_project.Chap15.«15_91_9_1»
import stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped IdealPowerTorsion

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo module glueability, expressed through the module Cech short
  complex and the canonical tensor base-change map on `(f)^∞`-torsion;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `tensorBaseChangeUnitPrimaryComponent`,
  `TensorProduct.comm`,
  `IsBeauvilleLaszloGlueingPairAlong`;
- best owner abstraction: the primitive comparison map is the chapter owner
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`, i.e. the canonical tensor
  base-change unit restricted to the primary component for `(f)`;
- primitive data vs derived API: the primitive data are the module Cech short complex and the
  canonical primary-component base-change map; the injectivity, surjectivity, and glueability
  criteria are derived API.

Source/core/bridge triage:
- `source-facing`: the Beauville-Laszlo exactness criteria for modules;
- `core/canonical`: `(beauvilleLaszloModuleCechSequence R' M f).ShortExact` and
  `tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M`;
- `bridge/view`: the textbook right-tensor order `M ⊗[R] R'`, related by tensor symmetry to the
  canonical owner `R' ⊗[R] M`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: tensor the right exact ring sequence `R → R' → R'_f` with `M`. Right exactness of
-- `M ⊗[R] -` turns the surjectivity statement from Lemma `15.91.6` into surjectivity of the
-- module-side right map.
/-- The module Beauville-Laszlo sequence is exact on the right under the quotient-isomorphism
hypothesis. -/
theorem beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Surjective ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := sorry

-- Proof sketch: the kernel of `M → M ⊗[R] Localization.Away f` is `M[f^∞]`. Therefore the left
-- Cech map is injective exactly when the comparison map from `M[f^∞]` to the `f^∞`-torsion of
-- `R' ⊗[R] M` is injective; via tensor symmetry this is the usual map to `(M ⊗[R] R')[f^∞]`.
/-- The module Beauville-Laszlo sequence is exact on the left exactly when the canonical
base-change map on `(f)^∞`-torsion is injective. -/
theorem beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
    (f : R) :
    Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: if the sequence is exact in the middle, then an `f^∞`-torsion element of
-- `R' ⊗[R] M` yields a kernel element of the right map and so comes from `M`. Conversely,
-- surjectivity on `f^∞`-torsion lets one lift the torsion correction needed to express a kernel
-- element of the right map as the image of an element of `M`.
/-- Under the quotient-isomorphism hypothesis, the module Beauville-Laszlo sequence is exact in the
middle exactly when the canonical base-change map on `(f)^∞`-torsion is surjective. -/
theorem beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) ↔
    Function.Surjective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: combine right exactness with the previous injectivity and surjectivity criteria.
-- Glueability is injectivity on the left, exactness in the middle, and surjectivity on the right,
-- so under the quotient-isomorphism hypothesis it is equivalent to bijectivity on `f^∞`-torsion.
/-- Lemma 15.91.10: if `R → R'` induces isomorphisms `R / f^n R → R' / f^n R'` for all positive
integers `n`, then `M` is glueable for `(R → R', f)` if and only if the induced map
on `(f)^∞`-torsion is bijective. -/
theorem isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Bijective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

-- Proof sketch: if `(R → R', f)` is a glueing pair, the ring-level Beauville-Laszlo sequence is
-- exact, and tensoring that exact sequence with `M` gives exactness in the middle for the
-- module-side sequence. The main criterion then reduces glueability to injectivity on
-- the canonical base-change map on `(f)^∞`-torsion.
/-- For a Beauville-Laszlo glueing pair `(R → R', f)`, module glueability is equivalent to
injectivity on `f^∞`-torsion. -/
theorem isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponent R' (principalIdeal f) M) := sorry

end

section

variable {R : Type u} [CommRing R]

variable {M : Type u} [AddCommGroup M] [Module R M]

-- Proof sketch: specialize the previous theorem to `R' = R^∧`. For a Beauville-Laszlo glueing
-- pair `(R, f)`, the completion pair is exact in the middle for every `M`, so only injectivity of
-- the canonical base-change map on `(f)^∞`-torsion remains.
/-- If `(R, f)` is a Beauville-Laszlo glueing pair, then `M` is glueable along the completion map
if and only if the canonical base-change map on `(f)^∞`-torsion is injective. -/
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f))
      f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective
        (tensorBaseChangeUnitPrimaryComponent
          (principalAdicCompletion f)
          (principalIdeal f)
          M) := sorry

end
