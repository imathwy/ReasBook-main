import StacksProject_2024.Chap15.«15_18_0_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {I : Ideal R} {I' : Ideal R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

namespace Ideal

/- Domain triage:
- primary domain: flatness loci of modules on closed subsets of `Spec` under tensor-product base
  change in commutative algebra;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`, `Module.Flat.baseChange`,
  `LocalizedModule.equivTensorProduct`;
- core/canonical owner: `Module.flatOverBaseLocus`;
- layer choice here: `source-facing`; the Stacks lemma is the base-change stability of the
  canonical closed-subset inclusion, while the primewise localization formulation is derived API.

Primitive data vs derived API:
- primitive data: the original closed-subset inclusion into `Module.flatOverBaseLocus` and the
  ideal containment `IR' ≤ I'`;
- derived API: the primewise statement for localizations above primes in the closed subset;
- the local base-change step itself is most canonically expressed by the tensor-product/base-change
  owners `LocalizedModule.equivTensorProduct`, `isLocalizedModule_iff_isBaseChange`, and
  `Module.Flat.baseChange`, rather than by a separate ad hoc localization wrapper.
-/

private theorem le_comap_asIdeal_of_mem_zeroLocus_map_le
    {K : Ideal S} {K' : Ideal S'} {q' : PrimeSpectrum S'}
    (hq' : q' ∈ zeroLocus (K' : Set S'))
    (hK' : Ideal.map (algebraMap S S') K ≤ K') :
    K ≤ Ideal.comap (algebraMap S S') q'.asIdeal := by
  have hq'le : K' ≤ q'.asIdeal := (mem_zeroLocus q' (K' : Set S')).1 hq'
  exact Ideal.map_le_iff_le_comap.mp <| le_trans hK' hq'le

-- Proof sketch: let `q'` be a prime of `S'` containing the extension of `I'`, and let `q` be its
-- image in `Spec S`. The hypothesis gives flatness of `M_q` over `R`. Localizing the tensor-product
-- square at `q'` identifies the localized base-changed module with the textbook local base change
-- of `M_q` via the canonical localization/tensor-product equivalences, and then
-- `Module.Flat.baseChange` gives the required flatness over `R'`.
/-- Base-change stability of a flatness-locus inclusion along any closed subset whose defining
ideal contains the extension of the original one. This is the owner-level closed-subset form used
by later Stacks specializations with additional algebra-side summand ideals. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le
    {K : Ideal S} {K' : Ideal S'}
    (hflat : zeroLocus (K : Set S) ⊆ Module.flatOverBaseLocus R S M)
    (hK' : Ideal.map (algebraMap S S') K ≤ K') :
    zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M' := by
  sorry

/-- Lemma 15.18.1: if `15.18.0.1` holds for `(R → S, I, M)`, then after a base change `R → R'`
and for any ideal `I'` containing `IR'`, the corresponding closed-subset inclusion into the
flat-over-base locus holds for `(R' → S', I', M')`. -/
@[stacks 052X]
theorem zeroLocus_subset_flatOverBaseLocus_of_baseChange
    (hflat : zeroLocus (I.map (algebraMap R S) : Set S) ⊆ Module.flatOverBaseLocus R S M)
    (hI' : I.map (algebraMap R R') ≤ I') :
    zeroLocus (I'.map (algebraMap R' S') : Set S') ⊆ Module.flatOverBaseLocus R' S' M' := by
  let iR' : R' →+* S' := (Algebra.TensorProduct.includeRight : R' →ₐ[R] S').toRingHom
  have hmap_eq :
      Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) I) =
        Ideal.map iR' (Ideal.map (algebraMap R R') I) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    simpa [iR'] using
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
        (algebraMap S S').comp (algebraMap R S) =
          ((Algebra.TensorProduct.includeRight : R' →ₐ[R] S').toRingHom).comp
            (algebraMap R R'))
  have hK' :
      Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) I) ≤
        Ideal.map (algebraMap R' S') I' := by
    rw [hmap_eq]
    simpa [iR'] using Ideal.map_mono hI'
  exact zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le hflat hK'

end Ideal

end
