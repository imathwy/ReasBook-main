import Mathlib
import stacks_project.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x

section

variable {R' : Type u} {S' : Type v} {M' : Type w} {R'' : Type x}
variable [CommRing R'] [CommRing S'] [CommRing R'']
variable [Algebra R' S'] [Algebra R' R'']
variable [AddCommGroup M'] [Module S' M'] [Module R' M'] [IsScalarTower R' S' M']
variable {I' : Ideal R'} {I'' : Ideal R''} {J' : Ideal S'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S''" => S' ⊗[R'] R''
local notation "M''" => S'' ⊗[S'] M'

/- Domain triage:
- primary domain: flatness loci of modules over a base ring on closed subsets of `Spec`;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`;
- core/canonical owner: `Module.flatOverBaseLocus`;
- `Lemma 15.19.3` is a `bridge/view` descent statement for that owner, so the flatness hypothesis
  on `V(I'')` should use the same closed-subset inclusion rather than a duplicate primewise
  formulation.

Primitive data vs derived API:
- primitive data: the ring maps `R' → S'` and `R' → R''`, the ideals `I'`, `I''`, `J'`,
  surjectivity of `V(I'') → V(I')`, and the base-changed flatness-locus statement;
- derived API: the primewise flatness of the localizations of `R''` over `V(I'')`, already
  canonically expressed by `zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R''`. -/

-- Proof sketch: given a prime `q'` of `S'` containing `I'S' + J'`, let `p'` be its image in
-- `Spec R'`. Use surjectivity of `V(I'') → V(I')` to choose `p'' ∈ V(I'')` above `p'`, then pick
-- a prime `q''` of `S' ⊗[R'] R''` above both `q'` and `p''`. The hypothesis for `(R'', I'')`
-- gives flatness of the localized base-changed module at `q''` over `R''`. Since `R''_{p''}` is
-- flat over `R'`, Lemma `10.100.1` descends this flatness to `M'_{q'}` over `R'`.
/-- Lemma 15.19.3: if the canonical closed-subset inclusion
`V(I''(S' ⊗[R'] R'') + J'(S' ⊗[R'] R'')) ⊆ Module.flatOverBaseLocus R'' (S' ⊗[R'] R'')
((S' ⊗[R'] R'') ⊗[S'] M')` holds after base change from `R'` to `R''`, then the corresponding
inclusion for `V(I'S' + J')` already holds over `R'`, provided `I'R'' ≤ I''`, the induced map
`V(I'') → V(I')` is surjective, and `I''` has flat-over-`R'` zero locus on `Spec R''`. -/
theorem zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase : zeroLocus
      ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') J' : Ideal S'') :
        Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus ((Ideal.map (algebraMap R' S') I' + J' : Ideal S') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := sorry

/-- The `J' = 0` specialization of Lemma 15.19.3, phrased directly as the canonical closed-subset
inclusion `V(I'S') ⊆ Module.flatOverBaseLocus R' S' M'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R' R''))
      (zeroLocus (I'' : Set R'')) (zeroLocus (I' : Set R')))
    (hlocFlat : zeroLocus (I'' : Set R'') ⊆ Module.flatOverBaseLocus R' R'' R'')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R'' S'') I'' : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'') :
    zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' := by
  have hbase' :
      zeroLocus
          ((Ideal.map (algebraMap R'' S'') I'' + Ideal.map (algebraMap S' S'') (⊥ : Ideal S') :
              Ideal S'') : Set S'') ⊆
        Module.flatOverBaseLocus R'' S'' M'' := by
    simpa [Ideal.map_bot, Ideal.add_eq_sup, sup_bot_eq] using hbase
  intro q hq
  exact zeroLocus_add_subset_flatOverBaseLocus_of_surjOn_zeroLocus_descends
    hI'' hsurj hlocFlat hbase' <| by
      simpa [Ideal.add_eq_sup, sup_bot_eq] using hq

end
