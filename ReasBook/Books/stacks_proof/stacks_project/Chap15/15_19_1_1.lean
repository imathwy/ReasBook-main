import stacks_proof.stacks_project.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal PrimeSpectrum

universe u v w

section

variable {R' : Type u} {S' : Type v} {M' : Type w}
variable [CommRing R'] [CommRing S'] [Algebra R' S']
variable [AddCommGroup M'] [Module S' M'] [Module R' M'] [IsScalarTower R' S' M']
variable (I' : Ideal R') (J' : Ideal S')

local notation "K'" => (I'.map (algebraMap R' S') + J' : Ideal S')

/-
Domain triage:
- primary domain: flatness loci of modules over a base ring on closed subsets of `Spec S'`;
- sampled owner declarations: `Module.flatOverBaseLocus`, `Module.mem_flatOverBaseLocus`, and
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`;
- core/canonical owner: `Module.flatOverBaseLocus`;
- primitive data: the sum ideal `I'.map (algebraMap R' S') + J'`;
- derived API: the closed-subset inclusion
  `V(I'.map (algebraMap R' S') + J') ⊆ Module.flatOverBaseLocus R' S' M'`
  and its primewise expansion via `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`;
- `15.19.1.1` is `source-facing`: its main entry should therefore be the sum-ideal closed-subset
  inclusion into `Module.flatOverBaseLocus`, while the primewise expansion is derived API.
-/

/- 15.19.1.1: the source condition is the canonical closed-subset inclusion for the sum ideal
`I'S' + J'`. -/
#check
  zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M'

/- Its primewise formulation is the specialization of
`Ideal.zeroLocus_subset_flatOverBaseLocus_iff` to the same sum ideal. -/
#check
  (zeroLocus_subset_flatOverBaseLocus_iff K' :
    zeroLocus (K' : Set S') ⊆ Module.flatOverBaseLocus R' S' M' ↔
      ∀ q' : PrimeSpectrum S',
        q' ∈ zeroLocus (K' : Set S') →
          Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M'))

end
