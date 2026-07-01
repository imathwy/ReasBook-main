import Mathlib
import stacks_project.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/- 
Domain-style sampling:
- primary domain: local Krull dimension on `Spec(S)` for finite type algebras over a field, under
  tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`,
  `topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field`;
- best owner abstraction: the source-facing theorem should remain an equality between the canonical
  local-dimension owner values `topologicalKrullDimAt x` and `topologicalKrullDimAt xK`, while the
  supporting local-ring/fiber calculations are already owned upstream by `Localization.AtPrime`,
  `fiberLocalRingAt`, and the dimension formulas in Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
- primitive data: only the point `x : PrimeSpectrum S`, the point `xK : PrimeSpectrum S_K`, and
  the canonical contraction witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: any quotient-presentation or localization comparison used in the proof. No extra
  public wrapper or duplicate local owner should be introduced here.

Source/core/bridge triage:
* `source-facing`: the invariance of `topologicalKrullDimAt` under tensoring a finite type
  `k`-algebra with a field extension `K / k`;
* `core/canonical`: `topologicalKrullDimAt`, `Localization.AtPrime`, `fiberLocalRingAt`, and the
  local dimension formulas from Lemmas `10.112.7`, `10.116.3`, and `10.116.4`;
* `bridge/view`: the tensor base-change morphism `iSK` and the induced prime-spectrum contraction
  equation `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: present `S` as a quotient of a polynomial ring over `k`, base change that
-- presentation to `K`, and compare the height differences given by Lemma `10.112.7` for the two
-- vertical flat maps in the resulting square of local rings. Then use the local-dimension formula
-- from Lemma `10.116.4` for the quotient presentations upstairs and downstairs to cancel the same
-- ambient polynomial-ring dimension.
/-- Lemma 10.116.6: if `S` is a finite type `k`-algebra, `x : Spec(S)` corresponds to a prime of
`S`, and `xK : Spec(K ⊗[k] S)` corresponds to a prime of `K ⊗[k] S` lying over `x`, then the
local topological Krull dimensions at `x` and `xK` are equal. -/
lemma primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    topologicalKrullDimAt x = topologicalKrullDimAt xK := sorry

end
