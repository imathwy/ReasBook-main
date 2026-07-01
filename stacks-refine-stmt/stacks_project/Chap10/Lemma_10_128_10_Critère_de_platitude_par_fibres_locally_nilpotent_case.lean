import stacks_project.Chap10.Definition_10_32_1
import stacks_project.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R}
variable [AddCommGroup M] [Module S' M]
variable [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.FinitePresentation S' M]

local notation "IS" => Ideal.map (algebraMap R S) I
local notation "FiberRing" => S ⧸ IS
local notation "FiberModule" => FiberRing ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for the locally nilpotent fiberwise flatness criterion:
* primary domain: fiberwise flatness for finitely presented modules over a locally nilpotent
  thickening, with fiber hypotheses carried by the canonical fiber module owner;
* sampled owner declarations of the same kind:
  `Ideal.qoutMapEquivTensorQout`,
  `Definition_10_65_2.mem_relativeAssassin_iff_fiber`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the primitive fiber hypothesis should live on
  `FiberModule = FiberRing ⊗[S] M`, where `FiberRing = S ⧸ Ideal.map (algebraMap R S) I` is the
  quotient presentation of the arbitrary-ideal fiber ring, equivalently
  `(R ⧸ I) ⊗[R] S` via `Ideal.qoutMapEquivTensorQout`; the quotient module
  `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))` is only a bridge view.

Primitive data vs. derived API:
* primitive data: the locally nilpotent ideal `I`, the algebra tower `R → S → S'`, the finite-type
  and finite-presentation hypotheses, the finitely presented `S'`-module `M`, flatness of the
  canonical fiber module `FiberModule` over `FiberRing`, and flatness of the restricted
  `R`-module `RestrictScalars R S' M`;
* derived API: flatness of the restricted `S`-module `RestrictScalars S S' M`, then flatness and
  essential finite presentation of the localizations `S_q` over `R`.

Source/core/bridge triage:
* `source-facing`: the three theorems below, which are the locally nilpotent variant of the
  fiberwise flatness criterion;
* `core/canonical`: the fiber module owner `FiberModule`, `Module.Flat`, and
  `RingHom.EssFinitePresentation`;
* `bridge/view`: the quotient models of the fiber ring and fiber module modulo `IS`.
-/

-- Proof sketch: first pass from the locally nilpotent ideal `I` to the closed fibers over the
-- primes `p = q ∩ R`; since `I ⊆ p`, base change of the canonical fiber-flatness hypothesis on
-- `FiberModule` yields flatness of the closed fiber over `p`. Apply the local fiberwise flatness
-- criterion of Lemma `10.128.9` to `R_p → S_q → S'_{q'}` for primes `q'` of `S'` above `q`,
-- obtaining flatness of the localized module over `S_q`. Then use the prime-local criterion for
-- flatness to conclude `RestrictScalars S S' M` is flat over `S`.
/-- Lemma 10.128.10 (Critère de platitude par fibres: locally nilpotent case): if `I` is a locally
nilpotent ideal of `R`, `R → S` is of finite type, `R → S'` is of finite presentation, `M` is a
finitely presented `S'`-module, the canonical fiber module
`FiberModule = (S ⧸ Ideal.map (algebraMap R S) I) ⊗[S] M`,
equivalently `M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M))`, is flat over the
canonical fiber ring `FiberRing = S ⧸ Ideal.map (algebraMap R S) I`, equivalently
`(R ⧸ I) ⊗[R] S`, and the restricted `R`-module `RestrictScalars R S' M` is flat over `R`, then
the restricted `S`-module `RestrictScalars S S' M` is flat over `S`. -/
theorem flat_over_middleRing_of_locallyNilpotent_of_flat_over_base_and_flat_mod_extended_ideal
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

-- Proof sketch: choose a prime `q'` of `S'` above `q` using the nontrivial fiber hypothesis and
-- Lemma `10.18.6`. For `p = q ∩ R`, the locally nilpotent hypothesis gives `I ⊆ p`, so base
-- change of `hflat_fiber` gives flatness of the canonical fiber over `p`. Apply Lemma `10.128.9`
-- to the local diagram `R_p → S_q → S'_{q'}` and the localized module `M_{q'}`.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is flat over `R`. -/
theorem localized_flat_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

-- Proof sketch: with the same localization setup as above, Lemma `10.128.9` shows that the local
-- ring map `R_p → S_q` is essentially of finite presentation. Interpreting this as a statement
-- about the localized `R`-algebra `S_q` gives the claimed essential finite presentation.
/-- If the residue-field fiber `(RestrictScalars S S' M) ⊗[S] κ(q)` is nontrivial, then the
localization `S_q` is essentially of finite presentation over `R`. -/
theorem localized_essFinitePresentation_of_locallyNilpotent_of_nontrivial_fiber
    (hI : I.IsLocallyNilpotent)
    (hflat_fiber : Module.Flat FiberRing FiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (hq : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    RingHom.EssFinitePresentation (algebraMap R (Localization.AtPrime q.asIdeal)) := sorry

end
