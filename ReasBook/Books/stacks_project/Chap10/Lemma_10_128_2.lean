import Mathlib
import stacks_project.Chap10.Definition_10_60_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

/- Domain-style sampling pass.
* primary domain: local commutative algebra of flat local homomorphisms out of a regular local
  ring, detected by the image of a regular system of parameters;
* sampled owner declarations:
  `IsRegularSystemOfParameters`,
  `IsRegularSystemOfParameters.isRegular`,
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`;
* best owner abstraction: the source-facing primitive datum is the chosen family
  `x : Fin d → maximalIdeal R` together with `hx : IsRegularSystemOfParameters x`; the list
  `List.ofFn fun i ↦ algebraMap R S (x i : R)` is only the bridge/view presenting the induced
  sequence in `S`, while the conclusion belongs on the canonical flatness owner `Module.Flat R S`.
* primitive data: the local map `R → S`, the regular-local owner on `R`, the Noetherian-local
  owner on `S`, the chosen regular system of parameters `x`, and regularity of its image in `S`;
* derived API: regularity of the underlying sequence in `R` from `hx.isRegular`, the regular-local
  prefix quotients from
  `IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal`, and the inductive
  flatness step furnished by `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`.

Source/core/bridge triage:
* source-facing: Lemma `10.128.2` itself;
* core/canonical: `IsRegularSystemOfParameters`, `Sequence.IsRegular`, and `Module.Flat`;
* bridge/view: the `List.ofFn` presentation of the image sequence in `S`.
-/

-- Proof sketch: let `d = ringKrullDim R`, and write the chosen regular system of parameters as
-- `x₁, …, x_d`. Since `R / (x₁, …, x_d)` is a field, the final quotient of `S` is flat over the
-- final quotient of `R`. Then apply
-- `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal` inductively up the regular sequence,
-- using at each step that the next parameter is a nonzerodivisor on the corresponding quotient of
-- `S`.
/-- Lemma 10.128.2: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring and a regular system of parameters of length `d = ringKrullDim R` maps to a
regular sequence in `S`, then `S` is flat over `R`. -/
theorem flat_of_regularSystemOfParameters_image_isRegular
    {d : ℕ} (x : Fin d → maximalIdeal R)
    (hx : IsRegularSystemOfParameters x)
    (hreg : IsRegular S (List.ofFn fun i ↦ algebraMap R S (x i : R))) :
    Module.Flat R S := sorry

end
