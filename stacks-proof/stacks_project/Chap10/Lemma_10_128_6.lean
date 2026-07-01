import stacks_project.Chap10.Lemma_10_128_5

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

open IsLocalRing RingTheory

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
variable [IsLocalHom (algebraMap R S)] [Module.Flat R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling for Lemma 10.128.6:
- primary domain: regular sequences on the canonical closed fiber of a flat local map, together
  with flatness of the successive quotient rings over the base;
- sampled owner declarations:
  `Ideal.Fiber`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff'`,
  `flat_quotient_and_isRegular_of_isRegular_closedFiber_of_essFinitePresentation`,
  `isRegular_and_flat_quotient_take_of_closedFiber_isRegular`;
- best owner abstraction: the core owner is the regular-sequence predicate
  `RingTheory.Sequence.IsRegular` on the canonical fiber ring
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the quotient-by-prefix rings
  `S ⧸ Ideal.ofList (fs.take (i + 1))` are derived bridge data;
- primitive data: the flat local map `R → S`, the essential finite presentation hypothesis
  `RingHom.EssFinitePresentation (algebraMap R S)`, and regularity of the image sequence in the
  canonical closed fiber under `algebraMap S ClosedFiber`;
- derived API: regularity of `fs` in `S` and flatness of the nonempty prefix quotients over `R`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for sequences regular on the closed fiber;
- `core/canonical`: `Ideal.Fiber`, `RingTheory.Sequence.IsRegular`,
  `RingHom.EssFinitePresentation`, and `Module.Flat`;
- `bridge/view`: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of `ClosedFiber`, together with the explicit
  quotient rings `S ⧸ Ideal.ofList (fs.take (i + 1))`.
-/

-- Proof sketch: argue by induction on `fs`. The base step is trivial. For the inductive step,
-- transport regularity of the head along the canonical quotient view
-- `ClosedFiber ≃ₐ[R] S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and apply Lemma `10.128.5`
-- to get that the head is regular in `S` and that the first quotient is flat over `R`. Then pass
-- to the quotient by the head and apply the induction hypothesis to the tail sequence.
/-- Lemma 10.128.6: for a flat essentially finitely presented local homomorphism `R → S`, if the
images of a finite sequence `fs` in the canonical closed fiber
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently in the quotient
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, form a regular sequence, then `fs` is a
regular sequence in `S`, and each quotient by a nonempty initial segment of `fs` is flat over
`R`. -/
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular_of_essFinitePresentation
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (algebraMap S ClosedFiber))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

end
