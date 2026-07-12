import Mathlib
import StacksProject_2024.Chap10.Lemma_10_99_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing RingTheory

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => S ⧸ 𝔪S

/- Domain sampling pass:
* primary domain: regular sequences under flat local base change and flatness of the resulting
  quotient rings;
* sampled owner declarations:
  - `RingTheory.Sequence.IsRegular`;
  - `RingTheory.Sequence.isRegular_cons_iff'`;
  - `RingTheory.Sequence.IsRegular.ndrecIterModByRegularWithRing`;
  - `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor`;
* source-facing layer: regularity of the image of `fs` in the closed-fiber quotient `ClosedFiber`;
* core/canonical layer: the owner predicate `RingTheory.Sequence.IsRegular`;
* bridge/view layer: the prefix quotients `S ⧸ Ideal.ofList (fs.take (i + 1))`.

Primitive data vs derived API:
* primitive data: the flat local map `R → S` and the regularity hypothesis on the image sequence in
  `ClosedFiber`, together with the Noetherian hypothesis on `S` needed by the flat-quotient owner
  theorem for each regular element;
* derived API: regularity of `fs` in `S` and flatness of the successive quotient rings.
-/

-- Proof sketch: use the owner induction principle
-- `Sequence.IsRegular.ndrecIterModByRegularWithRing` on the regular sequence in `ClosedFiber`. For
-- the first element, apply `flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor` to the head
-- in the closed fiber. Then pass to the quotient by that head and use the inductive
-- characterization of `Sequence.IsRegular` for the tail.
/-- Lemma 10.99.3: if `R → S` is a flat local homomorphism of local rings, `S` is Noetherian, and
the images of a finite sequence `fs` in the closed fibre `S / 𝔪S`, where `𝔪` is the maximal ideal
of `R`, form a regular sequence, then `fs` is a regular sequence in `S`, and each quotient by a
nonempty initial segment of `fs` is flat over `R`. -/
theorem isRegular_and_flat_quotient_take_of_closedFiber_isRegular (fs : List S)
    (hfs : Sequence.IsRegular ClosedFiber (fs.map (Ideal.Quotient.mk 𝔪S))) :
    Sequence.IsRegular S fs ∧
      ∀ i : Fin fs.length, Module.Flat R (S ⧸ Ideal.ofList (fs.take (i + 1))) := sorry

end
