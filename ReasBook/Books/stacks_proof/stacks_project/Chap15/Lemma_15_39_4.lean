import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_160_2
import stacks_proof.stacks_project.Chap15.Lemma_15_6_2
import stacks_proof.stacks_project.Chap15.Situation_15_6_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R S S' : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [IsCompleteLocalRing S] [IsNoetherianRing S]
variable [IsCompleteLocalRing S'] [IsNoetherianRing S']

/- Domain-style sampling:
- primary domain: surjective pullbacks of complete Noetherian local rings;
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `quotient_isCompleteLocalRing`,
  `IsLocalRing.of_surjective'`,
  `Function.Surjective.isLocalHom`;
- best owner abstraction: the chapter pullback owner `SurjectiveRingPullbackSituation` with its
  derived fibre-product ring `Bprime`;
- primitive data: the two complete Noetherian local source rings `S`, `S'`, the pullback owner
  `T : SurjectiveRingPullbackSituation S R S'`, the built-in surjectivity of `T.fromAprime`, and
  the remaining surjectivity hypothesis on `T.toA`;
- derived API: `R` is a local ring by `IsLocalRing.of_surjective'` applied to `T.fromAprime`, both
  maps to `R` are local by `Function.Surjective.isLocalHom`, `R` is complete local and Noetherian as a
  quotient of `S'`, and the fibre-product ring `T.Bprime` is complete local and Noetherian.

Source/core/bridge triage:
- `source-facing`: the fibre-product ring of two surjective local maps to a common complete local
  base;
- `core/canonical`: the predicates `IsCompleteLocalRing` and `IsNoetherianRing`;
- `bridge/view`: `SurjectiveRingPullbackSituation`, which packages the surjective pullback owner
  already used earlier in the chapter. -/

-- Proof sketch: first note that `R` is already a local ring by surjectivity of
-- `T.fromAprime : S' → R`, and then both maps `T.toA` and `T.fromAprime` are local by the
-- canonical surjective-local API. The same surjective map `T.fromAprime` exhibits `R` as a
-- quotient of the complete Noetherian local ring `S'`, so `R` is complete local and Noetherian.
-- Then realize the fibre product `S ×_R S'` as the categorical pullback of `T.toA` and
-- `T.fromAprime`. Using the Cohen-structure-theorem argument from the source, one gets a
-- surjection from a formal power series ring onto this pullback ring; hence it is complete local.
-- The same presentation shows the pullback is a quotient of a power series ring over a Cohen ring
-- or residue field, hence Noetherian as well.
namespace SurjectiveRingPullbackSituation

variable (T : SurjectiveRingPullbackSituation S R S') (h_toA : Function.Surjective T.toA)

/-- Helper for Lemma 15.39.4: a surjective ring map to a nontrivial ring has proper kernel. -/
lemma ker_ne_top_of_surjective {A B : Type u} [CommRing A] [CommRing B] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) :
    RingHom.ker φ ≠ ⊤ := by
  -- Lift `1` across the surjection; if the kernel were all of `A`, that lift would map to `0`.
  intro hker
  obtain ⟨a, ha⟩ := hφ 1
  have haKer : a ∈ RingHom.ker φ := by
    simpa [hker]
  have hzero : φ a = 0 := RingHom.mem_ker.mp haKer
  have hone : (1 : B) = 0 := by
    simpa [ha] using hzero
  exact one_ne_zero hone

/-- Helper for Lemma 15.39.4: the common target of the surjective pullback square is itself a
complete local ring. -/
lemma base_isCompleteLocalRing_of_surjective_target
    [Nontrivial R]
    (T : SurjectiveRingPullbackSituation S R S') :
    IsCompleteLocalRing R := by
  letI : IsLocalRing R := IsLocalRing.of_surjective' T.fromAprime T.fromAprime_surjective
  let e : S' ⧸ RingHom.ker T.fromAprime ≃+* R :=
    RingHom.quotientKerEquivOfSurjective T.fromAprime_surjective
  let hQ :
      IsCompleteLocalRing (S' ⧸ RingHom.ker T.fromAprime) :=
    quotient_isCompleteLocalRing (RingHom.ker T.fromAprime)
      (ker_ne_top_of_surjective T.fromAprime T.fromAprime_surjective)
  have hcomplete : IsAdicComplete (maximalIdeal R) R := by
    -- Transport maximal-ideal adic completeness across the quotient-kernel equivalence.
    rw [← IsAdicComplete.congr_ringEquiv
      (maximalIdeal R) e.symm]
    simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using
      (hQ.toIsAdicComplete :
        IsAdicComplete (maximalIdeal (S' ⧸ RingHom.ker T.fromAprime))
          (S' ⧸ RingHom.ker T.fromAprime))
  exact { toIsLocalRing := inferInstance, toIsAdicComplete := hcomplete }

/-- Helper for Lemma 15.39.4: the common target of the surjective pullback square is Noetherian
because it is a quotient of `S'`. -/
lemma base_isNoetherianRing_of_surjective_target
    [Nontrivial R]
    (T : SurjectiveRingPullbackSituation S R S') :
    IsNoetherianRing R := by
  let e : S' ⧸ RingHom.ker T.fromAprime ≃+* R :=
    RingHom.quotientKerEquivOfSurjective T.fromAprime_surjective
  letI : IsNoetherianRing (S' ⧸ RingHom.ker T.fromAprime) := by
    infer_instance
  exact isNoetherianRing_of_ringEquiv (S' ⧸ RingHom.ker T.fromAprime) e

/-- Helper for Lemma 15.39.4: a surjective cover by a complete local ring makes the pullback ring
complete local. -/
lemma isCompleteLocalRing_of_surjective_cover
    {P : Type u} [CommRing P] [IsCompleteLocalRing P] [Nontrivial T.Bprime]
    (φ : P →+* T.Bprime) (hφ : Function.Surjective φ) :
    IsCompleteLocalRing T.Bprime := by
  -- TODO: once the common power-series cover is in hand, descend completeness by combining
  -- `RingHom.quotientKerEquivOfSurjective` with `quotient_isCompleteLocalRing`.
  sorry

/-- Helper for Lemma 15.39.4: a surjective cover by a Noetherian ring makes the pullback ring
Noetherian. -/
lemma isNoetherianRing_of_surjective_cover
    {P : Type u} [CommRing P] [IsNoetherianRing P] [Nontrivial T.Bprime]
    (φ : P →+* T.Bprime) (hφ : Function.Surjective φ) :
    IsNoetherianRing T.Bprime := by
  let e : P ⧸ RingHom.ker φ ≃+* T.Bprime :=
    RingHom.quotientKerEquivOfSurjective hφ
  letI : IsNoetherianRing (P ⧸ RingHom.ker φ) := by
    infer_instance
  exact isNoetherianRing_of_ringEquiv (P ⧸ RingHom.ker φ) e

/-- Lemma 15.39.4: if `S → R` and `S' → R` are surjective local homomorphisms of complete
Noetherian local rings, then the fibre product `S ×_R S'`, formalized by the canonical pullback
owner `T.Bprime`, is again a complete local ring. -/
@[stacks 09Q8]
theorem bprime_isCompleteLocalRing_of_surjective :
    IsCompleteLocalRing T.Bprime := by
  -- Route correction: keep the source-faithful plan of producing one common finite-variable
  -- power-series cover of `T.Bprime`, then descend completeness through the quotient-kernel model.
  --
  -- TODO: as written, the theorem header does not assume the common target ring `R` is
  -- nontrivial/local. The textbook statement needs `R` to be a complete Noetherian local ring;
  -- without that, the claim is false (for the trivial target ring, the pullback is a product).
  -- TODO: build the common power-series cover over a coefficient field or Cohen ring using the
  -- synchronized coefficient-ring lifts from the source proof, and then close with
  -- `isCompleteLocalRing_of_surjective_cover`.
  sorry

/-- Under the same hypotheses, the pullback ring `T.Bprime = S ×_R S'` is Noetherian. -/
theorem bprime_isNoetherianRing_of_surjective :
    IsNoetherianRing T.Bprime := by
  -- The intended source route is to reuse the same surjective power-series cover as above and
  -- descend Noetherianity through `isNoetherianRing_of_surjective_cover`.
  --
  -- TODO: the current theorem statement is missing the target-side local/nontrivial hypotheses
  -- from the source. The trivial-target counterexample blocks any direct proof under the present
  -- header.
  -- TODO: once the common power-series cover of `T.Bprime` is constructed, close by transporting
  -- the quotient Noetherian instance across `RingHom.quotientKerEquivOfSurjective`.
  sorry

end SurjectiveRingPullbackSituation

end
