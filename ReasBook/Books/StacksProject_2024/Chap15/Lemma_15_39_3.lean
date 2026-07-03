import Mathlib
import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_160_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open CategoryTheory CommRingCat

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsCompleteLocalRing A] [IsCompleteLocalRing B] [IsLocalHom f]

/- Domain-style sampling for Lemma 15.39.3:
- primary domain: local homomorphisms of Noetherian complete local rings presented by finite-index
  formal power series rings;
- sampled owner declarations:
  * `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic`,
  * `exists_powerSeries_model_of_regular_completeLocalRing`,
  * `IsRegularSystemOfParameters`,
  * `IsPartOfRegularSystemOfParameters`;
- source/core/bridge triage:
  * `source-facing`: the existence of a commutative power-series presentation for a local map
    `A → B` with the parameter clause from the source and the flat/regular-fiber consequences used
    later in the chapter;
  * `core/canonical`: `MvPowerSeries σ R` with `[Finite σ]`, the owner predicates
    `IsRegularSystemOfParameters` and `IsPartOfRegularSystemOfParameters`, together with
    `RingHom.Flat`, `Ideal.Fiber`, and `IsRegularLocalRing`;
  * `bridge/view`: the chosen surjective maps `P → A`, `Q → B`, and `P → Q` forming the
    comparison square.
- best owner abstraction: the canonical owners here are the power-series rings themselves together
  with the regular-parameter predicates. The public theorem surface should therefore expose those
  primitive clauses directly instead of hiding them behind a local packaging predicate, and the
  equal-characteristic field branch should be stated with the canonical equal-characteristic
  condition rather than the narrower `CharZero` special case.
- primitive data: finite source and target variable types, coefficient field or Cohen-ring data,
  the three ring maps in the commutative square, and a chosen regular system of parameters on the
  source, indexed by `(maximalIdeal P).spanFinrank`, whose image is part of one on the target.
- derived API: flatness of the vertical map `rToS.Flat` and regularity of the closed fiber
  `(maximalIdeal P).Fiber Q`. -/

-- Proof sketch: in equal characteristic, use the Chapter 10 residue-field presentation owner
-- `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic` on the regular complete
-- local source and target presentation rings; in residue characteristic `p > 0`, use the Chapter
-- 10 Cohen-ring owner `exists_powerSeries_model_of_regular_completeLocalRing`. In both cases
-- Lemmas `15.39.1` and `15.37.5` produce the comparison map `P → Q`, and the parameter,
-- flatness, and regular-fiber clauses are then expressed directly by the canonical owners
-- `IsRegularSystemOfParameters`, `IsPartOfRegularSystemOfParameters`, `RingHom.Flat`, and
-- `IsRegularLocalRing`.
/-- Lemma 15.39.3: a local homomorphism `A → B` of Noetherian complete local rings admits a
commutative surjective presentation by finite-index formal power series rings in which a regular
system of parameters of the source maps to part of one on the target, the vertical map is flat,
and its closed fiber is regular local. In equal characteristic the coefficient rings can be taken
to be fields; in residue characteristic `p > 0` they can be taken to be Cohen rings. -/
theorem exists_powerSeries_presentation_of_localHom_completeLocal :
    (∃ _ : ringChar A = ringChar (ResidueField A),
      ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
        (K L : Type u) (_ : Field K) (_ : Field L),
        let P := MvPowerSeries σ K
        let Q := MvPowerSeries τ L
        ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
          let _ : Algebra P Q := rToS.toAlgebra
          Function.Surjective rToA ∧
            Function.Surjective sToB ∧
            CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
            (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
              (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                  (∀ i, rToS (x i : P) = (z i : Q)) ∧
                  IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
            rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q))
      ∨
      ∃ (p : ℕ) (_ : Nat.Prime p), CharP (ResidueField A) p ∧
        ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
          (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
          (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
          let P := MvPowerSeries σ R₀
          let Q := MvPowerSeries τ S₀
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

-- Proof sketch: this is the equal-characteristic branch of Lemma `15.39.3`, matching the Chapter
-- 10 field-presentation owner in arbitrary equal characteristic.
/-- Equal-characteristic companion to Lemma 15.39.3: if `A` has the same characteristic as its
residue field, then the coefficient rings in the presentation can be taken to be fields. -/
theorem exists_field_powerSeries_presentation_of_localHom_completeLocal
    (hAeqchar : ringChar A = ringChar (ResidueField A)) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (K L : Type u) (_ : Field K) (_ : Field L),
      let P := MvPowerSeries σ K
      let Q := MvPowerSeries τ L
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
              IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

-- Proof sketch: in positive residue characteristic, use the Cohen structure theorem to present
-- both `A` and `B` as quotients of finite-index power series rings over Cohen rings. As above,
-- Lemmas `15.39.1` and `15.37.5` lift the composite source presentation to the target power
-- series ring, and the parameter clause is expressed through the canonical owner
-- `IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank` after reordering the chosen
-- target regular system. Flatness and regularity of the closed fiber are then the same canonical
-- consequences as in the equal-characteristic case.
/-- Positive-residue-characteristic companion to Lemma 15.39.3: if the residue field of `A` has
characteristic `p > 0`, then the coefficient rings in the presentation can be taken to be Cohen
rings. -/
theorem exists_cohen_powerSeries_presentation_of_localHom_completeLocal
    (p : ℕ) (hp : Nat.Prime p) (hAp : CharP (ResidueField A) p) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
      let P := MvPowerSeries σ R₀
      let Q := MvPowerSeries τ S₀
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
              IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

end
