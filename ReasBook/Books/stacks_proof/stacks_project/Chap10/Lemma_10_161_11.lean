import stacks_proof.stacks_project.Chap10.Definition_10_161_1
import stacks_proof.stacks_project.Chap10.Lemma_10_161_7
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization and the `N-1`/`N-2` conditions;
* owner abstractions sampled:
  - `IsN1Ring` and `IsN2Ring`, the chapter-owner source-facing classes from
    `Definition_10_161_1`;
  - `isN2Ring_of_finite_extension`, the chapter bridge/view theorem for descending `N-2` along a
    finite extension of domains;
  - `Lemma 10.161.8` / `IsIntegralClosure.finite`, the chapter recall of the canonical finite
    integral-closure theorem for finite separable fraction-field extensions over a Noetherian
    normal domain.
* layer triage:
  - `source-facing`: the equivalence theorem below;
  - `core/canonical`: the owner classes `IsN1Ring` and `IsN2Ring`;
  - `bridge/view`: passing to the normalization `integralClosure R (FractionRing R)` and
    descending `N-2` back to `R` through `isN2Ring_of_finite_extension`.
* primitive data are only the ring `R` together with the Noetherian, domain, and
  characteristic-zero hypotheses. Finiteness of the normalization and separability of finite
  fraction-field extensions are derived API from the owner abstractions and mathlib.
-/

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CharZero (FractionRing R)]

-- Proof sketch: the implication `IsN2Ring R → IsN1Ring R` is the owner instance from
-- `Definition 10.161.1`. For the converse, pass to the normalization
-- `S = integralClosure R (FractionRing R)`, which is finite over `R` by the `N-1` hypothesis.
-- The ring `S` is a Noetherian normal domain with fraction field `FractionRing R`, so every
-- finite extension of its fraction field is separable in characteristic zero and
-- Lemma `10.161.8` / `IsIntegralClosure.finite` makes `S` an `N-2` ring. Then descend `N-2`
-- from `S` to `R` via the finite-extension theorem `isN2Ring_of_finite_extension`.
/-- Lemma 10.161.11: A Noetherian domain whose fraction field has characteristic zero is `N-1`
if and only if it is `N-2`, i.e. Japanese. -/
@[stacks 032M]
theorem isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero
    : IsN1Ring R ↔ IsN2Ring R := by
  constructor
  · intro hN1
    let S := integralClosure R (FractionRing R)
    letI : Module.Finite R S := hN1.integralClosure_finite
    letI : IsFractionRing S (FractionRing R) :=
      integralClosure.isFractionRing_of_finite_extension
        (A := R) (K := FractionRing R) (L := FractionRing R)
    letI : CharZero S := RingHom.charZero (algebraMap S (FractionRing R))
    letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    letI : IsIntegrallyClosed S :=
      integralClosure.isIntegrallyClosedOfFiniteExtension
        (R := R) (K := FractionRing R) (L := FractionRing R)
    have hRS : Function.Injective (algebraMap R S) := by
      intro x y hxy
      apply IsFractionRing.injective R (FractionRing R)
      simpa [S] using congrArg (fun z : S => (z : FractionRing R)) hxy
    have hSN2 : IsN2Ring S := by
      -- The normalization has the same fraction field, so characteristic zero forces every finite
      -- extension of that fraction field to be separable.
      refine IsN2Ring.mk ?_
      intro L _ _ _ _ _
      letI : PerfectField (FractionRing S) := PerfectField.ofCharZero
      letI : Algebra.IsSeparable (FractionRing S) L :=
        Algebra.IsAlgebraic.isSeparable_of_perfectField
      letI : Algebra S (integralClosure S L) :=
        SubalgebraClass.toAlgebra (s := integralClosure S L)
      letI : SMul S (integralClosure S L) :=
        (show Algebra S (integralClosure S L) from inferInstance).toSMul
      have hScalarTower : IsScalarTower S (integralClosure S L) L := by
        refine IsScalarTower.of_algebraMap_eq ?_
        intro x
        cases x
        rfl
      letI : IsScalarTower S (integralClosure S L) L := hScalarTower
      -- Lemma 10.161.8 applies to the Noetherian normal domain `S`.
      exact IsIntegralClosure.finite S (FractionRing S) L (integralClosure S L)
    letI : IsN2Ring S := hSN2
    -- Descend the `N-2` property along the finite normalization map `R → S`.
    exact isN2Ring_of_finite_extension (R := R) (S := S) hRS
  · intro hN2
    letI : IsN2Ring R := hN2
    -- The reverse implication is the owner instance `IsN2Ring R → IsN1Ring R`.
    infer_instance

end
