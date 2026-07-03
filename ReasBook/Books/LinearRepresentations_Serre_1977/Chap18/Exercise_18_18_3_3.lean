import Mathlib
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u x

namespace Representation

section

open PrimeToPRoot FDRep

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ}
variable [CharP k p]
variable {ι : Type x}

/- Domain-style sampling:
* primary domain: Brauer and ordinary characters on the canonical owner
  `PRegularConjClass G p`;
* relevant owner declarations inspected upstream in the chapter/project:
  `FDRep.ordinaryCharacterOnPRegularConjClass`,
  `FDRep.ordinaryCharacterOnPRegularConjClass_ofSubtype`,
  `FDRep.modularCharacterOnPRegularConjClass`,
  `FDRep.modularCharacterOnPRegularConjClass_ofSubtype`,
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions`,
  `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply`,
  `Representation.exists_residueFieldLift_of_isIrreducible_of_isPSolvable`;
* best owner abstraction: class functions on `PRegularConjClass G p`, with ordinary and modular
  character constructions treated as the source-facing views on that owner;
* primitive data: for parts `(1)` and `(2)`, an injective multiplicative lift
  `PrimeToPRoot p k →* Kˣ` and a simple modular representation `S`; for part `(3)`, only the
  same multiplicative lift, together with a complete pairwise-nonisomorphic irreducible family
  `E : ι → FDRep k G`, a simple ordinary representation `X`, and its nonnegative integral
  expansion in the Brauer-character basis;
* derived API: the existence and uniqueness statements in Exercise `18-18.3-3`, phrased on the
  canonical Brauer and restricted ordinary character owners.

Layer triage:
* source-facing: the three exercise statements comparing simple Brauer characters with restricted
  ordinary characters;
* core/canonical: `PRegularConjClass G p → K`;
* bridge/view: `PrimeToPRoot.toFieldLift`, used only where the source-facing statement genuinely
  starts from a multiplicative lift into `Kˣ`;
  `Representation.exists_residueFieldLift_of_isIrreducible_of_isPSolvable` stays only as a
  proof-route bridge rather than as public ambient data.
-/

/-- Exercise 18-18.3-3 (1): if `φ` is the Brauer character of a simple `k[G]`-module, viewed on
the canonical owner `PRegularConjClass G p` through a chosen injective multiplicative lift of the
prime-to-`p` roots of unity into `Kˣ`, then `φ` is the restriction to the `p`-regular conjugacy
classes of the ordinary character of some simple `K[G]`-module. -/
theorem simple_modularCharacter_exists_restricted_ordinary_character
    (lift : PrimeToPRoot p k →* Kˣ) (S : FDRep k G) (hp : Nat.Prime p) (hG : IsPSolvable p G)
    (hlift : Function.Injective lift) (hS : Simple S) :
    ∃ X : FDRep K G,
      Simple X ∧
        modularCharacterOnPRegularConjClass S (toFieldLift lift) =
          ordinaryCharacterOnPRegularConjClass p X := by
  -- Route correction: the source-faithful proof should apply Fong-Swan to a residue-field /
  -- fraction-field pair and then compare the reduced lattice character with the upstairs
  -- ordinary character on `PRegularConjClass G p`.
  -- TODO: the current target statement only quantifies over the abstract fields `k` and `K`,
  -- while the available Chapter 16/17 lift theorems are phrased through an auxiliary local ring
  -- `A` with residue field `k` and fraction field `K`. Once that bridge is exposed on this owner
  -- surface, the proof is the planned `p`-regular extensionality argument.
  sorry

/-- Helper for Exercise 18-18.3-3: once a complete simple modular family is fixed, a nonnegative
combination of its Brauer characters can equal one basis vector only for the corresponding
singleton coefficient family. -/
lemma modular_basis_singleton_of_eq_sum
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) (n : ι →₀ ℕ)
    (h :
      modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) =
        n.sum fun j m ↦
          (m : K) • modularCharacterOnPRegularConjClass (E j) (toFieldLift lift)) :
    n = Finsupp.single i 1 := by
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) lift hlift E hE_pairwise hE_complete
  ext j
  -- Read the given equality in Brauer-basis coordinates.
  have hrepr := congrArg (fun z : PRegularConjClass G p → K ↦ b.repr z j) h
  -- Characteristic zero reflects the coordinate equality back from `K` to `ℕ`.
  apply Nat.cast_injective (R := K)
  simpa [b, Finsupp.single_apply] using hrepr

-- Proof sketch: once part `(1)` identifies the Brauer character of `S` with one restricted
-- ordinary character, expand that ordinary character in the complete simple family `F` and apply
-- `irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions` to the simple modular
-- characters to conclude that any nonnegative integral expansion of that class function in the
-- family must be a single basis vector.
/-- Exercise 18-18.3-3 (2): if the Brauer character of a simple `k[G]`-module is viewed through a
chosen injective multiplicative lift of the prime-to-`p` roots of unity into `Kˣ`, then every
nonnegative integral expansion of that class function in the restricted ordinary characters
attached to `F` is a single summand. -/
theorem simple_modularCharacter_unique_nonnegative_expansion
    (lift : PrimeToPRoot p k →* Kˣ) (F : ι → FDRep K G) (S : FDRep k G)
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (hlift : Function.Injective lift)
    (hF_pairwise : PairwiseNonisomorphic F)
    (hF_complete : IsCompleteIrreducibleFamily F) (hS : Simple S)
    (n : ι →₀ ℕ)
    (hn :
      modularCharacterOnPRegularConjClass S (toFieldLift lift) =
        n.sum fun i m ↦ (m : K) • ordinaryCharacterOnPRegularConjClass p (F i)) :
    ∃ i, n = Finsupp.single i 1 := by
  -- The intended source route is: first realize the left-hand Brauer character as one restricted
  -- ordinary character by part `(1)`, then expand each `ordinaryCharacterOnPRegularConjClass p
  -- (F i)` as a nonnegative sum of Brauer basis vectors, and finally apply
  -- `modular_basis_singleton_of_eq_sum`.
  -- TODO: the remaining dependency-closed blocker is the nonnegative-column bridge for a simple
  -- ordinary module: each `ordinaryCharacterOnPRegularConjClass p (F i)` must be rewritten as a
  -- finite `ℕ`-combination of the Brauer basis coming from a complete simple modular family.
  sorry

-- Proof sketch: express the restricted ordinary character of the simple ordinary module `X` as a
-- nonnegative integral combination of the Brauer-character basis attached to `E`. For
-- `p`-solvable `G`, part `(1)` lifts each basis vector to a simple ordinary character and part
-- `(2)` forces any such nonnegative integral expansion of the restricted character of a simple
-- module to be a single summand.
/-- Exercise 18-18.3-3 (3): if `E` is a complete pairwise nonisomorphic family of simple
`k[G]`-modules and the restricted ordinary character of a simple `K[G]`-module `X` is a
nonnegative integral combination of the Brauer characters of the family `E`, then that restricted
ordinary character is itself one family Brauer character. -/
theorem simple_restricted_ordinary_character_eq_modularCharacter
    (lift : PrimeToPRoot p k →* Kˣ) (E : ι → FDRep k G) (X : FDRep K G)
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (hlift : Function.Injective lift)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) (hX : Simple X)
    (n : ι →₀ ℕ)
    (hn :
      ordinaryCharacterOnPRegularConjClass p X =
        n.sum fun i m ↦
          (m : K) • modularCharacterOnPRegularConjClass (E i) (toFieldLift lift)) :
    ∃ i,
      ordinaryCharacterOnPRegularConjClass p X =
        modularCharacterOnPRegularConjClass (E i) (toFieldLift lift) := by
  -- Once part `(2)` is available on the ordinary side, this converse direction should rewrite the
  -- right-hand Brauer-character expansion through the lifted ordinary simples supplied by part
  -- `(1)` and then collapse the coefficients to a singleton.
  -- TODO: this is blocked by the same nonnegative-column lemma as part `(2)`, together with the
  -- missing Fong-Swan bridge in part `(1)`.
  sorry

end

end Representation
