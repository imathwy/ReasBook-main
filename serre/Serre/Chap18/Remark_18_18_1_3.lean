import Mathlib
import Serre.Chap18.Proposition_18_18_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u v

namespace Representation

section VirtualModularCharacters

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommGroup A]
variable {G : Type u} [Group G]

/-
Domain-style sampling:
* source-facing: Serre's virtual modular character on `R₀[k](G)`, obtained by additivity from
  modular characters of finite-dimensional `k[G]`-representations.
* core/canonical owners inspected in this domain: `Representation.modularCharacter`,
  `finiteRepGrothendieckRelations`, `finiteRepGrothendieckCharacter`, and `decompositionHom`.
* primitive data: a lift `PrimeToPRoot p k → A`, the generator-level modular character
  `Representation.modularCharacter lift E.ρ`, and the Grothendieck relations
  `finiteRepGrothendieckRelations k G`.
* derived API: the quotient additive map `virtualModularCharacter` and its compatibility with the
  decomposition homomorphism.
* owner-level refinement: this additive Grothendieck descent only depends on the canonical owner
  `Representation.modularCharacter`, so the bridge/view API here does not keep a redundant
  characteristic-`p` assumption; that hypothesis is reserved for the later reduction comparison.
-/

private abbrev virtualModularCharacterLift
    (lift : PrimeToPRoot p k → A) :
    FreeAbelianGroup (FDRep k G) →+ ({ s : G // IsPRegular p s } → A) :=
  FreeAbelianGroup.lift fun E ↦ modularCharacter lift E.ρ

-- Proof sketch: the generators of `finiteRepGrothendieckRelations k G` come from short exact
-- sequences, and Proposition `18-18.1-2 (3)` states that `Representation.modularCharacter` is
-- additive
-- on exactly those sequences.
private theorem finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker
    (lift : PrimeToPRoot p k → A) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterLift lift).ker := by
  -- Descend along the Grothendieck presentation by checking the short-exact-sequence generators.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change virtualModularCharacterLift lift
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext s
  -- Proposition `18-18.1-2 (3)` identifies the middle term with the sum of the outer terms.
  have hchar :
      φ[lift](S.X₂.ρ) s = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s :=
    modularCharacter_add_of_shortExactSequence (p := p) (lift := lift) S hS s
  simpa [virtualModularCharacterLift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    sub_eq_zero.mpr hchar

/-- Remark 18-18.1-3: additivity of the modular character extends it from finite-dimensional
`k[G]`-representations to a virtual modular character on Serre's Grothendieck group `R_k(G)`,
valued on the `p`-regular locus of `G`. -/
def virtualModularCharacter (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ ({ s : G // IsPRegular p s } → A) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterLift lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterLift_ker lift)

-- Proof sketch: `virtualModularCharacter` is the quotient homomorphism induced by
-- `virtualModularCharacterLift`, so on the class of an actual finite representation it recovers
-- `Representation.modularCharacter`.
/-- Evaluating the virtual modular character on the Grothendieck class of a finite-dimensional
representation recovers its modular character. -/
@[simp] theorem virtualModularCharacter_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacter lift [E]₀ = modularCharacter lift E.ρ := by
  simp [virtualModularCharacter, virtualModularCharacterLift, finiteRepGrothendieckClass]

/-- Helper for Remark 18-18.1-3: on the class of an honest representation, the virtual modular
character is unchanged under conjugation of a `p`-regular element. -/
private theorem virtualModularCharacter_class_conj
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) (s t : G)
    (hs : IsPRegular p s) :
    virtualModularCharacter lift [E]₀ ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      virtualModularCharacter lift [E]₀ ⟨s, hs⟩ := by
  -- Reduce to the modular character of the actual representation `E`.
  rw [virtualModularCharacter_class]
  -- Proposition `18-18.1-2 (2)` gives conjugacy invariance on honest representations.
  exact modularCharacter_conj (p := p) (lift := lift) E.ρ s t hs

-- Proof sketch: compare the two evaluations as additive maps on `R₀[k](G)`; on generator
-- classes this is exactly Proposition `18-18.1-2 (2)`, and the Grothendieck quotient extends the
-- identity to all virtual classes.
/-- The virtual modular character is constant on conjugacy classes of `p`-regular elements. -/
theorem virtualModularCharacter_conj
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G)) (s t : G)
    (hs : IsPRegular p s) :
    virtualModularCharacter lift x ⟨t * s * t⁻¹, isPRegular_conj p s t hs⟩ =
      virtualModularCharacter lift x ⟨s, hs⟩ := by
  -- Descend the conjugacy calculation from honest representations to the Grothendieck quotient.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  -- The free abelian presentation reduces the statement to zero, generator, negation, and sum.
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp [virtualModularCharacter]
  · intro E
    exact virtualModularCharacter_class_conj (lift := lift) E s t hs
  · intro a ha
    simpa using congrArg Neg.neg ha
  · intro a b ha hb
    simp [map_add, ha, hb]

-- Route correction: the decomposition-compatibility comparison belongs to a later support layer.
-- This remark stays minimal so `Theorem_18_18_2_2` can import only the owner API it actually uses.

end VirtualModularCharacters

end Representation
