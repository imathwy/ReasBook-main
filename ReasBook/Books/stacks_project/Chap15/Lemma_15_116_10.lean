import Mathlib
import stacks_project.Chap10.Lemma_10_96_4
import stacks_project.Chap15.Lemma_15_38_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

local notation "κA" => ResidueField A

/- Domain-style sampling:
- primary domain: coefficient fields of complete local rings and compatibility of those coefficient
  fields under local ring homomorphisms;
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `isAdicComplete_of_pow_smul_top_eq_bot`,
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`,
  `ResidueField.map`,
  `IsLocalHom`;
- best owner abstraction: the complete-local-ring owner `IsCompleteLocalRing A` together with the
  coefficient-field section theorem
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`, and
  `ResidueField.map (algebraMap A A')` for the canonical residue-field comparison along a local
  homomorphism;
- primitive data: a local ring, nilpotence of its maximal ideal, and in the compatibility clause a
  local hom `A → A'` together with a chosen section `σ : ResidueField A →+* A` of `residue A`;
- derived API: completeness from nilpotence, the induced coefficient-field section, and the
  compatible lift along `ResidueField.map (algebraMap A A')`.

Source/core/bridge triage:
- `source-facing`: the two Lemma `15.116.10` existence statements about residue-field sections;
- `core/canonical`: `IsCompleteLocalRing` and
  `exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver`, together with the
  canonical residue-field map `ResidueField.map`;
- `bridge/view`: the private completeness upgrade from nilpotent maximal ideal, and the induced
  `ResidueField A`-algebra structure on `A'` used internally to construct a compatible section.
-/

private theorem isCompleteLocalRing_of_nilpotent_maximalIdeal
    (h_nil : IsNilpotent (maximalIdeal A)) : IsCompleteLocalRing A := by
  rcases h_nil with ⟨n, hn⟩
  let _ : IsAdicComplete (maximalIdeal A) A := by
    refine isAdicComplete_of_pow_smul_top_eq_bot (maximalIdeal A) n ?_
    simp [hn]
  infer_instance

-- Proof sketch: Proposition `10.158.9` makes the prime-field extension
-- `ZMod p → ResidueField A` formally smooth because `p` is prime. Since `maximalIdeal A` is
-- nilpotent, the residue map `A → ResidueField A` is a nilpotent thickening, so formal smoothness
-- produces a section `ResidueField A → A`.
/-- Lemma 15.116.10: if `A` is a local ring of characteristic `p` with nilpotent maximal ideal,
then the residue map `A → ResidueField A` admits a ring-theoretic section. -/
theorem exists_residueField_section_of_isNilpotent_maximalIdeal
    {p : ℕ} [Fact p.Prime] [CharP A p]
    (h_nil : IsNilpotent (maximalIdeal A)) :
    ∃ σ : κA →+* A, (residue A).comp σ = RingHom.id κA := by
  letI : IsCompleteLocalRing A := isCompleteLocalRing_of_nilpotent_maximalIdeal h_nil
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : Algebra (ZMod p) κA := ((residue A).comp (algebraMap (ZMod p) A)).toAlgebra
  rcases exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver A (ZMod p) with
      ⟨σ, hσ⟩
  exact ⟨σ.toRingHom, hσ⟩

section

variable {A' : Type u} [CommRing A'] [IsLocalRing A']
variable [Algebra A A'] [IsLocalHom (algebraMap A A')]

local notation "κA'" => ResidueField A'

/-- The canonical residue-field extension induced by a local homomorphism `A → A'`. -/
noncomputable instance residueFieldAlgebra : Algebra κA κA' :=
  (ResidueField.map (algebraMap A A')).toAlgebra

-- Proof sketch: derive a complete-local structure on `A'` from the nilpotence of its maximal
-- ideal. The chosen section `σ : ResidueField A → A` and the local map `A → A'` induce a
-- `ResidueField A`-algebra structure on `A'`; because `σ` is a section of `residue A`, the
-- induced residue-field map to `ResidueField A'` is the canonical comparison
-- `ResidueField.map (algebraMap A A')`. Lemma `15.38.3` then gives a section of `residue A'`
-- compatible with the chosen section on `A`.
/-- Lemma 15.116.10 (compatibility clause): let `A → A'` be a local homomorphism of local rings.
Assume the maximal ideal of `A'` is nilpotent, choose a section `σ : ResidueField A →+* A` of
`residue A`, and assume the canonical residue-field extension `ResidueField A' / ResidueField A`
is separable. Then there exists a section `σ' : ResidueField A' →+* A'` of `residue A'`
compatible with `σ` and the local map `A → A'`. -/
theorem exists_compatible_residueField_section_of_isNilpotent_maximalIdeal
    (h_nil' : IsNilpotent (maximalIdeal A'))
    (σ : κA →+* A)
    (hσ : (residue A).comp σ = RingHom.id κA)
    [Algebra.IsSeparableOver κA κA'] :
    ∃ σ' : κA' →+* A',
      (residue A').comp σ' = RingHom.id κA' ∧
        σ'.comp (ResidueField.map (algebraMap A A')) = (algebraMap A A').comp σ := by
  sorry

end

end
