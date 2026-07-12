import Mathlib
import StacksProject_2024.Chap10.Lemma_10_158_7

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
- `core/canonical`: formal smoothness of separable field extensions, together with the canonical
  residue-field map `ResidueField.map`;
- `bridge/view`: lifting across the nilpotent kernel of the residue map and the induced
  `ResidueField A`-algebra structure on `A'` used internally to construct a compatible section.
-/

-- Proof sketch: Proposition `10.158.9` makes the prime-field extension
-- `ZMod p → ResidueField A` formally smooth because `p` is prime. Since `maximalIdeal A` is
-- nilpotent, the residue map `A → ResidueField A` is a nilpotent thickening, so formal smoothness
-- produces a section `ResidueField A → A`.
/-- Lemma 15.116.10: if `A` is a local ring of characteristic `p` with nilpotent maximal ideal,
then the residue map `A → ResidueField A` admits a ring-theoretic section. -/
@[stacks 09EZ]
theorem exists_residueField_section_of_isNilpotent_maximalIdeal
    {p : ℕ} [Fact p.Prime] [CharP A p]
    (h_nil : IsNilpotent (maximalIdeal A)) :
    ∃ σ : κA →+* A, (residue A).comp σ = RingHom.id κA := by
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  letI : Algebra (ZMod p) κA := ((residue A).comp (algebraMap (ZMod p) A)).toAlgebra
  letI : Algebra.FormallySmooth (ZMod p) κA := Algebra.formallySmooth_of_isSeparableOver
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom (ZMod p) A κA) := by
    simpa [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq] using
      (residue_surjective (R := A))
  have hker_nil :
      IsNilpotent (RingHom.ker (IsScalarTower.toAlgHom (ZMod p) A κA : A →+* κA)) := by
    simpa [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq, ker_residue] using h_nil
  let σ : κA →ₐ[ZMod p] A :=
    Algebra.FormallySmooth.liftOfSurjective
      (AlgHom.id (ZMod p) κA) (IsScalarTower.toAlgHom (ZMod p) A κA) hsurj hker_nil
  have hσ_alg :
      (IsScalarTower.toAlgHom (ZMod p) A κA).comp σ = AlgHom.id (ZMod p) κA :=
    Algebra.FormallySmooth.comp_liftOfSurjective
      (AlgHom.id (ZMod p) κA) (IsScalarTower.toAlgHom (ZMod p) A κA) hsurj hker_nil
  have hσ_ring :
      (residue A).comp σ.toRingHom = RingHom.id κA := by
    simpa [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq] using
      congrArg AlgHom.toRingHom hσ_alg
  refine ⟨σ.toRingHom, ?_⟩
  exact hσ_ring

section

variable {A' : Type u} [CommRing A'] [IsLocalRing A']
variable [Algebra A A'] [IsLocalHom (algebraMap A A')]

local notation "κA'" => ResidueField A'

/-- The canonical residue-field extension induced by a local homomorphism `A → A'`. -/
noncomputable instance residueFieldAlgebra : Algebra κA κA' :=
  (ResidueField.map (algebraMap A A')).toAlgebra

section

omit [IsLocalRing A'] [IsLocalHom (algebraMap A A')]

/-- Helper for Lemma 15.116.10: the `κA`-algebra structure on `A'` induced by `σ` has algebra map
`(algebraMap A A').comp σ`. -/
private theorem residueField_target_algebraMap_eq_comp
    (σ : κA →+* A) :
    let _ : Algebra κA A' := ((algebraMap A A').comp σ).toAlgebra
    (algebraMap κA A' : κA →+* A') = (algebraMap A A').comp σ := by
  -- The induced `κA`-algebra on `A'` is defined from this ring homomorphism.
  simp [RingHom.algebraMap_toAlgebra]

end

/-- Helper for Lemma 15.116.10: after choosing a section `σ`, the residue map on `A'` restricts on
`κA` to the canonical comparison map on residue fields. -/
private theorem residueField_target_residue_comp_eq_map
    (σ : κA →+* A)
    (hσ : (residue A).comp σ = RingHom.id κA) :
    (residue A').comp ((algebraMap A A').comp σ) = ResidueField.map (algebraMap A A') := by
  ext x
  calc
    residue A' ((algebraMap A A') (σ x))
        = ResidueField.map (algebraMap A A') ((residue A) (σ x)) := by
            simpa using (ResidueField.map_residue (f := algebraMap A A') (r := σ x)).symm
    _ = ResidueField.map (algebraMap A A') x := by
          have hx : residue A (σ x) = x := DFunLike.congr_fun hσ x
          simpa [hx]

/-- Helper for Lemma 15.116.10: the residue map from `A'` is a `κA`-algebra hom for the
`κA`-algebra structure induced by the chosen section `σ`. -/
private noncomputable def residueField_target_algHom
    (σ : κA →+* A)
    (hσ : (residue A).comp σ = RingHom.id κA) :
    let _ : Algebra κA A' := ((algebraMap A A').comp σ).toAlgebra
    A' →ₐ[κA] κA' :=
  let _ : Algebra κA A' := ((algebraMap A A').comp σ).toAlgebra
  { toRingHom := residue A'
    commutes' := DFunLike.congr_fun
      (residueField_target_residue_comp_eq_map (A := A) (A' := A') σ hσ) }

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
@[stacks 09EZ]
theorem exists_compatible_residueField_section_of_isNilpotent_maximalIdeal
    (h_nil' : IsNilpotent (maximalIdeal A'))
    (σ : κA →+* A)
    (hσ : (residue A).comp σ = RingHom.id κA)
    [Algebra.IsSeparableOver κA κA'] :
    ∃ σ' : κA' →+* A',
      (residue A').comp σ' = RingHom.id κA' ∧
        σ'.comp (ResidueField.map (algebraMap A A')) = (algebraMap A A').comp σ := by
  -- Route correction: keep the canonical `κA`-algebra on `ResidueField A'` from
  -- `ResidueField.map (algebraMap A A')`; only the target ring `A'` gets the theorem-local
  -- algebra structure induced by `σ`.
  let κA'_alg : Algebra κA κA' := inferInstance
  let κA'_sep : Algebra.IsSeparableOver κA κA' := inferInstance
  letI : Algebra κA A' := ((algebraMap A A').comp σ).toAlgebra
  letI : Algebra κA κA' := κA'_alg
  letI : Algebra.IsSeparableOver κA κA' := κA'_sep
  letI : Algebra.FormallySmooth κA κA' := Algebra.formallySmooth_of_isSeparableOver
  have hA'_alg :
      (algebraMap κA A' : κA →+* A') = (algebraMap A A').comp σ := by
    simpa using residueField_target_algebraMap_eq_comp (A := A) (A' := A') σ
  let g : A' →ₐ[κA] κA' := residueField_target_algHom (σ := σ) (hσ := hσ)
  have hsurj : Function.Surjective g := by
    simpa [g, residueField_target_algHom] using (residue_surjective (R := A'))
  have hker_nil : IsNilpotent (RingHom.ker (g : A' →+* κA')) := by
    simpa [g, residueField_target_algHom, ker_residue] using h_nil'
  let τ : κA' →ₐ[κA] A' :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id κA κA') g hsurj hker_nil
  have hτ_alg : g.comp τ = AlgHom.id κA κA' :=
    Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id κA κA') g hsurj hker_nil
  have hτ_ring : (residue A').comp τ.toRingHom = RingHom.id κA' := by
    simpa [g, residueField_target_algHom] using congrArg AlgHom.toRingHom hτ_alg
  refine ⟨τ.toRingHom, ?_, ?_⟩
  · exact hτ_ring
  -- Compatibility is exactly the `κA`-linearity of `τ`, rewritten in ring-hom form.
  ext x
  calc
    τ ((ResidueField.map (algebraMap A A')) x)
        = τ ((algebraMap κA κA') x) := by
            rfl
    _ = (algebraMap κA A') x := τ.commutes x
    _ = ((algebraMap A A').comp σ) x := by
          rw [hA'_alg]

end

end
