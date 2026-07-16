import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_7_5

/-!
# The generator-field character as a `Γ_K`-twist orbit sum

For Serre §12.7 (Lemma 15), this records the keystone identity connecting the algebraic-closure
Fourier picture to Serre's generator-field characters: the image under `algebraMap K Ω` of the
generator-field character `χ_β` equals the sum, over the `Γ_K`-twist orbit of `β`, of the linear
characters `β'`.  Proved by transporting the orbit/embedding correspondence
(`gammaSubgroup_generator_value_mem_K_aroots_local` forward,
`gammaSubgroup_exists_twist_of_generator_root_local` backward) through the field-embedding sum
formula `generatorField_model_character_eq_sum_embeddings_on_generator_powers`.
-/

open Representation
open scoped Pointwise Representation BigOperators

noncomputable section

universe u v w

namespace Representation

section OrbitSum

variable {G : Type u} [Group G] [Finite G]
variable {L : Type v} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L) (x : G)

@[reducible] private def instFintypeOrbitSumGroup : Fintype G := Fintype.ofFinite G
attribute [local instance] instFintypeOrbitSumGroup
attribute [local instance] Classical.propDecidable

local notation "ΓK" => Γ[K](G)
local notation "C" => Subgroup.zpowers x

@[reducible] private def instFDOrbitSumCarrier
    (β : C →* (AlgebraicClosure K)ˣ) :
    FiniteDimensional K (generatorFieldCarrier (K := K) (x := x) β) :=
  IntermediateField.adjoin.finiteDimensional
    ((generatorField_generator_isAlgebraic (K := K) (x := x) β).isIntegral)
attribute [local instance] instFDOrbitSumCarrier

@[reducible] private def instFintypeOrbitSumEmbeddings
    (β : C →* (AlgebraicClosure K)ˣ) :
    Fintype (generatorFieldCarrier (K := K) (x := x) β →ₐ[K] AlgebraicClosure K) :=
  minpoly.AlgHom.fintype K (generatorFieldCarrier (K := K) (x := x) β) (AlgebraicClosure K)
attribute [local instance] instFintypeOrbitSumEmbeddings

/-- A linear character of the cyclic group `C = ⟨x⟩` is determined by its value on the
distinguished generator (it suffices to compare the underlying field values). -/
private theorem linearCharacter_eq_of_generator_value_eq_local
    (β₁ β₂ : C →* (AlgebraicClosure K)ˣ)
    (hgen : (((β₁ (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) =
        (((β₂ (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K))) :
    β₁ = β₂ := by
  have hgenU : β₁ (zpowers_generator (x := x)) = β₂ (zpowers_generator (x := x)) :=
    Units.ext hgen
  ext c
  rcases Subgroup.mem_zpowers_iff.mp c.2 with ⟨n, hn⟩
  have hc : c = (zpowers_generator (x := x)) ^ n := by
    apply Subtype.ext
    simpa using hn.symm
  rw [hc, map_zpow, map_zpow, hgenU]

/-- An embedding of the simple field `K(β(x))` is determined by its value on the distinguished
generator value `β(x)`. -/
private theorem embedding_eq_of_generator_value_eq_local
    (β : C →* (AlgebraicClosure K)ˣ)
    (σ₁ σ₂ : generatorFieldCarrier (K := K) (x := x) β →ₐ[K] AlgebraicClosure K)
    (h : σ₁ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ :
          generatorFieldCarrier (K := K) (x := x) β) =
        σ₂ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ :
          generatorFieldCarrier (K := K) (x := x) β)) :
    σ₁ = σ₂ := by
  apply PowerBasis.algHom_ext
    (IntermediateField.adjoin.powerBasis
      (generatorField_generator_isAlgebraic (K := K) (x := x) β).isIntegral)
  rw [IntermediateField.adjoin.powerBasis_gen]
  exact h

/-- Every member of the twist orbit takes, on the generator, a root of the `K`-minimal polynomial
of `β(x)`. -/
private theorem twistOrbit_generator_value_mem_aroots_local
    (β : C →* (AlgebraicClosure K)ˣ)
    {β' : C →* (AlgebraicClosure K)ˣ}
    (hβ' : β' ∈ Finset.image
      (fun t : ΓK => linearCharacter_twist (G := G) (K := K) (x := x) β t) Finset.univ) :
    (((β' (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∈
      (minpoly K
        (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K))).aroots (AlgebraicClosure K) := by
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hβ'
  rw [← ht]
  exact gammaSubgroup_generator_value_mem_K_aroots_local (K := K) (x := x) β t

/-- **Keystone (S5).** The image under `algebraMap K Ω` of the generator-field character of `β`,
at a power of the generator, equals the sum over the `Γ_K`-twist orbit of `β` of the linear
character values at that power. -/
theorem generatorField_character_eq_sum_twistOrbit_on_generator_powers
    (β : C →* (AlgebraicClosure K)ˣ) (n : ℤ) :
    ∑ β' ∈ Finset.image
        (fun t : ΓK => linearCharacter_twist (G := G) (K := K) (x := x) β t) Finset.univ,
        (((β' ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K)
        ((generatorField_linearCharacter_representation (K := K) (x := x) β).character
          ((zpowers_generator (x := x)) ^ n)) := by
  rw [generatorField_model_character_eq_sum_embeddings_on_generator_powers (K := K) (x := x) β n]
  refine Finset.sum_bij
    (fun β' hβ' => generatorField_algHom_of_generator_root (K := K) (x := x) β
      (twistOrbit_generator_value_mem_aroots_local (K := K) (x := x) β hβ'))
    (fun β' hβ' => Finset.mem_univ _)
    ?_ ?_ ?_
  · -- injectivity
    intro β'₁ hβ'₁ β'₂ hβ'₂ hEq
    apply linearCharacter_eq_of_generator_value_eq_local (K := K) (x := x)
    have h1 := generatorField_algHom_of_generator_root_apply_generator (K := K) (x := x) β
      (twistOrbit_generator_value_mem_aroots_local (K := K) (x := x) β hβ'₁)
    have h2 := generatorField_algHom_of_generator_root_apply_generator (K := K) (x := x) β
      (twistOrbit_generator_value_mem_aroots_local (K := K) (x := x) β hβ'₂)
    rw [← h1, ← h2]
    exact congrArg
      (fun σ : generatorFieldCarrier (K := K) (x := x) β →ₐ[K] AlgebraicClosure K =>
        σ (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ : generatorFieldCarrier (K := K) (x := x) β)) hEq
  · -- surjectivity
    intro σ _
    have hint : IsIntegral K (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K)) :=
      (generatorField_generator_isAlgebraic (K := K) (x := x) β).isIntegral
    set cgen : generatorFieldCarrier (K := K) (x := x) β :=
      ⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
        linear_character_value_mem_generatorField (K := K) (x := x) β
          (zpowers_generator (x := x))⟩ with hcgen
    have hroot : σ cgen ∈
        (minpoly K
          (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K))).aroots (AlgebraicClosure K) := by
      rw [Polynomial.mem_aroots]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      have hmp : minpoly K (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)) = minpoly K cgen := by
        have hco : (algebraMap (generatorFieldCarrier (K := K) (x := x) β)
            (AlgebraicClosure K)) cgen =
            (((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K)) := rfl
        rw [← hco]
        exact minpoly.algebraMap_eq
          (FaithfulSMul.algebraMap_injective
            (generatorFieldCarrier (K := K) (x := x) β) (AlgebraicClosure K)) cgen
      rw [hmp, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨t, ht⟩ :=
      gammaSubgroup_exists_twist_of_generator_root_local (K := K) (x := x) β hroot
    refine ⟨linearCharacter_twist (G := G) (K := K) (x := x) β t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    apply embedding_eq_of_generator_value_eq_local (K := K) (x := x) β
    rw [generatorField_algHom_of_generator_root_apply_generator (K := K) (x := x) β]
    exact ht
  · -- value match
    intro β' hβ'
    have hgenpow :
        (⟨(((β ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            ((zpowers_generator (x := x)) ^ n)⟩ :
          generatorFieldCarrier (K := K) (x := x) β) =
        (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ :
          generatorFieldCarrier (K := K) (x := x) β) ^ n := by
      apply Subtype.ext
      show (((β ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
          AlgebraicClosure K)) =
        ↑((⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K)),
            linear_character_value_mem_generatorField (K := K) (x := x) β
              (zpowers_generator (x := x))⟩ :
            generatorFieldCarrier (K := K) (x := x) β) ^ n)
      rw [map_zpow, Units.val_zpow_eq_zpow_val]
      exact (map_zpow₀ (algebraMap (generatorFieldCarrier (K := K) (x := x) β)
        (AlgebraicClosure K))
        (⟨(((β (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
          linear_character_value_mem_generatorField (K := K) (x := x) β
            (zpowers_generator (x := x))⟩ : generatorFieldCarrier (K := K) (x := x) β) n).symm
    have hrhs :
        (generatorField_algHom_of_generator_root (K := K) (x := x) β
          (twistOrbit_generator_value_mem_aroots_local (K := K) (x := x) β hβ'))
            (⟨(((β ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
                AlgebraicClosure K)),
              linear_character_value_mem_generatorField (K := K) (x := x) β
                ((zpowers_generator (x := x)) ^ n)⟩ :
              generatorFieldCarrier (K := K) (x := x) β) =
          (((β' (zpowers_generator (x := x)) : (AlgebraicClosure K)ˣ) :
            AlgebraicClosure K)) ^ n := by
      rw [hgenpow, map_zpow₀, generatorField_algHom_of_generator_root_apply_generator
        (K := K) (x := x) β]
    show (((β' ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K)) =
      (generatorField_algHom_of_generator_root (K := K) (x := x) β
        (twistOrbit_generator_value_mem_aroots_local (K := K) (x := x) β hβ'))
          (⟨(((β ((zpowers_generator (x := x)) ^ n) : (AlgebraicClosure K)ˣ) :
              AlgebraicClosure K)),
            linear_character_value_mem_generatorField (K := K) (x := x) β
              ((zpowers_generator (x := x)) ^ n)⟩ :
            generatorFieldCarrier (K := K) (x := x) β)
    rw [hrhs, map_zpow, Units.val_zpow_eq_zpow_val]

end OrbitSum

end Representation
