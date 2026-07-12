import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped SubgroupInduction

universe u v

namespace Representation

open Exercise_12_12_2_6

section ComplexConclusion

variable {G : Type u} [Group G] [Finite G]

/-- Helper for Exercise 12-12.2-6: precomposing a virtual character with a multiplicative
equivalence preserves character-ring membership. This earlier local owner lets the Shrink bridge
reuse the transport before the later identical general helper is declared. -/
theorem mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
    {K' : Type*} [Field K']
    {G₀ : Type*} [Group G₀] [Finite G₀]
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* G₀) {χ : G₀ → K'} (hχ : χ ∈ R[K'](G₀)) :
    (fun h : H ↦ χ (e h)) ∈ R[K'](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional K' ρ := hρfd
    let τρ : Representation K' H ρ := ρ.ρ.comp e.toMonoidHom
    have hτρ :
        τρ.character = fun h : H ↦ ρ.ρ.character (e h) := by
      ext h
      rfl
    exact hτρ ▸
      rep_character_mem_characterRingOverField_universe_local
        (K' := K') (H := H) (ρ := τρ)
  · intro n
    exact (R[K'](H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R[K'](H)).mul_mem hf hg

/-- Helper for Exercise 12-12.2-6: the one-dimensional representation attached to a unit-valued
character sends the identity to the identity endomorphism. -/
theorem oneDimensionalRepresentation_map_one_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) :
    LinearMap.lsmul K K ((β 1 : Kˣ) : K) = 1 := by
  ext
  simp [LinearMap.lsmul_apply]

/-- Helper for Exercise 12-12.2-6: the one-dimensional representation attached to a unit-valued
character is multiplicative. -/
theorem oneDimensionalRepresentation_map_mul_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) (x y : H) :
    LinearMap.lsmul K K ((β (x * y) : Kˣ) : K) =
      LinearMap.lsmul K K ((β x : Kˣ) : K) *
        LinearMap.lsmul K K ((β y : Kˣ) : K) := by
  ext
  simp [LinearMap.lsmul_apply, mul_comm]

/-- Helper for Exercise 12-12.2-6: a unit-valued character defines a one-dimensional
representation over the source field. -/
def oneDimensionalRepresentation_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) : Representation K H K where
  toFun h := LinearMap.lsmul K K ((β h : Kˣ) : K)
  map_one' := oneDimensionalRepresentation_map_one_shrink_local (K := K) β
  map_mul' x y := oneDimensionalRepresentation_map_mul_shrink_local (K := K) β x y

/-- Helper for Exercise 12-12.2-6: the character of the attached one-dimensional representation
recovers the original scalar-valued homomorphism. -/
theorem oneDimensionalRepresentation_character_apply_shrink_local
    {K : Type*} [Field K]
    {H : Type*} [Group H]
    (β : H →* Kˣ) (h : H) :
    (oneDimensionalRepresentation_shrink_local (K := K) β).character h = ((β h : Kˣ) : K) := by
  rw [Representation.character]
  let b := Module.Free.chooseBasis K K
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmat :
      LinearMap.toMatrix b b (oneDimensionalRepresentation_shrink_local (K := K) β h) =
        Matrix.diagonal fun _ ↦ ((β h : Kˣ) : K) := by
    convert (Algebra.toMatrix_lsmul (b := b) (((β h : Kˣ) : K))) using 1
  rw [hmat]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K K) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex K K]
    rw [Module.finrank_self]
  simp [Matrix.trace, hcard]

/-- Helper for Exercise 12-12.2-6: values of a linear character have order dividing the group
exponent, so they land in the corresponding roots-of-unity subgroup. -/
theorem linearCharacter_mem_rootsOfUnity_shrink_local
    {G' : Type*} [Group G'] [Finite G']
    (H : Subgroup G') (α : H →* ℂˣ) (h : H) :
    α h ∈ rootsOfUnity (Monoid.exponent G') ℂ := by
  let m := Monoid.exponent G'
  have hh : h ^ m = 1 := by
    apply H.subtype_injective
    simpa [m] using Monoid.pow_exponent_eq_one (h : G')
  rw [mem_rootsOfUnity]
  simpa [← map_pow] using congrArg α hh

/-- Helper for Exercise 12-12.2-6: if the source field contains the required roots of unity, then
every induced linear character already lies in the coefficient-extension character ring. -/
theorem induced_linear_character_mem_extension_of_hasEnoughRoots_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ]
    {G' : Type*} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')]
    (H : Subgroup G') (α : H →* ℂˣ) :
    Ind[H](α.toRepresentation.character) ∈ characterRingOverFieldInExtension K ℂ G' := by
  letI : Fintype H := Fintype.ofFinite H
  let m := Monoid.exponent G'
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hprim : (primitiveRoots m K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos m)]
    exact hζ
  let e : rootsOfUnity m K ≃* rootsOfUnity m ℂ :=
    rootsOfUnityEquivOfPrimitiveRoots (f := algebraMap K ℂ) (algebraMap K ℂ).injective hprim
  let αRoots : H →* rootsOfUnity m ℂ :=
    MonoidHom.codRestrict α (rootsOfUnity m ℂ)
      (fun h ↦ linearCharacter_mem_rootsOfUnity_shrink_local H α h)
  let βRoots : H →* rootsOfUnity m K := e.symm.toMonoidHom.comp αRoots
  let β : H →* Kˣ := (rootsOfUnity m K).subtype.comp βRoots
  let χK : R[K](H) :=
    ⟨(oneDimensionalRepresentation_shrink_local (K := K) β).character,
      rep_character_mem_characterRingOverField_universe_local
        (K' := K) (H := H) (ρ := oneDimensionalRepresentation_shrink_local (K := K) β)⟩
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨Ind[H]((χK : H → K)), Subgroup.inducedClassFunction_mem_characterRingOverField H χK, ?_⟩
  ext g
  simp [Subgroup.inducedClassFunction]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsg : s⁻¹ * g * s ∈ H
  · simp [hsg, χK, oneDimensionalRepresentation_character_apply_shrink_local]
    simpa [β, βRoots, αRoots, e, hsg, MonoidHom.toRepresentation_character_apply] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap K ℂ) (n := m) (algebraMap K ℂ).injective hprim
        (αRoots ⟨s⁻¹ * g * s, hsg⟩)
  · simp [hsg]

/-- Helper for Exercise 12-12.2-6: enough roots of unity identify the coefficient-extension image
of `R_K(G')` with the ordinary complex character ring. -/
theorem characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K]
    {G' : Type u} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')] :
    R[ℂ](G') ≤ characterRingOverFieldInExtension K ℂ G' := by
  intro χ hχ
  let Gs := Shrink.{0} G'
  let e : Gs ≃* G' := Shrink.mulEquiv
  let χH : Gs → ℂ := fun h ↦ χ (e h)
  have hχH : χH ∈ R[ℂ](Gs) := by
    simpa [Gs, e, χH] using
      mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
        (K' := ℂ) (G₀ := G') (H := Gs) e hχ
  let χHR : R[ℂ](Gs) := ⟨χH, hχH⟩
  have hmono : χHR ∈ monomialCharacterSpan Gs := by
    exact Representation.character_mem_monomialCharacterSpan χHR
  have hχ_ext :
      (χHR : Gs → ℂ) ∈ (characterRingOverFieldInExtension K ℂ Gs).toSubmodule := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmono
    · intro η hη
      rcases hη with ⟨L, α, hηeq⟩
      simpa [← hηeq] using
        induced_linear_character_mem_extension_of_hasEnoughRoots_shrink_local
          (K := K) (G' := Gs) L α
    · simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.zero_mem
    · intro η ξ _ _ hη hξ
      simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.add_mem hη hξ
    · intro n η _ hη
      simpa using (characterRingOverFieldInExtension K ℂ Gs).toSubmodule.smul_mem n hη
  have hχH_ext : χH ∈ characterRingOverFieldInExtension K ℂ Gs := by
    simpa [χHR] using hχ_ext
  rcases Subalgebra.mem_map.mp hχH_ext with ⟨χK, hχK, hχK_map⟩
  let χKG : G' → K := fun g ↦ χK (e.symm g)
  have hχKG : χKG ∈ R[K](G') := by
    simpa [Gs, e, χKG] using
      mem_characterRingOverField_of_precomp_mulEquiv_shrink_local
        (K' := K) (G₀ := Gs) (H := G') e.symm hχK
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨χKG, hχKG, ?_⟩
  ext g
  simpa [Gs, e, χKG, χH] using congrFun hχK_map (e.symm g)

/-- Helper for Exercise 12-12.2-6: enough roots of unity identify the coefficient-extension image
of `R_K(G')` with the ordinary complex character ring. -/
theorem characterRing_extension_eq_characterRing_of_hasEnoughRoots_shrink_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K]
    {G' : Type u} [Group G'] [Finite G']
    [HasEnoughRootsOfUnity K (Monoid.exponent G')] :
    characterRingOverFieldInExtension K ℂ G' = R[ℂ](G') := by
  apply le_antisymm
  · intro χ hχ
    rcases Subalgebra.mem_map.mp hχ with ⟨χK, hχK, rfl⟩
    simpa using
      map_mem_characterRingOverField_local
        (G := G') (f := (IsScalarTower.toAlgHom ℤ K ℂ)) χK hχK
  · intro χ hχ
    exact
      characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity_shrink_local
        (K := K) (G' := G') hχ

/-- Helper for Exercise 12-12.2-6: in the only case needed later, an algebraically closed source
field has enough roots of unity to realize every complex virtual character over `R_K(G)`. -/
theorem characterRingOverFieldInExtension_eq_characterRing_of_algClosed_toComplex_local
    {K : Type*} [Field K] [CharZero K] [Algebra K ℂ] [IsAlgClosed K] :
    characterRingOverFieldInExtension K ℂ G = R[ℂ](G) := by
  simpa using
    (characterRing_extension_eq_characterRing_of_hasEnoughRoots_shrink_local
      (K := K) (G' := G))

/-- Helper for Exercise 12-12.2-6: dividing a realizing equality for `m • χ_ρ` yields the
mapped scaled realizing character itself. -/
theorem scaled_realizing_character_maps_to_complex_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    let K := characterField ρ.ρ.character
    let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
    (fun g ↦ algebraMap K ℂ (χ g)) = ρ.ρ.character := by
  let _ : Finite G := inferInstance
  let K := characterField ρ.ρ.character
  let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
  ext g
  have hm_ne : (((m : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hpoint := congrFun hτchar g
  calc
    algebraMap K ℂ (χ g) = (((m : ℕ) : ℂ)⁻¹) * algebraMap K ℂ (τ.ρ.character g) := by
      simp [χ, map_mul]
    _ = (((m : ℕ) : ℂ)⁻¹) * (((m : ℕ) : ℂ) * ρ.ρ.character g) := by
      rw [hpoint]
      simp [smul_eq_mul]
    _ = ρ.ρ.character g := by
      field_simp [hm_ne]

/-- Helper for Exercise 12-12.2-6: dividing a realizing equality for `m • χ_ρ` yields the
canonical source-side overline witness for the realizing model. -/
theorem schur_realization_scaled_character_mem_overline_local
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (τ : Rep (characterField ρ.ρ.character) G)
    [FiniteDimensional (characterField ρ.ρ.character) τ]
    (m : ℕ+)
    (hτchar :
      (fun g ↦ algebraMap (characterField ρ.ρ.character) ℂ (τ.ρ.character g)) =
        (((m : ℕ) : ℂ) • ρ.ρ.character)) :
    ((((m : ℕ) : characterField ρ.ρ.character)⁻¹) • τ.ρ.character) ∈
      R̄[characterField ρ.ρ.character](G) := by
  let K := characterField ρ.ρ.character
  let χ : G → K := (((m : ℕ) : K)⁻¹) • τ.ρ.character
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift (R := K)
  letI : Algebra (AlgebraicClosure K) ℂ := ι.toAlgebra
  let ιZ : AlgebraicClosure K →ₐ[ℤ] ℂ := ι.restrictScalars ℤ
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hρ_mem : ρ.ρ.character ∈ R[ℂ](G) := by
    simpa using
      rep_character_mem_characterRingOverField_universe_local
        (K' := ℂ) (H := G) (ρ := ρ.ρ)
  have hχ_complex :
      (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) =
        ρ.ρ.character := by
    ext g
    change algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) (χ g)) =
      ρ.ρ.character g
    calc
      algebraMap (AlgebraicClosure K) ℂ (algebraMap K (AlgebraicClosure K) (χ g))
          = algebraMap K ℂ (χ g) := by
              exact AlgHom.commutes ι (χ g)
      _ = ρ.ρ.character g := by
            simpa [K, χ] using
              congrFun
                (scaled_realizing_character_maps_to_complex_local
                  (ρ := ρ) (τ := τ) (m := m) hτchar) g
  have hχ_in_extension :
      (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) ∈
        characterRingOverFieldInExtension (AlgebraicClosure K) ℂ G := by
    rw [characterRingOverFieldInExtension_eq_characterRing_of_algClosed_toComplex_local
      (G := G) (K := AlgebraicClosure K)]
    exact hχ_complex.symm ▸ hρ_mem
  rcases Subalgebra.mem_map.mp hχ_in_extension with ⟨ψ, hψ, hψmap⟩
  have hψ_eq :
      ψ = ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ := by
    ext g
    apply ι.injective
    exact congrFun hψmap g
  exact (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).2 <| by
    simpa [K, χ, hψ_eq] using hψ

end ComplexConclusion

end Representation
