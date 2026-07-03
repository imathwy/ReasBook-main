import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_2
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.TensorCharacterBridge

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

namespace Representation

open scoped BigOperators Representation SubgroupInduction

section

variable {K : Type v} [Field K] [Algebra K ℂ]
variable {G : Type} [Group G] [Finite G]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

/-- Helper for Theorem 12-12.3-1: any field admitting an algebra map into `ℂ` has characteristic
zero. -/
private instance charZeroFieldOfAlgebraComplex : CharZero K :=
  (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance

local instance fintypeGroup : Fintype G := Fintype.ofFinite G
local instance fintypeSubgroup (H : Subgroup G) : Fintype H := Fintype.ofFinite H

omit [Finite G] [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Theorem 12-12.3-1: scalar extension carries a `K`-character to the coefficientwise
complex image of that character. -/
private theorem scalarExtension_character_eq_map
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    (Representation.scalarExtension ρ).character = fun g ↦ algebraMap K ℂ (ρ.character g) := by
  -- The trace of the base-changed endomorphism is the image of the original trace.
  ext g
  exact LinearMap.trace_baseChange (ρ g) ℂ

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Theorem 12-12.3-1: the complex realization of `R[K](G)` is contained in the
ordinary character ring `R(G)`. -/
private theorem characterRingOverFieldInExtension_le_characterRing :
    characterRingOverFieldInExtension K ℂ G ≤ R(G) := by
  intro χ hχ
  rcases Subalgebra.mem_map.mp hχ with ⟨χK, hχK, rfl⟩
  change (fun g ↦ algebraMap K ℂ (χK g)) ∈ R(G)
  -- Check the inclusion on the irreducible generators of `R[K](G)` and then close under the
  -- algebra operations defining `Algebra.adjoin`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχK
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional K ρ := hρfd
    have hmap :
        (Representation.scalarExtension ρ.ρ).character =
          fun g ↦ algebraMap K ℂ (ρ.ρ.character g) :=
      scalarExtension_character_eq_map ρ.ρ
    have hmem : (Representation.scalarExtension ρ.ρ).character ∈ R(G) := by
      exact Representation.rep_character_mem_characterRing (Rep.of (Representation.scalarExtension ρ.ρ))
    simpa [hmap] using hmem
  · intro n
    let τ : Representation ℂ G ℂ :=
      Representation.trivial ℂ G ℂ
    have hτ : τ.character ∈ R(G) := by
      exact Representation.rep_character_mem_characterRing (Rep.of τ)
    have hscalar :
        (fun g ↦ algebraMap K ℂ ((algebraMap ℤ (G → K) n) g)) = n • τ.character := by
      ext g
      simp [τ, Representation.character, Representation.trivial]
    exact hscalar ▸ (R(G)).toSubmodule.smul_mem n hτ
  · intro f g _ _ hf hg
    simpa [Pi.add_apply, map_add] using (R(G)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa [Pi.mul_apply, map_mul] using (R(G)).mul_mem hf hg

omit [Algebra K ℂ] in
/-- Helper for Theorem 12-12.3-1: a unit-valued homomorphism over `K` defines the corresponding
one-dimensional `K`-representation. -/
private theorem oneDimensionalRepresentation_map_one {H : Type} [Group H]
    (β : H →* Kˣ) :
    LinearMap.lsmul K K ((β 1 : Kˣ) : K) = 1 := by
  -- At the identity element, the action is multiplication by `1`.
  ext
  simp [LinearMap.lsmul_apply]

omit [Algebra K ℂ] in
/-- Helper for Theorem 12-12.3-1: the one-dimensional `K`-representation attached to `β` is
multiplicative. -/
private theorem oneDimensionalRepresentation_map_mul {H : Type} [Group H]
    (β : H →* Kˣ) (x y : H) :
    LinearMap.lsmul K K ((β (x * y) : Kˣ) : K) =
      LinearMap.lsmul K K ((β x : Kˣ) : K) *
        LinearMap.lsmul K K ((β y : Kˣ) : K) := by
  -- Composition of scalar-multiplication maps is scalar multiplication by the product.
  ext
  simp [LinearMap.lsmul_apply, mul_comm]

/-- Helper for Theorem 12-12.3-1: the one-dimensional `K`-representation attached to a
unit-valued character. -/
private def oneDimensionalRepresentation {H : Type} [Group H]
    (β : H →* Kˣ) : Representation K H K where
  toFun h := LinearMap.lsmul K K ((β h : Kˣ) : K)
  map_one' := oneDimensionalRepresentation_map_one (K := K) β
  map_mul' x y := oneDimensionalRepresentation_map_mul (K := K) β x y

omit [Algebra K ℂ] in
/-- Helper for Theorem 12-12.3-1: the character of the one-dimensional `K`-representation
attached to `β` is the underlying scalar-valued homomorphism. -/
private theorem oneDimensionalRepresentation_character_apply {H : Type} [Group H]
    (β : H →* Kˣ) (h : H) :
    (oneDimensionalRepresentation (K := K) β).character h = ((β h : Kˣ) : K) := by
  -- The trace of scalar multiplication on a one-dimensional space is that scalar.
  rw [Representation.character]
  let b := Module.Free.chooseBasis K K
  rw [LinearMap.trace_eq_matrix_trace K b]
  have hmat :
      LinearMap.toMatrix b b (oneDimensionalRepresentation (K := K) β h) =
        Matrix.diagonal fun _ ↦ ((β h : Kˣ) : K) := by
    convert (Algebra.toMatrix_lsmul (b := b) (((β h : Kˣ) : K))) using 1
  rw [hmat]
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex K K) = 1 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex K K]
    rw [Module.finrank_self]
  simp [Matrix.trace, hcard]

/-- Helper for Theorem 12-12.3-1: the induced character of any degree-`1` complex subgroup
character already lies in the complex realization of `R[K](G)`. -/
private theorem induced_linear_character_mem_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity
    (H : Subgroup G) (α : H →* ℂˣ) :
    Ind[H](α.toRepresentation.character) ∈ characterRingOverFieldInExtension K ℂ G := by
  let m := Monoid.exponent G
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  have hprim : (primitiveRoots m K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots (NeZero.pos m)]
    exact hζ
  let e : rootsOfUnity m K ≃* rootsOfUnity m ℂ :=
    rootsOfUnityEquivOfPrimitiveRoots (f := algebraMap K ℂ) (algebraMap K ℂ).injective hprim
  let αRoots : H →* rootsOfUnity m ℂ :=
    MonoidHom.codRestrict α (rootsOfUnity m ℂ) fun h ↦ by
      -- Each value of a linear character has order dividing the exponent of `G`.
      have hhH : h ^ m = 1 := by
        apply H.subtype_injective
        simpa [m] using Monoid.pow_exponent_eq_one (h : G)
      rw [mem_rootsOfUnity]
      simpa [← map_pow] using congrArg α hhH
  let βRoots : H →* rootsOfUnity m K := e.symm.toMonoidHom.comp αRoots
  let β : H →* Kˣ := (rootsOfUnity m K).subtype.comp βRoots
  let χK : R[K](H) :=
    ⟨(oneDimensionalRepresentation (K := K) β).character,
      Representation.rep_character_mem_characterRingOverField (K := K) (G := H)
        (Rep.of (oneDimensionalRepresentation (K := K) β))⟩
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨Ind[H]((χK : H → K)), Subgroup.inducedClassFunction_mem_characterRingOverField H χK, ?_⟩
  -- Compare the induced `K`-character after applying `K → ℂ` with the original induced
  -- degree-`1` complex character term-by-term in the defining sum.
  ext g
  simp [Subgroup.inducedClassFunction]
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * g * s ∈ H
  · simp [hs, χK, oneDimensionalRepresentation_character_apply]
    simpa [β, βRoots, αRoots, e, hs, MonoidHom.toRepresentation_character_apply] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap K ℂ) (n := m) (algebraMap K ℂ).injective hprim
        (αRoots ⟨s⁻¹ * g * s, hs⟩)
  · simp [hs]

omit [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Helper for Theorem 12-12.3-1: induction preserves the complex realization of a subgroup
character that already comes from `R[K](H)`. -/
private theorem induced_mem_characterRingOverFieldInExtension_of_mem
    (H : Subgroup G) {χ : H → ℂ}
    (hχ : χ ∈ characterRingOverFieldInExtension K ℂ H) :
    Ind[H](χ) ∈ characterRingOverFieldInExtension K ℂ G := by
  rcases Subalgebra.mem_map.mp hχ with ⟨χK, hχK, rfl⟩
  refine Subalgebra.mem_map.mpr ?_
  refine ⟨Ind[H](χK), Subgroup.inducedClassFunction_mem_characterRingOverField H ⟨χK, hχK⟩, ?_⟩
  -- Induction is defined by a finite sum, so coefficient extension commutes with it termwise.
  ext g
  simp [Subgroup.inducedClassFunction]
  refine Finset.sum_congr rfl ?_
  intro s hs
  by_cases hsg : s⁻¹ * g * s ∈ H
  · simp [hsg]
  · simp [hsg]

/-- Helper for Theorem 12-12.3-1: Brauer's theorem `R(G) = monomialCharacterSpan G` reduces the
reverse inclusion to checking the monomial generators. -/
private theorem characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity :
    R(G) ≤ characterRingOverFieldInExtension K ℂ G := by
  intro χ hχ
  let χR : R(G) := ⟨χ, hχ⟩
  have hmono : χR ∈ monomialCharacterSpan G :=
    Representation.character_mem_monomialCharacterSpan χR
  -- Route correction: use the imported Chapter `10` Brauer-induction span theorem rather than
  -- searching for an explicit integral decomposition inside this file.
  have hsubmodule :
      (χR : G → ℂ) ∈ (characterRingOverFieldInExtension K ℂ G).toSubmodule := by
    -- Check the claim on monomial generators, then use the target submodule's closure.
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmono
    · intro η hη
      rcases hη with ⟨H, α, hηeq⟩
      simpa [← hηeq] using
        induced_linear_character_mem_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity
          (K := K) (G := G) H α
    · simpa using (characterRingOverFieldInExtension K ℂ G).toSubmodule.zero_mem
    · intro η ξ _ _ hη hξ
      simpa using (characterRingOverFieldInExtension K ℂ G).toSubmodule.add_mem hη hξ
    · intro n η _ hη
      simpa using (characterRingOverFieldInExtension K ℂ G).toSubmodule.smul_mem n hη
  simpa [χR] using hsubmodule

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's equality between the complex character ring and the complex realization
--   of `R[K](G)` under the enough-roots-of-unity hypothesis.
-- * core/canonical owners: `R[K](G)` from Proposition `12-12.1-1` and `R(G)` from Theorem
--   `11-11.2-1`.
-- * bridge/view: `characterRingOverFieldInExtension K ℂ G`, the generic coefficient-extension
--   owner from Proposition `12-12.1-1` specialized to `ℂ`.
-- * primitive data: the two character-ring owners and the coefficient-extension bridge.
-- * derived API: realizability criteria such as Proposition `12-12.1-2`, which are downstream
--   consequences rather than inputs to this theorem.
--
-- Proof sketch: Brauer's induction theorem writes every element of `R(G)` as an integral linear
-- combination of characters induced from degree-`1` characters of subgroups. A linear character of
-- any subgroup takes values among the roots of unity whose orders divide `Monoid.exponent G`, so
-- the `HasEnoughRootsOfUnity` hypothesis realizes those values in `K`. Hence each monomial
-- summand lies in the image of `R_K(G)`, giving `R(G) ≤ R_K(G)`, while the reverse inclusion is
-- tautological after applying the coefficient embedding `K → ℂ`.
/-- Theorem 12-12.3-1: if `K` contains the `m`th roots of unity, with `m = Monoid.exponent G`,
then the image of LinearRepresentations_Serre_1977's representation ring `R[K](G)` in complex-valued class functions equals
the ordinary representation ring `R(G)`. -/
theorem characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity :
    characterRingOverFieldInExtension K ℂ G = R(G) := by
  apply le_antisymm
  · -- Scalar extension of `K`-representations gives the tautological inclusion into `R(G)`.
    exact characterRingOverFieldInExtension_le_characterRing (K := K) (G := G)
  · exact characterRing_le_characterRingOverFieldInExtension_of_hasEnoughRootsOfUnity
      (K := K) (G := G)

end

end Representation
