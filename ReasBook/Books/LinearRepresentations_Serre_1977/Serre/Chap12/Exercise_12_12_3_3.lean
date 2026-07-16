import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_1_4
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_2_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_3_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_3_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_7
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.ComplexRealizationDescent

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation
open scoped BigOperators
open scoped SubgroupInduction

universe v

namespace Representation

open CategoryTheory

section

variable {G : Type} [Group G] [Finite G]

private local instance : Fintype G := Fintype.ofFinite G

-- The character field `characterField χ = ℚ(χ values)`, the Schur-index predicate
-- `HasSchurIndex χ m`, and its bundled unpacking `hasSchurIndex_iff_packaged_realization_local`
-- are all reused from `Exercise_12_12_2_3.API` / `Exercise_12_12_2_6.ComplexMinimalRealization`;
-- see `Representation.characterField` and `Representation.HasSchurIndex`.

/-- Enough roots of unity identify the complex realization of `R[K](G)` with the ordinary complex
character ring, in the universe-polymorphic form used by the later Chapter 12 arguments. -/
theorem characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity_local
    {K : Type*} [Field K] [Algebra K ℂ]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    characterRingOverFieldInExtension K ℂ G = R(G) :=
  -- Reuse the canonical Theorem 12-12.3-1 over the same base data.
  characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity (K := K) (G := G)

/-- If a characteristic-zero field embeds in `ℂ` and contains enough roots of unity for `G`, then
Serre's intrinsic and ordinary character rings over that field coincide. -/
theorem characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_complexEmbedding
    {K : Type*} [Field K] [Algebra K ℂ]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    R[K](G) = R̄[K](G) := by
  apply le_antisymm
  · exact characterRingOverField_le_overlineCharacterRing (K := K) (G := G)
  · intro χ hχ
    let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift (R := K)
    letI : Algebra (AlgebraicClosure K) ℂ := ι.toRingHom.toAlgebra
    letI : IsScalarTower K (AlgebraicClosure K) ℂ :=
      IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
    let ιZ : AlgebraicClosure K →ₐ[ℤ] ℂ := ι.restrictScalars ℤ
    have hχ_alg :
        ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ ∈
          R[AlgebraicClosure K](G) :=
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).1 hχ
    have hχ_complex_ext :
        (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) ∈
          characterRingOverFieldInExtension (AlgebraicClosure K) ℂ G := by
      exact Subalgebra.mem_map.mpr ⟨_, hχ_alg, rfl⟩
    have hbridge :
        (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) =
          ((IsScalarTower.toAlgHom ℤ K ℂ).compLeft G) χ := by
      -- `ι` is a `K`-algebra map, so applying `ι ∘ (K → AlgClosure)` equals `K → ℂ` termwise.
      funext g
      simp only [AlgHom.compLeft_apply, IsScalarTower.coe_toAlgHom']
      exact ι.commutes (χ g)
    have hχ_complex :
        ((IsScalarTower.toAlgHom ℤ K ℂ).compLeft G) χ ∈ R(G) := by
      rw [← characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity_local
        (K := AlgebraicClosure K) (G := G), ← hbridge]
      exact hχ_complex_ext
    have hχ_descends :
        ((IsScalarTower.toAlgHom ℤ K ℂ).compLeft G) χ ∈
          characterRingOverFieldInExtension K ℂ G := by
      rw [characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity_local
        (K := K) (G := G)]
      exact hχ_complex
    rcases Subalgebra.mem_map.mp hχ_descends with ⟨ψ, hψ, hψmap⟩
    have hψ_eq : ψ = χ := by
      ext g
      exact (algebraMap K ℂ).injective <| congrFun hψmap g
    simpa [hψ_eq] using hψ


/-- Helper for Exercise 12-12.3-3: use of Exercise `12-12.2-7` localized to the current item. -/
private theorem
    scaled_character_denominator_dvd_extensionDegree_of_isQuasisplitGroupAlgebra_local
    {K : Type} [Field K] [CharZero K]
    {L : Type} [Field L] [CharZero L] [Algebra K L] [FiniteDimensional K L]
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G))
    (hL : R[L](G) = R̄[L](G)) :
    (m : ℕ) ∣ Module.finrank K L := by
  -- Repackage the ring-equality quasisplitness as the class hypothesis of Exercise `12-12.2-7`
  -- and invoke its canonical denominator-divisibility theorem.
  have hquasi : IsQuasisplitGroupAlgebra L G :=
    (characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra L G).1 hL
  exact scaled_character_denominator_dvd_extensionDegree_of_isQuasisplitGroupAlgebra
    (K := K) (L := L) (G := G) ρ m hscaled hquasi

/-- Helper for Exercise 12-12.3-3: the cyclotomic intermediate field inside `ℂ` generated by the
`Monoid.exponent G`-th roots of unity. -/
private abbrev exponent_cyclotomic_intermediateField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    {z : ℂ | ∃ k ∈ ({Monoid.exponent G} : Set ℕ), k ≠ 0 ∧ z ^ k = 1}

/-- Helper for Exercise 12-12.3-3: the exponent cyclotomic intermediate field is the expected
singleton cyclotomic extension of `ℚ`. -/
private theorem exponent_cyclotomic_intermediateField_isCyclotomic :
    IsCyclotomicExtension {Monoid.exponent G} ℚ (exponent_cyclotomic_intermediateField (G := G)) := by
  let n := Monoid.exponent G
  letI : NeZero n := Monoid.neZero_exponent_of_finite
  -- Adjoin the primitive exponent root in `ℂ` and invoke the generic cyclotomic-adjoin theorem.
  simpa [exponent_cyclotomic_intermediateField] using
    (IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      ({n} : Set ℕ) ℚ ℂ
      (fun m hm hm0 ↦ by
        rw [Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨Complex.exp (2 * Real.pi * Complex.I / n), Complex.isPrimitiveRoot_exp n hm0⟩))

/-- Helper for Exercise 12-12.3-3: the exponent cyclotomic intermediate field contains enough
roots of unity for `Monoid.exponent G`. -/
private instance exponent_cyclotomic_intermediateField_hasEnoughRootsOfUnity :
    HasEnoughRootsOfUnity (exponent_cyclotomic_intermediateField (G := G)) (Monoid.exponent G) where
  prim := by
    -- Extract a primitive exponent root from the cyclotomic-extension structure.
    letI :
        IsCyclotomicExtension {Monoid.exponent G} ℚ
          (exponent_cyclotomic_intermediateField (G := G)) :=
      exponent_cyclotomic_intermediateField_isCyclotomic (G := G)
    simpa using
      (IsCyclotomicExtension.exists_isPrimitiveRoot
        (S := {Monoid.exponent G}) (A := ℚ)
        (B := exponent_cyclotomic_intermediateField (G := G))
        (n := Monoid.exponent G) (by simp)
        (show Monoid.exponent G ≠ 0 by exact NeZero.ne _))
  cyc := rootsOfUnity.isCyclic _ _

/-- Helper for Exercise 12-12.3-3: the character field of an irreducible complex representation
lies inside the exponent cyclotomic intermediate field. -/
private theorem characterField_le_exponent_cyclotomic_intermediateField
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible] :
    characterField ρ.ρ.character ≤ exponent_cyclotomic_intermediateField (G := G) := by
  let L := exponent_cyclotomic_intermediateField (G := G)
  letI : FiniteDimensional ℂ ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  -- The complex character of `ρ` is an honest virtual character, so by Theorem 12-12.3-1 (enough
  -- roots of unity in `L`) it is the coefficient image of an `L`-valued virtual character; hence
  -- every character value already lies in `L`.  This route is universe-independent of `ρ`.
  have hmem : ρ.ρ.character ∈ R(G) := by
    simpa using Representation.rep_character_mem_characterRing (ρ := ρ)
  rw [← characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity_local
    (K := L) (G := G)] at hmem
  rcases Subalgebra.mem_map.mp hmem with ⟨χL, _hχL, hχLmap⟩
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨g, rfl⟩
  -- `ρ.ρ.character g = algebraMap L ℂ (χL g) = ↑(χL g) ∈ L`.
  have hpoint : ρ.ρ.character g = algebraMap L ℂ (χL g) := (congrFun hχLmap g).symm
  rw [hpoint]
  exact (χL g).2

/-- Helper for Exercise 12-12.3-3: the exponent cyclotomic intermediate field gives a quasisplit
group algebra because it contains the exponent roots of unity. -/
private theorem isQuasisplitGroupAlgebra_exponent_cyclotomic_intermediateField :
    R[exponent_cyclotomic_intermediateField (G := G)](G) =
      R̄[exponent_cyclotomic_intermediateField (G := G)](G) :=
  -- The exponent cyclotomic field embeds in `ℂ` and contains enough roots of unity, so the
  -- generic complex-embedding criterion applies directly.
  characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_complexEmbedding
    (K := exponent_cyclotomic_intermediateField (G := G)) (G := G)

-- Source/core/bridge triage: this theorem is `source-facing`. Its primitive datum is the Chapter
-- 12 owner `HasSchurIndex` on the complex character of an irreducible representation. The
-- finite-dimensionality needed to form the character is derived upstream from `Finite G` and
-- `ρ.ρ.IsIrreducible`, so it does not remain primitive public data. The denominator/divisibility
-- route is already owned upstream by Exercise `12-12.2-7`, while the new local helpers only
-- package the cyclotomic intermediate field needed to apply that bridge in a dependency-closed
-- way.
-- Proof sketch: let `K` be the character field of `ρ.ρ.character`, and let `L` be the exponent
-- cyclotomic intermediate field inside `ℂ`. The Schur-index witness gives a `K`-representation
-- `τ` realizing `m • ρ.ρ.character`; divide that identity by `m` and descend it to
-- `R̄[K](G)`. The field `L` contains the character field and enough roots of unity, so `L[G]` is
-- quasisplit and Exercise `12-12.2-7` gives `m ∣ [L : K]`. Finally `[L : K]` divides
-- `[L : ℚ] = φ(exp G)` by the tower law and the cyclotomic degree formula.
/-- Exercise 12-12.3-3: every Schur index of an irreducible complex representation of `G`
divides the Euler function of the exponent `Monoid.exponent G`. -/
theorem schur_index_dvd_totient_exponent
    (ρ : Rep.{v} ℂ G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hm : HasSchurIndex ρ.ρ.character m) :
    (m : ℕ) ∣ Nat.totient (Monoid.exponent G) := by
  let K := characterField ρ.ρ.character
  let L := exponent_cyclotomic_intermediateField (G := G)
  -- Unpack the canonical Schur-index witness into a bundled realizing `Rep` and minimality data.
  rcases (hasSchurIndex_iff_packaged_realization_local (χ := ρ.ρ.character) (m := m)).1 hm with
    ⟨⟨τ, hτfd, hτchar⟩, hmin⟩
  let _ : FiniteDimensional K τ := hτfd
  have hτirr :
      τ.ρ.IsIrreducible :=
    minimal_realization_is_irreducible_local
      (ρ := ρ) (τ := τ) (m := m) hτchar hmin
  letI : τ.ρ.IsIrreducible := hτirr
  have hscaled :
      ((((m : ℕ) : K)⁻¹) • τ.ρ.character) ∈ R̄[K](G) :=
    schur_realization_scaled_character_mem_overline_local
      (ρ := ρ) (τ := τ) (m := m) hτchar
  have hKL : K ≤ L :=
    characterField_le_exponent_cyclotomic_intermediateField (ρ := ρ)
  -- Realize `L` as a finite field extension of the character field `K` inside `ℂ`.
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  letI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq fun x =>
      ((IntermediateField.inclusion hKL).commutes x).symm
  letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ L :=
    exponent_cyclotomic_intermediateField_isCyclotomic (G := G)
  letI : FiniteDimensional ℚ L :=
    IsCyclotomicExtension.finiteDimensional (S := {Monoid.exponent G}) (K := ℚ) (C := L)
  letI : FiniteDimensional K L := Module.Finite.right ℚ K L
  have hdivKL : (m : ℕ) ∣ Module.finrank K L :=
    scaled_character_denominator_dvd_extensionDegree_of_isQuasisplitGroupAlgebra_local
      (K := K) (L := L) (ρ := τ) (m := m) hscaled
      isQuasisplitGroupAlgebra_exponent_cyclotomic_intermediateField
  have hdivQL : Module.finrank K L ∣ Module.finrank ℚ L := by
    -- The tower law shows `[L : K]` divides `[L : ℚ]`.
    refine ⟨Module.finrank ℚ K, ?_⟩
    rw [mul_comm, Module.finrank_mul_finrank ℚ K L]
  have htot :
      Module.finrank ℚ L = Nat.totient (Monoid.exponent G) :=
    IsCyclotomicExtension.Rat.finrank (Monoid.exponent G) L
  -- Compose the denominator divisibility with the tower law and the cyclotomic degree formula.
  simpa [htot] using dvd_trans hdivKL hdivQL

end

end Representation
