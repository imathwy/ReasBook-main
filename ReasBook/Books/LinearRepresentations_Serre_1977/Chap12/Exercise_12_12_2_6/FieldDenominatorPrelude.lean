import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation

universe u v w

namespace Representation

open CategoryTheory
open scoped DirectSum

namespace Exercise_12_12_2_6

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_field : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: conjugating a representation by a linear equivalence preserves
the identity element of the representation law. -/
theorem conjRepresentation_map_one_local
    {V : Type*} {W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

/-- Helper for Exercise 12-12.2-6: conjugating a representation by a linear equivalence preserves
the multiplication law. -/
theorem conjRepresentation_map_mul_local
    {V : Type*} {W : Type u} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (ρ : Representation K G V) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-6: move a finite-dimensional `K`-representation to the ambient
carrier universe through a chosen finite basis. -/
def finBasisRepresentation_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) : Representation K G (Fin (Module.finrank K V) → K) :=
  let e := (Module.finBasis K V).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conjRepresentation_map_one_local (K := K) (G := G) e ρ
    map_mul' := fun g h ↦ conjRepresentation_map_mul_local (K := K) (G := G) e ρ g h }

/-- Helper for Exercise 12-12.2-6: transporting a representation through a finite basis does not
change its character. -/
theorem character_finBasisRepresentation_eq_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) :
    (finBasisRepresentation_local (K := K) (G := G) ρ).character g = ρ.character g := by
  simpa [finBasisRepresentation_local, Representation.character] using
    (LinearMap.trace_conj' (ρ g) ((Module.finBasis K V).equivFun))

/-- Helper for Exercise 12-12.2-6: every `FDRep` object is canonically isomorphic to the object
rebuilt from its underlying unbundled representation. -/
noncomputable def fdRepIsoOfRho_local (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Exercise 12-12.2-6: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
noncomputable def intertwiningMapCongrLeft_local
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V₁} {σ : Representation K G V₂}
    (e : ρ.Equiv σ) (τ : Representation K G W) :
    Representation.IntertwiningMap σ τ ≃ₗ[K] Representation.IntertwiningMap ρ τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-6: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
noncomputable def directSumIntertwiningMapEquivPi_local
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    Representation.IntertwiningMap (Representation.directSum π) τ ≃ₗ[K]
      ∀ i, Representation.IntertwiningMap (π i) τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Exercise 12-12.2-6: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. -/
theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit_local
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_left
      (fun hf ↦ hρ ⟨f.ofBijective hf⟩)

/-- Helper for Exercise 12-12.2-6: any finite-dimensional `K`-representation contributes an
honest character-ring element, independently of the carrier universe. -/
theorem rep_character_mem_characterRingOverField_universe_local
    {K' : Type v} [Field K']
    {H : Type u} [Group H] [Finite H]
    {V : Type w} [AddCommGroup V] [Module K' V] [FiniteDimensional K' V]
    (ρ : Representation K' H V) :
    ρ.character ∈ R[K'](H) := by
  let e := (Module.finBasis K' V).equivFun
  let ρfin : Representation K' H (Fin (Module.finrank K' V) → K') :=
    { toFun := fun h ↦ e.conj (ρ h)
      map_one' := by
        -- Conjugation carries the identity operator to the identity operator.
        calc
          e.conj (ρ 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id e
      map_mul' := by
        intro g h
        -- Conjugation transports the representation law without changing traces.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let τρ : Representation K' H (ULift.{max u v} (Fin (Module.finrank K' V) → K')) :=
    { toFun := fun h ↦
        { toFun := fun x ↦ ⟨ρfin h x.down⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  let τ : Rep K' H := Rep.of τρ
  have hfin : ρ.character = ρfin.character := by
    -- Conjugation preserves trace, so the coordinate-model character matches the original one.
    ext h
    symm
    simpa [τ, ρfin, Representation.character] using
      (LinearMap.trace_conj' (ρ h) e)
  have hulift : τ.ρ.character = ρfin.character := by
    -- `ULift` does not change trace values.
    ext h
    change
      LinearMap.trace K' (ULift.{max u v} (Fin (Module.finrank K' V) → K'))
          ((ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
            ULift.{max u v} (Fin (Module.finrank K' V) → K')).conj (ρfin h)) =
        LinearMap.trace K' (Fin (Module.finrank K' V) → K') (ρfin h)
    simpa [τ, τρ] using
      (LinearMap.trace_conj' (ρfin h)
        (ULift.moduleEquiv.symm : (Fin (Module.finrank K' V) → K') ≃ₗ[K']
          ULift.{max u v} (Fin (Module.finrank K' V) → K')))
  have hchar : ρ.character = τ.ρ.character := by
    exact hfin.trans hulift.symm
  exact hchar ▸ Representation.rep_character_mem_characterRingOverField (K := K') (G := H) τ

/-- Helper for Exercise 12-12.2-6: scalar extension transports a character by applying the
coefficient map to each value. -/
private theorem scalarExtension_character_eq_map_local
    {F : Type*} [Field F]
    {E : Type*} [Field E] [Algebra F E]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F G V) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap F E (τ.character g) := by
  -- Trace commutes with base change, so scalar extension only changes coefficients.
  ext g
  exact LinearMap.trace_baseChange (τ g) E

/-- Helper for Exercise 12-12.2-6: coefficientwise extension of a virtual character stays inside
the target character ring. -/
theorem map_mem_characterRingOverField_local
    {F : Type*} [Field F]
    {E : Type*} [Field E] [CharZero E]
    (f : F →ₐ[ℤ] E)
    (χ : G → F)
    (hχ : χ ∈ R[F](G)) :
    (f.compLeft G) χ ∈ R[E](G) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  -- Route correction: first check honest characters by scalar extension, then push that statement
  -- through the algebra-adjoin presentation of `R[F](G)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    let ρE : Rep E G := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (f.compLeft G) ρ.ρ.character = ρE.ρ.character := by
      -- Scalar extension changes only the coefficients of the character values.
      ext g
      simpa [ρE] using
        (congrFun
          (scalarExtension_character_eq_map_local
            (G := G) (τ := ρ.ρ)) g).symm
    exact hchar.symm ▸
      rep_character_mem_characterRingOverField_universe_local
        (ρ := Representation.scalarExtension ρ.ρ)
  · intro n
    change (fun _ : G ↦ f (algebraMap ℤ F n)) ∈ R[E](G)
    have hconst : (fun _ : G ↦ f (algebraMap ℤ F n)) = algebraMap ℤ (G → E) n := by
      ext g
      simpa using (f.commutes n)
    rw [hconst]
    exact (R[E](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is closed under addition.
    simpa using (R[E](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    -- The target character ring is also closed under pointwise multiplication.
    simpa using (R[E](G)).mul_mem hφ hψ

/-- Helper for Exercise 12-12.2-6: the value at `1` of an element of `R_K(G)` is an integer. -/
theorem value_at_one_eq_int_of_mem_characterRingOverField
    (χ : G → K)
    (hχ : χ ∈ R[K](G)) :
    ∃ z : ℤ, χ 1 = (z : K) := by
  refine
    Algebra.adjoin_induction
      (p := fun φ _ ↦ ∃ z : ℤ, φ 1 = (z : K)) ?_ ?_ ?_ ?_ hχ
  · intro φ hφ
    rcases hφ with ⟨ρ, hρfd, _hρirr, rfl⟩
    refine ⟨Module.finrank K ρ, ?_⟩
    letI : FiniteDimensional K ρ := hρfd
    simpa using (Representation.char_one (K := K) (G := G) ρ.ρ)
  · intro z
    exact ⟨z, by simp⟩
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨a, ha⟩
    rcases hψ with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    simp [ha, hb]
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨a, ha⟩
    rcases hψ with ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp [ha, hb, Int.cast_mul]

/-- Helper for Exercise 12-12.2-6: the value at `1` of an element of `\overline{R}_K(G)` is an
integer. -/
theorem value_at_one_eq_int_of_mem_overlineCharacterRing
    (χ : G → K)
    (hχ : χ ∈ R̄[K](G)) :
    ∃ z : ℤ, χ 1 = (z : K) := by
  obtain ⟨z, hz⟩ :=
    value_at_one_eq_int_of_mem_characterRingOverField
      (K := AlgebraicClosure K) (G := G)
      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ)
      ((mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).1 hχ)
  refine ⟨z, ?_⟩
  exact (algebraMap K (AlgebraicClosure K)).injective <| by
    simpa using hz

/-- Helper for Exercise 12-12.2-6: a source-side overline witness transports to any algebraically
closed extension by coefficientwise base change. -/
theorem mem_overlineCharacterRingInExtension_of_mem_overlineCharacterRing_local
    {L : Type*} [Field L] [CharZero L] [Algebra K L] [IsAlgClosed L]
    (χ : G → K)
    (hχ : χ ∈ R̄[K](G)) :
    χ ∈ overlineCharacterRingInExtension K L := by
  let ι : AlgebraicClosure K →ₐ[K] L := IsAlgClosed.lift (R := K)
  let ιZ : AlgebraicClosure K →ₐ[ℤ] L := ι.restrictScalars ℤ
  letI : Algebra (AlgebraicClosure K) L := ι.toRingHom.toAlgebra
  have hχ_closure :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ ∈
        R[AlgebraicClosure K](G) := by
    -- Unpack the source-facing `\overline{R}_K(G)` hypothesis as an algebraic-closure witness.
    simpa using
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) χ).1 hχ
  have hχ_lifted :
      (ιZ.compLeft G)
          (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) ∈
        R[L](G) :=
    map_mem_characterRingOverField_local
      (F := AlgebraicClosure K) (E := L) (f := ιZ)
      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) χ) hχ_closure
  exact (mem_overlineCharacterRingInExtension_iff K L χ).2 <| by
    -- The lifted algebraic-closure witness is exactly the coefficientwise image of `χ` in `L`.
    convert hχ_lifted using 1
    ext g
    simpa [ιZ] using (ι.commutes (χ g))

/-- Helper for Exercise 12-12.2-6: every admissible denominator for an irreducible character
divides the degree of the representation. -/
theorem scaled_character_denominator_dvd_finrank
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : (((m : ℕ) : K)⁻¹) • ρ.ρ.character ∈ R̄[K](G)) :
    (m : ℕ) ∣ Module.finrank K ρ := by
  obtain ⟨z, hz⟩ :=
    value_at_one_eq_int_of_mem_overlineCharacterRing
      (K := K) (G := G) ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) hscaled
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hscaled_one :
      (((m : ℕ) : K)⁻¹) * (Module.finrank K ρ : K) = (z : K) := by
    letI : FiniteDimensional K ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
    simpa [Representation.char_one, smul_eq_mul] using hz
  have hmulK : ((m : ℕ) : K) * (z : K) = (Module.finrank K ρ : K) := by
    calc
      ((m : ℕ) : K) * (z : K)
          = ((m : ℕ) : K) * ((((m : ℕ) : K)⁻¹) * (Module.finrank K ρ : K)) := by
              rw [hscaled_one]
      _ = (Module.finrank K ρ : K) := by
            field_simp [hmK_ne]
  have hdivZ : ((m : ℤ) : ℤ) ∣ (Module.finrank K ρ : ℤ) := by
    refine ⟨z, ?_⟩
    exact_mod_cast hmulK.symm
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

/-- Helper for Exercise 12-12.2-6: every simple finite-dimensional `K`-representation admits a
maximal Schur denominator. -/
theorem exists_schur_denominator_of_simple_local
    (V : FDRep K G) [Simple V] :
    ∃ m : ℕ+, FDRep.IsSchurDenominator V m := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ hn : 0 < n, FDRep.schurScaledCharacter V ⟨n, hn⟩ ∈ R̄[K](G)
  have hP_one : P 1 := by
    refine ⟨zero_lt_one, ?_⟩
    simpa [FDRep.schurScaledCharacter] using
      characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K V)
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      simp
    exact CategoryTheory.id_nonzero V hzero
  have hdim_pos : 0 < Module.finrank K V := by
    simpa using (Module.finrank_pos_iff.mpr hV_nontriv)
  have hbounded :
      ∀ n : ℕ+, FDRep.schurScaledCharacter V n ∈ R̄[K](G) → (n : ℕ) ≤ Module.finrank K V := by
    intro n hn
    letI : (Rep.of V.ρ).ρ.IsIrreducible := by
      simpa using (FDRep.isIrreducible_of_simple V)
    have hdiv : (n : ℕ) ∣ Module.finrank K V := by
      simpa [FDRep.schurScaledCharacter] using
        scaled_character_denominator_dvd_finrank
          (K := K) (G := G) (ρ := Rep.of V.ρ) (m := n) hn
    exact Nat.le_of_dvd hdim_pos hdiv
  let mNat := Nat.findGreatest P (Module.finrank K V)
  have hm_prop : P mNat := by
    exact Nat.findGreatest_spec (Nat.succ_le_of_lt hdim_pos) hP_one
  rcases hm_prop with ⟨hm_pos, hm_mem⟩
  refine ⟨⟨mNat, hm_pos⟩, ?_, ?_⟩
  · simpa using hm_mem
  · intro n hn
    have hPn : P (n : ℕ) := ⟨n.2, by simpa using hn⟩
    exact Nat.le_findGreatest (hbounded n hn) hPn

/-- Helper for Exercise 12-12.2-6: Schur denominators are invariant under `FDRep` isomorphism. -/
theorem isSchurDenominator_of_iso_local
    {V W : FDRep K G} (e : V ≅ W) {m : ℕ+}
    (hm : FDRep.IsSchurDenominator V m) :
    FDRep.IsSchurDenominator W m := by
  refine ⟨?_, ?_⟩
  · simpa [FDRep.schurScaledCharacter, FDRep.char_iso e] using hm.1
  · intro n hn
    have hn' : FDRep.schurScaledCharacter V n ∈ R̄[K](G) := by
      simpa [FDRep.schurScaledCharacter, FDRep.char_iso e] using hn
    exact hm.2 n hn'

end FieldPart

end Exercise_12_12_2_6

end Representation
