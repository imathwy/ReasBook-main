import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Serre.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension

noncomputable section

open CategoryTheory
open scoped Representation

universe u

namespace Representation

namespace ProjectiveScalarExtensionSplitInjective

section

variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.1-3: enough roots of unity persist after passing from `K` to the
field extension on which the same coefficients are interpreted. -/
theorem hasEnoughRootsOfUnity_extension_local
    {L : Type u} [Field L] [Algebra K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    HasEnoughRootsOfUnity L (Monoid.exponent G) where
  prim := by
    -- Map a primitive exponent root from `K` into `L` through the injective algebra map.
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent G)
    exact ⟨algebraMap K L ζ, hζ.map_of_injective (algebraMap K L).injective⟩
  cyc := by
    -- Roots of unity in a field form a cyclic group.
    infer_instance

/-- Helper for Corollary 16-16.1-3: if `K` contains the exponent roots of unity, then the order
of `G` remains nonzero in every coefficient field built from `K`. -/
theorem nat_card_ne_zero_of_hasEnoughRoots_local
    {L : Type u} [Field L] [Algebra K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    (Nat.card G : L) ≠ 0 := by
  intro hcard
  by_cases hchar0 : ringChar L = 0
  · letI : CharZero L := (CharP.ringChar_zero_iff_CharZero (R := L)).mp hchar0
    -- In characteristic zero the group order never vanishes under the natural-number cast.
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne' hcard
  · let p := ringChar L
    letI : CharP L p := ringChar.charP (R := L)
    have hp_prime : Nat.Prime p := by
      rcases CharP.char_is_prime_or_zero L p with hp | hp
      · exact hp
      · exact (hchar0 hp).elim
    letI : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd_card : p ∣ Nat.card G := by
      exact (CharP.cast_eq_zero_iff L p (Nat.card G)).1 hcard
    obtain ⟨g, hg_order⟩ := exists_prime_orderOf_dvd_card' (G := G) p hp_dvd_card
    have hp_dvd_exp : p ∣ Monoid.exponent G := by
      refine dvd_trans ?_ (Monoid.order_dvd_exponent g)
      simpa [hg_order]
    letI : HasEnoughRootsOfUnity L (Monoid.exponent G) :=
      hasEnoughRootsOfUnity_extension_local (K := K) (L := L) (G := G)
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Monoid.exponent G)
    rcases hp_dvd_exp with ⟨n, hn⟩
    have hpow_p : (ζ ^ n) ^ p = 1 := by
      calc
        (ζ ^ n) ^ p = ζ ^ (n * p) := by rw [pow_mul]
        _ = ζ ^ Monoid.exponent G := by rw [Nat.mul_comm, hn]
        _ = 1 := hζ.pow_eq_one
    have hsub_zero : (ζ ^ n - 1) ^ p = 0 := by
      calc
        (ζ ^ n - 1) ^ p = (ζ ^ n) ^ p - (1 : L) ^ p := by
          rw [sub_pow_char]
        _ = 0 := by simp [hpow_p]
    have hpow_n : ζ ^ n = 1 := by
      -- A field has no nonzero nilpotents, so the characteristic-`p` collapse forces `ζ ^ n = 1`.
      have hzero_pair : ζ ^ n - 1 = 0 ∧ p ≠ 0 := by
        simpa [pow_eq_zero_iff (Nat.succ_ne_zero _)] using hsub_zero
      exact sub_eq_zero.mp hzero_pair.1
    have h_exp_dvd_n : Monoid.exponent G ∣ n := hζ.dvd_of_pow_eq_one n hpow_n
    have hn_pos : 0 < n := by
      refine Nat.pos_of_ne_zero fun hn0 ↦ ?_
      have h_exp_zero : Monoid.exponent G = 0 := by simpa [hn0] using hn
      exact (NeZero.ne (Monoid.exponent G)) h_exp_zero
    have h_exp_le_n : Monoid.exponent G ≤ n := Nat.le_of_dvd hn_pos h_exp_dvd_n
    have h_exp_pos : 0 < Monoid.exponent G := Nat.pos_of_ne_zero (NeZero.ne (Monoid.exponent G))
    -- But `Monoid.exponent G = p * n` with `p ≥ 2`, so the exponent is strictly larger than `n`.
    have hp_two_le : 2 ≤ p := hp_prime.two_le
    have hn_lt_double : n < 2 * n := by
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using
        (show n < n + n from Nat.lt_add_of_pos_right hn_pos)
    have hdouble_le : 2 * n ≤ p * n := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp_two_le
    have hn_lt_exp : n < Monoid.exponent G := by
      calc
        n < 2 * n := hn_lt_double
        _ ≤ p * n := hdouble_le
        _ = Monoid.exponent G := hn.symm
    exact (not_lt_of_ge h_exp_le_n) hn_lt_exp

/-- Helper for Corollary 16-16.1-3: enough roots of unity imply Maschke's nonvanishing hypothesis
for every coefficient field used in this item. -/
theorem nat_card_neZero_of_hasEnoughRoots_local
    {L : Type u} [Field L] [Algebra K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    NeZero (Nat.card G : L) :=
  ⟨nat_card_ne_zero_of_hasEnoughRoots_local (K := K) (L := L) (G := G)⟩

/-- Helper for Corollary 16-16.1-3: scalar extension of a finite-dimensional representation
changes its character by applying the coefficient map. -/
theorem scalarExtension_character_eq_map_local
    {F : Type u} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (τ : Representation F G V) :
    (Representation.scalarExtension τ).character = fun g ↦ algebraMap F E (τ.character g) := by
  -- Trace commutes with base change, so scalar extension only changes coefficients.
  ext g
  exact LinearMap.trace_baseChange (τ g) E

/-- Helper for Corollary 16-16.1-3: over the algebraic closure, every character value of a
finite-dimensional representation is the sum of exponent roots of unity, hence already lies in
the image of `K`. -/
theorem finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (V : FDRep (AlgebraicClosure K) G) (g : G) :
    ∃ x : K, algebraMap K (AlgebraicClosure K) x = V.character g := by
  classical
  let m := Monoid.exponent G
  let b := Module.Free.chooseBasis (AlgebraicClosure K) V
  let A :
      Matrix (Module.Free.ChooseBasisIndex (AlgebraicClosure K) V)
        (Module.Free.ChooseBasisIndex (AlgebraicClosure K) V) (AlgebraicClosure K) :=
    LinearMap.toMatrix b b (V.ρ g)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K m
  let hprim : (primitiveRoots m K).Nonempty := by
    exact ⟨ζ, by
      rw [mem_primitiveRoots (Monoid.neZero_exponent_of_finite).pos]
      exact hζ⟩
  let e : rootsOfUnity m K ≃* rootsOfUnity m (AlgebraicClosure K) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (f := algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective hprim
  have hroot_preimage :
      ∀ μ ∈ A.charpoly.roots, ∃ x : K, algebraMap K (AlgebraicClosure K) x = μ := by
    intro μ hμ
    have hμ_rep :
        μ ∈ (V.ρ g).charpoly.roots := by
      simpa [A] using hμ
    have hμ_order : μ ^ orderOf g = 1 :=
      Representation.charpoly_root_pow_orderOf_eq_one V.ρ g hμ_rep
    have hμ_exp : μ ^ m = 1 := by
      rcases Monoid.order_dvd_exponent g with ⟨d, hd⟩
      simpa [m, hd, pow_mul, hμ_order]
    let μRoots : rootsOfUnity m (AlgebraicClosure K) := rootsOfUnity.mkOfPowEq μ hμ_exp
    refine ⟨((e.symm μRoots : rootsOfUnity m K) : Kˣ), ?_⟩
    -- The roots-of-unity equivalence identifies every closure root with a unique base-field root.
    simpa [e, μRoots, rootsOfUnity.coe_mkOfPowEq] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap K (AlgebraicClosure K))
        (n := m)
        (algebraMap K (AlgebraicClosure K)).injective
        hprim
        μRoots
  have hsum_preimage :
      ∀ s : Multiset (AlgebraicClosure K),
        (∀ μ ∈ s, ∃ x : K, algebraMap K (AlgebraicClosure K) x = μ) →
        ∃ x : K, algebraMap K (AlgebraicClosure K) x = s.sum := by
    intro s
    refine Multiset.induction_on s ?_ ?_
    · intro _
      exact ⟨0, by simp⟩
    · intro μ s ih hs
      rcases hs μ (by simp) with ⟨xμ, hxμ⟩
      rcases ih (fun ν hν ↦ hs ν (by simp [hν])) with ⟨xs, hxs⟩
      refine ⟨xμ + xs, ?_⟩
      rw [map_add, hxμ, hxs]
      simp
  rcases hsum_preimage A.charpoly.roots hroot_preimage with ⟨x, hx⟩
  -- Rewrite the trace as the sum of characteristic-polynomial roots and transport the resulting
  -- base-field witness back to the character value.
  refine ⟨x, ?_⟩
  calc
    algebraMap K (AlgebraicClosure K) x = A.charpoly.roots.sum := hx
    _ = A.trace := by
          symm
          exact Matrix.trace_eq_sum_roots_charpoly A
    _ = V.character g := by
          symm
          simpa [A, Representation.character] using
            (LinearMap.trace_eq_matrix_trace (AlgebraicClosure K) b (V.ρ g))

/-- Helper for Corollary 16-16.1-3: enough roots of unity force every honest finite-dimensional
character over an algebraic extension of `K` to be `K`-valued. -/
theorem finiteRep_character_isValuedInBaseField_of_hasEnoughRoots_local
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (V : FDRep L G) :
    IsValuedInBaseField K V.character := by
  classical
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift (R := K)
  let ιZ : L →ₐ[ℤ] AlgebraicClosure K := ι.restrictScalars ℤ
  letI : Algebra L (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  let V' : FDRep (AlgebraicClosure K) G := FDRep.of (Representation.scalarExtension V.ρ)
  have hchar_map :
      ∀ g : G,
        algebraMap L (AlgebraicClosure K) (V.character g) = V'.character g := by
    intro g
    -- Scalar extension changes the character only by applying the coefficient embedding.
    simpa [V'] using
      (congrFun
        (scalarExtension_character_eq_map_local
          (G := G) (F := L) (E := AlgebraicClosure K) (τ := V.ρ))
        g).symm
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
  refine ⟨fun g ↦ Classical.choose
      (finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
        (K := K) (G := G) V' g), ?_⟩
  -- Compare the chosen algebraic-closure witness with the original `L`-valued character through
  -- the injective embedding `L → AlgebraicClosure K`.
  ext g
  apply ι.injective
  have hchosen :=
    Classical.choose_spec
      (finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
        (K := K) (G := G) V' g)
  calc
    algebraMap L (AlgebraicClosure K)
        (algebraMap K L
          (Classical.choose
            (finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
              (K := K) (G := G) V' g)))
                = algebraMap K (AlgebraicClosure K)
            (Classical.choose
              (finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
                (K := K) (G := G) V' g)) := by
            simpa using
              (IsScalarTower.algebraMap_apply K L (AlgebraicClosure K)
                (Classical.choose
                  (finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
                    (K := K) (G := G) V' g))).symm
    _ = V'.character g := hchosen
    _ = algebraMap L (AlgebraicClosure K) (V.character g) := (hchar_map g).symm

/-- Helper for Corollary 16-16.1-3: integer-valued constant class functions are automatically
`K`-valued after extending coefficients to any field extension `L / K`. -/
theorem isValuedInBaseField_algebraMap_int_local
    {L : Type u} [Field L] [Algebra K L]
    (n : ℤ) :
    IsValuedInBaseField K (algebraMap ℤ (G → L) n) := by
  -- Rewrite `K`-valuedness as range membership for the coefficientwise algebra map, then choose
  -- the corresponding constant `K`-valued preimage.
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
  refine ⟨algebraMap ℤ (G → K) n, ?_⟩
  ext g
  simp [Pi.algebraMap_apply]

/-- Helper for Corollary 16-16.1-3: the `K`-valued class functions are closed under addition after
passing to any extension field `L / K`. -/
theorem isValuedInBaseField_add_local
    {L : Type u} [Field L] [Algebra K L]
    {φ ψ : G → L}
    (hφ : IsValuedInBaseField K φ)
    (hψ : IsValuedInBaseField K ψ) :
    IsValuedInBaseField K (φ + ψ) := by
  -- Unpack both coefficientwise preimages and add them pointwise over `K`.
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hφ hψ ⊢
  rcases hφ with ⟨φK, rfl⟩
  rcases hψ with ⟨ψK, rfl⟩
  refine ⟨φK + ψK, ?_⟩
  ext g
  simp

/-- Helper for Corollary 16-16.1-3: the `K`-valued class functions are closed under pointwise
multiplication after passing to any extension field `L / K`. -/
theorem isValuedInBaseField_mul_local
    {L : Type u} [Field L] [Algebra K L]
    {φ ψ : G → L}
    (hφ : IsValuedInBaseField K φ)
    (hψ : IsValuedInBaseField K ψ) :
    IsValuedInBaseField K (φ * ψ) := by
  -- Unpack both coefficientwise preimages and multiply them pointwise over `K`.
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hφ hψ ⊢
  rcases hφ with ⟨φK, rfl⟩
  rcases hψ with ⟨ψK, rfl⟩
  refine ⟨φK * ψK, ?_⟩
  ext g
  simp

/-- Helper for Corollary 16-16.1-3: enough roots of unity make the character of a simple
finite-dimensional `K'[G]`-representation `K`-valued. -/
theorem character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_in_algebraic_local
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {χ : G → L}
    (hχ : χ ∈ R[L](G)) :
    IsValuedInBaseField K χ := by
  -- Route correction: isolate the algebraic-extension value-descent once, so the remaining
  -- Chapter `12` blocker is only the image/descent step inside `R[AlgebraicClosure K](G)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional L ρ := hρfd
    -- The generator case is the honest-character descent proved above for arbitrary algebraic
    -- coefficient extensions.
    simpa [FDRep.of] using
      finiteRep_character_isValuedInBaseField_of_hasEnoughRoots_local
        (K := K) (L := L) (G := G) (V := FDRep.of ρ.ρ)
  · intro n
    -- Integer constants come directly from constant `K`-valued functions.
    simpa using isValuedInBaseField_algebraMap_int_local (K := K) (L := L) (G := G) n
  · intro φ ψ _ _ hφ hψ
    -- Addition preserves coefficientwise descent.
    exact isValuedInBaseField_add_local (K := K) hφ hψ
  · intro φ ψ _ _ hφ hψ
    -- Multiplication preserves coefficientwise descent.
    exact isValuedInBaseField_mul_local (K := K) hφ hψ

/-- Helper for Corollary 16-16.1-3: enough roots of unity make the character of a simple
finite-dimensional `K'[G]`-representation `K`-valued. -/
theorem character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_compiled
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {χ : G → K'}
    (hχ : χ ∈ R[K'](G)) :
    IsValuedInBaseField K χ := by
  -- Route correction: now that the theorem-local support owner proves the finite-extension
  -- descent directly, specialize the algebraic-extension owner to the finite extension `K' / K`.
  exact
    character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_in_algebraic_local
      (K := K) (L := K') (G := G) hχ

/-- Helper for Corollary 16-16.1-3: the coefficientwise embedding
`G → K → G → AlgebraicClosure K` is injective on class functions. -/
theorem algClosure_compLeft_injective_local :
    Function.Injective
      (((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) : (G → K) → G →
        AlgebraicClosure K) := by
  intro ψ₁ ψ₂ hψ
  -- Compare the two lifted class functions pointwise and descend along the injective field map.
  ext g
  exact (algebraMap K (AlgebraicClosure K)).injective (congrFun hψ g)

/-- Helper for Corollary 16-16.1-3: the algebraic-closure image of a `K`-valued class function
lies in the mapped owner `overlineCharacterRingOverField K G` exactly when the source function
lies in `R̄[K](G)`. -/
theorem algClosure_image_mem_overlineCharacterRingOverField_iff_local
    (ψ : G → K) :
    ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ψ ∈
        overlineCharacterRingOverField K G ↔
      ψ ∈ R̄[K](G) := by
  constructor
  · intro hψ
    rcases Subalgebra.mem_map.1 hψ with ⟨ψK, hψK, hEq⟩
    -- Route correction: unpack the mapped owner first and only then descend the equality of
    -- algebraic-closure-valued functions through injectivity of the coefficient embedding.
    have hψK_eq : ψK = ψ :=
      algClosure_compLeft_injective_local (K := K) (G := G) hEq
    simpa [hψK_eq] using hψK
  · intro hψ
    -- The source function itself is the required preimage in the mapped owner.
    exact ⟨ψ, hψ, rfl⟩

/-- Helper for Corollary 16-16.1-3: coefficientwise extension of a virtual character remains in
the target character ring. -/
theorem map_mem_characterRingOverField_local
    {F : Type u} [Field F]
    {E : Type u} [Field E]
    (f : F →ₐ[ℤ] E)
    (χ : G → F)
    (hχ : χ ∈ R[F](G)) :
    (f.compLeft G) χ ∈ R[E](G) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  -- First check honest characters by scalar extension, then extend to all virtual characters
  -- through the algebra-adjoin presentation of the character ring.
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
          (scalarExtension_character_eq_map_local (G := G) (F := F) (E := E) (τ := ρ.ρ))
          g).symm
    exact hchar.symm ▸
      Representation.rep_character_mem_characterRingOverField
        (K := E) (G := G) (Rep.of (Representation.scalarExtension ρ.ρ))
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
    -- The target character ring is closed under pointwise multiplication.
    simpa using (R[E](G)).mul_mem hφ hψ
end

end ProjectiveScalarExtensionSplitInjective

end Representation
