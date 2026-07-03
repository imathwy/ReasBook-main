import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap16.Theorem_16_16_1_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_3.Index

noncomputable section

open CategoryTheory
open scoped Representation

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Corollary 16-16.1-3: enough roots of unity persist after passing from `K` to the
field extension on which the same coefficients are interpreted. -/
private theorem hasEnoughRootsOfUnity_extension_local
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
private theorem nat_card_ne_zero_of_hasEnoughRoots_local
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
private theorem nat_card_neZero_of_hasEnoughRoots_local
    {L : Type u} [Field L] [Algebra K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    NeZero (Nat.card G : L) :=
  ⟨nat_card_ne_zero_of_hasEnoughRoots_local (K := K) (L := L) (G := G)⟩

/-- Helper for Corollary 16-16.1-3: scalar extension of a finite-dimensional representation
changes its character by applying the coefficient map. -/
private theorem scalarExtension_character_eq_map_local
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
private theorem finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_local
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
private theorem finiteRep_character_isValuedInBaseField_of_hasEnoughRoots_local
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
private theorem isValuedInBaseField_algebraMap_int_local
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
private theorem isValuedInBaseField_add_local
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
private theorem isValuedInBaseField_mul_local
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
private theorem character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_in_algebraic_local
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
private theorem character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_compiled
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
private theorem algClosure_compLeft_injective_local :
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
private theorem algClosure_image_mem_overlineCharacterRingOverField_iff_local
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
private theorem map_mem_characterRingOverField_local
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

/-- Helper for Corollary 16-16.1-3: the ordinary character of a finite-dimensional
`F[G]`-representation lies in the character ring `R[F](G)`. -/
private theorem finiteRepCharacter_mem_characterRing_local
    {F : Type u} [Field F]
    (V : FDRep F G) :
    V.character ∈ R[F](G) := by
  -- Repackage the bundled `FDRep` as the Chapter `12` `Rep` owner.
  simpa using Representation.rep_character_mem_characterRingOverField (K := F) (G := G) (Rep.of V.ρ)

/-- Helper for Corollary 16-16.1-3: lift the ordinary character map from genuine
finite-dimensional representations to the free abelian group on their isomorphism classes. -/
private abbrev finiteRepGrothendieckCharacterLift_local
    {F : Type u} [Field F] :
    FreeAbelianGroup (FDRep F G) →+ R[F](G) :=
  FreeAbelianGroup.lift fun V ↦
    ⟨V.character, finiteRepCharacter_mem_characterRing_local (G := G) V⟩

/-- Helper for Corollary 16-16.1-3: the trace of an endomorphism preserving a submodule splits
as the sum of the traces on the submodule and the induced quotient. -/
private theorem trace_eq_trace_restrict_add_trace_mapQ_local
    {F : Type u} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (W : Submodule F V) (hW : W ≤ W.comap f) :
    LinearMap.trace F V f =
      LinearMap.trace F W (f.restrict hW) +
        LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let e : (W × Q) ≃ₗ[F] V := W.prodEquivOfIsCompl Q hQ
  let qEquiv : (V ⧸ W) ≃ₗ[F] Q := W.quotientEquivOfIsCompl Q hQ
  let qBlock : Q →ₗ[F] Q := Q.linearProjOfIsCompl W hQ.symm ∘ₗ f ∘ₗ Q.subtype
  let cross : Q →ₗ[F] W :=
    LinearMap.fst F W Q ∘ₗ (e.symm.conj f) ∘ₗ LinearMap.inr F W Q
  let offdiag : (W × Q) →ₗ[F] (W × Q) :=
    LinearMap.inl F W Q ∘ₗ cross ∘ₗ LinearMap.snd F W Q
  let block : (W × Q) →ₗ[F] (W × Q) := LinearMap.prodMap (f.restrict hW) qBlock
  have hq : ∀ q : Q,
      (Submodule.Quotient.mk ((qBlock q : Q) : V) : V ⧸ W) =
        Submodule.Quotient.mk (f (q : V)) := by
    intro q
    -- The quotient only remembers the `Q`-component modulo the `W`-component.
    rw [Submodule.Quotient.eq']
    have hEq :
        -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q =
          (Submodule.IsCompl.projection hQ) (f q) := by
      rw [Submodule.IsCompl.projection_eq_self_sub_projection hQ]
      abel
    suffices -((Submodule.IsCompl.projection hQ.symm) (f q)) + f q ∈ W by
      simpa [qBlock]
    rw [hEq]
    exact (Submodule.IsCompl.projection_apply_mem hQ) (f q)
  have hqBlock : qBlock = qEquiv.conj (W.mapQ W f hW) := by
    ext q
    -- Transport the quotient map across the chosen complement equivalence.
    exact congrArg (fun x : Q => (x : V)) <| by
      apply qEquiv.symm.injective
      simpa [LinearEquiv.conj_apply_apply] using hq q
  have hleft : ∀ w : W, e.symm.conj f (w, 0) = block (w, 0) := by
    intro w
    have hwmem : f (w : V) ∈ W := hW w.2
    -- On the stable summand `W`, the conjugated map is exactly the restricted action.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, qBlock, hwmem]
  have hright : ∀ q : Q, e.symm.conj f (0, q) = offdiag (0, q) + block (0, q) := by
    intro q
    -- On the complement `Q`, the map splits into the quotient block and the off-diagonal term.
    ext <;> simp [LinearEquiv.symm_conj_apply, e, block, offdiag, cross, qBlock]
  have hsplit : e.symm.conj f = block + offdiag := by
    -- The previous two computations determine the conjugated operator on `W × Q`.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hpair : (w, q) = (w, 0) + (0, q) := by
      ext <;> simp
    have hblock_split : block (w, q) = block (w, 0) + block (0, q) := by
      rw [hpair, map_add]
    have hoffdiag_eq : offdiag (w, q) = offdiag (0, q) := by
      ext <;> simp [offdiag, cross]
    calc
      e.symm.conj f (w, q) = e.symm.conj f (w, 0) + e.symm.conj f (0, q) := by
        rw [hpair, map_add]
      _ = block (w, 0) + (offdiag (0, q) + block (0, q)) := by
        rw [hleft, hright]
      _ = block (w, q) + offdiag (w, q) := by
        rw [hblock_split, hoffdiag_eq]
        abel
      _ = (block + offdiag) (w, q) := rfl
  have hsq : offdiag * offdiag = 0 := by
    -- The off-diagonal operator lands in `W × 0`, so a second application vanishes.
    apply LinearMap.ext
    intro x
    rcases x with ⟨w, q⟩
    have hoff : offdiag (w, q) = (cross q, 0) := by
      ext <;> simp [offdiag, cross]
    rw [show (offdiag * offdiag) (w, q) = offdiag (offdiag (w, q)) by rfl, hoff]
    simp [offdiag]
  have hnil : IsNilpotent offdiag := by
    refine ⟨2, ?_⟩
    simpa [pow_two] using hsq
  have htr_block :
      LinearMap.trace F (W × Q) block =
        LinearMap.trace F W (f.restrict hW) + LinearMap.trace F Q qBlock := by
    simpa [block] using LinearMap.trace_prodMap' (f.restrict hW) qBlock
  have htr_q :
      LinearMap.trace F Q qBlock = LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
    rw [hqBlock]
    simpa using (LinearMap.trace_conj' (W.mapQ W f hW) qEquiv)
  have htr_off : LinearMap.trace F (W × Q) offdiag = 0 := by
    -- A square-zero endomorphism has nilpotent trace, hence zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent (R := F) (M := W × Q) hnil
  -- Conjugation transfers the trace computation back to the original endomorphism.
  calc
    LinearMap.trace F V f = LinearMap.trace F (W × Q) (e.symm.conj f) := by
      simpa [e] using (LinearMap.trace_conj' f e.symm)
    _ = LinearMap.trace F (W × Q) block + LinearMap.trace F (W × Q) offdiag := by
      rw [hsplit, map_add]
    _ = LinearMap.trace F W (f.restrict hW) + LinearMap.trace F Q qBlock := by
      rw [htr_block, htr_off, add_zero]
    _ = LinearMap.trace F W (f.restrict hW) +
          LinearMap.trace F (V ⧸ W) (W.mapQ W f hW) := by
        rw [htr_q]

/-- Helper for Corollary 16-16.1-3: the character of a representation is the sum of the
characters of a stable subrepresentation and its quotient. -/
private theorem character_eq_add_character_quotient_of_invariant_submodule_local
    {F : Type u} [Field F]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (W : Submodule F V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ρ.character = (ρ.subrepresentation W hW).character + (ρ.quotient W hW).character := by
  -- Apply the trace decomposition pointwise to the endomorphisms `ρ g`.
  ext g
  simpa [Representation.character] using
    trace_eq_trace_restrict_add_trace_mapQ_local (f := ρ g) (W := W) (hW := hW g)

/-- Helper for Corollary 16-16.1-3: the character of the middle term of a short exact sequence of
finite-dimensional representations is the sum of the end-term characters. -/
private theorem finiteRepCharacter_eq_add_of_shortExact_local
    {F : Type u} [Field F]
    (S : ShortComplex (FDRep F G)) (hS : S.ShortExact) :
    S.X₂.character = S.X₁.character + S.X₃.character := by
  let Fmod : FDRep F G ⥤ ModuleCat F :=
    (forget₂ (FDRep F G) (Rep F G)) ⋙ (forget₂ (Rep F G) (ModuleCat F))
  have hSF : (S.map Fmod).ShortExact := by
    -- Forgetting to `ModuleCat F` preserves the given short exact sequence.
    simpa [Fmod] using hS.map_of_exact Fmod
  let f : S.X₁.V →ₗ[F] S.X₂.V := ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[F] S.X₃.V := ((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat F`, short exactness is exactness of the underlying linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map Fmod)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is injective after forgetting to modules.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is surjective after the same forgetful step.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule F S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    -- Exactness identifies the image of the left map with the kernel of the right map.
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    -- The image of `f` is stable because `f` intertwines the group actions.
    change
      ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    -- The image equivalence intertwines the source action with the induced subrepresentation.
    change
      ((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[F] S.X₃.V := W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    -- The induced quotient map has trivial kernel because `W = ker g`.
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    -- Surjectivity descends from the original map `g`.
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    -- On quotient classes, the induced action is still defined by the intertwining map `g`.
    change
      ((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep F G) (Rep F G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep F G) (Rep F G)).map S.g) a x
  have hchar₁ :
      S.X₁.character = (Representation.subrepresentation S.X₂.ρ W hW).character := by
    -- Transport the source character across the image equivalence.
    simpa [W, f] using Representation.char_iso e₁
  have hchar₃ :
      S.X₃.character = (Representation.quotient S.X₂.ρ W hW).character := by
    -- Transport the quotient character across the induced quotient equivalence.
    simpa [W, qg] using (Representation.char_iso e₃).symm
  -- Compare the middle character with the sum of the invariant-submodule and quotient characters.
  calc
    S.X₂.character =
        (Representation.subrepresentation S.X₂.ρ W hW).character +
          (Representation.quotient S.X₂.ρ W hW).character := by
            simpa [W] using
              character_eq_add_character_quotient_of_invariant_submodule_local
                (G := G) S.X₂.ρ W hW
    _ = S.X₁.character + S.X₃.character := by
          rw [← hchar₁, ← hchar₃]

/-- Helper for Corollary 16-16.1-3: the ordinary-character lift kills the defining Grothendieck
relations, so it descends to `R₀[F](G)`. -/
private theorem finiteRepGrothendieckRelations_le_characterLift_ker_local
    {F : Type u} [Field F] :
    finiteRepGrothendieckRelations F G ≤
      (finiteRepGrothendieckCharacterLift_local (F := F)).ker := by
  -- It suffices to kill the defining short-exact-sequence generators of `R₀[F](G)`.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change finiteRepGrothendieckCharacterLift_local (F := F)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  ext g
  -- Evaluate the lift on the generator and cancel it using character additivity.
  have hchar :
      S.X₂.character g = S.X₁.character g + S.X₃.character g :=
    congrFun (finiteRepCharacter_eq_add_of_shortExact_local S hS) g
  simpa [finiteRepGrothendieckCharacterLift_local, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using sub_eq_zero.mpr hchar

/-- Helper for Corollary 16-16.1-3: the Grothendieck-group character map sends a virtual
representation class in `R₀[F](G)` to its ordinary character in `R[F](G)`. -/
private noncomputable def finiteRepGrothendieckCharacter_local
    {F : Type u} [Field F] :
    R₀[F](G) →+ R[F](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations F G)
    (finiteRepGrothendieckCharacterLift_local (F := F))
    (finiteRepGrothendieckRelations_le_characterLift_ker_local (F := F))

/-- Helper for Corollary 16-16.1-3: on a genuine finite-dimensional representation class, the
Grothendieck-group character map evaluates to the usual character. -/
@[simp] private theorem finiteRepGrothendieckCharacter_local_class
    {F : Type u} [Field F]
    (V : FDRep F G) (g : G) :
    finiteRepGrothendieckCharacter_local (F := F) [V]₀ g = V.character g := by
  -- The quotient lift is defined so that generator classes evaluate by the ordinary character.
  simp [finiteRepGrothendieckCharacter_local, finiteRepGrothendieckClass,
    finiteRepGrothendieckCharacterLift_local]

/-- Helper for Corollary 16-16.1-3: on a complete simple family, the Grothendieck-character map
matches the simple-class basis of `R₀[F](G)` with the irreducible-character basis of `R[F](G)`. -/
private theorem finiteRepGrothendieckCharacter_basis_image_local
    {F : Type u} [Field F] [CharZero F]
    {ι : Type*}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    ∀ i,
      finiteRepGrothendieckCharacter_local (F := F)
          (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i) =
        irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i := by
  intro i
  -- The simple-class basis vector is `[π i]₀`, and the irreducible-character basis vector is the
  -- ordinary character of the same irreducible representation.
  rw [show
      simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete i = [π i]₀ by
        simp [simple_finiteRep_classes_basis_of_complete_family_apply]]
  rw [show
      irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete i =
        (letI := hπ_complete.isSimple i
         FDRep.irreducibleCharacter F (π i)) by
        simp [irreducible_characters_basis_of_complete_family_apply]]
  -- On a genuine class, `finiteRepGrothendieckCharacter_local` evaluates to the ordinary
  -- character by definition.
  ext g
  simp [finiteRepGrothendieckCharacter_local_class]

/-- Helper for Corollary 16-16.1-3: once Maschke provides a complete simple family, the
Grothendieck-character map admits
an additive section built from the simple-class and irreducible-character bases. -/
private theorem finiteRepGrothendieckCharacter_local_has_inverse
    {F : Type u} [Field F] [CharZero F] [NeZero (Nat.card G : F)] :
    ∃ sF : R[F](G) →+ R₀[F](G),
      (finiteRepGrothendieckCharacter_local (F := F)).comp sF = AddMonoidHom.id _ ∧
        Function.LeftInverse sF (finiteRepGrothendieckCharacter_local (F := F)) := by
  classical
  obtain ⟨ι0, _, π0, hπ0_pairwise, hπ0_complete⟩ :=
    _root_.Representation.exists_complete_pairwise_nonisomorphic_simple_family_local
      (K := F) (G := G)
  let ι : Type u := ULift ι0
  let π : ι → FDRep F G := fun i ↦ π0 i.down
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro i j hij hIso
    have hdown_ne : i.down ≠ j.down := by
      intro hij0
      apply hij
      exact congrArg ULift.up hij0
    simpa [π] using hπ0_pairwise hdown_ne hIso
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := fun i ↦ ?_
        exists_iso := ?_ }
    · simpa [π] using hπ0_complete.isSimple i.down
    · intro S hS
      rcases hπ0_complete.exists_iso S hS with ⟨i, hi⟩
      exact ⟨ULift.up i, by simpa [π] using hi⟩
  let b₀ : Module.Basis ι ℤ (R₀[F](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let bR : Module.Basis ι ℤ (R[F](G)) :=
    irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete
  let fL : R₀[F](G) →ₗ[ℤ] R[F](G) :=
    (finiteRepGrothendieckCharacter_local (F := F)).toIntLinearMap
  let sL : R[F](G) →ₗ[ℤ] R₀[F](G) := bR.constr ℤ b₀
  have hf_basis : ∀ i, fL (b₀ i) = bR i := by
    intro i
    -- On the canonical basis, the Grothendieck-character map sends `[π i]₀` to the matching
    -- irreducible character.
    simpa [b₀, bR, fL] using
      finiteRepGrothendieckCharacter_basis_image_local (G := G) π hπ_pairwise hπ_complete i
  have hs_basis : ∀ i, sL (bR i) = b₀ i := by
    intro i
    -- The basis reconstruction map sends each basis vector straight back to its chosen source.
    simpa [sL] using bR.constr_basis ℤ b₀ i
  have hleftL : sL.comp fL = LinearMap.id := by
    -- Compare the two endomorphisms on the simple basis of `R₀[F](G)`.
    apply b₀.ext
    intro i
    rw [LinearMap.comp_apply, hf_basis i, hs_basis i]
    simp
  have hrightL : fL.comp sL = LinearMap.id := by
    -- The same basis comparison shows that the constructed map also recovers each irreducible
    -- character basis vector in `R[F](G)`.
    apply bR.ext
    intro i
    rw [LinearMap.comp_apply, hs_basis i, hf_basis i]
    simp
  let sF : R[F](G) →+ R₀[F](G) := sL.toAddMonoidHom
  refine ⟨sF, ?_, ?_⟩
  · -- Repackage the linear right-inverse identity as an equality of additive homomorphisms.
    apply AddMonoidHom.ext
    intro x
    have hx :=
      congrArg (fun t : R[F](G) →ₗ[ℤ] R[F](G) => t x) hrightL
    simpa [sF, fL, LinearMap.comp_apply] using hx
  · intro x
    -- Evaluating the linear left-inverse identity at `x` yields the desired left inverse.
    have hx :=
      congrArg (fun t : R₀[F](G) →ₗ[ℤ] R₀[F](G) => t x) hleftL
    simpa [sF, fL, LinearMap.comp_apply] using hx

/-- Helper for Corollary 16-16.1-3: over any field satisfying Maschke's nonvanishing hypothesis,
equality of Grothendieck characters already forces equality of Grothendieck classes. -/
private theorem finiteRepGrothendieckCharacter_eq_iff_general_local
    {F : Type u} [Field F] [CharZero F] [NeZero (Nat.card G : F)]
    {x y : R₀[F](G)} :
    finiteRepGrothendieckCharacter_local (F := F) x =
      finiteRepGrothendieckCharacter_local (F := F) y ↔ x = y := by
  constructor
  · intro hxy
    rcases finiteRepGrothendieckCharacter_local_has_inverse (F := F) (G := G) with
      ⟨sF, _, hsF⟩
    -- The basis-defined section makes the character map injective.
    exact hsF.injective hxy
  · intro hxy
    -- Rewriting by the class equality reduces the character identity to reflexivity.
    simpa [hxy]

/-- Helper for Corollary 16-16.1-3: coefficient extension commutes with the normalized character
pairing. -/
private theorem groupFunctionPairingOverField_algebraMap_local
    {F : Type u} [Field F]
    {E : Type u} [Field E] [Algebra F E]
    {φ ψ : G → F} :
    algebraMap F E (Representation.groupFunctionPairingOverField F φ ψ) =
      Representation.groupFunctionPairingOverField E
        (fun g ↦ algebraMap F E (φ g))
        (fun g ↦ algebraMap F E (ψ g)) := by
  -- Unfold the normalized pairing and push `algebraMap` through the averaging scalar and finite
  -- sum termwise.
  simp [Representation.groupFunctionPairingOverField, map_mul, map_sum]

/-- Helper for Corollary 16-16.1-3: a basiswise retract upgrades to a genuine left inverse once
ordinary scalar extension is known to be injective. -/
private theorem
    finiteRepGrothendieckScalarExtension_leftInverse_of_rightInverse_and_injective_local
    (r : R₀[K'](G) →+ R₀[K](G))
    (hr : (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _)
    (hinj : Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G)) :
    Function.LeftInverse r (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  intro x
  -- Apply the right-inverse identity at `f x` and then reflect back along injectivity.
  apply hinj
  have hr_apply :=
    congrArg (fun f : R₀[K'](G) →+ R₀[K'](G) =>
      f ((finiteRepGrothendieckScalarExtensionHom K K' G) x)) hr
  simpa [AddMonoidHom.comp_apply] using hr_apply

/-- Helper for Corollary 16-16.1-3: every `K'`-valued virtual character descends to some
`K`-valued virtual character once enough roots of unity identify `R[K](G)` with `R̄[K](G)`. -/
private theorem characterRing_mem_of_scalarExtension_mem_of_hasEnoughRoots_local
    {L : Type u} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ψ : G → K}
    (hψ_in_target :
      ((IsScalarTower.toAlgHom ℤ K L).compLeft G) ψ ∈ R[L](G)) :
    ψ ∈ R[K](G) := by
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift (R := K)
  let ιZ : L →ₐ[ℤ] AlgebraicClosure K := ι.restrictScalars ℤ
  letI : Algebra L (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  have hψ_closure :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ψ ∈
        R[AlgebraicClosure K](G) := by
    have hmap :
        (ιZ.compLeft G) (((IsScalarTower.toAlgHom ℤ K L).compLeft G) ψ) ∈
          R[AlgebraicClosure K](G) :=
      map_mem_characterRingOverField_local
        (G := G) (f := ιZ) (((IsScalarTower.toAlgHom ℤ K L).compLeft G) ψ) hψ_in_target
    -- The algebraic-closure lift is exactly the coefficientwise image of `ψ`.
    convert hmap using 1
    ext g
    simpa [ιZ] using (ι.commutes (ψ g))
  have hψ_overline : ψ ∈ R̄[K](G) :=
    (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) ψ).2 hψ_closure
  -- Convert the overline witness into an honest character-ring witness using the pending
  -- enough-roots equality.
  rw [Representation.characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_local
    (K := K) (G := G)]
  exact hψ_overline

/-- Helper for Corollary 16-16.1-3: algebraic-closure character membership descends back to the
honest character ring over `K`. -/
private theorem characterRing_mem_of_algClosure_image_mem_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ψ : G → K}
    (hψ :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ψ ∈
        R[AlgebraicClosure K](G)) :
    ψ ∈ R[K](G) := by
  -- Specialize the scalar-extension descent owner to `K' = AlgebraicClosure K`.
  exact
    characterRing_mem_of_scalarExtension_mem_of_hasEnoughRoots_local
      (K := K) (L := AlgebraicClosure K) (G := G) hψ

/-- Helper for Corollary 16-16.1-3: the remaining Chapter `12` descent owner is the reverse
inclusion `\overline{R}_K(G) ≤ R_K(G)` formulated on a single `K`-valued class function. -/
private theorem overlineCharacterRing_le_characterRing_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    R̄[K](G) ≤ R[K](G) := by
  intro ψ hψ
  have hψ_alg :
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G) ψ ∈
        R[AlgebraicClosure K](G) := by
    -- Unpack the source-facing overline owner into its algebraic-closure character witness.
    simpa [Representation.overlineCharacterRing] using
      (mem_overlineCharacterRingInExtension_iff K (AlgebraicClosure K) ψ).1 hψ
  -- Once the algebraic-closure image is known to be an honest character, the scalar-extension
  -- descent owner upgrades it back to a `K`-character.
  exact
    characterRing_mem_of_algClosure_image_mem_of_hasEnoughRoots_local
      (K := K) (G := G) hψ_alg

/-- Helper for Corollary 16-16.1-3: enough roots of unity identify the honest and overline
character rings over `K` by descending algebraic-closure characters coefficientwise. -/
private theorem characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_compiled
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    R[K](G) = R̄[K](G) := by
  apply le_antisymm
  · -- Honest `K`-characters always define overline characters after extending coefficients.
    exact characterRingOverField_le_overlineCharacterRing K G
  · -- The reverse inclusion is now isolated as the single remaining Chapter `12` owner.
    exact
      overlineCharacterRing_le_characterRing_of_hasEnoughRoots_local
        (K := K) (G := G)

/-- Helper for Corollary 16-16.1-3: every `K'`-valued virtual character descends to some
`K`-valued virtual character once enough roots of unity identify `R[K](G)` with `R̄[K](G)`. -/
private theorem characterRing_preimage_exists_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ' : R[K'](G)) :
    ∃ χ : R[K](G), (fun g ↦ algebraMap K K' (χ g)) = (χ' : G → K') := by
  -- Route correction: first descend `χ'` coefficientwise to a `K`-valued class function, then
  -- push that witness to the algebraic closure and rewrite `R[K](G) = R̄[K](G)`.
  have hχval :
      IsValuedInBaseField K (χ' : G → K') :=
    character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots_compiled
      (K := K) (K' := K') (G := G) χ'.2
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range] at hχval
  rcases hχval with ⟨ψ, hψ_map⟩
  have hψ_eq :
      ((IsScalarTower.toAlgHom ℤ K K').compLeft G) ψ = (χ' : G → K') := by
    ext g
    simpa using congrFun hψ_map g
  have hψ_in_target :
      ((IsScalarTower.toAlgHom ℤ K K').compLeft G) ψ ∈ R[K'](G) := by
    simpa [hψ_eq] using χ'.2
  have hψ_mem : ψ ∈ R[K](G) :=
    characterRing_mem_of_scalarExtension_mem_of_hasEnoughRoots_local
      (K := K) (L := K') (G := G) hψ_in_target
  refine ⟨⟨ψ, hψ_mem⟩, ?_⟩
  -- The descended witness was chosen exactly to recover the original `K'`-valued character.
  exact hψ_eq

/-- Helper for Corollary 16-16.1-3: the coefficientwise descent of a `K'`-character in
`R[K'](G)` is unique because the scalar extension map on class functions is injective. -/
private theorem characterRing_preimage_unique_local
    {χ₁ χ₂ : R[K](G)}
    (hχ : (fun g ↦ algebraMap K K' (χ₁ g)) = (fun g ↦ algebraMap K K' (χ₂ g))) :
    χ₁ = χ₂ := by
  -- Reflect the coefficientwise equality through the injective scalar-extension field map.
  ext g
  exact (algebraMap K K').injective (congrFun hχ g)

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, every `K'`-character in
`R[K'](G)` has a unique coefficientwise preimage in `R[K](G)`. -/
private theorem characterRing_preimage_existsUnique_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ' : R[K'](G)) :
    ∃! χ : R[K](G), (fun g ↦ algebraMap K K' (χ g)) = (χ' : G → K') := by
  rcases
      characterRing_preimage_exists_of_hasEnoughRoots_local
        (K := K) (K' := K') (G := G) χ' with
    ⟨χ, hχ⟩
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  -- The descended `K`-valued preimage is unique by injectivity of the coefficient map.
  exact
    characterRing_preimage_unique_local
      (K := K) (K' := K') (G := G) (χ₁ := ψ) (χ₂ := χ)
      (hψ.trans hχ.symm)

/-- Helper for Corollary 16-16.1-3: coefficientwise extension sends a `K`-character to a
`K'`-character. -/
private theorem characterRing_scalarExtension_mem_local
    (χ : R[K](G)) :
    (fun g ↦ algebraMap K K' (χ g)) ∈ R[K'](G) := by
  -- The coefficientwise map lands in `R[K'](G)` by the already isolated closure lemma.
  exact
    map_mem_characterRingOverField_local
      (G := G) (f := IsScalarTower.toAlgHom ℤ K K') (χ := χ) χ.2

/-- Helper for Corollary 16-16.1-3: the coefficientwise scalar-extension formula defines an
actual element of the target character ring. -/
private def characterRing_scalarExtension_apply_local
    (χ : R[K](G)) :
    R[K'](G) :=
  ⟨fun g ↦ algebraMap K K' (χ g),
    characterRing_scalarExtension_mem_local (K := K) (K' := K') (G := G) χ⟩

/-- Helper for Corollary 16-16.1-3: coefficientwise scalar extension sends `0` to `0`. -/
private theorem characterRing_scalarExtension_apply_zero_local :
    characterRing_scalarExtension_apply_local (K := K) (K' := K') (G := G) 0 = 0 := by
  -- This is pointwise the preservation of zero under `algebraMap K K'`.
  ext g
  simp [characterRing_scalarExtension_apply_local]

/-- Helper for Corollary 16-16.1-3: coefficientwise scalar extension preserves addition. -/
private theorem characterRing_scalarExtension_apply_add_local
    (χ ψ : R[K](G)) :
    characterRing_scalarExtension_apply_local (K := K) (K' := K') (G := G) (χ + ψ) =
      characterRing_scalarExtension_apply_local (K := K) (K' := K') (G := G) χ +
        characterRing_scalarExtension_apply_local (K := K) (K' := K') (G := G) ψ := by
  -- The coefficientwise extension is additive because `algebraMap K K'` is additive.
  ext g
  simp [characterRing_scalarExtension_apply_local]

/-- Helper for Corollary 16-16.1-3: scalar extension on characters is given by coefficientwise
application of `algebraMap K K'`. -/
private def characterRing_scalarExtensionHom_local :
    R[K](G) →+ R[K'](G) :=
  { toFun := characterRing_scalarExtension_apply_local (K := K) (K' := K') (G := G)
    map_zero' := characterRing_scalarExtension_apply_zero_local (K := K) (K' := K') (G := G)
    map_add' := characterRing_scalarExtension_apply_add_local (K := K) (K' := K') (G := G) }

/-- Helper for Corollary 16-16.1-3: coefficientwise scalar extension on the character ring is
injective because the field map `K → K'` is injective. -/
private theorem characterRing_scalarExtension_injective_local :
    Function.Injective (characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G)) := by
  intro χ₁ χ₂ hχ
  have hχ_fun :
      ((characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G) χ₁ : R[K'](G)) :
          G → K') =
        ((characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G) χ₂ : R[K'](G)) :
          G → K') :=
    congrArg (fun χ : R[K'](G) ↦ (χ : G → K')) hχ
  -- Compare the two scalar-extended characters pointwise and reflect through injectivity.
  ext g
  exact
    (algebraMap K K').injective
      (by
        simpa [characterRing_scalarExtensionHom_local, characterRing_scalarExtension_apply_local]
          using congrFun hχ_fun g)

/-- Helper for Corollary 16-16.1-3: the Grothendieck-character map commutes with scalar
extension from `K` to `K'`. -/
private theorem finiteRepGrothendieckCharacter_local_scalarExtension_commutes :
    (characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G)).comp
      (finiteRepGrothendieckCharacter_local (F := K)) =
      (finiteRepGrothendieckCharacter_local (F := K')).comp
        (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  apply AddMonoidHom.ext
  intro x
  -- Reduce the quotient identity to the free abelian group on actual representations.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · ext g
    simp [characterRing_scalarExtensionHom_local, characterRing_scalarExtension_apply_local,
      finiteRepGrothendieckCharacter_local]
  · intro V
    ext g
    -- On a generator class, scalar extension changes only the character coefficients.
    calc
      (characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G)
          (finiteRepGrothendieckCharacter_local (F := K) [V]₀)) g
          = algebraMap K K'
              (finiteRepGrothendieckCharacter_local (F := K) [V]₀ g) := by
                rfl
      _ = algebraMap K K' (V.character g) := by
            rw [finiteRepGrothendieckCharacter_local_class]
      _ = (FDRep.scalarExtension V).character g := by
            simpa using
              (congrFun
                (scalarExtension_character_eq_map_local
                  (G := G) (F := K) (E := K') (τ := V.ρ))
                g).symm
      _ =
          finiteRepGrothendieckCharacter_local (F := K')
            (finiteRepGrothendieckScalarExtensionHom K K' G [V]₀) g := by
              rw [finiteRepGrothendieckScalarExtensionHom_class_eq,
                finiteRepGrothendieckCharacter_local_class]
  · intro a ha
    ext g
    -- Negation is handled additively on both Grothendieck-group owners.
    simpa [map_neg, ha]
  · intro a₁ a₂ ha₁ ha₂
    ext g
    -- Additivity on both sides propagates the generator identity through the free abelian group.
    simpa [map_add, ha₁, ha₂]

/-- Helper for Corollary 16-16.1-3: the coefficientwise scalar-extension map on characters admits
a descent section under enough roots of unity. -/
private theorem characterRing_descent_rightInverse_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ d : R[K'](G) →+ R[K](G),
      Function.RightInverse d (characterRing_scalarExtensionHom_local
        (K := K) (K' := K') (G := G)) := by
  classical
  let dFun : R[K'](G) → R[K](G) := fun χ' ↦
    Classical.choose
      (characterRing_preimage_existsUnique_of_hasEnoughRoots_local
        (K := K) (K' := K') (G := G) χ')
  have hd_spec :
      ∀ χ' : R[K'](G),
        (fun g ↦ algebraMap K K' (dFun χ' g)) = (χ' : G → K') := by
    intro χ'
    exact
      (Classical.choose_spec
        (characterRing_preimage_existsUnique_of_hasEnoughRoots_local
          (K := K) (K' := K') (G := G) χ')).1
  have hd_zero : dFun 0 = 0 := by
    -- The unique descended preimage of the zero character is the zero character.
    refine
      characterRing_preimage_unique_local
        (K := K) (K' := K') (G := G) (χ₁ := dFun 0) (χ₂ := 0) ?_
    refine (hd_spec 0).trans ?_
    ext g
    simp
  have hd_add : ∀ χ₁ χ₂, dFun (χ₁ + χ₂) = dFun χ₁ + dFun χ₂ := by
    intro χ₁ χ₂
    -- Uniqueness of descended preimages forces additivity once the coefficientwise images agree.
    refine
      characterRing_preimage_unique_local
        (K := K) (K' := K') (G := G)
        (χ₁ := dFun (χ₁ + χ₂)) (χ₂ := dFun χ₁ + dFun χ₂) ?_
    refine (hd_spec (χ₁ + χ₂)).trans ?_
    ext g
    have hχ₁ := congrFun (hd_spec χ₁) g
    have hχ₂ := congrFun (hd_spec χ₂) g
    simp [hχ₁, hχ₂]
  let d : R[K'](G) →+ R[K](G) :=
    { toFun := dFun
      map_zero' := hd_zero
      map_add' := hd_add }
  refine ⟨d, ?_⟩
  intro χ'
  -- The chosen preimage is a genuine right inverse by construction.
  ext g
  simpa [d, characterRing_scalarExtensionHom_local, characterRing_scalarExtension_apply_local] using
    congrFun (hd_spec χ') g

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, coefficientwise scalar extension
on the character ring comes with the retract data needed to transport sections back to `R₀`. -/
private theorem characterRing_scalarExtension_retract_data_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ d : R[K'](G) →+ R[K](G),
      (characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G)).comp d =
          AddMonoidHom.id _ ∧
        Function.Injective (characterRing_scalarExtensionHom_local (K := K) (K' := K') (G := G)) :=
    by
  rcases
      characterRing_descent_rightInverse_local
        (K := K) (K' := K') (G := G) with
    ⟨d, hd⟩
  refine ⟨d, ?_, characterRing_scalarExtension_injective_local (K := K) (K' := K') (G := G)⟩
  -- Package the pointwise right-inverse identity as an equality of additive homomorphisms.
  apply AddMonoidHom.ext
  intro χ'
  exact hd χ'

/-- Helper for Corollary 16-16.1-3: once a complete simple family over `K` stays complete and
pairwise nonisomorphic after scalar extension to `K'`, the induced map on `R₀` is a basis
transport isomorphism. -/
private theorem finiteRepGrothendieckScalarExtension_retract_data_of_complete_simple_family_local
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (hπ'_pairwise :
      PairwiseNonisomorphic (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))))
    (hπ'_complete :
      IsCompleteIrreducibleFamily (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G)))) :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  classical
  let b : Module.Basis ι ℤ (R₀[K](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let b' : Module.Basis ι ℤ (R₀[K'](G)) :=
    simple_finiteRep_classes_basis_of_complete_family
      (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) hπ'_pairwise hπ'_complete
  let fL : R₀[K](G) →ₗ[ℤ] R₀[K'](G) :=
    (finiteRepGrothendieckScalarExtensionHom K K' G).toIntLinearMap
  let rL : R₀[K'](G) →ₗ[ℤ] R₀[K](G) := b'.constr ℤ b
  have hbasis_add : ∀ i,
      finiteRepGrothendieckScalarExtensionHom K K' G (b i) = b' i := by
    intro i
    -- Scalar extension sends the simple basis class `[π i]₀` to the matching simple class over
    -- `K'`, so the two chosen bases are transported termwise.
    rw [show b i = [π i]₀ by
      simp [b, simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [show b' i = [((FDRep.scalarExtension (π i) : FDRep K' G))]₀ by
      simp [b', simple_finiteRep_classes_basis_of_complete_family_apply]]
    rw [finiteRepGrothendieckScalarExtensionHom_class_eq]
  have hbasis : ∀ i, fL (b i) = b' i := by
    intro i
    simpa [fL] using hbasis_add i
  have hrightL : fL.comp rL = LinearMap.id := by
    -- On the target simple basis, the reconstruction map sends each basis vector back to its
    -- chosen source preimage and scalar extension returns the original basis vector.
    apply b'.ext
    intro i
    simp [rL, hbasis i]
  have hleftL : rL.comp fL = LinearMap.id := by
    -- The same basis comparison shows that the transported basis vectors over `K` are recovered
    -- after applying scalar extension and then the basis-defined inverse.
    apply b.ext
    intro i
    simp [rL, hbasis i]
  let r : R₀[K'](G) →+ R₀[K](G) := rL.toAddMonoidHom
  refine ⟨r, ?_, ?_⟩
  · -- Repackage the linear right-inverse identity as an equality of additive homomorphisms.
    apply AddMonoidHom.ext
    intro x
    have hright_apply :=
      congrArg (fun t : R₀[K'](G) →ₗ[ℤ] R₀[K'](G) => t x) hrightL
    simpa [fL, r, LinearMap.comp_apply] using hright_apply
  · -- The linear left-inverse identity immediately gives injectivity of scalar extension.
    intro x y hxy
    have hleft_apply_x :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) => t x) hleftL
    have hleft_apply_y :=
      congrArg (fun t : R₀[K](G) →ₗ[ℤ] R₀[K](G) => t y) hleftL
    calc
      x = rL (fL x) := by simpa [LinearMap.comp_apply] using hleft_apply_x.symm
      _ = rL (fL y) := by simpa [fL] using congrArg rL hxy
      _ = y := by simpa [LinearMap.comp_apply] using hleft_apply_y

/-- Helper for Corollary 16-16.1-3: the normalized pairing distributes over finite integer linear
combinations in the left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left_local
    {ι : Type*}
    (s : Finset ι)
    (a : ι → ℤ)
    (χ : ι → G → K)
    (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum contributes no pairing mass.
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      have hzsmul : (a i • χ i : G → K) = (((a i : ℤ) : K) • χ i) := by
        -- Rewrite the integer action on class functions as scalar multiplication in `K`.
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      -- After rewriting the inserted summand, bilinearity handles the rest.
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Corollary 16-16.1-3: the normalized pairing distributes over finite sums in the
left argument. -/
private theorem groupFunctionPairing_finset_sum_left_local
    {F : Type u} [Field F]
    {ι : Type*}
    (s : Finset ι)
    (χ : ι → G → F)
    (ψ : G → F) :
    ⟪∑ j ∈ s, χ j, ψ⟫ = ∑ j ∈ s, ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum contributes no pairing mass.
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Additivity of the pairing converts the inserted summand into the corresponding sum term.
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, ih, Finset.sum_insert hi]

/-- Helper for Corollary 16-16.1-3: if a simple object `σ` is represented by `π iσ` inside a
complete simple family, then its Grothendieck class is the `iσ`-th basis vector in the canonical
simple-class basis. -/
private theorem simple_class_basis_repr_eq_single_local
    {F : Type u} [Field F]
    {ι : Type*}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (σ : FDRep F G) [Simple σ]
    (iσ : ι)
    (hσ_iso : Nonempty (π iσ ≅ σ)) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr [σ]₀ =
      Finsupp.single iσ (1 : ℤ) := by
  let b : Module.Basis ι ℤ (R₀[F](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  have hclass : [σ]₀ = [π iσ]₀ := by
    -- Replace `σ` by the chosen family representative before reading basis coordinates.
    simpa using
      (finiteRepGrothendieckClass_eq_of_nonempty_iso
        (L := F) (G := G) (V := σ) (W := π iσ) ⟨hσ_iso.some.symm⟩)
  -- The canonical basis already sends `[π iσ]₀` to the singleton coordinate vector.
  calc
    b.repr [σ]₀ = b.repr [π iσ]₀ := by rw [hclass]
    _ = Finsupp.single iσ (1 : ℤ) := by
          simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using b.repr_self iσ

/-- Helper for Corollary 16-16.1-3: the coordinates of a simple class in a complete simple basis
are Kronecker-delta coordinates at the representing index. -/
private theorem simple_class_basis_coord_eq_ite_local
    {F : Type u} [Field F]
    {ι : Type*} [DecidableEq ι]
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (σ : FDRep F G) [Simple σ]
    (iσ j : ι)
    (hσ_iso : Nonempty (π iσ ≅ σ)) :
    (simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete).repr [σ]₀ j =
      if j = iσ then 1 else 0 := by
  -- Read off the `j`-th coordinate from the one-hot basis vector computed above.
  have hrepr :=
    simple_class_basis_repr_eq_single_local
      (G := G) π hπ_pairwise hπ_complete σ iσ hσ_iso
  have hcoord := congrArg (fun c : ι →₀ ℤ ↦ c j) hrepr
  simpa [Finsupp.single_apply, eq_comm] using hcoord

/-- Helper for Corollary 16-16.1-3: if a simple object `σ` is represented by `π iσ` inside a
complete simple family over a characteristic-zero field, then its irreducible character is the
`iσ`-th basis vector in the canonical irreducible-character basis. -/
private theorem irreducible_character_basis_repr_eq_single_local
    {F : Type u} [Field F] [CharZero F]
    {ι : Type*}
    (π : ι → FDRep F G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (σ : FDRep F G) [Simple σ]
    (iσ : ι)
    (hσ_iso : Nonempty (π iσ ≅ σ)) :
    (irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete).repr
        (FDRep.irreducibleCharacter F σ) =
      Finsupp.single iσ (1 : ℤ) := by
  let b : Module.Basis ι ℤ (R[F](G)) :=
    irreducible_characters_basis_of_complete_family F π hπ_pairwise hπ_complete
  have hchar :
      FDRep.irreducibleCharacter F σ = FDRep.irreducibleCharacter F (π iσ) := by
    -- Replace `σ` by the chosen family representative before reading irreducible-character
    -- coordinates in the canonical basis.
    ext g
    simpa [FDRep.irreducibleCharacter_apply] using
      congrFun (FDRep.char_iso hσ_iso.some.symm) g
  -- The canonical irreducible-character basis already sends `π iσ` to the singleton vector.
  calc
    b.repr (FDRep.irreducibleCharacter F σ) =
        b.repr (FDRep.irreducibleCharacter F (π iσ)) := by
          rw [hchar]
    _ = Finsupp.single iσ (1 : ℤ) := by
          simpa [b, irreducible_characters_basis_of_complete_family_apply] using b.repr_self iσ

/-- Helper for Corollary 16-16.1-3: once a descended source class has been identified as
`[π i]₀`, semisimplicity over `K'` upgrades the scalar-extension class equality to an actual
isomorphism. -/
private theorem scalarExtension_iso_of_descended_simple_class_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι : Type*}
    (π : ι → FDRep K G)
    (S : FDRep K' G) [Simple S]
    (i : ι)
    (hclass :
      finiteRepGrothendieckScalarExtensionHom K K' G [π i]₀ = [S]₀) :
    Nonempty (((FDRep.scalarExtension (π i) : FDRep K' G)) ≅ S) := by
  letI : NeZero (Nat.card G : K') :=
    nat_card_neZero_of_hasEnoughRoots_local (K := K) (L := K') (G := G)
  have hsemi_source :
      IsSemisimpleRepresentation ((FDRep.scalarExtension (π i) : FDRep K' G)).ρ := by
    -- Maschke over `K'` gives semisimplicity for the scalar-extended source simple object.
    infer_instance
  have hsemi_target : IsSemisimpleRepresentation S.ρ := by
    -- The simple target is semisimple over the same field for the same reason.
    infer_instance
  -- Rewrite the class equality in the literal `[scalarExtension (π i)]₀` form expected by the
  -- semisimple class-equality owner.
  have hclass' : [FDRep.scalarExtension (π i)]₀ = [S]₀ := by
    simpa using hclass
  exact
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple
      hsemi_source hsemi_target).mp hclass'

/-- Helper for Corollary 16-16.1-3: scalar extension of a simple source representation admits a
finite internal decomposition into irreducible summands whose characters add up to the
scalar-extended character. -/
private theorem scalarExtension_semisimple_irreducible_character_sum_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {T : FDRep K G} :
    ∃ (κ : Type*) (_ : Fintype κ)
      (σ : κ → Subrepresentation ((FDRep.scalarExtension T : FDRep K' G)).ρ),
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ ∧
        (∀ i, (σ i).toRepresentation.IsIrreducible) ∧
        ((FDRep.scalarExtension T : FDRep K' G)).character =
          ∑ i, ((σ i).toRepresentation).character := by
  classical
  let E : FDRep K' G := FDRep.scalarExtension T
  letI : NeZero (Nat.card G : K') :=
    nat_card_neZero_of_hasEnoughRoots_local (K := K) (L := K') (G := G)
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := E.ρ)
  letI : Fintype κ := hκ
  refine ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr, ?_⟩
  let hinternal : DirectSum.IsInternal (fun i : κ ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  -- Decompose the scalar-extended trace along the internal direct sum of irreducible summands.
  ext g
  simpa [E, Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := K') (M := E) (N := fun i : κ ↦ (σ i).toSubmodule) hinternal
      (f := E.ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Corollary 16-16.1-3: over a field containing the exponent roots of unity of `G`,
the self-intertwining space of a simple representation is nontrivial because it contains the
identity map. -/
private theorem simple_self_intertwining_nontrivial_local
    (V : FDRep K G) [Simple V] :
    Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  -- The identity endomorphism of `V` gives a nonzero intertwiner.
  refine ⟨0, e (𝟙 V), ?_⟩
  intro h
  apply CategoryTheory.id_nonzero V
  exact e.injective h.symm

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, the self-pairing of a simple
character is computed by the finrank of its self-intertwining space. -/
private theorem simple_character_pairing_eq_finrank_self_intertwining_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ =
      Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ) := by
  let X : Rep K G := (forget₂ (FDRep K G) (Rep K G)).obj V
  let e₁ : (V ⟶ V) ≃ₗ[K] (X ⟶ X) := (FDRep.forget₂HomLinearEquiv V V).symm
  let e₂ : (X ⟶ X) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := by
    simpa [X, FDRep.forget₂_ρ] using (Rep.homLinearEquiv X X)
  let e : (V ⟶ V) ≃ₗ[K] (Representation.IntertwiningMap V.ρ V.ρ) := e₁.trans e₂
  letI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero <|
      nat_card_ne_zero_of_hasEnoughRoots_local (K := K) (L := K) (G := G)
  letI : FiniteDimensional K (Representation.IntertwiningMap V.ρ V.ρ) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  -- The Chapter 12 pairing formula reduces the character pairing to the intertwining-space size.
  exact
    Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
      K V.ρ V.ρ

/-- Helper for Corollary 16-16.1-3: over the algebraic closure, the self-pairing of an
irreducible character is `1` once enough roots of unity give Maschke's nonvanishing hypothesis. -/
private theorem algebraicClosure_irreducible_character_self_pairing_eq_one_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {V : Type u} [AddCommGroup V] [Module (AlgebraicClosure K) V]
    (ρ : Representation (AlgebraicClosure K) G V)
    [FiniteDimensional (AlgebraicClosure K) V] [ρ.IsIrreducible] :
    ⟪ρ.character, ρ.character⟫ = (1 : AlgebraicClosure K) := by
  letI : Invertible (Nat.card G : AlgebraicClosure K) :=
    invertibleOfNonzero <|
      nat_card_ne_zero_of_hasEnoughRoots_local
        (K := K) (L := AlgebraicClosure K) (G := G)
  -- Over the algebraic closure, Schur's lemma makes the self-intertwining space
  -- one-dimensional.
  calc
    ⟪ρ.character, ρ.character⟫ =
        Module.finrank (AlgebraicClosure K) (Representation.IntertwiningMap ρ ρ) := by
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              (K := AlgebraicClosure K) (G := G) ρ ρ)
    _ = 1 := by
          simpa using
            (Representation.IsIrreducible.finrank_intertwiningMap_self (ρ := ρ))

/-- Helper for Corollary 16-16.1-3: once the algebraic-closure scalar extension of a simple
source representation is irreducible, the source self-pairing maps to `1`. -/
private theorem simple_character_pairing_self_map_eq_one_of_algClosure_irreducible_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (V : FDRep K G) [Simple V]
    (hVΩ : (Representation.scalarExtension V.ρ).IsIrreducible) :
    algebraMap K (AlgebraicClosure K) ⟪V.character, V.character⟫ =
      (1 : AlgebraicClosure K) := by
  let VΩ : FDRep (AlgebraicClosure K) G := FDRep.of (Representation.scalarExtension V.ρ)
  have hchar_map :
      VΩ.character = fun g ↦ algebraMap K (AlgebraicClosure K) (V.character g) := by
    -- Scalar extension only changes the character coefficients.
    simpa [VΩ] using
      (scalarExtension_character_eq_map_local
        (G := G) (F := K) (E := AlgebraicClosure K) (τ := V.ρ))
  have hpair_map :
      ⟪VΩ.character, VΩ.character⟫ =
        algebraMap K (AlgebraicClosure K) ⟪V.character, V.character⟫ := by
    -- Rewrite the algebraic-closure pairing through coefficient extension.
    rw [hchar_map, ← groupFunctionPairingOverField_algebraMap_local
      (F := K) (E := AlgebraicClosure K) (G := G) (φ := V.character) (ψ := V.character)]
  letI : (Representation.scalarExtension V.ρ).IsIrreducible := hVΩ
  have hpair_one :
      ⟪VΩ.character, VΩ.character⟫ = (1 : AlgebraicClosure K) := by
    -- The irreducible algebraic-closure scalar extension has one-dimensional self-intertwining.
    simpa [VΩ] using
      (algebraicClosure_irreducible_character_self_pairing_eq_one_local
        (K := K) (G := G) (ρ := Representation.scalarExtension V.ρ))
  -- Combine the scalar-extension pairing formula with the algebraic-closure irreducible pairing.
  exact hpair_map.symm.trans hpair_one

/-- Helper for Corollary 16-16.1-3: over a field containing the exponent roots of unity of `G`,
the self-pairing of a simple character should remain nonzero. -/
private theorem simple_character_pairing_self_ne_zero_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  intro hpair_zero
  -- Route correction: the remaining blocker is now explicit and source-faithful. A generic
  -- "zero character implies zero semisimple quotient" lemma is false in positive characteristic
  -- (for example `p` copies of the trivial representation of the trivial group over `𝔽_p`), so
  -- the only viable next step is the enough-roots/quasisplit bridge showing that the scalar
  -- extension to `AlgebraicClosure K` is irreducible, hence has self-pairing `1`.
  --
  -- TODO: prove `(Representation.scalarExtension V.ρ).IsIrreducible` from the Chapter `12/16`
  -- enough-roots descent route, then feed it to the preceding adapter lemma.
  have hVΩ :
      (Representation.scalarExtension V.ρ).IsIrreducible := by
    sorry
  have hpair_map_one :
      algebraMap K (AlgebraicClosure K) ⟪V.character, V.character⟫ =
        (1 : AlgebraicClosure K) := by
    -- The previous adapter isolates the remaining irreducibility input.
    exact
      simple_character_pairing_self_map_eq_one_of_algClosure_irreducible_local
        (K := K) (G := G) (V := V) hVΩ
  have hpair_map_zero :
      algebraMap K (AlgebraicClosure K) ⟪V.character, V.character⟫ =
        (0 : AlgebraicClosure K) := by
    -- Mapping the vanishing source pairing to the algebraic closure preserves zero.
    rw [hpair_zero]
    simp
  exact one_ne_zero (hpair_map_one.symm.trans hpair_map_zero)

/-- Helper for Corollary 16-16.1-3: if the scalar-extended character of a simple `K[G]`-module
agrees with the character of a simple `K'[G]`-module, then that simple target already appears as
an irreducible constituent of the scalar extension. -/
private theorem simple_constituent_exists_of_scalarExtension_character_eq_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {T : FDRep K G} [Simple T]
    (S : FDRep K' G) [Simple S]
    (hchar : (fun g ↦ algebraMap K K' (T.character g)) = S.character) :
    ∃ (κ : Type*) (_ : Fintype κ)
      (σ : κ → Subrepresentation ((FDRep.scalarExtension T : FDRep K' G)).ρ),
      iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
        (⨆ i, (σ i).toSubmodule) = ⊤ ∧
        (∀ i, (σ i).toRepresentation.IsIrreducible) ∧
        ((FDRep.scalarExtension T : FDRep K' G)).character =
          ∑ i, ((σ i).toRepresentation).character ∧
        ∃ i, Nonempty (FDRep.of ((σ i).toRepresentation) ≅ S) := by
  classical
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  obtain ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr, hσ_char⟩ :=
    scalarExtension_semisimple_irreducible_character_sum_local
      (K := K) (K' := K') (G := G) (T := T)
  letI : Fintype κ := hκ
  refine ⟨κ, hκ, σ, hσ_indep, hσ_top, hσ_irr, hσ_char, ?_⟩
  by_contra hconstituent
  have hterm_zero :
      ∀ idx, ⟪((σ idx).toRepresentation).character, S.character⟫ = (0 : K') := by
    intro idx
    letI : ((σ idx).toRepresentation).IsIrreducible := hσ_irr idx
    letI : Invertible (Nat.card G : K') :=
      invertibleOfNonzero <|
        nat_card_ne_zero_of_hasEnoughRoots_local (K := K) (L := K') (G := G)
    have hi_not_iso : ¬ Nonempty (((σ idx).toRepresentation).Equiv S.ρ) := by
      intro hi
      apply hconstituent
      rcases hi with ⟨e⟩
      refine ⟨idx, ?_⟩
      exact ⟨by simpa using (Representation.Equiv.toFDRepIso e)⟩
    -- Off-diagonal irreducible summands pair trivially with the simple target character.
    exact
      Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
        K' ((σ idx).toRepresentation) S.ρ hi_not_iso
  have hpair_zero :
      ⟪((FDRep.scalarExtension T : FDRep K' G)).character, S.character⟫ = (0 : K') := by
    rw [hσ_char]
    calc
      ⟪∑ i, ((σ i).toRepresentation).character, S.character⟫
          = ∑ i, ⟪((σ i).toRepresentation).character, S.character⟫ := by
              simpa using
                (groupFunctionPairing_finset_sum_left_local
                  (G := G) (F := K') (s := (Finset.univ : Finset κ))
                  (χ := fun idx : κ ↦ ((σ idx).toRepresentation).character)
                  (ψ := S.character))
      _ = ∑ i, (0 : K') := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hterm_zero i
      _ = 0 := by simp
  have hpair_ne :
      ⟪((FDRep.scalarExtension T : FDRep K' G)).character, S.character⟫ ≠ (0 : K') := by
    have hchar' : ((FDRep.scalarExtension T : FDRep K' G)).character = S.character := by
      calc
        ((FDRep.scalarExtension T : FDRep K' G)).character
            = fun g ↦ algebraMap K K' (T.character g) := by
                simpa using
                  (scalarExtension_character_eq_map_local
                    (G := G) (F := K) (E := K') (τ := T.ρ))
        _ = S.character := hchar
    -- After identifying the scalar-extended character with `S.character`, self-pairing is
    -- nonzero by Schur orthogonality.
    rw [hchar']
    letI : HasEnoughRootsOfUnity K' (Monoid.exponent G) :=
      hasEnoughRootsOfUnity_extension_local (K := K) (L := K') (G := G)
    exact
      simple_character_pairing_self_ne_zero_of_hasEnoughRoots_local
        (K := K') (G := G) (V := S)
  exact hpair_ne hpair_zero

/-- Helper for Corollary 16-16.1-3: once a constituent of the scalar extension already carries the
target simple character, the complementary quotient has zero character. -/
private theorem scalarExtension_quotient_character_eq_zero_of_constituent_local
    {T : FDRep K G}
    (S : FDRep K' G)
    {κ : Type*}
    (σ : κ → Subrepresentation ((FDRep.scalarExtension T : FDRep K' G)).ρ)
    (i : κ)
    (hEchar : ((FDRep.scalarExtension T : FDRep K' G)).character = S.character)
    (hconstituent_char : (FDRep.of ((σ i).toRepresentation)).character = S.character) :
    (Representation.quotient ((FDRep.scalarExtension T : FDRep K' G)).ρ
      (σ i).toSubmodule (σ i).apply_mem_toSubmodule).character = 0 := by
  let E : FDRep K' G := FDRep.scalarExtension T
  let Qρ : Representation K' G (E ⧸ (σ i).toSubmodule) :=
    Representation.quotient E.ρ (σ i).toSubmodule (σ i).apply_mem_toSubmodule
  have hdecomp :
      E.character =
        (FDRep.of ((σ i).toRepresentation)).character + Qρ.character := by
    -- Split the scalar-extended character into the chosen constituent and its quotient.
    simpa [E] using
      character_eq_add_character_quotient_of_invariant_submodule_local
        (G := G) (F := K') (ρ := E.ρ)
        (W := (σ i).toSubmodule) (hW := (σ i).apply_mem_toSubmodule)
  have hsum_target :
      (FDRep.of ((σ i).toRepresentation)).character + Qρ.character = S.character := by
    exact hdecomp.symm.trans hEchar
  have hsum_target' : S.character + Qρ.character = S.character := by
    calc
      S.character + Qρ.character =
          (FDRep.of ((σ i).toRepresentation)).character + Qρ.character := by
            rw [← hconstituent_char]
      _ = S.character := hsum_target
  -- Cancel the common simple character to see that the quotient character vanishes pointwise.
  ext g
  have hg : S.character g + Qρ.character g = S.character g + 0 := by
    simpa using congrFun hsum_target' g
  exact add_left_cancel hg

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, scalar extension of a simple
`K[G]`-representation should stay simple. -/
private theorem simple_scalarExtension_character_eq_nonempty_iso_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {T : FDRep K G} [Simple T]
    (S : FDRep K' G) [Simple S]
    (hchar : (fun g ↦ algebraMap K K' (T.character g)) = S.character) :
    Nonempty (((FDRep.scalarExtension T : FDRep K' G)) ≅ S) := by
  let E : FDRep K' G := FDRep.scalarExtension T
  letI : Simple E :=
    scalarExtension_simple_of_hasEnoughRoots_local
      (K := K) (K' := K') (G := G) (T := T)
  letI : Representation.IsIrreducible E.ρ := FDRep.isIrreducible_of_simple E
  letI : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  by_contra hIso
  have hnot_iso : ¬ Nonempty (Representation.Equiv E.ρ S.ρ) := by
    intro hrep
    apply hIso
    rcases hrep with ⟨e⟩
    exact ⟨Representation.Equiv.toFDRepIso e⟩
  have hpair_zero :
      ⟪E.character, S.character⟫ = (0 : K') := by
    -- Distinct simple targets have zero pairing over the scalar-extension field.
    exact
      Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
        K' E.ρ S.ρ hnot_iso
  have hEchar :
      E.character = S.character := by
    -- The scalar-extended source character is exactly the prescribed target character.
    calc
      E.character = fun g ↦ algebraMap K K' (T.character g) := by
        simpa [E] using
          (scalarExtension_character_eq_map_local
            (G := G) (F := K) (E := K') (τ := T.ρ))
      _ = S.character := hchar
  have hself_zero : ⟪S.character, S.character⟫ = (0 : K') := by
    -- Rewrite the mixed pairing through the character identity upstairs.
    simpa [hEchar] using hpair_zero
  letI : HasEnoughRootsOfUnity K' (Monoid.exponent G) :=
    hasEnoughRootsOfUnity_extension_local (K := K) (L := K') (G := G)
  have hself_ne : ⟪S.character, S.character⟫ ≠ (0 : K') := by
    -- Self-pairing of the simple target is nonzero over `K'`.
    exact
      simple_character_pairing_self_ne_zero_of_hasEnoughRoots_local
        (K := K') (G := G) (V := S)
  exact hself_ne hself_zero

/-- Helper for Corollary 16-16.1-3: if scalar extension identifies two simple `K[G]`-modules,
their ordinary characters already descend to the same element of `R[K](G)`. -/
private theorem irreducibleCharacter_eq_of_scalarExtension_nonempty_iso_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {V W : FDRep K G} [Simple V] [Simple W]
    (hIso :
      Nonempty
        (((FDRep.scalarExtension V : FDRep K' G)) ≅
          ((FDRep.scalarExtension W : FDRep K' G)))) :
    FDRep.irreducibleCharacter K V = FDRep.irreducibleCharacter K W := by
  rcases hIso with ⟨e⟩
  refine
    characterRing_preimage_unique_local
      (K := K) (K' := K') (G := G)
      (χ₁ := FDRep.irreducibleCharacter K V)
      (χ₂ := FDRep.irreducibleCharacter K W)
      ?_
  ext g
  -- Compare the two descended characters after scalar extension and then transport across the
  -- scalar-extension isomorphism upstairs.
  calc
    algebraMap K K' ((FDRep.irreducibleCharacter K V) g) =
        ((FDRep.scalarExtension V : FDRep K' G)).character g := by
          simpa [FDRep.irreducibleCharacter_apply] using
            (congrFun
              (scalarExtension_character_eq_map_local
                (G := G) (F := K) (E := K') (τ := V.ρ))
              g).symm
    _ = ((FDRep.scalarExtension W : FDRep K' G)).character g := by
          simpa using congrFun (FDRep.char_iso e) g
    _ = algebraMap K K' ((FDRep.irreducibleCharacter K W) g) := by
          simpa [FDRep.irreducibleCharacter_apply] using
            congrFun
              (scalarExtension_character_eq_map_local
                (G := G) (F := K) (E := K') (τ := W.ρ))
              g

/-- Helper for Corollary 16-16.1-3: in a pairwise nonisomorphic simple `K[G]`-family, scalar
extension cannot create a new isomorphism between two distinct indices. -/
private theorem scalarExtension_index_eq_of_nonempty_iso_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {i j : ι}
    (hIso :
      Nonempty
        (((FDRep.scalarExtension (π i) : FDRep K' G)) ≅
          ((FDRep.scalarExtension (π j) : FDRep K' G)))) :
    i = j := by
  -- Route correction: this reflection really uses the source family as a complete simple family,
  -- because the source-faithful route compares both indices through the unique descended index of
  -- the common scalar-extended simple target.
  letI : Simple (π i) := hπ_complete.isSimple i
  letI : Simple (π j) := hπ_complete.isSimple j
  letI : Representation.IsIrreducible (π i).ρ := FDRep.isIrreducible_of_simple (π i)
  letI : Representation.IsIrreducible (π j).ρ := FDRep.isIrreducible_of_simple (π j)
  letI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero <|
      nat_card_ne_zero_of_hasEnoughRoots_local (K := K) (L := K) (G := G)
  have hchar :
      FDRep.irreducibleCharacter K (π i) = FDRep.irreducibleCharacter K (π j) :=
    irreducibleCharacter_eq_of_scalarExtension_nonempty_iso_local
      (K := K) (K' := K') (G := G) (V := π i) (W := π j) hIso
  by_contra hij
  have hpair_eq :
      ⟪(π i).character, (π j).character⟫ =
        ⟪(π j).character, (π j).character⟫ := by
    -- Pair the descended character equality with the `j`-th source simple character.
    have hpair_eq' :=
      congrArg (fun χ : R[K](G) ↦ ⟪(χ : G → K), (π j).character⟫) hchar
    simpa [FDRep.irreducibleCharacter_apply] using hpair_eq'
  have hij_rep : ¬ Nonempty (Representation.Equiv (π i).ρ (π j).ρ) := by
    intro hij_rep
    apply hπ_pairwise hij
    rcases hij_rep with ⟨e⟩
    simpa using
      (show Nonempty (FDRep.of (π i).ρ ≅ FDRep.of (π j).ρ) from
        ⟨Representation.Equiv.toFDRepIso e⟩)
  have hpair_zero :
      ⟪(π i).character, (π j).character⟫ = (0 : K) := by
    -- Distinct simple characters are orthogonal over the source field.
    exact
      Representation.groupFunctionPairingOverField_character_eq_zero_of_not_isomorphic
        K (π i).ρ (π j).ρ hij_rep
  have hself_zero :
      ⟪(π j).character, (π j).character⟫ = (0 : K) := by
    -- Transport the off-diagonal vanishing across the paired character equality.
    exact hpair_eq.symm.trans hpair_zero
  have hself_ne :
      ⟪(π j).character, (π j).character⟫ ≠ (0 : K) := by
    -- Self-pairing of a simple character is nonzero by Schur orthogonality.
    exact
      simple_character_pairing_self_ne_zero_of_hasEnoughRoots_local
        (K := K) (G := G) (V := π j)
  exact hself_ne hself_zero

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, scalar extension of a simple
`K[G]`-representation should stay simple. -/
private theorem scalarExtension_simple_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {T : FDRep K G} [Simple T] :
    Simple ((FDRep.scalarExtension T : FDRep K' G)) := by
  -- Route correction: the missing owner is not a transport argument on submodules. The intended
  -- source-faithful proof is the one-hot coefficient argument on the scalar-extended character,
  -- and it must avoid the false positive-character claim that a semisimple representation with
  -- zero character is automatically subsingleton.
  --
  -- TODO: decompose `FDRep.scalarExtension T` semisimply over `K'`, descend its character with
  -- `characterRing_preimage_existsUnique_of_hasEnoughRoots_local`, and use coefficient
  -- uniqueness in the descended irreducible-character basis to force a single simple constituent.
  sorry

/-- Helper for Corollary 16-16.1-3: under enough roots of unity, every simple `K'[G]`-module
comes from a unique index in a complete simple `K[G]`-family after scalar extension. -/
private theorem scalarExtension_existsUnique_index_of_complete_simple_family_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (S : FDRep K' G) [Simple S] :
    ∃! i, Nonempty (((FDRep.scalarExtension (π i) : FDRep K' G)) ≅ S) := by
  classical
  have huniq :
      ∀ i j,
        Nonempty (((FDRep.scalarExtension (π i) : FDRep K' G)) ≅ S) →
          Nonempty (((FDRep.scalarExtension (π j) : FDRep K' G)) ≅ S) →
            i = j := by
    intro i j hi hj
    -- Any two indices mapping to `S` become isomorphic after scalar extension, so the previous
    -- reflection lemma forces the source indices to agree.
    exact
      scalarExtension_index_eq_of_nonempty_iso_local
        (K := K) (K' := K') (G := G) π hπ_pairwise hπ_complete
        ⟨hi.some.trans hj.some.symm⟩
  -- Route correction: the intended source proof first descends `S.character` to `R[K](G)`,
  -- expands that descended character in the irreducible `K`-basis attached to `π`, and then uses
  -- pairing against `S.character` to force a one-hot coefficient vector.
  --
  -- TODO: combine `characterRing_preimage_existsUnique_of_hasEnoughRoots_local` with the
  -- descended irreducible-character basis argument to produce one index `i`; once that existence
  -- witness is built, finish the `∃!` proof with `huniq`.
  sorry

/-- Helper for Corollary 16-16.1-3: once the source-faithful owners for simplicity and unique
descent are isolated, the scalar-extended family is automatically pairwise nonisomorphic and
complete. -/
private theorem scalarExtension_complete_simple_family_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    PairwiseNonisomorphic
        (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) ∧
      IsCompleteIrreducibleFamily
        (fun i ↦ ((FDRep.scalarExtension (π i) : FDRep K' G))) := by
  refine ⟨?_, ?_⟩
  · intro i j hij hIso
    -- Reflect the scalar-extension isomorphism back to the original `K`-family through character
    -- descent, then invoke pairwise nonisomorphism of the source family.
    exact
      hij <|
        scalarExtension_index_eq_of_nonempty_iso_local
          (K := K) (K' := K') (G := G) π hπ_pairwise hπ_complete hIso
  · refine
      { isSimple := fun i ↦
          scalarExtension_simple_of_hasEnoughRoots_local
            (K := K) (K' := K') (G := G) (T := π i)
        exists_iso := ?_ }
    intro S hS
    letI : Simple S := hS
    rcases
        scalarExtension_existsUnique_index_of_complete_simple_family_of_hasEnoughRoots_local
          (K := K) (K' := K') (G := G) π hπ_pairwise hπ_complete S with
      ⟨i, hi, _⟩
    rcases hi with ⟨e⟩
    -- The unique descended index supplies the completeness witness after reversing the isomorphism.
    exact ⟨i, ⟨e.symm⟩⟩

/-- Helper for Corollary 16-16.1-3: over any field, one can choose one representative of each
isomorphism class of simple finite-dimensional `G`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_over_field_local :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep K G // CategoryTheory.Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep K G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic representatives define the same quotient class, so distinct classes stay
    -- pairwise nonisomorphic.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Corollary 16-16.1-3: the remaining source-faithful Chapter `12/16` owner is the
retract data for ordinary scalar extension `R₀[K](G) → R₀[K'](G)`. -/
private theorem finiteRepGrothendieckScalarExtension_retract_data_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ r : R₀[K'](G) →+ R₀[K](G),
      (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
        Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_over_field_local
      (K := K) (G := G)
  obtain ⟨hπ'_pairwise, hπ'_complete⟩ :=
    scalarExtension_complete_simple_family_of_hasEnoughRoots_local
      (K := K) (K' := K') (G := G) π hπ_pairwise hπ_complete
  -- Once the source family and its scalar extension are both complete simple families, the
  -- basis-transport retract from the earlier packet applies directly.
  exact
    finiteRepGrothendieckScalarExtension_retract_data_of_complete_simple_family_local
      (K := K) (K' := K') (G := G) π hπ_pairwise hπ_complete hπ'_pairwise hπ'_complete

/-- Helper for Corollary 16-16.1-3: once the ordinary scalar-extension retract data is available,
it packages immediately into the left inverse consumed by the main corollary. -/
private theorem finiteRepGrothendieckScalarExtension_left_inverse_of_retract_data_local
    (h :
      ∃ r : R₀[K'](G) →+ R₀[K](G),
        (finiteRepGrothendieckScalarExtensionHom K K' G).comp r = AddMonoidHom.id _ ∧
          Function.Injective (finiteRepGrothendieckScalarExtensionHom K K' G)) :
    ∃ t : R₀[K'](G) →+ R₀[K](G),
      Function.LeftInverse t (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  rcases h with ⟨r, hr, hinj⟩
  -- The previously isolated formal upgrade turns the retract and injectivity data into a section.
  refine ⟨r, ?_⟩
  exact
    finiteRepGrothendieckScalarExtension_leftInverse_of_rightInverse_and_injective_local
      (K := K) (K' := K') (G := G) r hr hinj

/-- Helper for Corollary 16-16.1-3: the remaining Chapter `12` descent owner is a left inverse for
ordinary scalar extension `R₀[K](G) → R₀[K'](G)`. -/
private theorem finiteRepGrothendieckScalarExtension_left_inverse_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ t : R₀[K'](G) →+ R₀[K](G),
      Function.LeftInverse t (finiteRepGrothendieckScalarExtensionHom K K' G) := by
  -- The only open mathematical input is now the retract data isolated in the previous theorem.
  exact
    finiteRepGrothendieckScalarExtension_left_inverse_of_retract_data_local
      (K := K) (K' := K') (G := G)
      (finiteRepGrothendieckScalarExtension_retract_data_of_hasEnoughRoots_local
        (K := K) (K' := K') (G := G))

/-- Corollary 16-16.1-3: for every finite extension `K' / K`, the composite
`P_k(G) \xrightarrow{e} R_K(G) → R_K'(G)` is a split injection. -/
theorem projectiveGrothendieckScalarExtensionHom_after_scalarExtension_split_injective
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    ∃ s : R₀[K'](G) →+ finiteProjectiveGroupAlgebraGrothendieckGroup k G,
      Function.LeftInverse s
        ((finiteRepGrothendieckScalarExtensionHom K K' G).comp
          (projectiveGrothendieckScalarExtensionHom A K)) := by
  -- Route correction: stop reducing to the direct `A → K'` projective map. The corollary closes
  -- once we compose the known section of `projectiveGrothendieckScalarExtensionHom A K` with the
  -- ordinary scalar-extension retract over the finite extension `K' / K`.
  obtain ⟨t, ht⟩ :=
    finiteRepGrothendieckScalarExtension_left_inverse_of_hasEnoughRoots_local
      (K := K) (K' := K') (G := G)
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  refine ⟨s.comp t, ?_⟩
  intro x
  -- First retract along `R₀[K](G) → R₀[K'](G)`, then apply the existing section over `K`.
  change s (t
      ((finiteRepGrothendieckScalarExtensionHom K K' G)
        ((projectiveGrothendieckScalarExtensionHom A K) x))) = x
  rw [ht]
  exact hs x

end

end Representation
