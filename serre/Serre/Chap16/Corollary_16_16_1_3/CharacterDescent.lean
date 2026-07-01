import Mathlib
import Serre.Chap12.Proposition_12_12_1_1
import Serre.Chap12.Proposition_12_12_1_3
import Serre.Chap12.Proposition_12_12_6_5

noncomputable section

open scoped Representation

universe u

namespace Representation

open CategoryTheory

section

variable {K : Type u} [Field K]
variable {K' : Type u} [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Corollary 16-16.1-3: enough roots of unity persist after passing from `K` to an
algebraic extension. -/
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

/-- Helper for Corollary 16-16.1-3: scalar extension of a finite-dimensional representation
changes its character only by applying the coefficient map. -/
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
      congrFun
        (scalarExtension_character_eq_map_local
          (G := G) (F := L) (E := AlgebraicClosure K) (τ := V.ρ))
        g |>.symm
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
`K`-valued after extending coefficients to `K'`. -/
private theorem isValuedInBaseField_algebraMap_int_local (n : ℤ) :
    IsValuedInBaseField K (algebraMap ℤ (G → K') n) := by
  -- Rewrite `K`-valuedness as range membership for the coefficientwise algebra map, then choose
  -- the corresponding constant `K`-valued preimage.
  rw [Representation.isValuedInBaseField_iff_mem_pointwiseAlgebraMap_range]
  refine ⟨algebraMap ℤ (G → K) n, ?_⟩
  ext g
  simp [Pi.algebraMap_apply]

/-- Helper for Corollary 16-16.1-3: the `K`-valued class functions are closed under addition. -/
private theorem isValuedInBaseField_add_local
    {φ ψ : G → K'}
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

/-- Helper for Corollary 16-16.1-3: the `K`-valued class functions are closed under
pointwise multiplication. -/
private theorem isValuedInBaseField_mul_local
    {φ ψ : G → K'}
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

/-- Helper for Corollary 16-16.1-3: enough roots of unity should force every simple
`K'[G]`-character to take values in the base field `K`. -/
theorem simple_character_isValuedInBaseField_of_hasEnoughRoots_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (S : FDRep K' G) [Simple S] :
    IsValuedInBaseField K S.character := by
  -- Route correction: descend the ordinary character along the algebraic extension `K' / K`
  -- before packaging it as the simple generator used by the character ring.
  simpa using
    finiteRep_character_isValuedInBaseField_of_hasEnoughRoots_local
      (K := K) (L := K') (G := G) (V := S)

/-- Helper for Corollary 16-16.1-3: enough roots of unity force every `K'[G]`-virtual character
to take values in the base field `K`. -/
theorem character_isValuedInBaseField_of_mem_characterRing_of_hasEnoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    {χ : G → K'}
    (hχ : χ ∈ R[K'](G)) :
    IsValuedInBaseField K χ := by
  -- Extend the simple-character descent across the `ℤ`-algebra generation of `R[K'](G)`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, hρirr, rfl⟩
    letI : FiniteDimensional K' ρ := hρfd
    letI : ρ.ρ.IsIrreducible := hρirr
    let S : FDRep K' G := FDRep.of ρ.ρ
    letI : Representation.IsIrreducible S.ρ := by
      simpa [S] using hρirr
    letI : Simple S := FDRep.simple_of_isIrreducible S
    -- The generator case is the simple-character descent isolated above.
    simpa [S] using
      simple_character_isValuedInBaseField_of_hasEnoughRoots_local
        (K := K) (K' := K') (G := G) S
  · intro n
    -- Integer constants come directly from constant `K`-valued functions.
    simpa using isValuedInBaseField_algebraMap_int_local (K := K) (K' := K') (G := G) n
  · intro φ ψ _ _ hφ hψ
    -- Addition preserves coefficientwise descent.
    exact isValuedInBaseField_add_local (K := K) hφ hψ
  · intro φ ψ _ _ hφ hψ
    -- Multiplication preserves coefficientwise descent.
    exact isValuedInBaseField_mul_local (K := K) hφ hψ

/-- Helper for Corollary 16-16.1-3: enough roots of unity should make the group algebra
`K[G]` quasisplit. -/
theorem isQuasisplitGroupAlgebra_of_hasEnoughRootsOfUnity_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    IsQuasisplitGroupAlgebra K G := by
  -- Route correction: keep the source-faithful owner separate from the final rewrite
  -- `R[K](G) = R̄[K](G)`.
  --
  -- TODO: follow the Chapter 12 source route showing that enough roots annihilate the Schur
  -- denominators, hence `K[G]` is quasisplit.
  sorry

/-- Helper for Corollary 16-16.1-3: enough roots of unity identify the honest and overline
character rings over the base field. -/
theorem characterRing_eq_overlineCharacterRing_of_hasEnoughRootsOfUnity_local
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    R[K](G) = R̄[K](G) := by
  -- Convert the quasisplit owner into the exact ring-equality rewrite used downstream.
  exact
    (Representation.characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra K G).2
      (isQuasisplitGroupAlgebra_of_hasEnoughRootsOfUnity_local (K := K) (G := G))

end

end Representation
