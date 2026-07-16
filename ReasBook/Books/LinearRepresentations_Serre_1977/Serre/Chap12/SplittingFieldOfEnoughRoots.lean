import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_2_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Theorem_12_12_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u v w

namespace Representation

open CategoryTheory

section

variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGOfFinite_splittingFieldOfEnoughRoots : Fintype G :=
  Fintype.ofFinite G

/-- The cyclotomic field of the exponent of `G` contains enough exponent roots of unity. -/
instance cyclotomicField_exponent_hasEnoughRootsOfUnity :
    HasEnoughRootsOfUnity (CyclotomicField (Monoid.exponent G) ℚ) (Monoid.exponent G) where
  prim := by
    letI : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite
    letI :
        IsCyclotomicExtension {Monoid.exponent G} ℚ
          (CyclotomicField (Monoid.exponent G) ℚ) :=
      CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
    simpa using
      (IsCyclotomicExtension.exists_isPrimitiveRoot
        (S := {Monoid.exponent G}) (A := ℚ)
        (B := CyclotomicField (Monoid.exponent G) ℚ)
        (n := Monoid.exponent G) (by simp)
        (show Monoid.exponent G ≠ 0 by exact NeZero.ne _))
  cyc := rootsOfUnity.isCyclic _ _

/-- A characteristic-zero field containing the exponent roots receives the exponent cyclotomic
field. -/
noncomputable def cyclotomicFieldExponentAlgHomOfHasEnoughRoots
    (K : Type v) [Field K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] K := by
  classical
  let m := Monoid.exponent G
  let Lexp := CyclotomicField m ℚ
  letI : NeZero m := Monoid.neZero_exponent_of_finite
  letI : IsCyclotomicExtension {m} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := m) (K := ℚ)
  have hprim :
      ∀ n ∈ ({m} : Set ℕ), n ≠ 0 → ∃ r : K, IsPrimitiveRoot r n := by
    intro n hn _hn0
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K m
  let M : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {x : K | ∃ n ∈ ({m} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  let e : Lexp ≃ₐ[ℚ] M :=
    Classical.choice
      (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
        (S := {m}) ℚ Lexp K hprim)
  exact (IsScalarTower.toAlgHom ℚ M K).comp e.toAlgHom

/-- Coefficientwise scalar extension preserves ordinary virtual character rings. -/
theorem map_mem_characterRingOverField_algHom
    {F : Type u} [Field F]
    {E : Type v} [Field E]
    (f : F →ₐ[ℤ] E)
    {H : Type u} [Group H]
    (χ : G → F)
    (hχ : χ ∈ R[F](G)) :
    (f.compLeft G) χ ∈ R[E](G) := by
  letI : Algebra F E := f.toRingHom.toAlgebra
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional F ρ := hρfd
    let ρE : Rep E G := Rep.of (Representation.scalarExtension ρ.ρ)
    have hchar :
        (f.compLeft G) ρ.ρ.character = ρE.ρ.character := by
      ext g
      simpa [ρE] using
        (congrFun
          (by
            ext h
            exact LinearMap.trace_baseChange (ρ.ρ h) E :
              (Representation.scalarExtension ρ.ρ).character =
                fun h ↦ algebraMap F E (ρ.ρ.character h))
          g).symm
    simpa [hchar] using
      Representation.rep_character_mem_characterRingOverField
        (K := E) (G := G) ρE
  · intro n
    simpa using (R[E](G)).algebraMap_mem n
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).add_mem hφ hψ
  · intro φ ψ _ _ hφ hψ
    simpa using (R[E](G)).mul_mem hφ hψ

/-- Over an algebraically closed extension field, character values of finite-group
representations are already in any sufficiently large base field. -/
theorem finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_algClosed
    {F : Type u} [Field F]
    {Ω : Type v} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (ρ : Rep.{w} Ω G) [FiniteDimensional Ω ρ] (g : G) :
    ∃ x : F, algebraMap F Ω x = ρ.ρ.character g := by
  classical
  let m := Monoid.exponent G
  let b := Module.Free.chooseBasis Ω ρ
  let A :
      Matrix (Module.Free.ChooseBasisIndex Ω ρ)
        (Module.Free.ChooseBasisIndex Ω ρ) Ω :=
    LinearMap.toMatrix b b (ρ.ρ g)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F m
  let hprim : (primitiveRoots m F).Nonempty := by
    exact ⟨ζ, by
      rw [mem_primitiveRoots (Monoid.neZero_exponent_of_finite).pos]
      exact hζ⟩
  let e : rootsOfUnity m F ≃* rootsOfUnity m Ω :=
    rootsOfUnityEquivOfPrimitiveRoots
      (f := algebraMap F Ω)
      (algebraMap F Ω).injective hprim
  have hroot_preimage :
      ∀ μ ∈ A.charpoly.roots, ∃ x : F, algebraMap F Ω x = μ := by
    intro μ hμ
    have hμ_rep :
        μ ∈ (ρ.ρ g).charpoly.roots := by
      simpa [A] using hμ
    have hμ_order : μ ^ orderOf g = 1 :=
      Representation.charpoly_root_pow_orderOf_eq_one ρ.ρ g hμ_rep
    have hμ_exp : μ ^ m = 1 := by
      rcases Monoid.order_dvd_exponent g with ⟨d, hd⟩
      simpa [m, hd, pow_mul, hμ_order]
    let μRoots : rootsOfUnity m Ω := rootsOfUnity.mkOfPowEq μ hμ_exp
    refine ⟨((e.symm μRoots : rootsOfUnity m F) : Fˣ), ?_⟩
    simpa [e, μRoots, rootsOfUnity.coe_mkOfPowEq] using
      rootsOfUnityEquivOfPrimitiveRoots_symm_apply
        (f := algebraMap F Ω)
        (n := m)
        (algebraMap F Ω).injective
        hprim
        μRoots
  have hsum_preimage :
      ∀ s : Multiset Ω,
        (∀ μ ∈ s, ∃ x : F, algebraMap F Ω x = μ) →
        ∃ x : F, algebraMap F Ω x = s.sum := by
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
  refine ⟨x, ?_⟩
  calc
    algebraMap F Ω x = A.charpoly.roots.sum := hx
    _ = A.trace := by
          symm
          exact Matrix.trace_eq_sum_roots_charpoly A
    _ = ρ.ρ.character g := by
          symm
          simpa [A, Representation.character] using
            (LinearMap.trace_eq_matrix_trace Ω b (ρ.ρ g))

/-- Character values over any coefficient extension are in the sufficiently large base field. -/
theorem finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_extension
    {F : Type u} [Field F]
    {E : Type v} [Field E] [Algebra F E]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (ρ : Rep.{w} E G) [FiniteDimensional E ρ] (g : G) :
    ∃ x : F, algebraMap F E x = ρ.ρ.character g := by
  classical
  let Ω := AlgebraicClosure E
  let ρΩ : Rep.{max w v} Ω G := Rep.of (Representation.scalarExtension ρ.ρ)
  letI : FiniteDimensional Ω ρΩ := by
    dsimp [ρΩ]
    infer_instance
  obtain ⟨x, hx⟩ :=
    finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_algClosed
      (F := F) (Ω := Ω) (G := G) ρΩ g
  refine ⟨x, ?_⟩
  apply (algebraMap E Ω).injective
  calc
    algebraMap E Ω (algebraMap F E x) = algebraMap F Ω x := by
      simpa using (IsScalarTower.algebraMap_apply F E Ω x).symm
    _ = ρΩ.ρ.character g := hx
    _ = algebraMap E Ω (ρ.ρ.character g) := by
      simpa [ρΩ] using
        (congrFun
          (by
            ext h
            exact LinearMap.trace_baseChange (ρ.ρ h) Ω :
              (Representation.scalarExtension ρ.ρ).character =
                fun h ↦ algebraMap E Ω (ρ.ρ.character h))
          g)

/-- Over any coefficient extension, the value of a virtual character is already in a
sufficiently large base field. -/
theorem character_value_mem_algebraMap_range_of_hasEnoughRoots_extension
    {F : Type u} [Field F]
    {E : Type v} [Field E] [Algebra F E]
    [HasEnoughRootsOfUnity F (Monoid.exponent G)]
    (χ : G → E) (hχ : χ ∈ R[E](G)) (g : G) :
    ∃ x : F, algebraMap F E x = χ g := by
  classical
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional E ρ := hρfd
    exact finiteRep_character_value_mem_algebraMap_range_of_hasEnoughRoots_extension
      (F := F) (E := E) (G := G) ρ g
  · intro n
    refine ⟨algebraMap ℤ F n, ?_⟩
    simp
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨xφ, hxφ⟩
    rcases hψ with ⟨xψ, hxψ⟩
    refine ⟨xφ + xψ, ?_⟩
    simp [map_add, hxφ, hxψ]
  · intro φ ψ _ _ hφ hψ
    rcases hφ with ⟨xφ, hxφ⟩
    rcases hψ with ⟨xψ, hxψ⟩
    refine ⟨xφ * xψ, ?_⟩
    simp [map_mul, hxφ, hxψ]

end

end Representation
