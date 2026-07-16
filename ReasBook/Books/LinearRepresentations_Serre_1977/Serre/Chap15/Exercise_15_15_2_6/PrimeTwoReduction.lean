import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.Foundations

noncomputable section

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped Pointwise TensorProduct

universe u v w

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: a characteristic vector that already lies in `2E` forces every
diagonal value of the form to be even. -/
theorem isEven_of_characteristicModTwo_of_mem_two_mul
    (B : BilinForm ℤ E) (x : E) (hx : B.IsCharacteristicModTwo x) (hx_two : x ∈ (2 •ℤ E)) :
    B.IsEven := by
  intro y
  have hmod : B y y ≡ B x y [ZMOD 2] := hx y
  let f : E →ₗ[ℤ] ℤ := LinearMap.BilinForm.toLinHomFlip B y
  have hx_map : f x ∈ (2 •ℤ E).map f := Submodule.mem_map_of_mem hx_two
  have hmap_le : (2 •ℤ E).map f ≤ Representation.primeIdeal 2 • (⊤ : Submodule ℤ ℤ) := by
    calc
      (2 •ℤ E).map f = Representation.primeIdeal 2 • (⊤ : Submodule ℤ E).map f := by
        simp [Representation.primeIdeal, Submodule.map_smul'']
      _ ≤ Representation.primeIdeal 2 • (⊤ : Submodule ℤ ℤ) := by
        gcongr
        exact (show (⊤ : Submodule ℤ E).map f ≤ (⊤ : Submodule ℤ ℤ) from le_top)
  have hxy_mem : B x y ∈ Representation.primeIdeal 2 := by
    have : f x ∈ Representation.primeIdeal 2 • (⊤ : Submodule ℤ ℤ) := hmap_le hx_map
    simpa [f, Ideal.smul_top_eq_map] using this
  have hzero : B x y ≡ 0 [ZMOD 2] := by
    exact
      (by simpa [Representation.primeIdeal, Ideal.mem_span_singleton] using hxy_mem :
        (2 : ℤ) ∣ B x y).modEq_zero_int
  rw [even_iff_two_dvd]
  exact Int.modEq_zero_iff_dvd.mp (hmod.trans hzero)

/-- Helper for Exercise 15-15.2-6: a `G`-invariant bilinear form sends characteristic vectors to
characteristic vectors under the group action. -/
theorem isCharacteristicModTwo_map_of_invariant
    (ρ : Representation ℤ G E) (B : BilinForm ℤ E) (hB_invariant : B.IsInvariantUnder ρ)
    {x : E} (hx : B.IsCharacteristicModTwo x) (g : G) :
    B.IsCharacteristicModTwo (ρ g x) := by
  intro y
  have hchar : B (ρ g⁻¹ y) (ρ g⁻¹ y) ≡ B x (ρ g⁻¹ y) [ZMOD 2] := hx (ρ g⁻¹ y)
  have hB_pointwise := (LinearMap.BilinForm.isInvariantUnder_iff B ρ).1 hB_invariant
  have hdiag : B (ρ g⁻¹ y) (ρ g⁻¹ y) = B y y := by
    simpa [map_mul] using (hB_pointwise g⁻¹ y y)
  have hpair : B x (ρ g⁻¹ y) = B (ρ g x) y := by
    simpa [map_mul] using (hB_pointwise g x (ρ g⁻¹ y)).symm
  rw [← hdiag, ← hpair]
  exact hchar

/-- Helper for Exercise 15-15.2-6: two characteristic vectors differ by a vector whose pairing
with every lattice vector is even. -/
theorem sub_characteristic_vectors_pairing_even
    (B : BilinForm ℤ E) {x x' : E}
    (hx : B.IsCharacteristicModTwo x) (hx' : B.IsCharacteristicModTwo x') :
    ∀ y : E, B (x - x') y ≡ 0 [ZMOD 2] := by
  intro y
  have hxmod : B y y ≡ B x y [ZMOD 2] := hx y
  have hx'mod : B y y ≡ B x' y [ZMOD 2] := hx' y
  have hpair : B x y ≡ B x' y [ZMOD 2] := hxmod.symm.trans hx'mod
  have hsub : B (x - x') y = B x y - B x' y := by
    simp
  rw [hsub]
  have hzero : B x y - B x' y ≡ B x' y - B x' y [ZMOD 2] := hpair.sub (Int.ModEq.refl _)
  simpa using hzero

/-- Helper for Exercise 15-15.2-6: in any irreducible nontrivial representation over a field, a
fixed vector must vanish. -/
theorem eq_zero_of_fixed_of_irreducible_not_isTrivial
    {k : Type w} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (σ : Representation k G V) [σ.IsIrreducible]
    (hσ_nontrivial : ¬ Representation.IsTrivial σ)
    (ξ : V) (hξ : ∀ g : G, σ g ξ = ξ) :
    ξ = 0 := by
  by_contra hξ_ne
  let L : Submodule k V := k ∙ ξ
  let U : Subrepresentation σ :=
    { toSubmodule := L
      apply_mem_toSubmodule g := by
        intro x hx
        have hx' : x ∈ k ∙ ξ := by simpa [L] using hx
        rcases Submodule.mem_span_singleton.mp hx' with ⟨a, rfl⟩
        simpa [map_smulₛₗ, hξ g] using
          (Submodule.smul_mem (k ∙ ξ) a (Submodule.mem_span_singleton_self ξ) :
            a • ξ ∈ k ∙ ξ) }
  have hξ_mem : ξ ∈ U.toSubmodule := by
    simpa [U, L] using (Submodule.mem_span_singleton_self ξ : ξ ∈ k ∙ ξ)
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    have hξ_bot : ξ ∈ (⊥ : Subrepresentation σ).toSubmodule := by
      simpa [hU] using hξ_mem
    exact hξ_ne <| by simpa using hξ_bot
  have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
  have htriv : Representation.IsTrivial σ := by
    refine ⟨fun g ↦ ?_⟩
    ext x
    have hxU : x ∈ U.toSubmodule := by
      rw [hU_top]
      exact Submodule.mem_top
    have hx_fixed : σ g x = x := by
      have hxL : x ∈ L := by
        simpa [U] using hxU
      have hx' : x ∈ k ∙ ξ := by simpa [L] using hxL
      rcases Submodule.mem_span_singleton.mp hx' with ⟨a, rfl⟩
      simp [hξ g]
    exact hx_fixed
  exact hσ_nontrivial htriv

theorem fixed_class_eq_zero_of_irreducible_nontrivial_prime_reduction
    (ρ : Representation ℤ G E)
    (hρ₂ : ρ.HasIrreduciblePrimeReduction 2)
    (hρ₂_nontrivial : ρ.HasNontrivialPrimeReduction 2)
    (ξ : (ρ.primeStableLattice 2).reduction)
    (hξ : ∀ g : G, (ρ.primeStableLattice 2).reductionRepresentation g ξ = ξ) :
    ξ = 0 := by
  let ρ₂ := (ρ.primeStableLattice 2).reductionRepresentation
  letI : ρ₂.IsIrreducible := hρ₂
  simpa [ρ₂] using
    eq_zero_of_fixed_of_irreducible_not_isTrivial ρ₂ hρ₂_nontrivial ξ hξ

end IntegralLatticeAmbient

end ThompsonExercise
