import LinearRepresentations_Serre_1977.Serre.Chap10.Exercise_10_10_5_5.SubgroupInductionBridge

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

/-- Helper for Exercise 10-10.5-5: every generator of `R₀'(G)` vanishes at the identity. -/
theorem elementaryLinearCharacterAugmentationSpan_generator_apply_one_eq_zero
    (E : Subgroup G) (α : E →* ℂˣ) :
    ((Subgroup.characterRingInduction E (α.toCharacterRing - 1) : R(G)) : G → ℂ) 1 = 0 := by
  -- At the identity every induced summand samples the subgroup value at `1`, and the character
  -- difference `α - 1` vanishes there.
  rw [Subgroup.characterRingInduction_apply,
    Subgroup.inducedClassFunction_one_eq_index_mul_value]
  simp [MonoidHom.toCharacterRing_apply]

/-- Helper for Exercise 10-10.5-5: every element of `R₀'(G)` vanishes at the identity. -/
theorem apply_one_eq_zero_of_mem_elementaryLinearCharacterAugmentationSpan
    {χ : R(G)} (hχ : χ ∈ R₀'(G)) :
    ((χ : G → ℂ) 1) = 0 := by
  -- Package evaluation at `1` as a linear map and show that every generator of `R₀'(G)` lies in
  -- its kernel.
  let evalAtOne : R(G) →ₗ[ℤ] ℂ :=
    { toFun := fun ψ ↦ (ψ : G → ℂ) 1
      map_add' := by
        intro ψ η
        simp
      map_smul' := by
        intro n ψ
        simp }
  have hker : R₀'(G) ≤ LinearMap.ker evalAtOne := by
    change elementaryLinearCharacterAugmentationSpan G ≤ LinearMap.ker evalAtOne
    unfold elementaryLinearCharacterAugmentationSpan
    refine Submodule.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with ⟨E, -, α, rfl⟩
    change evalAtOne (Subgroup.characterRingInduction E (α.toCharacterRing - 1)) = 0
    simpa [evalAtOne] using
      elementaryLinearCharacterAugmentationSpan_generator_apply_one_eq_zero E α
  exact show evalAtOne χ = 0 from hker hχ

/-- Helper for Exercise 10-10.5-5: a finite sum of honest characters is again the character of an
honest finite-dimensional representation. -/
private theorem exists_fdRep_with_character_eq_sum
    {ι : Type*} (s : Finset ι) (π : ι → FDRep ℂ G) :
    ∃ τ : FDRep ℂ G, τ.character = s.sum fun i ↦ (π i).character := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨FDRep.of (Representation.trivial ℂ G (Fin 0 → ℂ)), ?_⟩
      -- The zero-dimensional trivial representation contributes the zero character.
      ext g
      simp [FDRep.character, Representation.trivial]
  | insert i s hi ih =>
      rcases ih with ⟨τ, hτ⟩
      refine ⟨FDRep.of (Representation.prod (π i).ρ τ.ρ), ?_⟩
      -- Add one summand by identifying the product character with the pointwise sum.
      calc
        (FDRep.of (Representation.prod (π i).ρ τ.ρ)).character =
            (Representation.prod (π i).ρ τ.ρ).character := rfl
        _ = Representation.character (π i).ρ + Representation.character τ.ρ := by
            exact Representation.char_prod (π i).ρ τ.ρ
        _ = (π i).character + τ.character := rfl
        _ = (π i).character + s.sum (fun j ↦ (π j).character) := by
            rw [hτ]
        _ = (insert i s).sum (fun j ↦ (π j).character) := by
            rw [Finset.sum_insert hi]

/-- Helper for Exercise 10-10.5-5: a finite nonnegative integral combination of honest
characters is again the character of an honest finite-dimensional representation. -/
private theorem exists_fdRep_with_character_eq_repr_sum
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G) (c : ι → ℤ) (hc : ∀ i, 0 ≤ c i) :
    ∃ τ : FDRep ℂ G, τ.character = ∑ i, c i • (π i).character := by
  let n : ι → ℕ := fun i ↦ Int.toNat (c i)
  let π' : (Σ i, Fin (n i)) → FDRep ℂ G := fun j ↦ π j.1
  obtain ⟨τ, hτ⟩ :=
    exists_fdRep_with_character_eq_sum (G := G) (s := Finset.univ) π'
  refine ⟨τ, ?_⟩
  -- Replicate the `i`th summand exactly `c i` times and then collapse the sigma-indexed sum.
  calc
    τ.character = ∑ j : Σ i, Fin (n i), (π' j).character := hτ
    _ = ∑ i, ∑ _ : Fin (n i), (π i).character := by
          simpa [π'] using
            (Fintype.sum_sigma (fun j : Σ i, Fin (n i) ↦ (π' j).character))
    _ = ∑ i, n i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [n]
    _ = ∑ i, c i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [show c i = Int.ofNat (n i) by
            simpa [n] using (Int.toNat_of_nonneg (hc i)).symm]
          simp

/-- Helper for Exercise 10-10.5-5: every virtual character of `G` is the difference of two honest
finite-dimensional characters. -/
lemma virtual_character_eq_character_difference_global
    (χ : R(G)) :
    ∃ Vpos Vneg : FDRep ℂ G,
      (χ : G → ℂ) = Vpos.character - Vneg.character := by
  classical
  let χtop : R((⊤ : Subgroup G)) :=
    ⟨(fun h : (⊤ : Subgroup G) ↦ (χ : G → ℂ) h),
      restrict_mem_characterRing_local (G := G) (H := ⊤) χ⟩
  obtain ⟨Vpos, Vneg, hχtop⟩ :=
    Representation.virtual_character_eq_character_difference (H := (⊤ : Subgroup G)) χtop
  let Wpos : FDRep ℂ G := FDRep.of (Vpos.ρ.comp Subgroup.topEquiv.symm.toMonoidHom)
  let Wneg : FDRep ℂ G := FDRep.of (Vneg.ρ.comp Subgroup.topEquiv.symm.toMonoidHom)
  refine ⟨Wpos, Wneg, ?_⟩
  -- Evaluate the top-subgroup character identity on the image of `g : G` in `⊤`.
  ext g
  have htop_eval := congrFun hχtop ⟨g, by simp⟩
  simpa [χtop, Wpos, Wneg]
    using htop_eval

end

end Representation
