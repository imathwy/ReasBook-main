import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_3_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Serre.Chap12.Lemma_12_12_1_4
import LinearRepresentations_Serre_1977.Serre.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap13.Corollary_13_13_1_2
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.SubrepresentationInvariant

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

namespace Representation

open scoped Representation

namespace Subgroup

/-- The finite family of cyclic subgroups of a finite group. -/
abbrev cyclicSubgroupsFamily_c1318 (G : Type*) [Group G] [Finite G] : Finset (Subgroup G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  exact Finset.univ.filter fun H : Subgroup G ↦ IsCyclic H

@[simp] theorem mem_cyclicSubgroupsFamily_c1318 {G : Type*} [Group G] [Finite G] {H : Subgroup G} :
    H ∈ cyclicSubgroupsFamily_c1318 G ↔ IsCyclic H := by
  classical
  simp [cyclicSubgroupsFamily_c1318]

end Subgroup

section

variable {G : Type} [Group G] [Finite G]

local instance instFintypeG_Corollary_13_13_1_8 : Fintype G := Fintype.ofFinite G
local instance anonInstP_Corollary_13_13_1_8_1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H
local instance anonInst_Corollary_13_13_1_8_1 : NeZero (Nat.card G : ℚ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

variable {V : Type v} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
variable {V' : Type w} [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V']

/- The subgroup permutation characters are written `ℓ_H^G` on the source-facing theorem surface. -/

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: the tensor-level map used in Frobenius reciprocity is
compatible with the defining coinvariant relation for induction. -/
private theorem frobenius_tensor_relation
    {H : Type*} [Group H] [Finite H]
    {K : Type*} [Field K]
    {U : Type*} [Group U] [Finite U]
    {X : Type*} [AddCommGroup X] [Module K X]
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    (α : H →* U) (E : Representation K U X) (θ : Representation K H Y)
    (f : θ.IntertwiningMap (E.comp α)) (g : H) (x : U) (y : Y) :
    (((((Finsupp.lift (Y →ₗ[K] X) K U) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
          (Representation.leftRegular K U) (α g)).compl₂
        (θ g) ∘ₗ Finsupp.lsingle x)
      (1 : K))
    y =
    ((((Finsupp.lift (Y →ₗ[K] X) K U) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
        Finsupp.lsingle x)
      (1 : K)) y := by
  let _ : Fintype H := Fintype.ofFinite H
  let _ : Fintype U := Fintype.ofFinite U
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, smul_eq_mul,
    Finsupp.lift_apply, map_mul, mul_inv_rev, zero_smul, Finsupp.sum_single_index, one_smul,
    IntertwiningMap.toLinearMap_apply, Module.End.mul_apply]
  have hg := LinearMap.congr_fun (f.2 g) y
  simp only [LinearMap.comp_apply] at hg
  change (E x⁻¹) ((E (α g)⁻¹) (f.toLinearMap ((θ g) y))) = (E x⁻¹) (f.toLinearMap y)
  rw [hg]
  simp

/-- Helper for Corollary 13-13.1-8: Frobenius reciprocity gives a linear equivalence between
intertwining maps without passing through the `Rep` wrapper. -/
private def frobenius_intertwining_equiv
    {H : Type*} [Group H] [Finite H]
    {K : Type*} [Field K]
    {U : Type*} [Group U] [Finite U]
    {X : Type*} [AddCommGroup X] [Module K X]
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    (α : H →* U) (E : Representation K U X) (θ : Representation K H Y) :
    ((ind α θ).IntertwiningMap E) ≃ₗ[K] θ.IntertwiningMap (E.comp α) where
  toFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ IndV.mk α θ 1
      isIntertwining' := fun g ↦ by
        ext x
        have hf := LinearMap.congr_fun (f.2 (α g)) (IndV.mk α θ 1 x)
        simpa [← Representation.Coinvariants.mk_inv_tmul] using hf }
  invFun f :=
    { toLinearMap := Representation.Coinvariants.lift _
        (TensorProduct.lift <| Finsupp.lift _ _ _ fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap)
        (fun g ↦ by
          simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
            TensorProduct.lift_comp_map]
          congr 1
          ext x y
          exact frobenius_tensor_relation α E θ f g x y)
      isIntertwining' := fun g ↦ by
        ext x
        simp }
  left_inv f := by
    ext h a
    have hf := LinearMap.congr_fun (f.2 h⁻¹) (IndV.mk α θ 1 a)
    simpa using hf.symm
  right_inv f := by
    ext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper for Corollary 13-13.1-8: Frobenius reciprocity identifies the character pairing of a
restricted representation with the pairing against the induced character. -/
private theorem groupFunctionPairing_character_comp_eq_character_ind
    {H : Type*} [Group H] [Finite H]
    {K : Type*} [Field K] [Invertible (Nat.card H : K)] [Invertible (Nat.card G : K)]
    {X : Type*} [AddCommGroup X] [Module K X]
    {Y : Type*} [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K X] [FiniteDimensional K Y]
    (α : H →* G) (E : Representation K G X)
    (θ : Representation K H Y) :
    ⟪θ.character, Representation.character (E.comp α)⟫ =
      ⟪(ind α θ).character, E.character⟫ := by
  let _ : Fintype H := Fintype.ofFinite H
  let _ : FiniteDimensional K (G →₀ K) := by
    infer_instance
  let _ : FiniteDimensional K (TensorProduct K (G →₀ K) Y) := by
    infer_instance
  let _ : FiniteDimensional K (IndV α θ) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  calc
    ⟪θ.character, Representation.character (E.comp α)⟫ =
        Module.finrank K (θ.IntertwiningMap (E.comp α)) := by
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K θ (E.comp α))
    _ = Module.finrank K ((ind α θ).IntertwiningMap E) := by
          have hdim : Module.finrank K (θ.IntertwiningMap (E.comp α)) =
              Module.finrank K ((ind α θ).IntertwiningMap E) :=
            (frobenius_intertwining_equiv α E θ).symm.finrank_eq
          simp [hdim]
    _ = ⟪(ind α θ).character, E.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K (ind α θ) E)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: transporting a rational virtual character through the bottom
field equivalence lands in the bottom-field character ring. -/
private theorem bot_symm_mem_characterRingOverField_of_mem
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    (fun s ↦ (IntermediateField.botEquiv ℚ K).symm (χ s)) ∈
      R[↥(⊥ : IntermediateField ℚ K)](G) := by
  -- Transport each honest character generator through scalar extension and close under the adjoin
  -- operations defining the virtual-character ring.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · intro ψ hψ
    rcases hψ with ⟨ρ, _, _, rfl⟩
    let ρL := Rep.of (Representation.scalarExtension (k := ↥(⊥ : IntermediateField ℚ K)) ρ.ρ)
    have hρL : ρL.ρ.character ∈ R[↥(⊥ : IntermediateField ℚ K)](G) := by
      exact Representation.rep_character_mem_characterRingOverField
        (K := ↥(⊥ : IntermediateField ℚ K)) (G := G) ρL
    have hchar :
        ρL.ρ.character =
          fun s ↦ (IntermediateField.botEquiv ℚ K).symm (ρ.ρ.character s) := by
      -- Scalar extension applies the coefficient map pointwise to characters.
      ext s
      have hs :
          ρL.ρ.character s =
            (IntermediateField.botEquiv ℚ K).symm (ρ.ρ.character s) := by
        change
            (LinearMap.trace ↥(⊥ : IntermediateField ℚ K)
              (TensorProduct ℚ ↥(⊥ : IntermediateField ℚ K) ↑ρ))
              ((Representation.scalarExtension (k := ↥(⊥ : IntermediateField ℚ K)) ρ.ρ) s) =
          algebraMap ℚ ↥(⊥ : IntermediateField ℚ K)
            ((LinearMap.trace ℚ ↑ρ) (ρ.ρ s))
        exact LinearMap.trace_baseChange (ρ.ρ s) ↥(⊥ : IntermediateField ℚ K)
      exact congrArg (fun x : ↥(⊥ : IntermediateField ℚ K) => (x : K)) hs
    simpa [ρL, hchar] using hρL
  · intro n
    -- Integer-valued constant functions are preserved by the bottom-field embedding.
    have hconst :
        (fun s : G ↦ (IntermediateField.botEquiv ℚ K).symm
          ((algebraMap ℤ (G → ℚ)) n s)) =
        algebraMap ℤ (G → ↥(⊥ : IntermediateField ℚ K)) n := by
      ext s
      simp [Pi.algebraMap_apply]
    rw [hconst]
    exact (R[↥(⊥ : IntermediateField ℚ K)](G)).algebraMap_mem n
  · intro f g _ _ hf hg
    -- The character ring is closed under addition.
    simpa [Pi.add_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).add_mem hf hg
  · intro f g _ _ hf hg
    -- The character ring is closed under multiplication.
    simpa [Pi.mul_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).mul_mem hf hg

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: transporting a bottom-field valued virtual character through
`botEquiv` lands in the literal rational character ring. -/
private theorem bot_equiv_mem_characterRingOverField_of_mem
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    {χ : G → ↥(⊥ : IntermediateField ℚ K)}
    (hχ : χ ∈ R[↥(⊥ : IntermediateField ℚ K)](G)) :
    (fun s ↦ IntermediateField.botEquiv ℚ K (χ s)) ∈ R[ℚ](G) := by
  let χQ : G → ℚ := fun s ↦ IntermediateField.botEquiv ℚ K (χ s)
  have hχQ_over :
      χQ ∈ overlineCharacterRingInExtension
        (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) := by
    -- The coefficientwise image of `χQ` in the bottom field is exactly the original `χ`.
    rw [mem_overlineCharacterRingInExtension_iff
      (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) χQ]
    have himage :
        ((IsScalarTower.toAlgHom ℤ ℚ ↥(⊥ : IntermediateField ℚ K)).compLeft G) χQ = χ := by
      ext s
      have hs : algebraMap ℚ K (χQ s) = (χ s : K) := by
        change algebraMap ℚ K (IntermediateField.botEquiv ℚ K (χ s)) =
          algebraMap ↥(⊥ : IntermediateField ℚ K) K (χ s)
        rw [IsScalarTower.algebraMap_apply ℚ ↥(⊥ : IntermediateField ℚ K) K
          (IntermediateField.botEquiv ℚ K (χ s))]
        rw [show algebraMap ℚ ↥(⊥ : IntermediateField ℚ K)
          (IntermediateField.botEquiv ℚ K (χ s)) = χ s by
          exact (IntermediateField.botEquiv ℚ K).symm_apply_apply (χ s)]
      simpa [χQ] using hs
    convert hχ using 1
  have hsmul :
      ((Module.finrank ℚ ↥(⊥ : IntermediateField ℚ K) : ℤ) • χQ) ∈ R[ℚ](G) :=
    Representation.extensionDegree_smul_mem_characterRingOverField
      (K := ℚ) (L := ↥(⊥ : IntermediateField ℚ K)) (G := G) ⟨χQ, hχQ_over⟩
  have hfinrank : Module.finrank ℚ ↥(⊥ : IntermediateField ℚ K) = 1 := by
    -- The bottom intermediate field is canonically isomorphic to `ℚ`.
    simpa using (IntermediateField.botEquiv ℚ K).toLinearEquiv.finrank_eq
  simpa [χQ, hfinrank] using hsmul

/-- Helper for Corollary 13-13.1-8: the source owner `ℚ ⊗ R_{↥⊥}(G)` transports to
`ℚ ⊗ R_ℚ(G)` through the pointwise bottom-field equivalence. -/
private theorem bot_equiv_mem_characterRingOverFieldScalarExtension_iff
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    (g : G → ↥(⊥ : IntermediateField ℚ K)) :
    g ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G) ↔
      (fun s ↦ IntermediateField.botEquiv ℚ K (g s)) ∈ ℚ⊗R[ℚ](G) := by
  let e : (G → ↥(⊥ : IntermediateField ℚ K)) →ₗ[ℚ] G → ℚ :=
    ((IntermediateField.botEquiv ℚ K).toLinearEquiv.compLeft G)
  have hmap :
      Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) = ℚ⊗R[ℚ](G) := by
    -- Route correction: transport the source owner before comparing the two coefficient fields.
    change Submodule.map e
        (Submodule.span ℚ
          (((R[↥(⊥ : IntermediateField ℚ K)](G)).toSubmodule :
            Submodule ℤ (G → ↥(⊥ : IntermediateField ℚ K))) :
              Set (G → ↥(⊥ : IntermediateField ℚ K)))) =
      Submodule.span ℚ
        (((R[ℚ](G)).toSubmodule : Submodule ℤ (G → ℚ)) : Set (G → ℚ))
    rw [Submodule.map_span]
    congr 1
    ext χ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      exact bot_equiv_mem_characterRingOverField_of_mem (G := G) (K := K)
        (by simpa using hψ)
    · intro hχ
      refine ⟨fun s ↦ (IntermediateField.botEquiv ℚ K).symm (χ s), ?_, ?_⟩
      · exact bot_symm_mem_characterRingOverField_of_mem (G := G) (K := K) hχ
      · ext s
        simp [e]
  constructor
  · intro hg
    have hem : e g ∈ Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) :=
      Submodule.mem_map.mpr ⟨g, hg, rfl⟩
    rw [hmap] at hem
    simpa [e] using hem
  · intro hg
    have hem : e g ∈ Submodule.map e (ℚ⊗R[↥(⊥ : IntermediateField ℚ K)](G)) := by
      rw [hmap]
      simpa [e] using hg
    rcases Submodule.mem_map.mp hem with ⟨g', hg', hg'eq⟩
    have hgg' : g' = g := by
      ext s
      exact congrArg (fun x : ↥(⊥ : IntermediateField ℚ K) => (x : K)) <|
        (IntermediateField.botEquiv ℚ K).injective (congrFun hg'eq s)
    simpa [hgg'] using hg'

/-- Helper for Corollary 13-13.1-8: when the structure map `ℚ → K` is surjective (as it is for the
bottom field `↥⊥`), spanning `R[K](G)` over `K` and over `ℚ` produces the same submodule, so
membership in either scalar extension is the same condition. -/
private theorem mem_characterRingOverFieldAlgebraScalarExtension_self_iff_rat
    {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (hsurj : Function.Surjective (algebraMap ℚ K)) (f : G → K) :
    f ∈ K⊗R[K](G) ↔ f ∈ ℚ⊗R[K](G) := by
  unfold Representation.characterRingOverFieldAlgebraScalarExtension
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        obtain ⟨q, rfl⟩ := hsurj a
        rw [algebraMap_smul]
        exact Submodule.smul_mem _ q hx
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        rw [← algebraMap_smul K a x]
        exact Submodule.smul_mem _ _ hx

/-- Helper for Corollary 13-13.1-8: the structure map `ℚ → ↥⊥` into the bottom intermediate field
is surjective. -/
private theorem algebraMap_rat_bot_surjective
    {K : Type*} [Field K] [CharZero K] :
    Function.Surjective (algebraMap ℚ ↥(⊥ : IntermediateField ℚ K)) := by
  intro x
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
  exact ⟨q, by ext; exact hq⟩

/-- Helper for Corollary 13-13.1-8: a rational-valued class function belongs to Serre's rational
character ring exactly when it is invariant under all `Γ_ℚ(G)` power maps. -/
private theorem rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant
    (f : G → ℚ) (hf : _root_.IsClassFunction f) :
    f ∈ ℚ⊗R[ℚ](G) ↔
      ∀ s (t : Γ_ℚ(G)), f s = f (s ^ t) := by
  let Lexp := CyclotomicField (Monoid.exponent G) ℚ
  letI : Field Lexp := inferInstance
  letI : CharZero Lexp := inferInstance
  letI : NumberField Lexp := inferInstance
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  let fBot : G → ↥(⊥ : IntermediateField ℚ Lexp) :=
    fun s ↦ (IntermediateField.botEquiv ℚ Lexp).symm (f s)
  have hfBotClass : _root_.IsClassFunction fBot := by
    -- Composing with the bottom-field equivalence preserves the class-function condition.
    exact hf.comp ((IntermediateField.botEquiv ℚ Lexp).symm : ℚ → ↥(⊥ : IntermediateField ℚ Lexp))
  let φBot : classFunctionSubmodule (⊥ : IntermediateField ℚ Lexp) G :=
    ⟨fBot, (mem_classFunctionSubmodule_iff _ _).2 hfBotClass⟩
  have hGammaBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) = ⊤ := by
    -- Over the bottom field `ℚ`, the cyclotomic Galois subgroup is the full unit group.
    unfold Representation.gammaSubgroup
    letI : IsGalois ℚ Lexp := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ Lexp
    have hfixingSubgroupBot : (⊥ : IntermediateField ℚ Lexp).fixingSubgroup = ⊤ :=
      IsGaloisGroup.fixingSubgroup_bot (G := Gal(Lexp / ℚ)) (K := ℚ) (L := Lexp)
    rw [hfixingSubgroupBot]
    simp
  have howner :
      fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := by
    -- Apply the Chapter 12 invariant criterion over the bottom intermediate field; the owner gives
    -- membership in the `↥⊥`-span, which coincides with the `ℚ`-span because `ℚ → ↥⊥` is onto.
    rw [← mem_characterRingOverFieldAlgebraScalarExtension_self_iff_rat
      (G := G) (K := ↥(⊥ : IntermediateField ℚ Lexp)) algebraMap_rat_bot_surjective fBot]
    simpa [φBot] using
      (Representation.classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        (G := G) (L := Lexp) (K := (⊥ : IntermediateField ℚ Lexp))
        φBot)
  calc
    f ∈ ℚ⊗R[ℚ](G) ↔
        fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) := by
          simpa [fBot] using
            (bot_equiv_mem_characterRingOverFieldScalarExtension_iff
              (G := G) (K := Lexp) fBot).symm
    _ ↔ ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := howner
    _ ↔ ∀ s (t : Γ_ℚ(G)), f s = f (s ^ t) := by
      constructor
      · intro h s t
        let tBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) := ⟨t, by simp [hGammaBot]⟩
        simpa [fBot, tBot, pow_subgroup_eq_pow_nat, pow_unit_eq_pow_nat] using
          congrArg (IntermediateField.botEquiv ℚ Lexp) (h s tBot)
      · intro h s t
        apply (IntermediateField.botEquiv ℚ Lexp).injective
        simpa [fBot, pow_subgroup_eq_pow_nat, pow_unit_eq_pow_nat] using h s (t : Γ_ℚ(G))

/-- Helper for Corollary 13-13.1-8: a rational scalar-extension character is constant on
elements generating the same cyclic subgroup. -/
private theorem eq_of_zpowers_eq_of_mem_rational_character_ring
    {θ : ℚ ⊗R[ℚ](G)} {x y : G}
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    (θ : G → ℚ) x = (θ : G → ℚ) y := by
  -- First show that every rational scalar-extension character is a class function.
  have hθClass : _root_.IsClassFunction (θ : G → ℚ) := by
    have hclass :
        ∀ {f : G → ℚ}, f ∈ ℚ⊗R[ℚ](G) → _root_.IsClassFunction f := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          exact Representation.isClassFunction_of_mem_characterRingOverField ψ
            (by simpa using hψ)
      | zero =>
          simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : ℚ)))
      | add f g _ _ hf hg =>
          letI : _root_.IsClassFunction f := hf
          letI : _root_.IsClassFunction g := hg
          simpa using (inferInstance : _root_.IsClassFunction (f + g))
      | smul a f _ hf =>
          letI : _root_.IsClassFunction f := hf
          simpa using (inferInstance : _root_.IsClassFunction (a • f))
    exact hclass θ.property
  -- Then the Chapter 13 rationality criterion upgrades this to `Γ_ℚ`-power invariance.
  have hθpow :
      ∀ s (t : Γ_ℚ(G)), (θ : G → ℚ) s = (θ : G → ℚ) (s ^ t) :=
    (rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant
      (θ : G → ℚ) hθClass).1 θ.property
  -- Equality of cyclic subgroups gives the required `Γ_ℚ`-conjugacy bridge.
  have hzpowConj :
      (Subgroup.zpowers x).IsConj (Subgroup.zpowers y) := by
    simpa [hxy] using Subgroup.IsConj.refl (Subgroup.zpowers x)
  rcases (gammaRat_conjugate_iff_conjugate_zpowers x y).2 hzpowConj with ⟨t, hxt⟩
  calc
    (θ : G → ℚ) x = (θ : G → ℚ) (y ^ t) := by
      exact hθClass.eq_of_isConj hxt
    _ = (θ : G → ℚ) y := by
      symm
      exact hθpow y t

/-- Helper for Corollary 13-13.1-8: pairing the restriction of a rational virtual character with
the trivial character gives the normalized subgroup sum. -/
private theorem pairing_restrict_trivialCharacter_eq_average
    (θ : ℚ ⊗R[ℚ](G)) (H : Subgroup.cyclicSubgroupsFamily_c1318 G) :
    ⟪(fun h : H.1 ↦ (θ : G → ℚ) h), (1 : H.1 → ℚ)⟫ =
      (Nat.card H.1 : ℚ)⁻¹ * ∑ s : H.1, (θ : G → ℚ) s := by
  rw [groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp

/-- Helper for Corollary 13-13.1-8: restriction preserves Serre's rational scalar-extension
character ring. -/
private theorem restrict_mem_characterRingOverFieldScalarExtension
    {A : Type} [Group A] [Finite A] (J : Subgroup A) {φ : A → ℚ}
    (hφ : φ ∈ ℚ ⊗R[ℚ](A)) :
    (fun j : J ↦ φ j) ∈ ℚ ⊗R[ℚ](J) := by
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype J := Fintype.ofFinite J
  induction hφ using Submodule.span_induction with
  | mem χ hχ =>
      have hχ_mem : χ ∈ R[ℚ](A) := by
        simpa using hχ
      have hχ_restrict : (fun j : J ↦ χ j) ∈ R[ℚ](J) := by
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ_mem
        · intro ψ hψ
          rcases hψ with ⟨ρ, hρfd, -, rfl⟩
          change (Rep.res J.subtype ρ).ρ.character ∈ R[ℚ](J)
          let _ : FiniteDimensional ℚ ρ := hρfd
          let _ : FiniteDimensional ℚ (Rep.res J.subtype ρ) := by
            infer_instance
          exact rep_character_mem_characterRingOverField (Rep.res J.subtype ρ)
        · intro n
          exact (R[ℚ](J)).algebraMap_mem n
        · intro f g _ _ hf hg
          simpa using (R[ℚ](J)).add_mem hf hg
        · intro f g _ _ hf hg
          simpa using (R[ℚ](J)).mul_mem hf hg
      exact mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField hχ_restrict
  | zero =>
      exact zero_mem (ℚ⊗R[ℚ](J))
  | add f g _ _ hf hg =>
      simpa using (ℚ⊗R[ℚ](J)).add_mem hf hg
  | smul a f _ hf =>
      simpa using (ℚ⊗R[ℚ](J)).smul_mem a hf

/-- Helper for Corollary 13-13.1-8: summing a restricted function over an internal subgroup
agrees with summing the ambient function over the corresponding mapped subgroup. -/
private theorem subgroup_sum_restrict_eq_sum_map_subtype
    (C : Subgroup G) (J : Subgroup C) (f : G → ℚ) :
    (∑ s : J, f s) = ∑ t : J.map C.subtype, f t := by
  classical
  simpa using
    (Fintype.sum_equiv (J.equivMapOfInjective C.subtype C.subtype_injective)
      (fun s : J ↦ f s) (fun t : J.map C.subtype ↦ f t) (fun s ↦ rfl))

/-- Helper for Corollary 13-13.1-8: a proper subgroup of a finite group has strictly smaller
cardinality. -/
private theorem proper_subgroup_natCard_lt {A : Type} [Group A] [Finite A] (J : Subgroup A)
    (hJ : J ≠ ⊤) : Nat.card J < Nat.card A := by
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype J := Fintype.ofFinite J
  have hex : ∃ a : A, a ∉ J := by
    by_cases hall : ∀ a : A, a ∈ J
    · exact False.elim (hJ (by
        ext a
        simp [hall a]))
    · exact not_forall.mp hall
  rcases hex with ⟨a, ha⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using (Fintype.card_subtype_lt (p := fun b : A ↦ b ∈ J) ha)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: every element of `R_ℚ(G)` is an integral linear combination
of honest finite-dimensional rational characters. -/
private theorem mem_span_rep_characters_of_mem_characterRingOverField
    {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    χ ∈ Submodule.span ℤ
      { ψ : G → ℚ |
          ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℚ U) (_ : FiniteDimensional ℚ U)
            (ρ : Representation ℚ G U), ψ = ρ.character } := by
  let honestCharacters : Set (G → ℚ) :=
    { ψ : G → ℚ |
        ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℚ U) (_ : FiniteDimensional ℚ U)
          (ρ : Representation ℚ G U), ψ = ρ.character }
  let T : Submodule ℤ (G → ℚ) := Submodule.span ℤ honestCharacters
  have hmul_T :
      ∀ {f g : G → ℚ}, f ∈ T → g ∈ T → f * g ∈ T := by
    intro f g hf hg
    have hleft : ∀ ψ : G → ℚ, ψ ∈ T → f * ψ ∈ T := by
      induction hf using Submodule.span_induction with
      | mem φ hφ =>
          rcases hφ with ⟨U, _, _, _, ρ, rfl⟩
          intro ψ hψ
          induction hψ using Submodule.span_induction with
          | mem ψ hψ =>
              rcases hψ with ⟨W, _, _, _, σ, rfl⟩
              let τ : Representation ℚ G (TensorProduct ℚ U W) := Representation.tprod ρ σ
              have hchar :
                  ρ.character * σ.character = τ.character := by
                change ρ.character * σ.character = (Representation.tprod ρ σ).character
                exact (Representation.char_tensor ρ σ).symm
              rw [hchar]
              exact Submodule.subset_span ⟨TensorProduct ℚ U W, inferInstance, inferInstance,
                inferInstance, τ, rfl⟩
          | zero =>
              simp
          | add ψ ξ _ _ hψ hξ =>
              simpa [mul_add] using Submodule.add_mem T hψ hξ
          | smul n ψ _ hψ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem T n hψ
      | zero =>
          intro ψ hψ
          simp
      | add φ ψ _ _ hφ hψ =>
          intro ξ hξ
          simpa [add_mul] using Submodule.add_mem T (hφ ξ hξ) (hψ ξ hξ)
      | smul n φ _ hφ =>
          intro ψ hψ
          simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
            Submodule.smul_mem T n (hφ ψ hψ)
    exact hleft g hg
  refine
    Algebra.adjoin_induction
      (p := fun f _ ↦ f ∈ Submodule.span ℤ honestCharacters)
      ?_ ?_ ?_ ?_ hχ
  · rintro ψ ⟨ρ, hρfd, -, rfl⟩
    exact Submodule.subset_span ⟨ρ, inferInstance, inferInstance, hρfd, ρ.ρ, rfl⟩
  · intro n
    let τ : Representation ℚ G ℚ := Representation.trivial ℚ G ℚ
    have htriv : τ.character ∈ T :=
      Submodule.subset_span ⟨ℚ, inferInstance, inferInstance, inferInstance, τ, rfl⟩
    have hscalar : algebraMap ℤ (G → ℚ) n = n • τ.character := by
      ext g
      simp [τ, Representation.character, Representation.trivial]
    rw [hscalar]
    simpa [T] using (Submodule.smul_mem T n htriv)
  · intro f g _ _ hf hg
    simpa [T] using (Submodule.add_mem T hf hg)
  · intro f g _ _ hf hg
    simpa [T] using (hmul_T hf hg)

/-- Helper for Corollary 13-13.1-8: pairing a cyclic subgroup permutation character with a
rational scalar-extension character is the restricted trivial pairing. -/
private theorem groupFunctionPairing_subgroupPermutationCharacter_eq_restrict_trivial_pairing
    (θ : ℚ ⊗R[ℚ](G)) (H : Subgroup.cyclicSubgroupsFamily_c1318 G) :
    ⟪(θ : G → ℚ), (ℓ_{H.1}^G : G → ℚ)⟫ =
      ⟪(fun h : H.1 ↦ (θ : G → ℚ) h), (1 : H.1 → ℚ)⟫ := by
  let repSpan : Submodule ℤ (G → ℚ) :=
    Submodule.span ℤ
      { ψ : G → ℚ |
          ∃ (U : Type) (_ : AddCommGroup U) (_ : Module ℚ U) (_ : FiniteDimensional ℚ U)
            (ρ : Representation ℚ G U), ψ = ρ.character }
  have hspan_bridge :
      ∀ {χ : G → ℚ}, χ ∈ repSpan →
        ⟪χ, (ℓ_{H.1}^G : G → ℚ)⟫ = ⟪(fun h : H.1 ↦ χ h), (1 : H.1 → ℚ)⟫ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem ψ hψ =>
        rcases hψ with ⟨U, _, _, _, ρ, rfl⟩
        let C : Subgroup G := H.1
        let τ : Representation ℚ C ℚ := Representation.trivial ℚ C ℚ
        have htriv_char : τ.character = (1 : C → ℚ) := by
          ext c
          simp [τ, Representation.character, Representation.trivial]
        have hperm :
            (ℓ_{H.1}^G : G → ℚ) = (Representation.ind C.subtype τ).character := by
          calc
            (ℓ_{H.1}^G : G → ℚ)
                = (C.classFunctionInduction (1 : C → ℚ) : G → ℚ) := by
                    rfl
            _ = (C.classFunctionInduction τ.character : G → ℚ) := by
                  rw [htriv_char]
            _ = (Representation.ind C.subtype τ).character := by
                  letI : NeZero (Nat.card C : ℚ) :=
                    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
                  simpa [Subgroup.classFunctionInduction_apply] using
                    (Subgroup.inducedClassFunction_eq_character_ind (H := C) (K := ℚ) τ)
        have hfrobenius :
            ⟪τ.character, Representation.character (ρ.comp C.subtype)⟫ =
              ⟪(Representation.ind C.subtype τ).character, ρ.character⟫ := by
          letI : Invertible (Nat.card C : ℚ) :=
            invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
          letI : Invertible (Nat.card G : ℚ) :=
            invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
          exact groupFunctionPairing_character_comp_eq_character_ind C.subtype ρ τ
        calc
          ⟪ρ.character, (ℓ_{H.1}^G : G → ℚ)⟫
              = ⟪(ℓ_{H.1}^G : G → ℚ), ρ.character⟫ := by
                  rw [groupFunctionPairing_comm]
          _ = ⟪(Representation.ind C.subtype τ).character, ρ.character⟫ := by
                rw [hperm]
          _ = ⟪τ.character, Representation.character (ρ.comp C.subtype)⟫ := by
                exact hfrobenius.symm
          _ = ⟪Representation.character (ρ.comp C.subtype), τ.character⟫ := by
                rw [groupFunctionPairing_comm]
          _ = ⟪(fun h : H.1 ↦ ρ.character h), (1 : H.1 → ℚ)⟫ := by
                rw [htriv_char]
                rfl
    | zero =>
        simp [Representation.groupFunctionPairingOverField]
    | add φ ψ _ _ hφ hψ =>
        calc
          ⟪φ + ψ, (ℓ_{H.1}^G : G → ℚ)⟫
              = ⟪φ, (ℓ_{H.1}^G : G → ℚ)⟫ + ⟪ψ, (ℓ_{H.1}^G : G → ℚ)⟫ := by
                  exact groupFunctionPairing_add_left φ ψ (ℓ_{H.1}^G : G → ℚ)
          _ = ⟪(fun h : H.1 ↦ φ h), (1 : H.1 → ℚ)⟫ +
                ⟪(fun h : H.1 ↦ ψ h), (1 : H.1 → ℚ)⟫ := by rw [hφ, hψ]
          _ = ⟪(fun h : H.1 ↦ φ h + ψ h), (1 : H.1 → ℚ)⟫ := by
                symm
                exact groupFunctionPairing_add_left (fun h : H.1 ↦ φ h) (fun h ↦ ψ h) 1
    | smul n φ _ hφ =>
        calc
          ⟪n • φ, (ℓ_{H.1}^G : G → ℚ)⟫ = (n : ℚ) * ⟪φ, (ℓ_{H.1}^G : G → ℚ)⟫ := by
            simpa [zsmul_eq_mul] using
              groupFunctionPairing_smul_left (n : ℚ) φ (ℓ_{H.1}^G : G → ℚ)
          _ = (n : ℚ) * ⟪(fun h : H.1 ↦ φ h), (1 : H.1 → ℚ)⟫ := by rw [hφ]
          _ = ⟪(fun h : H.1 ↦ (n • φ) h), (1 : H.1 → ℚ)⟫ := by
                simpa [zsmul_eq_mul] using
                  (groupFunctionPairing_smul_left
                    (n : ℚ) (fun h : H.1 ↦ φ h) (1 : H.1 → ℚ)).symm
  have hcharacter_bridge :
      ∀ {χ : G → ℚ}, χ ∈ R[ℚ](G) →
        ⟪χ, (ℓ_{H.1}^G : G → ℚ)⟫ = ⟪(fun h : H.1 ↦ χ h), (1 : H.1 → ℚ)⟫ := by
    intro χ hχ
    exact hspan_bridge (mem_span_rep_characters_of_mem_characterRingOverField hχ)
  have hscalar_bridge :
      ∀ {φ : G → ℚ}, φ ∈ ℚ ⊗R[ℚ](G) →
        ⟪φ, (ℓ_{H.1}^G : G → ℚ)⟫ = ⟪(fun h : H.1 ↦ φ h), (1 : H.1 → ℚ)⟫ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem χ hχ =>
        exact hcharacter_bridge hχ
    | zero =>
        simp [Representation.groupFunctionPairingOverField]
    | add φ ψ _ _ hφ hψ =>
        calc
          ⟪φ + ψ, (ℓ_{H.1}^G : G → ℚ)⟫
              = ⟪φ, (ℓ_{H.1}^G : G → ℚ)⟫ + ⟪ψ, (ℓ_{H.1}^G : G → ℚ)⟫ := by
                  exact groupFunctionPairing_add_left φ ψ (ℓ_{H.1}^G : G → ℚ)
          _ = ⟪(fun h : H.1 ↦ φ h), (1 : H.1 → ℚ)⟫ +
                ⟪(fun h : H.1 ↦ ψ h), (1 : H.1 → ℚ)⟫ := by rw [hφ, hψ]
          _ = ⟪(fun h : H.1 ↦ φ h + ψ h), (1 : H.1 → ℚ)⟫ := by
                symm
                exact groupFunctionPairing_add_left (fun h : H.1 ↦ φ h) (fun h ↦ ψ h) 1
    | smul a φ _ hφ =>
        calc
          ⟪a • φ, (ℓ_{H.1}^G : G → ℚ)⟫ = a * ⟪φ, (ℓ_{H.1}^G : G → ℚ)⟫ := by
            exact groupFunctionPairing_smul_left a φ (ℓ_{H.1}^G : G → ℚ)
          _ = a * ⟪(fun h : H.1 ↦ φ h), (1 : H.1 → ℚ)⟫ := by rw [hφ]
          _ = ⟪(fun h : H.1 ↦ (a • φ) h), (1 : H.1 → ℚ)⟫ := by
                simpa using
                  (groupFunctionPairing_smul_left a (fun h : H.1 ↦ φ h) (1 : H.1 → ℚ)).symm
  exact hscalar_bridge θ.property

/-- Helper for Corollary 13-13.1-8: on a finite cyclic group, vanishing subgroup sums force a
rational scalar-extension character to vanish. -/
private theorem cyclic_rat_character_eq_zero_of_zero_subgroup_sums
    {A : Type} [Group A] [Finite A] [IsCyclic A]
    (φ : ℚ ⊗R[ℚ](A))
    (hsum : ∀ J : Subgroup A, ∑ s : J, (φ : A → ℚ) s = 0) :
    φ = 0 := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (B : Type) (_ : Group B) (_ : Finite B) (_ : IsCyclic B),
      Nat.card B = n →
      ∀ ψ : ℚ ⊗R[ℚ](B),
        (∀ J : Subgroup B, ∑ s : J, (ψ : B → ℚ) s = 0) → ψ = 0
  have hstrong : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih B _ _ _ hBcard ψ hsumψ
    have hzero_nongenerator :
        ∀ b : B, Subgroup.zpowers b ≠ (⊤ : Subgroup B) → (ψ : B → ℚ) b = 0 := by
      intro b hb
      let J : Subgroup B := Subgroup.zpowers b
      have hlt : Nat.card J < n := by
        rw [← hBcard]
        exact proper_subgroup_natCard_lt J hb
      let ψJ : ℚ ⊗R[ℚ](J) :=
        ⟨fun j : J ↦ (ψ : B → ℚ) j,
          restrict_mem_characterRingOverFieldScalarExtension J ψ.property⟩
      have hsumJ : ∀ K : Subgroup J, ∑ s : K, (ψJ : J → ℚ) s = 0 := by
        intro K
        calc
          ∑ s : K, (ψJ : J → ℚ) s = ∑ t : K.map J.subtype, (ψ : B → ℚ) t := by
            exact subgroup_sum_restrict_eq_sum_map_subtype J K (ψ : B → ℚ)
          _ = 0 := hsumψ (K.map J.subtype)
      have hψJ_zero : ψJ = 0 := by
        simpa using
          ih (Nat.card J) hlt J inferInstance inferInstance inferInstance rfl ψJ hsumJ
      have hb_mem : b ∈ J := Subgroup.mem_zpowers b
      have hvalue : (ψJ : J → ℚ) ⟨b, hb_mem⟩ = 0 := by
        simp [hψJ_zero]
      simpa [ψJ] using hvalue
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic B)
    let gen : B → Prop := fun b ↦ Subgroup.zpowers b = (⊤ : Subgroup B)
    have hgenerator_value :
        ∀ b : B, gen b → (ψ : B → ℚ) b = (ψ : B → ℚ) g := by
      intro b hb
      simpa using
        eq_of_zpowers_eq_of_mem_rational_character_ring
          (x := b) (y := g) (θ := ψ) (by simp [gen, hb, hg])
    have hsum_all : ∑ b : B, (ψ : B → ℚ) b = 0 := by
      have htop : ∑ s : (⊤ : Subgroup B), (ψ : B → ℚ) s = 0 := hsumψ ⊤
      have htop_sum : ∑ s : (⊤ : Subgroup B), (ψ : B → ℚ) s = ∑ b : B, (ψ : B → ℚ) b := by
        exact
          Fintype.sum_equiv (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv
            (fun s : (⊤ : Subgroup B) ↦ (ψ : B → ℚ) s)
            (fun b : B ↦ (ψ : B → ℚ) b) (fun s ↦ rfl)
      exact htop_sum.symm ▸ htop
    have hsum_nongenerators :
        Finset.sum (Finset.univ.filter (fun b : B ↦ ¬ gen b)) (fun b ↦ (ψ : B → ℚ) b) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      exact hzero_nongenerator b (Finset.mem_filter.mp hb).2
    have hsum_generators :
        Finset.sum (Finset.univ.filter gen) (fun b ↦ (ψ : B → ℚ) b) =
          ((Finset.univ.filter gen).card : ℚ) * (ψ : B → ℚ) g := by
      calc
        Finset.sum (Finset.univ.filter gen) (fun b ↦ (ψ : B → ℚ) b)
            = Finset.sum (Finset.univ.filter gen) (fun _ ↦ (ψ : B → ℚ) g) := by
                refine Finset.sum_congr rfl ?_
                intro b hb
                exact hgenerator_value b (Finset.mem_filter.mp hb).2
        _ = ((Finset.univ.filter gen).card : ℚ) * (ψ : B → ℚ) g := by
              simp [nsmul_eq_mul]
    have hfiltered_zero :
        Finset.sum (Finset.univ.filter gen) (fun b ↦ (ψ : B → ℚ) b) = 0 := by
      have hsplit :=
        Finset.sum_filter_add_sum_filter_not Finset.univ gen (fun b : B ↦ (ψ : B → ℚ) b)
      rw [hsum_nongenerators, add_zero, hsum_all] at hsplit
      exact hsplit
    have hcard_generators_ne_zero :
        ((Finset.univ.filter gen).card : ℚ) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      refine Finset.card_ne_zero.mpr ?_
      exact ⟨g, by simp [gen, hg]⟩
    have hg_zero : (ψ : B → ℚ) g = 0 := by
      have hprod_zero :
          ((Finset.univ.filter gen).card : ℚ) * (ψ : B → ℚ) g = 0 := by
        rw [← hsum_generators]
        exact hfiltered_zero
      rcases mul_eq_zero.mp hprod_zero with hcard_zero | hvalue_zero
      · exact False.elim (hcard_generators_ne_zero hcard_zero)
      · exact hvalue_zero
    apply Subtype.ext
    ext b
    by_cases hb : gen b
    · simp [hgenerator_value b hb, hg_zero]
    · simp [hzero_nongenerator b hb]
  simpa using hstrong (Nat.card A) A inferInstance inferInstance inferInstance rfl φ hsum

/-- Helper for Corollary 13-13.1-8: if the subgroup sums of a rational scalar-extension character
vanish on every cyclic subgroup, then the character is zero. -/
private theorem rat_character_eq_zero_of_sum_eq_zero_on_cyclic_subgroups
    (θ : ℚ ⊗R[ℚ](G))
    (hsum : ∀ H : Subgroup.cyclicSubgroupsFamily_c1318 G, ∑ s : H.1, (θ : G → ℚ) s = 0) :
    θ = 0 := by
  apply Subtype.ext
  ext g
  let C : Subgroup G := Subgroup.zpowers g
  let θC : ℚ ⊗R[ℚ](C) :=
    ⟨fun c : C ↦ (θ : G → ℚ) c,
      restrict_mem_characterRingOverFieldScalarExtension C θ.property⟩
  have hsumC : ∀ J : Subgroup C, ∑ s : J, (θC : C → ℚ) s = 0 := by
    intro J
    have hmap_cyclic : IsCyclic (J.map C.subtype) :=
      ((J.equivMapOfInjective C.subtype C.subtype_injective).isCyclic).1 inferInstance
    calc
      ∑ s : J, (θC : C → ℚ) s = ∑ t : J.map C.subtype, (θ : G → ℚ) t := by
        exact subgroup_sum_restrict_eq_sum_map_subtype C J (θ : G → ℚ)
      _ = 0 := hsum ⟨J.map C.subtype, Subgroup.mem_cyclicSubgroupsFamily_c1318.2 hmap_cyclic⟩
  have hθC_zero : θC = 0 :=
    cyclic_rat_character_eq_zero_of_zero_subgroup_sums θC hsumC
  have hg_mem : g ∈ C := Subgroup.mem_zpowers g
  have hvalue : (θC : C → ℚ) ⟨g, hg_mem⟩ = 0 := by
    simp [hθC_zero]
  simpa [θC] using hvalue

/-- Helper for Corollary 13-13.1-8: orthogonality to every cyclic subgroup permutation character
forces a rational scalar-extension character to vanish. -/
private theorem rat_character_eq_zero_of_pairing_zero_on_cyclic_subgroupPermutationCharacters
    (θ : ℚ ⊗R[ℚ](G))
    (hpair :
      ∀ H : Subgroup.cyclicSubgroupsFamily_c1318 G,
        ⟪(θ : G → ℚ), (ℓ_{H.1}^G : G → ℚ)⟫ = 0) :
    θ = 0 := by
  apply rat_character_eq_zero_of_sum_eq_zero_on_cyclic_subgroups
  intro H
  have havg :
      (Nat.card H.1 : ℚ)⁻¹ * ∑ s : H.1, (θ : G → ℚ) s = 0 := by
    calc
      (Nat.card H.1 : ℚ)⁻¹ * ∑ s : H.1, (θ : G → ℚ) s
          = ⟪(fun h : H.1 ↦ (θ : G → ℚ) h), (1 : H.1 → ℚ)⟫ := by
              symm
              exact pairing_restrict_trivialCharacter_eq_average θ H
      _ = ⟪(θ : G → ℚ), (ℓ_{H.1}^G : G → ℚ)⟫ := by
            symm
            exact
              groupFunctionPairing_subgroupPermutationCharacter_eq_restrict_trivial_pairing θ H
      _ = 0 := hpair H
  have hcard_ne : (Nat.card H.1 : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [mul_comm] at havg
  exact (mul_eq_zero.mp havg).resolve_right (inv_ne_zero hcard_ne)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: conjugating a representation by a linear equivalence preserves
the identity element. -/
private theorem conjRepresentation_map_one
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (e : U ≃ₗ[ℚ] (Fin (Module.finrank ℚ U) → ℚ)) (ρ : Representation ℚ G U) :
    e.conj (ρ 1) = 1 := by
  calc
    e.conj (ρ 1) = e.conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id e

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: conjugating a representation by a linear equivalence preserves
multiplication. -/
private theorem conjRepresentation_map_mul
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (e : U ≃ₗ[ℚ] (Fin (Module.finrank ℚ U) → ℚ)) (ρ : Representation ℚ G U) (g h : G) :
    e.conj (ρ (g * h)) = e.conj (ρ g) * e.conj (ρ h) := by
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Corollary 13-13.1-8: every finite-dimensional rational representation may be moved
to a finite coordinate model without changing its character. -/
private def finBasisRepresentation
    {U : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    (ρ : Representation ℚ G U) : Representation ℚ G (Fin (Module.finrank ℚ U) → ℚ) :=
  let e := (Module.finBasis ℚ U).equivFun
  { toFun := fun g ↦ e.conj (ρ g)
    map_one' := conjRepresentation_map_one (G := G) e ρ
    map_mul' := conjRepresentation_map_mul (G := G) e ρ }

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: passing to finite coordinates does not change the character. -/
private theorem character_finBasisRepresentation_eq
    {U : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    (ρ : Representation ℚ G U) (g : G) :
    (finBasisRepresentation (G := G) ρ).character g = ρ.character g := by
  -- Conjugation preserves trace, so the coordinate model has the same character.
  change
    LinearMap.trace ℚ (Fin (Module.finrank ℚ U) → ℚ)
        (((Module.finBasis ℚ U).equivFun).conj (ρ g)) =
      LinearMap.trace ℚ U (ρ g)
  exact LinearMap.trace_conj' (ρ g) ((Module.finBasis ℚ U).equivFun)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: an arbitrary finite-dimensional rational character belongs to
`R_ℚ(G)` after transporting the carrier to finite coordinates. -/
lemma rep_character_mem_characterRingOverField_universe_bridge
    {U : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    (ρ : Representation ℚ G U) :
    ρ.character ∈ R[ℚ](G) := by
  let ρfin : Representation ℚ G (Fin (Module.finrank ℚ U) → ℚ) :=
    finBasisRepresentation (G := G) ρ
  let τ : Rep ℚ G := Rep.of ρfin
  have hchar : ρ.character = τ.ρ.character := by
    ext g
    symm
    simpa [τ, ρfin] using character_finBasisRepresentation_eq (G := G) ρ g
  -- Apply the Chapter 12 owner theorem after moving to a carrier in the ambient universe.
  exact hchar ▸ Representation.rep_character_mem_characterRingOverField τ

/-- Helper for Corollary 13-13.1-8: pairing a rational representation character with the cyclic
subgroup permutation character recovers the dimension of the corresponding fixed subspace. -/
lemma groupFunctionPairing_subgroupPermutationCharacter_eq_finrank_invariants
    (ρ : Representation ℚ G V) (C : Subgroup.cyclicSubgroupsFamily_c1318 G) :
    ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫ =
      Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) := by
  let τ : Representation ℚ C.1 ℚ := Representation.trivial ℚ C.1 ℚ
  have htriv : τ.character = (1 : C.1 → ℚ) := by
    ext c
    simp [τ, Representation.character, Representation.trivial]
  letI : Invertible (Nat.card C.1 : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card G : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hperm :
      (ℓ_{C.1}^G : G → ℚ) = (Representation.ind C.1.subtype τ).character := by
    calc
      (ℓ_{C.1}^G : G → ℚ)
          = (C.1.classFunctionInduction (1 : C.1 → ℚ) : G → ℚ) := by
              rfl
      _ = (C.1.classFunctionInduction τ.character : G → ℚ) := by
            rw [htriv]
      _ = (Representation.ind C.1.subtype τ).character := by
            simpa [Subgroup.classFunctionInduction_apply] using
              (Subgroup.inducedClassFunction_eq_character_ind (H := C.1) (K := ℚ) τ)
  -- Rewrite the cyclic permutation character as an induced trivial character, then apply
  -- Frobenius reciprocity followed by the averaging formula on the restriction to `C`.
  calc
    ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫
        = ⟪(Representation.ind C.1.subtype τ).character, ρ.character⟫ := by
            rw [hperm, groupFunctionPairing_comm]
    _ = ⟪τ.character, Representation.character (ρ.comp C.1.subtype)⟫ := by
          symm
          exact groupFunctionPairing_character_comp_eq_character_ind C.1.subtype ρ τ
    _ = ⟪Representation.character (ρ.comp C.1.subtype), τ.character⟫ := by
          rw [groupFunctionPairing_comm]
    _ = (Nat.card C.1 : ℚ)⁻¹ * ∑ s : C.1, Representation.character (ρ.comp C.1.subtype) s := by
          rw [htriv]
          rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
          simp
    _ = Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) := by
      simpa using
        (Representation.card_inv_mul_sum_char_eq_finrank (ρ := ρ.comp C.1.subtype))

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: product equivalences of representations are again
equivariant. -/
private theorem prodCongr_isIntertwining
    {U₁ : Type*} [AddCommGroup U₁] [Module ℚ U₁]
    {U₂ : Type*} [AddCommGroup U₂] [Module ℚ U₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module ℚ W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module ℚ W₂]
    {ρ₁ : Representation ℚ G U₁} {ρ₂ : Representation ℚ G U₂}
    {σ₁ : Representation ℚ G W₁} {σ₂ : Representation ℚ G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    ∀ g,
      ↑(e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) ∘ₗ (ρ₁.prod ρ₂) g =
        (σ₁.prod σ₂) g ∘ₗ ↑(e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) := by
  -- The product action intertwines componentwise because each factor does.
  intro g
  ext x <;> simp [Representation.prod, e₁.isIntertwining, e₂.isIntertwining]

/-- Helper for Corollary 13-13.1-8: equivariant equivalences may be combined componentwise over
products. -/
private def prodCongr
    {U₁ : Type*} [AddCommGroup U₁] [Module ℚ U₁]
    {U₂ : Type*} [AddCommGroup U₂] [Module ℚ U₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module ℚ W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module ℚ W₂]
    {ρ₁ : Representation ℚ G U₁} {ρ₂ : Representation ℚ G U₂}
    {σ₁ : Representation ℚ G W₁} {σ₂ : Representation ℚ G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    (ρ₁.prod ρ₂).Equiv (σ₁.prod σ₂) :=
  Representation.Equiv.mk
    (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv)
    (prodCongr_isIntertwining e₁ e₂)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: the linear equivalence coming from a complementary pair of
subrepresentations is equivariant. -/
private theorem prodEquivOfIsCompl_isIntertwining
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (ρ : Representation ℚ G U) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    ∀ g,
      ↑(σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) ∘ₗ
          (σ.toRepresentation.prod τ.toRepresentation) g =
        ρ g ∘ₗ ↑(σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) := by
  -- On each component, the product equivalence is just the subtype inclusion into `ρ`.
  intro g
  ext z
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inl,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((σ.toRepresentation g) z) = (ρ g) ↑z from rfl)
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inr,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((τ.toRepresentation g) z) = (ρ g) ↑z from rfl)

/-- Helper for Corollary 13-13.1-8: complementary invariant subspaces split a representation as a
product. -/
private def prodEquivOfIsCompl
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (ρ : Representation ℚ G U) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    (σ.toRepresentation.prod τ.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk
    (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ)
    (prodEquivOfIsCompl_isIntertwining ρ σ τ hστ)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-8: an irreducible rational representation has nontrivial carrier
space. -/
private theorem nontrivial_of_isIrreducible
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (ρ : Representation ℚ G U) [ρ.IsIrreducible] : Nontrivial U := by
  -- If the carrier were subsingleton, then `⊥ = ⊤` in the subrepresentation lattice, contradicting
  -- irreducibility.
  by_contra hU
  letI : Subsingleton U := not_nontrivial_iff_subsingleton.mp hU
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Corollary 13-13.1-8: equality of the fixed-space dimensions on every cyclic
subgroup forces equality of the rational characters. -/
lemma character_eq_of_finrank_invariants_eq_on_cyclicSubgroups
    (ρ : Representation ℚ G V) (ρ' : Representation ℚ G V')
    (hC : ∀ C : Subgroup.cyclicSubgroupsFamily_c1318 G,
      Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) =
        Module.finrank ℚ (invariants (ρ'.comp C.1.subtype))) :
    ρ.character = ρ'.character := by
  have hρmem : ρ.character ∈ ℚ⊗R[ℚ](G) := by
    exact
      mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
        (rep_character_mem_characterRingOverField_universe_bridge (G := G) ρ)
  have hρ'mem : ρ'.character ∈ ℚ⊗R[ℚ](G) := by
    exact
      mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
        (rep_character_mem_characterRingOverField_universe_bridge (G := G) ρ')
  have hdiff_mem : ρ.character - ρ'.character ∈ ℚ⊗R[ℚ](G) := by
    exact sub_mem hρmem hρ'mem
  let θ : ℚ⊗R[ℚ](G) := ⟨ρ.character - ρ'.character, hdiff_mem⟩
  have hpair :
      ∀ C : Subgroup.cyclicSubgroupsFamily_c1318 G,
        ⟪(θ : G → ℚ), (ℓ_{C.1}^G : G → ℚ)⟫ = 0 := by
    intro C
    have hneg : -ρ'.character = (-1 : ℚ) • ρ'.character := by
      ext g
      simp
    -- Route correction: package the character difference into `ℚ ⊗ R_ℚ(G)` and apply the
    -- working vanishing theorem from `13-13.1-6`.
    calc
      ⟪(θ : G → ℚ), (ℓ_{C.1}^G : G → ℚ)⟫
          = ⟪ρ.character - ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
              simp [θ]
      _ = ⟪ρ.character + (-1 : ℚ) • ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
            rw [sub_eq_add_neg, hneg]
      _ = ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫ +
            ⟪(-1 : ℚ) • ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
              rw [groupFunctionPairing_add_left]
      _ = ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫ +
            (-1 : ℚ) * ⟪ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
              rw [groupFunctionPairing_smul_left]
      _ = ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫ -
            ⟪ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by ring
      _ = Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) -
            Module.finrank ℚ (invariants (ρ'.comp C.1.subtype)) := by
              rw [groupFunctionPairing_subgroupPermutationCharacter_eq_finrank_invariants,
                groupFunctionPairing_subgroupPermutationCharacter_eq_finrank_invariants]
      _ = 0 := by rw [hC C, sub_self]
  have hθzero :
      θ = 0 :=
    Representation.rat_character_eq_zero_of_pairing_zero_on_cyclic_subgroupPermutationCharacters
      θ hpair
  ext g
  have hg :
      ((ρ.character - ρ'.character) : G → ℚ) g = 0 := by
    simpa [θ] using
      congrArg (fun χ : ℚ⊗R[ℚ](G) ↦ (χ : G → ℚ) g) hθzero
  exact sub_eq_zero.mp hg

omit [Finite G] [FiniteDimensional ℚ V'] in
/-- Helper for Corollary 13-13.1-8: a nonzero intertwiner from an irreducible representation is an
equivariant isomorphism onto its stable image. -/
lemma nonempty_equiv_range_of_nonzero_intertwining
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (σ : Representation ℚ G U) [σ.IsIrreducible]
    (τ : Representation ℚ G V')
    (f : σ.IntertwiningMap τ) (hf : f ≠ 0) :
    Nonempty (σ.Equiv f.range.toRepresentation) := by
  let fr :
      σ.IntertwiningMap f.range.toRepresentation :=
    f.toLinearMap.rangeRestrict.intertwiningMap_of_isIntertwiningMap σ f.range.toRepresentation
      (fun g x ↦ by
        ext
        exact LinearMap.congr_fun (f.2 g) x)
  have hf_inj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero (ρ := σ) (σ := τ) f).resolve_right hf
  have hfr_bijective : Function.Bijective fr := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hf_inj
      exact congrArg Subtype.val hxy
    · simpa [fr] using LinearMap.surjective_rangeRestrict f.toLinearMap
  exact
    Representation.nonempty_equiv_of_bijective_intertwiningMap
      (ρ1 := σ) (ρ2 := f.range.toRepresentation) fr hfr_bijective

/-- Helper for Corollary 13-13.1-8: the recursive cancellation proof over `ℚ`, written with
explicit carrier binders so Lean can recurse on the complement representation. -/
private theorem nonempty_equiv_of_character_eq_overQ_aux
    {U : Type v} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    {W : Type w} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (ρ : Representation ℚ G U) (ρ' : Representation ℚ G W)
    (hchar : ρ.character = ρ'.character) :
    Nonempty (ρ.Equiv ρ') := by
  classical
  by_cases hU : Nontrivial U
  · letI : Nontrivial U := hU
    letI : Invertible (Nat.card G : ℚ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    -- Evaluate at `1` to identify the ambient dimensions and hence the nontriviality of `ρ'`.
    have hdim' : (Module.finrank ℚ U : ℚ) = Module.finrank ℚ W := by
      simpa [Representation.char_one] using congrFun hchar 1
    have hdim : Module.finrank ℚ U = Module.finrank ℚ W :=
      Nat.cast_injective hdim'
    have hW : Nontrivial W := by
      exact Module.nontrivial_of_finrank_pos (hdim ▸ Module.finrank_pos)
    letI : Nontrivial W := hW
    obtain ⟨ιρ, _, πρ, hπρ_indep, hπρ_top, hπρ_irr⟩ :
        ∃ (ι : Type v) (_ : Fintype ι) (π : ι → Subrepresentation ρ),
          iSupIndep (fun i ↦ (π i).toSubmodule) ∧
            (⨆ i, (π i).toSubmodule) = ⊤ ∧
            ∀ i, (π i).toRepresentation.IsIrreducible := by
      exact exists_isInternal_irreducible_subrepresentations ρ
    have hιρ : Nonempty ιρ := by
      by_cases hιρ : IsEmpty ιρ
      · letI := hιρ
        exact False.elim <|
          (show (⊥ : Submodule ℚ U) ≠ ⊤ from bot_ne_top) <|
            by simp [iSup_of_empty] at hπρ_top
      · exact not_isEmpty_iff.mp hιρ
    let iρ := Classical.choice hιρ
    let σ₁ : Subrepresentation ρ := πρ iρ
    have hσ₁_irr : σ₁.toRepresentation.IsIrreducible := hπρ_irr iρ
    letI : σ₁.toRepresentation.IsIrreducible := hσ₁_irr
    haveI : Nontrivial σ₁.toSubmodule := nontrivial_of_isIrreducible σ₁.toRepresentation
    have hσ₁_pos : 0 < Module.finrank ℚ σ₁.toSubmodule := Module.finrank_pos
    obtain ⟨V₀, hV₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule ρ σ₁.toSubmodule
        σ₁.toSubmodule_mem_invtSubmodule
    let ρ₀ : Subrepresentation ρ := Subrepresentation.ofInvtSubmodule V₀
    have hρ₀ : IsCompl σ₁.toSubmodule ρ₀.toSubmodule := by
      simpa [ρ₀] using hV₀
    let eρ : (σ₁.toRepresentation.prod ρ₀.toRepresentation).Equiv ρ :=
      prodEquivOfIsCompl ρ σ₁ ρ₀ hρ₀
    have hσ₁_intertwining' :
        (Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ') : ℚ) =
          Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ) := by
      calc
        (Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ') : ℚ) =
            ⟪σ₁.toRepresentation.character, ρ'.character⟫ := by
              symm
              exact
                Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  ℚ σ₁.toRepresentation ρ'
        _ = ⟪σ₁.toRepresentation.character, ρ.character⟫ := by
              simp [hchar]
        _ = Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ) := by
              exact
                Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  ℚ σ₁.toRepresentation ρ
    have hσ₁_intertwining :
        Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ') =
          Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ) :=
      Nat.cast_injective hσ₁_intertwining'
    let iσ₁ : σ₁.toRepresentation.IntertwiningMap ρ :=
      σ₁.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap σ₁.toRepresentation ρ
        (fun g x ↦ rfl)
    have hiσ₁ : iσ₁ ≠ 0 := by
      obtain ⟨x, hx⟩ := exists_ne (0 : σ₁.toSubmodule)
      intro hiσ₁
      have hx0 := congrArg (fun f : σ₁.toRepresentation.IntertwiningMap ρ ↦ f x) hiσ₁
      exact hx (by simpa [iσ₁] using hx0)
    letI : Nontrivial (σ₁.toRepresentation.IntertwiningMap ρ) := ⟨⟨iσ₁, 0, hiσ₁⟩⟩
    have hσ₁_intertwining_pos :
        0 < Module.finrank ℚ (σ₁.toRepresentation.IntertwiningMap ρ') := by
      rw [hσ₁_intertwining]
      exact Module.finrank_pos
    letI : Nontrivial (σ₁.toRepresentation.IntertwiningMap ρ') :=
      Module.nontrivial_of_finrank_pos hσ₁_intertwining_pos
    obtain ⟨f, hf⟩ := exists_ne (0 : σ₁.toRepresentation.IntertwiningMap ρ')
    obtain ⟨eσ₁⟩ :
        Nonempty (σ₁.toRepresentation.Equiv f.range.toRepresentation) :=
      nonempty_equiv_range_of_nonzero_intertwining σ₁.toRepresentation ρ' f hf
    obtain ⟨V₀', hV₀'⟩ :=
      exists_isCompl_of_mem_invtSubmodule ρ' f.range.toSubmodule
        f.range.toSubmodule_mem_invtSubmodule
    let ρ₀' : Subrepresentation ρ' := Subrepresentation.ofInvtSubmodule V₀'
    have hρ₀' : IsCompl f.range.toSubmodule ρ₀'.toSubmodule := by
      simpa [ρ₀'] using hV₀'
    let eρ' : (f.range.toRepresentation.prod ρ₀'.toRepresentation).Equiv ρ' :=
      prodEquivOfIsCompl ρ' f.range ρ₀' hρ₀'
    have hcomp_char : ρ₀.toRepresentation.character = ρ₀'.toRepresentation.character := by
      -- Cancel the common irreducible summand supplied by the range of a nonzero intertwiner.
      have hsum :
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
            f.range.toRepresentation.character + ρ₀'.toRepresentation.character := by
        calc
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
              (σ₁.toRepresentation.prod ρ₀.toRepresentation).character := by
                symm
                exact Representation.char_prod σ₁.toRepresentation ρ₀.toRepresentation
          _ = ρ.character := Representation.char_iso eρ
          _ = ρ'.character := hchar
          _ = (f.range.toRepresentation.prod ρ₀'.toRepresentation).character := by
                exact (Representation.char_iso eρ').symm
          _ = f.range.toRepresentation.character + ρ₀'.toRepresentation.character := by
                exact Representation.char_prod f.range.toRepresentation ρ₀'.toRepresentation
      ext g
      have hg := congrFun hsum g
      have hleft :
          σ₁.toRepresentation.character g = f.range.toRepresentation.character g := by
        simpa using congrFun (Representation.char_iso eσ₁) g
      have hg' :
          σ₁.toRepresentation.character g + ρ₀.toRepresentation.character g =
            σ₁.toRepresentation.character g + ρ₀'.toRepresentation.character g := by
        simpa [hleft] using hg
      exact add_left_cancel hg'
    have hρ₀_lt : Module.finrank ℚ ρ₀.toSubmodule < Module.finrank ℚ U := by
      have hsplit :
          Module.finrank ℚ U =
            Module.finrank ℚ σ₁.toSubmodule + Module.finrank ℚ ρ₀.toSubmodule := by
        calc
          Module.finrank ℚ U =
              Module.finrank ℚ (σ₁.toSubmodule × ρ₀.toSubmodule) := by
                symm
                exact eρ.toLinearEquiv.finrank_eq
          _ = Module.finrank ℚ σ₁.toSubmodule + Module.finrank ℚ ρ₀.toSubmodule := by
                simp
      rw [hsplit]
      exact Nat.lt_add_of_pos_left hσ₁_pos
    obtain ⟨e₀⟩ :
        Nonempty (ρ₀.toRepresentation.Equiv ρ₀'.toRepresentation) :=
      nonempty_equiv_of_character_eq_overQ_aux
        ρ₀.toRepresentation ρ₀'.toRepresentation hcomp_char
    exact ⟨eρ.symm.trans ((prodCongr eσ₁ e₀).trans eρ')⟩
  · letI : Subsingleton U := not_nontrivial_iff_subsingleton.mp hU
    have hU0 : Module.finrank ℚ U = 0 := Module.finrank_zero_iff.mpr inferInstance
    have hW0' : (Module.finrank ℚ W : ℚ) = (0 : ℚ) := by
      simpa [hU0, Representation.char_one] using (congrFun hchar 1).symm
    have hW0 : Module.finrank ℚ W = 0 := by
      exact_mod_cast hW0'
    haveI : Subsingleton W := Module.finrank_zero_iff.mp hW0
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton U W) ?_⟩
    intro g
    ext x
    exact Subsingleton.elim _ _

termination_by Module.finrank ℚ U
decreasing_by
  simpa using hρ₀_lt

/-- Helper for Corollary 13-13.1-8: over `ℚ`, equality of characters forces an equivariant
equivalence of finite-dimensional representations. -/
lemma nonempty_equiv_of_character_eq_overQ
    (ρ : Representation ℚ G V) (ρ' : Representation ℚ G V')
    (hchar : ρ.character = ρ'.character) :
    Nonempty (ρ.Equiv ρ') := by
  -- Delegate to the explicit recursive helper on the carrier finrank.
  exact nonempty_equiv_of_character_eq_overQ_aux ρ ρ' hchar

/-- Companion bridge for Corollary `13-13.1-8`: the same criterion, expressed with the canonical
finite owner `Subgroup.cyclicSubgroupsFamily_c1318 G`. -/
theorem equiv_iff_finrank_invariants_eq_on_cyclicSubgroups
    (ρ : Representation ℚ G V) (ρ' : Representation ℚ G V') :
    Nonempty (ρ.Equiv ρ') ↔
      ∀ C : Subgroup.cyclicSubgroupsFamily_c1318 G,
        Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) =
          Module.finrank ℚ (invariants (ρ'.comp C.1.subtype)) := by
  constructor
  · rintro ⟨e⟩ C
    -- Equivalent representations have the same character, so the cyclic pairing bridge yields
    -- the same fixed-space dimension on every cyclic subgroup.
    apply Nat.cast_injective (R := ℚ)
    calc
      (Module.finrank ℚ (invariants (ρ.comp C.1.subtype)) : ℚ)
          = ⟪ρ.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
              symm
              exact
                groupFunctionPairing_subgroupPermutationCharacter_eq_finrank_invariants ρ C
      _ = ⟪ρ'.character, (ℓ_{C.1}^G : G → ℚ)⟫ := by
            simpa using
              congrArg
                (fun χ : G → ℚ ↦ ⟪χ, (ℓ_{C.1}^G : G → ℚ)⟫)
                (Representation.char_iso e)
      _ = Module.finrank ℚ (invariants (ρ'.comp C.1.subtype)) := by
            exact
              groupFunctionPairing_subgroupPermutationCharacter_eq_finrank_invariants ρ' C
  · intro hC
    -- Route correction: the converse first identifies the characters by Artin's cyclic-subgroup
    -- criterion, then isolates the rational descent from character equality to equivalence.
    have hchar :
        ρ.character = ρ'.character :=
      character_eq_of_finrank_invariants_eq_on_cyclicSubgroups ρ ρ' hC
    exact nonempty_equiv_of_character_eq_overQ ρ ρ' hchar

/-- Corollary 13-13.1-8: two finite-dimensional rational representations of a finite group are
equivariantly equivalent if and only if, for every cyclic subgroup `C ≤ G`, the fixed subspaces of
the restrictions `ρ|_C` and `ρ'|_C` have the same dimension. Here
`(ρ.comp C.subtype).invariants` is the subspace `V^C`. -/
theorem equiv_iff_finrank_invariants_eq_forall_isCyclic
    (ρ : Representation ℚ G V) (ρ' : Representation ℚ G V') :
    Nonempty (ρ.Equiv ρ') ↔
      ∀ C : Subgroup G, IsCyclic C →
        Module.finrank ℚ (invariants (ρ.comp C.subtype)) =
          Module.finrank ℚ (invariants (ρ'.comp C.subtype)) := by
  simpa [Subgroup.mem_cyclicSubgroupsFamily_c1318] using
    equiv_iff_finrank_invariants_eq_on_cyclicSubgroups (ρ := ρ) (ρ' := ρ')

end

end Representation
