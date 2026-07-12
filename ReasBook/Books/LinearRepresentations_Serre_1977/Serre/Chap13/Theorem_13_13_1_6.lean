import Mathlib
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_1_4
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap13.Corollary_13_13_1_2

noncomputable section

namespace Representation

open scoped BigOperators Representation

namespace Subgroup

/-- The finite family of cyclic subgroups of a finite group. -/
abbrev cyclicSubgroups (G : Type*) [Group G] [Finite G] : Finset (Subgroup G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  exact Finset.univ.filter fun H : Subgroup G ↦ IsCyclic H

@[simp] theorem mem_cyclicSubgroups {G : Type*} [Group G] [Finite G] {H : Subgroup G} :
    H ∈ cyclicSubgroups G ↔ IsCyclic H := by
  classical
  simp [cyclicSubgroups]

end Subgroup

open scoped Representation

/- The subgroup permutation characters are written `ℓ_H^G` on the source-facing theorem surface. -/

section

variable {G : Type} [Group G] [Finite G]

local instance instFintypeG_Theorem_13_13_1_6 : Fintype G := Fintype.ofFinite G
local instance anonInstP_Theorem_13_13_1_6_1 (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- Helper for Theorem 13-13.1-6: the tensor-level map used in Frobenius reciprocity is
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

/-- Helper for Theorem 13-13.1-6: Frobenius reciprocity gives a linear equivalence between
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

/-- Helper for Theorem 13-13.1-6: Frobenius reciprocity identifies the character pairing of a
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
/-- Helper for Theorem 13-13.1-6: transporting a rational virtual character through the bottom
field equivalence lands in the bottom-field character ring. -/
private theorem bot_symm_mem_characterRingOverField_of_mem
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {Monoid.exponent G} ℚ K]
    {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    (fun s ↦ (IntermediateField.botEquiv ℚ K).symm (χ s)) ∈
      R[↥(⊥ : IntermediateField ℚ K)](G) := by
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
    have hconst :
        (fun s : G ↦ (IntermediateField.botEquiv ℚ K).symm
          ((algebraMap ℤ (G → ℚ)) n s)) =
        algebraMap ℤ (G → ↥(⊥ : IntermediateField ℚ K)) n := by
      ext s
      simp [Pi.algebraMap_apply]
    rw [hconst]
    exact (R[↥(⊥ : IntermediateField ℚ K)](G)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa [Pi.add_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa [Pi.mul_apply] using (R[↥(⊥ : IntermediateField ℚ K)](G)).mul_mem hf hg

omit [Finite G] in
/-- Helper for Theorem 13-13.1-6: transporting a bottom-field valued virtual character through
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
    simpa using (IntermediateField.botEquiv ℚ K).toLinearEquiv.finrank_eq
  simpa [χQ, hfinrank] using hsmul

/-- Helper for Theorem 13-13.1-6: the source owner `ℚ ⊗ R_{↥⊥}(G)` transports to
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

/-- Helper for Theorem 13-13.1-6: a rational-valued class function belongs to Serre's rational
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
    exact hf.comp ((IntermediateField.botEquiv ℚ Lexp).symm : ℚ → ↥(⊥ : IntermediateField ℚ Lexp))
  let φBot : classFunctionSubmodule (⊥ : IntermediateField ℚ Lexp) G :=
    ⟨fBot, (mem_classFunctionSubmodule_iff _ _).2 hfBotClass⟩
  have hGammaBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) = ⊤ := by
    unfold Representation.gammaSubgroup
    letI : IsGalois ℚ Lexp := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ Lexp
    have hfixingSubgroupBot : (⊥ : IntermediateField ℚ Lexp).fixingSubgroup = ⊤ :=
      IsGaloisGroup.fixingSubgroup_bot (G := Gal(Lexp / ℚ)) (K := ℚ) (L := Lexp)
    rw [hfixingSubgroupBot]
    simp
  have hbot_mem :
      fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) ↔
        fBot ∈ (↥(⊥ : IntermediateField ℚ Lexp)) ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) := by
    constructor
    · intro hf
      refine Submodule.span_induction
          (p := fun x (_hx : x ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G)) ↦
            x ∈ (↥(⊥ : IntermediateField ℚ Lexp)) ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G))
          ?_ ?_ ?_ ?_ hf
      · intro χ hχ
        exact Submodule.subset_span (by simpa using hχ)
      · exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        exact Submodule.add_mem _ hx hy
      · intro a x _ hx
        convert
          (Submodule.smul_mem
            ((↥(⊥ : IntermediateField ℚ Lexp)) ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G))
            (algebraMap ℚ ↥(⊥ : IntermediateField ℚ Lexp) a) hx) using 1
        ext s
        simpa [Algebra.smul_def]
    · intro hf
      refine Submodule.span_induction
          (p := fun x (_hx :
            x ∈ (↥(⊥ : IntermediateField ℚ Lexp)) ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G)) ↦
              x ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G))
          ?_ ?_ ?_ ?_ hf
      · intro χ hχ
        exact Submodule.subset_span (by simpa using hχ)
      · exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        exact Submodule.add_mem _ hx hy
      · intro a x _ hx
        let q : ℚ := IntermediateField.botEquiv ℚ Lexp a
        have hq : algebraMap ℚ ↥(⊥ : IntermediateField ℚ Lexp) q = a := by
          exact (IntermediateField.botEquiv ℚ Lexp).symm_apply_apply a
        convert (Submodule.smul_mem (ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G)) q hx) using 1
        ext s
        simpa [Algebra.smul_def, hq]
  have hownerK :
      fBot ∈ (↥(⊥ : IntermediateField ℚ Lexp)) ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := by
    simpa [φBot] using
      (Representation.classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        (G := G) (L := Lexp) (K := (⊥ : IntermediateField ℚ Lexp))
        φBot)
  have howner :
      fBot ∈ ℚ⊗R[↥(⊥ : IntermediateField ℚ Lexp)](G) ↔
        ∀ s (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)), fBot s = fBot (s ^ t) := by
    exact hbot_mem.trans hownerK
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

/-- Helper for Theorem 13-13.1-6: a rational virtual character takes the same value on elements
generating the same cyclic subgroup. -/
lemma eq_of_zpowers_eq_of_mem_rational_character_ring
    {θ : ℚ ⊗R[ℚ](G)} {x y : G}
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    (θ : G → ℚ) x = (θ : G → ℚ) y := by
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
  have hθpow :
      ∀ s (t : Γ_ℚ(G)), (θ : G → ℚ) s = (θ : G → ℚ) (s ^ t) :=
    (rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant
      (θ : G → ℚ) hθClass).1 θ.property
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

/-- Helper for Theorem 13-13.1-6: pairing the restriction of a rational character to a cyclic
subgroup with the trivial character gives the normalized subgroup sum. -/
lemma pairing_restrict_trivialCharacter_eq_average
    (θ : ℚ ⊗R[ℚ](G)) (H : Subgroup.cyclicSubgroups G) :
    ⟪(fun h : H.1 ↦ (θ : G → ℚ) h), (1 : H.1 → ℚ)⟫ =
      (Nat.card H.1 : ℚ)⁻¹ * ∑ s : H.1, (θ : G → ℚ) s := by
  -- Rewrite the pairing with inversion on the trivial character and simplify.
  rw [groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  simp

/-- Helper for Theorem 13-13.1-6: restriction preserves the rational scalar-extension character
ring. -/
lemma restrict_mem_characterRingOverFieldScalarExtension_rat_local
    {A : Type} [Group A] [Finite A] (J : Subgroup A) {φ : A → ℚ}
    (hφ : φ ∈ ℚ ⊗R[ℚ](A)) :
    (fun j : J ↦ φ j) ∈ ℚ ⊗R[ℚ](J) := by
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype J := Fintype.ofFinite J
  -- Restrict the rational span generator-by-generator.
  induction hφ using Submodule.span_induction with
  | mem χ hχ =>
      have hχ_mem : χ ∈ R[ℚ](A) := by
        simpa using hχ
      have hχ_restrict : (fun j : J ↦ χ j) ∈ R[ℚ](J) := by
        -- Restriction sends representation characters to representation characters.
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

/-- Helper for Theorem 13-13.1-6: summing a restricted function over an internal subgroup agrees
with summing the ambient function over the corresponding mapped subgroup. -/
private lemma subgroup_sum_restrict_eq_sum_map_subtype
    (C : Subgroup G) (J : Subgroup C) (f : G → ℚ) :
    (∑ s : J, f s) = ∑ t : J.map C.subtype, f t := by
  classical
  -- Reindex the finite sum along the canonical equivalence `J ≃ J.map C.subtype`.
  simpa using
    (Fintype.sum_equiv (J.equivMapOfInjective C.subtype C.subtype_injective)
      (fun s : J ↦ f s) (fun t : J.map C.subtype ↦ f t) (fun s ↦ rfl))

/-- Helper for Theorem 13-13.1-6: a proper subgroup of a finite group has strictly smaller
cardinality. -/
private lemma proper_subgroup_natCard_lt {A : Type} [Group A] [Finite A] (J : Subgroup A)
    (hJ : J ≠ ⊤) : Nat.card J < Nat.card A := by
  let _ : Fintype A := Fintype.ofFinite A
  let _ : Fintype J := Fintype.ofFinite J
  -- A proper subgroup omits some ambient element, so its subtype cardinality is strictly smaller.
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
/-- Helper for Theorem 13-13.1-6: the rational trivial character is the constant function `1`. -/
private theorem rational_trivial_character_eq_one
    {A : Type} [Group A] :
    (Representation.trivial ℚ A ℚ).character = (1 : A → ℚ) := by
  -- Evaluate the trivial representation pointwise; every group element acts as the identity.
  ext a
  simp [Representation.character, Representation.trivial]

omit [Finite G] in
/-- Helper for Theorem 13-13.1-6: every element of `R[ℚ](G)` is an integral linear combination of
honest finite-dimensional rational characters. -/
lemma mem_span_rep_characters_of_mem_characterRingOverField
    {χ : G → ℚ} (hχ : χ ∈ R[ℚ](G)) :
    χ ∈ Submodule.span ℤ
      { ψ : G → ℚ |
          ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℚ V) (_ : FiniteDimensional ℚ V)
            (ρ : Representation ℚ G V), ψ = ρ.character } := by
  let honestCharacters : Set (G → ℚ) :=
    { ψ : G → ℚ |
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℚ V) (_ : FiniteDimensional ℚ V)
          (ρ : Representation ℚ G V), ψ = ρ.character }
  let T : Submodule ℤ (G → ℚ) := Submodule.span ℤ honestCharacters
  have hmul_T :
      ∀ {f g : G → ℚ}, f ∈ T → g ∈ T → f * g ∈ T := by
    intro f g hf hg
    have hleft : ∀ ψ : G → ℚ, ψ ∈ T → f * ψ ∈ T := by
      induction hf using Submodule.span_induction with
      | mem φ hφ =>
          rcases hφ with ⟨V, _, _, _, ρ, rfl⟩
          intro ψ hψ
          induction hψ using Submodule.span_induction with
          | mem ψ hψ =>
              rcases hψ with ⟨W, _, _, _, σ, rfl⟩
              let τ : Representation ℚ G (TensorProduct ℚ V W) := Representation.tprod ρ σ
              -- Products of honest characters are again honest characters via tensor products.
              have hchar :
                  ρ.character * σ.character = τ.character := by
                simpa [τ] using (Representation.char_tensor ρ σ).symm
              rw [hchar]
              exact Submodule.subset_span ⟨TensorProduct ℚ V W, inferInstance, inferInstance,
                inferInstance, τ, rfl⟩
          | zero =>
              simpa [T] using (Submodule.zero_mem T : (0 : G → ℚ) ∈ T)
          | add ψ ξ _ _ hψ hξ =>
              simpa [mul_add] using Submodule.add_mem T hψ hξ
          | smul n ψ _ hψ =>
              simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                Submodule.smul_mem T n hψ
      | zero =>
          intro ψ hψ
          simpa [T] using (Submodule.zero_mem T : (0 : G → ℚ) ∈ T)
      | add φ ψ _ _ hφ hψ =>
          intro ξ hξ
          simpa [add_mul] using Submodule.add_mem T (hφ ξ hξ) (hψ ξ hξ)
      | smul n φ _ hφ =>
          intro ψ hψ
          simpa [zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
            Submodule.smul_mem T n (hφ ψ hψ)
    exact hleft g hg
  -- The span of honest characters is a subalgebra containing every irreducible generator.
  refine
    Algebra.adjoin_induction
      (p := fun f _ ↦
        f ∈ Submodule.span ℤ honestCharacters)
      ?_ ?_ ?_ ?_ hχ
  · rintro ψ ⟨ρ, hρfd, -, rfl⟩
    exact Submodule.subset_span ⟨ρ, inferInstance, inferInstance, hρfd, ρ.ρ, rfl⟩
  · intro n
    let τ : Representation ℚ G ℚ := Representation.trivial ℚ G ℚ
    have htriv : τ.character ∈ T :=
      Submodule.subset_span ⟨ℚ, inferInstance, inferInstance, inferInstance, τ, rfl⟩
    have hscalar : algebraMap ℤ (G → ℚ) n = n • τ.character := by
      -- Rewrite the integer-valued constant function through the trivial character.
      rw [show τ.character = (1 : G → ℚ) by
        simpa [τ] using rational_trivial_character_eq_one (A := G)]
      ext g
      simp
    rw [hscalar]
    simpa [T] using (Submodule.smul_mem T n htriv)
  · intro f g _ _ hf hg
    simpa [T] using (Submodule.add_mem T hf hg)
  · intro f g _ _ hf hg
    simpa [T] using (hmul_T hf hg)

/-- Helper for Theorem 13-13.1-6: pairing a class function with a cyclic subgroup permutation
character is the pairing of its restriction with the trivial character. -/
lemma groupFunctionPairing_subgroupPermutationCharacter_eq_restrict_trivial_pairing
    (θ : ℚ ⊗R[ℚ](G)) (H : Subgroup.cyclicSubgroups G) :
    ⟪(θ : G → ℚ), (ℓ_{H.1}^G : G → ℚ)⟫ = ⟪(fun h : H.1 ↦ (θ : G → ℚ) h), (1 : H.1 → ℚ)⟫ := by
  -- Route correction: the useful bridge is the owner-level statement for
  -- `θ : ℚ⊗R[ℚ](G)`, not the broader arbitrary-class-function version.
  let repSpan : Submodule ℤ (G → ℚ) :=
    Submodule.span ℤ
      { ψ : G → ℚ |
          ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℚ V) (_ : FiniteDimensional ℚ V)
            (ρ : Representation ℚ G V), ψ = ρ.character }
  have hspan_bridge :
      ∀ {χ : G → ℚ}, χ ∈ repSpan →
        ⟪χ, (ℓ_{H.1}^G : G → ℚ)⟫ = ⟪(fun h : H.1 ↦ χ h), (1 : H.1 → ℚ)⟫ := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem ψ hψ =>
        rcases hψ with ⟨V, _, _, _, ρ, rfl⟩
        let C : Subgroup G := H.1
        let τ : Representation ℚ C ℚ := Representation.trivial ℚ C ℚ
        have htriv_char : τ.character = (1 : C → ℚ) := by
          -- Replace the trivial restricted character by the constant function `1`.
          simpa [τ] using rational_trivial_character_eq_one (A := C)
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
          exact
            groupFunctionPairing_character_comp_eq_character_ind C.subtype ρ τ
        -- Frobenius reciprocity identifies the ambient pairing with the restricted trivial pairing.
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

/-- Helper for Theorem 13-13.1-6: each cyclic subgroup permutation character already belongs to
the rational scalar-extension character ring. -/
lemma subgroupPermutationCharacter_mem_characterRingOverFieldScalarExtension
    (H : Subgroup.cyclicSubgroups G) :
    ((ℓ_{H.1}^G : G → ℚ)) ∈ ℚ ⊗R[ℚ](G) := by
  -- The induced trivial character is an honest rational character before scalar extension.
  exact
    mem_characterRingOverFieldScalarExtension_of_mem_characterRingOverField
      ((ℓ_{H.1}^G : R[ℚ](G)).property)

/-- Helper for Theorem 13-13.1-6: on a finite cyclic group, vanishing subgroup sums force a
rational virtual character to be zero. -/
private lemma cyclic_rat_character_eq_zero_of_zero_subgroup_sums
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
    -- First kill every nongenerator by restricting to the proper cyclic subgroup it generates.
    have hzero_nongenerator :
        ∀ b : B, Subgroup.zpowers b ≠ (⊤ : Subgroup B) → (ψ : B → ℚ) b = 0 := by
      intro b hb
      let J : Subgroup B := Subgroup.zpowers b
      have hlt : Nat.card J < n := by
        rw [← hBcard]
        exact proper_subgroup_natCard_lt J hb
      let ψJ : ℚ ⊗R[ℚ](J) :=
        ⟨fun j : J ↦ (ψ : B → ℚ) j,
          restrict_mem_characterRingOverFieldScalarExtension_rat_local J ψ.property⟩
      have hsumJ : ∀ K : Subgroup J, ∑ s : K, (ψJ : J → ℚ) s = 0 := by
        intro K
        -- Transport each internal subgroup sum to the ambient subgroup `K.map J.subtype`.
        calc
          ∑ s : K, (ψJ : J → ℚ) s = ∑ t : K.map J.subtype, (ψ : B → ℚ) t := by
            exact subgroup_sum_restrict_eq_sum_map_subtype J K (ψ : B → ℚ)
          _ = 0 := hsumψ (K.map J.subtype)
      have hψJ_zero : ψJ = 0 := by
        simpa using ih (Nat.card J) hlt J inferInstance inferInstance inferInstance rfl ψJ hsumJ
      have hb_mem : b ∈ J := Subgroup.mem_zpowers b
      have hvalue : (ψJ : J → ℚ) ⟨b, hb_mem⟩ = 0 := by
        simp [hψJ_zero]
      simpa [ψJ] using hvalue
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic B)
    let gen : B → Prop := fun b ↦ Subgroup.zpowers b = (⊤ : Subgroup B)
    have hgenerator_value :
        ∀ b : B, gen b → (ψ : B → ℚ) b = (ψ : B → ℚ) g := by
      intro b hb
      -- Rational characters are constant on elements generating the same cyclic subgroup.
      simpa [gen, hb, hg] using
        eq_of_zpowers_eq_of_mem_rational_character_ring
          (θ := ψ) (x := b) (y := g) (by simp [gen, hb, hg])
    have hsum_all : ∑ b : B, (ψ : B → ℚ) b = 0 := by
      have htop :
          ∑ s : (⊤ : Subgroup B), (ψ : B → ℚ) s = 0 :=
        hsumψ (⊤ : Subgroup B)
      have htop_sum :
          ∑ s : (⊤ : Subgroup B), (ψ : B → ℚ) s = ∑ b : B, (ψ : B → ℚ) b := by
        exact
          Fintype.sum_equiv (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv
            (fun s : (⊤ : Subgroup B) ↦ (ψ : B → ℚ) s)
            (fun b : B ↦ (ψ : B → ℚ) b) (fun s ↦ rfl)
      exact htop_sum.symm ▸ htop
    have hsum_nongenerators :
        Finset.sum (Finset.univ.filter (fun b : B ↦ ¬ gen b)) (fun b ↦ (ψ : B → ℚ) b) = 0 := by
      -- Every nongenerator already vanishes by the restriction step above.
      refine Finset.sum_eq_zero ?_
      intro b hb
      exact hzero_nongenerator b (Finset.mem_filter.mp hb).2
    have hsum_generators :
        Finset.sum (Finset.univ.filter gen) (fun b ↦ (ψ : B → ℚ) b) =
          ((Finset.univ.filter gen).card : ℚ) * (ψ : B → ℚ) g := by
      -- All generators carry the same value, so this filtered sum is a constant sum.
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
      -- Split the ambient total sum into generators and nongenerators.
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
    -- Finally every element is either a generator with the common zero value or a nongenerator.
    apply Subtype.ext
    ext b
    by_cases hb : gen b
    · simp [hgenerator_value b hb, hg_zero]
    · simp [hzero_nongenerator b hb]
  simpa using hstrong (Nat.card A) A inferInstance inferInstance inferInstance rfl φ hsum

/-- Helper for Theorem 13-13.1-6: if the sums of a rational virtual character vanish on all cyclic
subgroups of `G`, then the character is zero. -/
private lemma rat_character_eq_zero_of_sum_eq_zero_on_cyclic_subgroups
    (θ : ℚ ⊗R[ℚ](G))
    (hsum : ∀ H : Subgroup.cyclicSubgroups G, ∑ s : H.1, (θ : G → ℚ) s = 0) :
    θ = 0 := by
  apply Subtype.ext
  ext g
  let C : Subgroup G := Subgroup.zpowers g
  let θC : ℚ ⊗R[ℚ](C) :=
    ⟨fun c : C ↦ (θ : G → ℚ) c,
      restrict_mem_characterRingOverFieldScalarExtension_rat_local C θ.property⟩
  have hsumC : ∀ J : Subgroup C, ∑ s : J, (θC : C → ℚ) s = 0 := by
    intro J
    have hmap_cyclic : IsCyclic (J.map C.subtype) :=
      ((J.equivMapOfInjective C.subtype C.subtype_injective).isCyclic).1 inferInstance
    -- Reindex internal subgroup sums to the ambient cyclic subgroup `J.map C.subtype`.
    calc
      ∑ s : J, (θC : C → ℚ) s = ∑ t : J.map C.subtype, (θ : G → ℚ) t := by
        exact subgroup_sum_restrict_eq_sum_map_subtype C J (θ : G → ℚ)
      _ = 0 := hsum ⟨J.map C.subtype, Subgroup.mem_cyclicSubgroups.2 hmap_cyclic⟩
  have hθC_zero : θC = 0 :=
    cyclic_rat_character_eq_zero_of_zero_subgroup_sums θC hsumC
  have hg_mem : g ∈ C := Subgroup.mem_zpowers g
  -- Evaluate the restricted zero theorem at the distinguished generator `g ∈ zpowers g`.
  have hvalue : (θC : C → ℚ) ⟨g, hg_mem⟩ = 0 := by
    simp [hθC_zero]
  simpa [θC] using hvalue

/-- Helper for Theorem 13-13.1-6: orthogonality to every cyclic subgroup permutation character
forces a rational virtual character to vanish. -/
lemma rat_character_eq_zero_of_pairing_zero_on_cyclic_subgroupPermutationCharacters
    (θ : ℚ ⊗R[ℚ](G))
    (hpair :
      ∀ H : Subgroup.cyclicSubgroups G,
        ⟪(θ : G → ℚ), (ℓ_{H.1}^G : G → ℚ)⟫ = 0) :
    θ = 0 := by
  -- Rewrite each orthogonality condition as the vanishing of the corresponding cyclic subgroup sum.
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

-- Proof sketch: the core/canonical owner theorem `cyclicSubgroupInductionOverField_surjective`
-- says that `ℚ ⊗ R_ℚ(G)` is generated by inductions of arbitrary elements of `ℚ ⊗ R_ℚ(C)` from
-- cyclic subgroups `C`. Exercise `13-13.1-11` identifies each cyclic summand `ℚ ⊗ R_ℚ(C)` with
-- the `ℚ`-span of the induced trivial characters `ℓ_D^C`, and induction in stages then rewrites
-- their images in `G` as the permutation characters `ℓ_D^G` for cyclic `D ≤ G`.
/-- Theorem 13-13.1-6: Serre's rationalized character ring `ℚ ⊗ R_ℚ(G)`, realized as
`Representation.characterRingOverFieldScalarExtension ℚ G`, is the `ℚ`-span of the permutation
characters `ℓ_C^G = Ind_C^G(1_C)` induced from the cyclic subgroups `C ≤ G`. -/
theorem characterRingOverFieldScalarExtension_eq_span_cyclic_subgroupPermutationCharactersOverQ :
    ℚ ⊗R[ℚ](G) =
      Submodule.span ℚ
        (Set.range fun H : Subgroup.cyclicSubgroups G ↦
          (ℓ_{H.1}^G : G → ℚ)) := by
  let S : Submodule ℚ (G → ℚ) :=
    Submodule.span ℚ
      (Set.range fun H : Subgroup.cyclicSubgroups G ↦ (ℓ_{H.1}^G : G → ℚ))
  have hS_le : S ≤ ℚ ⊗R[ℚ](G) := by
    -- Each cyclic permutation character is itself a rational character, hence belongs to the
    -- scalar-extension owner.
    rw [Submodule.span_le]
    rintro _ ⟨H, rfl⟩
    exact subgroupPermutationCharacter_mem_characterRingOverFieldScalarExtension H
  -- Route correction: the remaining direction should follow Serre's source proof. One proves
  -- that any `θ : ℚ⊗R[ℚ](G)` orthogonal to all generators `ℓ_C^G` has zero cyclic averages, then
  -- uses the helper above to show that the value of `θ` depends only on the generated cyclic
  -- subgroup and concludes by induction on subgroup order.
  have hle : ℚ ⊗R[ℚ](G) ≤ S := by
    let pairToSpan : (ℚ ⊗R[ℚ](G)) →ₗ[ℚ] Module.Dual ℚ S :=
      { toFun := fun θ =>
          { toFun := fun s ↦ ⟪(θ : G → ℚ), (s : G → ℚ)⟫
            map_add' := by
              intro s t
              exact groupFunctionPairing_add_right (θ : G → ℚ) (s : G → ℚ) (t : G → ℚ)
            map_smul' := by
              intro a s
              simpa using
                groupFunctionPairing_smul_right a (θ : G → ℚ) (s : G → ℚ) }
        map_add' := by
          intro θ η
          ext s
          exact groupFunctionPairing_add_left (θ : G → ℚ) (η : G → ℚ) (s : G → ℚ)
        map_smul' := by
          intro a θ
          ext s
          simpa using groupFunctionPairing_smul_left a (θ : G → ℚ) (s : G → ℚ) }
    have hpairToSpan_injective : Function.Injective pairToSpan := by
      intro θ η hθη
      apply sub_eq_zero.mp
      apply rat_character_eq_zero_of_pairing_zero_on_cyclic_subgroupPermutationCharacters
      intro H
      let sH : S := ⟨(ℓ_{H.1}^G : G → ℚ), Submodule.subset_span ⟨H, rfl⟩⟩
      have hsH :
          pairToSpan (θ - η) sH = 0 := by
        have hsub : pairToSpan (θ - η) = 0 := by
          rw [LinearMap.map_sub, hθη, sub_self]
        exact congrArg (fun F : Module.Dual ℚ S ↦ F sH) hsub
      -- Evaluating the zero functional on each cyclic generator gives the orthogonality hypothesis.
      simpa [pairToSpan, sH] using hsH
    -- The pairing map into `S*` is injective, so `dim W ≤ dim S`.
    have hW_finrank_le :
        Module.finrank ℚ (ℚ ⊗R[ℚ](G)) ≤ Module.finrank ℚ S := by
      have hdual_le :
          Module.finrank ℚ (ℚ ⊗R[ℚ](G)) ≤ Module.finrank ℚ (Module.Dual ℚ S) :=
        LinearMap.finrank_le_finrank_of_injective hpairToSpan_injective
      rw [Subspace.dual_finrank_eq] at hdual_le
      exact hdual_le
    -- The inclusion `S ≤ W` gives the reverse inequality on dimensions.
    have hS_finrank_le :
        Module.finrank ℚ S ≤ Module.finrank ℚ (ℚ ⊗R[ℚ](G)) :=
      LinearMap.finrank_le_finrank_of_injective
        (f := Submodule.inclusion hS_le)
        (fun x y hxy ↦ by
          apply Subtype.ext
          ext g
          exact congrArg (fun z : ℚ ⊗R[ℚ](G) ↦ (z : G → ℚ) g) hxy)
    have hfinrank_eq :
        Module.finrank ℚ S = Module.finrank ℚ (ℚ ⊗R[ℚ](G)) :=
      le_antisymm hS_finrank_le hW_finrank_le
    exact (Submodule.eq_of_le_of_finrank_eq hS_le hfinrank_eq).symm.le
  exact le_antisymm hle hS_le

end

end Representation
