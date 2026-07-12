import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_2
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_3_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1
import LinearRepresentations_Serre_1977.Chap13.Corollary_13_13_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation
open scoped Representation

section

variable {G : Type} [Group G] [Finite G]

local instance instFintypeG_Corollary_13_13_1_5 : Fintype G := Fintype.ofFinite G
local instance neZeroExponentG_c1315 : NeZero (Monoid.exponent G) := Monoid.neZero_exponent_of_finite

local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ

/-- Helper for Corollary 13-13.1-5: choose a complex embedding of the cyclotomic field attached
to `Monoid.exponent G`. -/
private noncomputable def cyclotomicFieldExponentToComplex : Lexp →+* ℂ :=
  NumberField.ComplexEmbedding.lift Lexp (algebraMap ℚ ℂ)

/-- Helper for Corollary 13-13.1-5: the chosen complex embedding gives the cyclotomic field its
ambient `ℂ`-algebra structure. -/
noncomputable local instance cyclotomicFieldExponentAlgebraComplex : Algebra Lexp ℂ :=
  RingHom.toAlgebra cyclotomicFieldExponentToComplex

/-- Helper for Corollary 13-13.1-5: the cyclotomic field of the exponent of `G` contains the
required roots of unity. -/
private theorem cyclotomicFieldExponent_hasEnoughRootsOfUnity :
    HasEnoughRootsOfUnity Lexp (Monoid.exponent G) := by
  letI : NeZero ((Monoid.exponent G : ℚ)) := by
    exact ⟨Nat.cast_ne_zero.mpr (NeZero.ne (Monoid.exponent G))⟩
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  refine ⟨?_, inferInstance⟩
  exact ⟨IsCyclotomicExtension.zeta (Monoid.exponent G) ℚ Lexp,
    IsCyclotomicExtension.zeta_spec (Monoid.exponent G) ℚ Lexp⟩

/-- Helper for Corollary 13-13.1-5: the cyclotomic field attached to `Monoid.exponent G` carries
the canonical cyclotomic `ℚ`-structure needed for Serre's `Γ`-subgroups. -/
noncomputable local instance cyclotomicFieldExponent_isCyclotomicExtension :
    IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

omit [Finite G] in
/-- Helper for Corollary 13-13.1-5: restricting a virtual `K`-character to a subgroup again
lands in the corresponding subgroup character ring. -/
private theorem restrict_mem_characterRingOverField_local
    {K : Type*} [Field K] (H : Subgroup G) (χ : R[K](G)) :
    (fun h : H ↦ (χ : G → K) h) ∈ R[K](H) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · intro ψ hψ
    rcases hψ with ⟨ρ, hρfd, -, rfl⟩
    letI : FiniteDimensional K ρ := hρfd
    change (Rep.res H.subtype ρ).ρ.character ∈ R[K](H)
    letI : FiniteDimensional K (Rep.res H.subtype ρ) := inferInstance
    exact Representation.rep_character_mem_characterRingOverField (Rep.res H.subtype ρ)
  · intro n
    exact (R[K](H)).algebraMap_mem n
  · intro f g _ _ hf hg
    simpa using (R[K](H)).add_mem hf hg
  · intro f g _ _ hf hg
    simpa using (R[K](H)).mul_mem hf hg

/-- Helper for Corollary 13-13.1-5: if two elements have the same values under all ordinary
characters, then they are conjugate. -/
private theorem tensor_character_eval_eq_of_character_values_eq
    {x y : G} (hxy : ∀ χ : R(G), χ x = χ y) (z : ℂ ⊗R(G)) :
    (z : G → ℂ) x = (z : G → ℂ) y := by
  -- Extend the character-value equality from generators to the whole tensor character ring.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a χ
    simp [Representation.coe_tmul, hxy χ]
  · intro z w hz hw
    simpa using congrArg₂ (fun a b : ℂ ↦ a + b) hz hw

/-- Helper for Corollary 13-13.1-5: equality of all ordinary virtual-character values forces
equality of conjugacy classes. -/
private theorem isConj_of_character_values_eq
    {x y : G} (hxy : ∀ χ : R(G), χ x = χ y) : IsConj x y := by
  by_contra hconj
  -- Separate the two conjugacy classes by the weighted indicator tensor character from Chapter
  -- `11`, then compare its values using the character-value hypothesis.
  rcases
      weighted_adamsOperator_conjClassIndicator_lifts_to_tensorCharacterRing
        ℂ 1 (ConjClasses.mk x) (by
          intro z hz
          exact ⟨(z : ℂ), by simp⟩) with
    ⟨z, hz⟩
  have hEval := tensor_character_eval_eq_of_character_values_eq hxy z
  have hxz : (z : G → ℂ) x = Nat.card G := by
    have hx_indicator : (ConjClasses.mk x).indicator x = (1 : ℂ) := by
      classical
      simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
    -- At `x`, the indicator of its own conjugacy class is `1`; the global multiplier `|G| / (|G|,1)`
    -- equals `Nat.card G`.
    calc
      (z : G → ℂ) x =
          algebraMap ℂ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (1 : ℕ)) : ℕ) : ℂ) *
              Ψ^1((ConjClasses.mk x).indicator) x) := by
            simpa using congrFun hz x
      _ = Nat.card G := by
        simp [Representation.adamsOperator, hx_indicator]
  have hyz : (z : G → ℂ) y = 0 := by
    have hy_not_mem : y ∉ (ConjClasses.mk x).carrier := by
      intro hy_mem
      have hmk : ConjClasses.mk y = ConjClasses.mk x :=
        ConjClasses.mem_carrier_iff_mk_eq.mp hy_mem
      exact hconj (ConjClasses.mk_eq_mk_iff_isConj.mp hmk).symm
    have hy_mk_ne : ConjClasses.mk y ≠ ConjClasses.mk x := by
      intro hy_mk
      exact hy_not_mem (ConjClasses.mem_carrier_iff_mk_eq.mpr hy_mk)
    have hy_indicator : (ConjClasses.mk x).indicator y = (0 : ℂ) := by
      classical
      simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, hy_mk_ne]
    -- At any nonconjugate element, that same indicator vanishes.
    calc
      (z : G → ℂ) y =
          algebraMap ℂ ℂ
            ((((Nat.card G / Nat.gcd (Nat.card G) (1 : ℕ)) : ℕ) : ℂ) *
              Ψ^1((ConjClasses.mk x).indicator) y) := by
            simpa using congrFun hz y
      _ = 0 := by
        simp [Representation.adamsOperator, hy_indicator]
  have hneq : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  exact hneq <| by simpa [hxz, hyz] using hEval

/-- Helper for Corollary 13-13.1-5: equal generated cyclic subgroups give a `Γ_ℚ(G)`-power twist
conjugate to the original element. -/
private theorem exists_gammaRat_conjugate_of_zpowers_eq
    {x y : G} (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    ∃ t : Γ_ℚ(G), IsConj x (y ^ t) := by
  have hconjSub :
      (Subgroup.zpowers x).IsConj (Subgroup.zpowers y) := by
    simpa [hxy] using Subgroup.IsConj.refl (Subgroup.zpowers x)
  exact (gammaRat_conjugate_iff_conjugate_zpowers x y).2 hconjSub

omit [Finite G] in
/-- Helper for Corollary 13-13.1-5: a `Γ_ℚ(G)`-power of an element generates the same cyclic
subgroup as the original element. -/
private theorem zpowers_pow_gammaRat_eq (x : G) (t : Γ_ℚ(G)) :
    Subgroup.zpowers (x ^ t) = Subgroup.zpowers x := by
  -- A `Γ_ℚ(G)`-power is an ordinary natural power, so it certainly lies in the original cyclic
  -- subgroup.
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    simp [pow_unit_eq_pow_nat]
  · rw [Subgroup.zpowers_le]
    have hcop_exp :
        (((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val).Coprime
          (Monoid.exponent G) :=
      ZMod.val_coe_unit_coprime (t : (ZMod (Monoid.exponent G))ˣ)
    have hcop_ord :
        (((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val).Coprime
          (orderOf x) :=
      Nat.Coprime.of_dvd_right (Monoid.order_dvd_exponent x) hcop_exp
    -- Because the exponent is invertible modulo `orderOf x`, the original generator is a power of
    -- `x ^ t`.
    simpa [pow_unit_eq_pow_nat] using
      (mem_zpowers_pow_iff.mpr hcop_ord :
        x ∈ Subgroup.zpowers
          (x ^ (((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val)))

omit [Finite G] in
/-- Helper for Corollary 13-13.1-5: if equal generated cyclic subgroups always force conjugacy,
then every ordinary character is invariant under the `Γ_ℚ(G)` power action. -/
private theorem character_power_invariant_of_same_subgroup_conjugacy
    (hconj :
      ∀ x y : G, Subgroup.zpowers x = Subgroup.zpowers y → IsConj x y)
    (χ : R(G)) (x : G) (t : Γ_ℚ(G)) :
    χ (x ^ t) = χ x := by
  let hχClass : _root_.IsClassFunction (χ : G → ℂ) :=
    Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ) χ χ.property
  -- The hypothesis converts equality of the generated cyclic subgroups into actual conjugacy.
  exact hχClass.eq_of_isConj (hconj (x ^ t) x (zpowers_pow_gammaRat_eq x t))

/-- Helper for Corollary 13-13.1-5: once every ordinary character is invariant under all
`Γ_ℚ(G)`-power maps, equality of generated cyclic subgroups already implies conjugacy. -/
private theorem same_subgroup_conjugate_of_all_characters_power_invariant
    (hpow : ∀ χ : R(G), ∀ x : G, ∀ t : Γ_ℚ(G), χ (x ^ t) = χ x)
    {x y : G} (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
    IsConj x y := by
  rcases exists_gammaRat_conjugate_of_zpowers_eq hxy with ⟨t, hxt⟩
  -- Character values identify conjugacy classes, so it is enough to compare values at `x` and
  -- `y`.
  refine isConj_of_character_values_eq ?_
  intro χ
  have hχClass : _root_.IsClassFunction (χ : G → ℂ) :=
    Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ) χ χ.property
  calc
    χ x = χ (y ^ t) := by
      simpa using hχClass.eq_of_isConj hxt
    _ = χ y := hpow χ y t

/-- Helper for Corollary 13-13.1-5: every ordinary complex character is realized over the
cyclotomic field of exponent `Monoid.exponent G`. -/
private theorem ordinary_character_lift_to_cyclotomic
    (χ : R(G)) :
    ∃ χL : R[Lexp](G),
      ∀ g : G,
        algebraMap Lexp ℂ (χL g) = χ g := by
  letI := cyclotomicFieldExponent_hasEnoughRootsOfUnity (G := G)
  -- The Chapter `12` realization theorem identifies ordinary characters with the complex image of
  -- `R[Lexp](G)`.
  have hmem : (χ : G → ℂ) ∈ Representation.characterRingOverFieldInExtension Lexp ℂ G := by
    rw [Representation.characterRingOverFieldInExtension_eq_characterRing_of_hasEnoughRootsOfUnity
      (K := Lexp) (G := G)]
    exact χ.property
  rcases Subalgebra.mem_map.mp hmem with ⟨χL, hχL, hmap⟩
  refine ⟨⟨χL, hχL⟩, ?_⟩
  intro g
  -- Unpack the coefficientwise equality from the `Subalgebra.map` witness.
  simpa using congrFun hmap g

/-- Helper for Corollary 13-13.1-5: for a linear character on a subgroup of `G`, the cyclotomic
Galois action attached to `Γ[(⊥)]` acts on the value at `g` by the expected power map. -/
private theorem linear_character_value_galois_compatible_at_generator
    {H : Subgroup G} (g : H) (β : H →* Lexpˣ)
    (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)) :
    t • ((β g : Lexpˣ) : Lexp) =
      ((β (g ^ Representation.galoisPowerExponentUnit
        (t : (ZMod (Monoid.exponent G))ˣ)) : Lexpˣ) : Lexp) := by
  let n : ℕ := Representation.galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)
  let σ : Gal(Lexp / ℚ) :=
    (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
      (t : (ZMod (Monoid.exponent G))ˣ)
  have hgpow : g ^ Monoid.exponent G = 1 := by
    -- The ambient exponent kills every subgroup element as well.
    apply Subtype.ext
    exact Monoid.pow_exponent_eq_one (g : G)
  have hβpow_units : (β g) ^ Monoid.exponent G = 1 := by
    -- Linear-character values are therefore `exp(G)`-th roots of unity.
    rw [← map_pow]
    simp [hgpow]
  have hβpow : (((β g : Lexpˣ) : Lexp) ^ Monoid.exponent G) = 1 := by
    exact congrArg (fun u : Lexpˣ ↦ (u : Lexp)) hβpow_units
  have hσunit :
      IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ =
        (t : (ZMod (Monoid.exponent G))ˣ) := by
    exact
      MulEquiv.apply_symm_apply
        (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp) _
  change σ (((β g : Lexpˣ) : Lexp)) = ((β (g ^ n) : Lexpˣ) : Lexp)
  calc
    σ (((β g : Lexpˣ) : Lexp)) =
        ((β g : Lexpˣ) : Lexp) ^
          ((IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ).val.val) := by
            simpa using
              (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := Monoid.exponent G) (K := Lexp) σ hβpow)
    _ = ((β g : Lexpˣ) : Lexp) ^ n := by
      simp [hσunit, n, Representation.galoisPowerExponentUnit]
    _ = (((β g) ^ n : Lexpˣ) : Lexp) := by
      simp
    _ = ((β (g ^ n) : Lexpˣ) : Lexp) := by
      rw [β.map_pow]

omit [Finite G] in
/-- Helper for Corollary 13-13.1-5: an irreducible representation has a nontrivial carrier. -/
private theorem irreducible_representation_nontrivial_local
    {H : Type*} [Group H] {K : Type*} [Field K]
    {W : Type*} [AddCommGroup W] [Module K W]
    (τ : Representation K H W) [τ.IsIrreducible] : Nontrivial W := by
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top : (⊥ : Subrepresentation τ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext w
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim w 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Corollary 13-13.1-5: on the cyclic subgroup generated by `x`, every
`Lexp`-valued virtual character satisfies the expected `Γ[(⊥)]`-compatibility at the
distinguished generator. -/
private theorem zpowers_restricted_character_galois_compatible
    (x : G) (ψ : R[Lexp](Subgroup.zpowers x))
    (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)) :
    let g0 : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩
    t • ψ g0 =
      ψ (g0 ^ Representation.galoisPowerExponentUnit
        (t : (ZMod (Monoid.exponent G))ˣ)) := by
  let C : Subgroup G := Subgroup.zpowers x
  let g0 : C := ⟨x, Subgroup.mem_zpowers x⟩
  let n : ℕ := Representation.galoisPowerExponentUnit (t : (ZMod (Monoid.exponent G))ˣ)
  change t • ψ g0 = ψ (g0 ^ n)
  -- Restrict to the adjoin presentation of `R[Lexp](C)` and prove the identity on generators.
  refine Algebra.adjoin_induction (p := fun φ _ ↦ t • φ g0 = φ (g0 ^ n)) ?_ ?_ ?_ ?_ ψ.property
  · intro φ hφ
    rcases hφ with ⟨ρ, hρfd, hρirr, rfl⟩
    letI : FiniteDimensional Lexp ρ := hρfd
    letI : ρ.ρ.IsIrreducible := hρirr
    letI : Nontrivial ρ := irreducible_representation_nontrivial_local ρ.ρ
    haveI : Nontrivial (ρ →ₗ[Lexp] ρ) := inferInstance
    letI : IsMulCommutative C := Subgroup.zpowers_isMulCommutative x
    letI : HasEnoughRootsOfUnity Lexp (Monoid.exponent G) :=
      cyclotomicFieldExponent_hasEnoughRootsOfUnity (G := G)
    have horder_div_exp : orderOf g0 ∣ Monoid.exponent G := by
      simpa [Subgroup.orderOf_coe] using Monoid.order_dvd_exponent (g0 : G)
    haveI : HasEnoughRootsOfUnity Lexp (orderOf g0) := by
      exact HasEnoughRootsOfUnity.of_dvd Lexp horder_div_exp
    let f : Module.End Lexp ρ := ρ.ρ g0
    have h_ann :
        Polynomial.aeval f (Polynomial.X ^ orderOf g0 - 1 : Polynomial Lexp) = 0 := by
      have hpow : f ^ orderOf g0 = 1 := by
        change ρ.ρ g0 ^ orderOf g0 = 1
        simpa [f, pow_orderOf_eq_one] using (ρ.ρ.map_pow g0 (orderOf g0)).symm
      simp [hpow, f]
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Lexp (orderOf g0)
    have hsplit :
        (Polynomial.X ^ orderOf g0 - 1 : Polynomial Lexp).Splits := by
      simpa using Polynomial.X_pow_sub_one_splits hζ
    have hsplit_min :
        (minpoly Lexp f).Splits := by
      apply Polynomial.Splits.of_dvd hsplit
      · simpa using Polynomial.X_pow_sub_C_ne_zero (show 0 < orderOf g0 by exact orderOf_pos g0)
          (1 : Lexp)
      · rw [minpoly.dvd_iff]
        exact h_ann
    have hμdeg : (minpoly Lexp f).degree ≠ 0 := by
      exact ne_of_gt (minpoly.degree_pos (LinearMap.isIntegral f))
    let μ : Lexp := Polynomial.rootOfSplits hsplit_min hμdeg
    have hμroot : (minpoly Lexp f).IsRoot μ := by
      exact Polynomial.eval_rootOfSplits hsplit_min hμdeg
    have hμeig : Module.End.HasEigenvalue f μ := Module.End.hasEigenvalue_of_isRoot hμroot
    let E : Subrepresentation ρ.ρ :=
      { toSubmodule := Module.End.eigenspace f μ
        apply_mem_toSubmodule := by
          intro h w hw
          rw [Module.End.mem_eigenspace_iff] at hw ⊢
          have hcomm : Commute f (ρ.ρ h) := by
            change ρ.ρ g0 * ρ.ρ h = ρ.ρ h * ρ.ρ g0
            calc
              ρ.ρ g0 * ρ.ρ h = ρ.ρ (g0 * h) := by simpa using (ρ.ρ.map_mul g0 h).symm
              _ = ρ.ρ (h * g0) := by congr 1; exact mul_comm' g0 h
              _ = ρ.ρ h * ρ.ρ g0 := by simpa using (ρ.ρ.map_mul h g0)
          have hcomm_apply : f ((ρ.ρ h) w) = (ρ.ρ h) (f w) := by
            simpa using LinearMap.congr_fun hcomm.eq w
          calc
            f ((ρ.ρ h) w) = (ρ.ρ h) (f w) := hcomm_apply
            _ = (ρ.ρ h) (μ • w) := by rw [hw]
            _ = μ • (ρ.ρ h w) := by simp }
    have hE_ne : E ≠ ⊥ := by
      intro hE
      exact (Module.End.hasEigenvalue_iff.mp hμeig) <| by
        simpa [E] using congrArg Subrepresentation.toSubmodule hE
    have hE_top : E = ⊤ := by
      exact (IsSimpleOrder.bot_lt_iff_eq_top).1 (bot_lt_iff_ne_bot.mpr hE_ne)
    have hf_scalar : f = μ • (1 : ρ →ₗ[Lexp] ρ) := by
      ext w
      have hw : w ∈ E := by
        rw [hE_top]
        exact Submodule.mem_top
      exact (Module.End.mem_eigenspace_iff.mp hw)
    have hμpow : μ ^ orderOf g0 = 1 := by
      have hroot_pow :
          (Polynomial.X ^ orderOf g0 - 1 : Polynomial Lexp).IsRoot μ :=
        hμroot.dvd (by rw [minpoly.dvd_iff]; exact h_ann)
      simpa [Polynomial.IsRoot, sub_eq_zero] using hroot_pow
    have hμcompat : t • μ = μ ^ n := by
      let σ : Gal(Lexp / ℚ) :=
        (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
          (t : (ZMod (Monoid.exponent G))ˣ)
      have hσunit :
          IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ =
            (t : (ZMod (Monoid.exponent G))ˣ) := by
        exact
          MulEquiv.apply_symm_apply
            (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp) _
      change σ μ = μ ^ n
      have hμexp : μ ^ Monoid.exponent G = 1 := by
        rcases horder_div_exp with ⟨k, hk⟩
        calc
          μ ^ Monoid.exponent G = μ ^ (orderOf g0 * k) := by simpa [hk]
          _ = (μ ^ orderOf g0) ^ k := by rw [pow_mul]
          _ = 1 := by simp [hμpow]
      calc
        σ μ =
            μ ^
              ((IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ).val.val) := by
                simpa using
                  (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                    (n := Monoid.exponent G) (K := Lexp) σ hμexp)
        _ = μ ^ n := by
          simp [hσunit, n, Representation.galoisPowerExponentUnit]
    have hchar_g0 :
        ρ.ρ.character g0 = μ * (Module.finrank Lexp ρ : Lexp) := by
      change LinearMap.trace Lexp ρ f = μ * (Module.finrank Lexp ρ : Lexp)
      rw [hf_scalar]
      simp [LinearMap.trace_id, mul_comm]
    have hlsmul_pow (a : Lexp) (m : ℕ) :
        (a • (1 : ρ →ₗ[Lexp] ρ)) ^ m = a ^ m • (1 : ρ →ₗ[Lexp] ρ) := by
      induction m with
      | zero =>
          ext w
          simp
      | succ m ihm =>
          rw [pow_succ, ihm]
          ext w
          simp [pow_succ, smul_smul, mul_assoc, mul_left_comm, mul_comm]
    have hf_pow_scalar : ρ.ρ (g0 ^ n) = μ ^ n • (1 : ρ →ₗ[Lexp] ρ) := by
      calc
        ρ.ρ (g0 ^ n) = (ρ.ρ g0) ^ n := by simpa using (ρ.ρ.map_pow g0 n).symm
        _ = f ^ n := rfl
        _ = (μ • (1 : ρ →ₗ[Lexp] ρ)) ^ n := by rw [hf_scalar]
        _ = μ ^ n • (1 : ρ →ₗ[Lexp] ρ) := hlsmul_pow μ n
    have hchar_pow :
        ρ.ρ.character (g0 ^ n) = μ ^ n * (Module.finrank Lexp ρ : Lexp) := by
      rw [Representation.character, hf_pow_scalar]
      simp [LinearMap.trace_id, mul_comm]
    have hfinrank_fixed :
        t • (Module.finrank Lexp ρ : Lexp) = (Module.finrank Lexp ρ : Lexp) := by
      change
        (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
            (t : (ZMod (Monoid.exponent G))ˣ) (algebraMap ℚ Lexp (Module.finrank Lexp ρ)) =
          algebraMap ℚ Lexp (Module.finrank Lexp ρ)
      simpa using
        AlgEquiv.commutes
          ((IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
            (t : (ZMod (Monoid.exponent G))ˣ)) (Module.finrank Lexp ρ : ℚ)
    -- The generator acts by a scalar root of unity, so the cyclotomic action sends its trace to
    -- the trace at the corresponding power.
    calc
      t • ρ.ρ.character g0 = t • (μ * (Module.finrank Lexp ρ : Lexp)) := by rw [hchar_g0]
      _ = (t • μ) * (t • (Module.finrank Lexp ρ : Lexp)) := by rw [smul_mul']
      _ = μ ^ n * (Module.finrank Lexp ρ : Lexp) := by
        rw [hμcompat, hfinrank_fixed]
      _ = ρ.ρ.character (g0 ^ n) := hchar_pow.symm
  · intro m
    -- Integer constants are fixed by the cyclotomic action.
    change
      (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
          (t : (ZMod (Monoid.exponent G))ˣ) (algebraMap ℚ Lexp m) =
        algebraMap ℚ Lexp m
    simpa using
      AlgEquiv.commutes
        ((IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
          (t : (ZMod (Monoid.exponent G))ˣ)) (m : ℚ)
  · intro φ ψ _ _ hφ hψ
    -- The compatibility identity is preserved by addition in the character ring.
    calc
      t • (φ + ψ) g0 = t • (φ g0 + ψ g0) := by rfl
      _ = t • φ g0 + t • ψ g0 := by rw [smul_add]
      _ = φ (g0 ^ n) + ψ (g0 ^ n) := by rw [hφ, hψ]
      _ = (φ + ψ) (g0 ^ n) := by rfl
  · intro φ ψ _ _ hφ hψ
    -- The compatibility identity is also preserved by multiplication.
    calc
      t • (φ * ψ) g0 = t • (φ g0 * ψ g0) := by rfl
      _ = t • φ g0 * (t • ψ g0) := by rw [smul_mul']
      _ = φ (g0 ^ n) * ψ (g0 ^ n) := by rw [hφ, hψ]
      _ = (φ * ψ) (g0 ^ n) := by rfl

/-- Helper for Corollary 13-13.1-5: on the cyclic subgroup generated by `x`, ordinary
`Lexp`-valued characters are compatible with the `Γ_ℚ(G)` power action at the distinguished
generator. -/
private theorem zpowers_generator_galois_compatible_of_mem_characterRingOverField
    (x : G) (χL : R[Lexp](G)) (t : Γ[(⊥ : IntermediateField ℚ Lexp)](G)) :
    t • χL x = χL (x ^ t) := by
  let C : Subgroup G := Subgroup.zpowers x
  let χC : R[Lexp](C) :=
    ⟨fun h : C ↦ (χL : G → Lexp) h,
      restrict_mem_characterRingOverField_local (K := Lexp) C χL⟩
  -- Restrict to `⟨x⟩`, prove compatibility there at the distinguished generator, then simplify
  -- the subgroup-valued power back to the ambient power `x ^ t`.
  simpa [χC, C, Representation.pow_subgroup_eq_pow_nat, Representation.pow_unit_eq_pow_nat] using
    zpowers_restricted_character_galois_compatible (G := G) x χC t

/-- Helper for Corollary 13-13.1-5: if an ordinary character is rational-valued at every group
element, then it is invariant under all `Γ_ℚ(G)` power maps. -/
private theorem ordinary_character_power_invariant_of_rational_values
    (χ : R(G)) (hχQ : ∀ x : G, IsLocalization.IsInteger ℚ (χ x))
    (x : G) (t : Γ_ℚ(G)) :
    χ (x ^ t) = χ x := by
  letI : NumberField Lexp := inferInstance
  letI : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
    CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)
  rcases ordinary_character_lift_to_cyclotomic (G := G) χ with ⟨χL, hχL⟩
  have hGammaBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) = ⊤ := by
    -- Over the bottom field `ℚ`, the cyclotomic Galois subgroup is the whole unit group.
    unfold Representation.gammaSubgroup
    letI : IsGalois ℚ Lexp := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ Lexp
    have hfixingSubgroupBot : (⊥ : IntermediateField ℚ Lexp).fixingSubgroup = ⊤ :=
      IsGaloisGroup.fixingSubgroup_bot (G := Gal(Lexp / ℚ)) (K := ℚ) (L := Lexp)
    rw [hfixingSubgroupBot]
    simp
  let tBot : Γ[(⊥ : IntermediateField ℚ Lexp)](G) := ⟨t, by simp [hGammaBot]⟩
  have hcompat :
      tBot • χL x = χL (x ^ t) := by
    -- Route correction: isolate the missing cyclic-subgroup compatibility as a single dedicated
    -- helper and use it only at the distinguished generator `x`.
    simpa [tBot, Representation.pow_subgroup_eq_pow_nat, Representation.pow_unit_eq_pow_nat] using
      zpowers_generator_galois_compatible_of_mem_characterRingOverField
        (G := G) x χL tBot
  rcases hχQ x with ⟨q, hq⟩
  have hχLq : χL x = algebraMap ℚ Lexp q := by
    -- Compare inside `ℂ`; injectivity of `L → ℂ` identifies the lifted scalar with a rational one.
    apply (algebraMap Lexp ℂ).injective
    calc
      algebraMap Lexp ℂ (χL x) = χ x := hχL x
      _ = algebraMap ℚ ℂ q := hq.symm
      _ = algebraMap Lexp ℂ (algebraMap ℚ Lexp q) := by simp
  have hfixed : tBot • χL x = χL x := by
    -- Rational scalars lie in the bottom field, so every element of its fixing subgroup acts
    -- trivially on them.
    have ht_fix :
        (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
            (tBot : (ZMod (Monoid.exponent G))ˣ) ∈
          (⊥ : IntermediateField ℚ Lexp).fixingSubgroup := by
      exact (Subgroup.mem_map_equiv.mp tBot.2 : _)
    have hq_bot : algebraMap ℚ Lexp q ∈ (⊥ : IntermediateField ℚ Lexp) := by
      exact IntermediateField.mem_bot.mpr ⟨q, rfl⟩
    rw [hχLq]
    change
      (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
          (tBot : (ZMod (Monoid.exponent G))ˣ) (algebraMap ℚ Lexp q) =
        algebraMap ℚ Lexp q
    exact
      (IntermediateField.mem_fixingSubgroup_iff (⊥ : IntermediateField ℚ Lexp) _).1 ht_fix
        _ hq_bot
  -- Map the cyclotomic compatibility identity back to the original complex-valued character.
  calc
    χ (x ^ t) = algebraMap Lexp ℂ (χL (x ^ t)) := by
      symm
      simpa using hχL (x ^ t)
    _ = algebraMap Lexp ℂ (tBot • χL x) := by rw [hcompat.symm]
    _ = algebraMap Lexp ℂ (χL x) := by rw [hfixed]
    _ = χ x := hχL x

/-- Helper for Corollary 13-13.1-5: if an ordinary character is invariant under every
`Γ_ℚ(G)` power map, then each of its values already lies in `ℚ`. -/
private theorem ordinary_character_value_rational_of_power_invariant
    (χ : R(G)) (hpow : ∀ x : G, ∀ t : Γ_ℚ(G), χ (x ^ t) = χ x)
    (x : G) :
    IsLocalization.IsInteger ℚ (χ x) := by
  letI : NumberField Lexp := inferInstance
  letI : FiniteDimensional ℚ Lexp := inferInstance
  letI : IsGalois ℚ Lexp := IsCyclotomicExtension.isGalois {Monoid.exponent G} ℚ Lexp
  rcases ordinary_character_lift_to_cyclotomic (G := G) χ with ⟨χL, hχL⟩
  have hfixed :
      ∀ t : Γ[(⊥ : IntermediateField ℚ Lexp)](G), t • χL x = χL x := by
    intro t
    have hcompat : t • χL x = χL (x ^ t) := by
      -- Route correction: only the generator-compatibility bridge remains open here.
      simpa using
        zpowers_generator_galois_compatible_of_mem_characterRingOverField
          (G := G) x χL t
    have hpow_t : χ (x ^ t) = χ x := by
      -- Route correction: rewrite the subgroup power action back to the ambient `Γ_ℚ(G)` action.
      simpa [Representation.pow_subgroup_eq_pow_nat, Representation.pow_unit_eq_pow_nat] using
        hpow x (t : Γ_ℚ(G))
    -- Inject the compatibility equality into `ℂ` and use the assumed power-invariance there.
    apply (algebraMap Lexp ℂ).injective
    calc
      algebraMap Lexp ℂ (t • χL x) = algebraMap Lexp ℂ (χL (x ^ t)) := by rw [hcompat]
      _ = χ (x ^ t) := by simpa using hχL (x ^ t)
      _ = χ x := hpow_t
      _ = algebraMap Lexp ℂ (χL x) := by simpa using (hχL x).symm
  have hχLx_fixed :
      χL x ∈ IntermediateField.fixedField ((⊥ : IntermediateField ℚ Lexp).fixingSubgroup) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have ht_mem :
        IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ ∈
          Γ[(⊥ : IntermediateField ℚ Lexp)](G) := by
      have hσ_fix :
          (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
              (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ) ∈
            (⊥ : IntermediateField ℚ Lexp).fixingSubgroup := by
        simpa using hσ
      exact
        (Subgroup.mem_map_equiv.mpr hσ_fix :
          IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ ∈
            Γ[(⊥ : IntermediateField ℚ Lexp)](G))
    let t : Γ[(⊥ : IntermediateField ℚ Lexp)](G) :=
      ⟨IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp σ, ht_mem⟩
    have ht_fixed : t • χL x = χL x := hfixed t
    have ht_eq :
        (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
            (t : (ZMod (Monoid.exponent G))ˣ) = σ := by
      simpa [t] using
        (MulEquiv.symm_apply_apply
          (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp) σ)
    change
      (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).symm
          (t : (ZMod (Monoid.exponent G))ˣ) (χL x) =
        χL x at ht_fixed
    simpa [ht_eq] using ht_fixed
  have hχLx_bot : χL x ∈ (⊥ : IntermediateField ℚ Lexp) := by
    simpa [IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField ℚ Lexp)] using hχLx_fixed
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hχLx_bot
  -- The fixed-field theorem identifies the bottom field with `ℚ`, so the lifted value comes from
  -- an actual rational scalar.
  refine ⟨q, ?_⟩
  calc
    algebraMap ℚ ℂ q = algebraMap Lexp ℂ (χL x) := by
      rw [← hq]
      simp
    _ = χ x := hχL x

/- Source/core/bridge triage:
- `source-facing`: this corollary is the textbook three-way equivalence.
- `core/canonical`: the actual owner declarations behind the three clauses are
  `Representation.char_isIntegral`,
  `rational_valued_classFunction_mem_rational_character_ring_iff_power_invariant`, and
  `gammaRat_conjugate_iff_conjugate_zpowers`.
- `bridge/view`: the present `List.TFAE` packaging is the source-facing comparison layer between
  those owners; it should not introduce a parallel local notion of rationality, integrality, or
  cyclic-subgroup power-conjugacy.

Primitive data:
- the character ring owner `R(G)` and the pointwise value predicates.

Derived API:
- rational-valued and integer-valued are the canonical `IsLocalization.IsInteger` predicates;
  the cyclic-subgroup clause is the source-facing equality of generated subgroups. -/

-- Proof sketch: `Representation.char_isIntegral` shows every virtual-character value is an
-- algebraic integer, so the first two clauses are equivalent because a rational algebraic integer
-- is an integer. Theorem `rational_valued_classFunction_mem_rational_character_ring_iff_power_
-- invariant` gives the power-invariance criterion for rational values, and
-- `gammaRat_conjugate_iff_conjugate_zpowers` translates that condition into conjugacy of
-- generators of the same cyclic subgroup.
/-- Corollary 13-13.1-5: the following are equivalent for a finite group `G`: every element of
Serre's integral character ring `R(G)` is rational-valued, every element of `R(G)` is
integer-valued, and any two elements generating the same cyclic subgroup are conjugate. -/
theorem character_values_rational_integer_and_same_subgroup_conjugacy_tfae :
    [ (∀ χ : R(G), ∀ x : G, IsLocalization.IsInteger ℚ (χ x)),
      (∀ χ : R(G), ∀ x : G, IsLocalization.IsInteger ℤ (χ x)),
      (∀ x y : G, Subgroup.zpowers x = Subgroup.zpowers y → IsConj x y) ].TFAE := by
  have h_integral : ∀ χ : R(G), ∀ x : G, IsIntegral ℤ (χ x) := by
    intro χ x
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
    · rintro ψ ⟨ρ, hρfd, hρirr, rfl⟩
      letI : FiniteDimensional ℂ ρ := hρfd
      simpa using Representation.char_isIntegral ρ.ρ x
    · intro n
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ n))
    · intro f g _ _ hf hg
      exact hf.add hg
    · intro f g _ _ hf hg
      exact hf.mul hg
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h χ x
      have hrat : ∃ q : ℚ, χ x = q := by
        rcases h χ x with ⟨q, hq⟩
        exact ⟨q, hq.symm⟩
      rcases (IsIntegral.exists_int_iff_exists_rat (h_integral χ x)).mp hrat with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    · intro h χ x
      rcases h χ x with ⟨n, hn⟩
      refine ⟨(n : ℚ), ?_⟩
      simpa using hn
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h x y hxy
      have hpow : ∀ χ : R(G), ∀ z : G, ∀ t : Γ_ℚ(G), χ (z ^ t) = χ z := by
        intro χ z t
        -- Route correction: this is the exact owner-level bridge from clause `1` to the
        -- power-invariance criterion used in the subgroup-conjugacy endgame.
        exact ordinary_character_power_invariant_of_rational_values χ (h χ) z t
      -- The remaining `1 → 3` endgame is now a pure character-separation argument.
      exact same_subgroup_conjugate_of_all_characters_power_invariant hpow hxy
    · intro h χ x
      have hpow : ∀ t : Γ_ℚ(G), χ (x ^ t) = χ x := by
        intro t
        -- Under clause `3`, powers by `Γ_ℚ(G)` preserve the conjugacy class because they preserve
        -- the generated cyclic subgroup.
        exact character_power_invariant_of_same_subgroup_conjugacy h χ x t
      -- Route correction: the converse packages the remaining fixed-field step as a single
      -- helper, so the main TFAE proof now depends only on the genuine arithmetic bridge.
      exact ordinary_character_value_rational_of_power_invariant χ
        (fun y t ↦ character_power_invariant_of_same_subgroup_conjugacy h χ y t) x
  tfae_finish

end
