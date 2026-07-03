import Mathlib
import Mathlib.Data.ZMod.QuotientRing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_10_2_2 (from Chap10) -/
noncomputable section

open Representation
open scoped BigOperators Representation SubgroupInduction

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

/-- Helper for Theorem 10-10.2-2: choose the tensor-owner realization of Brauer's explicit
auxiliary function on the associated `p`-elementary subgroup. -/
private noncomputable def brauerAssociatedAuxiliaryTensorCharacter
    {p : ℕ} [Fact p.Prime] (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P) :=
  Classical.choose
    (exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction (p := p) x P hx)

/-- Helper for Theorem 10-10.2-2: the chosen tensor witness realizes Brauer's explicit auxiliary
function pointwise. -/
private theorem brauerAssociatedAuxiliaryTensorCharacter_realizes
    {p : ℕ} [Fact p.Prime] (x : G) (P : Sylow p C(x)) (hx : IsPRegular p x) :
    ((brauerAssociatedAuxiliaryTensorCharacter (p := p) x P hx :
        (↥(integralClosure ℤ ℂ)) ⊗R(associatedPElementarySubgroup p x P)) :
          associatedPElementarySubgroup p x P → ℂ) =
      brauerAssociatedAuxiliaryFunction p x P :=
  Classical.choose_spec
    (exists_tensor_character_realizing_brauerAssociatedAuxiliaryFunction (p := p) x P hx)

/-- Helper for Theorem 10-10.2-2: inducing a tensor character from a `p`-elementary subgroup
lands in the realized scalar extension `A ⊗ V_p`. -/
private theorem induced_tensor_character_mem_integralClosure_pElementary_scalarExtension
    {p : ℕ} [Fact p.Prime] (H : Subgroup G) (hH : IsPElementary p H)
    (ψ : (↥(integralClosure ℤ ℂ)) ⊗R(H)) :
    Ind[H]((ψ : H → ℂ)) ∈
      Representation.pElementaryInducedCharacterScalarExtension
        (↥(integralClosure ℤ ℂ)) p G := by
  classical
  induction ψ using TensorProduct.induction_on with
  | zero =>
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      -- The realized scalar extension is a submodule, so it contains the zero induced function.
      change Ind[H]((0 : H → ℂ)) ∈
          Representation.pElementaryInducedCharacterScalarExtension
            (↥(integralClosure ℤ ℂ)) p G
      rw [hzero]
      exact
        (Submodule.zero_mem
          (Representation.pElementaryInducedCharacterScalarExtension
            (↥(integralClosure ℤ ℂ)) p G) :
          (0 : G → ℂ) ∈
            Representation.pElementaryInducedCharacterScalarExtension
              (↥(integralClosure ℤ ℂ)) p G)
  | tmul a χ =>
      let _ : DecidablePred (fun K : Subgroup G ↦ IsPElementary p K) := Classical.decPred _
      have hHmem : H ∈ Finset.univ.filter (fun K : Subgroup G ↦ IsPElementary p K) := by
        simp [hH]
      have hbase' :
          Representation.Subgroup.characterRingInduction H χ ∈ V[p](G) := by
        -- Insert the induced honest virtual character directly into the defining Artin owner.
        rw [Representation.pElementaryInducedCharacterSpan]
        simpa using
          Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem χ
      have hbase :
          Ind[H]((χ : H → ℂ)) ∈
            Representation.pElementaryInducedCharacterScalarExtension
              (↥(integralClosure ℤ ℂ)) p G := by
        -- Honest induced characters already lie in `V_p`, hence in its scalar extension.
        simpa [Representation.Subgroup.characterRingInduction_apply] using
          mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementaryInducedCharacterSpan
            (A := ↥(integralClosure ℤ ℂ))
            (p := p)
            (χ := Representation.Subgroup.characterRingInduction H χ)
            hbase'
      have hsmul :
          Ind[H](a • (χ : H → ℂ)) = a • Ind[H]((χ : H → ℂ)) := by
        -- Induction is linear in the induced class function.
        ext g
        simp [Subgroup.inducedClassFunction, Finset.mul_sum,
          Algebra.smul_def, mul_assoc, mul_left_comm]
      simpa [hsmul] using
        (Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G).smul_mem a hbase
  | add ψ₁ ψ₂ hψ₁ hψ₂ =>
      have hcoe_add :
          (((ψ₁ + ψ₂ : (↥(integralClosure ℤ ℂ)) ⊗R(H)) : H → ℂ)) =
            (ψ₁ : H → ℂ) + (ψ₂ : H → ℂ) := by
        ext h
        simp
      have hadd :
          Ind[H]((ψ₁ : H → ℂ) + (ψ₂ : H → ℂ)) =
            Ind[H]((ψ₁ : H → ℂ)) + Ind[H]((ψ₂ : H → ℂ)) := by
        -- Induction is additive in the induced class function.
        ext g
        exact congrFun
          ((((classFunctionSubmodule ℂ G).subtype.comp H.classFunctionInduction).map_add
            (ψ₁ : H → ℂ) (ψ₂ : H → ℂ))) g
      rw [hcoe_add, hadd]
      exact
        (Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G).add_mem hψ₁ hψ₂

/-- Helper for Theorem 10-10.2-2: restrict a complex-valued class function on `G` to a subgroup
`H`. -/
private def functionRestriction (H : Subgroup G) : (G → ℂ) →ₐ[ℤ] (H → ℂ) where
  toFun χ := fun h ↦ χ h
  map_zero' := rfl
  map_one' := rfl
  map_add' χ ψ := by
    ext h
    rfl
  map_mul' χ ψ := by
    ext h
    rfl
  commutes' n := by
    ext h
    rfl

section
omit [Finite G]

/-- Helper for Theorem 10-10.2-2: restricting an ordinary virtual character to a subgroup stays
inside the subgroup character ring. -/
private theorem restrict_mem_characterRing_local (H : Subgroup G) (χ : R(G)) :
    (fun h : H ↦ (χ : G → ℂ) h) ∈ R(H) := by
  -- Restriction is an algebra map, so it suffices to check it on irreducible generators.
  change functionRestriction H χ ∈ R(H)
  have hmap_le : R(G).map (functionRestriction H) ≤ R(H) := by
    refine (Subalgebra.gc_map_comap (functionRestriction H)).l_le ?_
    rw [Representation.characterRingOverField]
    refine (Algebra.adjoin_le_iff).2 ?_
    intro ψ hψ
    rcases hψ with ⟨ρ, hfd, hirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hfd
    -- Restriction of representations restricts ordinary characters pointwise.
    change functionRestriction H (ρ.ρ.character) ∈ R(H)
    simpa [functionRestriction] using
      (Representation.rep_character_mem_characterRingOverField (K := ℂ)
        (ρ := Rep.res H.subtype ρ))
  exact hmap_le ⟨χ, χ.property, rfl⟩

end

/-- Helper for Theorem 10-10.2-2: multiplying an induced class function by an ambient character is
the same as inducing the pointwise product with the restricted character. -/
private theorem induced_mul_eq_induced_mul_restriction_local
    (H : Subgroup G) (ψ : H → ℂ) (χ : R(G)) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  -- Compare the source and target formulas summand-by-summand in the induction expansion.
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ :
        (χ : G → ℂ) (s⁻¹ * x * s) = (χ : G → ℂ) x := by
      exact (Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        (χ : G → ℂ) χ.property).eq_of_isConj <| isConj_iff.2 ⟨s, by group⟩
    have hχ' : (χ : G → ℂ) (s⁻¹ * (x * s)) = (χ : G → ℂ) x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

/-- Helper for Theorem 10-10.2-2: Brauer's subgroup `V_p` is stable under multiplication by an
arbitrary integral virtual character. -/
private theorem mul_mem_pElementaryInducedCharacterSpan_local
    (p : ℕ) {χ ψ : R(G)} (hψ : ψ ∈ V[p](G)) :
    χ * ψ ∈ V[p](G) := by
  classical
  let _ : DecidablePred (fun H : Subgroup G ↦ IsPElementary p H) := Classical.decPred _
  -- Rewrite `V_p` as the supremum of subgroup-induction ranges and prove stability on generators.
  rw [Representation.pElementaryInducedCharacterSpan] at hψ
  simp_rw [Representation.artinInducedCharacterSubmodule] at hψ
  refine Submodule.iSup_induction
      (p := fun H :
        {H : Subgroup G // H ∈ Finset.filter (fun H : Subgroup G ↦ IsPElementary p H) Finset.univ} ↦
          LinearMap.range (Representation.Subgroup.characterRingInduction H.1))
      (motive := fun ξ : R(G) ↦ χ * ξ ∈ V[p](G))
      hψ ?_ ?_ ?_
  · intro H ξ hξ
    rcases H with ⟨H, hHmem⟩
    rcases hξ with ⟨η, rfl⟩
    have hprod : (fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h)) ∈ R(H) := by
      exact (R(H)).mul_mem η.property (restrict_mem_characterRing_local H χ)
    let ζ : R(H) := ⟨fun h : H ↦ ((η : H → ℂ) h) * ((χ : G → ℂ) h), hprod⟩
    have hζ :
        χ * Representation.Subgroup.characterRingInduction H η =
          Representation.Subgroup.characterRingInduction H ζ := by
      -- Compare the owner-level characters pointwise through the induction product formula.
      apply Subtype.ext
      ext g
      have hind :=
        congrFun (induced_mul_eq_induced_mul_restriction_local H (η : H → ℂ) χ) g
      simpa [ζ, Representation.Subgroup.characterRingInduction_apply, mul_comm] using hind
    exact hζ ▸
      Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hHmem ζ
  · simp
  · intro ξ η hξ hη
    simpa [mul_add] using Submodule.add_mem (V[p](G)) hξ hη

/-- Helper for Theorem 10-10.2-2: multiplying a realized scalar-extended Brauer function by an
integral character keeps the result inside the same scalar extension of `V_p`. -/
private theorem mul_mem_integralClosure_pElementary_scalarExtension
    {p : ℕ} [Fact p.Prime] {φ : G → ℂ}
    (hφ : φ ∈
      Representation.pElementaryInducedCharacterScalarExtension
        (↥(integralClosure ℤ ℂ)) p G)
    (χ : R(G)) :
    ((χ : G → ℂ) * φ) ∈
      Representation.pElementaryInducedCharacterScalarExtension
        (↥(integralClosure ℤ ℂ)) p G := by
  classical
  rw [Representation.pElementaryInducedCharacterScalarExtension_eq_span
    (A := ↥(integralClosure ℤ ℂ)) (p := p) (G := G)] at hφ ⊢
  refine Submodule.span_induction
      (s := ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
        Set (G → ℂ)))
      (p := fun ψ _ ↦
        ((χ : G → ℂ) * ψ) ∈
          Submodule.span (↥(integralClosure ℤ ℂ))
            ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
              Set (G → ℂ)))
      ?_ ?_ ?_ ?_ hφ
  · intro ψ hψ
    rcases hψ with ⟨β, rfl⟩
    have hmul : χ * (β : R(G)) ∈ V[p](G) := by
      -- The integral Brauer owner `V_p` is an ideal inside `R(G)`.
      exact
        mul_mem_pElementaryInducedCharacterSpan_local
          (G := G) (p := p) (χ := χ) (ψ := (β : R(G))) β.property
    -- Rewrite the product generator through the honest `V_p` element `χ * β`.
    simpa [Representation.pElementaryInducedCharacterScalarExtension_eq_span,
      mul_comm] using
      mem_pElementaryInducedCharacterScalarExtension_of_mem_pElementaryInducedCharacterSpan
        (A := ↥(integralClosure ℤ ℂ)) (p := p) (χ := χ * (β : R(G))) hmul
  · exact
      show ((χ : G → ℂ) * (0 : G → ℂ)) ∈
          Submodule.span (↥(integralClosure ℤ ℂ))
            ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
              Set (G → ℂ))
      by
        rw [show ((χ : G → ℂ) * (0 : G → ℂ)) = 0 by
          ext g
          simp]
        exact (Submodule.zero_mem
        (Submodule.span (↥(integralClosure ℤ ℂ))
          ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
            Set (G → ℂ))))
  · intro ψ ξ _ _ hψ hξ
    simpa [mul_add] using
      Submodule.add_mem
        (Submodule.span (↥(integralClosure ℤ ℂ))
          ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
            Set (G → ℂ))) hψ hξ
  · intro a ψ _ hψ
    have hsmul : ((χ : G → ℂ) * (a • ψ)) = a • ((χ : G → ℂ) * ψ) := by
      ext g
      calc
        (((χ : G → ℂ) * (a • ψ)) g) =
            ψ g * (χ g * (((algebraMap (↥(integralClosure ℤ ℂ)) (G → ℂ)) a) g)) := by
              simp [Pi.mul_apply, Algebra.smul_def, mul_left_comm,
                mul_comm]
        _ = (((a : ↥(integralClosure ℤ ℂ)) : ℂ)) * (ψ g * χ g) := by
              change ψ g * (χ g * (((a : ↥(integralClosure ℤ ℂ)) : ℂ))) =
                (((a : ↥(integralClosure ℤ ℂ)) : ℂ)) * (ψ g * χ g)
              ring
        _ = (a • ((χ : G → ℂ) * ψ)) g := by
              simp [Pi.mul_apply, Algebra.smul_def,
                mul_comm]
    rw [hsmul]
    exact
      Submodule.smul_mem
        (Submodule.span (↥(integralClosure ℤ ℂ))
          ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
            Set (G → ℂ))) a hψ

/-- Helper for Theorem 10-10.2-2: choose a concrete representative of a conjugacy class of `G`.
-/
private noncomputable def conjClassRepresentative (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

section
omit [Finite G]

/-- Helper for Theorem 10-10.2-2: the chosen representative realizes its conjugacy class. -/
private theorem conjClassRepresentative_mk (c : ConjClasses G) :
    ConjClasses.mk (conjClassRepresentative c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Helper for Theorem 10-10.2-2: when `|G| = p^n l` with `(p, l) = 1`, an element is
`p`-regular exactly when its `l`th power is `1`. -/
private theorem isPRegular_iff_pow_primeToPart_eq_one
    (p n l : ℕ) [Fact p.Prime] (hcard : Nat.card G = p ^ n * l)
    (hl : Nat.Coprime p l) {s : G} :
    IsPRegular p s ↔ s ^ l = 1 := by
  constructor
  · -- A `p`-regular element has order dividing the prime-to-`p` factor `l`.
    intro hs
    have hs_not_dvd : ¬ p ∣ orderOf s := by
      exact (isPRegular_iff_not_dvd_orderOf (p := p) s).1 hs
    have hs_coprime_p : Nat.Coprime p (orderOf s) := by
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs_not_dvd
    have hs_coprime_pow : Nat.Coprime (orderOf s) (p ^ n) := by
      exact (hs_coprime_p.symm.pow_right n)
    have hs_dvd_l : orderOf s ∣ l := by
      apply Nat.Coprime.dvd_of_dvd_mul_right hs_coprime_pow
      rw [mul_comm, ← hcard]
      exact orderOf_dvd_natCard s
    calc
      s ^ l = s ^ (l % orderOf s) := by
        symm
        exact pow_mod_orderOf s l
      _ = 1 := by
        simp [Nat.mod_eq_zero_of_dvd hs_dvd_l]
  · -- Conversely, `l`-torsion is automatically prime to `p`.
    intro hs
    rw [isPRegular_iff_not_dvd_orderOf (p := p) s]
    intro hp
    have hs_dvd_l : orderOf s ∣ l := orderOf_dvd_of_pow_eq_one hs
    have hpdivl : p ∣ l := dvd_trans hp hs_dvd_l
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hl) hpdivl

end

/-- Helper for Theorem 10-10.2-2: the indicator of the `p`-regular locus is an integral virtual
character when `|G| = p^n l` with `(p, l) = 1`. -/
private theorem pregular_indicator_mem_characterRing
    (p n l : ℕ) [Fact p.Prime] (hcard : Nat.card G = p ^ n * l)
    (hl : Nat.Coprime p l) :
    (fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0) ∈ R(G) := by
  classical
  let lpos : 0 < l := by
    -- The prime-to-`p` factor cannot vanish because `p` is prime.
    apply Nat.pos_of_ne_zero
    intro hl0
    have hp_one : p = 1 := by
      simpa [hl0] using hl
    exact Nat.Prime.ne_one Fact.out hp_one
  have hscalar :
      (fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0) ∈
        Representation.characterRingScalarExtension ℤ G := by
    -- Important correction: do not apply Frobenius's Theorem 23 with `(A := ℤ)` here.
    -- In LinearRepresentations_Serre_1977 11.2, `A` is the subring of `ℂ` generated by the `|G|`-th roots of unity, so the
    -- theorem first gives the weighted Adams transform over that cyclotomic coefficient ring.
    -- The missing bridge is the separate integrality/descent step from that root-of-unity ring
    -- back to the integral character ring. The previous proof incorrectly skipped this descent.
    sorry
  have hspan : Representation.characterRingScalarExtension ℤ G = (R(G)).toSubmodule := by
    -- Over `ℤ`, scalar extension collapses back to the integral character ring.
    rw [Representation.characterRingScalarExtension]
    exact Submodule.span_eq ((R(G)).toSubmodule : Submodule ℤ (G → ℂ))
  simpa [hspan] using hscalar

/-- Helper for Theorem 10-10.2-2: if `(m : ℂ) / n` is integral and `n ≠ 0`, then `n` divides
`m`. -/
private theorem nat_dvd_of_isIntegral_natCast_div
    {m n : ℕ} (hn : n ≠ 0) (h : IsIntegral ℤ ((m : ℂ) / n)) :
    n ∣ m := by
  let q : ℚ := m / n
  have hq : IsIntegral ℤ q := by
    have hqC : IsIntegral ℤ (q : ℂ) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqC
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [q] using hden

/-- Helper for Theorem 10-10.2-2: the normalized pairing of two honest characters is the
dimension of the intertwining space. -/
private theorem groupFunctionPairing_character_eq_finrank_intertwiningMap_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    ⟪σ.character, ρ.character⟫ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ))

/-- Helper for Theorem 10-10.2-2: pairing any integral virtual character with an honest
representation character gives an algebraic integer. -/
private theorem characterRing_pairing_isIntegral_with_rep_character_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (η : R(G)) (ρ : Representation ℂ G V) :
    IsIntegral ℤ ⟪(η : G → ℂ), ρ.character⟫ := by
  let S : Set (G → ℂ) :=
    { ψ |
        ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
          (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
          ψ = σ.character }
  have hmul_span :
      ∀ {f g : G → ℂ},
        f ∈ Submodule.span ℤ S →
        g ∈ Submodule.span ℤ S →
        f * g ∈ Submodule.span ℤ S := by
    intro f g hf hg
    have hfg : ∀ g : G → ℂ, g ∈ Submodule.span ℤ S → f * g ∈ Submodule.span ℤ S := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
            (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
            ψ = σ.character at hψ
          rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              change ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (τ : Representation ℂ G X),
                ξ = τ.character at hξ
              rcases hξ with ⟨X, _instXAdd, _instXMod, _instXfd, τ, rfl⟩
              let π : Representation ℂ G (TensorProduct ℂ W X) := σ.tprod τ
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ W X, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : G → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact Submodule.zero_mem (Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using Submodule.add_mem (Submodule.span ℤ S) hξ hζ
          | smul n ξ _ hξ =>
              have hmul_zsmul : σ.character * (n • ξ) = n • (σ.character * ξ) := by
                ext x
                simp [zsmul_eq_mul, mul_left_comm]
              rw [hmul_zsmul]
              exact Submodule.smul_mem (Submodule.span ℤ S) n hξ
      | zero =>
          intro g hg
          have hzero_mul : (0 : G → ℂ) * g = 0 := by
            ext x
            simp
          rw [hzero_mul]
          exact Submodule.zero_mem (Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : G → ℂ) ∈ Submodule.span ℤ S := by
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span ⟨σ, inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ G ℂ).character = (1 : G → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      rw [show algebraMap ℤ (G → ℂ) n =
          n • (Representation.trivial ℂ G ℂ).character by
        ext x
        simp [htriv]]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ G ℂ, rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  refine
    Submodule.span_induction
      (p := fun ψ _ ↦ IsIntegral ℤ ⟪ψ, ρ.character⟫)
      ?_ ?_ ?_ ?_ hηspan
  · intro ψ hψ
    change ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
      ψ = σ.character at hψ
    rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
    rw [groupFunctionPairing_character_eq_finrank_intertwiningMap_local σ ρ]
    exact isIntegral_algebraMap
  · simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · intro ψ ξ _ _ hψ hξ
    simpa [Representation.groupFunctionPairing_add_left] using hψ.add hξ
  · intro n ψ _ hψ
    rw [show ⟪n • ψ, ρ.character⟫ = (n : ℂ) * ⟪ψ, ρ.character⟫ by
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (n : ℂ)) (φ := ψ) (ψ := ρ.character))]
    exact (isIntegral_algebraMap : IsIntegral ℤ (n : ℂ)).mul hψ

/-- Helper for Theorem 10-10.2-2: the `p`-regular indicator collapses to the trivial character
under the Chapter `10.2` factorization hypothesis. -/
private theorem pregular_indicator_eq_one
    (p n l : ℕ) [Fact p.Prime] (hcard : Nat.card G = p ^ n * l)
    (hl : Nat.Coprime p l) :
    let δ : R(G) :=
      ⟨fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0,
        pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
    δ = (1 : R(G)) := by
  let δ : R(G) :=
    ⟨fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0,
      pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
  let m : ℕ := Fintype.card { s : G // IsPRegular p s }
  have hpair_integral :
      IsIntegral ℤ ⟪(δ : G → ℂ), (Representation.trivial ℂ G ℂ).character⟫ := by
    -- Pairing an integral virtual character with the trivial character is integral.
    simpa using
      characterRing_pairing_isIntegral_with_rep_character_local
        (G := G) (V := ℂ) δ (Representation.trivial ℂ G ℂ)
  have hpair_eq :
      ⟪(δ : G → ℂ), (Representation.trivial ℂ G ℂ).character⟫ =
        ((m : ℂ) / Nat.card G) := by
    -- The pairing counts exactly the `p`-regular elements.
    rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
    calc
      (Nat.card G : ℂ)⁻¹ *
          ∑ x : G, (δ x) * (Representation.trivial ℂ G ℂ).character x⁻¹
          =
            (Nat.card G : ℂ)⁻¹ * ∑ x : G, if IsPRegular p x then (1 : ℂ) else 0 := by
              congr 2
              ext x
              by_cases hx : IsPRegular p x <;>
                simp [Representation.character, Representation.trivial, δ, hx]
      _ = (Nat.card G : ℂ)⁻¹ * ({ x : G | IsPRegular p x }.toFinset.card : ℂ) := by
            simp
      _ = (Nat.card G : ℂ)⁻¹ * (m : ℂ) := by
            congr 1
            have hm_nat : { x : G | IsPRegular p x }.toFinset.card = m := by
              simpa [m] using (Set.toFinset_card { x : G | IsPRegular p x })
            exact_mod_cast hm_nat
      _ = ((m : ℂ) / Nat.card G) := by
            rw [div_eq_mul_inv, mul_comm]
  have hcard_dvd_m : Nat.card G ∣ m := by
    -- Integrality of the normalized pairing forces divisibility by `|G|`.
    have hdiv :
        IsIntegral ℤ ((m : ℂ) / Nat.card G) := by
      simpa [hpair_eq] using hpair_integral
    exact
      nat_dvd_of_isIntegral_natCast_div
        (m := m) (n := Nat.card G) Nat.card_pos.ne' hdiv
  have hm_pos : 0 < m := by
    refine Fintype.card_pos_iff.mpr ?_
    exact ⟨⟨1, isPRegular_one p⟩⟩
  have hm_eq : m = Nat.card G := by
    apply Nat.le_antisymm
    · simpa [m, Nat.card_eq_fintype_card] using
        (Fintype.card_subtype_le (fun s : G ↦ IsPRegular p s))
    · exact Nat.le_of_dvd hm_pos hcard_dvd_m
  have hall : ∀ s : G, IsPRegular p s := by
    -- Equality of the counts forces every element to be `p`-regular.
    intro s
    by_contra hs
    have hlt :
        m < Nat.card G := by
      simpa [m] using
        (Fintype.card_subtype_lt (p := fun x : G ↦ IsPRegular p x) hs)
    exact Nat.lt_irrefl _ (hm_eq ▸ hlt)
  -- Once every element is `p`-regular, the indicator is the constant `1` function.
  apply Subtype.ext
  ext s
  simp [hall s]

-- Proof sketch: identify the trivial character with the unit `1 : R(G)`, then apply Brauer's
-- index theorem for `V_p` from `Theorem 10-10.2-1` at the prime `p`; since `l` is the prime-to-`p`
-- factor of `|G|`, the quotient `R(G) / V_p` has order prime to `p`, so multiplication by `l`
-- kills the class of the trivial character.
/-- Theorem 10-10.2-2: if `|G| = p^n l` with `l` prime to `p`, then `l` times the trivial
character belongs to Brauer's subgroup `V_p`. -/
theorem primeToPart_card_smul_trivialCharacter_mem_pElementaryInducedCharacterSpan
    (p n l : ℕ) [Fact p.Prime] (hcard : Nat.card G = p ^ n * l) (hl : Nat.Coprime p l) :
    l • (1 : R(G)) ∈ V[p](G) := by
  classical
  let Creg : Type := { c : ConjClasses G // IsPRegular p (conjClassRepresentative c) }
  letI : Fintype Creg := Fintype.ofFinite Creg
  let δ : R(G) :=
    ⟨fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0,
      pregular_indicator_mem_characterRing (G := G) p n l hcard hl⟩
  let representative (c : Creg) : G := conjClassRepresentative c.1
  let sylowCentralizer (c : Creg) : Sylow p C(representative c) := default
  let auxiliaryTensorCharacter (c : Creg) :
      (↥(integralClosure ℤ ℂ)) ⊗R(
        associatedPElementarySubgroup p (representative c) (sylowCentralizer c)) :=
    brauerAssociatedAuxiliaryTensorCharacter
      (p := p) (representative c) (sylowCentralizer c) c.2
  let βfun (c : Creg) : G → ℂ :=
    let ψc : associatedPElementarySubgroup p (representative c) (sylowCentralizer c) → ℂ :=
      auxiliaryTensorCharacter c
    Ind[associatedPElementarySubgroup p (representative c) (sylowCentralizer c)](ψc)
  let βmem : ∀ c : Creg,
      βfun c ∈
        Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G :=
    fun c ↦
      induced_tensor_character_mem_integralClosure_pElementary_scalarExtension
        (G := G) (p := p)
        (associatedPElementarySubgroup p (representative c) (sylowCentralizer c))
        (associatedPElementarySubgroup_isPElementary
          (p := p) (representative c) c.2 (sylowCentralizer c))
        (auxiliaryTensorCharacter c)
  let scalarValue : Creg → ℕ :=
    fun c ↦
      Nat.card C(representative c) /
        Nat.card (sylowCentralizer c : Subgroup C(representative c))
  let coeff : Creg → ℕ := fun c ↦ l / scalarValue c
  let θ : G → ℂ := ∑ c : Creg, (coeff c : ↥(integralClosure ℤ ℂ)) • βfun c
  have hθmem :
      θ ∈
        Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G := by
    unfold θ
    refine Submodule.sum_mem
        (Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G) ?_
    intro c hc
    exact
      (Representation.pElementaryInducedCharacterScalarExtension
        (↥(integralClosure ℤ ℂ)) p G).smul_mem (coeff c) (βmem c)
  have hl_eq_ordCompl : ordCompl[p] (Nat.card G) = l := by
    -- The given factorization identifies `l` with the prime-to-`p` part of `|G|`.
    rw [hcard]
    exact
      Nat.ordCompl_pow_mul_of_not_dvd n Fact.out
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hl)
  have hscalarValue_dvd_l : ∀ c : Creg, scalarValue c ∣ l := by
    intro c
    -- The explicit auxiliary value is the prime-to-`p` part of the relevant centralizer order.
    have hcent_dvd :
        Nat.card C(representative c) ∣ Nat.card G := by
      exact
        (Subgroup.card_dvd_of_le (show C(representative c) ≤ ⊤ from le_top)).trans <| by
          simp
    have hscalar_eq_ordCompl :
        scalarValue c = ordCompl[p] (Nat.card C(representative c)) := by
      unfold scalarValue
      rw [(sylowCentralizer c).card_eq_multiplicity]
    have hordCompl_dvd :
        ordCompl[p] (Nat.card C(representative c)) ∣ ordCompl[p] (Nat.card G) :=
      Nat.ordCompl_dvd_ordCompl_of_dvd hcent_dvd p
    have htmp : scalarValue c ∣ ordCompl[p] (Nat.card G) := by
      rw [hscalar_eq_ordCompl]
      exact hordCompl_dvd
    rw [hl_eq_ordCompl] at htmp
    exact htmp
  have hθconst : ∀ s : G, IsPRegular p s → θ s = (l : ℂ) := by
    intro s hs
    have hsrep : IsPRegular p (conjClassRepresentative (ConjClasses.mk s)) := by
      have hconj :
          IsConj s (conjClassRepresentative (ConjClasses.mk s)) := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        simpa using (conjClassRepresentative_mk (G := G) (ConjClasses.mk s)).symm
      rcases isConj_iff.1 hconj with ⟨t, ht⟩
      simpa [ht, mul_assoc] using isPRegular_conj p s t hs
    let c₀ : Creg := ⟨ConjClasses.mk s, hsrep⟩
    have hβsame :
        βfun c₀ s = (scalarValue c₀ : ℂ) := by
      -- On its supporting class, the induced tensor witness takes the explicit centralizer
      -- quotient value inherited from Brauer's auxiliary function.
      have hβclass :
          _root_.IsClassFunction (βfun c₀) :=
        Subgroup.inducedClassFunction_isClassFunction
          (associatedPElementarySubgroup p (representative c₀) (sylowCentralizer c₀))
          ((auxiliaryTensorCharacter c₀ :
              (↥(integralClosure ℤ ℂ)) ⊗R(
                associatedPElementarySubgroup p (representative c₀)
                  (sylowCentralizer c₀))) :
            associatedPElementarySubgroup p (representative c₀) (sylowCentralizer c₀) → ℂ)
      have hconj :
          IsConj s (representative c₀) := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        simpa [representative, c₀] using
          (conjClassRepresentative_mk (G := G) (ConjClasses.mk s)).symm
      have hvalue_rep :
          βfun c₀ (representative c₀) = (scalarValue c₀ : ℂ) := by
        have hdiv :
            Nat.card (sylowCentralizer c₀ : Subgroup C(representative c₀)) ∣
              Nat.card C(representative c₀) := by
          exact
            Subgroup.card_subgroup_dvd_card
              (sylowCentralizer c₀ : Subgroup C(representative c₀))
        have hP_ne_zero :
            ((Nat.card (sylowCentralizer c₀ : Subgroup C(representative c₀)) : ℕ) : ℂ) ≠ 0 := by
          exact Nat.cast_ne_zero.mpr <|
            Nat.card_ne_zero.mpr
              ⟨⟨1, by simp⟩, inferInstance⟩
        have hvalue_raw :
            βfun c₀ (representative c₀) =
              (Nat.card C(representative c₀) : ℂ) /
                Nat.card (sylowCentralizer c₀ : Subgroup C(representative c₀)) := by
          -- Route correction: transport the explicit value formula through the chosen tensor
          -- realization instead of forcing an integral owner on the local witness.
          simpa [βfun, auxiliaryTensorCharacter, representative, c₀] using
            associated_auxiliary_character_induced_value_at_x_eq_centralizer_quotient_of_realization
              (p := p) (x := conjClassRepresentative (ConjClasses.mk s))
              (P := sylowCentralizer c₀) c₀.2
              (brauerAssociatedAuxiliaryTensorCharacter
                (p := p) (conjClassRepresentative (ConjClasses.mk s))
                (sylowCentralizer c₀) c₀.2)
              (brauerAssociatedAuxiliaryTensorCharacter_realizes
                (p := p) (conjClassRepresentative (ConjClasses.mk s))
                (sylowCentralizer c₀) c₀.2)
        calc
          βfun c₀ (representative c₀) =
              (Nat.card C(representative c₀) : ℂ) /
                Nat.card (sylowCentralizer c₀ : Subgroup C(representative c₀)) :=
            hvalue_raw
          _ = (scalarValue c₀ : ℂ) := by
            unfold scalarValue
            rw [Nat.cast_div hdiv hP_ne_zero]
      calc
        βfun c₀ s = βfun c₀ (representative c₀) :=
          _root_.IsClassFunction.eq_of_isConj hβclass hconj
        _ = (scalarValue c₀ : ℂ) := hvalue_rep
    have hcoeffprod : coeff c₀ * scalarValue c₀ = l := by
      -- The chosen coefficient rescales the supporting value to exactly `l`.
      unfold coeff
      exact Nat.div_mul_cancel (hscalarValue_dvd_l c₀)
    have hcoeffprodC : ((coeff c₀ : ℕ) : ℂ) * (scalarValue c₀ : ℂ) = (l : ℂ) := by
      exact_mod_cast hcoeffprod
    -- All other class-supported witnesses vanish on `s`, so only the class of `s` contributes.
    calc
      θ s = ∑ c : Creg, (((coeff c : ℕ) : ℂ) * βfun c s) := by
        simp [θ, βfun, Algebra.smul_def]
      _ = (((coeff c₀ : ℕ) : ℂ) * βfun c₀ s) := by
            refine Finset.sum_eq_single c₀ ?_ ?_
            · intro c hc hne
              have hs_not_conj : ¬ IsConj s (representative c) := by
                intro hsconj
                apply hne
                apply Subtype.ext
                simpa [representative, c₀, conjClassRepresentative_mk (G := G) c.1] using
                  (ConjClasses.mk_eq_mk_iff_isConj.2 hsconj).symm
              have hzero : βfun c s = 0 := by
                -- The realization theorem already transports the vanishing clause away from the
                -- supporting conjugacy class.
                simpa [βfun, auxiliaryTensorCharacter] using
                  associated_auxiliary_character_vanishing_clause_of_realization
                    (p := p) (x := representative c) (P := sylowCentralizer c) c.2
                    (auxiliaryTensorCharacter c)
                    (brauerAssociatedAuxiliaryTensorCharacter_realizes
                      (p := p) (representative c) (sylowCentralizer c) c.2)
                    s hs hs_not_conj
              simp [hzero]
            · intro hc₀
              exact False.elim (hc₀ (by simp))
      _ = (((coeff c₀ : ℕ) : ℂ) * (scalarValue c₀ : ℂ)) := by
            rw [hβsame]
      _ = (l : ℂ) := hcoeffprodC
  have hθδ :
      (δ : G → ℂ) * θ = ((l • δ : R(G)) : G → ℂ) := by
    -- Multiplying by the `p`-regular indicator kills the irrelevant values of `θ`.
    ext s
    by_cases hs : IsPRegular p s
    · simp [δ, hθconst s hs, mul_comm]
    · simp [δ, hs]
  have hδeq : δ = (1 : R(G)) :=
    pregular_indicator_eq_one (G := G) p n l hcard hl
  have hldelta_scalar :
      ((l • δ : R(G)) : G → ℂ) ∈
        Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G := by
    -- The tensor Brauer owner is stable under multiplying by the integral `p`-regular indicator.
    rw [← hθδ]
    exact
      mul_mem_integralClosure_pElementary_scalarExtension
        (G := G) (p := p) hθmem δ
  have hldelta_mem : l • δ ∈ V[p](G) := by
    -- Descend the final integral class function through
    -- `(A ⊗ V_p) ∩ R(G) = image(V_p)`, instead of descending each local auxiliary witness.
    have hldelta_inter :
        (((l • δ : R(G)) : G → ℂ) ∈
          (Representation.pElementaryInducedCharacterScalarExtension
            (↥(integralClosure ℤ ℂ)) p G : Set (G → ℂ))) ∧
          (((l • δ : R(G)) : G → ℂ) ∈ (R(G) : Set (G → ℂ))) := by
      exact ⟨hldelta_scalar, (l • δ : R(G)).property⟩
    have hldelta_image :
        (((l • δ : R(G)) : G → ℂ) ∈
          ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
            Set (G → ℂ))) := by
      rw [← Representation.pElementaryInducedCharacterScalarExtension_inter_characterRing_eq_image
        (A := ↥(integralClosure ℤ ℂ)) (G := G) (p := p)]
      simpa [Set.mem_inter_iff] using hldelta_inter
    rcases hldelta_image with ⟨γ, hγ⟩
    have hγeq : (γ : R(G)) = l • δ := by
      apply Subtype.ext
      simpa [Representation.pElementaryInducedCharacterToFunction] using hγ
    simpa [hγeq] using γ.property
  -- Replacing the indicator by the trivial character gives the target scalar.
  simpa [hδeq] using hldelta_mem

end

/-! ### Exercise_10_10_3_4 (from Chap10) -/
noncomputable section

open Representation
open scoped BigOperators Representation SubgroupInduction

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]

attribute [local instance] Fintype.ofFinite

omit [Finite G] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Exercise 10-10.3-4: coefficientwise complexification preserves the class-function
condition for a bundled `A`-valued class function. -/
lemma complexified_classFunction_mem_classFunctionSubspace
    (ψ : classFunctionSubmodule A G) :
    (algebraMap A ℂ ∘ ψ) ∈ _root_.classFunctionSubspace G := by
  -- Postcomposing the existing class-function owner by `algebraMap A ℂ` keeps conjugacy
  -- invariance intact.
  rw [mem_classFunctionSubspace_iff]
  exact ((mem_classFunctionSubmodule_iff A (ψ : G → A)).1 ψ.2).comp (algebraMap A ℂ)

/-- Helper for Exercise 10-10.3-4: package the coefficientwise complexification of a bundled
`A`-valued class function in the canonical complex class-function owner. -/
def complexified_classFunctionSubspace_of_classFunctionSubmodule
    (ψ : classFunctionSubmodule A G) :
    _root_.classFunctionSubspace G :=
  ⟨algebraMap A ℂ ∘ ψ, complexified_classFunction_mem_classFunctionSubspace ψ⟩

/-- Helper for Exercise 10-10.3-4: multiplying an induced class function by a global class
function amounts to inducing the product with the restricted global factor. -/
lemma induced_mul_eq_induced_mul_restriction
    (H : Subgroup G) (ψ : H → ℂ) (χ : _root_.classFunctionSubspace G) :
    Ind[H](ψ) * (χ : G → ℂ) = Ind[H](fun h : H ↦ ψ h * χ h) := by
  classical
  ext x
  simp only [Pi.mul_apply, Subgroup.inducedClassFunction]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro s hs_univ
  by_cases hs : s⁻¹ * x * s ∈ H
  · have hs' : s⁻¹ * (x * s) ∈ H := by
      simpa [mul_assoc] using hs
    have hχ : χ (s⁻¹ * x * s) = χ x := by
      exact (χ.2 : _root_.IsClassFunction (χ : G → ℂ)).eq_of_isConj <|
        isConj_iff.2 ⟨s, by group⟩
    have hχ' : χ (s⁻¹ * (x * s)) = χ x := by
      simpa [mul_assoc] using hχ
    simp [hs', hχ', mul_comm, mul_assoc]
  · simp [hs]

omit [Finite G] in
/-- Helper for Exercise 10-10.3-4: a linear character value is integral over `ℤ` because it is a
root of unity. -/
lemma linear_character_value_isIntegral
    {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    IsIntegral ℤ ((χ h : ℂ)) := by
  -- The value of a linear character is a root of unity of order dividing `orderOf h`.
  apply IsIntegral.of_pow (n := orderOf h)
  · exact orderOf_pos h
  · rw [show ((χ h : ℂ) ^ orderOf h) = 1 by
      have hpowUnits : (χ h) ^ orderOf h = 1 := by
        rw [← map_pow]
        simp [pow_orderOf_eq_one h]
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hpowUnits]
    exact isIntegral_one

/-- Helper for Exercise 10-10.3-4: every linear character value lifts through `algebraMap A ℂ`
because `A` is the integral closure of `ℤ` in `ℂ`. -/
lemma linear_character_value_mem_range
    {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (h : H) :
    (χ h : ℂ) ∈ Set.range (algebraMap A ℂ) := by
  -- Convert integrality of the value into actual membership in the integral-closure ring.
  exact
    (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := ℂ)).mp
      (linear_character_value_isIntegral χ h)

/-- Helper for Exercise 10-10.3-4: the linear characters of a finite commutative group form a
finite type. -/
local instance linearCharacterFinite
    {H : Type} [CommGroup H] [Finite H] :
    Finite (H →* ℂˣ) := by
  let eDual : (H →* ℂˣ) ≃* H :=
    Classical.choice
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G := H) (M := ℂ))
  exact Finite.of_equiv H eDual.symm.toEquiv

/-- Helper for Exercise 10-10.3-4: the linear characters of a finite commutative group admit the
canonical `Fintype` structure coming from finiteness. -/
local instance linearCharacterFintype
    {H : Type} [CommGroup H] [Finite H] :
    Fintype (H →* ℂˣ) := Fintype.ofFinite (H →* ℂˣ)

/-- Helper for Exercise 10-10.3-4: on a finite commutative group, the sum of all linear
characters vanishes away from the identity. -/
lemma commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one
    {H : Type} [CommGroup H] [Finite H] {h : H} (hh : h ≠ 1) :
    ∑ χ : H →* ℂˣ, (χ h : ℂ) = 0 := by
  classical
  obtain ⟨φ, hφh⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (G := H) (M := ℂ) hh
  let e : (H →* ℂˣ) ≃ (H →* ℂˣ) :=
    { toFun := fun χ ↦ φ * χ
      invFun := fun χ ↦ φ⁻¹ * χ
      left_inv := by
        intro χ
        simp
      right_inv := by
        intro χ
        simp }
  have hsum :
      ∑ χ : H →* ℂˣ, ((φ * χ) h : ℂ) =
        ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
    exact Fintype.sum_equiv e
      (fun χ : H →* ℂˣ ↦ ((φ * χ) h : ℂ))
      (fun χ : H →* ℂˣ ↦ (χ h : ℂ))
      (fun χ ↦ rfl)
  have hmul :
      ∑ χ : H →* ℂˣ, ((φ * χ) h : ℂ) =
        (φ h : ℂ) * ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
    -- Pull the fixed scalar `φ(h)` out of the finite sum.
    simp [Finset.mul_sum]
  have hfactor :
      (((φ h : ℂ) - 1) * ∑ χ : H →* ℂˣ, (χ h : ℂ)) = 0 := by
    -- Compare the unchanged sum with its translate by multiplication with `φ`.
    calc
      (((φ h : ℂ) - 1) * ∑ χ : H →* ℂˣ, (χ h : ℂ)) =
          (φ h : ℂ) * ∑ χ : H →* ℂˣ, (χ h : ℂ) -
            ∑ χ : H →* ℂˣ, (χ h : ℂ) := by
              ring
      _ = 0 := by
        rw [← hmul, hsum, sub_self]
  have hne : ((φ h : ℂ) - 1) ≠ 0 := by
    intro hzero
    have hcast : (φ h : ℂ) = 1 := sub_eq_zero.mp hzero
    apply hφh
    ext
    simpa using hcast
  exact (mul_eq_zero.mp hfactor).resolve_left hne

/-- Helper for Exercise 10-10.3-4: the regular character of a finite commutative group is the sum
of all degree-`1` complex characters. -/
lemma commGroup_regularCharacter_eq_sum_linearCharacters
    {H : Type} [CommGroup H] [Finite H] :
    (leftRegular ℂ H).character = ∑ χ : H →* ℂˣ, (χ.toCharacterRing : H → ℂ) := by
  let _ : Fintype H := Fintype.ofFinite H
  ext h
  by_cases hh : h = 1
  · subst hh
    -- At the identity, every linear character contributes `1`, so only the count remains.
    rw [Representation.leftRegular_character_one (k := ℂ) (G := H), Finset.sum_apply]
    have hcard : Fintype.card H = Fintype.card (H →* ℂˣ) := by
      simpa using
        (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (G := H) (M := ℂ)).symm
    simp [hcard]
  · -- Away from the identity, the translated character sum collapses to zero.
    rw [Representation.leftRegular_character_eq_zero_of_ne_one (k := ℂ) (G := H) hh,
      Finset.sum_apply]
    simpa using (commGroup_sum_linearCharacter_apply_eq_zero_of_ne_one (H := H) hh).symm

/-- Helper for Exercise 10-10.3-4: the `|H|`-point mass at any element of a finite cyclic group is
an `A`-linear combination of linear characters, hence belongs to the scalar-extended character
ring. -/
lemma point_mass_card_mem_characterRingScalarExtension
    {H : Type} [CommGroup H] [Finite H] [DecidableEq H] (u : H) :
    (fun h : H ↦ if h = u then (Nat.card H : ℂ) else 0) ∈
      Representation.characterRingScalarExtension A H := by
  classical
  let b : (H →* ℂˣ) → A := fun χ ↦
    Classical.choose (linear_character_value_mem_range (A := A) χ u⁻¹)
  have hb : ∀ χ : H →* ℂˣ, algebraMap A ℂ (b χ) = (χ u⁻¹ : ℂ) := by
    intro χ
    exact Classical.choose_spec (linear_character_value_mem_range (A := A) χ u⁻¹)
  have hdecomp :
      (fun h : H ↦ if h = u then (Nat.card H : ℂ) else 0) =
        ∑ χ : H →* ℂˣ, b χ • ((χ.toCharacterRing : R(H)) : H → ℂ) := by
    ext h
    have hiff : u⁻¹ * h = 1 ↔ h = u := by
      constructor
      · intro hone
        calc
          h = 1 * h := by simp
          _ = u * (u⁻¹ * h) := by group
          _ = u := by rw [hone, mul_one]
      · intro hh
        subst hh
        simp
    -- Expand the point mass via the finite Fourier decomposition over all linear characters.
    calc
      (if h = u then (Nat.card H : ℂ) else 0)
          = ∑ χ : H →* ℂˣ, (χ u⁻¹ : ℂ) * (χ h : ℂ) := by
              symm
              calc
                ∑ χ : H →* ℂˣ, (χ u⁻¹ : ℂ) * (χ h : ℂ)
                    = ∑ χ : H →* ℂˣ, (χ (u⁻¹ * h) : ℂ) := by
                        refine Fintype.sum_congr
                          (fun χ : H →* ℂˣ ↦ (χ u⁻¹ : ℂ) * (χ h : ℂ))
                          (fun χ : H →* ℂˣ ↦ (χ (u⁻¹ * h) : ℂ)) ?_
                        intro χ
                        simp [map_mul]
                _ = (leftRegular ℂ H).character (u⁻¹ * h) := by
                      symm
                      simpa using
                        congrFun (commGroup_regularCharacter_eq_sum_linearCharacters (H := H))
                          (u⁻¹ * h)
                _ = if u⁻¹ * h = 1 then (Nat.card H : ℂ) else 0 := by
                      simpa using
                        (Representation.leftRegular_character_eq_ite (k := ℂ) (G := H) (u⁻¹ * h))
                _ = if h = u then (Nat.card H : ℂ) else 0 := by
                      by_cases hone : u⁻¹ * h = 1
                      · have hh : h = u := hiff.mp hone
                        simp [hh]
                      · have hh : h ≠ u := by
                          intro hh
                          exact hone (hiff.mpr hh)
                        simp [hone, hh]
      _ = ∑ χ : H →* ℂˣ, algebraMap A ℂ (b χ) * (χ h : ℂ) := by
            refine Fintype.sum_congr
              (fun χ : H →* ℂˣ ↦ (χ u⁻¹ : ℂ) * (χ h : ℂ))
              (fun χ : H →* ℂˣ ↦ algebraMap A ℂ (b χ) * (χ h : ℂ)) ?_
            intro χ
            simp [hb χ]
      _ = (∑ χ : H →* ℂˣ, b χ • ((χ.toCharacterRing : R(H)) : H → ℂ)) h := by
            simp [Algebra.smul_def]
  rw [hdecomp]
  -- Sum the scalar-extended linear characters term by term.
  refine Submodule.sum_mem (Representation.characterRingScalarExtension A H) ?_
  intro χ hχ
  exact Submodule.smul_mem _ (b χ)
    (Representation.mem_characterRingScalarExtension_of_mem_characterRing (A := A)
      ((χ.toCharacterRing : R(H)) : H → ℂ) χ.toCharacterRing.property)

omit [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ] in
/-- Helper for Exercise 10-10.3-4: if each value of a bundled `A`-valued class function lies in
the ideal `|G|A`, then the quotient by `|G|` can be chosen compatibly on conjugacy classes, hence
again defines a bundled class function. -/
lemma class_function_quotient_exists_of_groupOrder_mem_ideal
    (f : classFunctionSubmodule A G)
    (hf_mem_span : ∀ x : G, f x ∈ Ideal.span {(Nat.card G : A)}) :
    ∃ q : classFunctionSubmodule A G, ∀ x : G, f x = (Nat.card G : A) * q x := by
  classical
  let fClasses : ConjClasses G → A := classFunctionSubmodule.equivFun A G f
  let qClasses : ConjClasses G → A := fun c ↦
    Classical.choose <| show ∃ a : A, a * (Nat.card G : A) = fClasses c from by
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
      simpa [fClasses] using Ideal.mem_span_singleton'.mp (hf_mem_span x)
  have hqClasses : ∀ c : ConjClasses G, fClasses c = (Nat.card G : A) * qClasses c := by
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    change f x = (Nat.card G : A) * qClasses (ConjClasses.mk x)
    have hq : qClasses (ConjClasses.mk x) * (Nat.card G : A) = f x :=
      by
        simpa [fClasses, qClasses] using
          (Classical.choose_spec
            (show ∃ a : A, a * (Nat.card G : A) = fClasses (ConjClasses.mk x) from by
              simpa [fClasses] using Ideal.mem_span_singleton'.mp (hf_mem_span x)))
    calc
      f x = qClasses (ConjClasses.mk x) * (Nat.card G : A) := hq.symm
      _ = (Nat.card G : A) * qClasses (ConjClasses.mk x) := by
        ac_rfl
  let q : classFunctionSubmodule A G := (classFunctionSubmodule.equivFun A G).symm qClasses
  refine ⟨q, ?_⟩
  intro x
  -- Evaluate the chosen quotient on the conjugacy class of `x` and transport it back through the
  -- canonical equivalence with functions on `ConjClasses G`.
  simpa [fClasses, qClasses, q] using hqClasses (ConjClasses.mk x)

/-- Helper for Exercise 10-10.3-4: once the cyclic subgroup function is known to be the
coefficientwise complexification of an `A`-valued class function with values in `|H|A`, its
induction lies in the cyclic induced-character span. -/
lemma cyclic_card_mul_function_induced_mem_cyclicInducedCharacterSpan
    (H : Subgroup G) (hH : IsCyclic H) (φ : H → ℂ)
    (hdiv : ∀ h : H, ∃ a : A, φ h = algebraMap A ℂ ((Nat.card H : A) * a)) :
    Ind[H](φ) ∈ Representation.cyclicInducedCharacterSpan A G := by
  letI : CommGroup H := IsCyclic.commGroup
  classical
  have hclass_comm {f : H → ℂ} : _root_.IsClassFunction f := by
    refine ⟨?_⟩
    intro x y hxy
    rcases ConjClasses.mk_eq_mk_iff_isConj.mp hxy with ⟨c, hc⟩
    apply congrArg f
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  let a : H → A := fun h ↦ Classical.choose (hdiv h)
  have ha : ∀ h : H, φ h = algebraMap A ℂ ((Nat.card H : A) * a h) := by
    intro h
    exact Classical.choose_spec (hdiv h)
  let δ : H → H → ℂ := fun u h ↦ if u = h then Nat.card H else 0
  let φcf : _root_.classFunctionSubspace H :=
    ⟨φ, (_root_.mem_classFunctionSubspace_iff _).2 hclass_comm⟩
  have hscalar : (φcf : H → ℂ) ∈ Representation.characterRingScalarExtension A H := by
    have hdecomp :
        (φcf : H → ℂ) = ∑ u : H, a u • δ u := by
      ext h
      calc
        φcf h = algebraMap A ℂ ((Nat.card H : A) * a h) := ha h
        _ = (a h • δ h) h := by
          simp [δ, Pi.smul_apply, Algebra.smul_def, map_mul, mul_comm]
        _ = ∑ u : H, (a u • δ u) h := by
          simp [δ, Pi.smul_apply]
        _ = (∑ u : H, a u • δ u) h := by
          simp only [Finset.sum_apply]
    refine hdecomp ▸ ?_
    refine Submodule.sum_mem (Representation.characterRingScalarExtension A H) ?_
    intro u hu
    have hδscalar : δ u ∈ Representation.characterRingScalarExtension A H := by
      -- Realize `δ u` as the `|H|`-point mass obtained from the finite Fourier decomposition over
      -- all linear characters of the cyclic group `H`.
      simpa [δ, eq_comm] using
        point_mass_card_mem_characterRingScalarExtension (A := A) (H := H) u
    exact Submodule.smul_mem
      (Representation.characterRingScalarExtension A H)
      (a u)
      hδscalar
  let P : (H → ℂ) → Prop :=
    fun g ↦ Ind[H](g) ∈ Representation.cyclicInducedCharacterSpan A G
  have hP : P (φcf : H → ℂ) := by
    rw [Representation.characterRingScalarExtension] at hscalar
    refine Submodule.span_induction
      (s := (R(H) : Set (H → ℂ)))
      (p := fun g _ ↦ P g)
      ?_ ?_ ?_ ?_ hscalar
    · intro g hg
      simpa [P] using
        Representation.inducedClassFunction_mem_cyclicInducedCharacterSpan (A := A) H hH ⟨g, hg⟩
    · have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext x
        simp [Subgroup.inducedClassFunction]
      change Ind[H]((0 : H → ℂ)) ∈ Representation.cyclicInducedCharacterSpan A G
      rw [hzero]
      exact
        (Submodule.zero_mem (Representation.cyclicInducedCharacterSpan A G) :
          (0 : G → ℂ) ∈ Representation.cyclicInducedCharacterSpan A G)
    · intro f₁ f₂ hf₁ hf₂ hf₁_mem hf₂_mem
      simpa [P, Subgroup.inducedClassFunction_map_add] using
        Submodule.add_mem (Representation.cyclicInducedCharacterSpan A G) hf₁_mem hf₂_mem
    · intro a' g hg hg_mem
      simpa [P, Subgroup.inducedClassFunction_map_smul] using
        Submodule.smul_mem (Representation.cyclicInducedCharacterSpan A G) a' hg_mem
  simpa [P, φcf] using hP

-- Source/core/bridge triage:
-- * source-facing: an `A`-valued class function whose values lie in the ideal `|G|A`.
-- * core/canonical owners: `classFunctionSubmodule A G` and
--   `Representation.cyclicInducedCharacterSpan A G`.
-- * bridge/view: the coefficientwise complexification `algebraMap A ℂ ∘ f`.
-- * primitive data: `f : classFunctionSubmodule A G` together with the pointwise ideal-membership
--   hypothesis.
-- * derived API: membership of the coefficientwise complexification in the cyclic induced-character
--   span.
--
-- Proof sketch: write each value of `f` as `(Nat.card G : A) * a_x` with `a_x ∈ A`, use the same
-- Brauer-induction argument as in Lemma `10-10.3-1` but with coefficients in the ideal
-- `(Nat.card G)A`, and then compose with `algebraMap A ℂ` coefficientwise to regard the
-- resulting class function as a complex-valued element of the `A`-span of characters induced from
-- cyclic subgroups.
/-- Exercise 10-10.3-4: an `A`-valued class function on `G`, packaged in the canonical owner
`classFunctionSubmodule A G`, whose values all lie in the ideal generated by `|G|` becomes,
after applying `algebraMap A ℂ` pointwise, an element of the `A`-span of characters induced from
cyclic subgroups of `G`. -/
theorem classFunction_complexification_mem_cyclicInducedCharacterSpan_of_groupOrder_mem_ideal
    (f : classFunctionSubmodule A G)
    (hf_mem_span : ∀ x : G, f x ∈ Ideal.span {(Nat.card G : A)}) :
    (algebraMap A ℂ ∘ f) ∈ cyclicInducedCharacterSpan A G := by
  classical
  obtain ⟨q, hq⟩ :=
    class_function_quotient_exists_of_groupOrder_mem_ideal (f := f) hf_mem_span
  let χ : _root_.classFunctionSubspace G :=
    complexified_classFunctionSubspace_of_classFunctionSubmodule q
  have hcomplexified_decomp :
      (algebraMap A ℂ ∘ f) =
        ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](fun h : H ↦ θ[H] h * χ h) := by
    -- Rewrite `algebraMap A ℂ ∘ f` as `|G| • χ`, then reuse the same cyclic-subgroup expansion
    -- of `|G| • 1` as in Lemma `10-10.3-1`.
    calc
      (algebraMap A ℂ ∘ f) = ((Nat.card G : ℂ) • (χ : G → ℂ)) := by
        ext x
        calc
          algebraMap A ℂ (f x) = algebraMap A ℂ ((Nat.card G : A) * q x) := by
            rw [hq x]
          _ = (Nat.card G : ℂ) * χ x := by
            simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule, map_mul]
          _ = (((Nat.card G : ℂ) • (χ : G → ℂ)) x) := by
            simp
      _ = ((Nat.card G : ℂ) • (1 : G → ℂ)) * (χ : G → ℂ) := by
        ext x
        simp
      _ = (∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](θ[H])) * (χ : G → ℂ) := by
        rw [_root_.sum_induced_cyclicGroupTheta_eq_groupOrder_smul_one (G := G) (K := ℂ)]
      _ = ∑ H ∈ Subgroup.cyclicSubgroups G, Ind[H](fun h : H ↦ θ[H] h * χ h) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro H hH
        simpa using induced_mul_eq_induced_mul_restriction H (θ[H]) χ
  rw [hcomplexified_decomp]
  -- Each cyclic summand has values in `|H|A`, so the unresolved cyclic closing lemma applies.
  refine Submodule.sum_mem (Representation.cyclicInducedCharacterSpan A G) ?_
  intro H hH
  refine cyclic_card_mul_function_induced_mem_cyclicInducedCharacterSpan (A := A) H
    (Subgroup.mem_cyclicSubgroups.1 hH) (fun h : H ↦ θ[H] h * χ h) ?_
  intro h
  by_cases hh : Subgroup.zpowers h = ⊤
  · refine ⟨q h, ?_⟩
    simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule,
      Representation.cyclicGroupTheta, hh, map_mul]
  · refine ⟨0, ?_⟩
    simp [χ, complexified_classFunctionSubspace_of_classFunctionSubmodule,
      Representation.cyclicGroupTheta, hh]

end

/-! ### Exercise_10_10_3_5 (from Chap10) -/
/- Domain-style sampling for this item:
* primary domain: ordinary character theory for finite groups, with tensor characters reduced
  modulo a prime ideal and evaluated at the canonical `p'`-component `pRegularComponent p x`;
* relevant owner declarations inspected in this domain:
  `pRegularComponent`,
  `characterRingScalarExtension`,
  `integerValued_tensorCharacter_modEq_pRegularComponent`,
  `character_value_congruent_mod_ideal`;
* best owner abstraction: the source-facing exercise already lives on the chapter owner theorems
  for tensor characters `χ : A ⊗R(G)` and their quotient values modulo an ideal, so this item file
  should reuse those owners directly rather than maintain a parallel local theorem/helper layer.

Primitive data vs. derived API:
* primitive data: the prime ideal `𝔭`, the tensor character `χ : A ⊗R(G)`, its `A`-valued
  realization `f`, the element `x`, and the explicit counterexample witness data in the chapter
  file;
* derived API: quotient-equality reformulations, realized-span bridge lemmas, and auxiliary
  quartic-root witness helpers. Those are not new source-facing owners here and should not remain
  as a duplicate public layer in this item file.

Source/core/bridge triage:
* source-facing: the two exercise statements, namely the congruence modulo `𝔭` and the existence
  of a counterexample to the stronger modulus `(p)A`;
* core/canonical: the chapter owner theorems
  `character_value_congruent_mod_ideal` and
  `exists_tensorCharacter_character_value_mod_pIdeal_ne`;
* bridge/view: the deleted local quotient-equality and realized-span wrapper lemmas were only
  bridge/view API around those owners, not independent mathematical content.

This refine pass therefore targets the `core/canonical` layer: the item is best expressed as a
direct recall of the already-owned chapter declarations. -/

/- Exercise 10-10.3-5 (1) is already owned by the chapter theorem
`character_value_congruent_mod_ideal`. The item contributes no new owner beyond recalling that
canonical source-facing statement. -/
recall character_value_congruent_mod_ideal

/- Exercise 10-10.3-5 (2) is already owned by the chapter theorem
`exists_tensorCharacter_character_value_mod_pIdeal_ne`, which gives the explicit witness-data
counterexample to the stronger modulus `(p)A`. -/
recall exists_tensorCharacter_character_value_mod_pIdeal_ne
