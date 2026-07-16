import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_4
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_2_3
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_3_3
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_2_1.PRegularEndgame
import LinearRepresentations_Serre_1977.Serre.Chap11.Theorem_11_11_2_1
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Representation
open scoped BigOperators Representation SubgroupInduction

section

variable {G : Type} [Group G] [Finite G]

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
        _root_.mul_mem_pElementaryInducedCharacterSpan_local
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
    ConjClasses.mk (_root_.conjClassRepresentative c) = c :=
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

-- NOTE (falsification record): the former private helper `pregular_indicator_mem_characterRing`
-- (the indicator of the `p`-regular locus as an integral virtual character) and its dead
-- consumer chain (`nat_dvd_of_isIntegral_natCast_div`,
-- `groupFunctionPairing_character_eq_finrank_intertwiningMap_local`,
-- `characterRing_pairing_isIntegral_with_rep_character_local`, `pregular_indicator_eq_one`)
-- have been deleted: the statement was PROVEN FALSE in
-- `Representation.Brauer18.pregular_indicator_not_mem_characterRing`
-- (`Serre.Chap10.Theorem_10_10_2_1.PRegularEndgame`). The main theorem below now follows
-- Serre's actual Theorem 18' route via `Brauer18.const_primeToPart_mem_ownerSpan`.

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
  -- Theorem 18' (the §10.4 endgame): the constant function `l` lies in `A ⊗ V_p`.
  have hconst : (fun _ : G ↦ (l : ℂ)) ∈ Representation.Brauer18.ownerSpan (V[p](G)) :=
    Representation.Brauer18.const_primeToPart_mem_ownerSpan (V[p](G)) p n l hcard
      (fun χ ψ hψ ↦
        Representation.mul_mem_pElementaryInducedCharacterSpan (G := G) (p := p) (χ := χ) hψ)
      (fun K hK χ ↦ by
        rw [Representation.pElementaryInducedCharacterSpan]
        let _ : DecidablePred (fun J : Subgroup G ↦ IsPElementary p J) := Classical.decPred _
        have hKmem : K ∈ Finset.univ.filter (fun J : Subgroup G ↦ IsPElementary p J) := by
          simp [hK]
        exact Representation.characterRingInduction_mem_artinInducedCharacterSubmodule hKmem χ)
  -- The §10.4 owner span lands in the Chapter 10 scalar-extension bridge: both are spans of the
  -- image of `V_p` over the algebraic integers.
  have howner :
      Representation.Brauer18.ownerSpan (V[p](G)) ≤
        Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G := by
    rw [Representation.pElementaryInducedCharacterScalarExtension_eq_span]
    refine Submodule.span_le.2 ?_
    rintro φ ⟨β, rfl⟩
    exact Submodule.subset_span
      ⟨β, by simp [Representation.pElementaryInducedCharacterToFunction]⟩
  -- The constant function `l` is the realization of the integral character `l • 1`.
  have hconst_fun : ((l • (1 : R(G)) : R(G)) : G → ℂ) = fun _ : G ↦ (l : ℂ) := by
    ext s
    simp
  have hl1_scalar :
      ((l • (1 : R(G)) : R(G)) : G → ℂ) ∈
        Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G := by
    rw [hconst_fun]
    exact howner hconst
  -- Descend through the intersection theorem `(A ⊗ V_p) ∩ R(G) = image(V_p)`.
  have hl1_inter :
      (((l • (1 : R(G)) : R(G)) : G → ℂ) ∈
        (Representation.pElementaryInducedCharacterScalarExtension
          (↥(integralClosure ℤ ℂ)) p G : Set (G → ℂ))) ∧
        (((l • (1 : R(G)) : R(G)) : G → ℂ) ∈ (R(G) : Set (G → ℂ))) :=
    ⟨hl1_scalar, (l • (1 : R(G)) : R(G)).property⟩
  have hl1_image :
      (((l • (1 : R(G)) : R(G)) : G → ℂ) ∈
        ((LinearMap.range (Representation.pElementaryInducedCharacterToFunction p G)) :
          Set (G → ℂ))) := by
    rw [← Representation.pElementaryInducedCharacterScalarExtension_inter_characterRing_eq_image
      (A := ↥(integralClosure ℤ ℂ)) (G := G) (p := p)]
    simpa [Set.mem_inter_iff] using hl1_inter
  rcases hl1_image with ⟨γ, hγ⟩
  have hγeq : (γ : R(G)) = l • (1 : R(G)) := by
    apply Subtype.ext
    simpa [Representation.pElementaryInducedCharacterToFunction] using hγ
  simpa [hγeq] using γ.property

end
