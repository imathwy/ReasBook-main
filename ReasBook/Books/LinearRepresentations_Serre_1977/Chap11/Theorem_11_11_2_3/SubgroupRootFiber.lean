import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap10.Theorem_10_10_5_2
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_5_2
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_2
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.GroupTheory.ConjClassesPower
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_3
import LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_5_6

noncomputable section

open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation
open scoped SubgroupInduction

universe u v

namespace Representation

section FrobeniusTheorem

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

local instance : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

local instance nthPow_mem_conjClass_decidablePred
    (n : ℕ+) (c : ConjClasses G) :
    DecidablePred (fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier) :=
  Classical.decPred _

/-- The source sum from Theorem `11-11.2-3`, obtained by summing `ρ.character x` over the
elements whose `n`th power lies in the conjugacy class `c`. -/
def conjugacyClassNthRootCharacterSum
    (n : ℕ+) (c : ConjClasses G) (ρ : Representation ℂ G V) :
    ℂ :=
  ∑ x : G with x ^ (n : ℕ) ∈ c.carrier, ρ.character x

/-- Helper for Theorem 11-11.2-3: every value of a virtual character is an algebraic integer. -/
lemma characterRing_value_isIntegral (χ : R(G)) (x : G) :
    IsIntegral ℤ (χ x) := by
  -- Induct over the algebraic generation of `R(G)` by honest irreducible characters.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ χ.property
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    simpa using Representation.char_isIntegral ρ.ρ x
  · intro n
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ n))
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro f g _ _ hf hg
    exact hf.mul hg

/-- Helper for Theorem 11-11.2-3: the inverse `n`th-root indicator whose normalized pairing with a
character is the textbook scalar. -/
def normalizedInverseNthRootIndicator
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) : G → ℂ :=
  fun x ↦
    (Nat.card G : ℂ) *
      ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
        Ψ^n(c.indicator) x⁻¹

/-- Helper for Theorem 11-11.2-3: the normalized inverse `n`th-root indicator is a class
function. -/
lemma normalizedInverseNthRootIndicator_isClassFunction
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) :
    _root_.IsClassFunction (normalizedInverseNthRootIndicator n c g) := by
  let _ := (inferInstance : Finite G)
  have hindicator_mem :
      (c.indicator : G → ℂ) ∈ classFunctionSubmodule ℂ G :=
    (c.indicatorClassFunctionSubmodule (R := ℂ)).property
  have hadams :
      _root_.IsClassFunction (Ψ^n((c.indicator : G → ℂ))) :=
    isClassFunction_adamsOperator n
      ((mem_classFunctionSubmodule_iff ℂ (c.indicator : G → ℂ)).1 hindicator_mem)
  have hinv :
      _root_.IsClassFunction (fun x : G ↦ Ψ^n((c.indicator : G → ℂ)) x⁻¹) := by
    refine ⟨fun {x y} hxy ↦ ?_⟩
    have hxy_conj : IsConj x y :=
      (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
    rcases isConj_iff.1 hxy_conj with ⟨a, ha⟩
    have hxy_inv : IsConj x⁻¹ y⁻¹ := by
      refine isConj_iff.2 ⟨a, ?_⟩
      calc
        a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by simp [mul_assoc]
        _ = y⁻¹ := by rw [ha]
    exact hadams.eq_of_isConj hxy_inv
  refine ⟨fun {x y} hxy ↦ ?_⟩
  -- Reduce conjugacy invariance of the owner to the already-proved invariance of the inverse
  -- Adams transform.
  exact congrArg
    (fun z : ℂ ↦
      (Nat.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) * z)
    (hinv.eq_of_isConj ((ConjClasses.mk_eq_mk_iff_isConj).1 hxy))

/-- Helper for Theorem 11-11.2-3: pairing the normalized inverse root indicator with
`ρ.character` is exactly the displayed textbook scalar. -/
lemma normalizedInverseNthRootIndicator_pairing_eq
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (ρ : Representation ℂ G V) :
    ⟪normalizedInverseNthRootIndicator n c g, ρ.character⟫ =
      ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
        conjugacyClassNthRootCharacterSum n c ρ := by
  let _ := (inferInstance : FiniteDimensional ℂ V)
  -- Unfold the owner and rewrite the pairing so that the inverse on the left argument produces
  -- the direct `n`th-root fiber from the source sum.
  rw [Representation.groupFunctionPairingOverField]
  have hcard_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    (Fintype.card G : ℂ)⁻¹ *
        ∑ s : G,
          normalizedInverseNthRootIndicator n c g s⁻¹ * ρ.character s
      = (Fintype.card G : ℂ)⁻¹ *
          ∑ s : G,
            (((Fintype.card G : ℂ) *
                ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) *
                  (Ψ^n(c.indicator) s * ρ.character s)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [normalizedInverseNthRootIndicator, Nat.card_eq_fintype_card, mul_assoc]
    _ = (Fintype.card G : ℂ)⁻¹ *
          (((Fintype.card G : ℂ) *
              ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) *
            ∑ s : G, Ψ^n(c.indicator) s * ρ.character s) := by
            rw [← Finset.mul_sum]
    _ = (((Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ)) *
          ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) *
            ∑ s : G, Ψ^n(c.indicator) s * ρ.character s := by
            ring
    _ = ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          ∑ s : G, Ψ^n(c.indicator) s * ρ.character s := by
            rw [inv_mul_cancel₀ hcard_ne_zero, one_mul]
    _ =
        ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          ∑ s : G, if s ^ (n : ℕ) ∈ c.carrier then ρ.character s else 0 := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            by_cases hsroot : s ^ (n : ℕ) ∈ c.carrier
            · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
            · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    _ =
        ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          ∑ s : G with s ^ (n : ℕ) ∈ c.carrier, ρ.character s := by
            congr 1
            rw [Finset.sum_filter]
    _ = ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          conjugacyClassNthRootCharacterSum n c ρ := by
            rw [conjugacyClassNthRootCharacterSum]

/-- Helper for Theorem 11-11.2-3: elements of a fixed conjugacy class have the same order. -/
lemma orderOf_eq_of_mem_conjClass
    {c : ConjClasses G} (g : c.carrier) {x : G} (hx : x ∈ c.carrier) :
    orderOf x = orderOf (g : G) := by
  let _ := (inferInstance : Finite G)
  -- Pass from equality of conjugacy classes to semiconjugacy and use invariance of `orderOf`.
  have hxmk : ConjClasses.mk x = c := ConjClasses.mem_carrier_iff_mk_eq.mp hx
  have hgmk : ConjClasses.mk (g : G) = c := ConjClasses.mem_carrier_iff_mk_eq.mp g.property
  have hconj : ConjClasses.mk x = ConjClasses.mk (g : G) := hxmk.trans hgmk.symm
  rcases ConjClasses.mk_eq_mk_iff_isConj.mp hconj with ⟨a, ha⟩
  simpa using SemiconjBy.orderOf_eq (a := (a : G)) ha

/-- Helper for Theorem 11-11.2-3: if an elementary subgroup contains one `n`th root whose
`n`th power lies in `c`, then the target denominator `gcd(orderOf g,n)` already divides the
subgroup cardinality. -/
lemma gcd_classOrder_dvd_gcd_subgroup_card_of_exists_root
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (H : Subgroup G)
    (hex : ∃ h : H, (h : G) ^ (n : ℕ) ∈ c.carrier) :
    Nat.gcd (orderOf (g : G)) (n : ℕ) ∣ Nat.gcd (Nat.card H) (n : ℕ) := by
  rcases hex with ⟨h, hh⟩
  have hpow_order :
      orderOf ((h : G) ^ (n : ℕ)) = orderOf (h : G) / Nat.gcd (orderOf (h : G)) (n : ℕ) := by
    simpa using (orderOf_pow (n := (n : ℕ)) (h : G))
  have hclass_dvd :
      orderOf (g : G) ∣ orderOf (h : G) := by
    -- The chosen root identifies `orderOf g` with the order of `h ^ n`, which divides `orderOf h`.
    have hroot_order :
        orderOf ((h : G) ^ (n : ℕ)) = orderOf (g : G) :=
      orderOf_eq_of_mem_conjClass (c := c) g hh
    exact hroot_order ▸ by
      rw [hpow_order]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (orderOf (h : G)) (n : ℕ))
  have hsubgroup_card :
      orderOf (h : G) ∣ Nat.card H := by
    -- Convert the subgroup-order divisor statement back to the ambient element.
    simpa [Subgroup.orderOf_mk] using (orderOf_dvd_natCard h)
  have hcard :
      Nat.gcd (orderOf (g : G)) (n : ℕ) ∣ Nat.card H := by
    exact dvd_trans (Nat.gcd_dvd_left _ _) (dvd_trans hclass_dvd hsubgroup_card)
  -- Append the obvious `gcd` divisor on the second factor.
  exact Nat.dvd_gcd hcard (Nat.gcd_dvd_right (orderOf (g : G)) (n : ℕ))

/-- Helper for Theorem 11-11.2-3: if a subgroup contributes an `n`th root into `c`, then the
inverse target denominator can be rewritten through the subgroup-cardinality gcd by an integral
scalar quotient. -/
lemma inv_classOrder_gcd_eq_integral_scalar_mul_inv_subgroup_gcd_of_exists_root
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier) (H : Subgroup G)
    (hex : ∃ h : H, (h : G) ^ (n : ℕ) ∈ c.carrier) :
    ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) =
      algebraMap (integralClosure ℤ ℂ) ℂ
        (((Nat.gcd (Nat.card H) (n : ℕ) / Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
            integralClosure ℤ ℂ)) *
        ((Nat.gcd (Nat.card H) (n : ℕ) : ℂ)⁻¹) := by
  have hdiv :
      Nat.gcd (orderOf (g : G)) (n : ℕ) ∣ Nat.gcd (Nat.card H) (n : ℕ) :=
    gcd_classOrder_dvd_gcd_subgroup_card_of_exists_root (G := G) n c g H hex
  have hclass_ne_zero :
      ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  have hsubgroup_ne_zero :
      ((Nat.gcd (Nat.card H) (n : ℕ) : ℕ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_right n.ne_zero)
  -- Rewrite the larger denominator as an integral scalar multiple of the target one.
  rw [show
      algebraMap (integralClosure ℤ ℂ) ℂ
          (((Nat.gcd (Nat.card H) (n : ℕ) /
                Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) :
              integralClosure ℤ ℂ)) =
        ((Nat.gcd (Nat.card H) (n : ℕ) /
            Nat.gcd (orderOf (g : G)) (n : ℕ) : ℕ) : ℂ) by
      rfl]
  rw [Nat.cast_div hdiv]
  · field_simp [hclass_ne_zero, hsubgroup_ne_zero]
  · exact hclass_ne_zero

/-- Helper for Theorem 11-11.2-3: the normalized pairing of two honest characters is the
dimension of the intertwining space. -/
lemma groupFunctionPairing_character_eq_finrank_intertwiningMap_rootfiber_local
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) (ρ : Representation ℂ G V) :
    ⟪σ.character, ρ.character⟫ = (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  -- This is the normalized character-pairing identity from mathlib, rewritten into the local
  -- pairing notation used in this file.
  simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ))

/-- Helper for Theorem 11-11.2-3: pairing any virtual character with an honest representation
character gives an algebraic integer. -/
lemma characterRing_pairing_isIntegral_with_rep_character
    (η : R(G)) (ρ : Representation ℂ G V) :
    IsIntegral ℤ ⟪(η : G → ℂ), ρ.character⟫ := by
  -- Route correction: this base-case theorem should be reproved from the honest-character span
  -- together with the finite-dimensional intertwining-space formula.
  let S : Set (G → ℂ) :=
    { ψ |
        ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
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
          change ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
            (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
            ψ = σ.character at hψ
          rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
          intro g hg
          induction hg using Submodule.span_induction with
          | mem ξ hξ =>
              change ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module ℂ X)
                (_ : FiniteDimensional ℂ X) (τ : Representation ℂ G X),
                ξ = τ.character at hξ
              rcases hξ with ⟨X, _instXAdd, _instXMod, _instXfd, τ, rfl⟩
              let π : Representation ℂ G (TensorProduct ℂ W X) := σ.tprod τ
              -- Tensor products realize pointwise products of honest characters.
              refine Submodule.subset_span ?_
              refine ⟨TensorProduct ℂ W X, inferInstance, inferInstance, inferInstance, π, ?_⟩
              change σ.character * τ.character = (σ.tprod τ).character
              exact (Representation.char_tensor (ρ := σ) (σ := τ)).symm
          | zero =>
              have hzero_mul : σ.character * (0 : G → ℂ) = 0 := by
                ext x
                simp
              rw [hzero_mul]
              exact
                (Submodule.zero_mem (Submodule.span ℤ S) : (0 : G → ℂ) ∈ Submodule.span ℤ S)
          | add ξ ζ _ _ hξ hζ =>
              simpa [mul_add] using
                Submodule.add_mem (Submodule.span ℤ S) hξ hζ
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
          exact
            (Submodule.zero_mem (Submodule.span ℤ S) : (0 : G → ℂ) ∈ Submodule.span ℤ S)
      | add f₁ f₂ _ _ hf₁ hf₂ =>
          intro g hg
          simpa [add_mul] using
            Submodule.add_mem (Submodule.span ℤ S) (hf₁ g hg) (hf₂ g hg)
      | smul n f _ hf =>
          intro g hg
          simpa [zsmul_eq_mul, mul_left_comm, mul_assoc] using
            Submodule.smul_mem (Submodule.span ℤ S) n (hf g hg)
    exact hfg g hg
  have hηspan : (η : G → ℂ) ∈ Submodule.span ℤ S := by
    -- The local character ring is generated by irreducible characters, while the `ℤ`-span of all
    -- honest characters is stable under the ring operations via tensor products and the trivial
    -- representation.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ η.2
    · intro ψ hψ
      rcases hψ with ⟨σ, hσfd, _hσirr, rfl⟩
      exact Submodule.subset_span ⟨σ, inferInstance, inferInstance, hσfd, σ.ρ, rfl⟩
    · intro n
      have htriv :
          (Representation.trivial ℂ G (ULift.{u} ℂ)).character = (1 : G → ℂ) := by
        ext x
        simp [Representation.character, Representation.trivial]
      rw [show algebraMap ℤ (G → ℂ) n =
          n • (Representation.trivial ℂ G (ULift.{u} ℂ)).character by
        ext x
        simp [htriv]]
      exact
        Submodule.smul_mem (Submodule.span ℤ S) n <|
          Submodule.subset_span
            ⟨ULift.{u} ℂ, inferInstance, inferInstance, inferInstance,
              Representation.trivial ℂ G (ULift.{u} ℂ), rfl⟩
    · intro f g _ _ hf hg
      exact Submodule.add_mem (Submodule.span ℤ S) hf hg
    · intro f g _ _ hf hg
      exact hmul_span hf hg
  -- Evaluate the pairing on the honest-character spanning set.
  refine
    Submodule.span_induction
      (p := fun ψ _ ↦ IsIntegral ℤ ⟪ψ, ρ.character⟫)
      ?_ ?_ ?_ ?_ hηspan
  · intro ψ hψ
    change ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : FiniteDimensional ℂ W) (σ : Representation ℂ G W),
      ψ = σ.character at hψ
    rcases hψ with ⟨W, _instWAdd, _instWMod, _instWfd, σ, rfl⟩
    -- For a genuine character, the pairing is the finite dimension of the intertwining space.
    rw [groupFunctionPairing_character_eq_finrank_intertwiningMap_rootfiber_local (G := G)
      (V := V) σ ρ]
    exact isIntegral_algebraMap
  · -- The pairing with the zero class function is zero.
    simpa [Representation.groupFunctionPairingOverField] using
      (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · intro ψ ξ _ _ hψ hξ
    simpa [Representation.groupFunctionPairing_add_left] using hψ.add hξ
  · intro n ψ _ hψ
    rw [show ⟪n • ψ, ρ.character⟫ = (n : ℂ) * ⟪ψ, ρ.character⟫ by
      simpa [zsmul_eq_mul] using
        (Representation.groupFunctionPairing_smul_left
          (a := (n : ℂ)) (φ := ψ) (ψ := ρ.character))]
    exact (isIntegral_algebraMap : IsIntegral ℤ (n : ℂ)).mul hψ

/-- Helper for Theorem 11-11.2-3: the raw `n`th-root fiber sum of a degree-`1` character on a
subgroup is algebraically integral. -/
lemma linearCharacter_sum_isIntegral_on_subgroup_root_fiber
    (n : ℕ+) (c : ConjClasses G) (H : Subgroup G) (χ : H →* ℂˣ) :
    IsIntegral ℤ
      (Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
        fun h ↦ (χ h : ℂ)) := by
  -- Every summand is a linear-character value, hence an algebraic integer.
  refine IsIntegral.sum _ fun h hh ↦ ?_
  simpa using Representation.char_isIntegral χ.toRepresentation h

/-- Helper for Theorem 11-11.2-3: a degree-`1` character on a product group factors through the
two coordinate inclusions. -/
lemma linearCharacter_on_prod_apply_eq_mul
    {C P : Type*} [Group C] [Group P]
    (χ : C × P →* ℂˣ) (a : C) (u : P) :
    χ (a, u) = (χ.comp (MonoidHom.inl C P) a) * (χ.comp (MonoidHom.inr C P) u) := by
  -- Split `(a, u)` as the product of its two coordinate inclusions and apply multiplicativity.
  calc
    χ (a, u) = χ ((a, 1) * (1, u)) := by simp
    _ = χ (a, 1) * χ (1, u) := by rw [map_mul]
    _ = (χ.comp (MonoidHom.inl C P) a) * (χ.comp (MonoidHom.inr C P) u) := by
          rfl

/-- Helper for Theorem 11-11.2-3: transporting the subgroup root-fiber sum along an elementary
product decomposition rewrites it as a sum over the product coordinates. -/
lemma filtered_rootFiber_sum_eq_sum_over_elementary_product
    (n : ℕ+) (c : ConjClasses G) (H : Subgroup G) (χ : H →* ℂˣ)
    {p : ℕ} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
      (fun h ↦ (χ h : ℂ)) =
      Finset.sum (Finset.univ.filter fun y : C × P ↦
          (((hCP.isComplement.prodMulEquiv hCP.commute) y : H) : G) ^ (n : ℕ) ∈ c.carrier)
        (fun y ↦ (χ ((hCP.isComplement.prodMulEquiv hCP.commute) y) : ℂ)) := by
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  -- Rewrite both sides as indicator sums, then reindex along the product equivalence `e`.
  calc
    Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
        (fun h ↦ (χ h : ℂ))
      = ∑ h : H, if (h : G) ^ (n : ℕ) ∈ c.carrier then (χ h : ℂ) else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ y : C × P,
          if ((e y : H) : G) ^ (n : ℕ) ∈ c.carrier then (χ (e y) : ℂ) else 0 := by
          symm
          simpa [e] using
            Equiv.sum_comp e.toEquiv
              (fun h : H ↦ if (h : G) ^ (n : ℕ) ∈ c.carrier then (χ h : ℂ) else 0)
    _ = Finset.sum (Finset.univ.filter fun y : C × P ↦
          ((e y : H) : G) ^ (n : ℕ) ∈ c.carrier)
        (fun y ↦ (χ (e y) : ℂ)) := by
          rw [Finset.sum_filter]

/-- Helper for Theorem 11-11.2-3: the subgroup pairing with the inverse root owner rewrites as
the subgroup index times the normalized root-fiber sum. -/
lemma linearCharacter_pairing_normalizedInverseNthRootIndicator_eq
    (n : ℕ+) (c : ConjClasses G) (g : c.carrier)
    (H : Subgroup G) (χ : H →* ℂˣ) :
    ⟪χ.toRepresentation.character, fun h : H ↦ normalizedInverseNthRootIndicator n c g h⟫ =
      (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) *
        (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
          Finset.sum (Finset.univ.filter fun h : H ↦ (h : G) ^ (n : ℕ) ∈ c.carrier)
            fun h ↦ (χ h : ℂ)) := by
  -- Symmetry places the inverse-root owner on the left, so the pairing formula removes the
  -- inverse built into its definition.
  have hpair_eq :
      (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H, normalizedInverseNthRootIndicator n c g (s⁻¹ : H) *
            χ.toRepresentation.character s =
        (((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)) *
          (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            Finset.sum (Finset.univ.filter fun s : H ↦ (s : G) ^ (n : ℕ) ∈ c.carrier)
              fun s ↦ (χ s : ℂ)) := by
    calc
    (Fintype.card H : ℂ)⁻¹ *
        ∑ s : H, normalizedInverseNthRootIndicator n c g (s⁻¹ : H) *
          χ.toRepresentation.character s
      = (Fintype.card H : ℂ)⁻¹ *
          ∑ s : H,
            (((Fintype.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) *
              (Ψ^n(c.indicator) (s : G) * (χ s : ℂ))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [normalizedInverseNthRootIndicator, mul_assoc]
    _ = (Fintype.card H : ℂ)⁻¹ *
          (((Fintype.card G : ℂ) * ((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹)) *
            ∑ s : H, Ψ^n(c.indicator) (s : G) * (χ s : ℂ)) := by
            rw [← Finset.mul_sum]
    _ = (((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)) *
          (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            ∑ s : H, Ψ^n(c.indicator) (s : G) * (χ s : ℂ)) := by
            ring
    _ = (((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)) *
          (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            ∑ s : H, if (s : G) ^ (n : ℕ) ∈ c.carrier then (χ s : ℂ) else 0) := by
            congr 2
            refine Finset.sum_congr rfl ?_
            intro s hs
            by_cases hsroot : (s : G) ^ (n : ℕ) ∈ c.carrier
            · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
            · simp [Representation.adamsOperator, ConjClasses.indicator, hsroot]
    _ = (((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)) *
          (((Nat.gcd (orderOf (g : G)) (n : ℕ) : ℂ)⁻¹) *
            Finset.sum (Finset.univ.filter fun s : H ↦ (s : G) ^ (n : ℕ) ∈ c.carrier)
              fun s ↦ (χ s : ℂ)) := by
            congr 1
            congr 1
            rw [Finset.sum_filter]
  rw [Representation.groupFunctionPairing_comm, Representation.groupFunctionPairingOverField]
  simpa [Nat.card_eq_fintype_card, MonoidHom.toRepresentation_character_apply] using hpair_eq

/-- Helper for Theorem 11-11.2-3: the subgroup averaging factor `|G| / |H|` is an integer, hence
an algebraic integer. -/
lemma subgroup_index_scalar_isIntegral (H : Subgroup G) :
    IsIntegral ℤ (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) := by
  have hcardH_ne_zero : (Fintype.card H : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨1⟩).ne'
  have hcard : (Fintype.card G : ℂ) = (Fintype.card H : ℂ) * (H.index : ℂ) := by
    have hcard_nat : (Nat.card H : ℂ) * (H.index : ℂ) = (Nat.card G : ℂ) := by
      exact_mod_cast H.card_mul_index
    simpa [Nat.card_eq_fintype_card, mul_comm] using hcard_nat.symm
  have hscalar :
      ((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ) = (H.index : ℂ) := by
    calc
      ((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)
        = ((Fintype.card H : ℂ)⁻¹) * ((Fintype.card H : ℂ) * (H.index : ℂ)) := by rw [hcard]
      _ = (((Fintype.card H : ℂ)⁻¹) * (Fintype.card H : ℂ)) * (H.index : ℂ) := by ring
      _ = (H.index : ℂ) := by
            rw [inv_mul_cancel₀ hcardH_ne_zero, one_mul]
  have hintegral :
      IsIntegral ℤ (((Fintype.card H : ℂ)⁻¹) * (Fintype.card G : ℂ)) :=
    hscalar ▸ (isIntegral_algebraMap : IsIntegral ℤ (H.index : ℂ))
  simpa [Nat.card_eq_fintype_card] using hintegral

/-- Helper for Theorem 11-11.2-3: the image of `integralClosure ℤ ℂ` in `ℂ` is closed under
addition. -/
lemma range_algebraMap_add_integralClosure {z w : ℂ}
    (hz : z ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
    (hw : w ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)) :
    z + w ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨a + b, by simp⟩

/-- Helper for Theorem 11-11.2-3: the image of `integralClosure ℤ ℂ` in `ℂ` is closed under
multiplication. -/
lemma range_algebraMap_mul_integralClosure {z w : ℂ}
    (hz : z ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ))
    (hw : w ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ)) :
    z * w ∈ Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  rcases hz with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  exact ⟨a * b, by simp⟩

/-- Helper for Theorem 11-11.2-3: the subgroup averaging factor `|G| / |H|` comes from the
integral closure of `ℤ` in `ℂ`. -/
lemma subgroup_index_scalar_mem_range_integralClosure (H : Subgroup G) :
    (((Nat.card H : ℂ)⁻¹) * (Nat.card G : ℂ)) ∈
      Set.range (algebraMap (integralClosure ℤ ℂ) ℂ) := by
  -- Convert the already-proved algebraic integrality of the subgroup index scalar into explicit
  -- membership in the integral closure image.
  exact
    (IsIntegralClosure.isIntegral_iff
      (A := integralClosure ℤ ℂ) (R := ℤ) (B := ℂ)).1
      (subgroup_index_scalar_isIntegral (G := G) H)

end FrobeniusTheorem

end Representation
