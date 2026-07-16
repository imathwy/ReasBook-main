import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.ExternalTensor
import LinearRepresentations_Serre_1977.Serre.FiniteToFintype
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators TensorProduct Representation Representation.ExternalTensor

noncomputable section

universe u v

namespace Representation

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

-- Source/core/bridge triage: this proposition is `source-facing`. Its primitive data are only the
-- finite group `G`, the complex representation `ρ`, and irreducibility. The finite-dimensionality
-- used in the divisibility argument is derived from the canonical mathlib owner
-- `IsIrreducible.finiteDimensional_of_finite ρ`, so it should not remain primitive public data.
-- The core reused owners are the Chapter 2 transport theorem
-- `isIrreducible_of_nonempty_equiv`, the Chapter 6 divisibility theorem `finrank_dvd_card`, and
-- the group-theoretic owner `(Subgroup.center G).index = Nat.card (G ⧸ Subgroup.center G)`. The
-- tensor-power descent along the product-one subgroup of `(Subgroup.center G)^m` is only a
-- `bridge/view` construction that produces irreducible quotient representations to which
-- `finrank_dvd_card` applies.
--
-- Sampled owner declarations in this domain:
-- * `IsIrreducible.finiteDimensional_of_finite`
-- * `isIrreducible_of_nonempty_equiv`
-- * `self_character_pairing_eq_one_iff_isIrreducible`
-- * `finrank_dvd_card`
-- * the external tensor owner notation `σ ⊠ τ`
--
-- Proof sketch: apply `finrank_dvd_card` to the irreducible quotients obtained from the descended
-- tensor powers of `ρ`, deriving `FiniteDimensional ℂ V` first from
-- `IsIrreducible.finiteDimensional_of_finite ρ`. The resulting family of divisibility relations
-- forces `Module.finrank ℂ V` to divide the index of the center.
/-- Helper for Proposition 6-6.5-5: the action of the center on an irreducible complex
representation is given by a multiplicative scalar character. -/
lemma center_scalar_action_hom [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ∃ μ : Subgroup.center G →* ℂˣ, ∀ s : Subgroup.center G,
      ρ (s : G) = (μ s : ℂ) • (1 : Module.End ℂ V) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module (MonoidAlgebra ℂ G) V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra ℂ G) V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) V
  let exists_smul_id_of_mem_center :
      ∀ s : G, s ∈ Submonoid.center G → ∃ z : ℂ, ρ s = z • (1 : Module.End ℂ V) :=
    fun s hs ↦ by
      obtain ⟨z, hz⟩ := intertwiningMap_eq_smul_id ρ
        (Representation.IntertwiningMap.centralMul ρ s hs)
      refine ⟨z, ?_⟩
      simpa using congrArg Representation.IntertwiningMap.toLinearMap hz
  let scalar : Subgroup.center G → ℂ := fun s ↦
    Classical.choose <| exists_smul_id_of_mem_center (s : G)
      (show (s : G) ∈ Submonoid.center G from by
        simpa [Subgroup.center_toSubmonoid] using s.2)
  have hscalar (s : Subgroup.center G) :
      ρ (s : G) = scalar s • (1 : Module.End ℂ V) := by
    -- Each central group element acts by a homothety via the Chapter 3 Schur-lemma bridge.
    simpa [scalar] using
      (Classical.choose_spec <| exists_smul_id_of_mem_center (s : G)
        (show (s : G) ∈ Submonoid.center G from by
          simpa [Subgroup.center_toSubmonoid] using s.2))
  have hsmul_injective : Function.Injective fun z : ℂ ↦ z • (1 : Module.End ℂ V) := by
    -- A scalar multiple of the identity is determined by its value on any nonzero vector.
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro z w hzw
    have hvw : z • v = w • v := by
      simpa using congrArg (fun f : Module.End ℂ V ↦ f v) hzw
    have hsub : (z - w) • v = 0 := by
      rw [sub_smul, hvw, sub_self]
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (hv hzero).elim
  have hscalar_ne_zero (s : Subgroup.center G) : scalar s ≠ 0 := by
    intro hz
    have hzero : ρ (s : G) = 0 := by simpa [hscalar s, hz]
    have hone : (1 : Module.End ℂ V) = 0 := by
      calc
        (1 : Module.End ℂ V) = ρ (s : G) * ρ ((s : G)⁻¹) := by
          simpa using ρ.map_mul (s : G) ((s : G)⁻¹)
        _ = 0 := by rw [hzero]; simp
    exact one_ne_zero hone
  let μ : Subgroup.center G →* ℂˣ := {
    toFun := fun s ↦ Units.mk0 (scalar s) (hscalar_ne_zero s)
    map_one' := by
      -- The identity element acts as the identity operator, so the scalar at `1` is `1`.
      ext
      apply hsmul_injective
      calc
        scalar 1 • (1 : Module.End ℂ V) = ρ (1 : G) := (hscalar 1).symm
        _ = (1 : ℂ) • (1 : Module.End ℂ V) := by simp
    map_mul' := by
      intro s t
      -- Comparing the operator of `s * t` with the product of the operators of `s` and `t`
      -- forces multiplicativity of the scalar character.
      ext
      apply hsmul_injective
      calc
        scalar (s * t) • (1 : Module.End ℂ V) = ρ (s * t : G) := (hscalar (s * t)).symm
        _ = ρ (s : G) * ρ (t : G) := by simp
        _ = (scalar s * scalar t) • (1 : Module.End ℂ V) := by
              rw [hscalar s, hscalar t]
              calc
                (scalar s • (1 : Module.End ℂ V)) * (scalar t • (1 : Module.End ℂ V))
                    = scalar s • ((1 : Module.End ℂ V) * (scalar t • (1 : Module.End ℂ V))) := by
                        rw [smul_mul_assoc]
                _ = scalar s • (scalar t • (1 : Module.End ℂ V)) := by simp
                _ = (scalar s * scalar t) • (1 : Module.End ℂ V) := by rw [smul_smul]
  }
  refine ⟨μ, ?_⟩
  intro s
  simpa [μ] using hscalar s

/-- Helper for Proposition 6-6.5-5: if every positive power of `n` divides the corresponding power
of `a` up to a fixed nonzero factor `c`, then `n` already divides `a`. -/
lemma dvd_of_forall_succ_pow_dvd_center_card_mul_pow {n c a : ℕ} (hc : 0 < c)
    (h : ∀ m : ℕ, n ^ (m + 1) ∣ c * a ^ (m + 1)) :
    n ∣ a := by
  by_cases hn : n = 0
  · -- If `n = 0`, the first divisibility relation forces `a = 0`, so the conclusion is trivial.
    subst hn
    have hzero := h 0
    rw [pow_one, zero_dvd_iff] at hzero
    have ha0 : a = 0 := by
      rw [pow_one, mul_eq_zero] at hzero
      exact Or.resolve_left hzero hc.ne'
    simp [ha0]
  by_cases ha : a = 0
  · -- If `a = 0`, divisibility is immediate.
    subst ha
    exact dvd_zero n
  -- Compare prime factor multiplicities with the choice `m = v_p(c)`.
  refine Nat.factorization_le_iff_dvd hn ha |>.mp ?_
  intro p
  by_cases hp : Nat.Prime p
  · let m := c.factorization p
    have hdiv := h m
    have hfac :=
      Nat.factorization_le_iff_dvd (pow_ne_zero (m + 1) hn)
        (mul_ne_zero hc.ne' (pow_ne_zero (m + 1) ha)) |>.mpr hdiv
    have hfac' := hfac p
    have hfac'' : (m + 1) * n.factorization p ≤ m + (m + 1) * a.factorization p := by
      simpa [Nat.factorization_mul hc.ne' (pow_ne_zero (m + 1) ha), Nat.factorization_pow,
        Finsupp.smul_apply, Pi.smul_apply, m] using hfac'
    refine le_of_not_gt ?_
    intro hlt
    have hsucc : a.factorization p + 1 ≤ n.factorization p := Nat.succ_le_of_lt hlt
    have hpow :
        (m + 1) * (a.factorization p + 1) ≤ m + (m + 1) * a.factorization p := by
      exact le_trans (Nat.mul_le_mul_left (m + 1) hsucc) hfac''
    have hpow' :
        (m + 1) * a.factorization p + (m + 1) ≤ (m + 1) * a.factorization p + m := by
      simpa [Nat.mul_add, add_comm, add_left_comm, add_assoc] using hpow
    have hm : m + 1 ≤ m := by
      exact add_le_add_iff_left ((m + 1) * a.factorization p) |>.mp hpow'
    exact (Nat.not_succ_le_self m) hm
  · simpa [Nat.factorization_eq_zero_of_not_prime n hp,
      Nat.factorization_eq_zero_of_not_prime a hp]

/-- Helper for Proposition 6-6.5-5: precomposing an irreducible representation with a group
equivalence does not change its invariant subspaces, hence preserves irreducibility. -/
lemma isIrreducible_comp_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (σ : Representation ℂ H V) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Proposition 6-6.5-5: quotienting by a normal subgroup that acts trivially does not
create new invariant subspaces, so irreducibility descends to the quotient representation. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial
    (σ : Representation ℂ G V) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (σ.comp S.subtype)] [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.ofQuotient S) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (g : G ⧸ S) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for Proposition 6-6.5-5: replace a finite-dimensional representation space by a
small finite model and shrink the group universe at the same time. -/
noncomputable def finiteModelRep [Finite G] [Module.Finite ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ (Shrink.{0} G) (FGModuleRepr.ofFinite ℂ V) where
  toFun g :=
    (FGModuleRepr.ofFiniteEquiv ℂ V).symm.toLinearMap.comp
      ((ρ (Shrink.mulEquiv g)).comp (FGModuleRepr.ofFiniteEquiv ℂ V).toLinearMap)
  map_one' := by
    -- The transported action is conjugation by the fixed finite-model equivalence.
    ext x
    simp
  map_mul' g h := by
    -- Conjugation preserves multiplication, so the transported action is still a representation.
    ext x
    simp [LinearMap.comp_apply]

/-- Helper for Proposition 6-6.5-5: the small finite model carries exactly the same representation
as the shrunk original representation, up to equivalence. -/
noncomputable def finiteModelRepEquivComp [Finite G] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) :
    (finiteModelRep ρ).Equiv
      (ρ.comp (Shrink.mulEquiv : Shrink.{0} G ≃* G).toMonoidHom) :=
  Representation.Equiv.mk (FGModuleRepr.ofFiniteEquiv ℂ V) (fun g ↦ by
    -- The chosen linear equivalence intertwines the transported finite model with the shrunk
    -- original action by construction.
    ext x
    simp [finiteModelRep, LinearMap.comp_apply])

/-- Helper for Proposition 6-6.5-5: shrinking both factors of a product group is equivalent to
shrinking the product itself. -/
noncomputable def prodShrinkMulEquiv [Finite G] {H : Type*} [Group H] [Finite H] :
    (Shrink.{0} G × Shrink.{0} H) ≃* Shrink.{0} (G × H) :=
  (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
      (Shrink.mulEquiv : Shrink.{0} H ≃* H)).trans
    (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).symm

/-- Helper for Proposition 6-6.5-5: the tensor product of the two finite models is itself a finite
model for the tensor product space. -/
noncomputable def finiteModelTensorEquiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    (FGModuleRepr.ofFinite ℂ V ⊗[ℂ] FGModuleRepr.ofFinite ℂ W) ≃ₗ[ℂ]
      FGModuleRepr.ofFinite ℂ (V ⊗[ℂ] W) :=
  (TensorProduct.congr (FGModuleRepr.ofFiniteEquiv ℂ V) (FGModuleRepr.ofFiniteEquiv ℂ W)).trans
    (FGModuleRepr.ofFiniteEquiv ℂ (V ⊗[ℂ] W)).symm

/-- Helper for Proposition 6-6.5-5: the external tensor product of the two finite models matches
the finite model of the original external tensor product after the canonical shrink-identification
of the product group. -/
noncomputable def finiteModelExternalTensorEquiv
    [Finite G] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (V ⊗[ℂ] W)]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W) :
    Representation.Equiv
      (((finiteModelRep σ) ⊠ (finiteModelRep τ)).comp
        (prodShrinkMulEquiv.symm.toMonoidHom))
      (finiteModelRep (σ ⊠ τ)) :=
  Representation.Equiv.mk finiteModelTensorEquiv (fun g ↦ by
    -- The only group-theoretic work is to identify the two coordinates extracted from the shrunk
    -- product with the coordinates of the original pair.
    have hfst :
        Shrink.mulEquiv (prodShrinkMulEquiv.symm g).1 =
          (Shrink.mulEquiv g).1 :=
      congrArg Prod.fst <|
        (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
          (Shrink.mulEquiv : Shrink.{0} H ≃* H)).apply_symm_apply (Shrink.mulEquiv g)
    have hsnd :
        Shrink.mulEquiv (prodShrinkMulEquiv.symm g).2 =
          (Shrink.mulEquiv g).2 :=
      congrArg Prod.snd <|
        (MulEquiv.prodCongr (Shrink.mulEquiv : Shrink.{0} G ≃* G)
          (Shrink.mulEquiv : Shrink.{0} H ≃* H)).apply_symm_apply (Shrink.mulEquiv g)
    ext x y
    simp [finiteModelTensorEquiv, finiteModelRep, LinearMap.comp_apply, TensorProduct.map_tmul,
      hfst, hsnd])

/-- Helper for Proposition 6-6.5-5: the small finite model is irreducible whenever the original
representation is irreducible. -/
lemma finiteModelRep_isIrreducible [Finite G] [FiniteDimensional ℂ V] [Module.Finite ℂ V]
    (σ : Representation ℂ G V) [σ.IsIrreducible] :
    Representation.IsIrreducible (finiteModelRep σ) := by
  letI :
      Representation.IsIrreducible
        (σ.comp (Shrink.mulEquiv : Shrink.{0} G ≃* G).toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv (Shrink.mulEquiv : Shrink.{0} G ≃* G) σ
  -- First shrink the group, then transport the action to the fixed finite model.
  exact isIrreducible_of_nonempty_equiv ⟨(finiteModelRepEquivComp σ).symm⟩

/-- Helper for Proposition 6-6.5-5: the character of the external tensor product is the pointwise
product of the two factor characters. -/
lemma externalTensor_character_apply [Finite G] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W) (g : G × H) :
    (σ ⊠ τ).character g = σ.character g.1 * τ.character g.2 := by
  -- Expand the external tensor owner and apply the canonical tensor-character formula.
  simpa [Representation.character] using
    congrFun
      (Representation.char_tensor
        (σ.comp (MonoidHom.fst G H))
        (τ.comp (MonoidHom.snd G H)))
      g

/-- Helper for Proposition 6-6.5-5: the self-pairing of an external tensor product factors as the
product of the self-pairings of the two factors. -/
lemma externalTensor_self_pairing_eq_mul [Finite G] [Fintype G] {H : Type*} [Group H] [Finite H] [Fintype H]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W) :
    ⟪(σ ⊠ τ).character, (σ ⊠ τ).character⟫ =
      ⟪σ.character, σ.character⟫ * ⟪τ.character, τ.character⟫ := by
  classical
  have hsplit :
      ∑ g : G × H, (σ ⊠ τ).character g⁻¹ * (σ ⊠ τ).character g =
        ∑ g₁ : G, ∑ g₂ : H, (σ ⊠ τ).character (g₁, g₂)⁻¹ * (σ ⊠ τ).character (g₁, g₂) := by
    -- Expand the product-group sum into iterated sums using the product of the two universal
    -- finite sets so that the same `Fintype.ofFinite` instance is used throughout.
    rw [show (Finset.univ : Finset (G × H)) = (Finset.univ : Finset G).product Finset.univ by
          ext g
          rcases g with ⟨g₁, g₂⟩
          simp]
    simpa [Finset.product_eq_sprod] using
      (Finset.sum_product (Finset.univ : Finset G) (Finset.univ : Finset H)
        (fun g : G × H ↦ (σ ⊠ τ).character g⁻¹ * (σ ⊠ τ).character g))
  have hsum :
      ∑ g : G × H, (σ ⊠ τ).character g⁻¹ * (σ ⊠ τ).character g =
        (∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
          (∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂) := by
    calc
      ∑ g : G × H, (σ ⊠ τ).character g⁻¹ * (σ ⊠ τ).character g
          =
            ∑ g₁ : G, ∑ g₂ : H, (σ ⊠ τ).character (g₁, g₂)⁻¹ * (σ ⊠ τ).character (g₁, g₂) := by
              exact hsplit
      _ =
            ∑ g₁ : G, ∑ g₂ : H,
              (σ.character g₁⁻¹ * σ.character g₁) *
                (τ.character g₂⁻¹ * τ.character g₂) := by
              refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
              refine Finset.sum_congr rfl fun g₂ _ ↦ ?_
              have hInv :
                  (σ ⊠ τ).character (g₁, g₂)⁻¹ =
                    σ.character g₁⁻¹ * τ.character g₂⁻¹ := by
                simpa [Prod.fst_inv, Prod.snd_inv] using
                  externalTensor_character_apply σ τ ((g₁, g₂)⁻¹)
              have hVal :
                  (σ ⊠ τ).character (g₁, g₂) =
                    σ.character g₁ * τ.character g₂ := by
                simpa using externalTensor_character_apply σ τ (g := (g₁, g₂))
              rw [hInv, hVal]
              ring
      _ =
          ∑ g₁ : G,
            (σ.character g₁⁻¹ * σ.character g₁) *
              ∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂ := by
            refine Finset.sum_congr rfl fun g₁ _ ↦ ?_
            rw [Finset.mul_sum]
      _ =
          (∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
            (∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂) := by
            rw [Finset.sum_mul]
  have hcard :
      (Fintype.card (G × H) : ℂ) = (Fintype.card G : ℂ) * (Fintype.card H : ℂ) := by
    simpa [Nat.card_eq_fintype_card, Nat.cast_mul] using
      congrArg (fun n : ℕ ↦ (n : ℂ)) (Nat.card_prod G H)
  calc
    ⟪(σ ⊠ τ).character, (σ ⊠ τ).character⟫
        = (Fintype.card (G × H) : ℂ)⁻¹ *
            ∑ g : G × H, (σ ⊠ τ).character g⁻¹ * (σ ⊠ τ).character g := by
              unfold Representation.groupFunctionPairingOverField
              rfl
    _ =
        (Fintype.card (G × H) : ℂ)⁻¹ *
          ((∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
            (∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂)) := by
              rw [hsum]
    _ =
        (((Fintype.card G : ℂ) * (Fintype.card H : ℂ)) : ℂ)⁻¹ *
          ((∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
            (∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂)) := by
              simpa using congrArg
                (fun x : ℂ ↦ x⁻¹ *
                  ((∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
                    (∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂))) hcard
    _ =
        ((Fintype.card G : ℂ)⁻¹ * ∑ g₁ : G, σ.character g₁⁻¹ * σ.character g₁) *
          ((Fintype.card H : ℂ)⁻¹ * ∑ g₂ : H, τ.character g₂⁻¹ * τ.character g₂) := by
            rw [mul_inv_rev]
            ring
    _ = ⟪σ.character, σ.character⟫ * ⟪τ.character, τ.character⟫ := by
          unfold Representation.groupFunctionPairingOverField
          rfl

/-- Helper for Proposition 6-6.5-5: after moving both factors to the same finite-model owner, the
external tensor product is irreducible, and this remains true after identifying the product of the
shrunk groups with the shrink of the product. -/
lemma finiteModelExternalTensor_isIrreducible
    [Finite G] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W] [Module.Finite ℂ (V ⊗[ℂ] W)]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Representation.IsIrreducible
      (((finiteModelRep σ) ⊠ (finiteModelRep τ)).comp
        (prodShrinkMulEquiv.symm.toMonoidHom)) := by
  let π :
      Representation ℂ (Shrink.{0} G × Shrink.{0} H)
        (FGModuleRepr.ofFinite ℂ V ⊗[ℂ] FGModuleRepr.ofFinite ℂ W) :=
    (finiteModelRep σ) ⊠ (finiteModelRep τ)
  have hσirr : Representation.IsIrreducible (finiteModelRep σ) :=
    finiteModelRep_isIrreducible (σ := σ)
  have hτirr : Representation.IsIrreducible (finiteModelRep τ) :=
    finiteModelRep_isIrreducible (σ := τ)
  letI : Representation.IsIrreducible (finiteModelRep σ) := hσirr
  letI : Representation.IsIrreducible (finiteModelRep τ) := hτirr
  have hpair : ⟪π.character, π.character⟫ = (1 : ℂ) := by
    -- On the finite models, the Chapter 2 character criterion applies directly.
    rw [externalTensor_self_pairing_eq_mul]
    rw [self_pairing_eq_one_of_isIrreducible_via_fdrep (ρ := finiteModelRep σ)]
    rw [self_pairing_eq_one_of_isIrreducible_via_fdrep (ρ := finiteModelRep τ)]
    norm_num
  have hπirr : Representation.IsIrreducible π :=
    (self_character_pairing_eq_one_iff_isIrreducible (ρ := π)).mp hpair
  letI : Representation.IsIrreducible π := hπirr
  -- Precomposing with the product-shrink equivalence only changes the group coordinates.
  simpa [π] using
    (isIrreducible_comp_of_mulEquiv
      (e := prodShrinkMulEquiv.symm) π)

/-- Helper for Proposition 6-6.5-5: the external tensor product of irreducible finite-dimensional
representations of finite groups is irreducible. The new route isolates the same-universe finite
models needed by the bundled Chapter 3 theorem before transporting back. -/
lemma isIrreducible_externalTensor
    [Finite G] {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G V) (τ : Representation ℂ H W)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Representation.IsIrreducible (σ ⊠ τ) := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite σ
  letI : Module.Finite ℂ V := inferInstance
  letI : Module.Finite ℂ W := inferInstance
  letI : Module.Finite ℂ (V ⊗[ℂ] W) := inferInstance
  let π : Representation ℂ (G × H) (V ⊗[ℂ] W) := σ ⊠ τ
  -- Route correction: move to same-universe finite models, prove irreducibility there by the
  -- character pairing criterion, and then transport back to the original external tensor product.
  letI :
      Representation.IsIrreducible
        (((finiteModelRep σ) ⊠ (finiteModelRep τ)).comp
          (prodShrinkMulEquiv.symm.toMonoidHom)) :=
    finiteModelExternalTensor_isIrreducible (σ := σ) (τ := τ)
  letI : Representation.IsIrreducible (finiteModelRep π) :=
    isIrreducible_of_nonempty_equiv
      ⟨finiteModelExternalTensorEquiv (σ := σ) (τ := τ)⟩
  letI :
      Representation.IsIrreducible
        (π.comp (Shrink.mulEquiv : Shrink.{0} (G × H) ≃* (G × H)).toMonoidHom) :=
    isIrreducible_of_nonempty_equiv
      ⟨finiteModelRepEquivComp (ρ := π)⟩
  let e : Shrink.{0} (G × H) ≃* (G × H) :=
    Shrink.mulEquiv
  have hUnshrink :
      Representation.IsIrreducible
        ((π.comp e.toMonoidHom).comp e.symm.toMonoidHom) :=
    isIrreducible_comp_of_mulEquiv
      (e := e.symm)
      (π.comp e.toMonoidHom)
  let πun : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
    (π.comp e.toMonoidHom).comp e.symm.toMonoidHom
  letI : Representation.IsIrreducible πun := hUnshrink
  have hπun_equiv : Nonempty (πun.Equiv π) := by
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ (V ⊗[ℂ] W)) ?_⟩
    intro g
    ext x y
    simp [πun, π, e]
  -- Unshrink the product group to recover the original external tensor representation.
  simpa [π] using (isIrreducible_of_nonempty_equiv hπun_equiv : Representation.IsIrreducible π)

/-- Helper for Proposition 6-6.5-5: the center subgroup is commutative as a group in its own
right, so coordinatewise products of central tuples are available. -/
local instance centerCommGroup : CommGroup (Subgroup.center G) :=
  Group.commGroupOfCenterEqTop
    (show Subgroup.center (Subgroup.center G) = ⊤ from Subgroup.center_eq_top)

/-- Helper for Proposition 6-6.5-5: a `1`-tuple of group elements is canonically the same as a
single group element. -/
def finOneMulEquiv : (Fin 1 → G) ≃* G where
  toFun := fun f ↦ f 0
  invFun := fun g _ ↦ g
  left_inv := by
    intro f
    funext i
    fin_cases i
    rfl
  right_inv := by
    intro g
    rfl
  map_mul' := by
    intro f h
    rfl

/-- Helper for Proposition 6-6.5-5: splitting a tuple of length `n + m` into its first `n`
coordinates and its last `m` coordinates is a group equivalence. -/
def finAppendMulEquiv (n m : ℕ) : (Fin (n + m) → G) ≃* (Fin n → G) × (Fin m → G) where
  toEquiv := (Fin.appendEquiv n m).symm
  map_mul' := by
    intro f h
    ext i <;> rfl

/-- Helper for Proposition 6-6.5-5: the `n`-fold tensor power representation acts coordinatewise
on `⨂[ℂ]^n V`. -/
def tensorPowerRep (ρ : Representation ℂ G V) (n : ℕ) :
    Representation ℂ (Fin n → G) (⨂[ℂ]^n V) where
  toFun g := PiTensorProduct.map (fun i ↦ ρ (g i))
  map_one' := by
    -- Coordinatewise identity maps induce the identity on the full tensor product.
    simpa using
      (PiTensorProduct.map_one :
        PiTensorProduct.map (fun i : Fin n ↦ (1 : V →ₗ[ℂ] V)) = 1)
  map_mul' g h := by
    -- Coordinatewise multiplication of endomorphisms transports through `PiTensorProduct.map`.
    simpa using
      (PiTensorProduct.map_mul (fun i ↦ ρ (g i)) (fun i ↦ ρ (h i)))

/-- Helper for Proposition 6-6.5-5: the one-fold tensor-power representation is just the original
representation after identifying `Fin 1 → G` with `G`. -/
noncomputable def tensorPowerRepOneEquiv (ρ : Representation ℂ G V) :
    (tensorPowerRep ρ 1).Equiv (ρ.comp finOneMulEquiv.toMonoidHom) :=
  Representation.Equiv.mk
    (PiTensorProduct.subsingletonEquiv 0)
    (fun g ↦ by
      -- On pure tensors, the singleton tensor product evaluation is exactly the original action.
      ext f
      simp [tensorPowerRep, finOneMulEquiv, PiTensorProduct.subsingletonEquiv_apply_tprod])

/-- Helper for Proposition 6-6.5-5: splitting a tuple into its first `n` coordinates and its last
coordinate, then appending those pieces again, recovers the original tuple. -/
lemma fin_append_castAdd_last {α : Type*} (n : ℕ) (f : Fin (n + 1) → α) :
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n)) = f := by
  -- This is the exact `Fin.append` reconstruction used when splitting off the final tensor factor.
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
    simpa using (Fin.natAdd_last : Fin.natAdd n (0 : Fin 1) = Fin.last n)
  calc
    Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun _ : Fin 1 ↦ f (Fin.last n))
        =
          Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun i : Fin 1 ↦ f (Fin.natAdd n i)) := by
            congr 1
            funext i
            fin_cases i
            simpa using congrArg f hlast.symm
    _ = f := Fin.append_castAdd_natAdd

/-- Helper for Proposition 6-6.5-5: the inverse of `TensorPower.mulEquiv` on a pure tensor splits
off the last tensor coordinate. -/
lemma tensorPower_mulEquiv_symm_tprod_split_last (n : ℕ) (f : Fin (n + 1) → V) :
    ((TensorPower.mulEquiv :
        (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).symm
      (PiTensorProduct.tprod ℂ f)
      =
        (PiTensorProduct.tprod ℂ (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[ℂ]
          (PiTensorProduct.tprod ℂ (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
  -- Apply the forward equivalence so the goal becomes the standard pure-tensor multiplication rule.
  apply
    ((TensorPower.mulEquiv :
      (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).injective
  -- The only remaining task is to identify the appended index function with the original tuple.
  calc
    (TensorPower.mulEquiv : (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)
        (((TensorPower.mulEquiv :
            (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).symm
          (PiTensorProduct.tprod ℂ f))
        = PiTensorProduct.tprod ℂ f := by
            rw [LinearEquiv.apply_symm_apply]
    _ =
        PiTensorProduct.tprod ℂ
          (Fin.append (fun i : Fin n ↦ f (Fin.castAdd 1 i)) (fun i : Fin 1 ↦ f (Fin.natAdd n i))) := by
            congr 1
            exact (Fin.append_castAdd_natAdd : _).symm
    _ =
        (TensorPower.mulEquiv : (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)
          ((PiTensorProduct.tprod ℂ (fun i : Fin n ↦ f (Fin.castAdd 1 i))) ⊗ₜ[ℂ]
            (PiTensorProduct.tprod ℂ (fun i : Fin 1 ↦ f (Fin.natAdd n i)))) := by
              symm
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod ℂ
                  (fun i : Fin n ↦ f (Fin.castAdd 1 i))
                  (fun i : Fin 1 ↦ f (Fin.natAdd n i)))

/-- Helper for Proposition 6-6.5-5: after splitting a pure tensor into its first `n` coordinates
and its last coordinate, the successor tensor-power action matches the split external tensor
action. -/
lemma tensorPowerRepSucc_apply_tprod (ρ : Representation ℂ G V) (n : ℕ)
    (g : Fin (n + 1) → G) (f : Fin (n + 1) → V) :
    (TensorPower.mulEquiv :
      (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)
      (((((tensorPowerRep ρ n) ⊠ (tensorPowerRep ρ 1)).comp
          (finAppendMulEquiv n 1).toMonoidHom) g)
        (((TensorPower.mulEquiv :
            (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).symm
          ((PiTensorProduct.tprod ℂ) f)))
      = (PiTensorProduct.tprod ℂ) (fun i ↦ (ρ (g i)) (f i)) := by
  -- Route correction: the previous route mixed the representation computation with the hidden
  -- `mulEquiv.symm` reindexing. We first isolate that reindexing into a standalone rewrite.
  rw [tensorPower_mulEquiv_symm_tprod_split_last]
  let f₁ : Fin n → V := fun i ↦ f (Fin.castAdd 1 i)
  let f₂ : Fin 1 → V := fun i ↦ f (Fin.natAdd n i)
  let gf₁ : Fin n → V := fun i ↦ ρ (g (Fin.castAdd 1 i)) (f (Fin.castAdd 1 i))
  let gf₂ : Fin 1 → V := fun i ↦ ρ (g (Fin.natAdd n i)) (f (Fin.natAdd n i))
  -- After the split, the external tensor action is coordinatewise on each factor.
  have hsplit :
      (((((tensorPowerRep ρ n) ⊠ (tensorPowerRep ρ 1)).comp
          (finAppendMulEquiv n 1).toMonoidHom) g)
        ((PiTensorProduct.tprod ℂ f₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ f₂)))
      =
        (PiTensorProduct.tprod ℂ gf₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ gf₂) := by
    simp [f₁, f₂, gf₁, gf₂, Representation.tprod, tensorPowerRep, finAppendMulEquiv]
  rw [hsplit]
  -- Recombine the two pure tensors using the tensor-power multiplication owner from mathlib.
  calc
    (TensorPower.mulEquiv : (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)
        ((PiTensorProduct.tprod ℂ gf₁) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ gf₂))
        = PiTensorProduct.tprod ℂ (Fin.append gf₁ gf₂) := by
              simpa [TensorPower.gMul_def] using
                (TensorPower.tprod_mul_tprod ℂ gf₁ gf₂)
    _ = PiTensorProduct.tprod ℂ (fun i ↦ ρ (g i) (f i)) := by
          congr 1
          simpa [f₁, f₂, gf₁, gf₂] using
            (@Fin.append_castAdd_natAdd n 1 V
              (fun i : Fin (n + 1) ↦ ρ (g i) (f i)))

/-- Helper for Proposition 6-6.5-5: after splitting off the last tensor factor, the `(n + 1)`-fold
tensor-power representation matches the external tensor product of the `n`-fold power with the
one-fold power. -/
noncomputable def tensorPowerRepSuccEquiv (ρ : Representation ℂ G V) (n : ℕ) :
    (tensorPowerRep ρ (n + 1)).Equiv
      (((tensorPowerRep ρ n) ⊠ (tensorPowerRep ρ 1)).comp
        (finAppendMulEquiv n 1).toMonoidHom) :=
  Representation.Equiv.mk
    ((TensorPower.mulEquiv :
      (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).symm
    (fun g ↦ by
      -- The two actions agree on pure tensors after rewriting the tensor-power splitting.
      ext f
      apply
        ((TensorPower.mulEquiv :
          (⨂[ℂ]^n V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^(n + 1) V)).injective
      simpa [eq_comm, tensorPowerRep, PiTensorProduct.map_tprod] using
        tensorPowerRepSucc_apply_tprod ρ n g f)

/-- Helper for Proposition 6-6.5-5: every positive tensor power of an irreducible representation
is irreducible. -/
lemma tensor_power_rep_is_irreducible
    [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (n : ℕ) :
    Representation.IsIrreducible (tensorPowerRep ρ (n + 1)) := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : FiniteDimensional ℂ (⨂[ℂ]^1 V) :=
    FiniteDimensional.of_injective
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).toLinearMap
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 ↦ V) 0).injective
  have hOne : Representation.IsIrreducible (tensorPowerRep ρ 1) := by
    letI : Representation.IsIrreducible (ρ.comp finOneMulEquiv.toMonoidHom) :=
      isIrreducible_comp_of_mulEquiv (e := finOneMulEquiv) ρ
    -- The one-fold tensor power is equivalent to the original representation.
    exact isIrreducible_of_nonempty_equiv ⟨(tensorPowerRepOneEquiv (ρ := ρ)).symm⟩
  induction n with
  | zero =>
      exact hOne
  | succ n ih =>
      letI : Representation.IsIrreducible (tensorPowerRep ρ (n + 1)) := ih
      letI : Representation.IsIrreducible (tensorPowerRep ρ 1) := hOne
      let π :
          Representation ℂ ((Fin (n + 1) → G) × (Fin 1 → G))
            ((⨂[ℂ]^(n + 1) V) ⊗[ℂ] (⨂[ℂ]^1 V)) :=
        (tensorPowerRep ρ (n + 1)) ⊠ (tensorPowerRep ρ 1)
      letI : Representation.IsIrreducible π :=
        isIrreducible_externalTensor
          (σ := tensorPowerRep ρ (n + 1)) (τ := tensorPowerRep ρ 1)
      let e : (Fin (n + 1 + 1) → G) ≃* (Fin (n + 1) → G) × (Fin 1 → G) :=
        finAppendMulEquiv (n + 1) 1
      let πsplit :
          Representation ℂ (Fin (n + 1 + 1) → G)
            ((⨂[ℂ]^(n + 1) V) ⊗[ℂ] (⨂[ℂ]^1 V)) :=
        π.comp e.toMonoidHom
      have hπsplit : Representation.IsIrreducible πsplit := by
        simpa [πsplit, e] using
          (isIrreducible_comp_of_mulEquiv (e := e) π)
      letI : Representation.IsIrreducible πsplit := hπsplit
      -- The successor tensor power is equivalent to the split external tensor.
      exact isIrreducible_of_nonempty_equiv
        ⟨(tensorPowerRepSuccEquiv (ρ := ρ) (n := n + 1)).symm⟩

/-- Helper for Proposition 6-6.5-5: the degree of the positive tensor power is the corresponding
power of the original degree. -/
lemma tensor_power_finrank [FiniteDimensional ℂ V] (n : ℕ) :
    Module.finrank ℂ (⨂[ℂ]^(n + 1) V) = Module.finrank ℂ V ^ (n + 1) := by
  induction n with
  | zero =>
      -- A one-fold tensor product is just the original space.
      rw [pow_one]
      exact
        (show Module.finrank ℂ (⨂[ℂ] _ : Fin 1, V) = Module.finrank ℂ V from
          (PiTensorProduct.subsingletonEquiv 0).finrank_eq)
  | succ n ih =>
      -- Split off the last factor and use multiplicativity of finite dimension.
      calc
        Module.finrank ℂ (⨂[ℂ]^((n + 1) + 1) V)
            = Module.finrank ℂ ((⨂[ℂ]^(n + 1) V) ⊗[ℂ] (⨂[ℂ]^1 V)) := by
                simpa [Nat.add_comm] using
                  ((TensorPower.mulEquiv :
                    (⨂[ℂ]^(n + 1) V ⊗[ℂ] ⨂[ℂ]^1 V) ≃ₗ[ℂ] ⨂[ℂ]^((n + 1) + 1) V)).symm.finrank_eq
        _ = Module.finrank ℂ (⨂[ℂ]^(n + 1) V) * Module.finrank ℂ (⨂[ℂ]^1 V) := by
              simpa using
                (Module.finrank_tensorProduct :
                  Module.finrank ℂ ((⨂[ℂ]^(n + 1) V) ⊗[ℂ] (⨂[ℂ]^1 V)) =
                    Module.finrank ℂ (⨂[ℂ]^(n + 1) V) * Module.finrank ℂ (⨂[ℂ]^1 V))
        _ = Module.finrank ℂ V ^ (n + 1) * Module.finrank ℂ V := by
              rw [ih]
              rw [(PiTensorProduct.subsingletonEquiv 0).finrank_eq]
        _ = Module.finrank ℂ V ^ ((n + 1) + 1) := by
              simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 6-6.5-5: forgetting the central subtype on each coordinate embeds
central tuples into the full tuple group. -/
def centerTupleEmbedding (n : ℕ) : (Fin (n + 1) → Subgroup.center G) →* (Fin (n + 1) → G) where
  toFun z i := z i
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- Helper for Proposition 6-6.5-5: multiplying the entries of a central tuple defines a
homomorphism back to the center. -/
def centerTupleProd (n : ℕ) : (Fin (n + 1) → Subgroup.center G) →* Subgroup.center G where
  toFun z := ∏ i, z i
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simpa using
      (Finset.prod_mul_distrib : (∏ i, x i * y i) = (∏ i, x i) * ∏ i, y i)

/-- Helper for Proposition 6-6.5-5: Serre's product-one central subgroup inside the tuple group is
the image of the kernel of the coordinatewise product map. -/
def productOneCenterSubgroup (n : ℕ) : Subgroup (Fin (n + 1) → G) :=
  (centerTupleProd n).ker.map (centerTupleEmbedding n)

/-- Helper for Proposition 6-6.5-5: forgetting the central subtype on each coordinate is
injective. -/
lemma centerTupleEmbedding_injective (n : ℕ) :
    Function.Injective
      ((centerTupleEmbedding n : (Fin (n + 1) → Subgroup.center G) →* (Fin (n + 1) → G))) := by
  intro x y h
  ext i
  exact congrFun h i

/-- Helper for Proposition 6-6.5-5: the image of the coordinate-forgetful map is exactly the
subgroup of tuples whose entries are all central. -/
lemma centerTupleEmbedding_range (n : ℕ) :
    ((centerTupleEmbedding n : (Fin (n + 1) → Subgroup.center G) →* (Fin (n + 1) → G))).range =
      Subgroup.pi Set.univ (fun _ : Fin (n + 1) ↦ Subgroup.center G) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    intro i _
    exact (x i).2
  · intro hz
    refine ⟨fun i ↦ ⟨z i, hz i (by simp)⟩, ?_⟩
    rfl

/-- Helper for Proposition 6-6.5-5: the coordinatewise product map on central tuples is
surjective, by placing a chosen central element in the last coordinate and `1` elsewhere. -/
lemma centerTupleProd_surjective (n : ℕ) :
    Function.Surjective ((centerTupleProd n : (Fin (n + 1) → Subgroup.center G) →* Subgroup.center G)) := by
  intro z
  refine ⟨fun i ↦ if i = Fin.last n then z else 1, ?_⟩
  change ∏ i : Fin (n + 1), (if i = Fin.last n then z else 1) = z
  rw [Fin.prod_univ_castSucc]
  simp

/-- Helper for Proposition 6-6.5-5: the product-one central subgroup has the index appearing in
Serre's quotient-order computation. -/
lemma product_one_center_subgroup_index (n : ℕ) :
    ((productOneCenterSubgroup n : Subgroup (Fin (n + 1) → G))).index =
      Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (n + 1) := by
  let φ : (Fin (n + 1) → Subgroup.center G) →* Subgroup.center G := centerTupleProd n
  let ψ : (Fin (n + 1) → Subgroup.center G) →* (Fin (n + 1) → G) := centerTupleEmbedding n
  have hker : φ.ker.index = Nat.card (Subgroup.center G) := by
    rw [Subgroup.index_ker]
    have hrange : φ.range = ⊤ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        rcases centerTupleProd_surjective n z with ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    simpa [φ, hrange]
  have hrange :
      ψ.range.index =
        (Subgroup.center G).index ^ (n + 1) := by
    rw [show ψ.range = Subgroup.pi Set.univ (fun _ : Fin (n + 1) ↦ Subgroup.center G) by
          simpa [ψ] using centerTupleEmbedding_range n]
    rw [Subgroup.index_pi]
    simp
  calc
    (productOneCenterSubgroup n).index
        = φ.ker.index * ψ.range.index := by
              simpa [productOneCenterSubgroup, φ, ψ] using
                φ.ker.index_map_of_injective (centerTupleEmbedding_injective n)
    _ = Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (n + 1) := by
          rw [hker, hrange]

/-- Helper for Proposition 6-6.5-5: a central tuple acts on the tensor power by the product of the
corresponding scalar character values. -/
lemma tensorPowerRep_center_tuple_action (ρ : Representation ℂ G V)
    (μ : Subgroup.center G →* ℂˣ)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = (μ s : ℂ) • (1 : Module.End ℂ V))
    (n : ℕ) (z : Fin (n + 1) → Subgroup.center G) :
    tensorPowerRep ρ (n + 1) (centerTupleEmbedding n z) =
      (∏ i, (μ (z i) : ℂ)) • (1 : Module.End ℂ (⨂[ℂ]^(n + 1) V)) := by
  -- On pure tensors, each central coordinate acts by its scalar, so multilinearity collects the
  -- full product of those scalars.
  ext f
  have haction :
      PiTensorProduct.tprod ℂ (fun i : Fin (n + 1) ↦ (μ (z i) : ℂ) • f i) =
        (∏ i, (μ (z i) : ℂ)) • PiTensorProduct.tprod ℂ f := by
    exact
      (PiTensorProduct.tprod ℂ :
        MultilinearMap ℂ (fun _ : Fin (n + 1) ↦ V) (⨂[ℂ] _ : Fin (n + 1), V)).map_smul_univ
          (fun i ↦ (μ (z i) : ℂ)) f
  calc
    tensorPowerRep ρ (n + 1) (centerTupleEmbedding n z) ((PiTensorProduct.tprod ℂ) f)
        = PiTensorProduct.tprod ℂ (fun i ↦ ρ ((z i : Subgroup.center G) : G) (f i)) := by
            simp [tensorPowerRep, centerTupleEmbedding]
    _ = PiTensorProduct.tprod ℂ (fun i ↦ (μ (z i) : ℂ) • f i) := by
          congr 1
          funext i
          simpa [hμ (z i)]
    _ = (∏ i, (μ (z i) : ℂ)) • PiTensorProduct.tprod ℂ f := by
          simpa using haction

/-- Helper for Proposition 6-6.5-5: the product-one central subgroup acts trivially on the
positive tensor-power representation. -/
lemma tensor_power_rep_product_one_center_is_trivial (ρ : Representation ℂ G V)
    (μ : Subgroup.center G →* ℂˣ)
    (hμ : ∀ s : Subgroup.center G, ρ (s : G) = (μ s : ℂ) • (1 : Module.End ℂ V))
    (n : ℕ) :
    Representation.IsTrivial
      ((tensorPowerRep ρ (n + 1)).comp (productOneCenterSubgroup n).subtype) := by
  refine ⟨?_⟩
  intro g
  rcases g.2 with ⟨z, hz, hz'⟩
  have hg : (g : Fin (n + 1) → G) = centerTupleEmbedding n z := hz'.symm
  have hprod : ∏ i, (μ (z i) : ℂ) = 1 := by
    simpa [centerTupleProd] using congrArg (fun s : Subgroup.center G ↦ (μ s : ℂ)) hz
  -- Route correction: the kernel condition is used only after converting the action into the
  -- scalar product supplied by `tensorPowerRep_center_tuple_action`.
  calc
    ((tensorPowerRep ρ (n + 1)).comp (productOneCenterSubgroup n).subtype) g
        = tensorPowerRep ρ (n + 1) (centerTupleEmbedding n z) := by
            simpa [hg]
    _ = (∏ i, (μ (z i) : ℂ)) • (1 : Module.End ℂ (⨂[ℂ]^(n + 1) V)) :=
          tensorPowerRep_center_tuple_action ρ μ hμ n z
    _ = LinearMap.id := by
          rw [hprod]
          rw [one_smul]
          rfl

/-- Helper for Proposition 6-6.5-5: the tensor-power quotient construction from Serre's proof
produces the divisibility family needed for the final arithmetic extraction. -/
lemma tensor_power_quotient_finrank_pow_dvd_center_card_mul_index_pow
    [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (m : ℕ) :
    Module.finrank ℂ V ^ (m + 1) ∣
      Nat.card (Subgroup.center G) * (Subgroup.center G).index ^ (m + 1) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  obtain ⟨μ, hμ⟩ := center_scalar_action_hom ρ
  let H : Subgroup (Fin (m + 1) → G) := productOneCenterSubgroup m
  let σ := tensorPowerRep ρ (m + 1)
  letI : Representation.IsIrreducible σ := tensor_power_rep_is_irreducible ρ m
  letI : Representation.IsTrivial (σ.comp H.subtype) :=
    tensor_power_rep_product_one_center_is_trivial ρ μ hμ m
  have hHcenter : H ≤ Subgroup.center (Fin (m + 1) → G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    ext i
    rcases hg with ⟨z, hz, rfl⟩
    exact Subgroup.mem_center_iff.mp (z i).2 (h i)
  letI : H.Normal := ⟨fun a ha b ↦ by
    have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp (hHcenter ha) b
    simpa [Subgroup.mem_carrier, mul_assoc, hcomm] using ha⟩
  let τ := σ.ofQuotient H
  letI : Representation.IsIrreducible τ := isIrreducible_of_ofQuotient_of_isTrivial σ H
  have hdiv : Module.finrank ℂ (⨂[ℂ]^(m + 1) V) ∣ H.index := by
    -- The descended quotient representation is irreducible, so Corollary 6-6.5-4 applies.
    simpa [H, τ, Subgroup.index_eq_card] using finrank_dvd_card τ
  -- Rewrite both the tensor-power degree and the quotient order into Serre's arithmetic form.
  simpa [H, tensor_power_finrank, product_one_center_subgroup_index] using hdiv

/-- Proposition 6-6.5-5: the degree of an irreducible complex representation of a finite group
divides the index of the center. Finite-dimensionality is automatic in this setting. -/
theorem finrank_dvd_center_index [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Module.finrank ℂ V ∣ (Subgroup.center G).index := by
  -- The source proof reduces the main divisibility to a tensor-power family and then extracts
  -- the degree from the resulting prime-factor inequalities.
  have hc : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  exact dvd_of_forall_succ_pow_dvd_center_card_mul_pow hc
    (tensor_power_quotient_finrank_pow_dvd_center_card_mul_index_pow ρ)

end

end Representation
