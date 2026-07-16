import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_3_1
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Corollary_2_2_3_3
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.SubrepresentationInvariant

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u₁

namespace Representation

noncomputable section

section

open scoped Representation

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

local instance instNeZeroNatCardField : NeZero (Nat.card G : K) :=
  ⟨Invertible.ne_zero (Nat.card G : K)⟩

/- Domain-style sampling for this item:
* primary domain: finite-dimensional character theory of semisimple representations of finite
  groups over an algebraically closed field;
* relevant owner declarations inspected before refining:
  `Representation.exists_isCompl_of_mem_invtSubmodule`,
  `Representation.exists_isInternal_irreducible_subrepresentations`,
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`,
  `Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`;
* best owner abstraction: the public statement is about the canonical owners
  `Representation.character` and `Representation.Equiv`, while irreducible decompositions,
  complementary invariant subspaces, and multiplicity counts remain internal bridge data.

Primitive data vs derived API:
* primitive data are the representations `ρ`, `σ`, and the equality `ρ.character = σ.character`;
* the chosen irreducible summand, complementary invariant subspaces, and recursive splitting are
  derived proof data, so the file keeps them private and reuses the chapter multiplicity owner
  theorem instead of rebuilding a parallel projection-based positivity argument. -/

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)] in
/-- Helper for Corollary 2-2.3-4: products of equivariant isomorphisms remain equivariant. -/
private theorem prodCongr_isIntertwining
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module K W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module K W₂]
    {ρ₁ : Representation K G V₁} {ρ₂ : Representation K G V₂}
    {σ₁ : Representation K G W₁} {σ₂ : Representation K G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    ∀ g,
      (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) ∘ₗ (ρ₁.prod ρ₂) g =
        (σ₁.prod σ₂) g ∘ₗ (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) := by
  intro g
  ext x <;> simp [Representation.prod, e₁.isIntertwining, e₂.isIntertwining]

/-- Helper for Corollary 2-2.3-4: product decompositions transport equivariant isomorphisms. -/
private def prodCongr
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W₁ : Type*} [AddCommGroup W₁] [Module K W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module K W₂]
    {ρ₁ : Representation K G V₁} {ρ₂ : Representation K G V₂}
    {σ₁ : Representation K G W₁} {σ₂ : Representation K G W₂}
    (e₁ : ρ₁.Equiv σ₁) (e₂ : ρ₂.Equiv σ₂) :
    (ρ₁.prod ρ₂).Equiv (σ₁.prod σ₂) :=
  .mk (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv) (prodCongr_isIntertwining e₁ e₂)

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: the direct-sum equivalence from complementary
subrepresentations is equivariant. -/
private theorem prodEquivOfIsCompl_isIntertwining
    (ρ : Representation K G V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    ∀ g,
      (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) ∘ₗ
          (σ.toRepresentation.prod τ.toRepresentation) g =
        (ρ g) ∘ₗ (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ) := by
  intro g
  ext z
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inl,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((σ.toRepresentation g) z) = (ρ g) ↑z from rfl)
  · simpa [Submodule.coe_prodEquivOfIsCompl, LinearMap.comp_apply, LinearMap.coe_inr,
      LinearMap.coprod_apply, LinearMap.prodMap_apply, Submodule.coe_subtype, Representation.prod]
      using (show ↑((τ.toRepresentation g) z) = (ρ g) ↑z from rfl)

/-- Helper for Corollary 2-2.3-4: complementary invariant summands split the representation as a
product. -/
private def prodEquivOfIsCompl
    (ρ : Representation K G V) (σ τ : Subrepresentation ρ)
    (hστ : IsCompl σ.toSubmodule τ.toSubmodule) :
    (σ.toRepresentation.prod τ.toRepresentation).Equiv ρ :=
  .mk (σ.toSubmodule.prodEquivOfIsCompl τ.toSubmodule hστ)
    (prodEquivOfIsCompl_isIntertwining ρ σ τ hστ)

omit [Finite G] [CharZero K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
    [FiniteDimensional K V] in
/-- Helper for Corollary 2-2.3-4: irreducible representations are nontrivial. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation K G V) [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- If two finite-dimensional representations in the semisimple algebraically closed setting have
the same character, then they are equivariantly isomorphic. The companion iff theorem below is the
source-facing Corollary `2-2.3-4`. -/
theorem nonempty_equiv_of_character_eq
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (hchar : ρ.character = σ.character) :
    Nonempty (ρ.Equiv σ) := by
  classical
  -- Split first by whether the source representation is nontrivial.
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    -- Evaluate the common character at `1` to synchronize dimensions.
    have hdim' : (Module.finrank K V : K) = Module.finrank K W := by
      simpa [Representation.char_one] using congrFun hchar 1
    have hdim : Module.finrank K V = Module.finrank K W :=
      Nat.cast_injective hdim'
    have hW : Nontrivial W := by
      exact Module.nontrivial_of_finrank_pos (hdim ▸ Module.finrank_pos)
    letI : Nontrivial W := hW
    -- Choose an irreducible summand of `ρ`; equality of characters will force the same summand
    -- to appear inside `σ`.
    obtain ⟨ιρ, _, πρ, hπρ_indep, hπρ_top, hπρ_irr⟩ :
        ∃ (ι : Type v) (_ : Fintype ι) (π : ι → Subrepresentation ρ),
          iSupIndep (fun i ↦ (π i).toSubmodule) ∧
            (⨆ i, (π i).toSubmodule) = ⊤ ∧
            ∀ i, (π i).toRepresentation.IsIrreducible := by
      exact exists_isInternal_irreducible_subrepresentations ρ
    have hπρ_internal : DirectSum.IsInternal (fun i ↦ (πρ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hπρ_indep hπρ_top
    have hιρ : Nonempty ιρ := by
      by_cases hιρ : IsEmpty ιρ
      · letI := hιρ
        exact False.elim <|
          (show (⊥ : Submodule K V) ≠ ⊤ from bot_ne_top) <|
            by simp [iSup_of_empty] at hπρ_top
      · exact not_isEmpty_iff.mp hιρ
    let iρ := Classical.choice hιρ
    let σ₁ : Subrepresentation ρ := πρ iρ
    have hσ₁_irr : σ₁.toRepresentation.IsIrreducible := hπρ_irr iρ
    letI : σ₁.toRepresentation.IsIrreducible := hσ₁_irr
    have hσ₁_count :
        Nat.card { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      simpa [σ₁] using
        card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
          ρ πρ hπρ_internal hπρ_irr σ₁.toRepresentation hσ₁_irr
    have hσ₁_count_pos :
        0 < Nat.card { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      letI :
          Fintype { i // Nonempty ((πρ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
        Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨iρ, ⟨Representation.Equiv.refl _⟩⟩⟩
    have hρ_intertwining_pos :
        0 < Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      rw [← hσ₁_count]
      exact hσ₁_count_pos
    haveI : Nontrivial σ₁.toSubmodule := nontrivial_of_isIrreducible σ₁.toRepresentation
    have hσ₁_pos : 0 < Module.finrank K σ₁.toSubmodule := Module.finrank_pos
    -- Split off a complementary invariant summand from `ρ`.
    obtain ⟨V₀, hV₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule ρ σ₁.toSubmodule
        σ₁.toSubmodule_mem_invtSubmodule
    let ρ₀ : Subrepresentation ρ := Subrepresentation.ofInvtSubmodule V₀
    have hρ₀ : IsCompl σ₁.toSubmodule ρ₀.toSubmodule := by
      simpa [ρ₀] using hV₀
    let eρ : (σ₁.toRepresentation.prod ρ₀.toRepresentation).Equiv ρ :=
      prodEquivOfIsCompl ρ σ₁ ρ₀ hρ₀
    have hσ_intertwining' :
        (Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) : K) =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
      calc
        (Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) : K) =
            ⟪σ.character, σ₁.toRepresentation.character⟫ := by
              symm
              simpa using
                (groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  K σ σ₁.toRepresentation)
        _ = ⟪ρ.character, σ₁.toRepresentation.character⟫ := by
              simp [hchar]
        _ = Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) := by
              simpa using
                (groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
                  K ρ σ₁.toRepresentation)
    have hσ_intertwining :
        Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) =
          Module.finrank K (ρ.IntertwiningMap σ₁.toRepresentation) :=
      Nat.cast_injective hσ_intertwining'
    have hσ_intertwining_pos :
        0 < Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) := by
      rw [hσ_intertwining]
      exact hρ_intertwining_pos
    -- The same irreducible summand appears in `σ` with positive multiplicity.
    obtain ⟨ι, _, τ, hτ_indep, hτ_top, hτ_irr⟩ :
        ∃ (ι : Type w) (_ : Fintype ι) (τ : ι → Subrepresentation σ),
          iSupIndep (fun i ↦ (τ i).toSubmodule) ∧
            (⨆ i, (τ i).toSubmodule) = ⊤ ∧
            ∀ i, (τ i).toRepresentation.IsIrreducible := by
      exact exists_isInternal_irreducible_subrepresentations σ
    let hτ_internal : DirectSum.IsInternal (fun i ↦ (τ i).toSubmodule) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hτ_indep hτ_top
    have hcount :
        Nat.card { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } =
          Module.finrank K (σ.IntertwiningMap σ₁.toRepresentation) := by
      simpa using
        card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
          σ τ hτ_internal hτ_irr σ₁.toRepresentation hσ₁_irr
    have hcount_pos :
        0 < Nat.card { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      rw [hcount]
      exact hσ_intertwining_pos
    letI : Fintype { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
      Fintype.ofFinite _
    have hnonempty :
        Nonempty { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } := by
      rw [Nat.card_eq_fintype_card] at hcount_pos
      exact Fintype.card_pos_iff.mp hcount_pos
    let i₀ : { i // Nonempty ((τ i).toRepresentation.Equiv σ₁.toRepresentation) } :=
      Classical.choice hnonempty
    let σ₂ : Subrepresentation σ := τ i₀.1
    have hσ₂ : Nonempty (σ₂.toRepresentation.Equiv σ₁.toRepresentation) := i₀.2
    letI : σ₂.toRepresentation.IsIrreducible := hτ_irr i₀.1
    obtain ⟨W₀, hW₀⟩ :=
      exists_isCompl_of_mem_invtSubmodule σ σ₂.toSubmodule
        σ₂.toSubmodule_mem_invtSubmodule
    let σ₀ : Subrepresentation σ := Subrepresentation.ofInvtSubmodule W₀
    have hσ₀ : IsCompl σ₂.toSubmodule σ₀.toSubmodule := by
      simpa [σ₀] using hW₀
    let eσ : (σ₂.toRepresentation.prod σ₀.toRepresentation).Equiv σ :=
      prodEquivOfIsCompl σ σ₂ σ₀ hσ₀
    rcases hσ₂ with ⟨e₁₂⟩
    -- After cancelling the common irreducible character, recurse on the complements.
    have hcomp_char : ρ₀.toRepresentation.character = σ₀.toRepresentation.character := by
      have hsum :
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
            σ₂.toRepresentation.character + σ₀.toRepresentation.character := by
        calc
          σ₁.toRepresentation.character + ρ₀.toRepresentation.character =
              (σ₁.toRepresentation.prod ρ₀.toRepresentation).character := by
                symm
                exact Representation.char_prod σ₁.toRepresentation ρ₀.toRepresentation
          _ = ρ.character := Representation.char_iso eρ
          _ = σ.character := hchar
          _ = (σ₂.toRepresentation.prod σ₀.toRepresentation).character := by
                exact (Representation.char_iso eσ).symm
          _ = σ₂.toRepresentation.character + σ₀.toRepresentation.character := by
                exact Representation.char_prod σ₂.toRepresentation σ₀.toRepresentation
      ext g
      have hg := congrFun hsum g
      have hfirst : σ₂.toRepresentation.character g = σ₁.toRepresentation.character g :=
        congrFun (Representation.char_iso e₁₂) g
      have hg' :
          σ₁.toRepresentation.character g + ρ₀.toRepresentation.character g =
            σ₁.toRepresentation.character g + σ₀.toRepresentation.character g := by
        simpa [hfirst] using hg
      exact add_left_cancel hg'
    have hρ₀_lt : Module.finrank K ρ₀.toSubmodule < Module.finrank K V := by
      have hsplit :
          Module.finrank K V =
            Module.finrank K σ₁.toSubmodule + Module.finrank K ρ₀.toSubmodule := by
        calc
          Module.finrank K V =
              Module.finrank K (σ₁.toSubmodule × ρ₀.toSubmodule) := by
                symm
                exact eρ.toLinearEquiv.finrank_eq
          _ = Module.finrank K σ₁.toSubmodule + Module.finrank K ρ₀.toSubmodule := by
                simp
      rw [hsplit]
      exact Nat.lt_add_of_pos_left hσ₁_pos
    have hrest : Nonempty (ρ₀.toRepresentation.Equiv σ₀.toRepresentation) :=
      nonempty_equiv_of_character_eq ρ₀.toRepresentation σ₀.toRepresentation hcomp_char
    rcases hrest with ⟨e₀⟩
    exact ⟨eρ.symm.trans ((prodCongr e₁₂.symm e₀).trans eσ)⟩
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    -- In the zero-dimensional branch, both representations are forced to be trivial.
    have hV0 : Module.finrank K V = 0 := Module.finrank_zero_iff.mpr inferInstance
    have hW0' : (Module.finrank K W : K) = (0 : K) := by
      simpa [hV0, Representation.char_one] using (congrFun hchar 1).symm
    have hW0 : Module.finrank K W = 0 := by
      exact_mod_cast hW0'
    haveI : Subsingleton W := Module.finrank_zero_iff.mp hW0
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofSubsingleton V W) ?_⟩
    intro g
    ext x
    exact Subsingleton.elim _ _
termination_by Module.finrank K V
decreasing_by
  simpa using hρ₀_lt

/-- Corollary 2-2.3-4: two finite-dimensional representations of a finite group over an
algebraically closed field of characteristic zero in which `|G|` is invertible have the same
character if and only if they are isomorphic. The source-text complex statement is the
specialization `K = ℂ`. -/
theorem character_eq_iff_nonempty_equiv
    (ρ : Representation K G V) (σ : Representation K G W) :
    ρ.character = σ.character ↔ Nonempty (ρ.Equiv σ) := by
  constructor
  · exact nonempty_equiv_of_character_eq ρ σ
  · rintro ⟨e⟩
    exact Representation.char_iso e

end

end

end Representation
