import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_1
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_4_3
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

noncomputable section

section

open CategoryTheory
open scoped BigOperators
open scoped MonoidAlgebra
open scoped Representation

variable {G : Type} [Group G]
variable {ι : Type w}
variable [Finite G]
variable (π : ι → FDRep ℂ G)

local instance : Fintype G := Fintype.ofFinite G
local instance : NeZero (Nat.card G : ℂ) := ⟨by
  exact_mod_cast Nat.card_pos.ne'⟩

section CompleteFamily

/- Domain-style sampling for Theorem 2-2.5-2:
* primary domain: bundled class functions and irreducible characters;
* sampled owner declarations in this domain:
  - `classFunctionSubmodule ℂ G`,
  - `classFunctionSubmodule.equivFun ℂ G`,
  - `_root_.classFunctionSubspace G` as the thin complex alias,
  - `ConjClasses.indicatorClassFunction`.

Best owner abstraction:
* the canonical bundled owner is `classFunctionSubmodule ℂ G`;
* the root alias `classFunctionSubspace G` is only surface notation for that owner;
* the source-facing basis vectors are the existing bundled characters `(π i).ρ.classFunction`.

Primitive data vs. derived API:
* primitive public data: the basis owner on `classFunctionSubmodule ℂ G`;
* derived implementation data: linear independence, spanning, and coercion-to-function lemmas.

Source/core/bridge triage:
* source-facing: Theorem `2-2.5-2`, the class-function basis theorem itself;
* core/canonical: `classFunctionSubmodule ℂ G` together with the standard owner `Module.Basis`;
* bridge/view: the existing Chapter 2 owner-level bundling `ρ.classFunction`.

This file should therefore expose the basis owner directly on the canonical bundled class-function
owner, while keeping the linear-independence/spanning scaffolding internal.
-/

/-- Helper for Theorem 2-2.5-2: bundle a complex character as an element of the class-function
submodule. -/
private theorem character_mem_classFunctionSubmodule_local
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.character ∈ classFunctionSubmodule ℂ G := by
  -- Repackage the character-class-function instance at the canonical bundled owner.
  refine (mem_classFunctionSubmodule_iff ℂ _).2 ?_
  refine ⟨fun {x y} hxy ↦ ?_⟩
  exact Representation.char_eq_of_isConj (ρ := ρ) (ConjClasses.mk_eq_mk_iff_isConj.mp hxy)

/-- Helper for Theorem 2-2.5-2: bundle a complex character as an element of the class-function
submodule. -/
private abbrev characterClassFunction_local
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    classFunctionSubmodule ℂ G :=
  ⟨ρ.character, character_mem_classFunctionSubmodule_local (G := G) ρ⟩

/-- Helper for Theorem 2-2.5-2: an irreducible representation has nontrivial underlying space. -/
private theorem nontrivial_of_isIrreducible_local
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Nontrivial V := by
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

-- Proof sketch: orthogonality gives a pairwise orthogonal family of nonzero class functions, so
-- the irreducible characters are linearly independent as soon as the family is irreducible and
-- pairwise nonisomorphic.
/-- Helper for Theorem 2-2.5-2: the pairing with a finite linear combination of characters
distributes across the sum. -/
private theorem groupFunctionPairing_sum_smul_left_local
    (s : Finset ι) (a : ι → ℂ) (φ : ι → G → ℂ) (ψ : G → ℂ) :
    Representation.groupFunctionPairingOverField ℂ (Finset.sum s fun i ↦ a i • φ i) ψ =
      Finset.sum s fun i ↦ a i * Representation.groupFunctionPairingOverField ℂ (φ i) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum contributes nothing to the pairing.
      simp [Representation.groupFunctionPairingOverField]
  | @insert i s hi ih =>
      -- Expand the inserted term and distribute the pairing over the remaining finite sum.
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- The irreducible characters in a pairwise nonisomorphic irreducible family are linearly
independent in the class-function subspace. -/
private theorem linearIndependent_irreducibleCharacters_of_pairwiseNonisomorphic
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : PairwiseNonisomorphic π) :
    LinearIndependent ℂ (fun i ↦ characterClassFunction_local (G := G) (π i).ρ) := by
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  -- Pair a vanishing finite relation with one irreducible character to isolate its coefficient.
  rw [linearIndependent_iff']
  intro s a hsum i hi
  have hsum_fun : ∑ j ∈ s, a j • (π j).character = (0 : G → ℂ) := by
    -- Forget the bundled class-function wrapper before pairing.
    have hsum' := congrArg (fun z : classFunctionSubmodule ℂ G ↦ (z : G → ℂ)) hsum
    simpa using hsum'
  have hpair' :=
    congrArg (fun ψ : G → ℂ ↦ ⟪ψ, (π i).character⟫) hsum_fun
  have hpair :
      ⟪∑ j ∈ s, a j • (π j).character, (π i).character⟫ = (0 : ℂ) := by
    simpa [Representation.groupFunctionPairingOverField] using hpair'
  rw [groupFunctionPairing_sum_smul_left_local
    (s := s) (a := a) (φ := fun j ↦ (π j).character) (ψ := (π i).character)] at hpair
  rw [Finset.sum_eq_single i] at hpair
  · letI : Simple (π i) := hπ_simple i
    have hself : ⟪(π i).character, (π i).character⟫ = (1 : ℂ) := by
      have hself_iso : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself_iso]
        using (FDRep.char_orthonormal (π i) (π i))
    simpa [hself] using hpair
  · intro j _ hji
    letI : Simple (π j) := hπ_simple j
    letI : Simple (π i) := hπ_simple i
    have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
    have hij_pair : ⟪(π j).character, (π i).character⟫ = (0 : ℂ) := by
      simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hnot] using
        (FDRep.char_orthonormal (π j) (π i))
    rw [hij_pair, mul_zero]
  · intro hnot_mem
    exact (hnot_mem hi).elim

-- Proof sketch: apply Proposition `2-2.5-1` to each irreducible summand of the regular
-- representation, use completeness to identify the summands with members of the chosen family, and
-- then read off the coefficients from the image of the basis vector at `1`.
/-- Helper for Theorem 2-2.5-2: a class function whose pairing with every irreducible character in
the complete family vanishes must itself be zero. -/
private theorem eq_zero_of_pairing_irreducibleCharacters_eq_zero
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (f : classFunctionSubmodule ℂ G)
    (hf : ∀ i, ∑ t : G, f t * (π i).character t = 0) :
    f = 0 := by
  classical
  let ρ := leftRegular ℂ G
  let T : Module.End ℂ (G →₀ ℂ) := ρ.asAlgebraHom (Finsupp.equivFunOnFinite.symm f)
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation ρ),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible :=
    exists_isInternal_irreducible_subrepresentations (ρ := ρ)
  have hsub :
      ∀ j, (σ j).toSubmodule ≤ LinearMap.ker T := by
    intro j x hx
    let τ : FDRep ℂ G := FDRep.of (σ j).toRepresentation
    letI : Representation.IsIrreducible τ.ρ := by
      simpa [τ] using hσ_irr j
    letI : Simple τ := FDRep.simple_of_isIrreducible τ
    letI : Nontrivial τ := nontrivial_of_isIrreducible_local (G := G) τ.ρ
    obtain ⟨i, hi⟩ := hπ_complete.exists_iso τ (FDRep.simple_of_isIrreducible τ)
    rcases hi with ⟨e⟩
    have hchar :
        ((σ j).toRepresentation).character = (π i).character := by
      -- Completeness identifies this irreducible regular summand with one chosen family member.
      simpa [τ] using FDRep.char_iso e
    have hcoeff :
        ∑ t : G, f t * ((σ j).toRepresentation).character t = 0 := by
      simpa [hchar] using hf i
    have hfinrank :
        (Module.finrank ℂ (σ j).toSubmodule : ℂ) ≠ 0 := by
      -- Irreducible summands are nontrivial, hence have positive finite dimension.
      simpa [τ] using (show (Module.finrank ℂ τ : ℂ) ≠ 0 by
        exact_mod_cast Module.finrank_pos.ne')
    have hzero :
        (σ j).toRepresentation.asAlgebraHom (Finsupp.equivFunOnFinite.symm f) = 0 := by
      -- Proposition `2-2.5-1` turns the class-function operator on this irreducible summand into
      -- the zero scalar map.
      have hscalar :=
        asAlgebraHom_classFunction_eq_character_sum_smul_id
          (ρ := (σ j).toRepresentation) (f := f) hfinrank
      rw [hcoeff, mul_zero, zero_smul] at hscalar
      simpa using hscalar
    -- Forget the subtype after applying the zero restricted operator to the chosen vector.
    change T x = 0
    have hxzero :
        ((σ j).toRepresentation.asAlgebraHom (Finsupp.equivFunOnFinite.symm f) ⟨x, hx⟩ :
          (σ j).toSubmodule) = 0 := by
      simpa using congrArg (fun A : Module.End ℂ (σ j).toSubmodule => A ⟨x, hx⟩) hzero
    have hcoeffFinsupp :
        Finsupp.equivFunOnFinite.symm f = ∑ t : G, f t • MonoidAlgebra.of ℂ G t := by
      simpa [MonoidAlgebra.of] using Finsupp.equivFunOnFinite_symm_eq_sum f
    have hrestrict_apply :
        ((((σ j).toRepresentation.asAlgebraHom (Finsupp.equivFunOnFinite.symm f)) ⟨x, hx⟩ :
            (σ j).toSubmodule) : G →₀ ℂ) = T x := by
      -- Restricting the regular action to an invariant summand does not change the ambient value.
      dsimp [T, ρ]
      rw [hcoeffFinsupp]
      simp [Subrepresentation.toRepresentation]
    exact hrestrict_apply.symm.trans (congrArg Subtype.val hxzero)
  have hker_top : LinearMap.ker T = ⊤ := by
    -- The regular representation is the supremum of the irreducible summands just shown to lie in
    -- the kernel of the weighted operator.
    apply top_unique
    simpa [hσ_top] using iSup_le hsub
  have hsinge_zero : T (Finsupp.single (1 : G) (1 : ℂ)) = 0 := by
    -- With trivial kernel complement, the operator vanishes on the basis vector at `1`.
    have hmem :
        Finsupp.single (1 : G) (1 : ℂ) ∈ LinearMap.ker T := by
      simpa [hker_top] using
        (show Finsupp.single (1 : G) (1 : ℂ) ∈ (⊤ : Submodule ℂ (G →₀ ℂ)) from trivial)
    simpa [LinearMap.mem_ker] using hmem
  apply Subtype.ext
  ext g
  have hsinge_coeff := congrArg (fun v : G →₀ ℂ ↦ v g) hsinge_zero
  have happly :
      T (Finsupp.single (1 : G) (1 : ℂ)) g = f g := by
    -- Evaluating the regular-representation operator on `e₁` recovers the coefficients of `f`.
    dsimp [T, ρ]
    have hcoeff :
        Finsupp.equivFunOnFinite.symm f = ∑ t : G, f t • MonoidAlgebra.of ℂ G t := by
      simpa [MonoidAlgebra.of] using Finsupp.equivFunOnFinite_symm_eq_sum f
    rw [hcoeff]
    simp [Representation.ofMulAction_single, smul_eq_mul, Finsupp.single_apply]
  simpa [happly] using hsinge_coeff

-- Proof sketch: if a class function is orthogonal to every irreducible character, then
-- Proposition `asAlgebraHom_classFunction_sum_eq_character_sum_smul_id` forces the associated
-- endomorphism `∑ t, f t • ρ t` to vanish on every irreducible representation, hence on every
-- representation. Completeness identifies all irreducible characters with members of the family,
-- and applying the resulting vanishing statement to the regular representation shows the original
-- class function is zero, so the irreducible characters span `H`.
/-- The irreducible characters of a complete irreducible family span the class-function
subspace. -/
private theorem span_irreducibleCharacters_eq_top_of_complete_family
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Submodule.span ℂ (Set.range fun i ↦ characterClassFunction_local (G := G) (π i).ρ) = ⊤ := by
  classical
  let χ : ι → classFunctionSubmodule ℂ G := fun i ↦ characterClassFunction_local (G := G) (π i).ρ
  let W : Submodule ℂ (classFunctionSubmodule ℂ G) := Submodule.span ℂ (Set.range χ)
  let B : LinearMap.BilinForm ℂ (classFunctionSubmodule ℂ G) :=
    { toFun := fun φ =>
        { toFun := fun ψ ↦ ∑ t : G, φ t * ψ t
          map_add' := by
            intro ψ₁ ψ₂
            simp [mul_add, Finset.sum_add_distrib]
          map_smul' := by
            intro a ψ
            simp [smul_eq_mul, Finset.mul_sum, mul_left_comm] }
      map_add' := by
        intro φ₁ φ₂
        ext ψ
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a φ
        ext ψ
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hB_refl : B.IsRefl := by
    intro φ ψ hφψ
    simpa [B, mul_comm] using hφψ
  have horth : B.orthogonal W = ⊥ := by
    apply eq_bot_iff.2
    intro f hf
    have hf_zero : ∀ i, ∑ t : G, f t * (π i).character t = 0 := by
      intro i
      have hχ_mem : χ i ∈ W := Submodule.subset_span ⟨i, rfl⟩
      have hleft : B (χ i) f = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hf) _ hχ_mem
      simpa [B, χ, mul_comm] using hB_refl _ _ hleft
    -- Orthogonality to the full character span is exactly the source annihilator hypothesis.
    simpa [χ] using
      eq_zero_of_pairing_irreducibleCharacters_eq_zero π hπ_complete f hf_zero
  have hrestrict : (B.restrict W).Nondegenerate := by
    -- Once the orthogonal complement is zero, the pairing restricts nondegenerately to the span.
    apply B.nondegenerate_restrict_of_disjoint_orthogonal hB_refl
    rw [horth]
    simp
  -- The bilinear orthogonal-complement criterion now upgrades the annihilator computation to the
  -- spanning statement.
  exact B.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot hB_refl hrestrict horth

/-- Theorem 2-2.5-2: for a complete set of pairwise nonisomorphic irreducible complex
representations of a finite group, their characters form a basis of the class-function
space `H`. -/
def irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π) :
    Module.Basis ι ℂ (classFunctionSubmodule ℂ G) :=
  Module.Basis.mk
    (linearIndependent_irreducibleCharacters_of_pairwiseNonisomorphic
      π hπ_complete.isSimple hπ_pairwise)
    (span_irreducibleCharacters_eq_top_of_complete_family π hπ_complete).ge

-- Proof sketch: `Module.Basis.mk` evaluates to the generating family by
-- `Module.Basis.mk_apply`.
/-- Evaluating the basis from Theorem `2-2.5-2` at `i` returns the character of `π i`. -/
@[simp] theorem irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (i : ι) :
    ((irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete i : classFunctionSubmodule ℂ G) : G → ℂ) =
      (π i).character := by
  -- `Module.Basis.mk` evaluates to the original generating family.
  exact congrArg (fun z : classFunctionSubmodule ℂ G ↦ (z : G → ℂ)) <|
    Module.Basis.mk_apply
      (linearIndependent_irreducibleCharacters_of_pairwiseNonisomorphic
        π hπ_complete.isSimple hπ_pairwise)
      (span_irreducibleCharacters_eq_top_of_complete_family π hπ_complete).ge
      i

end CompleteFamily

end

end

end Representation
