import Mathlib
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_2_2_5_4 (from Chap02) -/
open scoped BigOperators
open CategoryTheory

noncomputable section

universe u v

namespace Representation

section

variable {G : Type} [Group G] [Finite G]
variable {ι : Type v}
variable (π : ι → FDRep ℂ G)

section CompleteFamily

/-- Helper for Proposition 2-2.5-4: pairing the conjugacy-class indicator with an irreducible
character returns the coefficient from the source proof. -/
private theorem indicator_pairing_with_irreducible_character
    (s : G) (i : ι) :
    Representation.groupFunctionPairingOverField ℂ
        ((ConjClasses.mk s).indicatorClassFunction : G → ℂ)
        (π i).character =
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
        star ((π i).character s) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let carrier : Set G := (ConjClasses.mk s).carrier
  let S : Finset G := Finset.univ.filter (fun t : G ↦ t ∈ carrier)
  -- Rewrite the normalized pairing as an explicit finite sum over the group.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  calc
    (↑(Nat.card G))⁻¹ *
        (∑ t : G, ((ConjClasses.mk s).indicator t : ℂ) * (π i).character t⁻¹) =
      (↑(Nat.card G))⁻¹ * Finset.sum S (fun t ↦ (π i).character t⁻¹) := by
        congr 1
        simp [ConjClasses.indicator, carrier, S, Set.indicator, Finset.sum_filter, mul_comm]
    _ = (↑(Nat.card G))⁻¹ * (S.card * star ((π i).character s)) := by
        congr 1
        -- Every term on the conjugacy class contributes the same value `χ_i(s)^*`.
        calc
          Finset.sum S (fun t ↦ (π i).character t⁻¹) =
              Finset.sum S (fun _ ↦ star ((π i).character s)) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            have ht' : t ∈ carrier := by
              simpa [S] using (Finset.mem_filter.mp ht).2
            have hconj : IsConj t s := by
              exact ConjClasses.mk_eq_mk_iff_isConj.mp
                ((ConjClasses.mem_carrier_iff_mk_eq).mp ht')
            have hconj_inv : IsConj t⁻¹ s⁻¹ := by
              rcases isConj_iff.mp hconj with ⟨a, ha⟩
              refine isConj_iff.mpr ⟨a, ?_⟩
              calc
                a * t⁻¹ * a⁻¹ = (a * t * a⁻¹)⁻¹ := by simp [mul_assoc]
                _ = s⁻¹ := by simp [ha]
            calc
              (π i).character t⁻¹ = (π i).character s⁻¹ := by
                simpa using Representation.char_eq_of_isConj (ρ := (π i).ρ) hconj_inv
              _ = star ((π i).character s) := by
                simpa using Representation.char_inv_eq_star_of_isOfFinOrder
                  (ρ := (π i).ρ) s (isOfFinOrder_of_finite s)
          _ = S.card * star ((π i).character s) := by
            simp [nsmul_eq_mul]
    _ = ((Nat.card carrier : ℂ) / Nat.card G) * star ((π i).character s) := by
        have hcard : S.card = Nat.card carrier := by
          let _ : Fintype carrier := Fintype.ofFinite carrier
          rw [Nat.card_eq_fintype_card]
          symm
          exact Fintype.card_of_subtype S (fun t ↦ by simp [S, carrier])
        rw [hcard]
        simp [div_eq_mul_inv, mul_assoc, mul_comm]

/-- Helper for Proposition 2-2.5-4: the coordinate of a class function in the irreducible
character basis is its pairing with the corresponding irreducible character. -/
private theorem repr_complete_family_basis_eq_pairing
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    [Finite ι]
    (x : classFunctionSubmodule ℂ G) (i : ι) :
    (irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
        π hπ_pairwise hπ_complete).repr x i =
      Representation.groupFunctionPairingOverField ℂ (x : G → ℂ) (π i).character := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let coordLinear : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦ b.repr y i
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  let pairLinear : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ :=
    { toFun := fun y ↦
        Representation.groupFunctionPairingOverField ℂ (y : G → ℂ) (π i).character
      map_add' := by
        intro y z
        simpa using Representation.groupFunctionPairing_add_left
          (y : G → ℂ) (z : G → ℂ) (π i).character
      map_smul' := by
        intro a y
        simpa using Representation.groupFunctionPairing_smul_left
          a (y : G → ℂ) (π i).character }
  have hmaps : coordLinear = pairLinear := by
    -- Compare the two linear functionals on the character basis itself.
    apply b.ext
    intro j
    have hcoord_j : coordLinear (b j) = if i = j then 1 else 0 := by
      simpa [eq_comm] using
        (show coordLinear (b j) = if j = i then 1 else 0 by
          simp [coordLinear, b, Module.Basis.repr_self, Finsupp.single_apply])
    have hpair_j : pairLinear (b j) = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        letI : Simple (π i) := hπ_complete.isSimple i
        have hself_iso : Nonempty (π i ≅ π i) := ⟨Iso.refl _⟩
        calc
          pairLinear (b i) =
              Representation.groupFunctionPairingOverField ℂ
                (π i).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 1 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hself_iso] using
              (FDRep.char_orthonormal (π i) (π i))
          _ = if i = i then 1 else 0 := by simp
      · have hji : j ≠ i := fun h ↦ hij h.symm
        letI : Simple (π j) := hπ_complete.isSimple j
        letI : Simple (π i) := hπ_complete.isSimple i
        have hnot : ¬ Nonempty (π j ≅ π i) := hπ_pairwise hji
        calc
          pairLinear (b j) =
              Representation.groupFunctionPairingOverField ℂ
                (π j).character (π i).character := by
            simp [pairLinear, b,
              irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply]
          _ = 0 := by
            simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
              hnot] using
              (FDRep.char_orthonormal (π j) (π i))
          _ = if i = j then 1 else 0 := by simp [hij]
    exact hcoord_j.trans hpair_j.symm
  -- Apply the equality of functionals to the chosen class function.
  have hmaps_apply := congrArg
    (fun f : classFunctionSubmodule ℂ G →ₗ[ℂ] ℂ ↦ f x) hmaps
  simpa [coordLinear, pairLinear] using hmaps_apply

-- Proof sketch: apply the character-basis expansion from the preceding results to the conjugacy
-- class indicator function `(ConjClasses.mk s).indicator`, then rearrange the resulting equality
-- of class functions.
/-- Proposition 2-2.5-4: for a complete set of pairwise nonisomorphic irreducible complex
representations, the scalar-weighted sum of their character functions is `(g / c(s))` times the
indicator of the conjugacy class of `s`, so parts (a) and (b) are its evaluations at `t = s` and
at `t` not conjugate to `s`. -/
theorem sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    ∑' i : ι, star ((π i).character s) • (π i).character =
      ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
        Set.indicator ((ConjClasses.mk s).carrier) (fun _ ↦ (1 : ℂ)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hg_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  let _ : NeZero (Nat.card G : ℂ) := ⟨hg_ne⟩
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  let b := irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
    π hπ_pairwise hπ_complete
  let x : classFunctionSubmodule ℂ G := (ConjClasses.mk s).indicatorClassFunction
  have hcoeff :
      ∀ i, b.repr x i =
        ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          star ((π i).character s) := by
    intro i
    -- The basis coefficient is exactly the pairing computed above.
    rw [repr_complete_family_basis_eq_pairing (π := π) hπ_pairwise hπ_complete x i]
    simpa [x] using indicator_pairing_with_irreducible_character (π := π) s i
  have hsum :
      ∑ i,
          (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
              star ((π i).character s)) • (π i).character =
        (x : G → ℂ) := by
    -- Evaluate the basis expansion pointwise after substituting the coefficient formula.
    funext t
    have hsum_t := congrArg
      (fun z : classFunctionSubmodule ℂ G ↦ (z : G → ℂ) t) (b.sum_repr x)
    simpa [b, x, hcoeff,
      irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family_apply,
      smul_eq_mul] using hsum_t
  have hscaled :
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
        (∑ i, star ((π i).character s) • (π i).character) =
      (x : G → ℂ) := by
    -- Factor the common scalar `(c(s) / g)` out of the finite basis expansion.
    rw [Finset.smul_sum]
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hsum
  have hcarrier_ne : (Nat.card ((ConjClasses.mk s).carrier) : ℂ) ≠ 0 := by
    let _ : Nonempty ((ConjClasses.mk s).carrier) :=
      ⟨⟨s, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl⟩⟩
    exact_mod_cast Nat.card_pos.ne'
  have hcoeff_ne :
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) ≠ 0 := by
    exact div_ne_zero hcarrier_ne hg_ne
  have hcancel :
      (((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) *
          ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier))) = 1 := by
    field_simp [hcarrier_ne, hg_ne]
  have hfinal :
      ∑ i, star ((π i).character s) • (π i).character =
        ((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) • (x : G → ℂ) := by
    -- Scalar multiplication by `(c(s) / g)` is injective, so it suffices to compare after
    -- multiplying both sides by that nonzero scalar.
    apply (smul_right_injective (G → ℂ) hcoeff_ne)
    calc
      ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
          (∑ i, star ((π i).character s) • (π i).character) =
        (x : G → ℂ) := hscaled
      _ =
        ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
          (((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
            (x : G → ℂ)) := by
        calc
          (x : G → ℂ) = (1 : ℂ) • (x : G → ℂ) := by simp
          _ =
            ((Nat.card ((ConjClasses.mk s).carrier) : ℂ) / Nat.card G) •
              (((Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier)) •
                (x : G → ℂ)) := by
            rw [smul_smul, hcancel]
  simpa [x, ConjClasses.indicator, Set.indicator, tsum_fintype] using hfinal

-- Proof sketch: evaluate
-- `sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family` at `t = s` and
-- use `conjClassIndicator_mk_self`.
/-- Evaluating the character-row orthogonality formula at `s` gives `g / c(s)`. -/
theorem sum_star_character_mul_character_self_eq_card_div_conjClass_card_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (s : G) :
    ∑' i : ι, star ((π i).character s) * (π i).character s =
      (Nat.card G : ℂ) / Nat.card ((ConjClasses.mk s).carrier) := by
  classical
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Evaluate the class-function identity at the element `s` itself.
  have hmain :=
    sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
      (π := π) hπ_pairwise hπ_complete s
  simpa [tsum_fintype, Pi.smul_apply, Set.indicator,
    ConjClasses.mem_carrier_iff_mk_eq] using congrFun hmain s

-- Proof sketch: evaluate
-- `sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family` at `t` and use
-- `conjClassIndicator_mk_eq_zero_of_not_isConj`.
/-- If `t` is not conjugate to `s`, the same irreducible-character sum vanishes. -/
theorem sum_star_character_mul_character_eq_zero_of_not_isConj_of_complete_family
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {s t : G} (hst : ¬ IsConj t s) :
    ∑' i : ι, star ((π i).character s) * (π i).character t = 0 := by
  classical
  let _ : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Evaluate the same class-function identity away from the conjugacy class of `s`.
  have hmain :=
    sum_star_character_mul_character_eq_conjClassIndicator_mk_of_complete_family
      (π := π) hπ_pairwise hπ_complete s
  have htnot : ConjClasses.mk t ≠ ConjClasses.mk s := by
    intro hmk
    exact hst (ConjClasses.mk_eq_mk_iff_isConj.mp hmk)
  simpa [tsum_fintype, Pi.smul_apply, Set.indicator,
    ConjClasses.mem_carrier_iff_mk_eq, htnot] using
    congrFun hmain t

end CompleteFamily

end

end Representation

/-! ### Theorem_2_2_5_2 (from Chap02) -/
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

/-! ### Theorem_2_2_5_2 (from Items/Chap02) -/
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

/-! ### Theorem_2_2_5_3 (from Chap02) -/
universe u v w

namespace Representation

noncomputable section

section

open CategoryTheory

variable {G : Type} [Group G] [Finite G]

variable {ι : Type v}
variable (π : ι → FDRep ℂ G)

-- Proof sketch: Theorem
-- `irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family` supplies a basis of
-- `classFunctionSubspace G` indexed by `ι`. Evaluating a class function on conjugacy classes
-- identifies that space with the full function space on `ConjClasses G`, whose dimension is the
-- number of conjugacy classes. Comparing the cardinalities of these bases yields the equality.
/-- Theorem 2-2.5-3: for a complete set of pairwise nonisomorphic irreducible complex
representations of a finite group, the number of indices is the number of conjugacy classes of
`G`. -/
theorem card_eq_card_conjClasses_of_complete_irreducible_family
    (hπ_simple : ∀ i, Simple (π i))
    (hπ_pairwise : ∀ ⦃i j⦄, i ≠ j → ¬ Nonempty (π i ≅ π j))
    (hπ_complete : ∀ τ : FDRep ℂ G, Simple τ → ∃ i, Nonempty (τ ≅ π i)) :
    Nat.card ι = Nat.card (ConjClasses G) := by
  classical
  -- Package the hypotheses into the canonical pairwise/completeness data used by Theorem `2-2.5-2`.
  have hπ_pairwise_cat : PairwiseNonisomorphic π := hπ_pairwise
  let hπ_family : IsCompleteIrreducibleFamily π := {
    isSimple := hπ_simple
    exists_iso := hπ_complete
  }
  -- The dependency theorem gives a basis of class functions indexed by the irreducible family.
  let bπ : Module.Basis ι ℂ (classFunctionSubmodule ℂ G) :=
    irreducibleCharacters_basis_of_classFunctionSubspace_of_complete_family
      π hπ_pairwise_cat hπ_family
  -- Evaluating a class function on conjugacy classes gives the canonical conjugacy-class basis.
  let bConj : Module.Basis (ConjClasses G) ℂ (classFunctionSubmodule ℂ G) :=
    Module.Basis.ofEquivFun (classFunctionSubmodule.equivFun ℂ G)
  -- Comparing the two bases identifies the irreducible indices with the conjugacy classes.
  exact Nat.card_congr (bπ.indexEquiv bConj)

end

end

end Representation

/-! ### Example_2_2_6_2 (from Chap02) -/
open scoped BigOperators

universe u v

namespace Representation

noncomputable section

section

variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) := by
  refine invertibleOfNonzero ?_
  exact_mod_cast Nat.card_pos.ne'

-- Proof sketch: apply the regular-character formula
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank` to `σ ⟶ leftRegular`, then use
-- `leftRegular_character_eq_ite` to collapse the sum to the identity element.
/-- The intertwining space from `σ` into the regular representation has dimension `dim σ`. -/
theorem finrank_intertwiningMap_leftRegular
    (σ : Representation ℂ G W) [FiniteDimensional ℂ W] :
    Module.finrank ℂ (σ.IntertwiningMap (leftRegular ℂ G)) = Module.finrank ℂ W := by
  let ρ := leftRegular ℂ G
  have hsum :
      ∑ g : G, ρ.character g * σ.character g⁻¹ =
        (Nat.card G : ℂ) * Module.finrank ℂ W := by
    rw [Finset.sum_eq_single 1]
    · rw [leftRegular_character_one]
      simp [σ.char_one]
    · intro g _ hg
      rw [leftRegular_character_eq_zero_of_ne_one hg]
      simp
    · intro h
      exact False.elim (h (Finset.mem_univ 1))
  have h :
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
        Module.finrank ℂ W := by
    calc
      (Module.finrank ℂ (σ.IntertwiningMap ρ) : ℂ) =
          (Nat.card G : ℂ)⁻¹ *
            ∑ g : G, ρ.character g * σ.character g⁻¹ := by
              symm
              simpa using
                (card_inv_mul_sum_char_mul_char_eq_finrank σ ρ)
      _ = Module.finrank ℂ W := by
        rw [hsum]
        field_simp
  exact_mod_cast h

variable (σ : Representation ℂ G W) [σ.IsIrreducible]

-- Proof sketch: Exercise `2-2.6-3` already gives the canonical owner map from a family of
-- intertwining maps into the `σ`-isotypic component. A basis of the intertwining space therefore
-- yields the desired direct-sum evaluation equivalence; the basis is auxiliary data, so it stays
-- explicit in this bridge construction.
/-- A basis of `Hom_G(σ, ℂ[G])` indexed by `Fin (dim σ)` yields the corresponding equivariant
identification of the `σ`-isotypic summand of the regular representation with the direct sum of
`dim σ` copies of `σ`. This is a bridge/view built from the chosen basis, not an intrinsic owner
of the isotypic summand. -/
def leftRegular_isotypicComponent_equiv_directSum_of_basis
    (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ
      (σ.IntertwiningMap (leftRegular ℂ G))) :
    (directSum fun _ : Fin (Module.finrank ℂ W) ↦ σ).Equiv
      ((leftRegular ℂ G).isotypicSubrepresentation σ).toRepresentation :=
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  let ρ := leftRegular ℂ G
  (ρ.familyDirectSumEvaluation σ b).ofBijective
    (familyDirectSumEvaluation_bijective ρ σ b)

-- Proof sketch: first compute `dim Hom_G(σ, ℂ[G]) = dim σ`. Then choose a basis of that
-- intertwining space with index set `Fin (dim σ)` and apply the explicit-basis bridge above.
/-- Example 2-2.6-2: for an irreducible complex representation `σ` of a finite group, the
`σ`-isotypic summand of the regular representation is equivariantly equivalent to the direct sum
of `dim σ` copies of `σ`. -/
theorem leftRegular_isotypicComponent_nonempty_equiv_directSum :
    Nonempty
      ((directSum fun _ : Fin (Module.finrank ℂ W) ↦ σ).Equiv
        ((leftRegular ℂ G).isotypicSubrepresentation σ).toRepresentation) := by
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  let b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ
      (σ.IntertwiningMap (leftRegular ℂ G)) :=
    Module.finBasisOfFinrankEq ℂ (σ.IntertwiningMap (leftRegular ℂ G))
      (finrank_intertwiningMap_leftRegular σ)
  exact ⟨leftRegular_isotypicComponent_equiv_directSum_of_basis σ b⟩

-- Proof sketch: apply the preceding direct-sum decomposition theorem and compare dimensions across
-- the resulting representation equivalence. The direct sum of `Module.finrank ℂ W` copies of `σ`
-- has dimension `Module.finrank ℂ W * Module.finrank ℂ W`.
/-- The complex dimension of the `σ`-isotypic summand of the regular representation is the square
of the degree of `σ`. -/
theorem finrank_leftRegular_isotypicComponent
    : Module.finrank ℂ (((leftRegular ℂ G).isotypicSubrepresentation σ).toSubmodule) =
      Module.finrank ℂ W ^ 2 := by
  letI : FiniteDimensional ℂ W := IsIrreducible.finiteDimensional_of_finite σ
  rcases leftRegular_isotypicComponent_nonempty_equiv_directSum σ with ⟨e⟩
  calc
    Module.finrank ℂ (((leftRegular ℂ G).isotypicSubrepresentation σ).toSubmodule) =
        Module.finrank ℂ
          (DirectSum (Fin (Module.finrank ℂ W)) (fun _ : Fin (Module.finrank ℂ W) ↦ W)) := by
            exact e.finrank_eq.symm
    _ = Module.finrank ℂ W ^ 2 := by
      simp [Module.finrank_directSum, pow_two]

end

end

end Representation
