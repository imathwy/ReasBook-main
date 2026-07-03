import Mathlib
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Induced

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_7_2_5 (from Chap07) -/
open scoped Representation
open scoped SubgroupInduction
open scoped BigOperators

noncomputable section

universe u v

namespace Subgroup

section

variable {G : Type u} [Group G]

/-- A subgroup `H ≤ G` is Frobenius when its intersection with each distinct conjugate `tHt⁻¹`
is trivial. -/
def IsFrobeniusSubgroup (H : Subgroup G) : Prop :=
  ∀ ⦃t : G⦄, t ∉ H → H ⊓ H.map (MulAut.conj t).toMonoidHom = ⊥

/-- The set of elements of `G` that are not conjugate to any element of `H`. This is the set
called `N` in Exercise `7-7.2-5`. -/
def frobeniusNonconjugateSet (H : Subgroup G) : Set G :=
  { g | ∀ h : H, ¬ IsConj g h }

end

section

variable {G : Type u} [Group G]
variable {R : Type v} [Semiring R]

private theorem classFunctionRestriction_mem (H : Subgroup G) (χ : classFunctionSubmodule R G) :
    ((LinearMap.funLeft R R H.subtype).comp (classFunctionSubmodule R G).subtype) χ ∈
      classFunctionSubmodule R H := by
  change IsClassFunction (fun h : H ↦ (χ : G → R) h)
  letI : IsClassFunction (χ : G → R) := (mem_classFunctionSubmodule_iff R _).1 χ.2
  refine ⟨fun {u v} huv ↦ ?_⟩
  have huvH : IsConj u v := (ConjClasses.mk_eq_mk_iff_isConj).1 huv
  have huvG : IsConj (u : G) (v : G) := by
    rw [isConj_iff] at huvH ⊢
    rcases huvH with ⟨c, hc⟩
    exact ⟨(c : G), by simpa using congrArg Subtype.val hc⟩
  exact (inferInstance : IsClassFunction (χ : G → R)).eq_of_isConj huvG

/-- Restriction of a class function on `G` to a subgroup `H`. -/
def classFunctionRestriction (H : Subgroup G) :
    classFunctionSubmodule R G →ₗ[R] classFunctionSubmodule R H :=
  LinearMap.codRestrict (classFunctionSubmodule R H)
    ((LinearMap.funLeft R R H.subtype).comp (classFunctionSubmodule R G).subtype)
    (classFunctionRestriction_mem H)

@[simp] theorem classFunctionRestriction_apply (H : Subgroup G) (χ : classFunctionSubmodule R G)
    (h : H) : (H.classFunctionRestriction χ : H → R) h = (χ : G → R) h := rfl

end

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

local instance (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- Helper for Exercise 7-7.2-5: two conjugating elements that send the same nonidentity element
into a Frobenius subgroup differ by an element of that subgroup. -/
theorem frobenius_fixed_coset_uniqueness
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    {g r₁ r₂ : G} (hg : g ≠ 1)
    (hr₁ : r₁⁻¹ * g * r₁ ∈ H) (hr₂ : r₂⁻¹ * g * r₂ ∈ H) :
    r₂⁻¹ * r₁ ∈ H := by
  let t : G := r₂⁻¹ * r₁
  by_cases ht : t ∈ H
  · simpa [t] using ht
  · have hbot : H ⊓ H.map (MulAut.conj t).toMonoidHom = ⊥ := hF ht
    have hmap : r₂⁻¹ * g * r₂ ∈ H.map (MulAut.conj t).toMonoidHom := by
      change ∃ x, x ∈ H ∧ (MulAut.conj t).toMonoidHom x = r₂⁻¹ * g * r₂
      refine ⟨r₁⁻¹ * g * r₁, hr₁, ?_⟩
      simp [MulAut.conj, t]
      group
    have hmem : r₂⁻¹ * g * r₂ ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := ⟨hr₂, hmap⟩
    have hone : r₂⁻¹ * g * r₂ = 1 := by
      have : r₂⁻¹ * g * r₂ ∈ (⊥ : Subgroup G) := by
        rwa [hbot] at hmem
      simpa using this
    apply False.elim
    apply hg
    calc
      g = r₂ * (r₂⁻¹ * g * r₂) * r₂⁻¹ := by group
      _ = 1 := by simp [hone]

/-- Helper for Exercise 7-7.2-5: once a left transversal is fixed, every nonidentity element of
`G` that is conjugate to `H` corresponds bijectively to a transversal element together with a
nonidentity element of `H`. -/
noncomputable def frobenius_nonidentity_conjugate_equiv_transversal_prod
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) :
    { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } ≃
      ↥(R : Set G) × { h : H // h ≠ 1 } := by
  classical
  let P : G → ↥(R : Set G) × { h : H // h ≠ 1 } → Prop := fun g p ↦
    g = (p.1 : G) * (p.2.1 : H) * (p.1 : G)⁻¹
  have hexu :
      ∀ {g : G}, g ≠ 1 → g ∉ H.frobeniusNonconjugateSet →
        ∃! p : ↥(R : Set G) × { h : H // h ≠ 1 }, P g p := by
    intro g hg1 hgN
    rw [frobeniusNonconjugateSet, Set.mem_setOf_eq, not_forall] at hgN
    rcases hgN with ⟨h, hh⟩
    have hconj : IsConj g h := Classical.not_not.mp hh
    rcases isConj_iff.1 hconj with ⟨c, hc⟩
    let y := hR.equiv c⁻¹
    let r : ↥(R : Set G) := y.1
    let t : H := y.2
    have hy : (r : G) * t = c⁻¹ := by
      simpa [y, r, t] using hR.equiv_fst_mul_equiv_snd c⁻¹
    have hr_mem : (r : G)⁻¹ * g * r ∈ H := by
      -- Rewrite the chosen conjugator through the fixed transversal decomposition.
      have hrewrite :
          (r : G)⁻¹ * g * r = ((t : H) : G) * h * (((t : H) : G)⁻¹) := by
        have hc' : g = c⁻¹ * h * c := by
          calc
            g = c⁻¹ * (c * g * c⁻¹) * c := by group
            _ = c⁻¹ * h * c := by rw [hc]
        have hc_inv : c = (c⁻¹)⁻¹ := by simp
        rw [hc', hc_inv, ← hy]
        simp [mul_assoc]
      rw [hrewrite]
      exact H.mul_mem (H.mul_mem t.property h.property) (H.inv_mem t.property)
    have hr_ne : (⟨(r : G)⁻¹ * g * r, hr_mem⟩ : H) ≠ 1 := by
      intro h1
      apply hg1
      have h1' : (r : G)⁻¹ * g * r = 1 := by
        simpa using congrArg Subtype.val h1
      calc
        g = (r : G) * ((r : G)⁻¹ * g * r) * (r : G)⁻¹ := by group
        _ = 1 := by simp [h1']
    refine ⟨⟨r, ⟨⟨(r : G)⁻¹ * g * r, hr_mem⟩, hr_ne⟩⟩, ?_, ?_⟩
    · -- The chosen pair reconstructs `g` by design.
      dsimp [P]
      group
    · intro p hp
      rcases p with ⟨r', h'⟩
      dsimp [P] at hp
      have hr'_mem : (r' : G)⁻¹ * g * r' ∈ H := by
        have hh'_mem : ((h'.1 : H) : G) ∈ H := h'.1.property
        simpa [hp, mul_assoc] using hh'_mem
      have hr'_eq : (r' : G)⁻¹ * g * r' = h'.1 := by
        rw [hp]
        group
      have hr_rel : (r' : G)⁻¹ * (r : G) ∈ H := by
        exact H.frobenius_fixed_coset_uniqueness hF (g := g) hg1 hr_mem hr'_mem
      have hleft :
          LeftCosetEquivalence H (r : G) (r' : G) := by
        simpa [LeftCosetEquivalence, leftCoset_eq_iff] using H.inv_mem hr_rel
      have hr_eq_fst :
          (hR.equiv (r : G)).fst = (hR.equiv (r' : G)).fst :=
        (hR.equiv_fst_eq_iff_leftCosetEquivalence).2 hleft
      have h1H : (1 : G) ∈ H := by
        simp
      have hr_self :
          (hR.equiv (r : G)).fst = r :=
        hR.equiv_fst_eq_self_of_mem_of_one_mem h1H r.property
      have hr'_self :
          (hR.equiv (r' : G)).fst = r' :=
        hR.equiv_fst_eq_self_of_mem_of_one_mem h1H r'.property
      have hr_eq : r = r' := hr_self.symm.trans <| hr_eq_fst.trans hr'_self
      have hh_eq : h'.1 = ⟨(r : G)⁻¹ * g * r, hr_mem⟩ := by
        apply Subtype.ext
        calc
          ((h'.1 : H) : G) = (r' : G)⁻¹ * g * r' := by
            simpa using hr'_eq.symm
          _ = (r : G)⁻¹ * g * r := by simpa [hr_eq]
          _ = ((⟨(r : G)⁻¹ * g * r, hr_mem⟩ : H) : G) := rfl
      apply Prod.ext
      · exact hr_eq.symm
      · apply Subtype.ext
        exact hh_eq
  refine
    { toFun := fun g ↦ Classical.choose (hexu (g := g) g.2.1 g.2.2)
      invFun := fun p ↦
        ⟨(p.1 : G) * (p.2.1 : H) * (p.1 : G)⁻¹, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- Conjugation preserves nontriviality of the subgroup element.
    intro h1
    exact p.2.2 <| by
      apply Subtype.ext
      calc
        (((p.2.1 : H) : G)) =
            (p.1 : G)⁻¹ * ((p.1 : G) * (p.2.1 : H) * (p.1 : G)⁻¹) * (p.1 : G) := by
              group
        _ = 1 := by simp [h1]
  · -- The image is visibly conjugate to a subgroup element, so it cannot lie in `N`.
    intro hN
    exact hN p.2.1 <| (isConj_iff.2 ⟨(p.1 : G)⁻¹, by group⟩)
  · -- Left inverse: the chosen witness satisfies the defining reconstruction equation.
    intro g
    apply Subtype.ext
    simpa [P] using (Classical.choose_spec (hexu (g := g) g.2.1 g.2.2)).1.symm
  · -- Right inverse: uniqueness recovers the original transversal/subgroup pair.
    intro p
    let g : G := (p.1 : G) * (p.2.1 : H) * (p.1 : G)⁻¹
    have hg1 : g ≠ 1 := by
      intro h1
      apply p.2.2
      apply Subtype.ext
      calc
        (((p.2.1 : H) : G)) = (p.1 : G)⁻¹ * g * (p.1 : G) := by
          dsimp [g]
          group
        _ = 1 := by simp [h1]
    have hgN : g ∉ H.frobeniusNonconjugateSet := by
      intro hN
      exact hN p.2.1 <| (isConj_iff.2 ⟨(p.1 : G)⁻¹, by
        dsimp [g]
        group⟩)
    have hchosen :
        P g (Classical.choose (hexu (g := g) hg1 hgN)) :=
      (Classical.choose_spec (hexu (g := g) hg1 hgN)).1
    exact ExistsUnique.unique (hexu (g := g) hg1 hgN) hchosen rfl

/-- Helper for Exercise 7-7.2-5: a left transversal for `H` has cardinality equal to the index
`[G : H]`. -/
theorem card_transversal_eq_index_of_isComplement
    (H : Subgroup G) (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) :
    Nat.card ↥(R : Set G) = H.index := by
  -- Compare the complement equivalence `G ≃ R × H` with the subgroup index identity.
  have hmul : Nat.card ↥(R : Set G) * Nat.card H = Nat.card G := by
    calc
      Nat.card ↥(R : Set G) * Nat.card H = Nat.card (↥(R : Set G) × H) := by
        simp [Nat.card_eq_fintype_card]
      _ = Nat.card G := by
        exact Nat.card_congr hR.equiv.symm
  have hmul' : Nat.card ↥(R : Set G) * Nat.card H = H.index * Nat.card H := by
    rw [hmul, H.index_mul_card]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul'

/-- Helper for Exercise 7-7.2-5: the nonidentity elements of `G` that are conjugate into `H`
occur in `H.index` copies of the nonidentity elements of `H`. -/
theorem frobenius_nonidentity_conjugate_card
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (R : Finset G) (hR : IsComplement (R : Set G) (H : Set G)) :
    Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } =
      H.index * (Nat.card H - 1) := by
  classical
  let e := H.frobenius_nonidentity_conjugate_equiv_transversal_prod hF R hR
  have hcardHne : Nat.card { h : H // h ≠ 1 } = Nat.card H - 1 := by
    -- Removing the identity from `H` leaves exactly `|H| - 1` elements.
    simp [Nat.card_eq_fintype_card]
  -- The geometric parametrization from the previous helper now becomes a counting formula.
  calc
    Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } =
        Nat.card (↥(R : Set G) × { h : H // h ≠ 1 }) := Nat.card_congr e
    _ = Nat.card ↥(R : Set G) * Nat.card { h : H // h ≠ 1 } := by
      simp [Nat.card_eq_fintype_card]
    _ = H.index * (Nat.card H - 1) := by
      rw [H.card_transversal_eq_index_of_isComplement R hR, hcardHne]

/-- Exercise 7-7.2-5 (1): source part (a). For a Frobenius subgroup `H ≤ G`, the set `N` of
elements of `G` that are not conjugate to any element of `H` has cardinality `|G| / |H| - 1`. -/
-- Proof sketch: decompose `G` into the identity, the conjugates of the nonidentity elements of
-- `H`, and the remaining set `N`. The Frobenius condition makes the conjugacy contributions from
-- distinct conjugates of `H` disjoint away from `1`, so counting these pieces yields the stated
-- formula.
theorem frobeniusNonconjugateSet_card (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) :
    Nat.card { g // g ∈ H.frobeniusNonconjugateSet } =
      Nat.card G / Nat.card H - 1 := by
  classical
  obtain ⟨S, hS, _h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have hcardC :
      Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } =
        H.index * (Nat.card H - 1) :=
    H.frobenius_nonidentity_conjugate_card hF R hR
  have h1not : (1 : G) ∉ H.frobeniusNonconjugateSet := by
    intro h1N
    exact h1N ⟨1, by simp⟩ (isConj_iff.2 ⟨1, by simp⟩)
  have hcardCompl :
      Nat.card { g : G // g ∉ H.frobeniusNonconjugateSet } =
        1 + Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } := by
    let α := { g : G // g ∉ H.frobeniusNonconjugateSet }
    let oneα : α := ⟨1, h1not⟩
    let _ : Fintype α := Fintype.ofFinite α
    have hcardNeα : Nat.card { x : α // x ≠ oneα } = Nat.card α - 1 := by
      -- Inside the complement of `N`, deleting the single point `1` subtracts exactly one.
      simpa [Nat.card_eq_fintype_card, oneα] using
        (Fintype.card_subtype_compl (fun x : α ↦ x = oneα))
    let e₁ : { x : α // x ≠ oneα } ≃ { x : α // x.1 ≠ 1 } :=
      Equiv.subtypeEquivRight fun x ↦ by
        constructor
        · intro hx hx1
          apply hx
          apply Subtype.ext
          simpa [oneα] using hx1
        · intro hx hx1
          apply hx
          simpa [oneα] using congrArg Subtype.val hx1
    let e₂ : { x : α // x.1 ≠ 1 } ≃
        { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } :=
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun g : G ↦ g ∉ H.frobeniusNonconjugateSet)
        (fun g : G ↦ g ≠ 1)).trans
        (Equiv.subtypeEquivRight fun g ↦ by simp [and_comm])
    have hcardNe :
        Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } = Nat.card α - 1 := by
      -- Route correction: count the complement of `N` by removing `1`, then identify the
      -- remainder with the nonidentity elements that are conjugate into `H`.
      calc
        Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } =
            Nat.card { x : α // x ≠ oneα } := by
              exact Nat.card_congr (e₁.trans e₂).symm
        _ = Nat.card α - 1 := hcardNeα
    let _ : Nonempty α := ⟨oneα⟩
    have hposα : 0 < Nat.card α := Nat.card_pos
    calc
      Nat.card { g : G // g ∉ H.frobeniusNonconjugateSet } = Nat.card α := rfl
      _ = (Nat.card α - 1) + 1 := (Nat.succ_pred_eq_of_pos hposα).symm
      _ = Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } + 1 := by
        rw [← hcardNe]
      _ = 1 + Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } := by
        omega
  have hcardCompl' :
      Nat.card { g : G // g ∉ H.frobeniusNonconjugateSet } =
        Nat.card G - Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } := by
    -- Counting the complement of `N` inside `G` rewrites the target cardinality as a subtraction.
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_compl (fun g : G ↦ g ∈ H.frobeniusNonconjugateSet))
  have hcardN :
      Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } =
        Nat.card G - (1 + Nat.card { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }) := by
    omega
  have hmain : Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } = H.index - 1 := by
    have hsplit : Nat.card H = (Nat.card H - 1) + 1 :=
      (Nat.succ_pred_eq_of_pos Nat.card_pos).symm
    -- Substitute the complement count and collapse the arithmetic using `|G| = [G : H] |H|`.
    calc
      Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } =
          H.index * Nat.card H - (1 + H.index * (Nat.card H - 1)) := by
            rw [hcardN, hcardC, ← H.index_mul_card]
      _ = H.index * ((Nat.card H - 1) + 1) - (1 + H.index * (Nat.card H - 1)) := by
        nth_rewrite 1 [hsplit]
        rfl
      _ = H.index * (Nat.card H - 1) + H.index - (1 + H.index * (Nat.card H - 1)) := by
        rw [mul_add, mul_one]
      _ = H.index - 1 := by
        omega
  have hindex : Nat.card G / Nat.card H = H.index := by
    -- The textbook quotient `|G| / |H|` is exactly the subgroup index.
    calc
      Nat.card G / Nat.card H = (H.index * Nat.card H) / Nat.card H := by
        rw [← H.index_mul_card]
      _ = H.index := by
        simpa [Nat.mul_comm] using (Nat.mul_div_right H.index Nat.card_pos)
  rw [hindex]
  exact hmain

end

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

local instance (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

open CategoryTheory

/-- Helper for Exercise 7-7.2-5: the auxiliary function `Ind_H^G(1) - 1` is a class function. -/
private theorem frobeniusPsi_mem_classFunctionSubspace (H : Subgroup G) :
    Ind[H](fun _ : H ↦ (1 : ℂ)) - 1 ∈ classFunctionSubspace G := by
  rw [mem_classFunctionSubspace_iff]
  refine ⟨fun {x y} hxy ↦ ?_⟩
  have hInd : IsClassFunction (Ind[H](fun _ : H ↦ (1 : ℂ))) := inferInstance
  have hxy' : IsConj x y := (ConjClasses.mk_eq_mk_iff_isConj).1 hxy
  simp [hInd.eq_of_isConj hxy']

/-- The auxiliary class function `ψ = Ind_H^G(1) - 1` attached to a subgroup `H ≤ G`. -/
def frobeniusPsi (H : Subgroup G) : classFunctionSubspace G :=
  ⟨Ind[H](fun _ : H ↦ (1 : ℂ)) - 1, frobeniusPsi_mem_classFunctionSubspace H⟩

@[simp] theorem frobeniusPsi_apply (H : Subgroup G) (g : G) :
    (H.frobeniusPsi : G → ℂ) g = Ind[H](fun _ : H ↦ (1 : ℂ)) g - 1 :=
  rfl

/-- The canonical Frobenius extension map on subgroup class functions. -/
def frobeniusExtension (H : Subgroup G) :
    classFunctionSubspace H →ₗ[ℂ] classFunctionSubspace G :=
  (H.classFunctionInduction.comp (classFunctionSubspace H).subtype) -
    (((LinearMap.proj (1 : H) : (H → ℂ) →ₗ[ℂ] ℂ).comp
      (classFunctionSubspace H).subtype).smulRight
      (H.frobeniusPsi))

/-- Helper for Exercise 7-7.2-5: evaluating the induced class function at the identity multiplies
the original value at `1` by the subgroup index. -/
theorem inducedClassFunction_one_eq_index_mul_value
    (H : Subgroup G) (χ : H → ℂ) :
    Ind[H](χ) 1 = (H.index : ℂ) * χ 1 := by
  classical
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  have h1H : (1 : G) ∈ H := by
    simp
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : (Nat.card G : ℂ) = (Nat.card H : ℂ) * H.index := by
    exact_mod_cast H.card_mul_index.symm
  have hχ1 : χ ⟨1, h1H⟩ = χ 1 := rfl
  have hsum0 : ∑ s : G, χ 1 = (Nat.card G : ℂ) * χ 1 := by
    simp [Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hsum :
      ∑ s : G,
        (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) =
          (Nat.card G : ℂ) * χ 1 := by
    -- Every summand at `g = 1` is the same value `χ 1`.
    have hterm :
        ∀ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) = χ 1 := by
      intro s
      have hs : s⁻¹ * (1 : G) * s ∈ H := by
        simpa using h1H
      simp [hs, hχ1]
    calc
      ∑ s : G,
          (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0)
          = ∑ s : G, χ 1 := by
              simpa using
                (Fintype.sum_congr
                  (f := fun s : G ↦
                    if hs : s⁻¹ * (1 : G) * s ∈ H then
                      χ ⟨s⁻¹ * (1 : G) * s, hs⟩
                    else 0)
                  (g := fun _ : G ↦ χ 1)
                  hterm)
      _ = (Nat.card G : ℂ) * χ 1 := hsum0
  -- Now simplify the normalized induction formula using `|G| = |H| * [G : H]`.
  calc
    Ind[H](χ) 1
        = ((Nat.card H : ℂ)⁻¹) *
            ∑ s : G,
              (if hs : s⁻¹ * (1 : G) * s ∈ H then χ ⟨s⁻¹ * (1 : G) * s, hs⟩ else 0) := by
            simp [Subgroup.inducedClassFunction]
    _ = ((Nat.card H : ℂ)⁻¹) * ((Nat.card G : ℂ) * χ 1) := by
      rw [hsum]
    _ = ((Nat.card H : ℂ)⁻¹) * (((Nat.card H : ℂ) * H.index) * χ 1) := by
      rw [hcard]
    _ = (H.index : ℂ) * χ 1 := by
      field_simp [hH]

/-- Helper for Exercise 7-7.2-5: for a nonidentity element of a Frobenius subgroup, the induced
class function has exactly the subgroup value coming from the trivial left coset. -/
theorem inducedClassFunction_apply_of_frobenius_mem
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    {χ : H → ℂ} (hχ : IsClassFunction χ) {h : H} (hh : h ≠ 1) :
    Ind[H](χ) h = χ h := by
  classical
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  let _ : NeZero (Nat.card H : ℂ) := by
    refine ⟨?_⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  obtain ⟨S, hS, h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  have h1H : (1 : G) ∈ H := by
    simp
  have h1R : (1 : G) ∈ R := by
    simpa [R] using h1S
  -- Route correction: instead of repeatedly unfolding the full induction sum, reduce to one
  -- left transversal and show the Frobenius condition leaves only the representative `1`.
  rw [Subgroup.induced_class_function_eq_sum_over_left_transversal
    (H := H) (ψ := χ) hχ (R := R) (hR := hR) (x := (h : G))]
  have hsingle :
      ∑ r ∈ R,
        (if hur : r⁻¹ * (h : G) * r ∈ H then χ ⟨r⁻¹ * (h : G) * r, hur⟩ else (0 : ℂ)) =
          (if hur : (1 : G)⁻¹ * (h : G) * 1 ∈ H then
            χ ⟨(1 : G)⁻¹ * (h : G) * 1, hur⟩
          else (0 : ℂ)) := by
    refine Finset.sum_eq_single_of_mem
      (s := R)
      (f := fun r ↦
        if hur : r⁻¹ * (h : G) * r ∈ H then
          χ ⟨r⁻¹ * (h : G) * r, hur⟩
        else (0 : ℂ))
      1 h1R ?_
    intro r hrR hrne1
    by_cases hur : r⁻¹ * (h : G) * r ∈ H
    · -- Any contributing representative must lie in `H`, hence it must be the chosen
      -- representative `1` for the trivial left coset.
      have hrinv : r⁻¹ ∈ H := by
        simpa using
          H.frobenius_fixed_coset_uniqueness hF (g := (h : G)) (r₁ := 1) (r₂ := r)
            (by simpa using hh) (by simpa using h.property) hur
      have hrH : r ∈ H := by
        simpa using H.inv_mem hrinv
      have hfstR : (hR.equiv r).1 = ⟨r, hrR⟩ :=
        hR.equiv_fst_eq_self_of_mem_of_one_mem h1H hrR
      have hfstH : (hR.equiv r).1 = ⟨1, h1R⟩ :=
        hR.equiv_fst_eq_one_of_mem_of_one_mem h1R hrH
      have hrEq : r = 1 := congrArg Subtype.val (hfstR.symm.trans hfstH)
      exact (hrne1 hrEq).elim
    · simp [hur]
  -- The surviving term is the trivial representative, so the conjugate is just `h`.
  simpa using hsingle

/-- Helper for Exercise 7-7.2-5: an element not conjugate to any element of `H` contributes no
term to the induced class function. -/
theorem inducedClassFunction_apply_eq_zero_of_mem_frobeniusNonconjugateSet
    (H : Subgroup G) {χ : H → ℂ} {n : G}
    (hn : n ∈ H.frobeniusNonconjugateSet) :
    Ind[H](χ) n = 0 := by
  classical
  let _ : DecidablePred fun x : G ↦ x ∈ H := Classical.decPred _
  -- Every defining summand is zero because any successful membership test would exhibit a
  -- conjugate of `n` lying in `H`.
  change ((Nat.card H : ℂ)⁻¹) *
      (∑ s : G, if hs : s⁻¹ * n * s ∈ H then χ ⟨s⁻¹ * n * s, hs⟩ else 0) = (0 : ℂ)
  have hsum :
      (∑ s : G, if hs : s⁻¹ * n * s ∈ H then χ ⟨s⁻¹ * n * s, hs⟩ else 0) = (0 : ℂ) := by
    refine Finset.sum_eq_zero ?_
    intro s
    by_cases hs : s⁻¹ * n * s ∈ H
    · exfalso
      exact hn ⟨s⁻¹ * n * s, hs⟩ (isConj_iff.2 ⟨s⁻¹, by group⟩)
    · simp [hs]
  rw [hsum, mul_zero]

/-- Exercise 7-7.2-5 (2): source part (b). The canonical Frobenius extension restricts to the
original class function on the subgroup `H`. -/
-- Proof sketch: evaluate the explicit formula for `H.frobeniusExtension χ` on an element of `H`,
-- use the Frobenius-subgroup condition to simplify the auxiliary term `ψ`, and then unfold the
-- induced-function definition.
theorem classFunctionRestriction_frobeniusExtension
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (χ : classFunctionSubspace H) :
    H.classFunctionRestriction (H.frobeniusExtension χ) = χ := by
  ext h
  by_cases hh : h = 1
  · -- At the identity, both induced terms are controlled by the index formula.
    subst hh
    change Ind[H]((χ : H → ℂ)) 1 -
        (χ : H → ℂ) 1 * (H.frobeniusPsi : G → ℂ) 1 =
      (χ : H → ℂ) 1
    rw [frobeniusPsi_apply, inducedClassFunction_one_eq_index_mul_value,
      inducedClassFunction_one_eq_index_mul_value (H := H) (χ := fun _ : H ↦ (1 : ℂ))]
    simp
    ring
  · have htriv : IsClassFunction (fun _ : H ↦ (1 : ℂ)) := by
      refine ⟨?_⟩
      intro x y hxy
      simp
    -- Away from `1`, the Frobenius condition collapses both induced terms to their unique
    -- contribution from the trivial coset.
    change Ind[H]((χ : H → ℂ)) h -
        (χ : H → ℂ) 1 * (H.frobeniusPsi : G → ℂ) h =
      (χ : H → ℂ) h
    rw [frobeniusPsi_apply]
    rw [inducedClassFunction_apply_of_frobenius_mem H hF
      ((mem_classFunctionSubspace_iff _).1 χ.2) hh,
      inducedClassFunction_apply_of_frobenius_mem H hF htriv hh]
    ring

/-- Exercise 7-7.2-5 (3): source part (b). The canonical Frobenius extension takes the value
`χ(1)` on the set `N` of elements not conjugate to any element of `H`. -/
-- Proof sketch: for `n ∈ N`, every conjugacy test appearing in the induced-function formula
-- fails, so the induced term vanishes and only the constant term `χ(1)` remains.
theorem frobeniusExtension_eqOn_frobeniusNonconjugateSet
    (H : Subgroup G) (χ : classFunctionSubspace H) :
    Set.EqOn (H.frobeniusExtension χ : G → ℂ) (fun _ ↦ (χ : H → ℂ) 1)
      H.frobeniusNonconjugateSet := by
  intro n hn
  -- On `N`, both induced terms vanish, so only the constant correction term remains.
  change Ind[H]((χ : H → ℂ)) n -
      (χ : H → ℂ) 1 * (H.frobeniusPsi : G → ℂ) n =
    (χ : H → ℂ) 1
  rw [frobeniusPsi_apply]
  rw [inducedClassFunction_apply_eq_zero_of_mem_frobeniusNonconjugateSet H hn,
    inducedClassFunction_apply_eq_zero_of_mem_frobeniusNonconjugateSet H
      (χ := fun _ : H ↦ (1 : ℂ)) hn]
  simp

/-- Exercise 7-7.2-5 (4): source part (b). A class function on `G` whose restriction to `H`
equals `χ` and whose value on `N` is constantly `χ(1)` is uniquely determined. -/
-- Proof sketch: every element of `G` is either in `N` or conjugate to an element of `H`, so the
-- two stated conditions determine the value of a class function on each conjugacy class.
theorem eq_frobeniusExtension_of_restriction_and_eqOn_frobeniusNonconjugateSet
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (χ : classFunctionSubspace H)
    {φ : classFunctionSubspace G} (hφ_restrict : H.classFunctionRestriction φ = χ)
    (hφ_nonconjugate : Set.EqOn (φ : G → ℂ) (fun _ ↦ (χ : H → ℂ) 1)
      H.frobeniusNonconjugateSet) :
    φ = H.frobeniusExtension χ := by
  ext g
  by_cases hgN : g ∈ H.frobeniusNonconjugateSet
  · -- On `N`, both functions take the prescribed constant value `χ(1)`.
    exact (hφ_nonconjugate hgN).trans
      (frobeniusExtension_eqOn_frobeniusNonconjugateSet H χ hgN).symm
  · rw [frobeniusNonconjugateSet, Set.mem_setOf_eq, not_forall] at hgN
    rcases hgN with ⟨h, hh⟩
    have hgconj : IsConj g h := by
      exact Classical.not_not.mp hh
    have hφ_class : IsClassFunction (φ : G → ℂ) :=
      (mem_classFunctionSubspace_iff _).1 φ.2
    have hExt_class : IsClassFunction (H.frobeniusExtension χ : G → ℂ) :=
      (mem_classFunctionSubspace_iff _).1 (H.frobeniusExtension χ).2
    have hφh : (φ : G → ℂ) h = (χ : H → ℂ) h := by
      have := congrArg (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) h) hφ_restrict
      simpa [classFunctionRestriction_apply] using this
    have hExth : (H.frobeniusExtension χ : G → ℂ) h = (χ : H → ℂ) h := by
      have hrestrict := congrArg
        (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) h)
        (classFunctionRestriction_frobeniusExtension H hF χ)
      simpa [classFunctionRestriction_apply] using hrestrict
    -- Outside `N`, the value is determined by the conjugacy class of some subgroup element.
    calc
      (φ : G → ℂ) g = (φ : G → ℂ) h := hφ_class.eq_of_isConj hgconj
      _ = (χ : H → ℂ) h := hφh
      _ = (H.frobeniusExtension χ : G → ℂ) h := hExth.symm
      _ = (H.frobeniusExtension χ : G → ℂ) g := hExt_class.eq_of_isConj hgconj.symm

/-- Exercise 7-7.2-5 (5): source part (c). The canonical Frobenius extension satisfies
`\tilde f = Ind_H^G(f) - f(1) ψ`, where `ψ = Ind_H^G(1) - 1`. -/
-- Proof sketch: this is exactly the definition of `H.frobeniusExtension χ` together with the
-- definition of `H.frobeniusPsi`.
theorem frobeniusExtension_eq_inducedClassFunction_sub_frobeniusPsi
    (H : Subgroup G) (χ : classFunctionSubspace H) :
    (H.frobeniusExtension χ : G → ℂ) =
      Ind[H]((χ : H → ℂ)) - ((χ : H → ℂ) 1) • (H.frobeniusPsi : G → ℂ) :=
  rfl

/-- Helper for Exercise 7-7.2-5: the Frobenius nonconjugate set is stable under inversion. -/
theorem inv_mem_frobeniusNonconjugateSet_iff
    (H : Subgroup G) {g : G} :
    g⁻¹ ∈ H.frobeniusNonconjugateSet ↔ g ∈ H.frobeniusNonconjugateSet := by
  constructor
  · intro hg h hh
    -- Inverting a conjugacy relation keeps us inside the subgroup, contradicting membership in
    -- the nonconjugate set for `g⁻¹`.
    have hhinv : IsConj g⁻¹ h⁻¹ := by
      rw [isConj_iff] at hh ⊢
      rcases hh with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        c * g⁻¹ * c⁻¹ = (c * g * c⁻¹)⁻¹ := by
          simpa [mul_assoc] using (conj_inv (a := g) (b := c)).symm
        _ = (h : G)⁻¹ := by rw [hc]
    exact hg ⟨h⁻¹, H.inv_mem h.property⟩ hhinv
  · intro hg h hh
    -- The same inversion argument runs in the reverse direction because inversion is involutive.
    have hhinv : IsConj g h⁻¹ := by
      rw [isConj_iff] at hh ⊢
      rcases hh with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        c * g * c⁻¹ = (c * g⁻¹ * c⁻¹)⁻¹ := by
          simpa [mul_assoc] using (conj_inv (a := g⁻¹) (b := c)).symm
        _ = (h : G)⁻¹ := by rw [hc]
    exact hg ⟨h⁻¹, H.inv_mem h.property⟩ hhinv

/-- Helper for Exercise 7-7.2-5: evaluating the Frobenius extension on an element conjugate into
`H` recovers the original subgroup class-function value. -/
theorem frobeniusExtension_apply_of_isConj
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (χ : classFunctionSubspace H)
    {g : G} {h : H} (hg : IsConj g h) :
    (H.frobeniusExtension χ : G → ℂ) g = (χ : H → ℂ) h := by
  have hExt_class : IsClassFunction (H.frobeniusExtension χ : G → ℂ) :=
    (mem_classFunctionSubspace_iff _).1 (H.frobeniusExtension χ).2
  have hExth : (H.frobeniusExtension χ : G → ℂ) h = (χ : H → ℂ) h := by
    -- Restriction back to `H` identifies the extension with the original class function.
    have hrestrict := congrArg
      (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) h)
      (H.classFunctionRestriction_frobeniusExtension hF χ)
    simpa [classFunctionRestriction_apply] using hrestrict
  -- Class-function invariance transports the subgroup value along the conjugacy relation.
  calc
    (H.frobeniusExtension χ : G → ℂ) g = (H.frobeniusExtension χ : G → ℂ) h :=
      hExt_class.eq_of_isConj hg
    _ = (χ : H → ℂ) h := hExth

/-- Helper for Exercise 7-7.2-5: on a conjugacy block coming from a nonidentity subgroup element,
the Frobenius-extension product `\tildeχ₁(g) \tildeχ₂(g⁻¹)` reduces to the subgroup product
`χ₁(h) χ₂(h⁻¹)`. -/
theorem frobeniusExtension_mul_inv_apply_of_isConj
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (χ₁ χ₂ : classFunctionSubspace H)
    {g : G} {h : H} (hg : IsConj g h) :
    (H.frobeniusExtension χ₁ : G → ℂ) g *
        (H.frobeniusExtension χ₂ : G → ℂ) g⁻¹ =
      (χ₁ : H → ℂ) h * (χ₂ : H → ℂ) h⁻¹ := by
  have hginv : IsConj g⁻¹ h⁻¹ := by
    rw [isConj_iff] at hg ⊢
    rcases hg with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      c * g⁻¹ * c⁻¹ = (c * g * c⁻¹)⁻¹ := by
        simpa [mul_assoc] using (conj_inv (a := g) (b := c)).symm
      _ = (h : G)⁻¹ := by rw [hc]
  -- Evaluate both Frobenius extensions on the conjugate pair `g` and `g⁻¹`.
  rw [H.frobeniusExtension_apply_of_isConj hF χ₁ hg,
    H.frobeniusExtension_apply_of_isConj hF χ₂ (h := h⁻¹) hginv]

/-- Helper for Exercise 7-7.2-5: on the Frobenius nonconjugate set `N`, the product
`\tildeχ₁(n) \tildeχ₂(n⁻¹)` is the constant subgroup value `χ₁(1) χ₂(1)`. -/
theorem frobeniusExtension_mul_inv_apply_of_mem_frobeniusNonconjugateSet
    (H : Subgroup G) (χ₁ χ₂ : classFunctionSubspace H)
    {n : G} (hn : n ∈ H.frobeniusNonconjugateSet) :
    (H.frobeniusExtension χ₁ : G → ℂ) n *
        (H.frobeniusExtension χ₂ : G → ℂ) n⁻¹ =
      (χ₁ : H → ℂ) 1 * (χ₂ : H → ℂ) 1 := by
  have hn_inv : n⁻¹ ∈ H.frobeniusNonconjugateSet :=
    (H.inv_mem_frobeniusNonconjugateSet_iff (g := n)).2 hn
  -- Both extension values are constant on `N`, including at the inverse by inversion stability.
  rw [H.frobeniusExtension_eqOn_frobeniusNonconjugateSet χ₁ hn,
    H.frobeniusExtension_eqOn_frobeniusNonconjugateSet χ₂ hn_inv]

-- Exercise 7-7.2-5 (6): source part (d). The Frobenius extension preserves the class-function
-- pairing from `H` to `G`.
-- Proof sketch: expand both sides using the formula from part (c), use Frobenius reciprocity for
-- induced characters together with the explicit pairing identities, and simplify the cross-terms
-- with the character `ψ`.
/-- Helper for Exercise 7-7.2-5: the unnormalized Frobenius-extension sum over `G` is the subgroup
sum scaled by the index `[G : H]`. -/
theorem frobeniusExtension_sum_mul_inv_eq_index_subgroup_sum
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (χ₁ χ₂ : classFunctionSubspace H) :
    ∑ g : G, (H.frobeniusExtension χ₁ : G → ℂ) g *
        (H.frobeniusExtension χ₂ : G → ℂ) g⁻¹ =
      (H.index : ℂ) * ∑ h : H, (χ₁ : H → ℂ) h * (χ₂ : H → ℂ) h⁻¹ := by
  classical
  -- Route correction: the remaining structural step is the partition
  -- `G = {1} ⊔ H.frobeniusNonconjugateSet ⊔ {g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet}`,
  -- with the nonidentity conjugate block reindexed through the fixed transversal equivalence.
  obtain ⟨S, hS, _h1S⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  let F : G → ℂ := fun g ↦
    (H.frobeniusExtension χ₁ : G → ℂ) g *
      (H.frobeniusExtension χ₂ : G → ℂ) g⁻¹
  let subgroupTerm : H → ℂ := fun h ↦ (χ₁ : H → ℂ) h * (χ₂ : H → ℂ) h⁻¹
  have h1not : (1 : G) ∉ H.frobeniusNonconjugateSet := by
    intro h1N
    exact h1N ⟨1, by simp⟩ (isConj_iff.2 ⟨1, by simp⟩)
  let oneC : { g : G // g ∉ H.frobeniusNonconjugateSet } := ⟨1, h1not⟩
  let e₁ :
      { x : { g : G // g ∉ H.frobeniusNonconjugateSet } // x ≠ oneC } ≃
        { x : { g : G // g ∉ H.frobeniusNonconjugateSet } // x.1 ≠ 1 } :=
    Equiv.subtypeEquivRight fun x ↦ by
      constructor
      · intro hx hx1
        apply hx
        apply Subtype.ext
        simpa [oneC] using hx1
      · intro hx hx1
        apply hx
        simpa [oneC] using congrArg Subtype.val hx1
  let e₂ :
      { x : { g : G // g ∉ H.frobeniusNonconjugateSet } // x.1 ≠ 1 } ≃
        { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun g : G ↦ g ∉ H.frobeniusNonconjugateSet)
      (fun g : G ↦ g ≠ 1)).trans
      (Equiv.subtypeEquivRight fun g ↦ by simp [and_comm])
  let e := H.frobenius_nonidentity_conjugate_equiv_transversal_prod hF R hR
  have hsplitN :
      ∑ g : G, F g =
        (∑ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n) +
          ∑ c : { g : G // g ∉ H.frobeniusNonconjugateSet }, F c := by
    -- First split the full-group sum into the `N` block and its complement.
    simpa [F] using
      (Fintype.sum_subtype_add_sum_subtype
        (fun g : G ↦ g ∈ H.frobeniusNonconjugateSet) F).symm
  have hsplitC :
      ∑ c : { g : G // g ∉ H.frobeniusNonconjugateSet }, F c =
        F 1 + ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b := by
    -- Inside the complement of `N`, isolate the identity and identify the rest with the desired
    -- nonidentity conjugate block.
    rw [Fintype.sum_eq_add_sum_subtype_ne (f := fun c : { g : G // g ∉ H.frobeniusNonconjugateSet } ↦
      F c) oneC]
    have hsumSubtype :
        ∑ x : { x : { g : G // g ∉ H.frobeniusNonconjugateSet } // x ≠ oneC }, F x.1 =
          ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b := by
      exact Fintype.sum_equiv (e₁.trans e₂) (fun x ↦ F x.1) (fun b ↦ F b) fun x ↦ by
        simp [e₁, e₂]
    simpa [oneC] using congrArg (F oneC + ·) hsumSubtype
  have hone :
      F 1 = subgroupTerm 1 := by
    -- Restricting the Frobenius extension back to `H` identifies the identity contribution.
    have hχ₁ :
        (H.frobeniusExtension χ₁ : G → ℂ) 1 = (χ₁ : H → ℂ) 1 := by
      simpa using
        H.frobeniusExtension_apply_of_isConj hF χ₁
          (g := 1) (h := (1 : H)) (isConj_iff.2 ⟨1, by simp⟩)
    have hχ₂ :
        (H.frobeniusExtension χ₂ : G → ℂ) 1 = (χ₂ : H → ℂ) 1 := by
      simpa using
        H.frobeniusExtension_apply_of_isConj hF χ₂
          (g := 1) (h := (1 : H)) (isConj_iff.2 ⟨1, by simp⟩)
    simp [F, subgroupTerm, hχ₁, hχ₂]
  have hsumN :
      ∑ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n =
        (Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } : ℂ) * subgroupTerm 1 := by
    -- The Frobenius extension is constant on `N`, so the whole `N`-block is a cardinality factor.
    have hconst :
        ∀ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n = subgroupTerm 1 := by
      intro n
      simpa [F, subgroupTerm] using
        H.frobeniusExtension_mul_inv_apply_of_mem_frobeniusNonconjugateSet χ₁ χ₂ n.2
    calc
      ∑ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n =
          ∑ _n : { g : G // g ∈ H.frobeniusNonconjugateSet }, subgroupTerm 1 := by
            apply Finset.sum_congr rfl
            intro n _
            exact hconst n
      _ = (Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } : ℂ) * subgroupTerm 1 := by
            simp [Nat.card_eq_fintype_card, nsmul_eq_mul, subgroupTerm]
  have hsumNonid :
      ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b =
        (H.index : ℂ) *
          ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
    -- Reindex the nonidentity conjugate block by the explicit transversal/subgroup equivalence.
    have hsumProd :
        ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b =
          ∑ p : ↥(R : Set G) × { h : H // h ≠ 1 }, subgroupTerm p.2 := by
      symm
      exact Fintype.sum_equiv e.symm
        (fun p : ↥(R : Set G) × { h : H // h ≠ 1 } ↦ subgroupTerm p.2)
        (fun b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet } ↦ F b)
        (fun p ↦ by
          have hconj :
              IsConj (((p.1 : G) * (p.2.1 : H) * (p.1 : G)⁻¹) : G) p.2.1 := by
            exact isConj_iff.2 ⟨(p.1 : G)⁻¹, by group⟩
          simpa [e, F, subgroupTerm,
            frobenius_nonidentity_conjugate_equiv_transversal_prod] using
            (H.frobeniusExtension_mul_inv_apply_of_isConj hF χ₁ χ₂ (g := (p.1 : G) *
              (p.2.1 : H) * (p.1 : G)⁻¹) (h := p.2.1) hconj).symm)
    calc
      ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b =
          ∑ p : ↥(R : Set G) × { h : H // h ≠ 1 }, subgroupTerm p.2 := hsumProd
      _ = ∑ r : ↥(R : Set G), ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
            rw [Fintype.sum_prod_type]
      _ = (Nat.card ↥(R : Set G) : ℂ) *
            ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
            simp [Nat.card_eq_fintype_card, nsmul_eq_mul, subgroupTerm]
      _ = (H.index : ℂ) * ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
            rw [H.card_transversal_eq_index_of_isComplement R hR]
  have hcardN_nat :
      Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } = H.index - 1 := by
    have hindex :
        Nat.card G / Nat.card H = H.index := by
      calc
        Nat.card G / Nat.card H = (H.index * Nat.card H) / Nat.card H := by
          rw [← H.index_mul_card]
        _ = H.index := by
          simpa [Nat.mul_comm] using (Nat.mul_div_right H.index Nat.card_pos)
    calc
      Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } =
          Nat.card G / Nat.card H - 1 := H.frobeniusNonconjugateSet_card hF
      _ = H.index - 1 := by rw [hindex]
  have hcardN_cast :
      ((Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } : ℂ) + 1) = H.index := by
    have hcardN_plus :
        Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 = H.index := by
      calc
        Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 = (H.index - 1) + 1 := by
          rw [hcardN_nat]
        _ = H.index := Nat.sub_add_cancel (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
    exact_mod_cast hcardN_plus
  have hsplitH :
      ∑ h : H, subgroupTerm h = subgroupTerm 1 +
        ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
    -- Split the subgroup sum into the identity and the nonidentity subgroup elements.
    simpa [subgroupTerm] using
      (Fintype.sum_eq_add_sum_subtype_ne (f := subgroupTerm) (1 : H))
  calc
    ∑ g : G, F g =
        (∑ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n) +
          ∑ c : { g : G // g ∉ H.frobeniusNonconjugateSet }, F c := hsplitN
    _ = (∑ n : { g : G // g ∈ H.frobeniusNonconjugateSet }, F n) +
          (F 1 + ∑ b : { g : G // g ≠ 1 ∧ g ∉ H.frobeniusNonconjugateSet }, F b) := by
            rw [hsplitC]
    _ = ((Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } : ℂ) * subgroupTerm 1) +
          (subgroupTerm 1 + (H.index : ℂ) *
            ∑ h : { h : H // h ≠ 1 }, subgroupTerm h) := by
            rw [hsumN, hone, hsumNonid]
    _ = (((Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } : ℂ) + 1) *
          subgroupTerm 1) +
          (H.index : ℂ) * ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
            ring
    _ = (H.index : ℂ) * subgroupTerm 1 +
          (H.index : ℂ) * ∑ h : { h : H // h ≠ 1 }, subgroupTerm h := by
            rw [hcardN_cast]
    _ = (H.index : ℂ) *
          (subgroupTerm 1 + ∑ h : { h : H // h ≠ 1 }, subgroupTerm h) := by
            ring
    _ = (H.index : ℂ) * ∑ h : H, subgroupTerm h := by
            rw [hsplitH]

/-- Exercise 7-7.2-5 (6): source part (d). The Frobenius extension preserves the class-function
pairing from `H` to `G`. -/
theorem groupFunctionPairing_frobeniusExtension_eq
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (χ₁ χ₂ : classFunctionSubspace H) :
    ⟪(χ₁ : H → ℂ), (χ₂ : H → ℂ)⟫ =
      ⟪(H.frobeniusExtension χ₁ : G → ℂ), (H.frobeniusExtension χ₂ : G → ℂ)⟫ := by
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hindex : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast H.index_ne_zero_of_finite
  have hcardG : (Nat.card G : ℂ) = (Nat.card H : ℂ) * (H.index : ℂ) := by
    exact_mod_cast H.card_mul_index.symm
  -- Normalize both pairings, then insert the raw Frobenius-extension sum identity.
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  rw [H.frobeniusExtension_sum_mul_inv_eq_index_subgroup_sum hF χ₁ χ₂]
  -- The remaining scalar equality is exactly `|G| = |H| * [G : H]`.
  rw [hcardG]
  field_simp [hcardH, hindex]

/-- Helper for Exercise 7-7.2-5: the character of a finite-dimensional subgroup representation is
a class function. -/
private theorem fdRepCharacterClassFunction_mem (H : Subgroup G) (θ : FDRep ℂ H) :
    θ.character ∈ classFunctionSubspace H := by
  rw [mem_classFunctionSubspace_iff]
  refine ⟨?_⟩
  intro x y hxy
  rcases isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.mp hxy) with ⟨a, rfl⟩
  exact (θ.char_conj x a).symm

private abbrev fdRepCharacterClassFunction (H : Subgroup G) (θ : FDRep ℂ H) :
    classFunctionSubspace H :=
  ⟨θ.character, fdRepCharacterClassFunction_mem H θ⟩

/-- Helper for Exercise 7-7.2-5: a simple finite-dimensional representation of `H` has
irreducible underlying representation. -/
theorem fdRep_underlying_isIrreducible_of_simple
    (H : Subgroup G) (θ : FDRep ℂ H) [CategoryTheory.Simple θ] :
    Representation.IsIrreducible θ.ρ := by
  rw [Representation.IsIrreducible]
  have hnontrivialθ : Nontrivial θ := by
    by_contra hθ
    letI := not_nontrivial_iff_subsingleton.mp hθ
    have hzero : (𝟙 θ : θ ⟶ θ) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero θ hzero
  letI : Nontrivial θ := hnontrivialθ
  letI : Nontrivial (Subrepresentation θ.ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine IsSimpleOrder.of_forall_eq_top fun σ hσ ↦ ?_
  let ισ : FDRep.of σ.toRepresentation ⟶ θ :=
    { hom := FGModuleCat.ofHom σ.toSubmodule.subtype
      comm g := by
        ext x
        rfl }
  have hισ_ne : ισ ≠ 0 := by
    intro hzero
    have hσbot : σ = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro w hw
      have hw0 : ((⟨w, hw⟩ : σ.toSubmodule) : θ) = 0 := by
        have : ισ ⟨w, hw⟩ = 0 := by
          rw [hzero]
          rfl
        simpa [ισ] using this
      simpa using hw0
    exact hσ hσbot
  have hισ_mono : Mono ισ := by
    exact ConcreteCategory.mono_of_injective _ fun x y h ↦ by
      change (x : θ) = (y : θ) at h
      exact Subtype.ext h
  haveI : IsIso ισ := CategoryTheory.isIso_of_mono_of_nonzero hισ_ne
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm le_top
  intro w hw
  let e : FDRep.of σ.toRepresentation ≅ θ := asIso ισ
  let x : σ.toSubmodule := e.inv.hom w
  have hx : ((x : σ.toSubmodule) : θ) = w := by
    have hw' :
        ConcreteCategory.hom e.hom.hom (ConcreteCategory.hom e.inv.hom w) = w := by
      exact Iso.inv_hom_id_apply e w
    simpa [x, e, ισ] using hw'
  exact hx ▸ x.property

/-- Exercise 7-7.2-5 (7): source part (e). If `f` is the character of an irreducible
representation of `H`, then the self-pairing of its Frobenius extension is `1`. -/
-- Proof sketch: apply part (d) with `f₁ = f₂ = θ.character`, and use the irreducible character
-- orthogonality relation on `H` to identify the left-hand side with `1`.
theorem self_groupFunctionPairing_frobeniusExtension_character_eq_one
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (θ : FDRep ℂ H) [CategoryTheory.Simple θ] :
    ⟪(H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ),
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ)⟫ =
      1 := by
  letI : Representation.IsIrreducible θ.ρ := H.fdRep_underlying_isIrreducible_of_simple θ
  -- Transfer the self-pairing from `H` to `G`, then use irreducible orthogonality on `H`.
  calc
    ⟪(H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ),
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ)⟫ =
        ⟪θ.character, θ.character⟫ := by
          symm
          exact H.groupFunctionPairing_frobeniusExtension_eq hF
            (fdRepCharacterClassFunction H θ)
            (fdRepCharacterClassFunction H θ)
    _ = 1 := by
      simpa [fdRepCharacterClassFunction] using
        (Representation.self_character_pairing_eq_one_iff_isIrreducible θ.ρ).2 inferInstance

/-- Exercise 7-7.2-5 (8): source part (e). For the character `f` of a finite-dimensional
representation of `H`, the value `\tilde f(1)` is a nonnegative integer. This is the intrinsic
Lean form of the textbook claim `\tilde f(1) ≥ 0` for a complex-valued character. -/
-- Proof sketch: evaluate the explicit formula from part (c) at `1`. The induced character at `1`
-- is the index `[G : H]` times `f(1)`, and `ψ(1) = [G : H] - 1`, so the two index terms cancel
-- and `\tilde f(1) = f(1)`. The remaining value is the degree of `θ`, hence a natural number.
theorem frobeniusExtension_character_one_eq_nat
    (H : Subgroup G) (θ : FDRep ℂ H) :
    ∃ n : ℕ,
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) :
          G → ℂ) 1 = n := by
  refine ⟨Module.finrank ℂ θ, ?_⟩
  -- Evaluate the explicit Frobenius-extension formula at `1` and cancel the index terms.
  rw [frobeniusExtension_eq_inducedClassFunction_sub_frobeniusPsi]
  change Ind[H](θ.character) 1 - θ.character 1 * (H.frobeniusPsi : G → ℂ) 1 =
    (Module.finrank ℂ θ : ℂ)
  rw [frobeniusPsi_apply]
  rw [inducedClassFunction_one_eq_index_mul_value,
    inducedClassFunction_one_eq_index_mul_value (H := H) (χ := fun _ : H ↦ (1 : ℂ)),
    FDRep.char_one]
  simp
  ring

-- Exercise 7-7.2-5 (9): source part (e). For the character `f` of a finite-dimensional
-- representation of `H`, its Frobenius extension is an integral linear combination of irreducible
-- characters of `G`. The safe owner route is to expand against a complete irreducible family from
-- Chapter `3`, avoiding the broken Chapter `12` character-ring import chain.
-- Proof sketch: first choose a complete pairwise nonisomorphic family of irreducibles on `G`.
-- Then expand the induced character and the auxiliary character `ψ = Ind_H^G(1) - 1` against that
-- family and subtract the corresponding integer coefficient vectors.
/-- Helper for Exercise 7-7.2-5: away from the identity, the regular character decomposed against a
complete irreducible family has vanishing value. -/
private theorem leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (s : G) :
    (Representation.leftRegular ℂ G).character s =
      ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character s := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (Representation.leftRegular ℂ G)),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
              ((σ j).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := Representation.leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv (σ j).toRepresentation (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let χσ : κ → ℂ := fun j ↦ ((σ j).toRepresentation).character s
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct irreducible classes cannot share a common summand of the regular representation.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hS_card (i : ι) : (S i).card = Module.finrank ℂ (π i) := by
    -- The multiplicity of `π i` in the regular representation equals its degree.
    have hπi_irreducible : Representation.IsIrreducible (π i).ρ := by
      letI : Simple (π i) := hπ_complete.isSimple i
      exact Representation.FDRep.isIrreducible_of_simple (π i)
    letI : Representation.IsIrreducible (π i).ρ := hπi_irreducible
    have hcard :
        Fintype.card
            { j // Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ)) } =
          (S i).card := by
      rw [show S i = Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))) by
            rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter
          (fun j ↦ Nonempty (Representation.Equiv ((σ j).toRepresentation) ((π i).ρ))))]
      · intro j
        simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using
        Representation.leftRegular_irreducible_multiplicity_eq_finrank
          σ hinternal hσ_irr (π i).ρ inferInstance
  have hS_sum (i : ι) :
      Finset.sum (S i) χσ = (Module.finrank ℂ (π i) : ℂ) * (π i).character s := by
    -- Inside one isomorphism class, every summand has the same character.
    calc
      Finset.sum (S i) χσ = Finset.sum (S i) (fun _j ↦ (π i).character s) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        simpa [χσ] using congrArg (fun χ : G → ℂ ↦ χ s) (Representation.char_iso e)
      _ = (S i).card * (π i).character s := by
        simp
      _ = (Module.finrank ℂ (π i) : ℂ) * (π i).character s := by
        simp [hS_card]
  have hcovered_raw :
      Finset.sum covered χσ = ∑ i : ι, Finset.sum (S i) χσ := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  have hcovered_univ : covered = Finset.univ := by
    -- Completeness identifies every irreducible regular summand with one class in `π`.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hτ_irreducible :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hσ_irr j
      letI :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hτ_irreducible
      obtain ⟨i, hi⟩ :=
        Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation
          (π := π) hπ_complete (W := (σ j).toSubmodule) (σ j).toRepresentation inferInstance
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      rcases hi with ⟨e⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
  have hsum_sigma :
      (Representation.leftRegular ℂ G).character s = ∑ j : κ, χσ j := by
    have hchar :
        (Representation.leftRegular ℂ G).character =
          ∑ j : κ, ((σ j).toRepresentation).character := by
      ext g
      simpa [Representation.character] using
        (LinearMap.trace_eq_sum_trace_restrict
          (R := ℂ) (M := MonoidAlgebra ℂ G) (N := fun j ↦ (σ j).toSubmodule) hinternal
          (f := (Representation.leftRegular ℂ G) g)
          (hf := fun j ↦ (σ j).apply_mem_toSubmodule g))
    simpa [χσ] using congrArg (fun χ : G → ℂ ↦ χ s) hchar
  calc
    (Representation.leftRegular ℂ G).character s = ∑ j : κ, χσ j := hsum_sigma
    _ = Finset.sum covered χσ := by
      simpa [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) χσ := hcovered_raw
    _ = ∑ i : ι, (Module.finrank ℂ (π i) : ℂ) * (π i).character s := by
      refine Finset.sum_congr rfl fun i _ ↦ hS_sum i

/-- Helper for Exercise 7-7.2-5: away from the identity, the regular character decomposed against a
complete irreducible family has vanishing value. -/
private theorem regular_character_vanishing_of_complete_irreducible_family_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    {s : G} (hs : s ≠ 1) :
    ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character s = 0 := by
  calc
    ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character s =
        (Representation.leftRegular ℂ G).character s := by
          symm
          exact
            leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family_local
              (π := π) hπ_pairwise hπ_complete s
    _ = 0 := Representation.leftRegular_character_eq_zero_of_ne_one hs

/-- Helper for Exercise 7-7.2-5: the character of an internal direct sum is the sum of the
characters of its stable summands. -/
private theorem character_eq_sum_of_internal_family_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ G V) (σ : κ → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i : κ, ((σ i).toRepresentation).character := by
  -- The trace of `ρ g` splits across the internal direct-sum decomposition.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Exercise 7-7.2-5: every finite-dimensional complex representation has character
equal to a finite nonnegative integral combination of a fixed complete irreducible family. -/
private theorem rep_character_eq_sum_irreducible_family_with_nat_coefficients_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (ρ : FDRep ℂ G) :
    ∃ m : ι → ℕ, ρ.character = ∑ i, (m i : ℂ) • (π i).character := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation ρ.ρ),
        iSupIndep (fun j ↦ (σ j).toSubmodule) ∧
          (⨆ j, (σ j).toSubmodule) = ⊤ ∧
          ∀ j,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
              ((σ j).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := ρ.ρ)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let S : ι → Finset κ :=
    fun i ↦ Finset.univ.filter fun j ↦
      Nonempty (Representation.Equiv (σ j).toRepresentation (π i).ρ)
  let covered : Finset κ := Finset.univ.biUnion S
  let m : ι → ℕ := fun i ↦ (S i).card
  have hS_disjoint : Pairwise fun i i' ↦ Disjoint (S i) (S i') := by
    -- Distinct complete-family classes cannot share one irreducible summand of `ρ`.
    intro i i' hii
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨e'⟩
    exact hπ_pairwise hii <| ⟨(e.symm.trans e').toFDRepIso⟩
  have hcovered_univ : covered = Finset.univ := by
    -- Completeness sends every irreducible summand to exactly one class in `π`.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hτ_irreducible :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hσ_irr j
      letI :
          Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ j).toSubmodule)
            ((σ j).toRepresentation) := hτ_irreducible
      obtain ⟨i, hi⟩ :=
        Representation.IsCompleteIrreducibleFamily.exists_iso_of_representation
          (π := π) hπ_complete (W := (σ j).toSubmodule) (σ j).toRepresentation inferInstance
      refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
      rcases hi with ⟨e⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
  have hcovered_raw (g : G) :
      Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) =
        ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) := by
    rw [show covered = Finset.univ.biUnion S from rfl]
    exact Finset.sum_biUnion fun i _ i' _ hii ↦ hS_disjoint hii
  refine ⟨m, ?_⟩
  -- Regroup the irreducible summands by their unique complete-family representative.
  ext g
  have hsum_sigma :
      ρ.character g = ∑ j : κ, ((σ j).toRepresentation).character g := by
    simpa using
      congrArg (fun χ : G → ℂ ↦ χ g)
        (character_eq_sum_of_internal_family_local (ρ := ρ.ρ) σ hinternal)
  have hS_sum (i : ι) :
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
        (m i : ℂ) * (π i).character g := by
    calc
      Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) =
          Finset.sum (S i) (fun _j ↦ (π i).character g) := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
            simpa using congrArg (fun χ : G → ℂ ↦ χ g) (Representation.char_iso e)
      _ = (S i).card * (π i).character g := by
            simp
      _ = (m i : ℂ) * (π i).character g := by
            simp [m]
  calc
    ρ.character g = ∑ j : κ, ((σ j).toRepresentation).character g := hsum_sigma
    _ = Finset.sum covered (fun j ↦ ((σ j).toRepresentation).character g) := by
          simpa [covered, hcovered_univ]
    _ = ∑ i : ι, Finset.sum (S i) (fun j ↦ ((σ j).toRepresentation).character g) :=
          hcovered_raw g
    _ = ∑ i : ι, (m i : ℂ) * (π i).character g := by
          refine Finset.sum_congr rfl fun i _ ↦ hS_sum i
    _ = (∑ i, (m i : ℂ) • (π i).character) g := by
          simp

/-- Helper for Exercise 7-7.2-5: the Frobenius extension of an irreducible subgroup character is
an explicit integer linear combination of the irreducible characters of `G`. -/
private theorem frobeniusExtension_character_eq_sum_irreducible_family_with_int_coefficients_local
    {ι : Type*} [Fintype ι]
    (H : Subgroup G) (θ : FDRep ℂ H)
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π) :
    ∃ c : ι → ℤ,
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ) =
        ∑ i, (c i : ℂ) • (π i).character := by
  letI : NeZero (Nat.card H : ℂ) := by
    refine ⟨?_⟩
    exact_mod_cast Nat.card_pos.ne'
  letI : FiniteDimensional ℂ (G →₀ ℂ) := by
    infer_instance
  letI : FiniteDimensional ℂ (TensorProduct ℂ (G →₀ ℂ) θ) := by
    infer_instance
  letI : FiniteDimensional ℂ (Representation.IndV H.subtype θ.ρ) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  let indθ : FDRep ℂ G := FDRep.of (Representation.ind H.subtype θ.ρ)
  letI : FiniteDimensional ℂ (TensorProduct ℂ (G →₀ ℂ) ℂ) := by
    infer_instance
  letI : FiniteDimensional ℂ (Representation.IndV H.subtype (Representation.trivial ℂ H ℂ)) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  let indOne : FDRep ℂ G := FDRep.of (Representation.ind H.subtype (Representation.trivial ℂ H ℂ))
  let oneG : FDRep ℂ G := FDRep.of (Representation.trivial ℂ G ℂ)
  obtain ⟨mθ, hmθ⟩ :=
    rep_character_eq_sum_irreducible_family_with_nat_coefficients_local
      (ι := ι) (π := π) hπ_pairwise hπ_complete indθ
  obtain ⟨mOne, hmOne⟩ :=
    rep_character_eq_sum_irreducible_family_with_nat_coefficients_local
      (ι := ι) (π := π) hπ_pairwise hπ_complete indOne
  obtain ⟨mTriv, hmTriv⟩ :=
    rep_character_eq_sum_irreducible_family_with_nat_coefficients_local
      (ι := ι) (π := π) hπ_pairwise hπ_complete oneG
  let n : ℕ := Module.finrank ℂ θ
  let c : ι → ℤ := fun i ↦
    (mθ i : ℤ) - (n : ℤ) * ((mOne i : ℤ) - (mTriv i : ℤ))
  refine ⟨c, ?_⟩
  -- Route correction: package the two induced representations inline and combine the resulting
  -- three complete-family expansions through the explicit Frobenius-extension formula from part (c).
  ext g
  have hindθ :
      Ind[H](θ.character) = indθ.character := by
    simpa [indθ] using
      (Subgroup.inducedClassFunction_eq_character_ind
        (H := H) (θ := θ.ρ))
  have hindOne :
      Ind[H](fun _ : H ↦ (1 : ℂ)) = indOne.character := by
    have htrivH :
        (Representation.trivial ℂ H ℂ).character = (fun _ : H ↦ (1 : ℂ)) := by
      ext h
      simp [Representation.character, Representation.trivial]
    rw [← htrivH]
    simpa [indOne] using
      (Subgroup.inducedClassFunction_eq_character_ind
        (H := H) (θ := Representation.trivial ℂ H ℂ))
  have htriv :
      oneG.character = (1 : G → ℂ) := by
    ext x
    change Representation.character (Representation.trivial ℂ G ℂ) x = 1
    simp [Representation.character, Representation.trivial]
  have hc_cast (i : ι) :
      (((c i : ℤ) : ℂ)) =
        (mθ i : ℂ) - (n : ℂ) * ((mOne i : ℂ) - (mTriv i : ℂ)) := by
    norm_num [c, n]
  have hcharOne : θ.character 1 = (n : ℂ) := by
    simpa [n] using (FDRep.char_one (ρ := θ))
  have hmθg :
      indθ.character g = ∑ i, (mθ i : ℂ) * (π i).character g := by
    simpa [Pi.smul_apply] using congrArg (fun f : G → ℂ ↦ f g) hmθ
  have hmOneg :
      indOne.character g = ∑ i, (mOne i : ℂ) * (π i).character g := by
    simpa [Pi.smul_apply] using congrArg (fun f : G → ℂ ↦ f g) hmOne
  have hmTrivg :
      oneG.character g = ∑ i, (mTriv i : ℂ) * (π i).character g := by
    simpa [Pi.smul_apply] using congrArg (fun f : G → ℂ ↦ f g) hmTriv
  -- Evaluate the Frobenius-extension formula at `g`, then regroup the three coefficient families.
  calc
    (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ) g =
        indθ.character g - (n : ℂ) * (indOne.character g - 1) := by
          rw [frobeniusExtension_eq_inducedClassFunction_sub_frobeniusPsi]
          simp only [Pi.sub_apply, Pi.smul_apply]
          rw [hindθ, frobeniusPsi_apply, hindOne, hcharOne]
          simpa [smul_eq_mul]
    _ = indθ.character g - (n : ℂ) * (indOne.character g - oneG.character g) := by
          rw [show oneG.character g = (1 : ℂ) by simpa using congrFun htriv g]
    _ = ∑ i, (((c i : ℤ) : ℂ) * (π i).character g) := by
          rw [hmθg, hmOneg, hmTrivg]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hc_cast i]
          ring
    _ = (∑ i, (c i : ℂ) • (π i).character) g := by
          simp [Pi.smul_apply]

/-- Helper for Exercise 7-7.2-5: an integral square sum equal to `1` has exactly one nonzero
coefficient, and that coefficient is `1` or `-1`. -/
private theorem integer_coefficients_eq_singleton_of_sq_sum_eq_one
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (h : ∑ i, (c i)^2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hnotallzero : ¬ ∀ i, c i = 0 := by
    intro hzero
    have hsum_zero : ∑ i, (c i)^2 = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_sq_le : (c i)^2 ≤ 1 := by
    calc
      (c i)^2 ≤ ∑ j, (c j)^2 := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ sq_nonneg (c j)) (Finset.mem_univ i) :
            (c i)^2 ≤ ∑ j, (c j)^2)
      _ = 1 := h
  have hi_sq_eq : (c i)^2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := by
    exact sq_eq_one_iff.mp hi_sq_eq
  refine ⟨i, hi_sign, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = ∑ k, (c k)^2 := by
        simpa using (Finset.sum_erase_add (s := Finset.univ) (f := fun k ↦ (c k)^2)
          (Finset.mem_univ i))
      _ = 1 := h
  have herase_zero : Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) = 0 := by
    linarith
  have hj_sq_le :
      (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (c k)) hj_mem :
        (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2))
  have hj_sq_eq_zero : (c j)^2 = 0 := by
    have hj_sq_nonneg : 0 ≤ (c j)^2 := sq_nonneg (c j)
    linarith
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

/-- Helper for Exercise 7-7.2-5: a simple finite-dimensional complex representation has positive
degree. -/
private theorem simple_fdRep_finrank_pos_local (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    0 < Module.finrank ℂ V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero V hzero
  exact Module.finrank_pos

/-- Helper for Exercise 7-7.2-5: every finite group admits a finite complete pairwise
nonisomorphic family of irreducible finite-dimensional complex representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      CategoryTheory.PairwiseNonisomorphic π ∧ Representation.IsCompleteIrreducibleFamily π := by
  classical
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :
      ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Subrepresentation (Representation.leftRegular ℂ G)),
        iSupIndep (fun i ↦ (σ i).toSubmodule) ∧
          (⨆ i, (σ i).toSubmodule) = ⊤ ∧
          ∀ i,
            Representation.IsIrreducible (G := G) (k := ℂ) (V := (σ i).toSubmodule)
              ((σ i).toRepresentation) :=
    exists_isInternal_irreducible_subrepresentations (ρ := Representation.leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot have isomorphic representatives.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    -- Each quotient representative comes from an irreducible summand of the regular representation.
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact Representation.FDRep.simple_of_isIrreducible (π q)
  have hπ_complete : Representation.IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := hπ_simple
        exists_iso := ?_ }
    intro τ _
    let τρ := τ.ρ
    have hτ_irreducible : Representation.IsIrreducible τρ := by
      exact Representation.FDRep.isIrreducible_of_simple τ
    letI : Representation.IsIrreducible τρ := hτ_irreducible
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        exact Subsingleton.elim _ _
      exact CategoryTheory.id_nonzero τ hzero
    letI : Nontrivial τ := hτ_nontriv
    have hτ_pos : 0 < Module.finrank ℂ τ := Module.finrank_pos
    have hτ_mult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } = Module.finrank ℂ τ := by
      simpa [τρ] using
        Representation.leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr τρ
          inferInstance
    have hτ_count_pos : 0 < Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv τρ) } := by
      rw [hτ_mult]
      exact hτ_pos
    obtain ⟨⟨j, hjτ⟩⟩ := (Nat.card_pos_iff.mp hτ_count_pos).1
    let q : ι := ⟦j⟧
    rcases hjτ with ⟨eτ⟩
    rcases Quotient.exact (Quotient.out_eq q) with ⟨eqj⟩
    refine ⟨q, ?_⟩
    exact ⟨(eτ.symm.trans eqj.symm).toFDRepIso⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

-- Exercise 7-7.2-5 (10): source part (e). The Frobenius extension of an irreducible character of
-- `H` is the character of an irreducible representation of `G`.
-- Proof sketch: use the previous parts of (e) to show that the extended class function has
-- self-pairing `1` and is an integral linear combination of irreducible characters, which
-- identifies it as the character of an irreducible representation of `G`.
/-- Helper for Exercise 7-7.2-5: a character is the sum of its diagonal matrix coefficients in any
finite basis. -/
private theorem character_eq_sum_diagonal_matrix_coefficients_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V) :
    ρ.character = fun g ↦ ∑ i, (ρ g).toMatrix b b i i := by
  ext g
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp [Matrix.diag]

/-- Helper for Exercise 7-7.2-5: after expanding both characters along finite bases, the normalized
pairing becomes a double sum of pairings of diagonal matrix coefficients. -/
private theorem pairing_eq_sum_diagonal_matrix_coefficient_pairings_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (bρ : Module.Basis ι ℂ V) (bσ : Module.Basis κ ℂ W) :
    ⟪ρ.character, σ.character⟫ =
      ∑ i, ∑ j,
        ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ := by
  rw [Representation.groupFunctionPairing_comm]
  rw [character_eq_sum_diagonal_matrix_coefficients_local (ρ := σ) bσ]
  rw [character_eq_sum_diagonal_matrix_coefficients_local (ρ := ρ) bρ]
  simp_rw [Representation.groupFunctionPairingOverField]
  calc
    (↑(Fintype.card G) : ℂ)⁻¹ *
        ∑ x : G, (∑ j, (σ x⁻¹).toMatrix bσ bσ j j) * ∑ i, (ρ x).toMatrix bρ bρ i i
      = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ x : G, ∑ j, (σ x⁻¹).toMatrix bσ bσ j j * ∑ i, (ρ x).toMatrix bρ bρ i i := by
          simp_rw [Finset.sum_mul]
    _ = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ x : G, ∑ j, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
          simp_rw [Finset.mul_sum]
    _ = (↑(Fintype.card G) : ℂ)⁻¹ *
          ∑ i, ∑ j, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
          congr 1
          have hxy :
              ∑ x : G, ∑ j, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ j, ∑ x : G, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            rw [Finset.sum_comm]
          have hyi :
              ∑ j, ∑ x : G, ∑ i, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ j, ∑ i, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
          have hji :
              ∑ j, ∑ i, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i =
                ∑ i, ∑ j, ∑ x : G, (σ x⁻¹).toMatrix bσ bσ j j * (ρ x).toMatrix bρ bρ i i := by
            rw [Finset.sum_comm]
          exact hxy.trans (hyi.trans hji)
    _ = ∑ i, ∑ j,
          ((↑(Fintype.card G) : ℂ)⁻¹ *
            ∑ x : G,
              (fun t ↦ (σ t).toMatrix bσ bσ j j) x⁻¹ *
                (fun t ↦ (ρ t).toMatrix bρ bρ i i) x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ j,
          ⟪fun t ↦ (σ t).toMatrix bσ bσ j j, fun t ↦ (ρ t).toMatrix bρ bρ i i⟫ := by
          simp_rw [Representation.groupFunctionPairingOverField]

/-- Helper for Exercise 7-7.2-5: characters of nonisomorphic irreducible representations are
orthogonal for LinearRepresentations_Serre_1977's normalized pairing. -/
private theorem character_pairing_eq_zero_of_not_isomorphic_irreducible_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [ρ.IsIrreducible] [σ.IsIrreducible] (hρσ : ¬ Nonempty (ρ.Equiv σ)) :
    ⟪ρ.character, σ.character⟫ = 0 := by
  letI : Invertible (Nat.card G : ℂ) := by
    refine invertibleOfNonzero ?_
    exact_mod_cast Nat.card_pos.ne'
  letI : IsEmpty (ρ.Equiv σ) := not_nonempty_iff.mp hρσ
  letI : Subsingleton (Representation.IntertwiningMap ρ σ) := inferInstance
  calc
    ⟪ρ.character, σ.character⟫ = Module.finrank ℂ (ρ.IntertwiningMap σ) := by
      simpa [Representation.groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
        (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := σ))
    _ = 0 := by
      rw [Module.finrank_zero_of_subsingleton]
      norm_num

/-- Helper for Exercise 7-7.2-5: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left_local
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (φ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ i ∈ s, a i • φ i, ψ⟫ = ∑ i ∈ s, ((a i : ℤ) : ℂ) * ⟪φ i, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty linear combination contributes nothing to the pairing.
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Rewrite the integer multiple as complex scalar multiplication before applying linearity.
      have hzsmul : (a i • φ i : G → ℂ) = (((a i : ℤ) : ℂ) • φ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, Representation.groupFunctionPairing_add_left, hzsmul,
        Representation.groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 7-7.2-5: the self-pairing of an explicit integral expansion in a complete
irreducible family is the corresponding integer square sum. -/
private theorem self_pairing_of_integral_complete_family_expansion_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (χ : G → ℂ) (c : ι → ℤ)
    (hexp : χ = ∑ i, (c i : ℂ) • (π i).character) :
    ⟪χ, χ⟫ = (((∑ i, (c i)^2 : ℤ) : ℂ)) := by
  have hdiag : ∀ i, ⟪(π i).character, (π i).character⟫ = (1 : ℂ) := by
    intro i
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    letI : Representation.IsIrreducible (π i).ρ :=
      Representation.FDRep.isIrreducible_of_simple (π i)
    -- Irreducible characters have unit self-pairing.
    simpa using
      (Representation.self_character_pairing_eq_one_iff_isIrreducible ((π i).ρ)).2
        inferInstance
  have hcoeff : ∀ i, ⟪(π i).character, χ⟫ = ((c i : ℤ) : ℂ) := by
    intro i
    calc
      ⟪(π i).character, χ⟫ = ⟪χ, (π i).character⟫ := by
        exact Representation.groupFunctionPairing_comm _ _
      _ = ∑ j, ((c j : ℤ) : ℂ) * ⟪(π j).character, (π i).character⟫ := by
            -- Expand the left occurrence of `χ` using the given irreducible-family expression.
            rw [hexp]
            simpa using
              groupFunctionPairing_sum_zsmul_left_local
                (s := Finset.univ) (a := c) (φ := fun j ↦ (π j).character)
                (ψ := (π i).character)
      _ = ((c i : ℤ) : ℂ) * ⟪(π i).character, (π i).character⟫ := by
            -- Orthogonality kills the off-diagonal terms because the family is pairwise nonisomorphic.
            refine Finset.sum_eq_single i ?_ ?_
            · intro j _ hji
              letI : CategoryTheory.Simple (π j) := hπ_complete.isSimple j
              letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
              letI : Representation.IsIrreducible (π j).ρ :=
                Representation.FDRep.isIrreducible_of_simple (π j)
              letI : Representation.IsIrreducible (π i).ρ :=
                Representation.FDRep.isIrreducible_of_simple (π i)
              have hnot_iso : ¬ Nonempty (Representation.Equiv (π j).ρ (π i).ρ) := by
                intro hrep
                exact hπ_pairwise hji ⟨Representation.Equiv.toFDRepIso (Classical.choice hrep)⟩
              have hpair_zero :
                  ⟪(π j).character, (π i).character⟫ = (0 : ℂ) :=
                character_pairing_eq_zero_of_not_isomorphic_irreducible_local
                  (ρ := (π j).ρ) (σ := (π i).ρ) (hρσ := hnot_iso)
              simp [hpair_zero]
            · intro hi
              exact (hi (Finset.mem_univ i)).elim
      _ = ((c i : ℤ) : ℂ) := by
            simp [hdiag i]
  -- Pair `χ` with itself by expanding the left factor termwise and then recover each coefficient.
  calc
    ⟪χ, χ⟫ = ⟪∑ i, (c i : ℂ) • (π i).character, χ⟫ := by
      rw [hexp]
    _ = ∑ i, ((c i : ℤ) : ℂ) * ⟪(π i).character, χ⟫ := by
          simpa using
            groupFunctionPairing_sum_zsmul_left_local
              (s := Finset.univ) (a := c) (φ := fun i ↦ (π i).character) (ψ := χ)
    _ = ∑ i, ((c i : ℤ) : ℂ) * ((c i : ℤ) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hcoeff i]
    _ = (((∑ i, (c i)^2 : ℤ) : ℂ)) := by
          simp [pow_two]

/-- Helper for Exercise 7-7.2-5: an explicit integral expansion against a complete irreducible
family, together with self-pairing `1`, forces a class function to be an irreducible character. -/
private theorem exists_simple_fdRep_character_eq_of_integral_expansion_self_pairing_eq_one_nonneg
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (χ : G → ℂ) (c : ι → ℤ)
    (hexp : χ = ∑ i, (c i : ℂ) • (π i).character)
    (hpair : ⟪χ, χ⟫ = (1 : ℂ)) (hone : 0 ≤ (χ 1).re) :
    ∃ ρ : FDRep ℂ G, CategoryTheory.Simple ρ ∧ ρ.character = χ := by
  have hsq_complex : (((∑ i, (c i)^2 : ℤ) : ℂ)) = (1 : ℂ) := by
    -- Route correction: isolate the orthogonality collapse first, then read off the square sum.
    rw [← self_pairing_of_integral_complete_family_expansion_local
      (π := π) hπ_pairwise hπ_complete (χ := χ) (c := c) hexp, hpair]
  have hsq : ∑ i, (c i)^2 = 1 := by
    exact_mod_cast hsq_complex
  obtain ⟨i, hi_sign, hzero⟩ := integer_coefficients_eq_singleton_of_sq_sum_eq_one c hsq
  have hsum_single : ∑ j, (c j : ℂ) • (π j).character = (c i : ℂ) • (π i).character := by
    -- All irreducible constituents except one have zero coefficient.
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      simp [hzero j hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hχ_single : χ = (c i : ℂ) • (π i).character := by
    -- Collapse the given integral expansion to the unique surviving irreducible character.
    calc
      χ = ∑ j, (c j : ℂ) • (π j).character := hexp
      _ = (c i : ℂ) • (π i).character := hsum_single
  rcases hi_sign with hi_pos | hi_neg
  · -- The positive coefficient identifies `χ` with the irreducible character `(π i).character`.
    refine ⟨π i, hπ_complete.isSimple i, ?_⟩
    calc
      (π i).character = ((1 : ℂ) • (π i).character) := by simp
      _ = χ := by simpa [hi_pos] using hχ_single.symm
  · letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    have hπ_pos : 0 < Module.finrank ℂ (π i) := simple_fdRep_finrank_pos_local (V := π i)
    have hχ_neg : χ = ((-1 : ℂ) • (π i).character) := by
      simpa [hi_neg] using hχ_single
    have hχ_one : (χ 1).re = -(Module.finrank ℂ (π i) : ℝ) := by
      -- Evaluating at the identity shows the negative sign would force a negative degree.
      calc
        (χ 1).re = (((((-1 : ℂ) • (π i).character) 1)).re) := by
          rw [hχ_neg]
        _ = -(Module.finrank ℂ (π i) : ℝ) := by
          simp [FDRep.char_one]
    have hπ_pos_real : 0 < (Module.finrank ℂ (π i) : ℝ) := by
      exact_mod_cast hπ_pos
    have hχ_one_neg : (χ 1).re < 0 := by
      rw [hχ_one]
      linarith
    exact (not_lt_of_ge hone hχ_one_neg).elim

/-- Exercise 7-7.2-5 (10): source part (e). The Frobenius extension of an irreducible character of
`H` is the character of an irreducible representation of `G`. -/
theorem exists_irreducible_representation_character_eq_frobeniusExtension
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (θ : FDRep ℂ H) [CategoryTheory.Simple θ] :
    ∃ ρ : FDRep ℂ G, CategoryTheory.Simple ρ ∧
      ρ.character =
        H.frobeniusExtension
          (fdRepCharacterClassFunction H θ) := by
  have hpair :
      ⟪(H.frobeniusExtension
          (fdRepCharacterClassFunction H θ) : G → ℂ),
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H θ) : G → ℂ)⟫ =
        (1 : ℂ) :=
    H.self_groupFunctionPairing_frobeniusExtension_character_eq_one hF θ
  have hone :
      0 ≤ ((H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ) 1).re := by
    rcases H.frobeniusExtension_character_one_eq_nat θ with ⟨n, hn⟩
    rw [hn]
    norm_num
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  obtain ⟨c, hc⟩ :=
    frobeniusExtension_character_eq_sum_irreducible_family_with_int_coefficients_local
      (H := H) (θ := θ) (π := π) hπ_pairwise hπ_complete
  -- Feed the explicit integral expansion, the self-pairing identity, and the value at `1`
  -- into the Chapter `3` irreducibility route.
  exact
    exists_simple_fdRep_character_eq_of_integral_expansion_self_pairing_eq_one_nonneg
      (π := π) hπ_pairwise hπ_complete
      (χ := H.frobeniusExtension (fdRepCharacterClassFunction H θ))
      (c := c) hc hpair hone

-- Exercise 7-7.2-5 (11): source part (e). Any irreducible representation of `G` whose character
-- is the Frobenius extension acts trivially on every element of `N`.
-- Proof sketch: on `N`, the extended character has value equal to its degree. Exercise
-- `6-6.5-7` then identifies the representing endomorphism with the identity.
/-- Helper for Exercise 7-7.2-5: the forward implication of Exercise `6-6.5-7` under a local
name, avoiding an extra item-file import. -/
theorem eq_one_of_character_eq_char_one_of_isOfFinOrder_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s)
    (hchar : ρ.character s = ρ.character 1) :
    ρ s = 1 := by
  -- This is exactly the forward implication of Exercise `6-6.5-7`.
  exact (Representation.eq_one_iff_character_eq_char_one ρ s hs).2 hchar

/-- Exercise 7-7.2-5 (11): source part (e). Any irreducible representation of `G` whose character
is the Frobenius extension acts trivially on every element of `N`. -/
theorem eq_one_on_frobeniusNonconjugateSet_of_irreducible_character_eq_frobeniusExtension
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (θ : FDRep ℂ H) [CategoryTheory.Simple θ]
    (ρ : FDRep ℂ G) [CategoryTheory.Simple ρ]
    (hχ : ρ.character =
      H.frobeniusExtension
        (fdRepCharacterClassFunction H θ)) :
    H.frobeniusNonconjugateSet ⊆ (ρ.ρ.ker : Set G) := by
  have hvalue_one :
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ) 1 =
        θ.character 1 := by
    -- The Frobenius extension restricts back to the original character on `H`, in particular at
    -- the identity element.
    have hrestrict := congrArg
      (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) 1)
      (H.classFunctionRestriction_frobeniusExtension hF
        (fdRepCharacterClassFunction H θ))
    simpa [classFunctionRestriction_apply, fdRepCharacterClassFunction] using hrestrict
  intro n hn
  change ρ.ρ n = 1
  -- On `N`, the Frobenius extension takes the same value as at `1`, so the local Chapter 6
  -- criterion identifies the representing endomorphism with the identity.
  have hχ_eval (g : G) :
      ρ.character g =
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H θ) : G → ℂ) g := by
    simpa using congrArg (fun ψ : G → ℂ ↦ ψ g) hχ
  have hχ_one :
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H θ) : G → ℂ) 1 =
        ρ.character 1 := by
    simpa using (hχ_eval 1).symm
  have hchar : ρ.character n = ρ.character 1 := by
    have hvalue_nonconjugate :
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H θ) : G → ℂ) n =
          (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) 1 := by
      calc
        (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) n =
            (fdRepCharacterClassFunction H θ : H → ℂ) 1 := by
              exact H.frobeniusExtension_eqOn_frobeniusNonconjugateSet
                (fdRepCharacterClassFunction H θ) hn
        _ = θ.character 1 := rfl
        _ = (H.frobeniusExtension
              (fdRepCharacterClassFunction H θ) : G → ℂ) 1 := hvalue_one.symm
    calc
      ρ.character n =
          (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) n := by
              simpa using hχ_eval n
      _ = (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) 1 := hvalue_nonconjugate
      _ = ρ.character 1 := hχ_one
  exact eq_one_of_character_eq_char_one_of_isOfFinOrder_local
    (ρ := ρ.ρ) (s := n) (hs := isOfFinOrder_of_finite n) hchar

end

section

variable {G : Type} [Group G] [Finite G]

/-- Helper for Exercise 7-7.2-5: a finite-dimensional complex representation of degree `1` is the
representation attached to a linear character. -/
private theorem exists_linear_character_of_fdRep_finrank_one_local
    (V : FDRep ℂ G) (hV : Module.finrank ℂ V = 1) :
    ∃ α : G →* ℂˣ, V.character = α.toRepresentation.character := by
  let scalarEquiv : ℂ ≃ₗ[ℂ] (V →ₗ[ℂ] V) := LinearEquiv.smul_id_of_finrank_eq_one hV
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hV c
  let α₀ : G → ℂ := fun g ↦ scalarEquiv.symm (V.ρ g)
  have hα₀_eq (g : G) : V.ρ g = α₀ g • LinearMap.id := by
    -- In degree `1`, every action map is scalar multiplication by a unique complex number.
    calc
      V.ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    -- The identity element acts by the identity endomorphism, so its scalar is `1`.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = V.ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[ℂ] V) := by
        simp
      _ = scalarEquiv 1 := by
        simpa using (hscalar (1 : ℂ)).symm
  have hα₀_mul (g h : G) : α₀ (g * h) = α₀ g * α₀ h := by
    -- Multiplicativity of the representation turns the scalar assignment into a character.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = V.ρ (g * h) := by
        simp [α₀]
      _ = V.ρ g * V.ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : G) : α₀ g ≠ 0 := by
    -- An invertible action map on a nonzero one-dimensional space cannot have scalar `0`.
    have hpos : 0 < Module.finrank ℂ V := by
      simpa [hV]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hg0
    have hzero : V.ρ g = 0 := by
      simp [hα₀_eq, hg0]
    have hone : (1 : V →ₗ[ℂ] V) ≠ 0 := one_ne_zero
    have hmul : V.ρ g * V.ρ g⁻¹ = (1 : V →ₗ[ℂ] V) := by
      simpa using (V.ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[ℂ] V) = 0 := by
      calc
        (1 : V →ₗ[ℂ] V) = V.ρ g * V.ρ g⁻¹ := hmul.symm
        _ = 0 := by
          rw [hzero]
          simp
    exact hone hidzero
  let α : G →* ℂˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        exact hα₀_one
      map_mul' g h := by
        ext
        exact hα₀_mul g h }
  refine ⟨α, ?_⟩
  ext g
  -- Taking traces of the scalar action recovers the original character.
  rw [MonoidHom.toRepresentation_character_apply]
  calc
    V.character g = LinearMap.trace ℂ V (V.ρ g) := by
      rfl
    _ = LinearMap.trace ℂ V (α₀ g • LinearMap.id) := by
      rw [hα₀_eq]
    _ = α₀ g * LinearMap.trace ℂ V LinearMap.id := by
      simp [smul_eq_mul]
    _ = α₀ g * Module.finrank ℂ V := by
      simp [LinearMap.trace_id]
    _ = α₀ g := by
      simp [hV]
    _ = (α g : ℂ) := rfl

/-- Exercise 7-7.2-5 (12): source part (f). Every one-dimensional complex representation of a
Frobenius subgroup `H` extends to a one-dimensional representation of `G` whose kernel contains
`N`. -/
-- Proof sketch: apply part (e) to the one-dimensional representation `χ.toRepresentation` of `H`.
-- Because the degree is `1`, the irreducible representation of `G` obtained there is again
-- one-dimensional, so it comes from a canonical degree-1 character `ρ : G →* ℂˣ`; the character
-- equality then forces `ρ` to extend `χ` and to be trivial on `N`.
theorem exists_linear_representation_extension_with_frobeniusNonconjugateSet_in_kernel
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (χ : H →* ℂˣ) :
    ∃ ρ : G →* ℂˣ,
      ρ.comp H.subtype = χ ∧ H.frobeniusNonconjugateSet ⊆ (ρ.ker : Set G) := by
  let θ : FDRep ℂ H := FDRep.of χ.toRepresentation
  letI : Representation.IsIrreducible θ.ρ := by
    -- The source representation has degree `1`, so it is irreducible.
    simpa [θ] using MonoidHom.toRepresentation_isIrreducible χ
  letI : CategoryTheory.Simple θ := Representation.FDRep.simple_of_isIrreducible θ
  obtain ⟨τ, _hτsimple, hτchar⟩ :=
    H.exists_irreducible_representation_character_eq_frobeniusExtension hF θ
  have hτchar_one : τ.character 1 = 1 := by
    -- Restrict the Frobenius extension back to `H` at the identity to read off the degree.
    calc
      τ.character 1 =
          (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) 1 := by
              simpa using congrArg (fun ψ : G → ℂ ↦ ψ 1) hτchar
      _ = θ.character 1 := by
            have hrestrict := congrArg
              (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) 1)
              (H.classFunctionRestriction_frobeniusExtension hF
                (fdRepCharacterClassFunction H θ))
            simpa [classFunctionRestriction_apply, fdRepCharacterClassFunction] using hrestrict
      _ = 1 := by
            simp [θ, MonoidHom.toRepresentation_character_apply]
  have hτfinrank : Module.finrank ℂ τ = 1 := by
    -- For finite-dimensional representations, the character at `1` is the degree.
    have hcast : (Module.finrank ℂ τ : ℂ) = 1 := by
      simpa [FDRep.char_one] using hτchar_one
    exact_mod_cast hcast
  obtain ⟨ρ, hρchar⟩ := exists_linear_character_of_fdRep_finrank_one_local τ hτfinrank
  refine ⟨ρ, ?_, ?_⟩
  · ext h
    -- Compare the restricted extending character with `χ` through the common Frobenius extension.
    calc
      ((ρ.comp H.subtype) h : ℂ) = ρ.toRepresentation.character h := by
        simp [MonoidHom.toRepresentation_character_apply]
      _ = τ.character h := by
            simpa using congrArg (fun ψ : G → ℂ ↦ ψ h) hρchar.symm
      _ = (H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) : G → ℂ) h := by
            simpa using congrArg (fun ψ : G → ℂ ↦ ψ h) hτchar
      _ = θ.character h := by
            have hrestrict := congrArg
              (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) h)
              (H.classFunctionRestriction_frobeniusExtension hF
                (fdRepCharacterClassFunction H θ))
            simpa [classFunctionRestriction_apply, fdRepCharacterClassFunction] using hrestrict
      _ = χ.toRepresentation.character h := by
            rfl
      _ = (χ h : ℂ) := MonoidHom.toRepresentation_character_apply χ h
  · let σ : FDRep ℂ G := FDRep.of ρ.toRepresentation
    letI : Representation.IsIrreducible σ.ρ := by
      -- The extracted linear character again affords a degree-`1` irreducible representation.
      simpa [σ] using MonoidHom.toRepresentation_isIrreducible ρ
    letI : CategoryTheory.Simple σ := Representation.FDRep.simple_of_isIrreducible σ
    have hσchar :
        σ.character =
          H.frobeniusExtension
            (fdRepCharacterClassFunction H θ) := by
      exact hρchar.symm.trans hτchar
    intro n hn
    -- Part (11) identifies the representing endomorphism with the identity on `N`.
    have hker : σ.ρ n = 1 := by
      exact
        H.eq_one_on_frobeniusNonconjugateSet_of_irreducible_character_eq_frobeniusExtension
          hF θ σ hσchar hn
    change ρ n = 1
    have hker_apply := LinearMap.congr_fun hker (1 : ℂ)
    apply Units.ext
    simpa [σ, MonoidHom.toRepresentation, Representation.ofMulAction] using hker_apply

-- Exercise 7-7.2-5 (13): source part (f). The set `N ∪ {1}` is the underlying set of a normal
-- subgroup of `G`.
-- Proof sketch: intersect the kernels of the linear extensions from part (f) to obtain a normal
-- subgroup whose elements are exactly `1` together with the elements of `N`.
/-- Helper for Exercise 7-7.2-5: the intersection of the kernels of irreducible Frobenius
extensions contains `N ∪ {1}`. -/
private theorem insert_one_frobeniusNonconjugateSet_subset_extension_kernel_iInf_local
    {ι : Type*} [Fintype ι]
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (π : ι → FDRep ℂ H)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (ρ : ι → FDRep ℂ G)
    (hρsimple : ∀ i, CategoryTheory.Simple (ρ i))
    (hρchar : ∀ i,
      (ρ i).character =
        H.frobeniusExtension (fdRepCharacterClassFunction H (π i))) :
    Set.insert 1 H.frobeniusNonconjugateSet ⊆
      ((⨅ i, (ρ i).ρ.ker : Subgroup G) : Set G) := by
  intro g hg
  rcases (Set.mem_insert_iff.mp hg) with rfl | hgN
  · -- The identity lies in every kernel, hence in their intersection.
    show (1 : G) ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G)
    rw [Subgroup.mem_iInf]
    intro i
    simp
  · -- Each irreducible Frobenius extension acts trivially on `N`.
    show g ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G)
    rw [Subgroup.mem_iInf]
    intro i
    letI : CategoryTheory.Simple (π i) := hπ_complete.isSimple i
    letI : CategoryTheory.Simple (ρ i) := hρsimple i
    exact
      H.eq_one_on_frobeniusNonconjugateSet_of_irreducible_character_eq_frobeniusExtension
        hF (π i) (ρ i) (hρchar i) hgN

/-- Helper for Exercise 7-7.2-5: membership in the intersection of the extension kernels forces
every irreducible character in the chosen complete family to take its degree value. -/
private theorem character_eq_degree_of_mem_extension_kernel_iInf_local
    {ι : Type*} [Fintype ι]
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (π : ι → FDRep ℂ H)
    (ρ : ι → FDRep ℂ G)
    (hρchar : ∀ i,
      (ρ i).character =
        H.frobeniusExtension (fdRepCharacterClassFunction H (π i)))
    {h : H}
    (hh : (h : G) ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G)) :
    ∀ i, (π i).character h = Module.finrank ℂ (π i) := by
  intro i
  have hker : (ρ i).ρ (h : G) = 1 := by
    -- Kernel membership turns the representing endomorphism into the identity.
    have hmem : (h : G) ∈ (ρ i).ρ.ker := (Subgroup.mem_iInf.mp hh) i
    simpa using hmem
  have hchar_eq :
      (ρ i).character (h : G) = (ρ i).character 1 := by
    -- Equal representation endomorphisms have equal traces, hence equal character values.
    have hker' : (ρ i).ρ (h : G) = (ρ i).ρ 1 := by
      calc
        (ρ i).ρ (h : G) = 1 := hker
        _ = (ρ i).ρ 1 := by simp
    simpa [Representation.character] using
      congrArg (fun T : ρ i →ₗ[ℂ] ρ i => LinearMap.trace ℂ (ρ i) T) hker'
  have hrestrict_h :
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H (π i)) : G → ℂ) h =
        (π i).character h := by
    -- Restrict the Frobenius extension back to `H` at the chosen subgroup element.
    have hrestrict := congrArg
      (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) h)
      (H.classFunctionRestriction_frobeniusExtension hF
        (fdRepCharacterClassFunction H (π i)))
    simpa [classFunctionRestriction_apply, fdRepCharacterClassFunction] using hrestrict
  have hrestrict_one :
      (H.frobeniusExtension
        (fdRepCharacterClassFunction H (π i)) : G → ℂ) 1 =
        Module.finrank ℂ (π i) := by
    -- The same restriction identity at `1` identifies the degree of the subgroup representation.
    have hrestrict := congrArg
      (fun ψ : classFunctionSubspace H ↦ (ψ : H → ℂ) 1)
      (H.classFunctionRestriction_frobeniusExtension hF
        (fdRepCharacterClassFunction H (π i)))
    simpa [classFunctionRestriction_apply, fdRepCharacterClassFunction, FDRep.char_one] using
      hrestrict
  have hρ_eval :
      (ρ i).character (h : G) =
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H (π i)) : G → ℂ) h := by
    simpa using congrArg (fun ψ : G → ℂ ↦ ψ h) (hρchar i)
  have hρ_eval_one :
      (ρ i).character 1 =
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H (π i)) : G → ℂ) 1 := by
    simpa using congrArg (fun ψ : G → ℂ ↦ ψ 1) (hρchar i)
  -- Compare the kernel-induced character identity with the restriction formulas on `H`.
  calc
    (π i).character h =
        (H.frobeniusExtension
          (fdRepCharacterClassFunction H (π i)) : G → ℂ) h := hrestrict_h.symm
    _ = (ρ i).character (h : G) := hρ_eval.symm
    _ = (ρ i).character 1 := hchar_eq
    _ = (H.frobeniusExtension
          (fdRepCharacterClassFunction H (π i)) : G → ℂ) 1 := hρ_eval_one
    _ = Module.finrank ℂ (π i) := hrestrict_one

/-- Helper for Exercise 7-7.2-5: a nontrivial subgroup element cannot lie in the intersection of
the kernels of the chosen irreducible Frobenius extensions. -/
private theorem nontrivial_subgroup_element_not_mem_extension_kernel_iInf_local
    {ι : Type*} [Fintype ι]
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup)
    (π : ι → FDRep ℂ H)
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : Representation.IsCompleteIrreducibleFamily π)
    (ρ : ι → FDRep ℂ G)
    (hρchar : ∀ i,
      (ρ i).character =
        H.frobeniusExtension (fdRepCharacterClassFunction H (π i)))
    (h : H) (hh : h ≠ 1) :
    (h : G) ∉ (⨅ i, (ρ i).ρ.ker : Subgroup G) := by
  intro hhmem
  have hvalue :
      ∀ i, (π i).character h = Module.finrank ℂ (π i) :=
    H.character_eq_degree_of_mem_extension_kernel_iInf_local hF π ρ hρchar hhmem
  have hvanish :
      ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character h = 0 := by
    -- The complete-family regular-character identity vanishes away from `1`.
    simpa using
      regular_character_vanishing_of_complete_irreducible_family_local
        (G := H) (π := π) hπ_pairwise hπ_complete hh
  have hsum_card :
      ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character h =
        (Nat.card H : ℂ) := by
    have hsum_sq_cast :
        ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character 1 =
          (Nat.card H : ℂ) := by
      calc
        ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character 1 =
            (Representation.leftRegular ℂ H).character 1 := by
              symm
              exact
                leftRegular_character_eq_sum_degree_mul_character_of_complete_irreducible_family_local
                  (G := H) (π := π) hπ_pairwise hπ_complete 1
        _ = (Nat.card H : ℂ) := by
              simpa using (Representation.leftRegular_character_one (k := ℂ) (G := H))
    -- Rewriting every character value by its degree turns the sum into the square-degree formula.
    calc
      ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character h =
          ∑ i, (Module.finrank ℂ (π i) : ℂ) * (Module.finrank ℂ (π i) : ℂ) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [hvalue i]
      _ = ∑ i, (Module.finrank ℂ (π i) : ℂ) * (π i).character 1 := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simp [FDRep.char_one]
      _ = (Nat.card H : ℂ) := hsum_sq_cast
  have hcard_ne : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hcard_zero : (Nat.card H : ℂ) = 0 := by
    exact hsum_card.symm.trans hvanish
  exact hcard_ne hcard_zero

/-- Helper for Exercise 7-7.2-5: membership in the intersection of the extension kernels is
stable under conjugacy. -/
private theorem mem_extension_kernel_iInf_of_isConj_local
    {ι : Sort*}
    (ρ : ι → FDRep ℂ G)
    {g x : G} (hconj : IsConj g x) :
    g ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G) →
      x ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G) := by
  intro hg
  have hnormal : (⨅ i, (ρ i).ρ.ker : Subgroup G).Normal := by
    exact Subgroup.normal_iInf_normal fun i => inferInstance
  rcases isConj_iff.mp hconj with ⟨c, hc⟩
  -- Normality transports membership across the chosen conjugacy relation.
  have hx :
      c * g * c⁻¹ ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G) :=
    hnormal.conj_mem g hg c
  simpa [hc] using hx

/-- Exercise 7-7.2-5 (13): source part (f). The set `N ∪ {1}` is the underlying set of a normal
subgroup of `G`. -/
theorem exists_normal_subgroup_eq_insert_one_frobeniusNonconjugateSet
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) :
    ∃ A : Subgroup G,
      A.Normal ∧
        (A : Set G) = Set.insert 1 H.frobeniusNonconjugateSet := by
  classical
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := H)
  choose ρ hρsimple hρchar using
    fun i => H.exists_irreducible_representation_character_eq_frobeniusExtension hF (π i)
  let A : Subgroup G := ⨅ i, (ρ i).ρ.ker
  have hA_normal : A.Normal := by
    -- Kernels are normal, and normality is preserved by arbitrary intersections.
    dsimp [A]
    exact Subgroup.normal_iInf_normal fun i => inferInstance
  have hsubset :
      Set.insert 1 H.frobeniusNonconjugateSet ⊆ (A : Set G) := by
    -- Theorem (11) gives the easy inclusion `N ∪ {1} ⊆ A`.
    simpa [A] using
      H.insert_one_frobeniusNonconjugateSet_subset_extension_kernel_iInf_local
        hF π hπ_complete ρ hρsimple hρchar
  refine ⟨A, hA_normal, Set.Subset.antisymm ?_ hsubset⟩
  intro g hgA
  by_cases hg1 : g = 1
  · -- The identity is already one of the required points of `N ∪ {1}`.
    subst hg1
    exact Set.mem_insert 1 H.frobeniusNonconjugateSet
  · have hgA' : g ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G) := by
      simpa [A] using hgA
    by_cases hgN : g ∈ H.frobeniusNonconjugateSet
    · -- Elements already in `N` lie in the claimed set by definition.
      simpa [Set.mem_insert_iff] using (Or.inr hgN : g = 1 ∨ g ∈ H.frobeniusNonconjugateSet)
    · -- Route correction: transport `g` to a conjugate subgroup element and then separate it
      -- from the kernel intersection using the complete irreducible family on `H`.
      rw [frobeniusNonconjugateSet, Set.mem_setOf_eq, not_forall] at hgN
      rcases hgN with ⟨h, hh⟩
      have hconj : IsConj g h := Classical.not_not.mp hh
      have hhA : (h : G) ∈ (⨅ i, (ρ i).ρ.ker : Subgroup G) :=
        mem_extension_kernel_iInf_of_isConj_local (ρ := ρ) hconj hgA'
      have hh_ne : h ≠ 1 := by
        intro hh1
        apply hg1
        rcases isConj_iff.mp hconj with ⟨c, hc⟩
        calc
          g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = 1 := by simp [hc, hh1]
      have hh_not :
          (h : G) ∉ (⨅ i, (ρ i).ρ.ker : Subgroup G) :=
        H.nontrivial_subgroup_element_not_mem_extension_kernel_iInf_local
          hF π hπ_pairwise hπ_complete ρ hρchar h hh_ne
      exact (hh_not hhA).elim

/-- Exercise 7-7.2-5 (14): source part (f). A normal subgroup with underlying set `N ∪ {1}`
meets `H` trivially. -/
-- Proof sketch: an element lying in both `H` and `N ∪ {1}` is either `1` or simultaneously
-- conjugate and nonconjugate to an element of `H`, so only the identity can occur.
theorem inf_eq_bot_of_normal_subgroup_eq_insert_one_frobeniusNonconjugateSet
    (H : Subgroup G) (A : Subgroup G)
    (hA_set : (A : Set G) = Set.insert 1 H.frobeniusNonconjugateSet) :
    H ⊓ A = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxH, hxA⟩
    have hxA' : x ∈ Set.insert 1 H.frobeniusNonconjugateSet := by
      simpa [hA_set] using hxA
    have hxA'' : x = 1 ∨ x ∈ H.frobeniusNonconjugateSet := by
      simpa [Set.mem_insert_iff] using hxA'
    rcases hxA'' with rfl | hxN
    · simp
    · exfalso
      exact (hxN ⟨x, hxH⟩) (isConj_iff.2 ⟨1, by simp⟩)
  · exact bot_le

/-- Exercise 7-7.2-5 (15): source part (f). A normal subgroup with underlying set `N ∪ {1}`,
together with `H`, generates all of `G`. -/
-- Proof sketch: compare the cardinalities of `H` and `N ∪ {1}` using part (a), then use the
-- trivial-intersection statement to identify the product size with `|G|`.
theorem sup_eq_top_of_normal_subgroup_eq_insert_one_frobeniusNonconjugateSet
    (H : Subgroup G) (hF : H.IsFrobeniusSubgroup) (A : Subgroup G)
    (hA_set : (A : Set G) = Set.insert 1 H.frobeniusNonconjugateSet) :
    H ⊔ A = ⊤ := by
  classical
  have h1not : (1 : G) ∉ H.frobeniusNonconjugateSet := by
    intro h1N
    exact (h1N ⟨1, by simp⟩) (isConj_iff.2 ⟨1, by simp⟩)
  have hcardA_insert :
      Nat.card A = Nat.card { g : G // g ∈ Set.insert 1 H.frobeniusNonconjugateSet } := by
    exact Nat.card_congr (Equiv.setCongr hA_set)
  have hcardA_split :
      Nat.card { g : G // g ∈ Set.insert 1 H.frobeniusNonconjugateSet } =
        Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 := by
    -- The set `N ∪ {1}` is `N` together with one extra point because `1 ∉ N`.
    have hcardSum :
        Nat.card ({ g : G // g ∈ H.frobeniusNonconjugateSet } ⊕ PUnit) =
          Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 := by
      letI : Fintype { g : G // g ∈ H.frobeniusNonconjugateSet } := Fintype.ofFinite _
      simp [Nat.card_eq_fintype_card]
    calc
      Nat.card { g : G // g ∈ Set.insert 1 H.frobeniusNonconjugateSet } =
          Nat.card ({ g : G // g ∈ H.frobeniusNonconjugateSet } ⊕ PUnit) := by
            exact Nat.card_congr (Equiv.Set.insert h1not)
      _ = Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 := hcardSum
  have hcardA : Nat.card A = H.index := by
    -- Part (a) says `|N| = [G : H] - 1`; adding back the identity gives `|A| = [G : H]`.
    have hindex : Nat.card G / Nat.card H = H.index := by
      calc
        Nat.card G / Nat.card H = (H.index * Nat.card H) / Nat.card H := by
          rw [← H.index_mul_card]
        _ = H.index := by
          simpa [Nat.mul_comm] using
            (Nat.mul_div_right H.index (show 0 < Nat.card H by exact Nat.card_pos))
    have hN :
        Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } =
          Nat.card G / Nat.card H - 1 := by
      simpa using
        (H.frobeniusNonconjugateSet_card hF :
          Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } =
            Nat.card G / Nat.card H - 1)
    have hNplus :
        Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 =
          (Nat.card G / Nat.card H - 1) + 1 := by
      exact congrArg (fun n : Nat ↦ n + 1) hN
    calc
      Nat.card A =
          Nat.card { g : G // g ∈ Set.insert 1 H.frobeniusNonconjugateSet } := hcardA_insert
      _ = Nat.card { g : G // g ∈ H.frobeniusNonconjugateSet } + 1 := hcardA_split
      _ = (Nat.card G / Nat.card H - 1) + 1 := hNplus
      _ = (H.index - 1) + 1 := by rw [hindex]
      _ = H.index := Nat.sub_add_cancel (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
  have hcard_mul : Nat.card H * Nat.card A = Nat.card G := by
    -- The cardinality route now matches the subgroup index formula.
    rw [hcardA]
    exact H.card_mul_index
  have hdisj : Disjoint H A := by
    rw [disjoint_iff]
    exact H.inf_eq_bot_of_normal_subgroup_eq_insert_one_frobeniusNonconjugateSet A hA_set
  -- A finite subgroup complement is exactly a disjoint subgroup with the correct cardinal product.
  exact (Subgroup.isComplement'_of_card_mul_and_disjoint hcard_mul hdisj).sup_eq_top

end

section

variable {G : Type u} [Group G]

/-- Helper for Exercise 7-7.2-5: for a nontrivial element of the normal complement, the Frobenius
intersection condition is equivalent to the absence of nontrivial fixed points under conjugation
by elements of `H`. -/
theorem frobenius_intersection_with_normal_component_iff_fixed_point_local
    (H : Subgroup G) (A : Subgroup G) (hA : A.Normal) (hHA : H.IsComplement' A)
    {a : A} (ha : a ≠ 1) :
    H ⊓ H.map (MulAut.conj (a : G)).toMonoidHom = ⊥ ↔
      ∀ s : H, s ≠ 1 → (s : G) * (a : G) * (s : G)⁻¹ ≠ a := by
  constructor
  · intro hbot s hs hfix
    -- A fixed point `s a s⁻¹ = a` makes `s` lie in both `H` and `aHa⁻¹`.
    have hsmap_eq : (MulAut.conj (a : G)).toMonoidHom (s : G) = s := by
      have hcomm : (s : G) * (a : G) = (a : G) * (s : G) := by
        have := congrArg (fun z : G => z * (s : G)) hfix
        simpa [mul_assoc] using this
      calc
        (MulAut.conj (a : G)).toMonoidHom (s : G) = (a : G) * (s : G) * (a : G)⁻¹ := rfl
        _ = (s : G) * (a : G) * (a : G)⁻¹ := by rw [← hcomm]
        _ = s := by simp [mul_assoc]
    have hmem : (s : G) ∈ H ⊓ H.map (MulAut.conj (a : G)).toMonoidHom := by
      refine ⟨s.2, (Subgroup.mem_map).2 ?_⟩
      exact ⟨s, s.2, hsmap_eq⟩
    have hs_one : (s : G) = 1 := by
      have hmem_bot : (s : G) ∈ (⊥ : Subgroup G) := by
        rwa [hbot] at hmem
      exact by simpa using hmem_bot
    exact hs (Subtype.ext hs_one)
  · intro hfree
    have hbotHA : H ⊓ A = ⊥ := disjoint_iff.mp hHA.disjoint
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxH, hxmap⟩
      rcases (Subgroup.mem_map).1 hxmap with ⟨y, hyH, hyx⟩
      have hyx_eq : (a : G) * y * (a : G)⁻¹ = x := by
        simpa [MulAut.conj] using hyx
      -- Conjugating `x` by `a` lands back in `H`, because `x ∈ aHa⁻¹`.
      have hy_eq : (a : G)⁻¹ * x * (a : G) = y := by
        calc
          (a : G)⁻¹ * x * (a : G) = (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * (a : G) := by
            rw [hyx_eq]
          _ = y := by
            group
      have hy_mem : (a : G)⁻¹ * x * (a : G) ∈ H := by
        simpa [hy_eq] using hyH
      have hcomm_mem_H : (a : G)⁻¹ * x * (a : G) * x⁻¹ ∈ H := by
        exact H.mul_mem hy_mem (H.inv_mem hxH)
      -- The same commutator lies in `A` because `A` is normal.
      have hconjA : x * (a : G) * x⁻¹ ∈ A := hA.conj_mem (a : G) a.2 x
      have hcomm_mem_A : (a : G)⁻¹ * x * (a : G) * x⁻¹ ∈ A := by
        have : (a : G)⁻¹ * (x * (a : G) * x⁻¹) ∈ A := A.mul_mem (A.inv_mem a.2) hconjA
        simpa [mul_assoc] using this
      have hcomm_one : (a : G)⁻¹ * x * (a : G) * x⁻¹ = 1 := by
        have : (a : G)⁻¹ * x * (a : G) * x⁻¹ ∈ H ⊓ A := ⟨hcomm_mem_H, hcomm_mem_A⟩
        have hbot_mem : (a : G)⁻¹ * x * (a : G) * x⁻¹ ∈ (⊥ : Subgroup G) := by
          rwa [hbotHA] at this
        exact by simpa using hbot_mem
      -- So `x` centralizes `a`; the fixed-point hypothesis forces `x = 1`.
      have hfix : (x : G) * (a : G) * (x : G)⁻¹ = a := by
        calc
          (x : G) * (a : G) * (x : G)⁻¹ =
              (a : G) * ((a : G)⁻¹ * x * (a : G) * (x : G)⁻¹) := by
                group
          _ = a := by simp [hcomm_one]
      have hx_one : x = 1 := by
        by_contra hx_ne
        have hx_ne' : (⟨x, hxH⟩ : H) ≠ 1 := by
          intro hx_sub
          apply hx_ne
          exact congrArg Subtype.val hx_sub
        exact (hfree ⟨x, hxH⟩ hx_ne' hfix).elim
      simpa [hx_one]
    · exact bot_le

/-- Exercise 7-7.2-5 (16): source part (g). If `G` is the internal semidirect product of `H` and
a normal subgroup `A`, then `H` is Frobenius exactly when every nonidentity element of `H` acts
without fixed points on `A - {1}` by conjugation. -/
-- Proof sketch: in the semidirect-product decomposition, an element belongs to
-- `H ∩ tHt⁻¹` precisely when the `H`-part centralizes the `A`-part of `t`. The Frobenius
-- condition therefore amounts to saying that no nontrivial element of `H` fixes a nontrivial
-- element of `A`. The internal-product data are most canonically recorded by the complement owner
-- `H.IsComplement' A` together with the normality of `A`.
theorem isFrobeniusSubgroup_iff_free_on_normal_complement
    (H : Subgroup G) (A : Subgroup G) (hA : A.Normal) (hHA : H.IsComplement' A) :
    H.IsFrobeniusSubgroup ↔
      ∀ (s : H) (hs : s ≠ 1) (t : A) (ht : t ≠ 1), (s : G) * (t : G) * (s : G)⁻¹ ≠ t := by
  constructor
  · intro hF s hs t ht
    have hbotHA : H ⊓ A = ⊥ := disjoint_iff.mp hHA.disjoint
    have ht_not_mem : (t : G) ∉ H := by
      intro htH
      have : (t : G) ∈ H ⊓ A := ⟨htH, t.2⟩
      have hbot_mem : (t : G) ∈ (⊥ : Subgroup G) := by
        rwa [hbotHA] at this
      have ht_one : (t : G) = 1 := by
        simpa using hbot_mem
      exact ht (Subtype.ext ht_one)
    have hbot : H ⊓ H.map (MulAut.conj (t : G)).toMonoidHom = ⊥ := hF ht_not_mem
    exact
      (H.frobenius_intersection_with_normal_component_iff_fixed_point_local A hA hHA ht).1
        hbot s hs
  · intro hfree u hu
    rcases hHA.2 u with ⟨⟨s, a⟩, hsa⟩
    have hsa' : (s : G) * (a : G) = u := by
      simpa using hsa
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply hu
      have hu_eq : u = (s : G) * (a : G) := by
        simpa using hsa'.symm
      rw [hu_eq, ha1]
      simpa using s.2
    have hbot_a : H ⊓ H.map (MulAut.conj (a : G)).toMonoidHom = ⊥ :=
      (H.frobenius_intersection_with_normal_component_iff_fixed_point_local A hA hHA ha_ne).2
        (fun t ht ↦ hfree t ht a ha_ne)
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxH, hxmap⟩
      rcases (Subgroup.mem_map).1 hxmap with ⟨y, hyH, hyx⟩
      -- Conjugating by the `H`-component transports the general intersection to the
      -- special `aHa⁻¹` intersection handled by the helper above.
      have hyx' : x = (s : G) * ((a : G) * y * (a : G)⁻¹) * (s : G)⁻¹ := by
        calc
          x = u * y * u⁻¹ := by
            simpa [MulAut.conj] using hyx.symm
          _ = (s : G) * ((a : G) * y * (a : G)⁻¹) * (s : G)⁻¹ := by
            rw [← hsa']
            group
      have hzH : (s : G)⁻¹ * x * (s : G) ∈ H := by
        exact H.mul_mem (H.mul_mem (H.inv_mem s.2) hxH) s.2
      have hzmap : (s : G)⁻¹ * x * (s : G) ∈ H.map (MulAut.conj (a : G)).toMonoidHom := by
        refine (Subgroup.mem_map).2 ?_
        refine ⟨y, hyH, ?_⟩
        have hz_eq : (s : G)⁻¹ * x * (s : G) = (a : G) * y * (a : G)⁻¹ := by
          calc
            (s : G)⁻¹ * x * (s : G) =
                (s : G)⁻¹ * ((s : G) * ((a : G) * y * (a : G)⁻¹) * (s : G)⁻¹) * (s : G) := by
                  rw [hyx']
            _ = (a : G) * y * (a : G)⁻¹ := by
                  group
        simpa [MulAut.conj] using hz_eq.symm
      have hzmem : (s : G)⁻¹ * x * (s : G) ∈ H ⊓ H.map (MulAut.conj (a : G)).toMonoidHom :=
        ⟨hzH, hzmap⟩
      have hz_one : (s : G)⁻¹ * x * (s : G) = 1 := by
        have hbot_mem : (s : G)⁻¹ * x * (s : G) ∈ (⊥ : Subgroup G) := by
          rwa [hbot_a] at hzmem
        exact by simpa using hbot_mem
      have hx_one : x = 1 := by
        calc
          x = (s : G) * ((s : G)⁻¹ * x * (s : G)) * (s : G)⁻¹ := by
                group
          _ = 1 := by simp [hz_one]
      simpa [hx_one]
    · exact bot_le

end

end Subgroup
