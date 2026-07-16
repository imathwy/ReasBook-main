import Mathlib.CategoryTheory.Limits.Lattice
import StacksProject_2024.stacks_project.Chap20.«20_9_0_1»
import StacksProject_2024.stacks_project.Chap20.Definition_20_23_1.DeletedIndex
import StacksProject_2024.stacks_project.Chap20.Lemma_20_9_3
import StacksProject_2024.stacks_project.Chap20.OpensInstances

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

/- Domain-style sampling for Definition 20.23.1:
- primary domain: alternating Čech cochain complexes of abelian presheaves on a family of opens;
- sampled owner API:
  `cechComplexFunctor`,
  `cechTerm`,
  `cechDifferentialToFun`,
  `CochainComplex.of`;
- best owner abstraction: this item is `source-facing`, so the owner is the alternating Čech
  subcomplex itself, implemented as the canonical subgroup restriction of the ordinary Čech owner
  `(cechComplexFunctor 𝒰).obj ℱ`.

Source/core/bridge triage:
- `source-facing`: alternating Čech cochains, their restricted differential, the resulting complex,
  and its canonical inclusion into the ordinary Čech complex;
- `core/canonical`: the ordinary Čech complex `(cechComplexFunctor 𝒰).obj ℱ`;
- `bridge/view`: the tuplewise predicate `IsAlternatingCechCochain` and the inclusion map into the
  ordinary Čech complex.

Primitive data versus derived API:
- primitive data: the alternating predicate on ordinary Čech cochains;
- derived API: the alternating subgroup in each degree, the restricted differential, the resulting
  cochain complex, and its inclusion into the ordinary Čech complex. -/

/-- Permuting the indices of a Čech tuple does not change the corresponding intersection of opens. -/
theorem cechIntersection_comp_perm (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 1) → ι) (τ : Equiv.Perm (Fin (p + 1))) :
    cechIntersection 𝒰 (σ ∘ τ) = cechIntersection 𝒰 σ := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun a ↦ ?_
    simpa [cechIntersection, Function.comp] using
      (iInf_le (fun b : Fin (p + 1) ↦ 𝒰 (σ (τ b))) (τ.symm a))
  · refine le_iInf fun a ↦ ?_
    simpa [cechIntersection, Function.comp] using
      (iInf_le (fun b : Fin (p + 1) ↦ 𝒰 (σ b)) (τ a))

/-- The predicate that a degree-`p` Čech cochain is alternating: it vanishes on repeated indices
and transforms by the sign of a permutation. -/
def IsAlternatingCechCochain (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : cechTerm 𝒰 F p) : Prop :=
  (∀ σ : Fin (p + 1) → ι, ¬ Function.Injective σ → s σ = 0) ∧
    ∀ (σ : Fin (p + 1) → ι) (τ : Equiv.Perm (Fin (p + 1))),
      F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ)) =
        (Equiv.Perm.sign τ) • s σ

/-- An alternating Čech cochain vanishes on tuples with repeated indices. -/
theorem IsAlternatingCechCochain.eq_zero_of_not_injective
    {𝒰 : ι → Opens X} {F : X.Presheaf AddCommGrpCat.{max u v}} {p : ℕ}
    {s : cechTerm 𝒰 F p} (hs : IsAlternatingCechCochain 𝒰 F p s) {σ : Fin (p + 1) → ι}
    (hσ : ¬ Function.Injective σ) :
    s σ = 0 :=
  hs.1 σ hσ

/-- An alternating Čech cochain transforms by the sign of a permutation of its indices. -/
theorem IsAlternatingCechCochain.perm
    {𝒰 : ι → Opens X} {F : X.Presheaf AddCommGrpCat.{max u v}} {p : ℕ}
    {s : cechTerm 𝒰 F p} (hs : IsAlternatingCechCochain 𝒰 F p s) (σ : Fin (p + 1) → ι)
    (τ : Equiv.Perm (Fin (p + 1))) :
    F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ)) =
      (Equiv.Perm.sign τ) • s σ :=
  hs.2 σ τ

-- Proof sketch: the zero cochain vanishes on all repeated tuples and is fixed by every signed
-- permutation relation.
/-- The zero Čech cochain is alternating. -/
@[simp] theorem isAlternatingCechCochain_zero (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    IsAlternatingCechCochain 𝒰 F p 0 := by
  constructor
  · -- The zero cochain vanishes on every tuple, hence in particular on noninjective ones.
    intro σ hσ
    rfl
  · -- Every morphism of abelian groups sends zero to zero, and signed multiples of zero are zero.
    intro σ τ
    rw [Pi.zero_apply, map_zero, Pi.zero_apply]
    simp

-- Proof sketch: the alternating conditions are linear, so the sum of two alternating cochains is
-- again alternating.
/-- Alternating Čech cochains are closed under addition. -/
theorem IsAlternatingCechCochain.add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s t : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s)
    (ht : IsAlternatingCechCochain 𝒰 F p t) :
    IsAlternatingCechCochain 𝒰 F p (s + t) := by
  constructor
  · -- Vanishing on repeated tuples is preserved by pointwise addition.
    intro σ hσ
    simp [hs.eq_zero_of_not_injective hσ, ht.eq_zero_of_not_injective hσ]
  · -- The signed permutation relation is linear in the cochain value.
    intro σ τ
    calc
      F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op ((s + t) (σ ∘ τ)) =
          F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ)) +
            F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (t (σ ∘ τ)) := by
              simp [Pi.add_apply]
      _ = (Equiv.Perm.sign τ) • s σ + (Equiv.Perm.sign τ) • t σ := by
            rw [hs.perm σ τ, ht.perm σ τ]
      _ = (Equiv.Perm.sign τ) • (s + t) σ := by
            simp [Pi.add_apply]

-- Proof sketch: negation preserves both vanishing on repeated indices and the signed permutation
-- relation.
/-- Alternating Čech cochains are closed under negation. -/
theorem IsAlternatingCechCochain.neg (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) :
    IsAlternatingCechCochain 𝒰 F p (-s) := by
  constructor
  · -- Vanishing on repeated tuples is preserved by negation.
    intro σ hσ
    simp [hs.eq_zero_of_not_injective hσ]
  · -- Negation commutes with every restriction map and with integer scalar multiplication.
    intro σ τ
    simpa using congrArg Neg.neg (hs.perm σ τ)

/-- The additive subgroup of degree-`p` alternating Čech cochains. -/
private def alternatingCechTermSubgroup (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddSubgroup (cechTerm 𝒰 F p) where
  carrier := {s | IsAlternatingCechCochain 𝒰 F p s}
  zero_mem' := isAlternatingCechCochain_zero 𝒰 F p
  add_mem' hs ht := IsAlternatingCechCochain.add 𝒰 F p hs ht
  neg_mem' hs := IsAlternatingCechCochain.neg 𝒰 F p hs

/-- The degree-`p` term of the alternating Čech complex. -/
abbrev alternatingCechTerm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (alternatingCechTermSubgroup 𝒰 F p)

private theorem exists_succAbove_preimage {n : ℕ} (j i : Fin (n + 1)) (h : i ≠ j) :
    ∃ k : Fin n, j.succAbove k = i := by
  rcases lt_or_gt_of_ne h with hij | hji
  · refine ⟨i.castPred (Fin.ne_of_lt (Nat.lt_of_lt_of_le hij j.le_last)), ?_⟩
    exact Fin.succAbove_castPred_of_lt j i hij
  · refine ⟨i.pred (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hji)), ?_⟩
    exact Fin.succAbove_pred_of_lt j i hji

private theorem comp_swap_eq_self {n : ℕ} {α : Type*} (σ : Fin n → α) {a b : Fin n}
    (hab : σ a = σ b) :
    σ ∘ Equiv.swap a b = σ := by
  funext k
  simpa [Function.comp] using Equiv.apply_swap_eq_self hab k

private theorem comp_succAbove_not_injective_of_eq {n : ℕ} {α : Type*} (σ : Fin (n + 1) → α)
    {a b j : Fin (n + 1)} (hab : σ a = σ b) (hne : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    ¬ Function.Injective (σ ∘ j.succAboveEmb) := by
  intro h
  obtain ⟨a', ha'⟩ := exists_succAbove_preimage j a hja.symm
  obtain ⟨b', hb'⟩ := exists_succAbove_preimage j b hjb.symm
  have hpred : a' = b' := h <| by
    dsimp [Function.comp]
    rw [ha', hb', hab]
  exact hne <| by
    have hsucc := congrArg j.succAbove hpred
    simpa [ha', hb'] using hsucc

private theorem addCommGrpCat_eqToHom_apply {A B : AddCommGrpCat} (h : A = B) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom h)) x =
      cast (congrArg (fun Z : AddCommGrpCat ↦ ↥Z) h) x := by
  cases h
  rfl

private theorem cast_cechSection_eq (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (f : (σ : Fin (p + 1) → ι) → F.obj (op (cechIntersection 𝒰 σ)))
    {σ τ : Fin (p + 1) → ι} (h : σ = τ) :
    cast
        (congrArg
          (fun Z : AddCommGrpCat.{max u v} ↦ ↥Z)
          (congrArg (fun ν ↦ F.obj (op (cechIntersection 𝒰 ν))) h))
        (f σ) =
      f τ := by
  cases h
  rfl

-- Proof sketch: the usual Čech differential preserves vanishing on repeated indices and the sign
-- rule for permuting indices, so it restricts to the alternating subgroup.
/-- Helper for Definition 20.23.1: deleting `j` after `τ` and deleting `τ j` before the induced
deleted-index permutation give the same Čech tuple. -/
private theorem cech_deleted_tuple_perm (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 2) → ι) (τ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    cechIntersection 𝒰 (((σ ∘ τ) ∘ j.succAboveEmb)) =
      cechIntersection 𝒰 ((σ ∘ (τ j).succAboveEmb) ∘ deleted_index_perm τ j) := by
  -- Proof comment: rewrite the deleted tuple pointwise with
  -- `deleted_index_perm_comp_succAbove` and then apply `cechIntersection`.
  have hdel :
      ((σ ∘ τ) ∘ j.succAboveEmb) =
        (σ ∘ (τ j).succAboveEmb) ∘ deleted_index_perm τ j := by
    funext k
    change σ (τ (j.succAbove k)) = σ ((τ j).succAbove (deleted_index_perm τ j k))
    simpa [Function.comp] using congrArg σ (congrFun (deleted_index_perm_comp_succAbove τ j) k)
  simpa [hdel] using congrArg (cechIntersection 𝒰) hdel

/-- Helper for Definition 20.23.1: the restriction square comparing the `j`-th deleted tuple of
`σ ∘ τ` with the `(τ j)`-th deleted tuple of `σ` commutes in `Opens X`. -/
private theorem cech_restriction_transport_deleted_index_hom (𝒰 : ι → Opens X) {p : ℕ}
    (σ : Fin (p + 2) → ι) (τ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm ≫
        homOfLE (cechIntersection_le_succAbove 𝒰 (σ ∘ τ) j) ≫
        eqToHom (cech_deleted_tuple_perm 𝒰 σ τ j) =
      homOfLE (cechIntersection_le_succAbove 𝒰 σ (τ j)) ≫
        eqToHom
          (cechIntersection_comp_perm 𝒰 (σ ∘ (τ j).succAboveEmb)
            (deleted_index_perm τ j)).symm := by
  -- Proof comment: the intended proof is subsingleton elimination in the thin category `Opens X`
  -- after aligning the codomain via `deleted_index_perm_comp_succAbove`.
  exact Subsingleton.elim _ _

/-- Helper for Definition 20.23.1: after applying `F.map` to the deleted-index restriction square,
the two resulting composites agree on sections. -/
private theorem cech_restriction_transport_deleted_index
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (σ : Fin (p + 2) → ι) (τ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2))
    (x : F.obj
      (op (cechIntersection 𝒰
        (((σ ∘ (τ j).succAboveEmb) ∘ deleted_index_perm τ j))))) :
    F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
        (cechRestriction 𝒰 F (σ ∘ τ) j
          (F.map (eqToHom (cech_deleted_tuple_perm 𝒰 σ τ j)).op x)) =
      cechRestriction 𝒰 F σ (τ j)
        (F.map
          (eqToHom
            (cechIntersection_comp_perm 𝒰 (σ ∘ (τ j).succAboveEmb)
              (deleted_index_perm τ j)).symm).op x) := by
  have h :
      (eqToHom (cech_deleted_tuple_perm 𝒰 σ τ j)).op ≫
          (homOfLE (cechIntersection_le_succAbove 𝒰 (σ ∘ τ) j)).op ≫
            (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op =
        (eqToHom
            (cechIntersection_comp_perm 𝒰 (σ ∘ (τ j).succAboveEmb)
              (deleted_index_perm τ j)).symm).op ≫
          (homOfLE (cechIntersection_le_succAbove 𝒰 σ (τ j))).op := by
    exact congrArg Quiver.Hom.op
      (cech_restriction_transport_deleted_index_hom 𝒰 σ τ j)
  rw [cechRestriction]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  rw [h]

/-- Helper for Definition 20.23.1: transporting the `j`-th Čech differential summand along a
permutation rewrites it as the sign-twisted `(τ j)`-th summand. -/
private theorem cech_differential_summand_perm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) (σ : Fin (p + 2) → ι)
    (τ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
        (cechRestriction 𝒰 F (σ ∘ τ) j (s (((σ ∘ τ) ∘ j.succAboveEmb)))) =
      (Equiv.Perm.sign (deleted_index_perm τ j)) •
        cechRestriction 𝒰 F σ (τ j) (s (σ ∘ (τ j).succAboveEmb)) := by
  let σ' : Fin (p + 1) → ι := σ ∘ (τ j).succAboveEmb
  let δ : Equiv.Perm (Fin (p + 1)) := deleted_index_perm τ j
  have hdel :
      ((σ ∘ τ) ∘ j.succAboveEmb) = σ' ∘ δ := by
    funext k
    change σ (τ (j.succAbove k)) = σ ((τ j).succAbove (δ k))
    simpa [σ', δ, Function.comp] using
      congrArg σ (congrFun (deleted_index_perm_comp_succAbove τ j) k)
  have htransport :=
    cech_restriction_transport_deleted_index 𝒰 F σ τ j (s (σ' ∘ δ))
  have hperm := hs.perm σ' δ
  have hperm_restrict :
      cechRestriction 𝒰 F σ (τ j)
          (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ' δ).symm).op (s (σ' ∘ δ))) =
        (Equiv.Perm.sign δ) • cechRestriction 𝒰 F σ (τ j) (s σ') := by
    calc
      cechRestriction 𝒰 F σ (τ j)
          (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ' δ).symm).op (s (σ' ∘ δ))) =
        cechRestriction 𝒰 F σ (τ j) ((Equiv.Perm.sign δ) • s σ') := by
          rw [hperm]
      _ = (Equiv.Perm.sign δ) • cechRestriction 𝒰 F σ (τ j) (s σ') := by
          rw [Units.smul_def, Units.smul_def]
          rw [map_zsmul]
  have hsdel :
      s (((σ ∘ τ) ∘ j.succAboveEmb)) =
        F.map (eqToHom (cech_deleted_tuple_perm 𝒰 σ τ j)).op (s (σ' ∘ δ)) := by
    have hcech :
        cech_deleted_tuple_perm 𝒰 σ τ j = congrArg (cechIntersection 𝒰) hdel := by
      apply Subsingleton.elim
    rw [hcech]
    erw [eqToHom_op, eqToHom_map]
    rw [addCommGrpCat_eqToHom_apply]
    simpa using (cast_cechSection_eq 𝒰 F s hdel.symm).symm
  calc
    F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
        (cechRestriction 𝒰 F (σ ∘ τ) j (s (((σ ∘ τ) ∘ j.succAboveEmb)))) =
      F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
        (cechRestriction 𝒰 F (σ ∘ τ) j
          (F.map (eqToHom (cech_deleted_tuple_perm 𝒰 σ τ j)).op (s (σ' ∘ δ)))) := by
            rw [hsdel]
    _ = cechRestriction 𝒰 F σ (τ j)
          (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ' δ).symm).op (s (σ' ∘ δ))) := by
            dsimp [σ', δ] at htransport ⊢
            exact htransport
    _ = (Equiv.Perm.sign δ) • cechRestriction 𝒰 F σ (τ j) (s σ') := hperm_restrict
    _ = (Equiv.Perm.sign (deleted_index_perm τ j)) •
          cechRestriction 𝒰 F σ (τ j) (s (σ ∘ (τ j).succAboveEmb)) := by
            rfl

/-- Helper for Definition 20.23.1: the Čech differential of an alternating cochain satisfies the
permutation-sign rule in the next degree. -/
private theorem cech_differential_sum_reindex {p : ℕ} {A : Type*} [AddCommGroup A]
    (t : Fin (p + 2) → A) (τ : Equiv.Perm (Fin (p + 2))) :
    ∑ j : Fin (p + 2),
        ((((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ j)) • t (τ j)) =
      (Equiv.Perm.sign τ) •
        ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • t k := by
  calc
    ∑ j : Fin (p + 2),
        ((((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ j)) • t (τ j)) =
      ∑ j : Fin (p + 2), ((Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ))) • t (τ j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [deleted_index_perm_coefficient]
    _ = ∑ k : Fin (p + 2), ((Equiv.Perm.sign τ * ((-1 : ℤ) ^ (k : ℕ))) • t k) := by
          simpa using
            Equiv.sum_comp τ
              (fun k : Fin (p + 2) ↦
                ((Equiv.Perm.sign τ * ((-1 : ℤ) ^ (k : ℕ))) • t k))
    _ = (Equiv.Perm.sign τ) •
          ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • t k := by
            have h :
                (Equiv.Perm.sign τ) • ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • t k =
                  ∑ k : Fin (p + 2),
                    (Equiv.Perm.sign τ) • (((-1 : ℤ) ^ (k : ℕ)) • t k) := by
              simpa using (Finset.smul_sum : _)
            simpa [mul_smul] using h.symm

/-- Helper for Definition 20.23.1: the Čech differential of an alternating cochain satisfies the
permutation-sign rule in the next degree. -/
private theorem cechDifferential_perm_formula (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) (σ : Fin (p + 2) → ι)
    (τ : Equiv.Perm (Fin (p + 2))) :
    F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
        ((cechDifferentialToFun 𝒰 F p s) (σ ∘ τ)) =
      (Equiv.Perm.sign τ) • (cechDifferentialToFun 𝒰 F p s σ) := by
  rw [cechDifferentialToFun, map_sum]
  calc
    ∑ j : Fin (p + 2),
        F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
          (((-1 : ℤ) ^ (j : ℕ)) •
            cechRestriction 𝒰 F (σ ∘ τ) j (s (((σ ∘ τ) ∘ j.succAboveEmb)))) =
      ∑ j : Fin (p + 2),
          ((((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ j)) •
          cechRestriction 𝒰 F σ (τ j) (s (σ ∘ (τ j).succAboveEmb))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [map_zsmul, cech_differential_summand_perm 𝒰 F p hs σ τ j]
          simpa using
            (smul_smul ((-1 : ℤ) ^ (j : ℕ))
              (Equiv.Perm.sign (deleted_index_perm τ j))
              (cechRestriction 𝒰 F σ (τ j) (s (σ ∘ (τ j).succAboveEmb))))
    _ = (Equiv.Perm.sign τ) •
          ∑ k : Fin (p + 2),
            ((-1 : ℤ) ^ (k : ℕ)) •
              cechRestriction 𝒰 F σ k (s (σ ∘ k.succAboveEmb)) := by
            exact
              cech_differential_sum_reindex
                (fun k : Fin (p + 2) ↦
                  cechRestriction 𝒰 F σ k (s (σ ∘ k.succAboveEmb))) τ
    _ = (Equiv.Perm.sign τ) • (cechDifferentialToFun 𝒰 F p s σ) := by
          rfl

/-- Helper for Definition 20.23.1: if two entries of a Čech tuple coincide, then the corresponding
pair of differential summands cancel after the alternating-sign reindexing. -/
private theorem cech_differential_pair_cancel (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ} {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) (σ : Fin (p + 2) → ι)
    {a b : Fin (p + 2)} (hab : σ a = σ b) (hne : a ≠ b) :
    ((-1 : ℤ) ^ (a : ℕ)) • cechRestriction 𝒰 F σ a (s (σ ∘ a.succAboveEmb)) +
      ((-1 : ℤ) ^ (b : ℕ)) • cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) = 0 := by
  let τ : Equiv.Perm (Fin (p + 2)) := Equiv.swap a b
  have hswap : σ ∘ τ = σ := comp_swap_eq_self σ hab
  have hsummand :
      cechRestriction 𝒰 F σ a (s (σ ∘ a.succAboveEmb)) =
        (Equiv.Perm.sign (deleted_index_perm τ a)) •
          cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) := by
    have h := cech_differential_summand_perm 𝒰 F p hs σ τ a
    have hleft :
        F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
            (cechRestriction 𝒰 F (σ ∘ τ) a (s (((σ ∘ τ) ∘ a.succAboveEmb)))) =
          cechRestriction 𝒰 F σ a (s (σ ∘ a.succAboveEmb)) := by
      have hproof :
          cechIntersection_comp_perm 𝒰 σ τ = congrArg (cechIntersection 𝒰) hswap := by
        apply Subsingleton.elim
      rw [hproof]
      erw [eqToHom_op, eqToHom_map]
      rw [addCommGrpCat_eqToHom_apply]
      simpa using
        cast_cechSection_eq 𝒰 F
          (fun ν ↦ cechRestriction 𝒰 F ν a (s (ν ∘ a.succAboveEmb))) hswap
    calc
      cechRestriction 𝒰 F σ a (s (σ ∘ a.succAboveEmb)) =
        F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
          (cechRestriction 𝒰 F (σ ∘ τ) a (s (((σ ∘ τ) ∘ a.succAboveEmb)))) := hleft.symm
      _ = (Equiv.Perm.sign (deleted_index_perm τ a)) •
          cechRestriction 𝒰 F σ (τ a) (s (σ ∘ (τ a).succAboveEmb)) := h
      _ = (Equiv.Perm.sign (deleted_index_perm τ a)) •
          cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) := by
            have hτa :
                cechRestriction 𝒰 F σ (τ a) (s (σ ∘ (τ a).succAboveEmb)) =
                  cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) := by
              exact
                congrArg (fun k ↦ cechRestriction 𝒰 F σ k (s (σ ∘ k.succAboveEmb))) <|
                  by simp [τ]
            simpa [hτa]
  have hcoeff :
      (((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ a)) =
        -(((-1 : ℤ) ^ (b : ℕ))) := by
    calc
      (((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ a)) =
          Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ a : ℕ)) := by
            exact deleted_index_perm_coefficient τ a
      _ = -(((-1 : ℤ) ^ (b : ℕ))) := by
            simp [τ, Equiv.Perm.sign_swap hne]
  calc
    ((-1 : ℤ) ^ (a : ℕ)) • cechRestriction 𝒰 F σ a (s (σ ∘ a.succAboveEmb)) +
        ((-1 : ℤ) ^ (b : ℕ)) • cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) =
      (((((-1 : ℤ) ^ (a : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ a))) •
          cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb))) +
        ((-1 : ℤ) ^ (b : ℕ)) • cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) := by
          rw [hsummand, Units.smul_def, smul_smul]
    _ = (-(((-1 : ℤ) ^ (b : ℕ)))) • cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) +
        ((-1 : ℤ) ^ (b : ℕ)) • cechRestriction 𝒰 F σ b (s (σ ∘ b.succAboveEmb)) := by
          rw [hcoeff]
    _ = 0 := by
          simp [neg_smul]

/-- Helper for Definition 20.23.1: the repeated-index clause for the differential is the only
remaining alternating condition after the permutation formula is established. -/
private theorem cechDifferential_vanish_of_not_injective (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) :
    ∀ σ : Fin (p + 2) → ι, ¬ Function.Injective σ → cechDifferentialToFun 𝒰 F p s σ = 0 := by
  intro σ hσ
  rw [cechDifferentialToFun]
  simp only [Function.Injective, not_forall] at hσ
  rcases hσ with ⟨a, hσ⟩
  rcases hσ with ⟨b, hσ⟩
  rcases hσ with ⟨hab, hne⟩
  rw [← Finset.sum_add_sum_compl ({a, b} : Finset (Fin (p + 2)))]
  rw [Finset.sum_pair hne, cech_differential_pair_cancel 𝒰 F hs σ hab hne, zero_add]
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  have hnotinj : ¬ Function.Injective (σ ∘ j.succAboveEmb) :=
    comp_succAbove_not_injective_of_eq σ hab hne hj.1 hj.2
  rw [hs.eq_zero_of_not_injective hnotinj]
  rw [cechRestriction, map_zero]
  simp

/-- The ordinary Čech differential preserves alternating cochains. -/
private theorem cechDifferential_preserves_alternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) {s : cechTerm 𝒰 F p}
    (hs : IsAlternatingCechCochain 𝒰 F p s) :
    IsAlternatingCechCochain 𝒰 F (p + 1) (cechDifferentialToFun 𝒰 F p s) := by
  -- Route correction: the deleted-index permutation and coefficient bookkeeping are now separated
  -- from the owner-level transport square, so the permutation clause is proved independently of
  -- the repeated-index cancellation argument.
  constructor
  · -- The remaining open part is the direct repeated-index cancellation in the alternating sum.
    exact cechDifferential_vanish_of_not_injective 𝒰 F p hs
  · -- The signed permutation relation follows from the termwise transport and sum reindexing.
    exact cechDifferential_perm_formula 𝒰 F p hs

/-- The underlying function of the differential on the alternating Čech complex. -/
private def alternatingCechDifferentialToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechTerm 𝒰 F p → alternatingCechTerm 𝒰 F (p + 1) :=
  fun s ↦
    ⟨cechDifferentialToFun 𝒰 F p s.1,
      cechDifferential_preserves_alternating 𝒰 F p s.2⟩

-- Proof sketch: the restricted differential is induced from the additive ordinary Čech
-- differential, hence remains additive on the alternating subgroup.
/-- The alternating Čech differential is additive. -/
private theorem alternatingCechDifferentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : alternatingCechTerm 𝒰 F p) :
    alternatingCechDifferentialToFun 𝒰 F p (s + t) =
      alternatingCechDifferentialToFun 𝒰 F p s +
        alternatingCechDifferentialToFun 𝒰 F p t := by
  -- Equality in the subgroup is checked on the underlying Čech cochains.
  apply Subtype.ext
  ext σ
  exact congrFun (cechDifferentialToFun_map_add 𝒰 F p s.1 t.1) σ

/-- The degree-`p` differential in the alternating Čech complex. -/
private abbrev alternatingCechDifferential (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechTerm 𝒰 F p ⟶ alternatingCechTerm 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (alternatingCechDifferentialToFun 𝒰 F p)
      (alternatingCechDifferentialToFun_map_add 𝒰 F p))

-- Proof sketch: the restricted differential squares to zero because it is obtained by restricting
-- the ordinary Čech differential, which already satisfies `d ∘ d = 0`.
/-- Consecutive differentials in the alternating Čech complex compose to zero. -/
private theorem alternatingCechDifferential_comp_alternatingCechDifferential
    (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechDifferential 𝒰 F p ≫ alternatingCechDifferential 𝒰 F (p + 1) = 0 := by
  -- Proof comment: after forgetting the subgroup packaging, this is exactly the tuplewise
  -- square-zero identity already proved for the ordinary Čech differential.
  ext s σ
  exact congrFun (congrArg (fun f ↦ f s.1) (cechDifferential_comp_cechDifferential 𝒰 F p)) σ

/-- Definition 20.23.1: the alternating Čech complex as the alternating cochain subcomplex of the
ordinary Čech complex. -/
@[stacks 01FH]
def alternatingCechComplex (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of (alternatingCechTerm 𝒰 F) (alternatingCechDifferential 𝒰 F)
    (alternatingCechDifferential_comp_alternatingCechDifferential 𝒰 F)

/-- The alternating Čech differential evaluates by the ordinary Čech alternating-sum formula on
the underlying cochain. -/
theorem alternatingCechComplex_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (alternatingCechComplex 𝒰 F).X p) (σ : Fin (p + 2) → ι) :
    ((alternatingCechComplex 𝒰 F).d p (p + 1) s).1 σ =
      cechDifferentialToFun 𝒰 F p s.1 σ := by
  simpa [alternatingCechComplex] using
    (show ((alternatingCechDifferential 𝒰 F p) s).1 σ =
        cechDifferentialToFun 𝒰 F p s.1 σ by
      rfl)

private abbrev alternatingCechInclusionComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (alternatingCechComplex 𝒰 F).X p ⟶ ((cechComplexFunctor 𝒰).obj F).X p :=
  AddCommGrpCat.ofHom (alternatingCechTermSubgroup 𝒰 F p).subtype ≫
    (cechTermIso 𝒰 F p).inv

-- Proof sketch: the inclusion is compatible with differentials because the alternating complex was
-- defined by restricting the ordinary Čech differential.
private theorem alternatingCechInclusionComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechInclusionComponent 𝒰 F p ≫ ((cechComplexFunctor 𝒰).obj F).d p (p + 1) =
      (alternatingCechComplex 𝒰 F).d p (p + 1) ≫
        alternatingCechInclusionComponent 𝒰 F (p + 1) := by
  apply (cancel_mono (cechTermIso 𝒰 F (p + 1)).hom).1
  rw [Category.assoc, cechTermIso_comm_d, Category.assoc]
  simp only [Iso.trans_inv, eqToIso.inv, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]
  ext s σ
  have hsub :
      ((alternatingCechTermSubgroup 𝒰 F (p + 1)).subtype.comp
        (AddMonoidHom.mk' (alternatingCechDifferentialToFun 𝒰 F p)
          (alternatingCechDifferentialToFun_map_add 𝒰 F p))) s =
        cechDifferentialToFun 𝒰 F p s.1 := by
    ext τ
    rfl
  simpa [alternatingCechComplex, alternatingCechDifferential] using
    (congrArg (fun f ↦ f σ) hsub).symm

/-- Helper for Definition 20.23.1: the alternating Čech inclusion components satisfy the adjacent
degree compatibility required by `HomologicalComplex.Hom.mk`. -/
private theorem alternatingCechInclusion_hom_condition (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    ∀ i j, i + 1 = j →
      alternatingCechInclusionComponent 𝒰 F i ≫ ((cechComplexFunctor 𝒰).obj F).d i j =
        (alternatingCechComplex 𝒰 F).d i j ≫ alternatingCechInclusionComponent 𝒰 F j := by
  intro i j hij
  rcases hij with rfl
  -- Once the target degree is identified as `i + 1`, this is exactly the componentwise lemma.
  simpa using alternatingCechInclusionComponent_comm 𝒰 F i

/-- The canonical inclusion of the alternating Čech complex into the ordinary Čech complex. -/
def alternatingCechInclusion (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechComplex 𝒰 F ⟶ (cechComplexFunctor 𝒰).obj F :=
  HomologicalComplex.Hom.mk
    (alternatingCechInclusionComponent 𝒰 F)
    (alternatingCechInclusion_hom_condition 𝒰 F)

/-- The alternating Čech inclusion is the underlying alternating cochain, viewed pointwise in the
ordinary Čech complex. -/
@[simp] theorem alternatingCechInclusion_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (alternatingCechComplex 𝒰 F).X p) (σ : Fin (p + 1) → ι) :
    (cechTermIso 𝒰 F p).hom ((alternatingCechInclusion 𝒰 F).f p s) σ = s.1 σ := by
  have h :
      alternatingCechInclusionComponent 𝒰 F p ≫ (cechTermIso 𝒰 F p).hom =
        AddCommGrpCat.ofHom (alternatingCechTermSubgroup 𝒰 F p).subtype := by
    simp [alternatingCechInclusionComponent]
  exact congrArg (fun f ↦ f s σ) h

-- Proof sketch: a morphism of presheaves acts componentwise on each Čech tuple, so it preserves
-- both vanishing on repeated indices and the signed permutation relation.
/-- Componentwise application of a presheaf morphism preserves alternating Čech cochains. -/
theorem IsAlternatingCechCochain.map (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ)
    {s : cechTerm 𝒰 F p} (hs : IsAlternatingCechCochain 𝒰 F p s) :
    IsAlternatingCechCochain 𝒰 G p
      (fun σ ↦ α.app (op (cechIntersection 𝒰 σ)) (s σ)) := by
  constructor
  · -- Vanishing on repeated tuples is preserved because each component map sends zero to zero.
    intro σ hσ
    simp [hs.eq_zero_of_not_injective hσ]
  · -- The signed permutation relation is preserved by naturality of the presheaf morphism.
    intro σ τ
    have hnat :
        G.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
            (α.app (op (cechIntersection 𝒰 (σ ∘ τ))) (s (σ ∘ τ))) =
          α.app (op (cechIntersection 𝒰 σ))
            (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ))) := by
      simpa using
        congrArg (fun k ↦ k (s (σ ∘ τ)))
          ((α.naturality (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op).symm)
    calc
      G.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
          (α.app (op (cechIntersection 𝒰 (σ ∘ τ))) (s (σ ∘ τ))) =
        α.app (op (cechIntersection 𝒰 σ))
          (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op (s (σ ∘ τ))) := hnat
      _ = α.app (op (cechIntersection 𝒰 σ)) ((Equiv.Perm.sign τ) • s σ) := by
        rw [hs.perm σ τ]
      _ = (Equiv.Perm.sign τ) • α.app (op (cechIntersection 𝒰 σ)) (s σ) := by
        simp

/-- The underlying function induced in degree `p` by a morphism of presheaves on alternating
Čech cochains. -/
private def alternatingCechTermMapToFun (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ) :
    alternatingCechTerm 𝒰 F p → alternatingCechTerm 𝒰 G p :=
  fun s ↦
    ⟨fun σ ↦ α.app (op (cechIntersection 𝒰 σ)) (s.1 σ),
      IsAlternatingCechCochain.map 𝒰 α p s.2⟩

-- Proof sketch: the component maps `α.app _` are additive, and the alternating term map is
-- defined by applying them pointwise.
/-- The degreewise map induced on alternating Čech cochains by a presheaf morphism is additive. -/
private theorem alternatingCechTermMapToFun_map_add (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ)
    (s t : alternatingCechTerm 𝒰 F p) :
    alternatingCechTermMapToFun 𝒰 α p (s + t) =
      alternatingCechTermMapToFun 𝒰 α p s +
        alternatingCechTermMapToFun 𝒰 α p t := by
  -- Equality in the alternating subgroup is checked pointwise.
  apply Subtype.ext
  ext σ
  change α.app (op (cechIntersection 𝒰 σ)) ((s.1 + t.1) σ) =
      α.app (op (cechIntersection 𝒰 σ)) (s.1 σ) +
        α.app (op (cechIntersection 𝒰 σ)) (t.1 σ)
  simp

/-- The degree-`p` map on alternating Čech terms induced by a morphism of presheaves. -/
private abbrev alternatingCechTermMap (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ) :
    alternatingCechTerm 𝒰 F p ⟶ alternatingCechTerm 𝒰 G p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (alternatingCechTermMapToFun 𝒰 α p)
      (alternatingCechTermMapToFun_map_add 𝒰 α p))

-- Proof sketch: both sides are the ordinary Čech differential followed by componentwise
-- application of `α`, so naturality of the ordinary differential gives the equality.
/-- The degreewise maps induced by a presheaf morphism commute with the alternating Čech
differentials. -/
-- TODO: expand both sides on tuple coordinates, commute each restriction map with `α` by
-- naturality, and then move `α.app` across the finite alternating sum using `map_sum`.
private theorem alternatingCechTermMap_comm (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ) :
    alternatingCechTermMap 𝒰 α p ≫ alternatingCechDifferential 𝒰 G p =
      alternatingCechDifferential 𝒰 F p ≫ alternatingCechTermMap 𝒰 α (p + 1) := by
  ext s σ
  change
    ∑ j : Fin (p + 2),
        (-1 : ℤ) ^ (j : ℕ) •
          cechRestriction 𝒰 G σ j
            (α.app (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) (s.1 (σ ∘ j.succAboveEmb))) =
      α.app (op (cechIntersection 𝒰 σ))
        (∑ j : Fin (p + 2),
          (-1 : ℤ) ^ (j : ℕ) •
            cechRestriction 𝒰 F σ j (s.1 (σ ∘ j.succAboveEmb)))
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hnat :
      G.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op
          (α.app (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) (s.1 (σ ∘ j.succAboveEmb))) =
        α.app (op (cechIntersection 𝒰 σ))
          (F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op
            (s.1 (σ ∘ j.succAboveEmb))) := by
    have h :
        AddCommGrpCat.Hom.hom
            (α.app (op (cechIntersection 𝒰 (σ ∘ j.succAboveEmb))) ≫
              G.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op) =
          AddCommGrpCat.Hom.hom
            (F.map (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op ≫
              α.app (op (cechIntersection 𝒰 σ))) := by
      exact congrArg AddCommGrpCat.Hom.hom
        ((α.naturality (homOfLE (cechIntersection_le_succAbove 𝒰 σ j)).op).symm)
    exact congrArg (fun f ↦ f (s.1 (σ ∘ j.succAboveEmb))) h
  rw [hnat, cechRestriction]
  simp

/-- Helper for Definition 20.23.1: the alternating Čech term maps induced by a presheaf morphism
satisfy the adjacent-degree compatibility required by `HomologicalComplex.Hom.mk`. -/
private theorem alternatingCechComplexMap_hom_condition (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) :
    ∀ i j, i + 1 = j →
      alternatingCechTermMap 𝒰 α i ≫ (alternatingCechComplex 𝒰 G).d i j =
        (alternatingCechComplex 𝒰 F).d i j ≫ alternatingCechTermMap 𝒰 α j := by
  intro i j hij
  rcases hij with rfl
  -- After identifying the adjacent degree, this is the pointwise commutation lemma.
  simpa [alternatingCechComplex] using alternatingCechTermMap_comm 𝒰 α i

/-- The morphism of alternating Čech complexes induced by a morphism of presheaves. -/
private def alternatingCechComplexMap (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) :
    alternatingCechComplex 𝒰 F ⟶ alternatingCechComplex 𝒰 G :=
  HomologicalComplex.Hom.mk
    (alternatingCechTermMap 𝒰 α)
    (alternatingCechComplexMap_hom_condition 𝒰 α)

/-- Helper for Definition 20.23.1: the alternating Čech complex map induced by the identity
presheaf morphism is the identity chain map. -/
private theorem alternatingCechComplexMap_id (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechComplexMap 𝒰 (𝟙 F) = 𝟙 (alternatingCechComplex 𝒰 F) := by
  ext p s
  rfl

/-- Helper for Definition 20.23.1: alternating Čech complex maps respect composition of presheaf
morphisms. -/
private theorem alternatingCechComplexMap_comp (𝒰 : ι → Opens X)
    {F G H : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (β : G ⟶ H) :
    alternatingCechComplexMap 𝒰 (α ≫ β) =
      alternatingCechComplexMap 𝒰 α ≫ alternatingCechComplexMap 𝒰 β := by
  ext p s
  rfl

/-- The alternating Čech complex is functorial in the presheaf. -/
def alternatingCechComplexFunctor (𝒰 : ι → Opens X) :
    X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ where
  obj F := alternatingCechComplex 𝒰 F
  map α := alternatingCechComplexMap 𝒰 α
  map_id F := alternatingCechComplexMap_id 𝒰 F
  map_comp α β := alternatingCechComplexMap_comp 𝒰 α β

/-- The map induced by `alternatingCechComplexFunctor` acts degreewise by applying the presheaf
morphism to each Čech tuple. -/
@[simp] theorem alternatingCechComplexFunctor_map_f_apply (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (α : F ⟶ G) (p : ℕ)
    (s : (alternatingCechComplex 𝒰 F).X p) (σ : Fin (p + 1) → ι) :
    (((alternatingCechComplexFunctor 𝒰).map α).f p s).1 σ =
      α.app (op (cechIntersection 𝒰 σ)) (s.1 σ) :=
  rfl
