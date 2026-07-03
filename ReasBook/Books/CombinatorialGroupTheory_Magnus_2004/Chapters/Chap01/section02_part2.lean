import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_2_25 (from Items/Chap01) -/
section

variable {F : Type u} [Group F] {ι : Type*}

/-- The diagonal conjugation action on a family of generated subgroups recovers the textbook
simultaneous conjugation-into predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: the diagonal `ConjAct F` action on `ι → Subgroup F`, together with the
-- pointwise order on that family.
theorem exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le
    (U V : ι → Finset F) :
    (∃ g : ConjAct F,
      g • (fun i ↦ Subgroup.closure (U i : Set F)) ≤ fun i ↦ Subgroup.closure (V i : Set F)) ↔
      ∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.ofConjAct g, ?_⟩
    intro i
    simpa [generated_subgroup_conjugate_into_by, Pi.smul_apply,
      toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.toConjAct g, ?_⟩
    intro i
    simpa [generated_subgroup_conjugate_into_by, Pi.smul_apply,
      toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i

/-- The diagonal conjugation action on a family of generated subgroups recovers the textbook
simultaneous exact-conjugacy predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: `orbitRel (ConjAct F) (ι → Subgroup F)`.
theorem exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel
    (U V : ι → Finset F) :
    orbitRel (ConjAct F) (ι → Subgroup F)
      (fun i ↦ Subgroup.closure (V i : Set F))
      (fun i ↦ Subgroup.closure (U i : Set F)) ↔
      ∃ g : F, ∀ i,
        MulAut.conj g • Subgroup.closure (U i : Set F) = Subgroup.closure (V i : Set F) := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.ofConjAct g, ?_⟩
    intro i
    simpa [Pi.smul_apply, toConjAct_smul_subgroup_eq_mulAut_conj_smul] using congrFun hg i
  · rintro ⟨g, hg⟩
    refine ⟨ConjAct.toConjAct g, ?_⟩
    exact funext fun i ↦ by
      simpa [Pi.smul_apply, toConjAct_smul_subgroup_eq_mulAut_conj_smul] using hg i

end

noncomputable section

private def finsetLetters {ι : Type*} [DecidableEq ι] {F : Type*} [Group F]
    (basis : FreeGroupBasis ι F) (U : Finset F) : List ι :=
  U.toList.flatMap fun u ↦ (basis.repr u).toWord.map Prod.fst

private def signedLetters {ι : Type*} (letters : List ι) : List (ι × Bool) :=
  List.flatMap (fun a ↦ [(a, false), (a, true)]) letters

private def wordsOfLength {ι : Type*} (letters : List ι) : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      List.flatMap
        (fun w ↦ (signedLetters letters).map fun a ↦ a :: w)
        (wordsOfLength letters n)

private def searchBound {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] (U : Finset F) : ℕ :=
  U.sum fun u ↦ FreeGroup.norm (basis.repr u)

private def candidateWords {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] (U : Finset F) : List (List (ι × Bool)) :=
  List.flatMap (wordsOfLength (finsetLetters basis U)) (List.range (searchBound basis U + 1))

private def candidateElements {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] [DecidableEq F] (U : Finset F) : Finset F :=
  ((candidateWords basis U).map fun w ↦ basis.repr.symm (FreeGroup.mk w)).toFinset

private def candidateTuples {ι : Type*} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] [DecidableEq F] (U : Finset F) (n : ℕ) : Finset (Fin n → F) := by
  classical
  let _ : Fintype {x // x ∈ candidateElements basis U} := by infer_instance
  exact
    (Finset.univ : Finset (Fin n → {x // x ∈ candidateElements basis U})).image fun f i ↦
      (f i : F)

private def tupleBasisOfClosure {F : Type u} [Group F] {n : ℕ} (u : Fin n → F) : Prop :=
  IsFreeGroupBasis {x : Subgroup.closure (Set.range u) | (x : F) ∈ Set.range u}

private def tuplePresentsGeneratedSubgroup {F : Type u} [Group F] {n : ℕ}
    (U : Finset F) (u : Fin n → F) : Prop :=
  tupleBasisOfClosure u ∧ Subgroup.closure (Set.range u) = Subgroup.closure (U : Set F)

private def tupleLiesInGeneratedSubgroup {F : Type u} [Group F] {n : ℕ}
    (V : Finset F) (v : Fin n → F) : Prop :=
  ∀ i, v i ∈ Subgroup.closure (V : Set F)

private def appendTuplePair {F : Type*} [Group F]
    (uv₁ : Σ m, (Fin m → F) × (Fin m → F))
    (uv₂ : Σ n, (Fin n → F) × (Fin n → F)) :
    Σ p, (Fin p → F) × (Fin p → F) :=
  match uv₁, uv₂ with
  | ⟨m, uv₁⟩, ⟨n, uv₂⟩ =>
      ⟨m + n, (Fin.append uv₁.1 uv₂.1, Fin.append uv₁.2 uv₂.2)⟩

section Search

variable {ι : Type*} [DecidableEq ι] {F : Type u} [Group F] [IsFreeGroup F]

private noncomputable def candidateTuplePairsInto (basis : FreeGroupBasis ι F)
    [DecidableEq F] (U V : Finset F) : List (Σ m, (Fin m → F) × (Fin m → F)) := by
  classical
  exact
    (List.range (U.card + 1)).flatMap fun m ↦
      (((candidateTuples basis U m).product (candidateTuples basis V m)).toList).filterMap fun uv ↦
        letI := generated_subgroup_membership_decidable V
        if tuplePresentsGeneratedSubgroup U uv.1 ∧ tupleLiesInGeneratedSubgroup V uv.2 then
          some ⟨m, (uv.1, uv.2)⟩
        else
          none

private noncomputable def candidateTuplePairsEq (basis : FreeGroupBasis ι F)
    [DecidableEq F] (U V : Finset F) : List (Σ m, (Fin m → F) × (Fin m → F)) := by
  classical
  exact
    (List.range (Nat.min U.card V.card + 1)).flatMap fun m ↦
      (((candidateTuples basis U m).product (candidateTuples basis V m)).toList).filterMap fun uv ↦
        if tuplePresentsGeneratedSubgroup U uv.1 ∧ tuplePresentsGeneratedSubgroup V uv.2 then
          some ⟨m, (uv.1, uv.2)⟩
        else
          none

private noncomputable def familyTuplePairsInto (basis : FreeGroupBasis ι F) [DecidableEq F] :
    List (Finset F × Finset F) → List (Σ m, (Fin m → F) × (Fin m → F))
  | [] => [⟨0, (Fin.elim0, Fin.elim0)⟩]
  | (U, V) :: UVs =>
      (candidateTuplePairsInto basis U V).flatMap fun head ↦
        (familyTuplePairsInto basis UVs).map fun tail ↦ appendTuplePair head tail

private noncomputable def familyTuplePairsEq (basis : FreeGroupBasis ι F) [DecidableEq F] :
    List (Finset F × Finset F) → List (Σ m, (Fin m → F) × (Fin m → F))
  | [] => [⟨0, (Fin.elim0, Fin.elim0)⟩]
  | (U, V) :: UVs =>
      (candidateTuplePairsEq basis U V).flatMap fun head ↦
        (familyTuplePairsEq basis UVs).map fun tail ↦ appendTuplePair head tail

private noncomputable def generatedSubgroupFamilyConjugateIntoSearch {n : ℕ}
    (basis : FreeGroupBasis ι F) [DecidableEq F] (U V : Fin n → Finset F) : Bool := by
  classical
  exact
    (familyTuplePairsInto basis ((List.finRange n).map fun i ↦ (U i, V i))).any fun
      | ⟨_, uv⟩ =>
          letI := exists_common_conjugator_decidable uv.1 uv.2
          decide (∃ g : F, ∀ i, g⁻¹ * uv.1 i * g = uv.2 i)

private noncomputable def generatedSubgroupFamilyConjugateSearch {n : ℕ}
    (basis : FreeGroupBasis ι F) [DecidableEq F] (U V : Fin n → Finset F) : Bool := by
  classical
  exact
    (familyTuplePairsEq basis ((List.finRange n).map fun i ↦ (U i, V i))).any fun
      | ⟨_, uv⟩ =>
          letI := exists_common_conjugator_decidable uv.1 uv.2
          decide (∃ g : F, ∀ i, g⁻¹ * uv.1 i * g = uv.2 i)

private theorem exists_conjugator_for_generated_subgroup_family_le_iff_search_true
    (basis : FreeGroupBasis ι F) [DecidableEq F] {n : ℕ} (U V : Fin n → Finset F) :
    (∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i)) ↔
      generatedSubgroupFamilyConjugateIntoSearch basis U V = true := by
  sorry

private theorem generated_subgroup_family_conjugate_iff_search_true
    (basis : FreeGroupBasis ι F) [DecidableEq F] {n : ℕ} (U V : Fin n → Finset F) :
    orbitRel (ConjAct F) (Fin n → Subgroup F)
      (fun i ↦ Subgroup.closure (V i : Set F))
      (fun i ↦ Subgroup.closure (U i : Set F)) ↔
      generatedSubgroupFamilyConjugateSearch basis U V = true := by
  sorry

end Search

section Decidable

variable {F : Type u} [Group F] [IsFreeGroup F] {ι : Type*} [Fintype ι]

private theorem exists_forall_iff_exists_forall_reindex {α ι κ : Type*} (e : ι ≃ κ)
    (P : α → ι → Prop) :
    (∃ a : α, ∀ i : ι, P a i) ↔ ∃ a : α, ∀ j : κ, P a (e.symm j) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun j ↦ ha (e.symm j)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i ↦ by simpa using ha (e i)⟩

/-- Proposition 1-2-25 (1): in a free group, it is decidable whether one element conjugates each
generated subgroup `U i` into the corresponding generated subgroup `V i` for a finite family.

This public API keeps the source-facing family predicate. Its implementation searches finite tuple
presentations of the finitely generated subgroups `Gp(U i)` and uses the chapter owner abstraction
`exists_common_conjugator_decidable` to test whether one conjugator works for the concatenated
tuple family. The search only uses letters that actually occur in the finite input subsets, so no
ambient finite-rank hypothesis appears in the public statement. The companion bridge theorem
`exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le` identifies the
proposition with the canonical diagonal `ConjAct F` action on the family of generated subgroups. -/
-- Layer: `source-facing`.
-- `core/canonical`: the diagonal `ConjAct F` action on `ι → Subgroup F`.
-- `bridge/view`: `exists_conjugator_for_generated_subgroup_family_le_iff_exists_smul_le`.
noncomputable def exists_conjugator_for_generated_subgroup_family_le_decidable
    (U V : ι → Finset F) :
    Decidable (∃ g : F, ∀ i, generated_subgroup_conjugate_into_by g (U i) (V i)) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq F
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U' : Fin (Fintype.card ι) → Finset F := fun i ↦ U (e.symm i)
  let V' : Fin (Fintype.card ι) → Finset F := fun i ↦ V (e.symm i)
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  exact
    decidable_of_iff
      (generatedSubgroupFamilyConjugateIntoSearch basis U' V' = true)
      ((exists_forall_iff_exists_forall_reindex e
          (fun g i ↦ generated_subgroup_conjugate_into_by g (U i) (V i))).trans
        (exists_conjugator_for_generated_subgroup_family_le_iff_search_true basis U' V')).symm

/-- Proposition 1-2-25 (2): in a free group, it is decidable whether the family of generated
subgroups attached to `U` and `V` are simultaneously conjugate for a finite family.

This public statement is centered on the canonical diagonal conjugation-action orbit relation on
`ι → Subgroup F`. As above, the implementation searches finite tuple presentations of the
input-generated subgroups and delegates the common-conjugator test to the chapter's tuple owner
abstraction. The Lean owner here remains the orbit predicate itself; the companion bridge theorem
`exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel` recovers the textbook
existential formulation. -/
-- Layer: `source-facing` exact conjugacy through the owner relation on families of subgroups.
-- `core/canonical`: `orbitRel (ConjAct F) (ι → Subgroup F)`.
-- `bridge/view`: `exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel`.
noncomputable def generated_subgroup_family_conjugate_decidable
    (U V : ι → Finset F) :
    Decidable
      (orbitRel (ConjAct F) (ι → Subgroup F)
        (fun i ↦ Subgroup.closure (V i : Set F))
        (fun i ↦ Subgroup.closure (U i : Set F))) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq F
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let U' : Fin (Fintype.card ι) → Finset F := fun i ↦ U (e.symm i)
  let V' : Fin (Fintype.card ι) → Finset F := fun i ↦ V (e.symm i)
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  have h_orbit :
      orbitRel (ConjAct F) (ι → Subgroup F)
          (fun i ↦ Subgroup.closure (V i : Set F))
          (fun i ↦ Subgroup.closure (U i : Set F)) ↔
        orbitRel (ConjAct F) (Fin (Fintype.card ι) → Subgroup F)
          (fun i ↦ Subgroup.closure (V' i : Set F))
          (fun i ↦ Subgroup.closure (U' i : Set F)) := by
    exact
      ((exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel U V).trans
        (exists_forall_iff_exists_forall_reindex e
          (fun g i ↦ ConjAct.toConjAct g • Subgroup.closure (U i : Set F) =
            Subgroup.closure (V i : Set F)))).trans
        (exists_conjugator_for_generated_subgroup_family_eq_iff_orbitRel U' V').symm
  exact
    decidable_of_iff
      (generatedSubgroupFamilyConjugateSearch basis U' V' = true)
      (h_orbit.trans (generated_subgroup_family_conjugate_iff_search_true basis U' V')).symm

end Decidable

end

/-! ### Proposition_1_2_26 (from Items/Chap01) -/
universe u

open FreeGroup
open MulAction

noncomputable section

private def tupleLetters {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) : List ι :=
  List.flatMap (fun i ↦
    ((basis.repr (u i)).toWord.map Prod.fst) ++ ((basis.repr (v i)).toWord.map Prod.fst)
  ) (List.finRange n)

private def signedLetters {ι : Type*} (letters : List ι) : List (ι × Bool) :=
  List.flatMap (fun a ↦ [(a, false), (a, true)]) letters

private def wordsOfLength {ι : Type*} (letters : List ι) : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      List.flatMap (fun w ↦ (signedLetters letters).map fun a ↦ a :: w) (wordsOfLength letters n)

private def searchBound {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) : ℕ :=
  ∑ i : Fin n, (FreeGroup.norm (basis.repr (u i)) + FreeGroup.norm (basis.repr (v i)))

private def candidateWords {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) : List (List (ι × Bool)) :=
  List.flatMap (wordsOfLength (tupleLetters basis u v)) (List.range (searchBound basis u v + 1))

private def commonConjugatorSearch {ι : Type*} [DecidableEq ι] {F : Type*} [Group F] {n : ℕ}
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) : Bool := by
  let _ : DecidableEq F := Classical.decEq F
  exact
    (candidateWords basis u v).any fun word ↦
      let w := basis.repr.symm (FreeGroup.mk word)
      decide (∀ i, w⁻¹ * u i * w = v i)

section Search

variable {ι : Type*} [DecidableEq ι] {F : Type u} [Group F] [IsFreeGroup F] {n : ℕ}

/-- Internal bounded-search specification: relative to a chosen free basis, the simultaneous
conjugacy predicate on tuples is detected by searching candidate conjugators up to the standard
length bound built from the tuple entries. -/
private theorem exists_common_conjugator_iff_search_true (basis : FreeGroupBasis ι F)
    (u v : Fin n → F) :
    (∃ w : F, ∀ i, w⁻¹ * u i * w = v i) ↔
      commonConjugatorSearch basis u v = true := by
  sorry

end Search

section

variable {F : Type u} [Group F] {n : ℕ}

/-- The diagonal conjugation action on `Fin n → F` recovers the textbook common-conjugator
predicate. -/
-- Layer: `bridge/view`.
-- `core/canonical`: `orbitRel (ConjAct F) (Fin n → F)`.
theorem exists_common_conjugator_iff_orbitRel (u v : Fin n → F) :
    orbitRel (ConjAct F) (Fin n → F) v u ↔
      ∃ w : F, ∀ i, w⁻¹ * u i * w = v i := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨ConjAct.ofConjAct g⁻¹, ?_⟩
    intro i
    simp [Pi.smul_apply, ConjAct.smul_def, mul_assoc]
  · rintro ⟨w, hw⟩
    refine ⟨ConjAct.toConjAct w⁻¹, ?_⟩
    ext i
    simpa [Pi.smul_apply, ConjAct.smul_def, mul_assoc] using hw i

private theorem orbitRel_iff_search_true {ι : Type*} [DecidableEq ι] [IsFreeGroup F]
    (basis : FreeGroupBasis ι F) (u v : Fin n → F) :
    orbitRel (ConjAct F) (Fin n → F) v u ↔ commonConjugatorSearch basis u v = true :=
  (exists_common_conjugator_iff_orbitRel u v).trans
    (exists_common_conjugator_iff_search_true basis u v)

/-- The canonical diagonal conjugation-action orbit relation on `Fin n → F` is decidable in a free
group.

This is the owner-side bounded-search decision procedure behind Proposition `1-2-26`. The
companion bridge theorem `exists_common_conjugator_iff_orbitRel` recovers the textbook
common-conjugator predicate from this canonical `orbitRel` formulation. -/
-- Layer: `core/canonical`.
noncomputable instance decidableRel_commonConjugatorOrbitRel [IsFreeGroup F] :
    DecidableRel (orbitRel (ConjAct F) (Fin n → F)) := by
  let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  intro v u
  exact
    decidable_of_iff
      (commonConjugatorSearch basis u v = true)
      (orbitRel_iff_search_true basis u v).symm

/-- Proposition 1-2-26: it is decidable whether two `n`-tuples admit a common conjugator.

The public statement keeps the source-facing free-group decision problem. Its canonical owner is
still the diagonal conjugation-action orbit relation on `Fin n → F`, exposed by the companion
bridge theorem `exists_common_conjugator_iff_orbitRel`. The bounded-search construction is exposed
owner-side through `decidableRel_commonConjugatorOrbitRel`, and this source-facing declaration is
the corresponding bridge back to the textbook existential predicate. -/
-- Layer: `source-facing`.
-- `core/canonical`: `orbitRel (ConjAct F) (Fin n → F)`.
noncomputable def exists_common_conjugator_decidable [IsFreeGroup F] (u v : Fin n → F) :
    Decidable (∃ w : F, ∀ i, w⁻¹ * u i * w = v i) :=
  decidable_of_iff
    (orbitRel (ConjAct F) (Fin n → F) v u)
    (exists_common_conjugator_iff_orbitRel u v)

end

/-! ### Proposition_1_2_27 (from Items/Chap01) -/
universe u v

noncomputable section

namespace FreeGroupBasis

variable {ι : Type v} {F : Type u} [Group F] [Finite ι]

/-
Primary domain: finite-rank free groups with a chosen basis and source-facing basis-extension
statements measured by the ambient basis length.

Layer triage:
- `source-facing`: a nonempty subset `A` contained in some free basis extends to a basis `A ∪ B`
  with the complementary basis elements no longer than elements of `A`.
- `core/canonical`: `FreeGroupBasis ι F` is the owner abstraction for the ambient basis and its
  length function, while `IsFreeGroupBasis` is the chapter owner predicate for subset-style bases.
- `bridge/view`: `FreeGroupBasis.isFreeGroupBasis_range` is the chapter bridge from an indexed
  basis to the corresponding subset basis.

Domain sampling:
1. `FreeGroupBasis.repr` is the canonical bridge from the ambient free group to the reduced-word
   model on the chosen basis.
2. `FreeGroupBasis.isFreeGroupBasis_range` in `Definition_1_1_1` is the chapter owner bridge from
   a basis to the subset-style predicate `IsFreeGroupBasis`.
3. `finset_isFreeGroupBasis_iff_card_and_closure_eq_top` in `Proposition_1_2_9` is the owner-side
   finite-rank basis criterion used downstream when the resulting basis is finite.

Primitive vs. derived:
the primitive public data are the chosen finite basis `basis`, the subset `A`, its nonemptiness,
and the hypothesis that `A` lies in some free basis. The completion set `B`, the basis property of
`A ∪ B`, and the accompanying length bounds are derived source-facing output.
-/

-- Keep the `DecidableEq` requirement local: it is only needed to form `FreeGroup.norm` on the
-- reduced words `basis.repr x`, and it should not leak into the public theorem interface.
local instance : DecidableEq ι := Classical.decEq ι

/-- Proposition 1-2-27: let `basis : FreeGroupBasis ι F` be a finite basis of the free group `F`,
and let `A` be a nonempty subset of `F` contained in some free basis. Then `F` has a basis
`A ∪ B` such that every element of `B` has `basis`-length bounded by the `basis`-length of some
element of `A`. This is the source-faithful formulation of the statement that the longest element
of `B` is no longer than the longest element of `A`. -/
-- Layer: source-facing basis-extension statement.
-- Core/canonical owner abstractions: `FreeGroupBasis` for the ambient word-length function and
-- `IsFreeGroupBasis` for the resulting basis `A ∪ B`.
-- Proof sketch: start from a basis containing `A`, Nielsen-reduce the complementary part while
-- keeping the maximal `basis`-length on `A` unchanged, and then use the chapter criterion that a
-- generating `N`-reduced set in a finite-rank free group must consist of basis elements of length
-- `1`; any longer complementary element would contradict the chosen minimal-length completion.
theorem exists_completion_with_length_bound (basis : FreeGroupBasis ι F) (A : Set F)
    (hA : A.Nonempty) (hpart : ∃ S : Set F, A ⊆ S ∧ IsFreeGroupBasis S) :
    ∃ B : Set F, IsFreeGroupBasis (A ∪ B) ∧
      ∀ b ∈ B, ∃ a ∈ A, (basis.repr b).norm ≤ (basis.repr a).norm := sorry

end FreeGroupBasis

end

/-! ### Definition_1_2_28 (from Items/Chap01) -/
universe u

variable {F : Type u} [Group F]

open CategoryTheory

namespace Subgroup

/-- Definition 1-2-28: The subgroups `F₁` and `F₂` are free factors of `F`, equivalently `F`
is the free product `F₁ * F₂`, when there are generating sets `X₁` and `X₂` with
`Subgroup.closure X₁ = F₁`, `Subgroup.closure X₂ = F₂`, `X₁ ∩ X₂ = ∅`, and `X₁ ∪ X₂` a basis of
`F`. -/
-- Layer: source-facing definition.
-- Core/canonical owner abstraction: `IsFreeGroupBasis` for the union `X₁ ∪ X₂`.
def AreFreeFactors (F₁ F₂ : Subgroup F) : Prop :=
  ∃ X₁ X₂ : Set F,
    closure X₁ = F₁ ∧ closure X₂ = F₂ ∧ Disjoint X₁ X₂ ∧ IsFreeGroupBasis (X₁ ∪ X₂)

/-- A subgroup `H` is a free factor of an overgroup `G` when `H ≤ G` and the transported subgroup
`H.subgroupOf G` has a complementary free factor inside `G`. -/
-- Layer: bridge/view from the source-facing two-factor decomposition `AreFreeFactors` to the
-- one-sided overgroup relation used throughout Hall's theorem and its corollaries.
def IsFreeFactorOf (H G : Subgroup F) : Prop :=
  H ≤ G ∧ ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K

/-- Unpack the owner relation “`H` is a free factor of `G`”. -/
theorem isFreeFactorOf_iff {H G : Subgroup F} :
    H.IsFreeFactorOf G ↔ H ≤ G ∧ ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K :=
  Iff.rfl

/-- Free-factor decompositions are symmetric in the two factors. -/
theorem AreFreeFactors.symm {F₁ F₂ : Subgroup F} :
    AreFreeFactors F₁ F₂ ↔ AreFreeFactors F₂ F₁ := by
  constructor
  · rintro ⟨X₁, X₂, hX₁, hX₂, hdisj, hbasis⟩
    refine ⟨X₂, X₁, hX₂, hX₁, hdisj.symm, ?_⟩
    exact (Set.union_comm X₁ X₂) ▸ hbasis
  · rintro ⟨X₂, X₁, hX₂, hX₁, hdisj, hbasis⟩
    refine ⟨X₁, X₂, hX₁, hX₂, hdisj.symm, ?_⟩
    exact (Set.union_comm X₂ X₁) ▸ hbasis

/-- A free-product decomposition by free factors exhibits the ambient group as free. -/
-- Proof sketch: unpack the defining generating sets `X₁` and `X₂`; their union is a free basis of
-- `F`, so `IsFreeGroupBasis.isFreeGroup` gives the desired free-group structure on the ambient
-- group.
theorem AreFreeFactors.isFreeGroup {F₁ F₂ : Subgroup F} (h : AreFreeFactors F₁ F₂) :
    IsFreeGroup F := by
  rcases h with ⟨X₁, X₂, -, -, -, hX⟩
  exact hX.isFreeGroup

/-- A free factor of an overgroup is, in particular, a subgroup of that overgroup. -/
theorem IsFreeFactorOf.le {H G : Subgroup F} (h : H.IsFreeFactorOf G) : H ≤ G :=
  h.1

/-- A free factor of an overgroup comes with a complementary free factor in that overgroup. -/
theorem IsFreeFactorOf.exists_complement {H G : Subgroup F} (h : H.IsFreeFactorOf G) :
    ∃ K : Subgroup G, AreFreeFactors (H.subgroupOf G) K :=
  h.2

/-- A subgroup of a free group admits a complementary free factor exactly when its inclusion has a
left inverse. -/
-- Layer: bridge/view from the source-facing free-factor relation to the chapter owner abstraction
-- `Function.LeftInverse` for subgroup inclusions. The categorical split-mono formulation is
-- derived from `subtype_isSplitMono_iff_exists_leftInverse`, so it is not kept as a parallel
-- primitive bridge here.
theorem exists_complement_iff_exists_leftInverse [IsFreeGroup F] (F₁ : Subgroup F) :
    (∃ F₂ : Subgroup F, AreFreeFactors F₁ F₂) ↔
      ∃ ρ : F →* F₁, Function.LeftInverse ρ F₁.subtype := by
  sorry

/-- The inclusion of either side of a free-factor decomposition is split. -/
theorem AreFreeFactors.left_isSplitMono {F₁ F₂ : Subgroup F}
    (h : AreFreeFactors F₁ F₂) : IsSplitMono (GrpCat.ofHom F₁.subtype) := by
  let _ : IsFreeGroup F := h.isFreeGroup
  rw [subtype_isSplitMono_iff_exists_leftInverse]
  exact (exists_complement_iff_exists_leftInverse F₁).mp ⟨F₂, h⟩

/-- The right-hand factor in a free-factor decomposition also has split inclusion. -/
theorem AreFreeFactors.right_isSplitMono {F₁ F₂ : Subgroup F}
    (h : AreFreeFactors F₁ F₂) : IsSplitMono (GrpCat.ofHom F₂.subtype) :=
  (AreFreeFactors.symm.mp h).left_isSplitMono

/-- If `H` is a free factor of `G`, then its inclusion into `G` is split. -/
theorem IsFreeFactorOf.isSplitMono {H G : Subgroup F} (h : H.IsFreeFactorOf G) :
    IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := by
  rcases h.exists_complement with ⟨K, hK⟩
  exact hK.left_isSplitMono

private def retractToFreeFactor {H G : Subgroup F} (h : H.IsFreeFactorOf G)
    (ρ : G →* H.subgroupOf G) : G →* H :=
  (subgroupOfEquivOfLe h.le).toMonoidHom.comp ρ

/-- A free factor of a finitely generated overgroup is finitely generated. -/
-- Layer: derived owner API for `Subgroup.IsFreeFactorOf`.
theorem IsFreeFactorOf.fg {H G : Subgroup F} [Group.FG G] (h : H.IsFreeFactorOf G) :
    Group.FG H := by
  have hsplit : IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := h.isSplitMono
  rw [subtype_isSplitMono_iff_exists_leftInverse] at hsplit
  rcases hsplit with ⟨ρ, hρ⟩
  let e : H.subgroupOf G ≃* H := subgroupOfEquivOfLe h.le
  let ρ' : G →* H := retractToFreeFactor h ρ
  have hsurj : Function.Surjective ρ' := by
    intro x
    refine ⟨(e.symm x).1, ?_⟩
    simpa using congrArg e (hρ (e.symm x))
  exact Group.fg_of_surjective hsurj

/-- A free factor of a finitely generated overgroup has rank at most that of the overgroup. -/
-- Layer: derived owner API for `Subgroup.IsFreeFactorOf`, obtained from the retraction supplied by
-- `IsFreeFactorOf.isSplitMono` and the canonical owner theorem `Group.rank_le_of_surjective`.
theorem IsFreeFactorOf.rank_le {H G : Subgroup F} [Group.FG H] [Group.FG G]
    (h : H.IsFreeFactorOf G) : Group.rank H ≤ Group.rank G := by
  have hsplit : IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := h.isSplitMono
  rw [subtype_isSplitMono_iff_exists_leftInverse] at hsplit
  rcases hsplit with ⟨ρ, hρ⟩
  let e : H.subgroupOf G ≃* H := subgroupOfEquivOfLe h.le
  let ρ' : G →* H := retractToFreeFactor h ρ
  have hsurj : Function.Surjective ρ' := by
    intro x
    refine ⟨(e.symm x).1, ?_⟩
    simpa using congrArg e (hρ (e.symm x))
  exact Group.rank_le_of_surjective ρ' hsurj

end Subgroup

/-! ### Proposition_1_2_29 (from Items/Chap01) -/
universe u v

open FreeGroup

noncomputable section

namespace Proposition_1_2_29

private def signedLetters {ι : Type*} [Fintype ι] : List (ι × Bool) :=
  ((Fintype.elems : Finset ι).toList).flatMap fun a ↦ [(a, false), (a, true)]

private def wordsOfLength {ι : Type*} [Fintype ι] : ℕ → List (List (ι × Bool))
  | 0 => [[]]
  | n + 1 =>
      (wordsOfLength n).flatMap fun w ↦ (signedLetters : List (ι × Bool)).map fun a ↦ a :: w

private def totalNormBound {ι : Type v} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [DecidableEq ι] (U : Finset F) : ℕ :=
  U.sum fun u ↦ (basis.repr u).norm

private def elementsUpToNorm {ι : Type v} {F : Type u} [Group F] (basis : FreeGroupBasis ι F)
    [Finite ι] [DecidableEq ι] [DecidableEq F] (m : ℕ) : Finset F := by
  let _ : Fintype ι := Fintype.ofFinite ι
  exact
    (((List.range (m + 1)).flatMap wordsOfLength).map fun w ↦
      basis.repr.symm (FreeGroup.mk w)).toFinset

private def boundedCompletionPairs {ι : Type v} {F : Type u} [Group F]
    (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι] [DecidableEq F] (U : Finset F) :
    Finset (Finset F × Finset F) :=
  let candidates := elementsUpToNorm basis (totalNormBound basis U)
  candidates.powerset.product candidates.powerset

private def isCompletionPair {F : Type u} [Group F] [DecidableEq F] (U : Finset F)
    (WV : Finset F × Finset F) : Prop :=
  Subgroup.closure ↑WV.1 = Subgroup.closure (↑U : Set F) ∧
    IsFreeGroupBasis (↑(WV.1 ∪ WV.2) : Set F)

private noncomputable def finset_isFreeGroupBasis_decidable {ι : Type v} {F : Type u}
    [Group F] (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι] [DecidableEq F]
    (S : Finset F) : Decidable (IsFreeGroupBasis (S : Set F)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq (Subgroup F) := Classical.decEq _
  exact
    decidable_of_iff
      (S.card = Fintype.card ι ∧ Subgroup.closure (↑S : Set F) = ⊤)
      (finset_isFreeGroupBasis_iff_card_and_closure_eq_top basis S).symm

private theorem free_factor_iff_exists_bounded_candidate_pair {ι : Type v}
    {F : Type u} [Group F] (basis : FreeGroupBasis ι F) [Finite ι] [DecidableEq ι]
    [DecidableEq F] (U : Finset F) :
    (∃ K : Subgroup F, (Subgroup.closure ↑U).AreFreeFactors K) ↔
      U = ∅ ∨
        ∃ WV ∈ boundedCompletionPairs basis U, isCompletionPair U WV := by
  sorry

end Proposition_1_2_29

open Proposition_1_2_29

section SourceFacing

variable {ι : Type v} {F : Type u} [Group F]
variable (basis : FreeGroupBasis ι F) [Finite ι]

local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq F := Classical.decEq F

/-- Proposition 1-2-29, source-facing finite criterion: for a finite subset `U` of a finitely
generated free group, the subgroup `Gp(U)` is a free factor exactly when either `U` is empty or,
after replacing `U` by a bounded generating set for the same subgroup, one can complete it to a
basis of the ambient group using only elements whose word lengths are bounded by the total
`basis`-word length of `U`. -/
-- Layer: source-facing finite criterion.
-- `core/canonical`: `Subgroup.AreFreeFactors`, `FreeGroupBasis`, and `IsFreeGroupBasis`.
theorem generated_subgroup_free_factor_iff_exists_bounded_completion (U : Finset F) :
    let m := U.sum fun u ↦ (basis.repr u).norm
    (∃ K : Subgroup F, (Subgroup.closure ↑U).AreFreeFactors K) ↔
      U = ∅ ∨
        ∃ W V : Finset F,
          Subgroup.closure ↑W = Subgroup.closure (↑U : Set F) ∧
            IsFreeGroupBasis (↑(W ∪ V) : Set F) ∧
            (∀ w ∈ W, (basis.repr w).norm ≤ m) ∧
            ∀ v ∈ V, (basis.repr v).norm ≤ m := by
  sorry

end SourceFacing

section Decidable

variable {F : Type u} [Group F] [IsFreeGroup F] [Finite (IsFreeGroup.Generators F)]

local instance : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
local instance : DecidableEq F := Classical.decEq F

/-- Proposition 1-2-29: in a finitely generated free group, free-factorhood of the subgroup
generated by a finite set is decided by the bounded finite completion criterion from the
source-facing theorem, organized around the owner relation `Subgroup.AreFreeFactors` and the
finite-rank basis criterion from Proposition 1-2-9. For the owner-level reformulation by a
left inverse to the subgroup inclusion, use
`Subgroup.exists_complement_iff_exists_leftInverse`. -/
noncomputable def generated_subgroup_free_factor_decidable (U : Finset F) :
    Decidable (∃ K : Subgroup F, (Subgroup.closure ↑U).AreFreeFactors K) := by
  let basis : FreeGroupBasis (IsFreeGroup.Generators F) F := IsFreeGroup.basis F
  letI : DecidablePred (isCompletionPair U) := fun WV ↦ by
    letI : DecidableEq (Subgroup F) := Classical.decEq _
    letI := finset_isFreeGroupBasis_decidable basis (WV.1 ∪ WV.2)
    exact instDecidableAnd
  letI : Decidable (U = ∅ ∨ ∃ WV ∈ boundedCompletionPairs basis U, isCompletionPair U WV) := by
    infer_instance
  exact
    decidable_of_iff
      (U = ∅ ∨ ∃ WV ∈ boundedCompletionPairs basis U, isCompletionPair U WV)
      (free_factor_iff_exists_bounded_candidate_pair basis U).symm

end Decidable

/-! ### Proposition_1_2_30 (from Items/Chap01) -/
universe u v

open FreeGroup

noncomputable section

variable {ι : Type v} {F : Type u} [Group F]

local instance : DecidableEq ι := Classical.decEq ι

/-!
Primary domain: conjugacy growth in free groups measured by reduced-word length.

Layer triage:
- `source-facing`: the basis-relative word-length statement for a free group with chosen basis.
- `core/canonical`: `FreeGroup.norm` on the canonical `FreeGroup ι` model.
- `bridge/view`: `FreeGroupBasis.repr` transports the source-facing formulation to that owner
  statement.

Domain sampling:
1. `FreeGroup.norm` is the owner reduced-word length function.
2. `FreeGroupBasis.repr` is the canonical equivalence from an abstract free group with chosen basis
   to the concrete `FreeGroup` model.
3. `commute_map_iff` is the owner transport lemma for commutation through the basis equivalence.

Primitive vs. derived:
- primitive public data: elements `u w` and the hypothesis `¬ Commute u w`;
- derived API: the basis-level formulation obtained by transporting the canonical `FreeGroup`
  statement through `b.repr`.
-/

namespace FreeGroup

/-- Proposition 1-2-30 on the canonical free-group model: if `u` and `w` do not commute, then
there is an integer from which onward the reduced-word lengths of the conjugates
`w^{-m} * u * w^m` form a strictly increasing sequence. -/
-- Layer: core/canonical owner statement on `FreeGroup ι`.
-- Proof sketch: first conjugate `w` to a cyclically reduced element, which does not change the
-- reduced-word lengths of the conjugates up to a bounded shift. For sufficiently large positive
-- powers, enough of the initial and terminal copies of `w` survive free reduction in
-- `w^{-m} * u * w^m`, so each successive conjugation by `w` strictly increases the reduced-word
-- length. If no such tail existed, the eventual periodicity argument from the textbook would force
-- `u` and `w` to commute, contradicting the hypothesis.
theorem exists_conjugate_power_tail_strictMono_norm_of_not_commute
    (u w : FreeGroup ι) (huw : ¬ Commute u w) :
    ∃ n : ℤ,
      StrictMono fun k : ℕ ↦
        norm (w ^ (-(n + k : ℤ)) * u * w ^ (n + k : ℤ)) := sorry

end FreeGroup

namespace FreeGroupBasis

/-- Proposition 1-2-30: if `u` and `w` do not commute in a free group, then there is an integer
from which onward the reduced-word lengths of the conjugates `w^{-m} * u * w^m` form a strictly
increasing sequence, relative to a chosen free basis. -/
-- Layer: source-facing bridge/view statement obtained from the canonical `FreeGroup` owner
-- theorem through `b.repr`.
theorem exists_conjugate_power_tail_strictMono_wordLength_of_not_commute
    (b : FreeGroupBasis ι F) (u w : F) (huw : ¬ Commute u w) :
    ∃ n : ℤ,
      StrictMono fun k : ℕ ↦
        norm (b.repr (w ^ (-(n + k : ℤ)) * u * w ^ (n + k : ℤ))) := by
  simpa [map_mul, map_zpow] using
    FreeGroup.exists_conjugate_power_tail_strictMono_norm_of_not_commute (b.repr u) (b.repr w)
      (by simpa [commute_map_iff b.repr.injective] using huw)

end FreeGroupBasis
