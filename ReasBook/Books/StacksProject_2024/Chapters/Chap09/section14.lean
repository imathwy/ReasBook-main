import Mathlib
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_14_1 (from Chap09) -/
/- Domain-style sampling for Definition 9.14.1:
- primary domain: purely inseparable algebraic elements and purely inseparable field extensions;
- sampled owner declarations:
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem`,
  `IsPurelyInseparable`,
  `isPurelyInseparable_iff_pow_mem`,
  `isPurelyInseparable_self`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `IsPurelyInseparable F K`, while the simple-extension theorem
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem` gives the source's
  one-element criterion without introducing a second owner;
- primitive data: none locally, since both the extension predicate and its simple-extension /
  pointwise characterizations are already owned upstream in mathlib;
- derived API: the source-style power-membership criteria for simple and general extensions, plus
  the trivial-extension instance.

Source/core/bridge triage:
- `source-facing`: the textbook notions "an element is purely inseparable over `F`" and "the
  extension `K/F` is purely inseparable";
- `core/canonical`: `IsPurelyInseparable`;
- `bridge/view`: the power-membership characterization theorems for simple extensions and general
  extensions, together with the trivial-extension instance.

This file should therefore remain a pure recall surface. Any local wrapper or restated owner
declaration would only duplicate the existing mathlib API without adding new mathematics. -/

/- Definition 9.14.1 (1): for `α ∈ K`, the textbook notion that `α` is purely inseparable over
`F` is canonically expressed by the simple extension `F⟮α⟯ / F` being purely inseparable. In
exponential characteristic `q`, the source criterion that `α ^ (q ^ n) ∈ F` for some `n` is
exactly `IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem`. -/
recall IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem

/- Definition 9.14.1 (2): in characteristic `p > 0`, the textbook notion that the extension `K/F`
is purely inseparable is the canonical mathlib typeclass `IsPurelyInseparable F K`. -/
recall IsPurelyInseparable

/- Companion recall for Definition 9.14.1 (2): in exponential characteristic `q`, the textbook
pointwise condition that every element of `K` has some `q^n`-th power in `F` is exactly the
canonical characterization `isPurelyInseparable_iff_pow_mem`. -/
recall isPurelyInseparable_iff_pow_mem

/- Companion recall for the convention following Definition 9.14.1: in arbitrary characteristic,
the trivial extension `F / F` is canonically purely inseparable, via `isPurelyInseparable_self`. -/
recall isPurelyInseparable_self

/-! ### Lemma_9_14_2 (from Chap09) -/
/- Domain-style sampling:
* primary domain: irreducibility criteria for binomials `X ^ p - C a` over a field;
* sampled owner declarations:
  `X_pow_sub_C_irreducible_of_prime`,
  `X_pow_sub_C_irreducible_iff_of_prime`,
  `pow_ne_of_irreducible_X_pow_sub_C`,
  `root_X_pow_sub_C_pow`;
* best owner abstraction: the mathlib theorem `X_pow_sub_C_irreducible_of_prime`;
* primitive data: a field `F`, a prime `p`, an element `a : F`, and the hypothesis that `a` is
  not a `p`th power;
* derived API: the irreducibility of `X ^ p - C a`.

Layer triage:
* `core/canonical`: this file is just the canonical irreducibility theorem for `X ^ p - C a`;
* `bridge/view`: the textbook wording adds a characteristic-`p` hypothesis, but that assumption is
  redundant for the actual owner theorem and should not survive as primitive public API.

So this item should be a direct recall of the owner theorem, not a parallel local wrapper with a
weaker proof route.
-/

/- Lemma 9.14.2: if `F` has characteristic `p` and `t` has no `p`th root in `F`, then
`X ^ p - C t` is irreducible over `F`. Mathlib proves the stronger canonical statement without the
characteristic-`p` assumption, namely `X_pow_sub_C_irreducible_of_prime`. -/
recall X_pow_sub_C_irreducible_of_prime

/-! ### Lemma_9_14_3 (from Chap09) -/
/- Lemma 9.14.3: after Definition 9.14.1 fixes the owner notion of a purely inseparable
extension as `IsPurelyInseparable`, the textbook tower statement is exactly the canonical
transitivity theorem `IsPurelyInseparable.trans`. -/
recall IsPurelyInseparable.trans

/-! ### Lemma_9_14_4 (from Chap09) -/
universe u v

section

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]

/- Domain-style sampling:
* primary domain: relative perfect closures and purely inseparable intermediate subextensions;
* sampled owner declarations:
  `perfectClosure`,
  `le_perfectClosure_iff`,
  `IntermediateField.isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one`;
* best owner abstraction: the canonical intermediate field `perfectClosure k E`, already tagged in
  mathlib with Stacks `09HH`;
* primitive data: none locally, since the owner object and its canonical characterizations already
  exist upstream;
* derived API: the elementwise simple-extension criterion is recovered from the owner theorem
  `le_perfectClosure_iff` together with the standard simple-extension bridge, so it should not be
  the main public entry here.

Layer triage:
* `source-facing`: Lemma 9.14.4 identifies the subextension of `E / k` consisting of the elements
  purely inseparable over `k`;
* `core/canonical`: `perfectClosure k E`;
* `bridge/view`: membership and simple-extension characterizations of `perfectClosure`.

This file should therefore be a recall surface for the canonical owner `perfectClosure`, not a
local theorem whose statement hides that owner behind an elementwise reformulation.
-/

/- Lemma 9.14.4: the subextension of `E / k` consisting of the elements of `E` that are purely
inseparable over `k` is the canonical intermediate field `perfectClosure k E`. -/
#check perfectClosure k E

end

/- Companion recall: `perfectClosure k E` is the owner-level relative perfect closure, and the
source elementwise criterion is a derived bridge rather than the main declaration of this item. -/
recall perfectClosure

/-! ### Lemma_9_14_5 (from Chap09) -/
universe u v

section

variable {F : Type u} {E : Type u} [Field F] [Field E] [Algebra F E]
open scoped IntermediateField

/- Domain-style sampling:
* primary domain: finite purely inseparable towers built by successive simple adjunctions;
* sampled owner declarations:
  `IntermediateField.adjoin`,
  `F⟮α⟯`,
  `IsPurelyInseparable.minpoly_eq_X_sub_C_pow`,
  `finrank_adjoin_simple_eq_one_iff`;
* best owner abstraction: the source-facing finite stage tower formed by adjoining the prefix of a
  tuple of generators, built directly from `IntermediateField.adjoin`;
* primitive data: a finite generator family `α : Fin n → E` and its induced intermediate-field
  tower;
* derived API: the degree-`p` conclusion and the “not already a `p`th power in the previous stage”
  clause for each successive simple adjunction.

Layer triage:
* `source-facing`: this theorem's existence of a finite generator tower with successive degree-`p`
  steps;
* `core/canonical`: mathlib's purely inseparable simple-extension owners and finrank lemmas;
* `bridge/view`: the theorem packages those single-step canonical facts along the prefix-adjoin
  tower, without introducing a separate generated-extension package.
-/

/-- The subset of `E` consisting of the entries of `α` whose indices are strictly before `i`. -/
def finiteGeneratorPrefix {n : ℕ} (α : Fin n → E) (i : Fin (n + 1)) : Set E :=
  {x | ∃ j : Fin n, j.1 < i.1 ∧ α j = x}

/-- The intermediate field generated over `F` by the entries of `α` strictly before `i`. -/
def finiteGeneratorStage (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (α : Fin n → E) (i : Fin (n + 1)) : IntermediateField F E :=
  IntermediateField.adjoin F (finiteGeneratorPrefix α i)

/-- A finite generator family whose prefix-adjoin stages form successive degree-`p` purely
inseparable simple extensions and generate all of `E`. -/
class IsPthRootTower (F : Type u) {E : Type v} [Field F] [Field E] [Algebra F E]
    (p : ℕ) {n : ℕ} (α : Fin n → E) : Prop where
  /-- The full generator family spans the whole extension field. -/
  stage_top :
    finiteGeneratorStage F α (Fin.last n) = ⊤
  /-- Each successive simple adjunction has relative degree `p`. -/
  relfinrank_eq (i : Fin n) :
    (finiteGeneratorStage F α (Fin.castSucc i)).relfinrank
      (finiteGeneratorStage F α (Fin.succ i)) = p
  /-- Each chosen generator has its `p`th power in the previous stage. -/
  pth_power_mem (i : Fin n) :
    α i ^ p ∈ finiteGeneratorStage F α (Fin.castSucc i)
  /-- No chosen generator is already a `p`th power in the previous stage. -/
  not_pth_power (i : Fin n) :
    ¬ ∃ β : finiteGeneratorStage F α (Fin.castSucc i),
      (β : E) ^ p = α i ^ p

/-- Helper for Lemma 9.14.5: when the extension has degree `1`, the empty generating family
already forms a `p`th-root tower. -/
lemma empty_pth_root_tower_of_finrank_one
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (p : ℕ)
    (hKL : Module.finrank K L = 1) :
    ∃ α : Fin 0 → L, IsPthRootTower K p α := by
  refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The only stage of the empty family is the bottom field, so degree `1` forces it to be top.
  simpa [finiteGeneratorStage, finiteGeneratorPrefix] using
    (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).2 hKL
  -- There are no transition stages in an empty family.
  intro i
  exact Fin.elim0 i
  -- There are no generators, so the `p`th-power condition is vacuous.
  intro i
  exact Fin.elim0 i
  -- There are no generators, so the non-`p`th-power condition is also vacuous.
  intro i
  exact Fin.elim0 i

/-- Helper for Lemma 9.14.5: a simple purely inseparable step of degree `p` strictly decreases
the remaining ambient degree. -/
lemma finrank_tail_lt_of_degree_p_step
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime]
    [FiniteDimensional K L] (β : L) (hβ : Module.finrank K K⟮β⟯ = p) :
    Module.finrank K⟮β⟯ L < Module.finrank K L := by
  -- Multiplicativity of finite dimension identifies the ambient degree with `p` times the tail.
  have hmul : Module.finrank K K⟮β⟯ * Module.finrank K⟮β⟯ L = Module.finrank K L :=
    Module.finrank_mul_finrank K K⟮β⟯ L
  rw [hβ] at hmul
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpos : 0 < Module.finrank K⟮β⟯ L := Module.finrank_pos
  calc
    Module.finrank K⟮β⟯ L < p * Module.finrank K⟮β⟯ L := by
      simpa [mul_comm] using (lt_mul_of_one_lt_right hpos hp)
    _ = Module.finrank K L := by simpa using hmul

/-- Helper for Lemma 9.14.5: a nontrivial finite purely inseparable extension contains an element
whose simple adjunction has degree exactly `p`, with `p`th power in the base field but no `p`th
root there. -/
lemma exists_degree_p_simple_step_of_nontrivial
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hKL : 1 < Module.finrank K L) :
    ∃ β : L,
      Module.finrank K K⟮β⟯ = p ∧
      β ^ p ∈ (⊥ : IntermediateField K L) ∧
      ¬ ∃ γ : (⊥ : IntermediateField K L), (γ : L) ^ p = β ^ p := by
  classical
  have hexp_pos : 0 < IsPurelyInseparable.exponent K L := by
    by_contra hexp_zero
    have hexp_zero' : IsPurelyInseparable.exponent K L = 0 := by
      exact le_antisymm (Nat.le_of_not_gt hexp_zero) (Nat.zero_le _)
    have hbot_top : (⊥ : IntermediateField K L) = ⊤ := by
      apply IntermediateField.bot_eq_top_of_finrank_adjoin_eq_one
      intro x
      have hx_range : x ∈ (algebraMap K L).range := by
        simpa [hexp_zero'] using (IsPurelyInseparable.exponent_def' (K := K) (L := L) p x)
      exact (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := K) (E := L) (α := x)).2 <|
        by simpa [IntermediateField.mem_bot] using hx_range
    have hfinrank_one : Module.finrank K L = 1 :=
      (IntermediateField.bot_eq_top_iff_finrank_eq_one (F := K) (E := L)).1 hbot_top
    omega
  have hpred :
      IsPurelyInseparable.exponent K L - 1 < IsPurelyInseparable.exponent K L := by
    omega
  obtain ⟨a, ha_not_range⟩ :=
    IsPurelyInseparable.exponent_min' (K := K) (L := L) p hpred
  let e : ℕ := IsPurelyInseparable.exponent K L
  haveI : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  let β : L := iterateFrobenius L p (e - 1) a
  have hβ_not_bot : β ∉ (⊥ : IntermediateField K L) := by
    simpa [β, e, iterateFrobenius_def, IntermediateField.mem_bot] using ha_not_range
  have he_succ : 1 + (e - 1) = e := by
    omega
  have hβ_pow_mem_range : β ^ p ∈ (algebraMap K L).range := by
    -- One more `p`-power lands in the base field by the definition of the extension exponent.
    have hpow :
        iterateFrobenius L p e a ∈ (algebraMap K L).range := by
      simpa [e, iterateFrobenius_def] using
        (IsPurelyInseparable.exponent_def' (K := K) (L := L) p a)
    have hfrobenius :
        frobenius L p (iterateFrobenius L p (e - 1) a) = iterateFrobenius L p e a := by
      calc
        frobenius L p (iterateFrobenius L p (e - 1) a)
            = iterateFrobenius L p 1 (iterateFrobenius L p (e - 1) a) := by
                rw [iterateFrobenius_one]
        _ = iterateFrobenius L p (1 + (e - 1)) a := by
              rw [iterateFrobenius_add_apply]
        _ = iterateFrobenius L p e a := by rw [he_succ]
    rw [← hfrobenius] at hpow
    simpa [β, frobenius_def] using hpow
  have hβ_pow_mem_bot : β ^ p ∈ (⊥ : IntermediateField K L) := by
    simpa [IntermediateField.mem_bot] using hβ_pow_mem_range
  have hβ_elemExponent_le_one : IsPurelyInseparable.elemExponent K β ≤ 1 :=
    IsPurelyInseparable.elemExponent_le_of_pow_mem' (K := K) (L := L) p (by
      simpa using hβ_pow_mem_range)
  have hβ_elemExponent_ne_zero : IsPurelyInseparable.elemExponent K β ≠ 0 := by
    intro hzero
    have hβ_range : β ∈ (algebraMap K L).range := by
      simpa [hzero] using (IsPurelyInseparable.elemExponent_def' (K := K) (L := L) p β)
    exact hβ_not_bot <| by simpa [IntermediateField.mem_bot] using hβ_range
  have hβ_elemExponent_one : IsPurelyInseparable.elemExponent K β = 1 := by
    omega
  refine ⟨β, ?_, hβ_pow_mem_bot, ?_⟩
  -- Exponent `1` forces the minimal polynomial to have degree exactly `p`.
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral β),
    IsPurelyInseparable.minpoly_natDegree_eq' (K := K) (L := L) p β, hβ_elemExponent_one, pow_one]
  -- A `p`th root in the base field would equal `β` by injectivity of Frobenius.
  rintro ⟨γ, hγ⟩
  have hγ_eq : (γ : L) = β := by
    exact (frobenius L p).injective (by simpa [frobenius_def] using hγ)
  exact hβ_not_bot (show β ∈ (⊥ : IntermediateField K L) from by simpa [hγ_eq] using γ.2)

/-- Helper for Lemma 9.14.5: after prepending `β`, the prefix before `Fin.succ j` consists of
`β` together with the old prefix before `j`. -/
lemma finiteGeneratorPrefix_cons_succ
    {n : ℕ} (β : E) (γ : Fin n → E) (j : Fin (n + 1)) :
    finiteGeneratorPrefix (Fin.cons β γ) (Fin.succ j) =
      insert β (finiteGeneratorPrefix γ j) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    -- Split the contributing index into the new head or a tail index.
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · exact Set.mem_insert _ _
    · right
      refine ⟨k, ?_, by simp [Fin.cons_succ]⟩
      simpa using hi
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · -- The prepended head always appears in the first nonempty prefix.
      exact ⟨0, by simp, by simp [Fin.cons_zero]⟩
    · rcases hx with ⟨k, hk, rfl⟩
      -- Tail generators keep the same relative order after the prepended head.
      refine ⟨Fin.succ k, ?_, by simp [Fin.cons_succ]⟩
      simpa using hk

/-- Helper for Lemma 9.14.5: after adjoining the prepended head `β`, every later stage is the
old `F⟮β⟯`-stage viewed by restriction of scalars back to `F`. -/
lemma finiteGeneratorStage_prepend_eq_restrictScalars
    {n : ℕ} (β : E) (γ : Fin n → E) (j : Fin (n + 1)) :
    finiteGeneratorStage F (Fin.cons β γ) (Fin.succ j) =
      (finiteGeneratorStage F⟮β⟯ γ j).restrictScalars F := by
  -- Rewrite the new prefix set as adjoining `β` plus the old prefix generators.
  rw [finiteGeneratorStage, finiteGeneratorPrefix_cons_succ (β := β) (γ := γ) (j := j)]
  rw [show insert β (finiteGeneratorPrefix γ j) = ({β} : Set E) ∪ finiteGeneratorPrefix γ j by
    ext x
    simp]
  rw [IntermediateField.adjoin_union]
  -- Restricting the `F⟮β⟯`-adjoin stage back to `F` produces the same `F`-adjoin.
  simpa [finiteGeneratorStage] using
    (IntermediateField.restrictScalars_adjoin_eq_sup (F := F) (K := F⟮β⟯)
      (S := finiteGeneratorPrefix γ j)).symm

/-- Helper for Lemma 9.14.5: after prepending `β`, the first nontrivial stage is exactly the
simple adjunction `F⟮β⟯`. -/
lemma finiteGeneratorStage_prepend_zero
    {n : ℕ} (β : E) (γ : Fin n → E) :
    finiteGeneratorStage F (Fin.cons β γ) (Fin.succ (0 : Fin (n + 1))) = F⟮β⟯ := by
  -- The first nonempty prefix contains only the prepended head `β`.
  rw [finiteGeneratorStage, finiteGeneratorPrefix_cons_succ (β := β) (γ := γ)
    (j := (0 : Fin (n + 1)))]
  -- Adjoining that singleton prefix is exactly the simple generated intermediate field.
  simp [finiteGeneratorPrefix]

-- Proof sketch: argue by induction on `[E : F]`. If `E = F`, take the empty generating family.
-- Otherwise choose `α ∈ E \ F` with `α ^ p ∈ F` but `α` not a `p`th power in `F`, so
-- `F⟮α⟯ / F` has degree `p`; then apply the induction hypothesis to `E / F⟮α⟯` and concatenate
-- the resulting generators.
/-- Helper for Lemma 9.14.5: strong induction on the ambient degree builds the desired
sequence of degree-`p` purely inseparable simple steps. -/
theorem exists_pthRoot_tower_of_finite_purelyInseparable_aux
    {K : Type v} {L : Type v} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [FiniteDimensional K L] [IsPurelyInseparable K L] :
    ∃ (n : ℕ) (α : Fin n → L), IsPthRootTower K p α := by
  generalize hd : Module.finrank K L = d
  induction d using Nat.strongRecOn generalizing K L with
  | ind d ih =>
      by_cases hKL : Module.finrank K L = 1
      · -- Degree `1` is the trivial tower: the empty family already spans the extension.
        obtain ⟨α, hα⟩ := empty_pth_root_tower_of_finrank_one (K := K) (L := L) p hKL
        exact ⟨0, α, hα⟩
      · have hlt : 1 < Module.finrank K L := by
          have hpos : 0 < Module.finrank K L := Module.finrank_pos
          omega
        obtain ⟨β, hβ_deg, hβ_mem, hβ_not_pth⟩ :=
          exists_degree_p_simple_step_of_nontrivial (K := K) (L := L) p hlt
        let M : IntermediateField K L := K⟮β⟯
        have htail : Module.finrank M L < d := by
          rw [← hd]
          simpa [M] using
            finrank_tail_lt_of_degree_p_step (K := K) (L := L) p β hβ_deg
        -- The recursive step is over the intermediate base field `M = K⟮β⟯`.
        letI : CharP M p := IntermediateField.charP (F := K) (E := L) (L := M) p
        obtain ⟨n, γ, hγ⟩ := ih (Module.finrank M L) htail (K := M) (L := L) rfl
        let α : Fin (n + 1) → L := Fin.cons β γ
        refine ⟨n + 1, α, ?_⟩
        refine
          { stage_top := ?_
            relfinrank_eq := ?_
            pth_power_mem := ?_
            not_pth_power := ?_ }
        · -- The concatenated tower reaches the top because the recursive tail already does over `M`.
          rw [← Fin.succ_last, finiteGeneratorStage_prepend_eq_restrictScalars (F := K)
            (β := β) (γ := γ) (j := Fin.last n)]
          simpa using congrArg (fun S => S.restrictScalars K) hγ.stage_top
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · -- The first step is exactly the simple degree-`p` adjunction `K ⊆ K⟮β⟯`.
            rw [show finiteGeneratorStage K α (Fin.castSucc (0 : Fin (n + 1))) = ⊥ by
              simp [α, finiteGeneratorStage, finiteGeneratorPrefix]]
            rw [show finiteGeneratorStage K α (Fin.succ (0 : Fin (n + 1))) = M by
              simpa [α, M] using
                finiteGeneratorStage_prepend_zero (F := K) (β := β) (γ := γ)]
            rw [IntermediateField.relfinrank_bot_left]
            simpa [M] using hβ_deg
          · -- Every later step is inherited from the recursive tower after stage normalization.
            rw [show finiteGeneratorStage K α (Fin.castSucc (Fin.succ j)) =
                (finiteGeneratorStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    finiteGeneratorStage_prepend_eq_restrictScalars (F := K) (β := β) (γ := γ)
                      (j := Fin.castSucc j)]
            rw [show finiteGeneratorStage K α (Fin.succ (Fin.succ j)) =
                (finiteGeneratorStage M γ (Fin.succ j)).restrictScalars K by
                  simpa [α] using
                    finiteGeneratorStage_prepend_eq_restrictScalars (F := K) (β := β) (γ := γ)
                      (j := Fin.succ j)]
            simpa using hγ.relfinrank_eq j
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · -- The chosen head `β` has its `p`th power in the base field by construction.
            simpa [α, finiteGeneratorStage, finiteGeneratorPrefix] using hβ_mem
          · -- Tail `p`th-power membership is exactly the recursive condition over `M`.
            rw [show finiteGeneratorStage K α (Fin.castSucc (Fin.succ j)) =
                (finiteGeneratorStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    finiteGeneratorStage_prepend_eq_restrictScalars (F := K) (β := β) (γ := γ)
                      (j := Fin.castSucc j)]
            simpa [α] using hγ.pth_power_mem j
        · intro i
          obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
          · -- The first adjoined root was chosen not to be a `p`th power in the base field.
            simpa [α, finiteGeneratorStage, finiteGeneratorPrefix] using hβ_not_pth
          · -- Tail non-`p`th-power witnesses transfer unchanged under restriction of scalars.
            rw [show finiteGeneratorStage K α (Fin.castSucc (Fin.succ j)) =
                (finiteGeneratorStage M γ (Fin.castSucc j)).restrictScalars K by
                  simpa [α] using
                    finiteGeneratorStage_prepend_eq_restrictScalars (F := K) (β := β) (γ := γ)
                      (j := Fin.castSucc j)]
            simpa [α] using hγ.not_pth_power j

/-- Lemma 9.14.5: a finite purely inseparable extension of characteristic `p > 0` admits a finite
generating family whose successive stages are degree-`p` extensions obtained by adjoining
`p`th roots of elements from the previous stage that are not already `p`th powers there. -/
theorem exists_pthRoot_tower_of_finite_purelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP F p] [FiniteDimensional F E] [IsPurelyInseparable F E] :
    ∃ (n : ℕ) (α : Fin n → E), IsPthRootTower F p α := by
  -- Invoke the universe-polymorphic strong-induction helper at the current extension.
  simpa using
    exists_pthRoot_tower_of_finite_purelyInseparable_aux (K := F) (L := E) p

end

/-! ### Lemma_9_14_6 (from Chap09) -/
/- Lemma 9.14.6: for an algebraic field extension `E / F`, the unique subextension `E / E_{sep} / F`
with `E_{sep} / F` separable and `E / E_{sep}` purely inseparable is the canonical intermediate
field `separableClosure F E`; equivalently, an intermediate field `L` has these two properties
exactly when `L = separableClosure F E`. This is the canonical theorem
`eq_separableClosure_iff`. -/
recall eq_separableClosure_iff

/-! ### Definition_9_14_7 (from Chap09) -/
universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

namespace FieldExtensionDegree
end FieldExtensionDegree

/- Domain-style sampling for Definition 9.14.7:
- primary domain: separable closure and separable / inseparable degrees of field extensions;
- sampled owner declarations:
  `separableClosure`,
  `eq_separableClosure_iff`,
  `Field.sepDegree`,
  `Field.insepDegree`;
- best owner abstraction: the textbook degrees are canonically owned by the mathlib declarations
  `Field.sepDegree F E` and `Field.insepDegree F E`, both defined from the intermediate field
  `separableClosure F E` identified in Lemma 9.14.6;
- primitive data: none locally, since the underlying intermediate field and both degree
  constructions are already owned upstream in mathlib;
- derived API: the bridge from the textbook subextension `E_sep` to `separableClosure F E` comes
  from Lemma 9.14.6 via `eq_separableClosure_iff`, while later tower laws and finite-degree
  consequences are downstream theorems on `Field.sepDegree` and `Field.insepDegree`.

Source/core/bridge triage:
- `source-facing`: the textbook separable degree `[E : F]_s = [E_sep : F]` and inseparable degree
  `[E : F]_i = [E : E_sep]`;
- `core/canonical`: `Field.sepDegree F E` and `Field.insepDegree F E`;
- `bridge/view`: Lemma 9.14.6, which identifies the source field `E_sep` with the canonical owner
  `separableClosure F E`.

This file should therefore remain a pure recall surface. Any local abbreviation or restated degree
definition would only duplicate the existing owner declarations. -/

/- Definition 9.14.7: the textbook separable degree notation `[E : F]_s` is the canonical owner
`Field.sepDegree F E`. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]_s" => Field.sepDegree F E

/- Companion notation: the textbook inseparable degree notation `[E : F]_i` is the canonical owner
`Field.insepDegree F E`. -/
scoped[FieldExtensionDegree] notation:max "[" E " : " F "]_i" => Field.insepDegree F E

open scoped FieldExtensionDegree

/- Source-facing checks: the textbook degree notations `[E : F]_s` and `[E : F]_i` denote the
canonical cardinal-valued degree owners. -/
#check ([E : F]_s : Cardinal)
#check ([E : F]_i : Cardinal)

/- Definition 9.14.7: for an algebraic field extension `E / F`, with `E_sep` identified in
Lemma 9.14.6 as `separableClosure F E`, the textbook separable degree `[E : F]_s = [E_sep : F]`
is the canonical mathlib notion `Field.sepDegree F E`. -/
recall Field.sepDegree

/- Companion recall: for the same extension, the textbook inseparable degree `[E : F]_i =
[E : E_sep]` is the canonical mathlib notion `Field.insepDegree F E`. -/
recall Field.insepDegree

/-! ### Lemma_9_14_8 (from Chap09) -/
universe u v

section

open scoped FieldExtensionDegree

variable {F : Type u} {K : Type v}
variable [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/- Domain-style sampling for Lemma 9.14.8:
- primary domain: finite field extensions, separable degree, and counting `F`-algebra
  morphisms into an algebraic closure;
- sampled owner declarations:
  `Field.sepDegree`,
  `Field.sepDegree_le_rank`,
  `Cardinal.cast_toNat_of_lt_aleph0`,
  `Field.finSepDegree_eq`,
  `Field.finSepDegree_eq_of_isAlgClosed`;
- best owner abstraction: the chapter owner notation `[K : F]_s`, i.e. the canonical cardinal
  owner `Field.sepDegree F K` introduced in Definition 9.14.7;
- primitive data: only the finite extension `K/F`;
- derived API: the finite count of `F`-algebra morphisms `K →ₐ[F] AlgebraicClosure F`,
  obtained by passing through the auxiliary numerical bridge `Field.finSepDegree F K` and then
  identifying `[K : F]_s` with its finite `toNat`.

Source/core/bridge triage:
- `source-facing`: the finite-extension formula that the separable degree `[K : F]_s` equals the
  number of `F`-algebra morphisms from `K` to an algebraic closure of `F`;
- `core/canonical`: the chapter owner `[K : F]_s = Field.sepDegree F K`;
- `bridge/view`: `Field.finSepDegree_eq` and `Field.finSepDegree_eq_of_isAlgClosed`, together with
  the finiteness bridge `Cardinal.cast_toNat_of_lt_aleph0`.

This file should therefore keep the source-facing finite theorem on `[K : F]_s`, not collapse it
to the auxiliary numerical theorem whose main owner is `Field.finSepDegree`.
-/

/-- Helper for Lemma 9.14.8: the separable degree cardinal of a finite extension is finite. -/
lemma sepDegree_lt_aleph0_of_finiteDimensional :
    [K : F]_s < Cardinal.aleph0 := by
  -- The separable degree is bounded by the rank, and finite-dimensionality makes the rank finite.
  exact (Field.sepDegree_le_rank F K).trans_lt (Module.rank_lt_aleph0 F K)

/-- Helper for Lemma 9.14.8: `Field.finSepDegree` is the finite cardinality of `[K : F]_s`. -/
lemma sepDegree_toNat_eq_finSepDegree :
    Cardinal.toNat [K : F]_s = Field.finSepDegree F K := by
  -- This is the canonical bridge from the separable degree cardinal to a natural number.
  simpa using (Field.finSepDegree_eq F K).symm

/-- Lemma 9.14.8: for a finite extension `K/F`, the separable degree `[K : F]_s` equals the
number of `F`-algebra morphisms from `K` to an algebraic closure of `F`. -/
theorem sepDegree_eq_natCard_algHom :
    [K : F]_s = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
  -- First realize the separable degree as a finite cardinal.
  calc
    [K : F]_s = Cardinal.toNat [K : F]_s := by
      -- Finite-dimensionality guarantees that the separable degree cardinal is finite.
      symm
      exact Cardinal.cast_toNat_of_lt_aleph0
        (sepDegree_lt_aleph0_of_finiteDimensional (F := F) (K := K))
    -- Next pass to the canonical numerical owner `Field.finSepDegree`.
    _ = Field.finSepDegree F K := by
      simpa using congrArg (fun n : ℕ ↦ (n : Cardinal.{v}))
        (sepDegree_toNat_eq_finSepDegree (F := F) (K := K))
    -- Finally identify that numerical invariant with the number of embeddings into
    -- an algebraic closure.
    _ = Nat.card (K →ₐ[F] AlgebraicClosure F) := by
      simpa using Field.finSepDegree_eq_of_isAlgClosed F K (AlgebraicClosure F)

end

/-! ### Lemma_9_14_9_Multiplicativity (from Chap09) -/
/- Domain-style sampling for Lemma 9.14.9:
- primary domain: separable and inseparable degrees in towers of field extensions;
- sampled owner declarations:
  `Field.sepDegree`,
  `Field.insepDegree`,
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic`,
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- best owner abstraction: the canonical mathlib tower-law owners
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- primitive data: only a tower `F ⟶ E ⟶ K` and the algebraicity of the middle extension `E / F`;
- derived API: the textbook display order `[K : F]_s = [K : E]_s [E : F]_s` and
  `[K : F]_i = [K : E]_i [E : F]_i`, obtained from the canonical owners by symmetry and
  commutativity of cardinal multiplication.

Source/core/bridge triage:
- `source-facing`: the textbook multiplicativity formulas written in degree notation;
- `core/canonical`: the mathlib tower laws
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- `bridge/view`: only the harmless reordering of factors into the textbook display order.

This file should therefore be pure canonical recall. Keeping local wrapper theorems here would
duplicate the owner declarations without adding new mathematics.
-/

/- Lemma 9.14.9 (Multiplicativity) (1): the canonical owner for separable-degree multiplicativity
in a tower `K / E / F` is `Field.sepDegree_mul_sepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]_s * [K : E]_s = [K : F]_s` is exactly the
textbook formula up to symmetry and commutativity. -/
recall Field.sepDegree_mul_sepDegree_of_isAlgebraic

/- Lemma 9.14.9 (Multiplicativity) (2): the canonical owner for inseparable-degree multiplicativity
in a tower `K / E / F` is `Field.insepDegree_mul_insepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]_i * [K : E]_i = [K : F]_i` is exactly the
textbook formula up to symmetry and commutativity. -/
recall Field.insepDegree_mul_insepDegree_of_isAlgebraic
