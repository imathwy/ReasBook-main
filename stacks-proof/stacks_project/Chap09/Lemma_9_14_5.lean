import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
