import StacksProject_2024.Chap09.Situation_9_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open Situation_9_12_7
open scoped Situation_9_12_7

noncomputable section

universe u v w

namespace Situation_9_12_7

section

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable (F)
variable (α : Fin n → K)

local notation "K[" i "]" => stage F α i
local notation "P[" i "]" => P[F, α; i]

/- Domain-style sampling:
* primary domain: towers of simple field extensions, transported minimal polynomials, and the
  canonical simple-adjoin embedding API;
* sampled owner declarations:
  `K[F, α; i]`,
  `P[F, α; i]`,
  `IntermediateField.algHomAdjoinIntegralEquiv`,
  `IntermediateField.equivOfEq`;
* best owner abstraction: the source-facing tuple predicate should be built from the successive
  root clauses for the chapter owner polynomials `P[F, α; i]`, while the corresponding stage
  embeddings are derived recursively from those clauses through the canonical simple-adjoin owner;
* primitive data: only the transported root conditions for the tuple `β`;
* derived API: the recursively constructed family of stage embeddings and the resulting bijection
  with `F`-algebra embeddings `K →ₐ[F] L`.
-/

-- Proof sketch: unfold the source-facing stage as an adjoin of the empty prefix of generators.
/-- The zeroth stage in the generator tower is the base field. -/
theorem stage_zero_eq_bot : K[(0 : Fin (n + 1))] = (⊥ : IntermediateField F K) := sorry

-- Proof sketch: compare the prefix of generators at `i + 1` with the previous prefix plus
-- the single new generator `α i`.
/-- The successor stage is obtained by adjoining the next generator to the preceding stage. -/
theorem stage_succ_eq_adjoin (i : Fin n) :
    K[i.succ] =
      (IntermediateField.adjoin K[i.castSucc] ({α i} : Set K)).restrictScalars F := sorry

private noncomputable def stageZeroEmbedding : K[(0 : Fin (n + 1))] →ₐ[F] L :=
  (Algebra.ofId F L).comp
    (((IntermediateField.equivOfEq (stage_zero_eq_bot F α)).trans
      (IntermediateField.botEquiv F K)).toAlgHom)

private noncomputable def successiveRootDataAux (m : ℕ) (hm : m ≤ n) (β : Fin n → L) :
    Σ p : Prop, p → K[⟨m, Nat.lt_succ_of_le hm⟩] →ₐ[F] L := by
  classical
  exact match m with
  | 0 => ⟨True, fun _ ↦ stageZeroEmbedding F α⟩
  | k + 1 =>
      let hk : k ≤ n := Nat.le_of_succ_le hm
      let i : Fin n := ⟨k, Nat.lt_of_succ_le hm⟩
      let prev := successiveRootDataAux k hk β
      let rootProp : Prop :=
        if hp : prev.1 then
          ((P[i]).map (prev.2 hp).toRingHom).IsRoot (β i)
        else
          False
      ⟨prev.1 ∧ rootProp, fun h ↦
        let hp : prev.1 := h.1
        let ψ := prev.2 hp
        let _ : Algebra K[i.castSucc] L := ψ.toRingHom.toAlgebra
        let _ : IsScalarTower F K[i.castSucc] L :=
          IsScalarTower.of_algebraMap_eq' (ψ.comp_algebraMap_of_tower F).symm
        let _ : Module.Finite K[i.castSucc] K := FiniteDimensional.right F K[i.castSucc] K
        let hαi : IsIntegral K[i.castSucc] (α i) :=
          (Algebra.IsIntegral.of_finite K[i.castSucc] K).isIntegral (α i)
        have hroot : ((P[i]).map ψ.toRingHom).IsRoot (β i) := by
          dsimp [rootProp] at h
          simpa [hp] using h.2
        have hroot' : Polynomial.aeval (β i) (P[i]) = 0 := by
          change Polynomial.eval₂ ψ.toRingHom (β i) (P[i]) = 0
          rw [Polynomial.eval₂_eq_eval_map]
          simpa [Polynomial.IsRoot] using hroot
        let ψ' :=
          (IntermediateField.algHomAdjoinIntegralEquiv K[i.castSucc] hαi).symm
            ⟨β i, mem_aroots.mpr ⟨minpoly.ne_zero hαi, hroot'⟩⟩
        (ψ'.restrictScalars F).comp
          (IntermediateField.equivOfEq (stage_succ_eq_adjoin F α i)).toAlgHom⟩

private noncomputable def successiveRootData (i : Fin (n + 1)) (β : Fin n → L) :
    Σ p : Prop, p → K[i] →ₐ[F] L := by
  cases i with
  | mk m hm =>
      simpa [stage] using successiveRootDataAux F α m (Nat.le_of_lt_succ hm) β

/-- The stagewise root condition from Lemma 9.12.8 up to stage `i`: recursively adjoining
`β 0, ..., β (i - 1)` yields stage embeddings `φ_j`, and at each successor step `β j` is a root
of the transported polynomial `P_j` over the preceding embedding. -/
def IsSuccessiveRootTupleUpTo (i : Fin (n + 1)) (β : Fin n → L) : Prop :=
  (successiveRootData F α i β).1

/-- The recursively constructed stage embedding `φ_i : K_i → L` attached to a tuple satisfying the
stagewise root conditions up to `i`. -/
noncomputable def stageEmbedding (i : Fin (n + 1)) (β : Fin n → L)
    (hβ : IsSuccessiveRootTupleUpTo F α i β) :
    K[i] →ₐ[F] L :=
  (successiveRootData F α i β).2 hβ

/-- The successor-stage root clause for the tuple `β` at stage `i`: once the previous stage
embedding `K_i →ₐ[F] L` has been recursively constructed, the next coordinate `β i` is a root of
the transported polynomial `P_i`. -/
def IsRootAtStage (i : Fin n) (β : Fin n → L) : Prop :=
  ∀ hβ : IsSuccessiveRootTupleUpTo F α i.castSucc β,
    ((P[i]).map (stageEmbedding F α i.castSucc β hβ).toRingHom).IsRoot (β i)

/-- The initial stage condition is empty. -/
@[simp] theorem isSuccessiveRootTupleUpTo_zero (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α 0 β := sorry

-- Proof sketch: unfold the recursive construction at the base stage.
/-- The initial stage embedding is the canonical base embedding `F →ₐ[F] L`. -/
@[simp] theorem stageEmbedding_zero (β : Fin n → L)
    (hβ : IsSuccessiveRootTupleUpTo F α 0 β) :
    stageEmbedding F α 0 β hβ = stageZeroEmbedding F α := sorry

-- Proof sketch: the recursive predicate is proof-irrelevant, so the constructed embedding does
-- not depend on the particular proof of the stage condition.
@[simp] theorem stageEmbedding_congr {i : Fin (n + 1)} {β : Fin n → L}
    {hβ hβ' : IsSuccessiveRootTupleUpTo F α i β} :
    stageEmbedding F α i β hβ = stageEmbedding F α i β hβ' := sorry

-- Proof sketch: unfold one step of the recursive auxiliary construction and simplify the
-- conditional carrying the previous-stage proof.
private theorem successiveRootDataAux_succ_exists_iff
    (k : ℕ) (hm : k + 1 ≤ n) (β : Fin n → L) :
    (successiveRootDataAux F α (k + 1) hm β).1 ↔
      ∃ hprev : (successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).1,
        ((P[⟨k, Nat.lt_of_succ_le hm⟩]).map
          ((successiveRootDataAux F α k (Nat.le_of_succ_le hm) β).2 hprev).toRingHom).IsRoot
          (β ⟨k, Nat.lt_of_succ_le hm⟩) := sorry

-- Proof sketch: specialize the auxiliary successor characterization to the finite index `i`.
private theorem isSuccessiveRootTupleUpTo_succ_exists_iff (i : Fin n) (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α i.succ β ↔
      ∃ hprev : IsSuccessiveRootTupleUpTo F α i.castSucc β,
        ((P[i]).map (stageEmbedding F α i.castSucc β hprev).toRingHom).IsRoot (β i) := sorry

-- Proof sketch: combine the previous-stage existence with proof-irrelevance of the recursively
-- constructed embedding.
/-- The recursive stage condition at `k + 1` says that the previous stage has already been built
and that `β k` is a root of the transported polynomial `P_k` over the preceding stage embedding
`φ_k`. -/
theorem isSuccessiveRootTupleUpTo_succ_iff (i : Fin n) (β : Fin n → L) :
    IsSuccessiveRootTupleUpTo F α i.succ β ↔
      IsSuccessiveRootTupleUpTo F α i.castSucc β ∧ IsRootAtStage F α i β := sorry

/-- A tuple `β` satisfies the successive root conditions of Lemma 9.12.8 if its full stagewise
construction reaches stage `n`. This is the concise chapter shorthand for the recursive owner
predicate `IsSuccessiveRootTupleUpTo`. -/
abbrev IsSuccessiveRootTuple (β : Fin n → L) : Prop :=
  IsSuccessiveRootTupleUpTo F α (Fin.last n) β

end

end Situation_9_12_7

section

variable (F : Type u) (K : Type v) (L : Type w)
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
variable [FiniteDimensional F K]
variable {n : ℕ}

variable {F K}
variable {L}

-- Proof sketch: transport each minimal-polynomial relation along the algebra homomorphism.
/-- Evaluating an `F`-algebra embedding `K → L` on the chosen generators produces a
tuple satisfying the successive root conditions. The algebraic-closure case from the source is a
specialization of this canonical statement. -/
lemma algHom_isSuccessiveRootTuple (α : Fin n → K) (φ : K →ₐ[F] L) :
    IsSuccessiveRootTuple F α (φ ∘ α) := sorry

-- Proof sketch: construct the inverse map recursively along the stage tower using the root
-- conditions and the simple-adjoin universal property, then use the top-stage hypothesis.
/-- Lemma 9.12.8: evaluating an `F`-algebra embedding `K → L` on the chosen generators gives a
bijection from embeddings of `K` into `L` to the subtype of tuples satisfying the successive root
conditions for the polynomials `P_i`. The source's algebraic-closure formulation is the special
case where `L` is an algebraic closure of `F`. -/
lemma embeddingTuple_bijective (α : Fin n → K)
    (hα : K[F, α; Fin.last n] = ⊤) :
    Function.Bijective
      (fun φ : K →ₐ[F] L ↦
        (⟨φ ∘ α, algHom_isSuccessiveRootTuple α φ⟩ :
          {β : Fin n → L // IsSuccessiveRootTuple F α β})) := sorry

end
