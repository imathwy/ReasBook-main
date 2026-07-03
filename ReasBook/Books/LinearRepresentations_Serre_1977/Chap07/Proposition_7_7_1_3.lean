import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Definition_3_3_3_1

universe u v w x

namespace Representation

section Stabilizer

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]

/-- Bridge/view: the action underlying a representation. -/
private abbrev toDistribMulAction (ρ : Representation k G V) : DistribMulAction G V where
  smul g v := ρ g v
  one_smul v := by
    change ρ 1 v = v
    exact LinearMap.congr_fun ρ.map_one v
  mul_smul g h v := by
    change ρ (g * h) v = ρ g (ρ h v)
    exact LinearMap.congr_fun (ρ.map_mul g h) v
  smul_zero g := map_zero (ρ g)
  smul_add g x y := map_add (ρ g) x y

/-- Bridge/view: scalar commutation for the pointwise action on submodules induced by `ρ`. -/
private abbrev smulCommClass (ρ : Representation k G V) :
    let _ : DistribMulAction G V := ρ.toDistribMulAction
    SMulCommClass G k V := by
  letI := ρ.toDistribMulAction
  exact ⟨fun g a v ↦ (ρ g).map_smul a v⟩

/-- The stabilizer subgroup of a submodule for the action induced by `ρ`. -/
def submoduleStabilizer (ρ : Representation k G V) (W : Submodule k V) : Subgroup G := by
  letI := ρ.toDistribMulAction
  letI : SMulCommClass G k V := ρ.smulCommClass
  letI : DistribMulAction G (Submodule k V) := Submodule.pointwiseDistribMulAction
  exact MulAction.stabilizer G W

/-- Membership in `ρ.submoduleStabilizer W` is equivalent to preserving `W` under `ρ`. -/
theorem mem_submoduleStabilizer_iff_map_eq
    (ρ : Representation k G V) (W : Submodule k V) {g : G} :
    g ∈ ρ.submoduleStabilizer W ↔ W.map (ρ g) = W := by
  letI := ρ.toDistribMulAction
  letI : SMulCommClass G k V := ρ.smulCommClass
  letI : DistribMulAction G (Submodule k V) := Submodule.pointwiseDistribMulAction
  simpa [submoduleStabilizer] using
    (show g ∈ MulAction.stabilizer G W ↔ W.map (DistribSMul.toLinearMap k V g) = W from
      Submodule.mem_stabilizer_submodule_iff_map_eq)

/-- An element of the stabilizer sends every vector of `W` back into `W`. -/
-- Proof sketch: if `h` stabilizes `W` for the induced action on submodules, then `h • v` lies in
-- `h • W = W` for every `v ∈ W`.
private theorem submoduleStabilizer_apply_mem
    (ρ : Representation k G V) (W : Submodule k V) (h : ρ.submoduleStabilizer W)
    {v : V} (hv : v ∈ W) :
    ρ h v ∈ W := by
  have hh : W.map (ρ h) = W := by
    exact (mem_submoduleStabilizer_iff_map_eq ρ W).mp h.property
  simpa [hh] using (Submodule.mem_map.mpr ⟨v, hv, rfl⟩ : ρ h v ∈ W.map (ρ h))

/-- The restricted subrepresentation carried by a submodule inside its stabilizer subgroup. -/
def stabilizedSubrepresentation
    (ρ : Representation k G V) (W : Submodule k V) :
    Subrepresentation (ρ.comp (ρ.submoduleStabilizer W).subtype) where
  toSubmodule := W
  apply_mem_toSubmodule := submoduleStabilizer_apply_mem ρ W

end Stabilizer

section TransitiveSummands

variable {k : Type u} [Semiring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommMonoid V] [Module k V]
variable {I : Type x}

variable [MulAction G I] [MulAction.IsPretransitive G I]

/-- A family of submodules is permuted by `ρ` if each group element carries `W i` onto `W (g • i)`.
-/
def PermutesSubmoduleFamily (ρ : Representation k G V) (W : I → Submodule k V) : Prop :=
  ∀ g : G, ∀ i : I, (W i).map (ρ g) = W (g • i)

end TransitiveSummands

section TransitiveSummands

variable {k : Type u} [Ring k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {I : Type x}

variable [MulAction G I] [MulAction.IsPretransitive G I]

-- Source/core/bridge triage for Proposition 7-7.1-3:
-- * source-facing: LinearRepresentations_Serre_1977's stabilizer of a chosen summand and the associated stabilizer
--   subrepresentation from which `ρ` is induced, for a family of submodules permuted by `ρ`.
-- * core/canonical owners sampled in the representation-theoretic domain:
--   `Representation.IsInducedFromSubrepresentation`, `DirectSum.iSupIndep`, and
--   `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`.
-- * primitive data: the representation `ρ`, a family of submodules `W`, the canonical internal
--   direct-sum data `iSupIndep W` and `iSup W = ⊤`, the permutation property
--   `ρ.PermutesSubmoduleFamily W`, and the chosen index `i0`.
-- * bridge/view: `ρ.submoduleStabilizer (W i0)` packages the induced `MulAction.stabilizer`
--   subgroup without leaking its implementation instances into theorem statements; the local
--   internal direct-sum owner is recovered canonically from `hindep` and `hspan`.
-- * derived API: the stabilizer subgroup `ρ.submoduleStabilizer (W i0)` and the induced
--   stabilizer subrepresentation `ρ.stabilizedSubrepresentation (W i0)`.

noncomputable section

/-- Helper for Proposition 7-7.1-3: an element lies in the stabilizer of the chosen summand exactly
when it carries that summand onto itself in the permuted family. -/
private theorem submoduleStabilizer_iff_translated_summand_eq
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hperm : ρ.PermutesSubmoduleFamily W)
    {g : G} :
    g ∈ ρ.submoduleStabilizer (W i0) ↔ W (g • i0) = W i0 := by
  -- The stabilizer condition is exactly the equality supplied by the permutation hypothesis.
  rw [mem_submoduleStabilizer_iff_map_eq]
  constructor
  · intro hg
    calc
      W (g • i0) = (W i0).map (ρ g) := (hperm g i0).symm
      _ = W i0 := hg
  · intro hg
    calc
      (W i0).map (ρ g) = W (g • i0) := hperm g i0
      _ = W i0 := hg

/-- Helper for Proposition 7-7.1-3: if the chosen summand is zero, then transitivity forces every
summand in the permuted family to be zero. -/
private theorem all_summands_eq_bot_of_chosen_eq_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hbot : W i0 = ⊥) :
    ∀ i : I, W i = ⊥ := by
  intro i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i0 i
  -- Transitivity writes `i` as a translate of `i0`, so equivariance transports the zero summand.
  rw [← hg, ← hperm g i0]
  simp [hbot]

/-- Helper for Proposition 7-7.1-3: when the chosen summand is nonzero, stabilizing that summand
is equivalent to fixing its index. -/
private theorem mem_submoduleStabilizer_iff_fix_index_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    g ∈ ρ.submoduleStabilizer (W i0) ↔ g • i0 = i0 := by
  constructor
  · intro hg
    have hEq : W (g • i0) = W i0 :=
      (submoduleStabilizer_iff_translated_summand_eq ρ W i0 hperm).mp hg
    by_contra hne_fix
    have hdisj_top : Disjoint (W i0) (⨆ (j) (_ : j ≠ i0), W j) :=
      (iSupIndep_def.mp hindep) i0
    have hle : W (g • i0) ≤ ⨆ (j) (_ : j ≠ i0), W j := by
      exact le_iSup_of_le (g • i0) <| le_iSup_of_le hne_fix le_rfl
    -- Independence makes the chosen summand disjoint from any distinct translate.
    have hdisj : Disjoint (W i0) (W (g • i0)) :=
      hdisj_top.mono_right hle
    have hself : Disjoint (W i0) (W i0) := by
      simpa [hEq] using hdisj
    exact hne (disjoint_self.mp hself)
  · intro hfix
    -- If `g` fixes the chosen index, the equivariant family equality is exactly the stabilizer
    -- condition.
    exact (submoduleStabilizer_iff_translated_summand_eq ρ W i0 hperm).mpr <| by
      simp [hfix]

/-- Helper for Proposition 7-7.1-3: the quotient-to-index map is well defined once the
submodule stabilizer agrees with the index stabilizer on the nonzero branch. -/
private theorem submoduleStabilizerQuotientToIndex_wellDefined_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    {g₁ g₂ : G}
    (hrel : QuotientGroup.leftRel (ρ.submoduleStabilizer (W i0)) g₁ g₂) :
    g₁ • i0 = g₂ • i0 := by
  have hmem : g₁⁻¹ * g₂ ∈ ρ.submoduleStabilizer (W i0) :=
    QuotientGroup.leftRel_apply.mp hrel
  have hfix : (g₁⁻¹ * g₂) • i0 = i0 :=
    (mem_submoduleStabilizer_iff_fix_index_of_ne_bot ρ W i0 hindep hperm hne (g₁⁻¹ * g₂)).mp hmem
  -- Two representatives of the same left coset differ by an element fixing `i0`.
  calc
    g₁ • i0 = g₁ • ((g₁⁻¹ * g₂) • i0) := by rw [hfix]
    _ = g₂ • i0 := by simp [mul_smul]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, a left coset of the stabilizer is sent
to the corresponding translated index. -/
private def submoduleStabilizerQuotientToIndex_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    G ⧸ ρ.submoduleStabilizer (W i0) → I :=
  Quotient.lift
    (fun g : G ↦ g • i0)
    (fun _ _ hab ↦
      submoduleStabilizerQuotientToIndex_wellDefined_of_ne_bot ρ W i0 hindep hperm hne hab)

@[simp] private theorem submoduleStabilizerQuotientToIndex_of_ne_bot_mk
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne
        (g : G ⧸ ρ.submoduleStabilizer (W i0)) =
      g • i0 :=
  by
    simp [submoduleStabilizerQuotientToIndex_of_ne_bot]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, the quotient-to-index map is injective
because equal translates differ by an element fixing the chosen index. -/
private theorem submoduleStabilizerQuotientToIndex_injective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Injective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) := by
  intro q₁ q₂ hq
  revert hq
  refine Quotient.inductionOn₂' q₁ q₂ ?_
  intro g₁ g₂ hq_mk
  apply QuotientGroup.eq.mpr
  have hq_smul : g₁ • i0 = g₂ • i0 := by
    simpa using hq_mk
  have hfix : (g₁⁻¹ * g₂) • i0 = i0 := by
    -- Equal images in the quotient map mean the relative element fixes `i0`.
    calc
      (g₁⁻¹ * g₂) • i0 = g₁⁻¹ • (g₂ • i0) := by rw [mul_smul]
      _ = g₁⁻¹ • (g₁ • i0) := by rw [← hq_smul]
      _ = i0 := by simp
  exact
    (mem_submoduleStabilizer_iff_fix_index_of_ne_bot ρ W i0 hindep hperm hne (g₁⁻¹ * g₂)).mpr
      hfix

/-- Helper for Proposition 7-7.1-3: pretransitivity makes the quotient-to-index map surjective. -/
private theorem submoduleStabilizerQuotientToIndex_surjective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Surjective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) := by
  intro i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G i0 i
  -- Every index is a translate of `i0`, so it has a quotient representative.
  refine ⟨(g : G ⧸ ρ.submoduleStabilizer (W i0)), ?_⟩
  simpa using hg

/-- Helper for Proposition 7-7.1-3: the quotient by the stabilizer of a nonzero chosen summand is
equivalent to the index set. -/
private theorem submoduleStabilizerQuotientToIndex_bijective_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    Function.Bijective (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne) :=
  ⟨submoduleStabilizerQuotientToIndex_injective_of_ne_bot ρ W i0 hindep hperm hne,
    submoduleStabilizerQuotientToIndex_surjective_of_ne_bot ρ W i0 hindep hperm hne⟩

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, quotient cosets of the stabilizer
reindex the family of summands. -/
private noncomputable def submoduleStabilizerQuotientEquivIndex_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥) :
    G ⧸ ρ.submoduleStabilizer (W i0) ≃ I :=
  Equiv.ofBijective
    (submoduleStabilizerQuotientToIndex_of_ne_bot ρ W i0 hindep hperm hne)
    (submoduleStabilizerQuotientToIndex_bijective_of_ne_bot ρ W i0 hindep hperm hne)

@[simp] private theorem submoduleStabilizerQuotientEquivIndex_of_ne_bot_mk
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (g : G) :
    submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hne
        (g : G ⧸ ρ.submoduleStabilizer (W i0)) =
      g • i0 :=
  by
    simp [submoduleStabilizerQuotientEquivIndex_of_ne_bot]

/-- Helper for Proposition 7-7.1-3: on the nonzero branch, each left-coset translate of the
stabilized summand agrees with the corresponding original summand. -/
private theorem leftQuotientSubmodule_eq_reindexed_family_of_ne_bot
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : W i0 ≠ ⊥)
    (q : G ⧸ ρ.submoduleStabilizer (W i0)) :
    ρ.leftQuotientSubmodule
        (ρ.submoduleStabilizer (W i0))
        (ρ.stabilizedSubrepresentation (W i0))
        q =
      W (submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hne q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- The translate indexed by `gH` is just the image of `W i0` under `ρ g`, hence `W (g • i0)`.
  rw [ρ.leftQuotientSubmodule_mk]
  simpa using hperm g i0

/-- Proposition 7-7.1-3: if the submodules `W i` are independent, span `V`, and are permuted
transitively by `G`, then the chosen summand `W i0` is stable under its stabilizer subgroup, and
`ρ` is induced from the corresponding stabilizer subrepresentation. Equivalently, `V` is an
internal direct sum of the `W i`, and the family of left-coset translates of `W i0` gives that
decomposition. -/
-- Proof sketch: identify the left cosets of the stabilizer of `W i0` with the index set `I` via
-- transitivity, compare the transported copies of `W i0` with the equivariant family `W`, and
-- then transfer the internal direct-sum decomposition along that identification.
theorem
    isInducedFromSubrepresentation_submoduleStabilizer_of_indep_span_of_permuted_family
    (ρ : Representation k G V)
    (W : I → Submodule k V)
    (i0 : I)
    (hindep : iSupIndep W)
    (hspan : iSup W = ⊤)
    (hperm : ρ.PermutesSubmoduleFamily W) :
    ρ.IsInducedFromSubrepresentation
      (ρ.submoduleStabilizer (W i0))
      (ρ.stabilizedSubrepresentation (W i0)) := by
  classical
  let _ : DecidableEq (G ⧸ ρ.submoduleStabilizer (W i0)) := Classical.decEq _
  have hInternal :
      DirectSum.IsInternal
        (ρ.leftQuotientSubmodule
          (ρ.submoduleStabilizer (W i0))
          (ρ.stabilizedSubrepresentation (W i0))) := by
    by_cases hbot : W i0 = ⊥
    · -- In the degenerate branch, transitivity forces every original summand and every quotient
      -- translate to be zero.
      have hall : ∀ i : I, W i = ⊥ :=
        all_summands_eq_bot_of_chosen_eq_bot ρ W i0 hperm hbot
      have hleftbot :
          ∀ q : G ⧸ ρ.submoduleStabilizer (W i0),
            ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))
                q =
              ⊥ := by
        intro q
        refine Quotient.inductionOn' q ?_
        intro g
        rw [ρ.leftQuotientSubmodule_mk]
        change Submodule.map (ρ g) (W i0) = ⊥
        rw [hbot]
        exact Submodule.map_bot (ρ g)
      have hleftbot_fun :
          (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) =
            fun _ : G ⧸ ρ.submoduleStabilizer (W i0) ↦ (⊥ : Submodule k V) := by
        funext q
        exact hleftbot q
      have hindep_left :
          iSupIndep
            (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) := by
        -- A family of zero submodules is independent.
        rw [iSupIndep_def]
        intro q
        rw [hleftbot q]
        exact disjoint_bot_left
      have hspan_bot : iSup W = ⊥ := by
        simp [hall]
      have htopbot : (⊥ : Submodule k V) = ⊤ := by
        -- The original spanning hypothesis collapses `V` in the zero-summand branch.
        calc
          (⊥ : Submodule k V) = iSup W := hspan_bot.symm
          _ = ⊤ := hspan
      have hspan_left :
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
            ⊤ := by
        calc
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
              ⊥ := by
              rw [hleftbot_fun]
              simp
          _ = ⊤ := htopbot
      exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep_left hspan_left
    · -- On the nonzero branch, orbit-stabilizer identifies the quotient translates with the
      -- original family `W`.
      let e :=
        submoduleStabilizerQuotientEquivIndex_of_ne_bot ρ W i0 hindep hperm hbot
      have hleft :
          ∀ q : G ⧸ ρ.submoduleStabilizer (W i0),
            ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))
                q =
              W (e q) := by
        intro q
        simpa [e] using
          leftQuotientSubmodule_eq_reindexed_family_of_ne_bot ρ W i0 hindep hperm hbot q
      have hleft_fun :
          (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) =
            W ∘ e := by
        funext q
        exact hleft q
      have hindep_left :
          iSupIndep
            (ρ.leftQuotientSubmodule
              (ρ.submoduleStabilizer (W i0))
              (ρ.stabilizedSubrepresentation (W i0))) := by
        -- Reindex the original independent family along the quotient-index equivalence.
        rw [hleft_fun]
        exact hindep.comp e.injective
      have hspan_left :
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
            ⊤ := by
        calc
          iSup
              (ρ.leftQuotientSubmodule
                (ρ.submoduleStabilizer (W i0))
                (ρ.stabilizedSubrepresentation (W i0))) =
              iSup (W ∘ e) := by
              rw [hleft_fun]
          _ = iSup W := by
              simpa [Function.comp] using (Equiv.iSup_comp (g := W) e)
          _ = ⊤ := hspan
      exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep_left hspan_left
  unfold Representation.IsInducedFromSubrepresentation
  simpa using hInternal

end

end TransitiveSummands

end Representation
