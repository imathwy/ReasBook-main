import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Serre.Chap04.Definition_4_12
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_14
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_15
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_16
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RepresentationTheory.Character

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Representation

/- Source/core/bridge triage:
- `source-facing`: the three clauses of Theorem 4-17 about the self-pairing `(χ | χ)_G`;
- `core/canonical`: the endomorphism-space dimension `Module.finrank ℂ (ρ.IntertwiningMap ρ)`;
- `bridge/view`: the direct-sum multiplicity formula `∑ i, m i ^ 2`, with the ordered-pair count
  retained only as an internal helper for clause (3).
-/

universe u v w w'

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]
variable {ι : Type w} [Finite ι]

-- Classical decidability is only used so the subtype indexing the ordered-pair count in (3)
-- carries the canonical finite-cardinality instances needed by `Nat.card`.
attribute [local instance] Classical.propDecidable

-- Finite index sets in this file are always handled classically.
noncomputable local instance instDecidableEqOfFinite (α : Type*) [Finite α] : DecidableEq α :=
  Classical.decEq α

/-- Helper for Theorem 4-17: each subrepresentation of a continuous representation inherits the
continuity needed to form its `L²(G)` character. -/
private theorem subrepresentation_toRepresentation_isContinuous
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : Subrepresentation ρ) :
    Representation.IsContinuous σ.toRepresentation := by
  -- The ambient continuous action restricts to each invariant subspace.
  refine Representation.isContinuous_of_continuousAction σ.toRepresentation ?_
  exact
    ((Representation.continuousAction ρ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      (fun gx ↦ σ.apply_mem_toSubmodule gx.1 gx.2.2)

/-- Helper for Theorem 4-17: the character of an internal direct sum is the sum of the characters
of its summands. -/
private theorem character_eq_sum_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i, ((σ i).toRepresentation).character := by
  classical
  -- The trace of `ρ g` decomposes as the sum of the traces on the invariant summands.
  ext g
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Theorem 4-17: the `L²(G)` characters of the summands in an internal
decomposition. -/
private abbrev summandCharacterFamily
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation)) :
    ι → G →₂[(μG : Measure G)] ℂ :=
  fun i ↦
    letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
    characterL2 ((σ i).toRepresentation)

/-- Helper for Theorem 4-17: the `L²(G)` character of an internal direct sum is the sum of the
`L²(G)` characters of its summands. -/
private theorem characterL2_eq_sum_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation)) :
    characterL2 ρ = ∑ i, summandCharacterFamily ρ σ hσcont i := by
  classical
  let χσ := summandCharacterFamily ρ σ hσcont
  -- Compare the continuous characters first, then map the equality through `ContinuousMap.toLp`.
  suffices
      hchar :
        ({ toFun := ρ.character
           continuous_toFun := continuous_character_of_isContinuousCompact (ρ := ρ) } :
            C(G, ℂ)) =
          ∑ i,
            ({ toFun := ((σ i).toRepresentation).character
               continuous_toFun := continuous_character_of_isContinuousCompact
                 (ρ := (σ i).toRepresentation) } : C(G, ℂ)) by
    simpa [χσ, summandCharacterFamily, Representation.characterL2] using
      congrArg (ContinuousMap.toLp (E := ℂ) (p := (2 : ENNReal)) (μ := μG) ℂ) hchar
  ext g
  simp [character_eq_sum_of_isInternal (ρ := ρ) (σ := σ) (hinternal := hinternal)]

/-- Helper for Theorem 4-17: the self-pairing of an internal direct sum is the sum of the
pairings with the summand characters. -/
private theorem characterPairing_self_eq_sumPairingsToSummands_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation))
    (χσ : ι → G →₂[(μG : Measure G)] ℂ)
    (hχσ : ∀ i,
      χσ i =
        (letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
         characterL2 ((σ i).toRepresentation))) :
    (characterL2 ρ | characterL2 ρ)_G = ∑ i, (characterL2 ρ | χσ i)_G := by
  classical
  have hcharSum :
      characterL2 ρ = ∑ i, χσ i := by
    calc
      characterL2 ρ =
          ∑ i,
            (letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
             characterL2 ((σ i).toRepresentation)) := by
              exact
                characterL2_eq_sum_of_isInternal
                  (ρ := ρ) (σ := σ) (hinternal := hinternal) (hσcont := hσcont)
      _ = ∑ i, χσ i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hχσ i]
  calc
    (characterL2 ρ | characterL2 ρ)_G = (characterL2 ρ | ∑ i, χσ i)_G := by
      rw [hcharSum]
    _ = ∑ i, (characterL2 ρ | χσ i)_G := by
      simpa [squareIntegrableFunctionInner_eq_inner] using
        (sum_inner (𝕜 := ℂ) (s := Finset.univ) (f := χσ) (x := characterL2 ρ))

/-- Helper for Theorem 4-17: the self-pairing of an internal direct sum equals the sum of the
pairings with the canonical `L²(G)` characters of the summands. -/
private theorem characterPairing_self_eq_sumCanonicalSummandPairings_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    (characterL2 ρ | characterL2 ρ)_G =
      ∑ i,
        (characterL2 ρ |
          summandCharacterFamily ρ σ
            (fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)) i)_G := by
  let hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation) :=
    fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)
  have hpairingsLocal :
      (characterL2 ρ | characterL2 ρ)_G =
        ∑ i, (characterL2 ρ | summandCharacterFamily ρ σ hσcont i)_G := by
    exact
      characterPairing_self_eq_sumPairingsToSummands_of_isInternal
        (ρ := ρ)
        (σ := σ)
        (hinternal := hinternal)
        (hσcont := hσcont)
        (χσ := summandCharacterFamily ρ σ hσcont)
        (hχσ := fun _ ↦ rfl)
  simpa [hσcont] using hpairingsLocal

/-- Helper for Theorem 4-17: summing the pairings against the summand characters yields the sum of
the corresponding intertwining-space dimensions. -/
private theorem sumPairingsToSummands_eq_sumFinrankIntertwining_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation))
    (χσ : ι → G →₂[(μG : Measure G)] ℂ)
    (hχσ : ∀ i,
      χσ i =
        (letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
         characterL2 ((σ i).toRepresentation))) :
    ∑ i, (characterL2 ρ | χσ i)_G =
      ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i _
  letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
  letI : Representation.IsIrreducible ((σ i).toRepresentation) := hσ i
  rw [hχσ i]
  exact
    Representation.characterPairing_eq_finrank_intertwiningMap_of_isInternal
      (ρ := ρ) (σ := σ) (hinternal := hinternal) (hσ := hσ)
      ((σ i).toRepresentation)

/-- Helper for Theorem 4-17: the canonical summand-character pairings in an internal irreducible
decomposition equal the corresponding intertwining-space dimensions. -/
private theorem sumCanonicalSummandPairings_eq_sumFinrankIntertwining_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible) :
    ∑ i,
        (characterL2 ρ |
          summandCharacterFamily ρ σ
            (fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)) i)_G =
      ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
  let hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation) :=
    fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)
  have hfinrankLocal :
      ∑ i, (characterL2 ρ | summandCharacterFamily ρ σ hσcont i)_G =
        ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
    letI : Representation.IsIrreducible ((σ i).toRepresentation) := hσ i
    simpa [summandCharacterFamily] using
      (Representation.characterPairing_eq_finrank_intertwiningMap_of_isInternal
        (ρ := ρ) (σ := σ) (hinternal := hinternal) (hσ := hσ) ((σ i).toRepresentation))
  simpa [hσcont] using hfinrankLocal

/-- Helper for Theorem 4-17: repackage Theorem 4-16 with the canonical classical decidable
equality on the finite summand index. -/
private theorem characterPairing_eq_finrankIntertwiningMap_of_isInternalFinite
    [Fintype ι]
    {W : Type w'} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    (characterL2 ρ | characterL2 π)_G = Module.finrank ℂ (ρ.IntertwiningMap π) := by
  classical
  have hinternal' : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) := by
    simpa using hinternal
  simpa using
    (Representation.characterPairing_eq_finrank_intertwiningMap_of_isInternal
      (ρ := ρ) (σ := σ) (hinternal := hinternal') (hσ := hσ) (π := π))

/-- Helper for Theorem 4-17: repackage the Chapter 3 multiplicity-count owner with the canonical
classical decidable equality on the finite summand index. -/
private theorem cardIsomorphicIrreducibleSummands_eq_finrankIntertwiningMapFinite
    [Fintype ι]
    {W : Type w'} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (π : Representation ℂ G W) [Representation.IsIrreducible π] :
    Nat.card { j // Nonempty (((σ j).toRepresentation).Equiv π) } =
      Module.finrank ℂ (ρ.IntertwiningMap π) := by
  classical
  have hinternal' : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) := by
    simpa using hinternal
  simpa using
    (Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
      (ρ := ρ) (σ := σ) (hinternal := hinternal') (hσ := hσ) (τ := π) inferInstance)

/-- Helper for Theorem 4-17: an irreducible representation has a nontrivial carrier. -/
private theorem nontrivial_of_isIrreducibleLocal
    {W : Type w'} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G W) [Representation.IsIrreducible τ] : Nontrivial W := by
  by_contra hW
  letI : Subsingleton W := not_nontrivial_iff_subsingleton.mp hW
  have hbot_top : (⊥ : Subrepresentation τ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact IsSimpleOrder.bot_ne_top hbot_top

/-- Helper for Theorem 4-17: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
-- Route correction: the active finrank decomposition only needs source-side direct-sum transport,
-- so the old codomain-side helper layer is dropped in favor of this precomposition equivalence.
private theorem equivIntertwiningMapCongrLeft
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {W' : Type w'} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G U} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (τ : Representation ℂ G W') :
    Nonempty (σ.IntertwiningMap τ ≃ₗ[ℂ] ρ.IntertwiningMap τ) := by
  -- Precomposition with `e` transports an intertwiner out of `σ` to one out of `ρ`.
  exact ⟨
    { toFun := fun f ↦ f.comp e.toIntertwiningMap
      invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
      left_inv := by
        intro f
        -- The inverse pair collapses because `e` and `e.symm` compose to the identity.
        apply IntertwiningMap.ext
        ext x
        simp
      right_inv := by
        intro f
        -- The same computation proves the other inverse identity.
        apply IntertwiningMap.ext
        ext x
        simp
      map_add' := by
        intro f g
        -- Precomposition is linear on intertwining maps.
        apply IntertwiningMap.ext
        ext x
        rfl
      map_smul' := by
        intro a f
        -- Scalar multiplication is preserved pointwise under precomposition.
        apply IntertwiningMap.ext
        ext x
        rfl }⟩

/-- Helper for Theorem 4-17: postcomposing with a representation equivalence identifies
intertwining spaces with the same source. -/
private theorem equivIntertwiningMapCongrRight
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {W' : Type w'} [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G U} {σ : Representation ℂ G W}
    {τ : Representation ℂ G W'}
    (e : σ.Equiv τ) :
    Nonempty (ρ.IntertwiningMap σ ≃ₗ[ℂ] ρ.IntertwiningMap τ) := by
  -- Postcomposition with `e` transports an intertwiner into `σ` to one into `τ`.
  exact ⟨
    { toFun := fun f ↦ e.toIntertwiningMap.comp f
      invFun := fun f ↦ e.symm.toIntertwiningMap.comp f
      left_inv := by
        intro f
        -- The forward and backward transports cancel pointwise.
        apply IntertwiningMap.ext
        ext x
        simp
      right_inv := by
        intro f
        -- The same pointwise simplification gives the reverse inverse law.
        apply IntertwiningMap.ext
        ext x
        simp
      map_add' := by
        intro f g
        -- Postcomposition is linear on intertwining maps.
        apply IntertwiningMap.ext
        ext x
        simp
      map_smul' := by
        intro a f
        -- Scalar multiplication is preserved pointwise under postcomposition.
        apply IntertwiningMap.ext
        ext x
        simp }⟩

/-- Helper for Theorem 4-17: irreducibility is preserved by a representation equivalence. -/
private theorem isIrreducible_of_equiv
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G U} {σ : Representation ℂ G W}
    [ρ.IsIrreducible] (e : ρ.Equiv σ) :
    σ.IsIrreducible := by
  -- The project already provides the global transport theorem; use it directly here.
  exact Representation.isIrreducible_of_nonempty_equiv ⟨e⟩

/-- Helper for Theorem 4-17: intertwining maps out of a finite direct sum are exactly families of
intertwining maps out of the summands. -/
private theorem directSumIntertwiningMapEquivPi
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    {W : κ → Type w'} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (π : (i : κ) → Representation ℂ G (W i))
    (τ : Representation ℂ G W') :
    Nonempty ((Representation.directSum π).IntertwiningMap τ ≃ₗ[ℂ] ∀ i, (π i).IntertwiningMap τ) := by
  -- A map out of the direct sum is determined by its restrictions to the coordinate inclusions.
  exact ⟨
    { toFun := fun F i ↦
        ((F.toLinearMap.comp
            (DirectSum.lof ℂ κ W i)).intertwiningMap_of_isIntertwiningMap
          (π i) τ fun g x ↦ by
            simpa [Representation.directSum] using
              congr($(F.isIntertwining' g) (DirectSum.lof ℂ κ W i x)))
      invFun := fun f ↦
        { toLinearMap := DirectSum.toModule ℂ κ W' fun i ↦ (f i).toLinearMap
          isIntertwining' := by
            intro g
            apply DirectSum.linearMap_ext
            intro i
            ext x
            simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
      left_inv := by
        intro F
        -- Two maps out of a direct sum agree once they agree on each coordinate injection.
        apply IntertwiningMap.ext
        apply DirectSum.linearMap_ext
        intro i
        ext x
        change
          (DirectSum.toModule ℂ κ W'
            (fun j ↦ F.toLinearMap.comp (DirectSum.lof ℂ κ W j)))
            (DirectSum.lof ℂ κ W i x) =
          F (DirectSum.lof ℂ κ W i x)
        simp
      right_inv := by
        intro f
        -- Reassembling the coordinate family recovers each original intertwiner.
        funext i
        apply IntertwiningMap.ext
        ext x
        change
          (DirectSum.toModule ℂ κ W' fun j ↦ (f j).toLinearMap)
            (DirectSum.lof ℂ κ W i x) =
          (f i) x
        simp
      map_add' := by
        intro F H
        -- The coordinate restrictions commute with addition.
        funext i
        apply IntertwiningMap.ext
        ext x
        rfl
      map_smul' := by
        intro a F
        -- The coordinate restrictions commute with scalar multiplication.
        funext i
        apply IntertwiningMap.ext
        ext x
        rfl }⟩

/-- Helper for Theorem 4-17: intertwining maps into a finite direct sum are exactly families of
intertwining maps into the summands. -/
private theorem intertwiningMapIntoDirectSumEquivPi
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    {W : κ → Type w'} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : Representation ℂ G U)
    (π : (i : κ) → Representation ℂ G (W i)) :
    Nonempty (ρ.IntertwiningMap (Representation.directSum π) ≃ₗ[ℂ] ∀ i, ρ.IntertwiningMap (π i)) := by
  -- A map into the direct sum is determined by its coordinate projections.
  exact ⟨
    { toFun := fun F i ↦
        ((DirectSum.component ℂ κ W i).comp F.toLinearMap).intertwiningMap_of_isIntertwiningMap
          ρ (π i) fun g x ↦ by
            simpa [Representation.directSum] using
              congrArg (fun T ↦ DirectSum.component ℂ κ W i (T x)) (F.isIntertwining' g)
      invFun := fun f ↦
        { toLinearMap :=
            (DirectSum.linearEquivFunOnFintype ℂ κ W).symm.toLinearMap.comp
              (LinearMap.pi fun i ↦ (f i).toLinearMap)
          isIntertwining' := by
            intro g
            ext x i
            -- The direct-sum action is coordinatewise, so each component intertwines separately.
            change ((LinearMap.pi fun i ↦ (f i).toLinearMap) ((ρ g) x)) i =
              ((π i) g) (((LinearMap.pi fun i ↦ (f i).toLinearMap) x) i)
            simp [Representation.IntertwiningMap.isIntertwining] }
      left_inv := by
        intro F
        -- Equality of direct-sum-valued maps is checked coordinatewise.
        apply IntertwiningMap.ext
        ext x i
        change DirectSum.component ℂ κ W i (F x) = (F x) i
        rfl
      right_inv := by
        intro f
        -- Reassembling the coordinate family recovers each original component.
        funext i
        apply IntertwiningMap.ext
        ext x
        change
          DirectSum.component ℂ κ W i
              ((DirectSum.linearEquivFunOnFintype ℂ κ W).symm
                ((LinearMap.pi fun i ↦ (f i).toLinearMap) x)) =
            (f i) x
        rfl
      map_add' := by
        intro F H
        -- Projection to each coordinate commutes with addition.
        funext i
        apply IntertwiningMap.ext
        ext x
        rfl
      map_smul' := by
        intro a F
        -- Projection to each coordinate commutes with scalar multiplication.
        funext i
        apply IntertwiningMap.ext
        ext x
        rfl }⟩

/-- Helper for Theorem 4-17: under an internal decomposition, the endomorphism space of `ρ`
splits as the product of the spaces `σ i ⟶ ρ`. -/
private theorem finrank_intertwiningMap_self_eq_sum_finrank_toSummands_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    Module.finrank ℂ (ρ.IntertwiningMap ρ) =
      ∑ i, Module.finrank ℂ (((σ i).toRepresentation).IntertwiningMap ρ) := by
  classical
  let ℳ : ι → Submodule ℂ V := fun i ↦ (σ i).toSubmodule
  let π : ∀ i, Representation ℂ G (ℳ i) := fun i ↦ (σ i).toRepresentation
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hinternal
  let decompositionEquiv : (Representation.directSum π).Equiv ρ :=
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv ℳ).symm
      (fun g ↦ by
        -- The direct-sum action is componentwise, so the decomposition map is equivariant.
        ext i x
        simp [Representation.directSum, π]
        rfl)
  have hpi :
      Module.finrank ℂ (∀ i, (π i).IntertwiningMap ρ) =
        ∑ i, Module.finrank ℂ (((σ i).toRepresentation).IntertwiningMap ρ) := by
    have hpi' :
        Module.finrank ℂ (∀ i, (π i).IntertwiningMap ρ) =
          ∑ i, Module.finrank ℂ ((π i).IntertwiningMap ρ) := by
      rw [Module.finrank_pi_fintype]
    simpa [π] using hpi'
  -- Replace `ρ` by the equivalent direct sum and then use the direct-sum source universal property.
  calc
    Module.finrank ℂ (ρ.IntertwiningMap ρ) =
        Module.finrank ℂ ((Representation.directSum π).IntertwiningMap ρ) := by
          exact (Classical.choice (equivIntertwiningMapCongrLeft decompositionEquiv ρ)).finrank_eq
    _ = Module.finrank ℂ (∀ i, (π i).IntertwiningMap ρ) := by
          exact (Classical.choice (directSumIntertwiningMapEquivPi π ρ)).finrank_eq
    _ = ∑ i, Module.finrank ℂ (((σ i).toRepresentation).IntertwiningMap ρ) := hpi

/-- Helper for Theorem 4-17: every irreducible summand in an internal decomposition contributes a
positive-dimensional intertwining space from `ρ`. -/
private theorem finrank_intertwiningMap_toSummand_pos_of_isInternal
    [Fintype ι]
    [DecidableEq ι]
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (i : ι) :
    0 < Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) := by
  let ℳ : ι → Submodule ℂ V := fun j ↦ (σ j).toSubmodule
  let π : ∀ j, Representation ℂ G (ℳ j) := fun j ↦ (σ j).toRepresentation
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hinternal
  let decompositionEquiv : (Representation.directSum π).Equiv ρ :=
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv ℳ).symm
      (fun g ↦ by
        ext j x
        simp [Representation.directSum, π]
        rfl)
  let projectionLinear : V →ₗ[ℂ] ℳ i :=
    (DirectSum.component ℂ ι (fun j ↦ ℳ j) i).comp decompositionEquiv.symm.toLinearMap
  let projection : ρ.IntertwiningMap ((σ i).toRepresentation) :=
    projectionLinear.intertwiningMap_of_isIntertwiningMap
      ρ (π i) fun g x ↦ by
        simpa [projectionLinear, Representation.directSum] using
          congrArg (fun T ↦ DirectSum.component ℂ ι (fun j ↦ ℳ j) i (T x))
            (decompositionEquiv.symm.toIntertwiningMap.isIntertwining' g)
  have hprojection_ne : projection ≠ 0 := by
    letI : Nontrivial (ℳ i) := nontrivial_of_isIrreducibleLocal (τ := π i)
    obtain ⟨x, hx⟩ := exists_ne (0 : ℳ i)
    have hprojection_eval :
        projection (decompositionEquiv (DirectSum.lof ℂ ι (fun j ↦ ℳ j) i x)) = x := by
      change projectionLinear (decompositionEquiv (DirectSum.lof ℂ ι (fun j ↦ ℳ j) i x)) = x
      simp [projectionLinear, decompositionEquiv]
    intro hprojection_zero
    have hx_zero := congrArg
      (fun f : ρ.IntertwiningMap ((σ i).toRepresentation) ↦
        f (decompositionEquiv (DirectSum.lof ℂ ι (fun j ↦ ℳ j) i x)))
      hprojection_zero
    simpa [hprojection_eval, hx] using hx_zero
  letI : Nontrivial (ρ.IntertwiningMap ((σ i).toRepresentation)) :=
    ⟨⟨projection, 0, hprojection_ne⟩⟩
  exact Module.finrank_pos

/-- Helper for Theorem 4-17: under an internal decomposition, the endomorphism space of `ρ`
also splits as the product of the spaces `ρ ⟶ σ i`. -/
private theorem finrank_intertwiningMap_self_eq_sum_finrank_fromAmbient_toSummands_of_isInternal
    [Fintype ι]
    [DecidableEq ι]
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    Module.finrank ℂ (ρ.IntertwiningMap ρ) =
      ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) := by
  classical
  let ℳ : ι → Submodule ℂ V := fun i ↦ (σ i).toSubmodule
  let π : ∀ i, Representation ℂ G (ℳ i) := fun i ↦ (σ i).toRepresentation
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hinternal
  let decompositionEquiv : (Representation.directSum π).Equiv ρ :=
    Representation.Equiv.mk
      (DirectSum.decomposeLinearEquiv ℳ).symm
      (fun g ↦ by
        -- The direct-sum action is componentwise, so the decomposition map is equivariant.
        ext i x
        simp [Representation.directSum, π]
        rfl)
  have hpi :
      Module.finrank ℂ (∀ i, ρ.IntertwiningMap (π i)) =
        ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) := by
    have hpi' :
        Module.finrank ℂ (∀ i, ρ.IntertwiningMap (π i)) =
          ∑ i, Module.finrank ℂ (ρ.IntertwiningMap (π i)) := by
      rw [Module.finrank_pi_fintype]
    simpa [π] using hpi'
  -- Replace the target of endomorphisms by the equivalent direct sum and use the direct-sum
  -- codomain universal property.
  calc
    Module.finrank ℂ (ρ.IntertwiningMap ρ) =
        Module.finrank ℂ (ρ.IntertwiningMap (Representation.directSum π)) := by
          exact
            (Classical.choice
              (equivIntertwiningMapCongrRight (ρ := ρ) decompositionEquiv.symm)).finrank_eq
    _ = Module.finrank ℂ (∀ i, ρ.IntertwiningMap (π i)) := by
          exact (Classical.choice (intertwiningMapIntoDirectSumEquivPi ρ π)).finrank_eq
    _ = ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) := hpi

/-- Helper for Theorem 4-17: a subrepresentation whose underlying submodule is `⊤` is
equivariantly the ambient representation. -/
private theorem toRepresentationEquivOfToSubmoduleEqTop
    (ρ : Representation ℂ G V)
    (σ : Subrepresentation ρ)
    (hσ : σ.toSubmodule = ⊤) :
    Nonempty (σ.toRepresentation.Equiv ρ) := by
  have hσ_top : σ = ⊤ := Subrepresentation.toSubmodule_injective hσ
  subst hσ_top
  -- Once the subrepresentation is literally `⊤`, its inclusion is the identity on the carrier.
  refine ⟨Representation.Equiv.mk Submodule.topEquiv ?_⟩
  intro g
  ext x
  rfl

/-- Helper for Theorem 4-17: under an internal irreducible decomposition, the self-pairing of
`ρ` is the sum of the multiplicity dimensions `ρ ⟶ σ i`. -/
private theorem characterPairing_self_eq_sum_finrank_fromAmbient_toSummands_of_isInternal
    [Fintype ι]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible) :
    (characterL2 ρ | characterL2 ρ)_G =
      ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
  classical
  have hpairings :
      (characterL2 ρ | characterL2 ρ)_G =
        ∑ i,
          (characterL2 ρ |
            summandCharacterFamily ρ σ
              (fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)) i)_G := by
    exact characterPairing_self_eq_sumCanonicalSummandPairings_of_isInternal ρ σ hinternal
  have hfinrankSum :
      ∑ i,
          (characterL2 ρ |
            summandCharacterFamily ρ σ
              (fun i ↦ subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)) i)_G =
        ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
    exact
      sumCanonicalSummandPairings_eq_sumFinrankIntertwining_of_isInternal ρ σ hinternal hσ
  exact hpairings.trans hfinrankSum

/-- Companion canonical form of Theorem 4-17: for a finite-dimensional continuous complex
representation `ρ` of a compact group, the self-pairing `(χ | χ)_G` is the dimension of the
intertwining endomorphism space `ρ.IntertwiningMap ρ`. -/
theorem characterPairing_self_eq_finrank_intertwiningMap_self_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    (characterL2 ρ | characterL2 ρ)_G = (Module.finrank ℂ (ρ.IntertwiningMap ρ) : ℂ) := by
  classical
  obtain ⟨κ, hκFintype, hκDecEq, σ, hinternal, hσ⟩ :
      ∃ (κ : Type (max u v)) (_ : Fintype κ) (_ : DecidableEq κ)
        (σ : κ → Subrepresentation ρ),
        DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
          ∀ i, (σ i).toRepresentation.IsIrreducible := by
    simpa using exists_isInternal_irreducible_subrepresentations_of_compact (ρ := ρ)
  letI : Fintype κ := hκFintype
  letI : Finite κ := inferInstance
  letI : DecidableEq κ := instDecidableEqOfFinite κ
  have hinternalFinite : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) := by
    have hDecEq : hκDecEq = instDecidableEqOfFinite κ := by
      funext a b
      exact Subsingleton.elim _ _
    cases hDecEq
    exact hinternal
  have hpairing_sum :
      (characterL2 ρ | characterL2 ρ)_G =
        ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := by
    exact
      characterPairing_self_eq_sum_finrank_fromAmbient_toSummands_of_isInternal
        ρ σ hinternalFinite hσ
  letI : DecidableEq κ := hκDecEq
  have hfinrank_sum :
      ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) =
        Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
    exact
      (finrank_intertwiningMap_self_eq_sum_finrank_fromAmbient_toSummands_of_isInternal
        ρ σ hinternal).symm
  calc
    (characterL2 ρ | characterL2 ρ)_G =
        ∑ i, (Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℂ) := hpairing_sum
    _ = ((∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) : ℕ) : ℂ) := by
          simp
    _ = Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
          exact congrArg (fun n : ℕ ↦ (n : ℂ)) hfinrank_sum

/-- Positive-integrality clause of Theorem 4-17: for a nonzero finite-dimensional continuous
complex representation `ρ` of a
compact group, the self-pairing `(χ | χ)_G` of its character is a positive integer. -/
theorem exists_nat_pos_eq_characterPairing_self_of_nontrivial_of_isContinuousCompact
    [Nontrivial V] (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    ∃ n : ℕ, 0 < n ∧ ((n : ℂ) = (characterL2 ρ | characterL2 ρ)_G) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hid_ne : Representation.IntertwiningMap.id ρ ≠ 0 := by
    -- The identity intertwiner is nonzero on any nonzero vector.
    intro h
    have := congrArg (fun f : ρ.IntertwiningMap ρ ↦ f v) h
    simp [hv] at this
  letI : Nontrivial (ρ.IntertwiningMap ρ) := ⟨⟨Representation.IntertwiningMap.id ρ, 0, hid_ne⟩⟩
  refine ⟨Module.finrank ℂ (ρ.IntertwiningMap ρ), Module.finrank_pos, ?_⟩
  -- The canonical self-pairing formula turns the positive dimension into the desired integer.
  simpa using
    (characterPairing_self_eq_finrank_intertwiningMap_self_of_isContinuousCompact
      (ρ := ρ)).symm

/-- Helper corollary: for a finite-dimensional continuous complex representation `ρ` of a compact
group, the self-pairing `(χ | χ)_G` of its character is an integer. -/
theorem exists_nat_eq_characterPairing_self_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    ∃ n : ℕ, ((n : ℂ) = (characterL2 ρ | characterL2 ρ)_G) := by
  refine ⟨Module.finrank ℂ (ρ.IntertwiningMap ρ), ?_⟩
  -- The endomorphism-space dimension is the canonical integer realizing the self-pairing.
  simpa using
    (characterPairing_self_eq_finrank_intertwiningMap_self_of_isContinuousCompact
      (ρ := ρ)).symm

/-- Irreducibility clause of Theorem 4-17: for a finite-dimensional continuous complex
representation `ρ` of a compact group, the self-pairing `(χ | χ)_G` is `1` if and only if `ρ` is
irreducible. -/
theorem characterPairing_self_eq_one_iff_isIrreducible_of_isContinuousCompact
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] :
    ((characterL2 ρ | characterL2 ρ)_G = 1) ↔ ρ.IsIrreducible := by
  constructor
  · intro hpair
    have hfinrank_cast : (Module.finrank ℂ (ρ.IntertwiningMap ρ) : ℂ) = 1 := by
      -- Rewrite the pairing hypothesis through the canonical endomorphism-space formula.
      rw [← characterPairing_self_eq_finrank_intertwiningMap_self_of_isContinuousCompact (ρ := ρ)]
      exact hpair
    have hfinrank : Module.finrank ℂ (ρ.IntertwiningMap ρ) = 1 := by
      exact_mod_cast hfinrank_cast
    obtain ⟨κ, hκFintype, hκDecEq, σ, hinternal, hσ⟩ :
        ∃ (κ : Type (max u v)) (_ : Fintype κ) (_ : DecidableEq κ)
          (σ : κ → Subrepresentation ρ),
          DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) ∧
            ∀ i, (σ i).toRepresentation.IsIrreducible := by
      simpa using exists_isInternal_irreducible_subrepresentations_of_compact (ρ := ρ)
    letI : Fintype κ := hκFintype
    letI : DecidableEq κ := hκDecEq
    letI : Finite κ := inferInstance
    have hsum :
        ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) = 1 := by
      -- The codomain-side decomposition rewrites `finrank End_G(ρ)` as a sum of positive terms.
      calc
        ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) =
            Module.finrank ℂ (ρ.IntertwiningMap ρ) := by
              symm
              exact
                finrank_intertwiningMap_self_eq_sum_finrank_fromAmbient_toSummands_of_isInternal
                  (ρ := ρ) (σ := σ) hinternal
        _ = 1 := hfinrank
    have hcard_le_one : Fintype.card κ ≤ 1 := by
      calc
        Fintype.card κ = Finset.card (Finset.univ : Finset κ) := by
          simp
        _ = ∑ i : κ, (1 : ℕ) := by
          simp
        _ ≤ ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact Nat.succ_le_of_lt
            (finrank_intertwiningMap_toSummand_pos_of_isInternal
              (ρ := ρ) (σ := σ) hinternal hσ i)
        _ = 1 := hsum
    have hsub : Subsingleton κ := (Fintype.card_le_one_iff_subsingleton (α := κ)).mp hcard_le_one
    have hnonempty : Nonempty κ := by
      by_contra hι
      letI : IsEmpty κ := not_nonempty_iff.mp hι
      have hsum_zero :
          ∑ i, Module.finrank ℂ (ρ.IntertwiningMap ((σ i).toRepresentation)) = 0 := by
        simp
      exact Nat.one_ne_zero (hsum.symm.trans hsum_zero)
    obtain ⟨i0⟩ := hnonempty
    have huniq : ∀ j : κ, j = i0 := fun j ↦ hsub.elim j i0
    have htop : (σ i0).toSubmodule = ⊤ := by
      -- With a unique summand, the internal supremum equality says that summand is the whole
      -- representation.
      have hsup_single : (⨆ j, (σ j).toSubmodule) = (σ i0).toSubmodule := by
        apply le_antisymm
        · refine iSup_le ?_
          intro j
          simpa [huniq j] using (le_rfl : (σ i0).toSubmodule ≤ (σ i0).toSubmodule)
        · exact le_iSup (fun j ↦ (σ j).toSubmodule) i0
      calc
        (σ i0).toSubmodule = ⨆ j, (σ j).toSubmodule := by
          simpa using hsup_single.symm
        _ = ⊤ := hinternal.submodule_iSup_eq_top
    have htopEquiv : Nonempty (((σ i0).toRepresentation).Equiv ρ) := by
      -- The unique summand has carrier `⊤`, so it is equivariantly the ambient representation.
      exact toRepresentationEquivOfToSubmoduleEqTop (ρ := ρ) (σ := σ i0) htop
    letI : ((σ i0).toRepresentation).IsIrreducible := hσ i0
    -- Irreducibility transports across the identified equivalence with the unique summand.
    exact isIrreducible_of_equiv (Classical.choice htopEquiv)
  · intro hρ
    letI : ρ.IsIrreducible := hρ
    -- Theorem 4-15 gives the irreducible self-pairing value.
    simpa using
      Representation.characterPairing_self_eq_one_of_isIrreducible_of_isContinuousCompact
        (ρ := ρ)

/-- Helper for Theorem 4-17: in the repeated direct-sum model, the hom-space from one fixed
irreducible copy `π j.1` has dimension exactly the multiplicity `m j.1`. -/
private theorem finrank_intertwiningMap_piToRepeatedDirectSum_eq_m
    {κ : Type w} [Fintype κ]
    {W : κ → Type w'} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (π : (i : κ) → Representation ℂ G (W i))
    [∀ i, Representation.IsIrreducible (π i)]
    (m : κ → ℕ)
    (hπ_pairwise : Pairwise fun i j ↦ ¬ Nonempty ((π i).Equiv (π j)))
    (j : κ) :
    Module.finrank ℂ
        ((π j).IntertwiningMap (Representation.directSum fun l : Σ i, Fin (m i) ↦ π l.1)) =
      m j := by
  classical
  calc
    Module.finrank ℂ
        ((π j).IntertwiningMap (Representation.directSum fun l : Σ i, Fin (m i) ↦ π l.1)) =
        Module.finrank ℂ (∀ l : Σ i, Fin (m i), (π j).IntertwiningMap (π l.1)) := by
          -- Split maps into the repeated direct sum by their coordinate projections.
          exact
            (Classical.choice
              (intertwiningMapIntoDirectSumEquivPi
                (ρ := π j) (π := fun l : Σ i, Fin (m i) ↦ π l.1))).finrank_eq
    _ = ∑ l : Σ i, Fin (m i), Module.finrank ℂ ((π j).IntertwiningMap (π l.1)) := by
          rw [Module.finrank_pi_fintype]
    _ = ∑ l : Σ i, Fin (m i), if Nonempty ((π j).Equiv (π l.1)) then 1 else 0 := by
          -- Schur's lemma reduces each irreducible factor to the `1/0` indicator.
          refine Finset.sum_congr rfl ?_
          intro l _
          simpa using
            (Representation.finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible
              (π j) inferInstance (π l.1) inferInstance)
    _ = m j := by
          -- Only the copies indexed by `Fin (m j)` survive the pairwise-nonisomorphic outer index.
          rw [Fintype.sum_sigma]
          have hinner :
              ∀ i,
                (∑ k : Fin (m i), if Nonempty ((π j).Equiv (π i)) then (1 : ℕ) else 0) =
                  if i = j then m j else 0 := by
            intro i
            by_cases hij : i = j
            · subst i
              have hself : Nonempty ((π j).Equiv (π j)) := ⟨Representation.Equiv.refl _⟩
              simpa [hself]
            · have hnot : ¬ Nonempty ((π j).Equiv (π i)) := by
                intro hji
                exact hπ_pairwise hij ⟨(Classical.choice hji).symm⟩
              simp [hij, hnot]
          calc
            (∑ i, ∑ k : Fin (m i), if Nonempty ((π j).Equiv (π i)) then (1 : ℕ) else 0) =
                ∑ i, if i = j then m j else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  exact hinner i
            _ = m j := by
                  simp

/-- Helper for Theorem 4-17: the direct-sum model with `m i` copies of each `π i` has
endomorphism-space dimension `∑ i m i^2`. -/
private theorem finrank_intertwiningMap_self_eq_sumSqMultiplicities_of_directSumModel
    {κ : Type w} [Fintype κ]
    {W : κ → Type w'} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (π : (i : κ) → Representation ℂ G (W i))
    [∀ i, Representation.IsIrreducible (π i)]
    (m : κ → ℕ)
    (hπ_pairwise : Pairwise fun i j ↦ ¬ Nonempty ((π i).Equiv (π j))) :
    Module.finrank ℂ
        ((Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1).IntertwiningMap
          (Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1)) =
      ∑ i, m i ^ 2 := by
  classical
  let R : Representation ℂ G (DirectSum (Σ i, Fin (m i)) fun j ↦ W j.1) :=
    Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1
  calc
    Module.finrank ℂ
        ((Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1).IntertwiningMap
          (Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1)) =
        Module.finrank ℂ
          (∀ j : Σ i, Fin (m i),
            (π j.1).IntertwiningMap R) :=
          by
            -- Split endomorphisms of the direct sum by their source coordinate restrictions.
            exact
              (Classical.choice
                (directSumIntertwiningMapEquivPi
                  (π := fun j : Σ i, Fin (m i) ↦ π j.1)
                  (τ := R))).finrank_eq
    _ = ∑ j : Σ i, Fin (m i),
          Module.finrank ℂ
            ((π j.1).IntertwiningMap R) :=
          by
            rw [Module.finrank_pi_fintype]
    _ = ∑ j : Σ i, Fin (m i), m j.1 := by
          -- Each source coordinate contributes exactly its multiplicity.
          refine Finset.sum_congr rfl ?_
          intro j _
          exact finrank_intertwiningMap_piToRepeatedDirectSum_eq_m
            (π := π) (m := m) hπ_pairwise j.1
    _ = ∑ i, m i ^ 2 := by
          -- Summing the multiplicity `m i` over its `m i` repeated copies produces `m i^2`.
          rw [Fintype.sum_sigma]
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [Finset.sum_const, Fintype.card_fin, pow_two]

/-- Theorem 4-17 — if the irreducible isomorphism classes occurring in a finite-dimensional
continuous complex representation `ρ` of a compact group are represented by a finite family `π i`
with multiplicities `m i`, so that `ρ` is equivalent to the direct sum of `m i` copies of each
`π i`, then `(χ | χ)_G = ∑ i, m i ^ 2`. Lean records
`V ≃ ⨁ π, π^(⊕ m π)` by
`Nonempty (ρ.Equiv (Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1))`. -/
theorem characterPairing_self_eq_sum_sq_multiplicities_of_equiv_directSum
    {κ : Type w} [Fintype κ] {W : κ → Type w'}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, TopologicalSpace (W i)]
    [∀ i, IsTopologicalAddGroup (W i)] [∀ i, ContinuousSMul ℂ (W i)]
    [∀ i, T2Space (W i)] [∀ i, FiniteDimensional ℂ (W i)]
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (π : (i : κ) → Representation ℂ G (W i))
    [∀ i, Representation.IsContinuous (π i)] [∀ i, Representation.IsIrreducible (π i)]
    (m : κ → ℕ)
    (hπ_pairwise : Pairwise fun i j ↦ ¬ Nonempty ((π i).Equiv (π j)))
    (hρ_equiv :
      Nonempty (ρ.Equiv (Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1))) :
    (characterL2 ρ | characterL2 ρ)_G = ∑ i, ((m i : ℂ) ^ 2) := by
  classical
  let R := Representation.directSum fun j : Σ i, Fin (m i) ↦ π j.1
  rcases hρ_equiv with ⟨e⟩
  have hEndTransport :
      Module.finrank ℂ (ρ.IntertwiningMap ρ) = Module.finrank ℂ (R.IntertwiningMap R) := by
    -- Transport endomorphisms first on the source, then on the target, across the given
    -- representation equivalence `ρ ≃ R`.
    calc
      Module.finrank ℂ (ρ.IntertwiningMap ρ) =
          Module.finrank ℂ (R.IntertwiningMap ρ) := by
            symm
            exact (Classical.choice (equivIntertwiningMapCongrLeft e ρ)).finrank_eq
      _ = Module.finrank ℂ (R.IntertwiningMap R) := by
            exact (Classical.choice (equivIntertwiningMapCongrRight (ρ := R) e)).finrank_eq
  have hDirectSum :
      Module.finrank ℂ (R.IntertwiningMap R) = ∑ i, m i ^ 2 := by
    -- The raw direct-sum universal property computes the endomorphism dimension of `R`.
    simpa [R] using
      finrank_intertwiningMap_self_eq_sumSqMultiplicities_of_directSumModel
        (π := π) (m := m) hπ_pairwise
  calc
    (characterL2 ρ | characterL2 ρ)_G = (Module.finrank ℂ (ρ.IntertwiningMap ρ) : ℂ) := by
      -- First rewrite the self-pairing as the endomorphism-space dimension of `ρ`.
      exact characterPairing_self_eq_finrank_intertwiningMap_self_of_isContinuousCompact (ρ := ρ)
    _ = (Module.finrank ℂ (R.IntertwiningMap R) : ℂ) := by
          -- Then transport that dimension across the direct-sum model equivalence.
          exact congrArg (fun n : ℕ ↦ (n : ℂ)) hEndTransport
    _ = ((∑ i, m i ^ 2 : ℕ) : ℂ) := by
          -- The direct-sum model itself has endomorphism dimension `∑ i m_i^2`.
          exact congrArg (fun n : ℕ ↦ (n : ℂ)) hDirectSum
    _ = ∑ i, ((m i : ℂ) ^ 2) := by
          simp

end

end Representation
