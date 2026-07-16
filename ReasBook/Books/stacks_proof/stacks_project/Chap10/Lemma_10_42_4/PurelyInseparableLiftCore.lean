import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import stacks_proof.stacks_project.Chap09.Lemma_9_14_5
import stacks_proof.stacks_project.Chap09.Lemma_9_26_11
import stacks_proof.stacks_project.Chap09.Lemma_9_28_2
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_42_3
import Mathlib.Tactic.StacksAttribute


section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A finite purely inseparable lift of `K / k` whose upper extension becomes separably generated
over the lifted base field. -/
class IsPurelyInseparableLiftWithSeparablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (k' : Type w) [Field k'] [Algebra k k']
    (K' : Type (max v w)) [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] : Prop where
  /-- The top extension in the lift is finite. -/
  finiteDimensional_top : FiniteDimensional K K'
  /-- The top extension in the lift is purely inseparable. -/
  purelyInseparable_top : IsPurelyInseparable K K'
  /-- The base change in the lift is finite. -/
  finiteDimensional_base : FiniteDimensional k k'
  /-- The base change in the lift is purely inseparable. -/
  purelyInseparable_base : IsPurelyInseparable k k'
  /-- After the lift, the total extension is separably generated. -/
  separablyGenerated_top : IsSeparablyGenerated k' K'

/-- Helper for Lemma 10.42.4: composing two finite purely inseparable lifts again gives a finite
purely inseparable lift whose top remains separably generated over the final base. -/
lemma compose_purelyInseparable_lifts
    {k' : Type w} [Field k'] [Algebra k k']
    {K' : Type (max v w)} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    {w' : Type w} [Field w'] [Algebra k' w'] [Algebra k w']
    {L : Type (max v w)} [Field L] [Algebra k L] [Algebra K L] [Algebra k' L] [Algebra K' L]
    [Algebra w' L]
    [IsScalarTower k K L] [IsScalarTower k k' L] [IsScalarTower k' K' L] [IsScalarTower k' w' L]
    [IsScalarTower k w' L] [IsScalarTower K K' L] [IsScalarTower k k' w'] :
    IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' →
      IsPurelyInseparableLiftWithSeparablyGenerated k' K' w' L →
        IsPurelyInseparableLiftWithSeparablyGenerated k K w' L := by
  intro h₁ h₂
  -- The composed square inherits finiteness and purely inseparable top/base edges by transitivity.
  refine
    ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI : FiniteDimensional K K' := h₁.finiteDimensional_top
    letI : FiniteDimensional K' L := h₂.finiteDimensional_top
    exact FiniteDimensional.trans K K' L
  · letI : IsPurelyInseparable K K' := h₁.purelyInseparable_top
    letI : IsPurelyInseparable K' L := h₂.purelyInseparable_top
    exact IsPurelyInseparable.trans (F := K) (E := K') (K := L)
  · letI : FiniteDimensional k k' := h₁.finiteDimensional_base
    letI : FiniteDimensional k' w' := h₂.finiteDimensional_base
    exact FiniteDimensional.trans k k' w'
  · letI : IsPurelyInseparable k k' := h₁.purelyInseparable_base
    letI : IsPurelyInseparable k' w' := h₂.purelyInseparable_base
    exact IsPurelyInseparable.trans (F := k) (E := k') (K := w')
  · -- The second lift already provides separable generation over the final lifted base.
    exact h₂.separablyGenerated_top

/-- Helper for Lemma 10.42.4: if the first square is only a finite purely inseparable step on the
base and top edges, then composing it with a later purely inseparable lift still yields the final
purely inseparable lift with separably generated top. -/
lemma compose_purelyInseparable_step_with_lift
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {B : Type w} [Field B] [Algebra F B]
    {L : Type (max v w)} [Field L] [Algebra F L] [Algebra E L] [Algebra B L]
    [IsScalarTower F E L] [IsScalarTower F B L]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    [FiniteDimensional E L] [IsPurelyInseparable E L]
    {B' : Type w} [Field B'] [Algebra F B'] [Algebra B B'] [IsScalarTower F B B']
    {L' : Type (max v w)} [Field L'] [Algebra F L'] [Algebra E L'] [Algebra B L'] [Algebra L L']
    [Algebra B' L']
    [IsScalarTower F E L'] [IsScalarTower E L L'] [IsScalarTower F B' L']
    [IsScalarTower B L L'] [IsScalarTower B B' L'] :
    IsPurelyInseparableLiftWithSeparablyGenerated B L B' L' →
      IsPurelyInseparableLiftWithSeparablyGenerated F E B' L' := by
  intro h
  -- The top edge is the composite `E ⟶ L ⟶ L'`, so finiteness and purely inseparable-ness
  -- propagate by the standard tower lemmas.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI : FiniteDimensional L L' := h.finiteDimensional_top
    exact FiniteDimensional.trans E L L'
  · letI : IsPurelyInseparable L L' := h.purelyInseparable_top
    exact IsPurelyInseparable.trans (F := E) (E := L) (K := L')
  · letI : FiniteDimensional B B' := h.finiteDimensional_base
    exact FiniteDimensional.trans F B B'
  · letI : IsPurelyInseparable B B' := h.purelyInseparable_base
    exact IsPurelyInseparable.trans (F := F) (E := B) (K := B')
  · -- The second lift already provides the final separably generated structure.
    exact h.separablyGenerated_top

/-- Helper for Lemma 10.42.4: over a perfect base field, the identity square already gives the
required purely inseparable lift. -/
lemma exists_identity_lift_with_separablyGenerated_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  let k' : Type (max u w) := ULift.{w} k
  let K' : Type (max v (max u w)) := ULift.{max u w} K
  let ek : k' ≃ₐ[k] k := by
    change ULift.{w} k ≃ₐ[k] k
    exact ULift.algEquiv (R := k) (A := k)
  letI : Algebra k' k := ULift.algebra' k k
  letI : Algebra k' K := ULift.algebra' k K
  letI : Algebra k' K' := ULift.algebra
  letI : Algebra.IsAlgebraic k k' := ek.symm.isAlgebraic
  letI : PerfectField k' := Algebra.IsAlgebraic.perfectField (K := k) (L := k')
  letI : Algebra.EssFiniteType k' k :=
    (Algebra.EssFiniteType.iff_of_algEquiv (ULift.algEquiv (R := k') (A := k))).mp inferInstance
  letI : Algebra.EssFiniteType k' K := Algebra.EssFiniteType.comp k' k K
  letI : Algebra.EssFiniteType k' K' :=
    (Algebra.EssFiniteType.iff_of_algEquiv (ULift.algEquiv (R := k') (A := K))).mpr inferInstance
  -- Use lifted copies of `k` and `K` so the witness universes match the theorem statement.
  refine ⟨k', inferInstance, inferInstance, K', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- The witness class fields are all the identity-extension facts.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact (ULift.algEquiv (R := K) (A := K)).symm.isPurelyInseparable
  · infer_instance
  · exact (ULift.algEquiv (R := k) (A := k)).symm.isPurelyInseparable
  · infer_instance

/-- Helper for Lemma 10.42.4: if `K / k` is already separably generated, the source base case
packages into the theorem's widened-universe identity square. -/
lemma exists_identity_lift_with_separablyGenerated_of_isSeparablyGenerated
    (hsepgen : IsSeparablyGenerated k K) :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  let k' : Type (max u w) := ULift.{w} k
  let K' : Type (max v (max u w)) := ULift.{max u w} K
  let ek : k' ≃ₐ[k] k := by
    change ULift.{w} k ≃ₐ[k] k
    exact ULift.algEquiv (R := k) (A := k)
  letI : Algebra k' k := ULift.algebra' k k
  letI : Algebra k' K := ULift.algebra' k K
  letI : Algebra k' K' := ULift.algebra
  letI : Algebra.IsAlgebraic k k' := ek.symm.isAlgebraic
  have hsepgen_over_lifted_base : IsSeparablyGenerated k' K := by
    rcases hsepgen with ⟨s, hs, hsep⟩
    refine ⟨s, ?_, ?_⟩
    · -- Algebraic base change preserves the chosen transcendence basis.
      exact
        (Algebra.IsAlgebraic.isTranscendenceBasis_iff
          (R := k) (S := k') (A := K) (x := (Subtype.val : s → K))).mp hs
    · let F : IntermediateField k K := IntermediateField.adjoin k s
      let F' : IntermediateField k' K := IntermediateField.adjoin k' s
      letI : Algebra F F' :=
        (IntermediateField.inclusion
          (K := k) (L := K) (E := F) (F := F'.restrictScalars k)
          (IntermediateField.adjoin_le_iff.mpr fun y hy ↦
            IntermediateField.subset_adjoin (F := k') (S := s) hy)).toAlgebra
      letI : IsScalarTower F F' K := .of_algebraMap_eq fun x ↦ rfl
      letI : Algebra.IsSeparable F K := by
        simpa [F] using hsep
      -- Enlarging the intermediate base inside the same tower preserves separability.
      simpa [F, F'] using (Algebra.isSeparable_tower_top_of_isSeparable F F' K)
  have hsepgen_top : IsSeparablyGenerated k' K' := by
    -- Transport the separably generated structure across the lifted copy of `K`.
    exact hsepgen_over_lifted_base.of_algEquiv (ULift.algEquiv (R := k') (A := K)).symm
  refine ⟨k', inferInstance, inferInstance, K', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- All remaining fields are the identity-extension facts on the lifted copies.
  refine ⟨?_, ?_, ?_, ?_, hsepgen_top⟩
  · infer_instance
  · exact (ULift.algEquiv (R := K) (A := K)).symm.isPurelyInseparable
  · infer_instance
  · exact (ULift.algEquiv (R := k) (A := k)).symm.isPurelyInseparable

end
