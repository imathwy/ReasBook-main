module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Logic.Equiv.Nat

public section

/-- Helper for Proposition 69.2: the integer action that shifts the generators of
`FreeGroup ℤ` one place to the right. -/
private def integerShiftAction : Multiplicative ℤ →* MulAut (FreeGroup ℤ) :=
  -- Powers of the one-step permutation encode all integer shifts.
  zpowersHom _ (FreeGroup.freeGroupCongr (Equiv.addRight 1))

/-- Helper for Proposition 69.2: the `n`-th power of the one-step shift sends
`FreeGroup.of k` to `FreeGroup.of (k + n)`. -/
private lemma integerShiftPower_of (n k : ℤ) :
    ((FreeGroup.freeGroupCongr (Equiv.addRight 1)) ^ n) (FreeGroup.of k) =
      FreeGroup.of (k + n) := by
  -- Integer induction tracks forward shifts and inverse shifts separately.
  induction n using Int.inductionOn' (b := 0) generalizing k with
  | zero => simp
  | succ n hn ih =>
      rw [zpow_add_one, MulAut.mul_apply, FreeGroup.freeGroupCongr_apply]
      have hAdd : (k + 1) + n = k + (n + 1) := by
        omega
      exact (ih (k + 1)).trans (congrArg FreeGroup.of hAdd)
  | pred n hn ih =>
      rw [zpow_sub_one, MulAut.mul_apply, MulAut.inv_apply,
        FreeGroup.freeGroupCongr_symm, FreeGroup.freeGroupCongr_apply]
      have hSub : (k - 1) + n = k + (n - 1) := by
        omega
      exact (ih (k - 1)).trans (congrArg FreeGroup.of hSub)

/-- Helper for Proposition 69.2: `integerShiftAction` translates the index of
each canonical generator by the acting integer. -/
private lemma integerShiftAction_of (n k : ℤ) :
    integerShiftAction (Multiplicative.ofAdd n) (FreeGroup.of k) = FreeGroup.of (k + n) := by
  -- Reduce the action to the power computation above.
  have hToAdd : Multiplicative.toAdd (Multiplicative.ofAdd n) = n := rfl
  rw [integerShiftAction, zpowersHom_apply, hToAdd]
  exact integerShiftPower_of n k

/-- Helper for Proposition 69.2: the `k`-th generator is sent to the conjugate
`a ^ k * b * (a ^ k)⁻¹` in `FreeGroup (Fin 2)`. -/
private def conjugateGeneratorHom : FreeGroup ℤ →* FreeGroup (Fin 2) :=
  -- Extend the indexed conjugate family by the free-group universal property.
  FreeGroup.lift fun k ↦
    (FreeGroup.of (0 : Fin 2)) ^ k * FreeGroup.of (1 : Fin 2) *
      ((FreeGroup.of (0 : Fin 2)) ^ k)⁻¹

/-- Helper for Proposition 69.2: the two generators act respectively as a shift
and as the zeroth generator in the shift semidirect product. -/
private def shiftSemidirectRepresentation :
    FreeGroup (Fin 2) →* FreeGroup ℤ ⋊[integerShiftAction] Multiplicative ℤ :=
  -- The universal map records the shift invariant of the conjugate family.
  FreeGroup.lift fun i ↦ if i = 0 then
    SemidirectProduct.inr (Multiplicative.ofAdd 1)
  else SemidirectProduct.inl (FreeGroup.of 0)

/-- Helper for Proposition 69.2: the first generator represents one unit of
shift in `shiftSemidirectRepresentation`. -/
private lemma shiftSemidirectRepresentationOfZero :
    shiftSemidirectRepresentation (FreeGroup.of (0 : Fin 2)) =
      SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
  -- Evaluate the universal map on the first free generator.
  simp [shiftSemidirectRepresentation]

/-- Helper for Proposition 69.2: the second generator represents
`FreeGroup.of 0` in the normal factor. -/
private lemma shiftSemidirectRepresentationOfOne :
    shiftSemidirectRepresentation (FreeGroup.of (1 : Fin 2)) =
      SemidirectProduct.inl (FreeGroup.of 0) := by
  -- Evaluate the universal map on the second free generator.
  simp [shiftSemidirectRepresentation]

/-- Helper for Proposition 69.2: the shift representation sends every indexed
conjugate to the corresponding generator in its normal factor. -/
private lemma shiftSemidirectRepresentation_comp_conjugateGeneratorHom :
    shiftSemidirectRepresentation.comp conjugateGeneratorHom =
      (SemidirectProduct.inl : FreeGroup ℤ →*
        FreeGroup ℤ ⋊[integerShiftAction] Multiplicative ℤ) := by
  -- Extensionality reduces the bridge equation to one indexed conjugate.
  apply FreeGroup.ext_hom
  intro k
  simp only [MonoidHom.comp_apply, conjugateGeneratorHom, FreeGroup.lift_apply_of,
    map_mul, map_zpow, map_inv]
  -- Conjugation by the shift element is precisely the semidirect-product action.
  rw [shiftSemidirectRepresentationOfZero, shiftSemidirectRepresentationOfOne,
    ← map_zpow, ← map_inv, ← SemidirectProduct.inl_aut]
  have hPower : (Multiplicative.ofAdd 1) ^ k = Multiplicative.ofAdd k := by
    apply (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ).injective
    simp
  rw [hPower, integerShiftAction_of]
  simp

/-- Helper for Proposition 69.2: the family of conjugates freely embeds
`FreeGroup ℤ` into `FreeGroup (Fin 2)`. -/
private lemma conjugateGeneratorHom_injective : Function.Injective conjugateGeneratorHom := by
  intro x y hxy
  -- The detector turns equality of conjugates into equality under `inl`.
  have hDetected :
      (SemidirectProduct.inl x : FreeGroup ℤ ⋊[integerShiftAction] Multiplicative ℤ) =
        SemidirectProduct.inl y := by
    rw [← shiftSemidirectRepresentation_comp_conjugateGeneratorHom]
    exact congrArg shiftSemidirectRepresentation hxy
  -- The normal-factor inclusion is injective.
  exact SemidirectProduct.inl_injective hDetected

/-- Proposition 69.2 (1). The free group on two generators has a subgroup with a
system of three free generators. -/
theorem freeGroupHasSubgroupOfLargerFiniteRank :
    ∃ H : Subgroup (FreeGroup (Fin 2)), Nonempty (FreeGroupBasis (Fin 3) H) := by
  -- Restrict the countable conjugate family to the first three integer indices.
  let indexEmbedding : Fin 3 → ℤ := fun i ↦ (i : ℕ)
  let finiteConjugateGeneratorHom : FreeGroup (Fin 3) →* FreeGroup (Fin 2) :=
    conjugateGeneratorHom.comp (FreeGroup.map indexEmbedding)
  have hIndex : Function.Injective indexEmbedding := by
    intro i j hij
    apply Fin.ext
    exact Int.ofNat_injective hij
  have hFinite : Function.Injective finiteConjugateGeneratorHom :=
    conjugateGeneratorHom_injective.comp (FreeGroup.map_injective hIndex)
  -- Transport the canonical three-element basis onto the range subgroup.
  use finiteConjugateGeneratorHom.range
  exact Nonempty.intro
    ((FreeGroupBasis.ofFreeGroup (Fin 3)).map (MonoidHom.ofInjective hFinite))

/-- Companion to Proposition 69.2: the free group on two generators has a subgroup
with a countably infinite system of free generators. -/
theorem freeGroupHasSubgroupOfInfiniteRank :
    ∃ H : Subgroup (FreeGroup (Fin 2)), Nonempty (FreeGroupBasis ℕ H) := by
  -- Map the canonical integer-indexed basis onto the embedded range.
  use conjugateGeneratorHom.range
  -- Reindex that basis through the standard equivalence `ℤ ≃ ℕ`.
  exact Nonempty.intro
    (((FreeGroupBasis.ofFreeGroup ℤ).map
      (MonoidHom.ofInjective conjugateGeneratorHom_injective)).reindex Equiv.intEquivNat)
