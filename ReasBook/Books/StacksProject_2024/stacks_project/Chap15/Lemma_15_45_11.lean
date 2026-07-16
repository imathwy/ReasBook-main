import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_119_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: local commutative algebra of discrete valuation rings under henselization and
  strict henselization;
* sampled owner declarations:
  `IsDiscreteValuationRing`,
  `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_tfae_of_henselization_and_strictHenselization`,
  `ringKrullDim_henselization_eq`,
  `ringKrullDim_strictHenselization_eq`;
* best owner abstraction: the source-facing DVR clauses should be compared through the canonical
  owner pair `IsRegularLocalRing` and `ringKrullDim`, not by a parallel local DVR-specific bridge;
* primitive data: the local ring `R` and the chosen henselization / strict henselization owners;
* derived API: the equivalence between DVRs and one-dimensional regular local rings, together with
  the chapter's regular-local and Krull-dimension invariance theorems.

Source/core/bridge triage:
* `source-facing`: the three-way `List.TFAE` for the DVR condition;
* `core/canonical`: `IsRegularLocalRing` and `ringKrullDim`;
* `bridge/view`: `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_tfae_of_henselization_and_strictHenselization`,
  `ringKrullDim_henselization_eq`, and `ringKrullDim_strictHenselization_eq`.
-/
-- Proof sketch: apply Lemma `10.119.7` to characterize discrete valuation rings as the
-- one-dimensional regular local rings, then use Lemma `15.45.10` for
-- preservation and reflection of regularity along henselization and strict henselization and
-- Lemma `15.45.7` for equality of Krull dimensions.
/-- Lemma 15.45.11: for a local ring `R`, the following are equivalent: `R` is a
discrete valuation ring, a chosen henselization `Rh` of `R` is a discrete valuation ring, and a
chosen strict henselization `Rsh` of `R` is a discrete valuation ring. -/
theorem discreteValuationRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE
      [(∃ (_ : IsDomain R), IsDiscreteValuationRing R),
        (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh),
        (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh)] := by
  have hdimRh : ringKrullDim R = ringKrullDim Rh := ringKrullDim_henselization_eq
  have hdimRsh : ringKrullDim R = ringKrullDim Rsh := ringKrullDim_strictHenselization_eq
  have hRegular :
      List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh, IsRegularLocalRing Rsh] :=
    isRegularLocalRing_tfae_of_henselization_and_strictHenselization
  have h12 :
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
        ∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh := by
    calc
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
          IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
        discreteValuationRing_iff_regularLocalRing_dim_one
      _ ↔ IsRegularLocalRing Rh ∧ ringKrullDim R = 1 := by
        constructor
        · intro h
          exact ⟨(hRegular.out 0 1).mp h.1, h.2⟩
        · intro h
          exact ⟨(hRegular.out 0 1).mpr h.1, h.2⟩
      _ ↔ IsRegularLocalRing Rh ∧ ringKrullDim Rh = 1 := by
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          rw [← hdimRh]
          exact h.2
        · intro h
          refine ⟨h.1, ?_⟩
          rw [hdimRh]
          exact h.2
      _ ↔ (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh) :=
        discreteValuationRing_iff_regularLocalRing_dim_one.symm
  have h13 :
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
        ∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh := by
    calc
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
          IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
        discreteValuationRing_iff_regularLocalRing_dim_one
      _ ↔ IsRegularLocalRing Rsh ∧ ringKrullDim R = 1 := by
        constructor
        · intro h
          exact ⟨(hRegular.out 0 2).mp h.1, h.2⟩
        · intro h
          exact ⟨(hRegular.out 0 2).mpr h.1, h.2⟩
      _ ↔ IsRegularLocalRing Rsh ∧ ringKrullDim Rsh = 1 := by
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          rw [← hdimRsh]
          exact h.2
        · intro h
          refine ⟨h.1, ?_⟩
          rw [hdimRsh]
          exact h.2
      _ ↔ (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh) :=
        discreteValuationRing_iff_regularLocalRing_dim_one.symm
  have h23 :
      (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh) ↔
        ∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh :=
    h12.symm.trans h13
  intro x hx y hy
  simp only [List.mem_cons] at hx hy
  rcases hx with rfl | rfl | hx
  · rcases hy with rfl | rfl | hy
    · exact Iff.rfl
    · exact h12
    · rcases hy with rfl | hy
      · exact h13
      · cases hy
  · rcases hy with rfl | rfl | hy
    · exact h12.symm
    · exact Iff.rfl
    · rcases hy with rfl | hy
      · exact h23
      · cases hy
  · rcases hx with rfl | hx
    · rcases hy with rfl | rfl | hy
      · exact h13.symm
      · exact h23.symm
      · rcases hy with rfl | hy
        · exact Iff.rfl
        · cases hy
    · cases hx

end
