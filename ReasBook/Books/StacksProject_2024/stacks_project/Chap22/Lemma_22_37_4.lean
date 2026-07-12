import StacksProject_2024.Chap13.Definition_13_36_3
import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap22.RLinearTriangulatedEquivalence
import StacksProject_2024.Chap22.Remark_22_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uA uDA vDA uDB vDB

section

variable {R : Type uR} [CommRing R]
variable {A : Type uA} [Ring A] [Algebra R A]
variable {DA : Type uDA} {DB : Type uDB}
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [CategoryTheory.Linear R DA] [CategoryTheory.Linear R DB]
variable [HasCoproducts.{max uDA vDA} DA] [HasCoproducts.{max uDB vDB} DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]
variable (Aunit : DA)

omit [HasZeroObject DB] [HasCoproducts.{max uDB vDB} DB]
  [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB] in
/-- The chapter-level generator owner `IsWeakGenerator` is exactly the source zero-detection
criterion for shifted Homs; the forward implication reuses
`detectsZero_of_isWeakGenerator` from Remark `22.37.3`. -/
theorem isWeakGenerator_iff_detectsZero
    (P : DB) :
    IsWeakGenerator P ↔
      ∀ N : DB, (∀ i : ℤ, ∀ f : P ⟶ N⟦i⟧, f = 0) → IsZero N := by
  constructor
  · intro hP N hN
    exact detectsZero_of_isWeakGenerator hP hN
  · intro hP N hNzero
    by_contra hNweak
    push Not at hNweak
    exact hNzero (hP N hNweak)

/-- Lemma 22.37.4 (1): let `R` be a ring, and let `(A,d)` and `(B,d)` be differential
graded `R`-algebras. In the current abstract derived-category surface, `DA` and `DB` denote
`D(A,d)` and `D(B,d)`, and `Aunit` denotes the regular object `A` of `D(A,d)`. The hypothesis
`A = H^0(A)` is represented by the vanishing of the shifted self-Homs of `Aunit` away from
degree zero together with the `R`-algebra identification `End(Aunit) ≃ A`; the usual regular
object compactness and generation facts for `D(A,d)` are explicit hypotheses in this abstract
surface. The bridge owner `RLinearTriangulatedEquivalence R DA DB` packages the ambient
`R`-linear triangulated structure on an equivalence `DA ≌ DB`.

Then `DA` and `DB` are equivalent as `R`-linear triangulated categories if and only if there is
an object `P : DB` which is compact, is a weak generator of `DB`, and whose self-Homs vanish
away from degree zero and have degree-zero endomorphism algebra `A`. The companion theorem
`isWeakGenerator_iff_detectsZero` identifies `IsWeakGenerator` with the source zero-detection
condition on shifted Homs. -/
@[stacks 09S8]
theorem exists_rLinearTriangulatedEquivalence_iff_exists_compact_generator_selfExt
    (hAunit_compact : IsCompactObject Aunit)
    (hAunit_weakGenerator : IsWeakGenerator Aunit)
    (hAunit_selfExt_zero :
      ∀ i : ℤ, i ≠ 0 → ∀ f : Aunit ⟶ Aunit⟦i⟧, f = 0)
    (hAunit_end : Nonempty (End Aunit ≃ₐ[R] A)) :
    Nonempty (RLinearTriangulatedEquivalence R DA DB) ↔
      ∃ P : DB,
        IsCompactObject P ∧
        IsWeakGenerator P ∧
        (∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0) ∧
        Nonempty (End P ≃ₐ[R] A) := sorry

/-- Lemma 22.37.4 (2): for an object `P` satisfying the compact generator and prescribed
self-Ext conditions in part (1), there is an `R`-linear triangulated equivalence constructed from
`P` together with a chosen object-level identification `e.functor.obj Aunit ≅ P` of the image of
the regular object `Aunit` of `D(A,d)` with `P`. The regular object hypotheses from part (1)
remain part of the source-facing data for this equivalence statement. -/
@[stacks 09S8]
theorem exists_rLinearTriangulatedEquivalence_obj_regular_of_compact_generator_selfExt
    (hAunit_compact : IsCompactObject Aunit)
    (hAunit_weakGenerator : IsWeakGenerator Aunit)
    (hAunit_selfExt_zero :
      ∀ i : ℤ, i ≠ 0 → ∀ f : Aunit ⟶ Aunit⟦i⟧, f = 0)
    (hAunit_end : Nonempty (End Aunit ≃ₐ[R] A))
    (P : DB)
    (hP_compact : IsCompactObject P)
    (hP_weakGenerator : IsWeakGenerator P)
    (hP_selfExt_zero :
      ∀ i : ℤ, i ≠ 0 → ∀ f : P ⟶ P⟦i⟧, f = 0)
    (hP_end : Nonempty (End P ≃ₐ[R] A)) :
    ∃ e : RLinearTriangulatedEquivalence R DA DB,
      Nonempty (e.functor.obj Aunit ≅ P) := sorry

end
