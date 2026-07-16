import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/- Domain triage:
- `source-facing`: the four-way field-extension criterion for normality in Lemma `10.165.1`;
- `core/canonical`: the ring-level owner `IsNormalRing` together with the tensor base-change
  objects `k' ⊗[k] A`;
- `bridge/view`: the pairwise clause projections extracted from the `List.TFAE`.

The theorem below should remain the source-facing TFAE. The individual implications among its
clauses are derived API and should be named once here, then reused downstream instead of rebuilding
the same proposition list locally.
-/
-- Proof sketch: `(1) → (2) → (3)` and `(1) → (4)` are immediate. For `(4) → (3)`, embed any
-- finite purely inseparable extension into the chosen perfect closure and descend normality along
-- the induced faithfully flat base-change map. For `(2) → (1)`, write an arbitrary field
-- extension as a directed colimit of finitely generated subextensions and apply stability of
-- normality under filtered colimits. For `(3) → (2)`, replace a finitely generated extension by a
-- finite purely inseparable extension that becomes separable over a finite purely inseparable
-- extension of the base, then use ascent along smooth algebras, localization, and faithful-flat
-- descent.
/-- Lemma 10.165.1: for a commutative `k`-algebra `A`, the following are equivalent: every base
change `k' ⊗[k] A` to a field extension `k' / k` is a normal ring, it suffices to check this for
finitely generated field extensions, it suffices to check this for finite purely inseparable field
extensions, and it suffices to check it after base change to the chosen model
`perfectClosure k (AlgebraicClosure k)` of `k^{perf}`. -/
theorem isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure :
    List.TFAE [
      ∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A),
      IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
    ] := sorry

/-- Lemma 10.165.1, clauses `(1) ↔ (3)`: it is enough to test normality of all tensor base
changes `k' ⊗[k] A` on finite purely inseparable field extensions `k' / k`. -/
theorem forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable :
    (∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A)) ↔
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A) := by
  let l : List Prop := [
    ∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type w) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
      IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A),
    IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
  ]
  have htfae : List.TFAE l := by
    simpa [l] using
      isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure
  simpa [l] using htfae.out 0 2 (by simp [l]) (by simp [l])

end
