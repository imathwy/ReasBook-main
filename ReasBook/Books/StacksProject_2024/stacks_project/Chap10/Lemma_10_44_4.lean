import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Lemma_10_44_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_45_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

-- Proof sketch: the implications from algebraic closure to perfect closure to `k^{1/p}` and from
-- the perfect closure to arbitrary finite purely inseparable extensions follow from the canonical
-- embeddings among these extensions. For `(1) → (5)`, reduce an arbitrary field extension to a
-- finitely generated one and use the purely inseparable lift from Lemma `10.42.4` together with
-- reducedness under separably generated extensions from Lemma `10.43.6`. For `(2) → (5)`, first
-- deduce that `S` is reduced, then check geometric reducedness on localizations at minimal primes
-- using Lemma `10.44.2`, and finally apply Lemma `10.43.7`.
/-- Lemma 10.44.4: for a field `k` of characteristic `p`, the following are equivalent for a
commutative `k`-algebra `S`: every finite purely inseparable extension `k' / k` yields a reduced
base change `k' ⊗[k] S`, the base change to the chosen model `onePthRootExtension k p` of
`k^{1/p}` is reduced, the base change to the relative perfect closure
`perfectClosure k (AlgebraicClosure k)` modeling `k^{perf}` is reduced, the base change to
`AlgebraicClosure k` is reduced, and `S` is geometrically reduced over `k`. -/
theorem isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced :
    List.TFAE [
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S),
      IsReduced (onePthRootExtension k p ⊗[k] S),
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
      IsReduced (AlgebraicClosure k ⊗[k] S),
      IsGeometricallyReduced k S
    ] := sorry

/-- Lemma 10.44.4, clause `(2) ↔ (5)`: geometric reducedness is equivalent to reducedness after
base change to the chosen model `onePthRootExtension k p` of `k^{1/p}`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_onePthRootExtension
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsGeometricallyReduced k S ↔ IsReduced (onePthRootExtension k p ⊗[k] S) :=
  by
    let l : List Prop := [
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S),
      IsReduced (onePthRootExtension k p ⊗[k] S),
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
      IsReduced (AlgebraicClosure k ⊗[k] S),
      IsGeometricallyReduced k S
    ]
    have htfae : List.TFAE l := by
      simpa [l] using
        isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
    constructor
    · intro h
      letI : IsGeometricallyReduced k S := h
      infer_instance
    · intro h
      exact (htfae.out 1 4 (by simp [l]) (by simp [l])).mp h

end

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Lemma 10.44.4, clause `(3) ↔ (5)`: geometric reducedness is equivalent to reducedness after
base change to the canonical perfect closure `perfectClosure k (AlgebraicClosure k)`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_perfectClosure :
    IsGeometricallyReduced k S ↔
      IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S) :=
  by
    constructor
    · intro h
      letI : IsGeometricallyReduced k S := h
      infer_instance
    · intro h
      by_cases h0 : ringChar k = 0
      · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
        letI : PerfectField k := PerfectField.ofCharZero
        let kperf := perfectClosure k (AlgebraicClosure k)
        obtain ⟨e, -⟩ := perfectClosure_algebraicClosure_existsUnique_algEquiv k k
        let e' : kperf ⊗[k] S ≃ₐ[k] S :=
          (Algebra.TensorProduct.congr e (AlgEquiv.refl : S ≃ₐ[k] S)).trans
            (Algebra.TensorProduct.lid k S)
        letI : IsReduced (kperf ⊗[k] S) := h
        letI : IsReduced S := isReduced_of_injective e'.symm.toRingHom e'.symm.injective
        infer_instance
      · letI : CharP k (ringChar k) := inferInstance
        have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
        letI : Fact (ringChar k).Prime := ⟨hprime⟩
        let l : List Prop := [
          ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
            [IsPurelyInseparable k k'],
            IsReduced (k' ⊗[k] S),
          IsReduced (onePthRootExtension k (ringChar k) ⊗[k] S),
          IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
          IsReduced (AlgebraicClosure k ⊗[k] S),
          IsGeometricallyReduced k S
        ]
        have htfae : List.TFAE l := by
          simpa [l] using
            isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
        exact (htfae.out 2 4 (by simp [l]) (by simp [l])).mp h

/-- Lemma 10.44.4, clause `(1) ↔ (5)`: a commutative `k`-algebra `S` is geometrically reduced
iff every finite purely inseparable extension `k' / k` yields a reduced base change
`k' ⊗[k] S`. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable :
    IsGeometricallyReduced k S ↔
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsReduced (k' ⊗[k] S) := by
  constructor
  · intro h k' _ _ _ _
    letI : IsGeometricallyReduced k S := h
    infer_instance
  · intro h
    by_cases h0 : ringChar k = 0
    · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
      let ek : ULift.{v} k ≃ₐ[k] k := ULift.algEquiv
      letI : IsPurelyInseparable k (ULift.{v} k) :=
        ek.symm.isPurelyInseparable
      have hk : IsReduced (ULift.{v} k ⊗[k] S) := h (ULift.{v} k)
      let e : ULift.{v} k ⊗[k] S ≃ₐ[k] S :=
        (Algebra.TensorProduct.congr ek (AlgEquiv.refl : S ≃ₐ[k] S)).trans
          (Algebra.TensorProduct.lid k S)
      letI : IsReduced (ULift.{v} k ⊗[k] S) := hk
      letI : IsReduced S := isReduced_of_injective e.symm.toRingHom e.symm.injective
      letI : PerfectField k := PerfectField.ofCharZero
      infer_instance
    · letI : CharP k (ringChar k) := inferInstance
      have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
      letI : Fact (ringChar k).Prime := ⟨hprime⟩
      let l : List Prop := [
        ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
          IsReduced (k' ⊗[k] S),
        IsReduced (onePthRootExtension k (ringChar k) ⊗[k] S),
        IsReduced (perfectClosure k (AlgebraicClosure k) ⊗[k] S),
        IsReduced (AlgebraicClosure k ⊗[k] S),
        IsGeometricallyReduced k S
      ]
      have htfae : List.TFAE l := by
        simpa [l] using
          isReduced_tensorProduct_tfae_finitePurelyInseparable_onePthRoot_perfectClosure_algebraicClosure_geometricallyReduced
      exact (htfae.out 0 4 (by simp [l]) (by simp [l])).mp h

/- Lemma 10.44.4, clause `(4) ↔ (5)`: this is exactly the owner-class characterization
`isGeometricallyReduced_iff`. -/
recall isGeometricallyReduced_iff

end
