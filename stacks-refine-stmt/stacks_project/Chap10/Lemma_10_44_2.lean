import Mathlib
import stacks_project.Chap10.Definition_10_42_1
import stacks_project.Chap10.Lemma_10_43_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

section

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]

/-- The subfield of `AlgebraicClosure k` consisting of elements whose `p`-th power lies in the
image of `k`; this is a concrete model for `k^{1/p}`. -/
private noncomputable def onePthRootSubfield : Subfield (AlgebraicClosure k) :=
  let _ : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  Subfield.comap (frobenius (AlgebraicClosure k) p) ((algebraMap k (AlgebraicClosure k)).fieldRange)

-- Proof sketch: an element of `k` maps into the Frobenius preimage of the base field because
-- `(algebraMap k (AlgebraicClosure k) x) ^ p = algebraMap k (AlgebraicClosure k) (x ^ p)`.
/-- The image of `k` is contained in the chosen model of `k^{1/p}` inside `AlgebraicClosure k`. -/
private theorem onePthRootSubfield_algebraMap_mem (x : k) :
    algebraMap k (AlgebraicClosure k) x ∈ onePthRootSubfield k p := sorry

/-- The intermediate field of `AlgebraicClosure k` modeling the extension `k^{1/p} / k`. -/
noncomputable def onePthRootExtension : IntermediateField k (AlgebraicClosure k) :=
  (onePthRootSubfield k p).toIntermediateField (onePthRootSubfield_algebraMap_mem k p)

-- Proof sketch: unfold `onePthRootExtension` and `onePthRootSubfield`; membership in the Frobenius
-- comap is exactly the condition that the `p`-th power lies in the image of `k`.
/-- An element of `AlgebraicClosure k` belongs to the chosen `k^{1/p}` exactly when its `p`-th
power comes from `k`. -/
theorem mem_onePthRootExtension_iff {x : AlgebraicClosure k} :
    x ∈ onePthRootExtension k p ↔
      x ^ p ∈ (algebraMap k (AlgebraicClosure k)).fieldRange := sorry

end

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

-- Proof sketch: `(1) → (4)` is the separable-implies-geometrically-reduced direction from the
-- previous section; `(4) → (3)` is obtained by base change to the chosen model of `k^{1/p}`;
-- `(3) → (2)` uses the Frobenius-induced multiplication map on `K ⊗[k] k^{1/p}` and reducedness
-- to deduce injectivity; `(2) → (1)` reduces to the finitely generated case and applies the
-- separating-transcendence-basis criterion from Lemma `10.44.1`.
/-- Lemma 10.44.2: for a field extension `K / k` of characteristic `p > 0`, the following are
equivalent: `K` is separable over `k` in the sense of Definition `10.42.1`, Frobenius preserves
`k`-linear independence on finite subsets of `K`, the base change `K ⊗[k] k^{1/p}` is reduced,
and `K` is geometrically reduced over `k`. -/
theorem isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced :
    List.TFAE [
      IsSeparableOver k K,
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
      IsReduced (K ⊗[k] onePthRootExtension k p),
      IsGeometricallyReduced k K
    ] := sorry

/-- Lemma 10.44.2, clauses `(1) ↔ (2)`: Frobenius preserves `k`-linear independence on every
finite subset of `K` iff `K / k` is separable in the sense of Definition `10.42.1 (2)`. -/
theorem isSeparableOver_iff_linearIndepOn_pow :
    IsSeparableOver k K ↔
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K) := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 1 (by simp [l]) (by simp [l]))

/-- Lemma 10.44.2, clauses `(1) ↔ (3)`: reducedness after base change to the chosen model
`onePthRootExtension k p` of `k^{1/p}` is equivalent to separability of `K / k`. -/
theorem isSeparableOver_iff_isReduced_tensorProduct_onePthRootExtension :
    IsSeparableOver k K ↔ IsReduced (K ⊗[k] onePthRootExtension k p) := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 2 (by simp [l]) (by simp [l]))

/-- Lemma 10.44.2, clauses `(1) ↔ (4)`: for field extensions in characteristic `p`, geometric
reducedness is equivalent to separability in the sense of Definition `10.42.1 (2)`. -/
theorem isSeparableOver_iff_isGeometricallyReduced_of_charP
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsSeparableOver k K ↔ IsGeometricallyReduced k K := by
  let l : List Prop := [
    IsSeparableOver k K,
    ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K),
    IsReduced (K ⊗[k] onePthRootExtension k p),
    IsGeometricallyReduced k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using isSeparableOver_tfae_linearIndepOn_pow_reduced_onePthRoot_geometricallyReduced
  simpa [l] using (htfae.out 0 3 (by simp [l]) (by simp [l]))

end

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

-- Proof sketch: in positive characteristic, specialize
-- `isSeparableOver_iff_isGeometricallyReduced_of_charP` to `p := ringChar k`; in characteristic
-- zero, separability and geometric reducedness both follow from the characteristic-zero case of
-- the chapter.
/-- Lemma 10.44.2, clauses `(1) ↔ (4)`: for any field extension `K / k`, geometric reducedness is
equivalent to separability in the sense of Definition `10.42.1 (2)`. -/
theorem isSeparableOver_iff_isGeometricallyReduced :
    IsSeparableOver k K ↔ IsGeometricallyReduced k K := by
  have hzero : ringChar k = 0 ↔ CharZero k := CharP.ringChar_zero_iff_CharZero k
  constructor
  · intro hsep
    letI : IsSeparableOver k K := hsep
    exact isGeometricallyReduced_of_isSeparableOver
  · intro hgeom
    by_cases h0 : ringChar k = 0
    · letI : CharZero k := hzero.1 h0
      exact ⟨fun L hL ↦ by
        letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
        infer_instance⟩
    · letI : CharP k (ringChar k) := inferInstance
      have hprime : (ringChar k).Prime := CharP.char_prime_of_ne_zero k h0
      letI : Fact (ringChar k).Prime := ⟨hprime⟩
      let hchar : IsSeparableOver k K ↔ IsGeometricallyReduced k K :=
        isSeparableOver_iff_isGeometricallyReduced_of_charP (ringChar k)
      exact hchar.2 hgeom

end
