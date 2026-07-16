import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_7
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Group

open Subgroup

variable {H : Type u} [Group H]

-- Source/core/bridge triage:
-- * source-facing: `IsPElementaryDecomposition p C P`, `IsPElementary p H`, and `IsElementary H`.
-- * core/canonical: `IsPGroup`, `Subgroup.IsComplement'`, and `Subgroup.centralizer`.
-- * bridge/view: `Subgroup.IsComplement'.prodMulEquiv` identifies complementary commuting factors
--   with a direct product.
--
-- Primitive data are the cyclic prime-to-`p` factor `C`, the finite `p`-group factor `P`, their
-- centralizing relation, and their complement decomposition. Finiteness of `C`, commutation of
-- individual elements, and finiteness of the ambient group are derived API.

/-- A pair of subgroups `C` and `P` gives a `p`-elementary decomposition of `H` if `p` is prime,
`C` is a finite cyclic group of order prime to `p`, `P` is a finite `p`-group, `C` centralizes
`P`, and every element of `H` admits a unique factorization as an element of `C` times an element
of `P`. -/
def IsPElementaryDecomposition (p : ℕ) (C P : Subgroup H) : Prop :=
  Nat.Prime p ∧
    Finite P ∧
      IsCyclic C ∧
        Nat.Coprime p (Nat.card C) ∧
          IsPGroup p P ∧
            C ≤ centralizer (P : Set H) ∧
              C.IsComplement' P

namespace IsPElementaryDecomposition

variable {p : ℕ} {C P : Subgroup H}

/-- The prime attached to a `p`-elementary decomposition. -/
theorem prime (h : IsPElementaryDecomposition p C P) : Nat.Prime p := by
  rcases h with ⟨hp, -, -, -, -, -, -⟩
  exact hp

/-- The cyclic factor in a `p`-elementary decomposition is finite. -/
theorem finite_cyclic_factor (h : IsPElementaryDecomposition p C P) : Finite C := by
  rcases h with ⟨hp, -, -, hcoprime, -, -, -⟩
  by_contra hC
  haveI : Infinite C := not_finite_iff_infinite.mp hC
  have hc : Nat.Coprime p 0 := by
    simpa [Nat.card_eq_zero_of_infinite] using hcoprime
  rw [Nat.coprime_zero_right] at hc
  exact hp.ne_one hc

/-- The `p`-group factor in a `p`-elementary decomposition is finite. -/
theorem finite_pGroup_factor (h : IsPElementaryDecomposition p C P) : Finite P := by
  rcases h with ⟨-, hP, -, -, -, -, -⟩
  exact hP

/-- The cyclic factor in a `p`-elementary decomposition. -/
theorem cyclic (h : IsPElementaryDecomposition p C P) : IsCyclic C := by
  rcases h with ⟨-, -, hC, -, -, -, -⟩
  exact hC

/-- The cyclic factor has order prime to `p`. -/
theorem coprime_card (h : IsPElementaryDecomposition p C P) :
    Nat.Coprime p (Nat.card C) := by
  rcases h with ⟨-, -, -, hcoprime, -, -, -⟩
  exact hcoprime

/-- The second factor is a `p`-group. -/
theorem isPGroup (h : IsPElementaryDecomposition p C P) : IsPGroup p P := by
  rcases h with ⟨-, -, -, -, hP, -, -⟩
  exact hP

/-- The cyclic factor centralizes the `p`-group factor. -/
theorem centralizes (h : IsPElementaryDecomposition p C P) :
    C ≤ centralizer (P : Set H) := by
  rcases h with ⟨-, -, -, -, -, hcentral, -⟩
  exact hcentral

/-- The two factors are complementary subgroups of `H`. -/
theorem isComplement (h : IsPElementaryDecomposition p C P) : C.IsComplement' P := by
  rcases h with ⟨-, -, -, -, -, -, hcomp⟩
  exact hcomp

/-- Elements of the two factors commute. -/
theorem commute (h : IsPElementaryDecomposition p C P) (c : C) (u : P) :
    Commute (c : H) (u : H) := by
  change (c : H) * (u : H) = (u : H) * (c : H)
  exact (h.centralizes c.2 u.1 u.2).symm

/-- A `p`-elementary decomposition has finite ambient group. -/
theorem finite (h : IsPElementaryDecomposition p C P) : Finite H := by
  letI : Finite C := h.finite_cyclic_factor
  letI : Finite P := h.finite_pGroup_factor
  exact Finite.of_equiv (C × P) (h.isComplement.prodMulEquiv h.commute).toEquiv

end IsPElementaryDecomposition

/-- Definition 10-10.1-3: a group `H` is `p`-elementary if `p` is prime and `H` admits finite
complementary subgroups `C` and `P`, with `C` cyclic of order prime to `p`, `P` a `p`-group, and
`C` centralizing `P`. -/
def IsPElementary (p : ℕ) (H : Type u) [Group H] : Prop :=
  ∃ C P : Subgroup H, IsPElementaryDecomposition p C P

/-- A group is elementary if it is `p`-elementary for some `p`. -/
def IsElementary (H : Type u) [Group H] : Prop :=
  ∃ p : ℕ, IsPElementary p H

-- Proof sketch: this is the direct elimination of the existential definition of
-- `IsPElementary`.
theorem IsPElementary.prime {p : ℕ} (hH : IsPElementary p H) : Nat.Prime p := by
  rcases hH with ⟨C, P, h⟩
  exact h.prime

/-- A `p`-elementary group is finite. -/
theorem IsPElementary.finite {p : ℕ} (hH : IsPElementary p H) : Finite H := by
  rcases hH with ⟨C, P, h⟩
  exact h.finite

section

variable {p : ℕ}

-- Proof sketch: choose a `p`-elementary decomposition `H ≃ C × P`; the cyclic factor is abelian
-- and hence nilpotent, the `p`-group factor is nilpotent by `IsPGroup.isNilpotent`, and the
-- products and isomorphic images of nilpotent groups are nilpotent.
/-- A `p`-elementary group is nilpotent. -/
theorem IsPElementary.isNilpotent (hH : IsPElementary p H) :
    Group.IsNilpotent H := by
  rcases hH with ⟨C, P, h⟩
  letI : Fact p.Prime := ⟨h.prime⟩
  letI : Finite P := h.finite_pGroup_factor
  letI : Group.IsNilpotent P := h.isPGroup.isNilpotent
  letI : IsCyclic C := h.cyclic
  let _ : CommGroup C := IsCyclic.commGroup
  exact (Group.isNilpotent_congr (h.isComplement.prodMulEquiv h.commute)).1 inferInstance

variable {C P : Subgroup H}

/-- Helper for Definition 10-10.1-3: the coordinates of `x` under the complementary product
equivalence multiply back to `x`. -/
theorem IsPElementaryDecomposition.symm_apply_eq_mul_coords
    (h : IsPElementaryDecomposition p C P) (x : H) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).1 : H) * ((e.symm x).2 : H) = x := by
  let e := h.isComplement.prodMulEquiv h.commute
  -- Unfold the product equivalence only at the final multiplication formula.
  change e (e.symm x) = x
  exact e.apply_symm_apply x

/-- Helper for Definition 10-10.1-3: the subgroup coordinates of `x` form its `p`-component
decomposition. -/
theorem IsPElementaryDecomposition.symm_isPComponentDecomposition
    (h : IsPElementaryDecomposition p C P) (x : H) :
    let e := h.isComplement.prodMulEquiv h.commute
    IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The `P`-coordinate has `p`-power order because `P` is a `p`-group.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup) ((e.symm x).2)
    exact ⟨n, by simpa [Subgroup.orderOf_mk] using hn⟩
  · -- The `C`-coordinate has order dividing the prime-to-`p` order of `C`.
    have hdiv : orderOf (((e.symm x).1 : H)) ∣ Nat.card C := by
      simpa using C.orderOf_dvd_natCard ((e.symm x).1).2
    exact h.coprime_card.of_dvd_right hdiv
  · -- Coordinates commute because every element of `C` centralizes every element of `P`.
    exact (h.commute ((e.symm x).1) ((e.symm x).2)).symm
  · -- The product equivalence reconstructs `x`, and commutation swaps the factor order.
    calc
      ((e.symm x).2 : H) * ((e.symm x).1 : H) = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
        exact (h.commute ((e.symm x).1) ((e.symm x).2)).symm
      _ = x := by
        simpa [e] using h.symm_apply_eq_mul_coords x

/-- Helper for Definition 10-10.1-3: a `p`-regular element has trivial `P`-coordinate in the
canonical `C × P` decomposition. -/
theorem IsPElementaryDecomposition.right_coord_eq_one_of_isPRegular
    (h : IsPElementaryDecomposition p C P) {x : H} (hx : IsPRegular p x) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).2 : H) = 1 := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  have hcoords : IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
    simpa [e] using h.symm_isPComponentDecomposition x
  have htriv : IsPComponentDecomposition p x 1 x := by
    -- The trivial decomposition of a `p`-regular element has vanishing `p`-part.
    refine ⟨?_, hx, Commute.one_left _, by simp⟩
    exact ⟨0, by simp⟩
  -- Uniqueness of `p`-component decompositions identifies the `P`-coordinate with `1`.
  exact hcoords.eq_pUnipotentComponent.trans htriv.eq_pUnipotentComponent.symm

/-- Helper for Definition 10-10.1-3: a `p`-element has trivial `C`-coordinate in the canonical
`C × P` decomposition. -/
theorem IsPElementaryDecomposition.left_coord_eq_one_of_isPElement
    (h : IsPElementaryDecomposition p C P) {x : H} (hx : IsPElement p x) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).1 : H) = 1 := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  have hcoords : IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
    simpa [e] using h.symm_isPComponentDecomposition x
  have htriv : IsPComponentDecomposition p x x 1 := by
    -- The trivial decomposition of a `p`-element has vanishing prime-to-`p` part.
    refine ⟨hx, isPRegular_one p, Commute.one_right _, by simp⟩
  -- Uniqueness of `p`-component decompositions identifies the `C`-coordinate with `1`.
  exact hcoords.eq_pRegularComponent.trans htriv.eq_pRegularComponent.symm

-- Proof sketch: in a `p`-elementary decomposition, every element factors uniquely as `c * u`
-- with `c ∈ C` and `u ∈ P`. The order of `c` is prime to `p`, the order of `u` is a power of `p`,
-- and the factors commute, so the `p'`-elements are exactly the elements of `C`.
/-- In a `p`-elementary decomposition, the cyclic factor is exactly the set of `p`-regular
elements. -/
theorem IsPElementaryDecomposition.cyclic_factor_eq_setOf_isPRegular
    (h : IsPElementaryDecomposition p C P) :
    (C : Set H) = {x | IsPRegular p x} := by
  ext x
  constructor
  · intro hx
    -- Membership in `C` forces the order of `x` to divide the prime-to-`p` order of `C`.
    have hdiv : orderOf x ∣ Nat.card C := C.orderOf_dvd_natCard hx
    exact h.coprime_card.of_dvd_right hdiv
  · intro hx
    let e := h.isComplement.prodMulEquiv h.commute
    have hright : ((e.symm x).2 : H) = 1 := by
      simpa [e] using h.right_coord_eq_one_of_isPRegular hx
    -- Route correction: rather than doing fresh order arithmetic in `H`, collapse the `P`
    -- coordinate to `1` and read `x` off from the remaining `C`-coordinate.
    have hx_eq : x = ((e.symm x).1 : H) := by
      calc
        x = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
          simpa [e] using (h.symm_apply_eq_mul_coords x).symm
        _ = ((e.symm x).1 : H) * 1 := by rw [hright]
        _ = ((e.symm x).1 : H) := by simp
    rw [hx_eq]
    exact ((e.symm x).1).2

-- Proof sketch: use the same unique factorization as above. The commuting decomposition separates
-- the `p`-power part and the prime-to-`p` part of the order, so the `p`-elements are exactly the
-- elements of the `p`-group factor `P`.
/-- In a `p`-elementary decomposition, the `p`-group factor is exactly the set of
`p`-elements. -/
theorem IsPElementaryDecomposition.p_group_factor_eq_setOf_isPElement
    (h : IsPElementaryDecomposition p C P) :
    (P : Set H) = {x | IsPElement p x} := by
  letI : Fact p.Prime := ⟨h.prime⟩
  ext x
  constructor
  · intro hx
    -- Membership in the `p`-group factor gives a `p`-power order immediately.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup) ⟨x, hx⟩
    exact ⟨n, by simpa [Subgroup.orderOf_mk] using hn⟩
  · intro hx
    let e := h.isComplement.prodMulEquiv h.commute
    have hleft : ((e.symm x).1 : H) = 1 := by
      simpa [e] using h.left_coord_eq_one_of_isPElement hx
    -- Once the prime-to-`p` coordinate vanishes, `x` is exactly the `P`-coordinate.
    have hx_eq : x = ((e.symm x).2 : H) := by
      calc
        x = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
          simpa [e] using (h.symm_apply_eq_mul_coords x).symm
        _ = 1 * ((e.symm x).2 : H) := by rw [hleft]
        _ = ((e.symm x).2 : H) := by simp
    rw [hx_eq]
    exact ((e.symm x).2).2

end

end Group
