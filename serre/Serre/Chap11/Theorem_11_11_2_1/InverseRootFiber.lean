import Serre.Chap11.Theorem_11_11_2_1.ElementarySubgroupBridge

noncomputable section

universe u v w

namespace Representation

section FrobeniusTheorem

open scoped Representation TensorProduct BigOperators SubgroupInduction

variable {G : Type u} [Group G]
variable {A : Type v} [CommRing A] [Algebra A ℂ]

/-- Helper for Theorem 11-11.2-1: in `C × P` with commutative left factor, conjugacy preserves
the left coordinate and is exactly conjugacy on the right coordinate. -/
theorem prod_isConj_iff_left_eq_and_right_isConj
    {C : Type w} {P : Type*} [CommGroup C] [Group P] {x y : C × P} :
    IsConj x y ↔ x.1 = y.1 ∧ IsConj x.2 y.2 := by
  constructor
  · intro hxy
    rw [isConj_iff] at hxy
    rcases hxy with ⟨g, hg⟩
    constructor
    · -- The commutative `C`-coordinate is fixed by conjugation.
      have hfst := congrArg Prod.fst hg
      simpa [mul_assoc] using hfst
    · -- The `P`-coordinate carries the entire conjugacy datum.
      rw [isConj_iff]
      refine ⟨g.2, ?_⟩
      have hsnd := congrArg Prod.snd hg
      simpa [mul_assoc] using hsnd
  · rintro ⟨hfst, hsnd⟩
    rw [isConj_iff] at hsnd ⊢
    rcases hsnd with ⟨u, hu⟩
    -- Conjugating by `(1, u)` leaves the `C`-coordinate untouched and conjugates only in `P`.
    refine ⟨(1, u), ?_⟩
    ext
    · simpa [hfst]
    · simpa [mul_assoc] using hu

/-- Helper for Theorem 11-11.2-1: transporting a conjugacy class through an elementary
decomposition `H ≃ C × P` fixes the cyclic coordinate and leaves only a `P`-conjugacy class. -/
theorem elementary_prod_conjclass_split_local
    {H : Type w} [Group H] [Finite H] [Fintype H] (d : ConjClasses H) (x0 : d.carrier)
    {p : Nat} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let y0 := e.symm (x0 : H)
    ∃ dP : ConjClasses P, ∀ y : C × P, (e y : H) ∈ d.carrier ↔ y.1 = y0.1 ∧ y.2 ∈ dP.carrier := by
  letI : IsCyclic C := hCP.cyclic
  letI : CommGroup C := IsCyclic.commGroup
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let y0 : C × P := e.symm (x0 : H)
  let dP : ConjClasses P := ConjClasses.mk y0.2
  have hx0 : ConjClasses.mk (x0 : H) = d := (ConjClasses.mem_carrier_iff_mk_eq).mp x0.property
  refine ⟨dP, ?_⟩
  intro y
  constructor
  · intro hy
    have hconjH : IsConj (e y) (x0 : H) := by
      apply (ConjClasses.mk_eq_mk_iff_isConj).mp
      exact (ConjClasses.mem_carrier_iff_mk_eq.mp hy).trans hx0.symm
    have hconjProd : IsConj y y0 := by
      rw [isConj_iff] at hconjH ⊢
      rcases hconjH with ⟨a, ha⟩
      refine ⟨e.symm a, ?_⟩
      -- Pull the conjugating element back through the product equivalence.
      simpa [e, y0, mul_assoc] using congrArg e.symm ha
    rcases (prod_isConj_iff_left_eq_and_right_isConj (x := y) (y := y0)).1 hconjProd with
      ⟨hy1, hy2⟩
    constructor
    · exact hy1
    · -- The remaining condition is exactly membership in the induced `P`-conjugacy class.
      exact (ConjClasses.mem_carrier_iff_mk_eq).2 <|
        (ConjClasses.mk_eq_mk_iff_isConj).2 hy2
  · rintro ⟨hy1, hy2⟩
    have hconjP : IsConj y.2 y0.2 := by
      exact (ConjClasses.mk_eq_mk_iff_isConj).mp <|
        (ConjClasses.mem_carrier_iff_mk_eq).mp hy2
    have hconjProd : IsConj y y0 :=
      (prod_isConj_iff_left_eq_and_right_isConj (x := y) (y := y0)).2 ⟨hy1, hconjP⟩
    have hconjH : IsConj (e y) (x0 : H) := by
      rw [isConj_iff] at hconjProd ⊢
      rcases hconjProd with ⟨a, ha⟩
      refine ⟨e a, ?_⟩
      -- Push the product conjugacy witness forward to the ambient group.
      simpa [e, y0, mul_assoc] using congrArg e ha
    exact (ConjClasses.mem_carrier_iff_mk_eq).2 <|
      ((ConjClasses.mk_eq_mk_iff_isConj).2 hconjH).trans hx0

/-- Helper for Theorem 11-11.2-1: after choosing one `n`th root in the conjugacy class, the
transported `n`th-root predicate on `H ≃ C × P` splits into a cyclic power equation and a
`P`-conjugacy-class condition. -/
theorem elementary_prod_rootfiber_filter_split_local
    {H : Type w} [Group H] [Finite H] [Fintype H] (n : ℕ+) (d : ConjClasses H)
    {p : Nat} {C P : Subgroup H} (hCP : IsPElementaryDecomposition p C P)
    (h0 : H) (hh0 : h0 ^ (n : Nat) ∈ d.carrier) :
    let e := hCP.isComplement.prodMulEquiv hCP.commute
    let y0 := e.symm h0
    ∃ dP : ConjClasses P, ∀ y : C × P,
      ((e y : H) ^ (n : Nat) ∈ d.carrier) ↔
        y.1 ^ (n : Nat) = y0.1 ^ (n : Nat) ∧ y.2 ^ (n : Nat) ∈ dP.carrier := by
  letI : IsCyclic C := hCP.cyclic
  letI : CommGroup C := IsCyclic.commGroup
  let e := hCP.isComplement.prodMulEquiv hCP.commute
  let y0 : C × P := e.symm h0
  let x0 : d.carrier := ⟨h0 ^ (n : Nat), hh0⟩
  obtain ⟨dP, hdP⟩ := elementary_prod_conjclass_split_local (d := d) (x0 := x0) hCP
  refine ⟨dP, ?_⟩
  intro y
  -- Apply the conjugacy-class splitter to the powered product point `y ^ n`.
  simpa [e, y0, x0, map_pow, mul_assoc] using hdP (y ^ (n : Nat))

end FrobeniusTheorem

end Representation
