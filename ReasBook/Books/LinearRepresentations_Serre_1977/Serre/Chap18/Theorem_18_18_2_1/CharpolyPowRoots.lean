import Mathlib

noncomputable section

universe u x

open Polynomial

namespace Representation

/-- Flipping the sign of every factor of a multiset product over a field multiplies the
product by `(-1) ^ card`. -/
private lemma prod_map_sub_aux {k : Type u} [Field k] {α : Type*} (m : Multiset α)
    (f g : α → k) :
    (m.map fun a => f a - g a).prod
      = (-1 : k) ^ Multiset.card m * (m.map fun a => g a - f a).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
    ring

/-- Interchange of a double multiset product in a commutative monoid. -/
private lemma prod_swap_aux {k : Type u} [CommMonoid k] {α : Type*} {β : Type*}
    (s : Multiset α) (t : Multiset β) (f : α → β → k) :
    (s.map fun a => (t.map fun b => f a b).prod).prod
      = (t.map fun b => (s.map fun a => f a b).prod).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.prod_map_mul]

/-- The determinant of `aeval u` applied to a product of linear factors is the product of the
determinants of the corresponding linear endomorphisms. -/
private lemma det_aeval_prod_aux {k : Type u} [Field k]
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (u : V →ₗ[k] V) (m : Multiset k) :
    LinearMap.det (aeval u (m.map fun β => X - C β).prod)
      = (m.map fun β => LinearMap.det (u - algebraMap k (V →ₗ[k] V) β)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, map_mul, Multiset.map_cons,
      Multiset.prod_cons, ih]
    congr 2
    rw [map_sub, aeval_X, aeval_C]

/-- Over an algebraically closed field, the characteristic-polynomial root multiset of the
`b`-th power of an endomorphism is the multiset of `b`-th powers of the roots. -/
theorem charpoly_pow_roots {k : Type u} [Field k] [IsAlgClosed k]
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (u : V →ₗ[k] V) {b : ℕ} (hb : b ≠ 0) :
    (u ^ b).charpoly.roots = u.charpoly.roots.map (· ^ b) := by
  -- It suffices to identify the polynomials themselves.
  suffices h : (u ^ b).charpoly
      = ((u.charpoly.roots.map (· ^ b)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  -- Facts about `u.charpoly`.
  have hu_splits : u.charpoly.Splits := IsAlgClosed.splits _
  have hu_card : Multiset.card u.charpoly.roots = Module.finrank k V := by
    rw [← hu_splits.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  -- `det` of a negated endomorphism.
  have hneg : ∀ f : V →ₗ[k] V,
      LinearMap.det (-f) = (-1 : k) ^ Module.finrank k V * LinearMap.det f := by
    intro f
    rw [← neg_one_smul k f, LinearMap.det_smul]
  -- `det (u - β)` as a product over the roots of `u.charpoly`.
  have h3 : ∀ β : k, LinearMap.det (u - algebraMap k (V →ₗ[k] V) β)
      = (u.charpoly.roots.map fun μ => μ - β).prod := by
    intro β
    have e1 : LinearMap.det (u - algebraMap k (V →ₗ[k] V) β)
        = (-1 : k) ^ Module.finrank k V
            * (u.charpoly.roots.map fun μ => β - μ).prod := by
      rw [show u - algebraMap k (V →ₗ[k] V) β = -(algebraMap k (V →ₗ[k] V) β - u) from
          (neg_sub _ _).symm,
        hneg, ← LinearMap.eval_charpoly, hu_splits.eval_eq_prod_roots,
        (LinearMap.charpoly_monic u).leadingCoeff, one_mul]
    have e2 : (u.charpoly.roots.map fun μ => μ - β).prod
        = (-1 : k) ^ Module.finrank k V
            * (u.charpoly.roots.map fun μ => β - μ).prod := by
      rw [← hu_card]
      exact prod_map_sub_aux _ _ _
    rw [e1, e2]
  -- Compare evaluations at every point of the (infinite) field `k`.
  apply Polynomial.funext
  intro y
  -- Evaluation of the right-hand side.
  have hQ : (((u.charpoly.roots.map (· ^ b)).map fun a => X - C a).prod).eval y
      = (u.charpoly.roots.map fun μ => y - μ ^ b).prod := by
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    simp
  rw [hQ, LinearMap.eval_charpoly]
  -- The auxiliary polynomial `X ^ b - C y`.
  set p : k[X] := X ^ b - C y with hp_def
  have hp_monic : p.Monic := monic_X_pow_sub_C y hb
  have hp_splits : p.Splits := IsAlgClosed.splits p
  have hp_factor : p = (p.roots.map fun β => X - C β).prod :=
    hp_splits.eq_prod_roots_of_monic hp_monic
  -- `algebraMap y - u ^ b = -(aeval u p)`.
  have h1 : algebraMap k (V →ₗ[k] V) y - u ^ b = -(aeval u p) := by
    rw [hp_def, map_sub, map_pow, aeval_X, aeval_C, neg_sub]
  -- Evaluation of `p` at any point, as a product over its roots.
  have h4 : ∀ μ : k, (p.roots.map fun β => μ - β).prod = μ ^ b - y := by
    intro μ
    have e := hp_splits.eval_eq_prod_roots μ
    rw [hp_monic.leadingCoeff, one_mul] at e
    rw [← e, hp_def]
    simp
  calc LinearMap.det (algebraMap k (V →ₗ[k] V) y - u ^ b)
      = (-1 : k) ^ Module.finrank k V * LinearMap.det (aeval u p) := by
        rw [h1, hneg]
    _ = (-1 : k) ^ Module.finrank k V
        * (p.roots.map fun β => LinearMap.det (u - algebraMap k (V →ₗ[k] V) β)).prod := by
        conv_lhs => rw [hp_factor]
        rw [det_aeval_prod_aux]
    _ = (-1 : k) ^ Module.finrank k V
        * (p.roots.map fun β => (u.charpoly.roots.map fun μ => μ - β).prod).prod := by
        simp only [h3]
    _ = (-1 : k) ^ Module.finrank k V
        * (u.charpoly.roots.map fun μ => (p.roots.map fun β => μ - β).prod).prod := by
        rw [prod_swap_aux p.roots u.charpoly.roots fun β μ => μ - β]
    _ = (-1 : k) ^ Module.finrank k V
        * (u.charpoly.roots.map fun μ => μ ^ b - y).prod := by
        simp only [h4]
    _ = (u.charpoly.roots.map fun μ => y - μ ^ b).prod := by
        rw [prod_map_sub_aux u.charpoly.roots (fun μ => μ ^ b) fun _ => y, hu_card,
          ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

end Representation
