import Mathlib
import Serre.Chap11.Theorem_11_11_2_1
import Serre.RepresentationTheory.SymmetricExterior
import Serre.Chap09.Exercise_9_9_1_3.ScalarSymmetricPowers

open scoped Representation

noncomputable section

universe u v w

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem neg_charpoly_reverse_coeff_eq_signed_esymm_roots
    [IsAlgClosed k] (A : V →ₗ[k] V) (n : ℕ) :
    (((-A).charpoly.reverse : Polynomial k).coeff n) =
      (-1 : k) ^ n * (((-A).charpoly).roots.esymm n) := by
  let p : Polynomial k := (-A).charpoly
  have hp_monic : p.Monic := by
    -- Characteristic polynomials are monic, so Vieta applies with leading coefficient `1`.
    simpa [p] using LinearMap.charpoly_monic (-A)
  by_cases hn : n ≤ p.natDegree
  · -- In the in-range case, `coeff_reverse` converts the reversed coefficient into the
    -- complementary coefficient of `p`, and Vieta rewrites that coefficient via the roots.
    rw [show (((-A).charpoly.reverse : Polynomial k).coeff n) = p.reverse.coeff n by rfl]
    rw [Polynomial.coeff_reverse, Polynomial.revAt_le hn]
    have hcoeff :=
      Polynomial.coeff_eq_esymm_roots_of_splits (p := p) (IsAlgClosed.splits p)
        (k := p.natDegree - n) (Nat.sub_le _ _)
    rw [hcoeff, hp_monic.leadingCoeff, one_mul]
    have hsub : p.natDegree - (p.natDegree - n) = n := by
      omega
    simp [hsub, p]
  · -- Outside the degree range, both sides vanish: the reversed polynomial has no such
    -- coefficient, and the corresponding elementary symmetric sum is indexed above the root count.
    have hnlt : p.natDegree < n := lt_of_not_ge hn
    rw [show (((-A).charpoly.reverse : Polynomial k).coeff n) = p.reverse.coeff n by rfl]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · have hcard : p.roots.card < n := by
        rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots]
        exact hnlt
      rw [show
          (-1 : k) ^ n * p.roots.esymm n =
            (-1 : k) ^ n * (Multiset.map Multiset.prod (Multiset.powersetCard n p.roots)).sum by
          rfl]
      rw [Multiset.powersetCard_eq_empty _ hcard]
      simp
    · exact lt_of_le_of_lt p.reverse_natDegree_le hnlt
/-- Helper for Exercise 9-9.1-3: substituting `T ↦ -T` into `det (1 - M T)` gives
`det (1 + M T)` at the matrix-polynomial level. -/
theorem matrix_det_neg_subst
    {ι : Type w} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k) :
    Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C) =
      Polynomial.comp
        (Matrix.det (1 - (Polynomial.X : Polynomial k) • M.map Polynomial.C))
        (-Polynomial.X) := by
  let e : Polynomial k →+* Polynomial k :=
    Polynomial.eval₂RingHom (Polynomial.C : k →+* Polynomial k) (-Polynomial.X)
  have heC (a : k) : e (Polynomial.C a) = Polynomial.C a := by
    simp [e]
  have heX : e (Polynomial.X : Polynomial k) = -Polynomial.X := by
    simp [e]
  -- Apply the polynomial endomorphism `T ↦ -T` entrywise before taking determinants.
  change Matrix.det (1 + (Polynomial.X : Polynomial k) • M.map Polynomial.C) =
      e (Matrix.det (1 - (Polynomial.X : Polynomial k) • M.map Polynomial.C))
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  -- On each entry, the substitution flips the sign of the `T`-term and preserves constants.
  rw [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, RingHom.map_sub, RingHom.map_one, RingHom.map_mul, heX, heC]
    simp
  · rw [if_neg h, RingHom.map_sub, RingHom.map_zero, RingHom.map_mul, heX, heC]
    simp

end

end Representation
