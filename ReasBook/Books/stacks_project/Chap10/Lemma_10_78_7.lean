import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: finite locally free modules over a semilocal ring, controlled by the fiber-rank
  function on `Spec R`;
- inspected owner-style declarations:
  `Module.free_of_flat_of_finrank_eq`,
  `Module.isLocallyConstant_rankAtStalk`,
  `Module.rankAtStalk_eq`,
  `Ideal.bijective_algebraMap_quotient_residueField`;
- owner abstraction: the canonical rank function `Module.rankAtStalk` together with the freeness
  criterion `Module.free_of_flat_of_finrank_eq`;
- layer: `source-facing`; the public theorem is the connected-spectrum corollary of the owner API;
- primitive data: the ring `R`, module `M`, and the semilocal/connectedness hypotheses;
- derived API: constancy of maximal fiber dimensions and the resulting `Module.Free R M`.
-/

/- Lemma 10.78.7: over a commutative semilocal ring, a finite locally free module whose fibers
over all maximal residue fields have the same finite dimension is free. -/
recall Module.free_of_flat_of_finrank_eq

variable {R : Type u} {M : Type v} [CommRing R] [Finite (MaximalSpectrum R)]
  [AddCommGroup M] [Module R M]

open scoped TensorProduct

omit [Finite (MaximalSpectrum R)] in
private theorem maximalFiber_finrank_eq_rankAtStalk [Module.Finite R M] [Module.Flat R M]
    (P : MaximalSpectrum R) :
    Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.rankAtStalk M P.toPrimeSpectrum := by
  let e : (R ⧸ P.asIdeal) ≃ₐ[R] P.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ P.asIdeal) P.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField P.asIdeal)
  let j := TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  have hj : ∀ (r : R ⧸ P.asIdeal) (x : TensorProduct R (R ⧸ P.asIdeal) M),
      j (r • x) = e r • j x := by
    intro r x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a m
      change e (r * a) ⊗ₜ[R] m = e r • (e a ⊗ₜ[R] m)
      rw [map_mul]
      rfl
    · intro x y hx hy
      simp [smul_add, hx, hy]
  have hfinrank : Module.finrank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
      Module.finrank P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] M) := by
    have hrank : Module.rank (R ⧸ P.asIdeal) ((R ⧸ P.asIdeal) ⊗[R] M) =
        Module.rank P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] M) :=
      rank_eq_of_equiv_equiv e.toRingEquiv j.toAddEquiv e.toRingEquiv.bijective hj
    change Cardinal.toNat (Module.rank (R ⧸ P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M)) =
      Cardinal.toNat (Module.rank P.asIdeal.ResidueField (TensorProduct R P.asIdeal.ResidueField M))
    exact congr_arg Cardinal.toNat hrank
  rw [hfinrank]
  exact (Module.rankAtStalk_eq P.toPrimeSpectrum).symm

/-- If a semilocal ring has connected spectrum, then every finite locally free module over it is
free. -/
-- Proof sketch: the rank function on `PrimeSpectrum R` is locally constant for finite flat modules.
-- On a connected spectrum it is therefore constant, so `Module.free_of_flat_of_finrank_eq` applies.
theorem free_of_semilocal_of_connected_spectrum [Module.FinitePresentation R M] [Module.Flat R M]
    [ConnectedSpace (PrimeSpectrum R)] : Module.Free R M := by
  let p₀ : PrimeSpectrum R := Classical.choice inferInstance
  let n := Module.rankAtStalk M p₀
  have hconst : Module.rankAtStalk M = Function.const (PrimeSpectrum R) n :=
    Module.isLocallyConstant_rankAtStalk.eq_const p₀
  refine Module.free_of_flat_of_finrank_eq R M n fun P ↦ ?_
  rw [maximalFiber_finrank_eq_rankAtStalk P]
  exact congrFun hconst P.toPrimeSpectrum
