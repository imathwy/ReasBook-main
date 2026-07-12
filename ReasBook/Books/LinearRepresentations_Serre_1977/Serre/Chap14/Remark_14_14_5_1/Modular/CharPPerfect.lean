import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.CharPMain
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SplitBaseChange
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.CharPReduction
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SeparableSemisimple
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.HomBaseChange

/-!
# Characteristic-`p` absolute simplicity over a *general perfect* field

This module upgrades the finite-field black box
`charP_scalarExtension_isIrreducible_of_splitsPrimeToP` (`CharPMain.lean`, valid only for a finite
residue field, where the modular Galois descent is unobstructed) to an **arbitrary perfect** field
`k` of characteristic `p`, by the classical *finite splitting subfield + ascent* route of Serre's
Remark 14-14.5-1.

## Proof outline

Let `S : FDRep k G` be simple and let `n := ordCompl[p] (Monoid.exponent G)` be the prime-to-`p`
part of the exponent of `G`.

* **Step 1 (finite splitting subfield).**  Since `p ∤ n`, `(n : k) ≠ 0`, so the splitting
  hypothesis `hsplit` supplies a primitive `n`-th root of unity `ζ ∈ k`.  As `ζ` is a root of unity
  it is integral over the prime field `ZMod p`, so `F := ZMod p (ζ) = IntermediateField.adjoin
  (ZMod p) {ζ}` is **finite** (a finite-dim extension of a finite field).  Every prime-to-`p`
  divisor `d` of `exp G` divides `n`, so `ζ ^ (n / d) ∈ F` is a primitive `d`-th root of unity:
  hence `F` *also* splits the prime-to-`p` roots of unity of `G`.
* **Step 2 (`F` splits `G`).**  `F` is finite, so the black box applies over `F`: combined with the
  modular Schur-index-`1` content (`finrank_intertwiningMap_eq_one_of_splitsPrimeToP`), every simple
  `M : FDRep F G` has `finrank_F (M ⟶ M) = 1`.  Steps 1–2 are packaged into the existential
  `exists_finite_splitting_subfield`, which keeps the auxiliary `Algebra (ZMod p) k` /
  `IntermediateField` instances out of the main proof's instance environment.
* **Step 3 (ascent).**  Splitting ascends along the field extension `k ⊇ F`
  (`dim_end_one_ascends_of_subfield_splits`): the simple `k[G]`-module `S.ρ.asModule` has
  `finrank_k End = 1`, which the intertwiner/`End` bridge `IntertwiningMap.equivLinearMapAsModule`
  turns into `(B) : finrank_k (IntertwiningMap S.ρ S.ρ) = 1`.
* **Step 4 (assemble).**  With `(A)` geometric semisimplicity over a perfect field and `(B)`, the
  characteristic-independent anchor
  `isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one` concludes.

This file introduces **no** new `sorry`; it inherits `sorryAx` only transitively, through the two
isolated atoms imported by `CharPMain.lean`/`SeparableSemisimple.lean`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra Polynomial

open CategoryTheory

namespace Representation

variable {k : Type u} [Field k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

include hp hk in
/-- **Steps 1–2: a finite splitting subfield.**  Over a field `k` of characteristic `p` which
splits the prime-to-`p` roots of unity of `G`, there is a *finite* subfield `F ⊆ k` that splits `G`
in the strong sense that every simple `F[G]`-representation has a one-dimensional endomorphism
algebra.

`F` is the prime field adjoined a primitive `n`-th root of unity, `n` the prime-to-`p` part of the
exponent of `G`.  The auxiliary `Algebra (ZMod p) k` and `IntermediateField` instances are confined
to this lemma so they do not interfere with instance resolution in the main proof. -/
private theorem exists_finite_splitting_subfield
    (hsplit : SplitsPrimeToPRootsOfUnity k G) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra F k) (_ : Finite F),
      ∀ (M : FDRep F G), Simple M → Module.finrank F (M ⟶ M) = 1 := by
  classical
  -- The prime-to-`p` part `n` of the exponent of `G`.
  have hexp : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  set n : ℕ := ordCompl[p] (Monoid.exponent G) with hn_def
  have hn_pos : 0 < n := by rw [hn_def]; exact Nat.ordCompl_pos p hexp
  have hn_ne : n ≠ 0 := hn_pos.ne'
  have hn_dvd : n ∣ Monoid.exponent G := by rw [hn_def]; exact Nat.ordCompl_dvd _ _
  have hp_n : ¬ p ∣ n := by rw [hn_def]; exact Nat.not_dvd_ordCompl Fact.out hexp
  have hn_cast : (n : k) ≠ 0 := fun h => hp_n ((CharP.cast_eq_zero_iff k p n).mp h)
  -- A primitive `n`-th root of unity `ζ ∈ k`.
  haveI : HasEnoughRootsOfUnity k n := hsplit n hn_dvd hn_cast
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have hζpow : ζ ^ n = 1 := hζ.pow_eq_one
  -- The finite splitting subfield `F = ZMod p (ζ)`.
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  set F : IntermediateField (ZMod p) k := IntermediateField.adjoin (ZMod p) {ζ} with hF_def
  have hint : IsIntegral (ZMod p) ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn_ne, ?_⟩
    simp [hζpow]
  haveI : FiniteDimensional (ZMod p) ↥F := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite ↥F := Module.finite_of_finite (ZMod p)
  have hζmem : ζ ∈ F := IntermediateField.subset_adjoin (ZMod p) {ζ} (Set.mem_singleton ζ)
  -- `F` splits the prime-to-`p` roots of unity of `G`.
  have hsplitF : SplitsPrimeToPRootsOfUnity (↥F) G := by
    intro d hd_dvd hd_cast
    -- `(d : F) ≠ 0` forces `p ∤ d`, hence `d ∣ n`.
    have hd_castk : (d : k) ≠ 0 := by
      intro h
      apply hd_cast
      apply (algebraMap ↥F k).injective
      rw [map_natCast, map_zero]; exact h
    have hpd : ¬ p ∣ d := fun h => hd_castk ((CharP.cast_eq_zero_iff k p d).mpr h)
    have hdn : d ∣ n := by
      have hcop : Nat.Coprime d (ordProj[p] (Monoid.exponent G)) :=
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpd).symm.pow_right _
      have hmul : Monoid.exponent G = ordProj[p] (Monoid.exponent G) * n := by
        rw [hn_def]; exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
      exact hcop.dvd_of_dvd_mul_left (hmul ▸ hd_dvd)
    -- `ζ ^ (n / d) ∈ F` is a primitive `d`-th root of unity.
    have hprimd : IsPrimitiveRoot (ζ ^ (n / d)) d :=
      hζ.pow hn_pos (Nat.div_mul_cancel hdn).symm
    refine { prim := ⟨(⟨ζ, hζmem⟩ : ↥F) ^ (n / d), ?_⟩, cyc := inferInstance }
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥F k) _ (algebraMap ↥F k).injective
    have hcoe : (algebraMap ↥F k) (⟨ζ, hζmem⟩ : ↥F) = ζ := rfl
    rw [map_pow, hcoe]; exact hprimd
  -- `F` is finite, so the finite-field black box gives the splitting predicate.
  refine ⟨↥F, inferInstance, inferInstance, inferInstance, fun M hM => ?_⟩
  haveI := hM
  have hbridge : Module.finrank (↥F) (M ⟶ M)
      = Module.finrank (↥F) (Representation.IntertwiningMap M.ρ M.ρ) :=
    LinearEquiv.finrank_eq
      ((Representation.linHom.invariantsEquivFDRepHom M M).symm.trans
        (Representation.invariantsEquivIntertwiningMap M.ρ M.ρ))
  rw [hbridge]
  exact finrank_intertwiningMap_eq_one_of_splitsPrimeToP hsplitF M

/-- **Step 4 assembly (in a clean environment).**  From geometric semisimplicity `(A)` and the
endomorphism-dimension `(B') : finrank_k End_{k[G]}(S.ρ.asModule) = 1`, the scalar extension of a
simple `k[G]`-representation `S` is irreducible.

The endomorphism/intertwiner bridge `IntertwiningMap.equivLinearMapAsModule` converts `(B')` into
`finrank_k (IntertwiningMap S.ρ S.ρ) = 1`, and the characteristic-independent anchor concludes.

This is factored out as a separate lemma precisely so the bridge — whose statement mentions
`IntertwiningMap S.ρ S.ρ` — is elaborated *without* the auxiliary `Algebra F k` instance that the
caller has in scope (that instance, together with an `asModule`/`IntertwiningMap` goal, derails the
`asModule`-instance synthesis).  The bridge equivalence `e` is bound with an explicit type so that
the base ring `k` and the `Module.End`-codomain instance are pinned for `finrank_eq`. -/
private theorem isIrreducible_scalarExtension_of_finrank_end_asModule_eq_one (S : FDRep k G)
    (hss : IsSemisimpleRepresentation
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ))
    (hend : Module.finrank k (Module.End (MonoidAlgebra k G) (Representation.asModule S.ρ)) = 1) :
    Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) := by
  let e : Representation.IntertwiningMap S.ρ S.ρ ≃ₗ[k]
      Module.End (MonoidAlgebra k G) (Representation.asModule S.ρ) :=
    Representation.IntertwiningMap.equivLinearMapAsModule S.ρ S.ρ
  exact isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one S.ρ hss
    (e.finrank_eq.trans hend)

include hp hk in
set_option backward.isDefEq.respectTransparency false in
/-- **Characteristic-`p` absolute simplicity over a perfect splitting field.**

Over a *perfect* field `k` of characteristic `p` which splits the prime-to-`p` roots of unity of the
finite group `G`, the scalar extension to the algebraic closure `k̄` of a simple `k[G]`-rep
`S` is irreducible — i.e. `S` is *absolutely simple*.

This is the general-perfect-field form of the modular branch of Remark 14-14.5-1.  It reduces to the
finite-residue-field black box `charP_scalarExtension_isIrreducible_of_splitsPrimeToP` by descending
to a finite splitting subfield `F := ZMod p (ζ)` and ascending splitting along `k ⊇ F`. -/
theorem charP_scalarExtension_isIrreducible_of_splitsPrimeToP_perfect [PerfectField k]
    (hsplit : SplitsPrimeToPRootsOfUnity k G) (S : FDRep k G) [Simple S] :
    Representation.IsIrreducible
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) := by
  classical
  -- (A) Geometric semisimplicity over the perfect base field — established before `F` is
  -- introduced, in a clean instance environment.
  haveI hirrS : Representation.IsIrreducible S.ρ := FDRep.isIrreducible_of_simple S
  haveI hsimpleS : IsSimpleModule (MonoidAlgebra k G) (Representation.asModule S.ρ) :=
    (irreducible_iff_isSimpleModule_asModule S.ρ).mp hirrS
  haveI hssS : IsSemisimpleRepresentation S.ρ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule S.ρ).mpr inferInstance
  have hss : IsSemisimpleRepresentation
      (Representation.scalarExtension (k := AlgebraicClosure k) S.ρ) :=
    isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField S.ρ
  -- Steps 1–2: a finite subfield `F ⊆ k` splitting `G`.
  obtain ⟨F, hFieldF, hAlgF, _, hF⟩ := exists_finite_splitting_subfield (k := k) (p := p) hsplit
  letI := hFieldF
  letI := hAlgF
  -- (B') Step 3: ascend splitting along `k ⊇ F`.  No type annotation on `hend1`, so that the
  -- `asModule`-mentioning type is never re-elaborated as a goal while `Algebra F k` is in scope.
  have hend1 := Serre.SplitBaseChange.dim_end_one_ascends_of_subfield_splits hF
    (Representation.asModule S.ρ) hsimpleS
  -- Step 4: assemble (A) and (B') through the (clean) anchor lemma.
  exact isIrreducible_scalarExtension_of_finrank_end_asModule_eq_one S hss hend1

end Representation
