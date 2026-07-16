import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory CategoryTheory.Limits ChainComplex

variable {R : Type u} [Ring R]

/-- Situation 10.102.1: a finite complex of finite free `R`-modules
`0 → R^{n_e} → R^{n_{e-1}} → ⋯ → R^{n_0}`, organized around its canonical owner
`ChainComplex (ModuleCat R) ℕ` together with chosen identifications of the degrees `0, …, e`
with the standard finite free modules `R^{n_i}`. -/
@[stacks 00MS]
structure FiniteFreeComplex (R : Type u) [Ring R] (e : ℕ) where
  /-- The underlying chain complex of `R`-modules. -/
  toChainComplex : ChainComplex (ModuleCat R) ℕ
  /-- The complex is zero in degrees strictly above `e`. -/
  isZero_toChainComplex_X : ∀ i : ℕ, e < i → Limits.IsZero (toChainComplex.X i)
  /-- The ranks `n_i` of the standard finite free presentations in degrees `i = 0, …, e`. -/
  rank : Fin (e + 1) → ℕ
  /-- The chosen identification of the degree-`i` term with `R^{n_i}`. -/
  termIso :
    ∀ i : Fin (e + 1),
      toChainComplex.X i ≅ ModuleCat.of R (Fin (rank i) → R)

namespace FiniteFreeComplex

variable {e : ℕ} (C : _root_.FiniteFreeComplex R e)

private def alternatingRankIndex (i : Fin e) (k : Fin (e - i)) : Fin (e + 1) :=
  ⟨i.1 + 1 + k.1, by omega⟩

/-- The standard free `R`-module used to present the degree-`i` term. -/
abbrev term (i : Fin (e + 1)) : Type u :=
  Fin (C.rank i) → R

/-- The chosen identification of `C` in degree `i` with the standard finite free module
`R^{n_i}`. -/
abbrev termIsoAt (i : Fin (e + 1)) :
    C.toChainComplex.X i ≅ ModuleCat.of R (C.term i) :=
  C.termIso i

/-- The differential `φ_i : C_{i + 1} → C_i` expressed in the chosen standard coordinates. -/
abbrev differential (i : ℕ) (hi : i < e) :
    C.term ⟨i + 1, Nat.succ_lt_succ hi⟩ →ₗ[R] C.term ⟨i, Nat.lt_succ_of_lt hi⟩ :=
  ((C.termIsoAt ⟨i + 1, Nat.succ_lt_succ hi⟩).inv ≫
      C.toChainComplex.d (i + 1) i ≫
      (C.termIsoAt ⟨i, Nat.lt_succ_of_lt hi⟩).hom).hom

/-- The differential `φ_i : C_{i + 1} → C_i` of a finite free complex. -/
abbrev diffAt (i : Fin e) : C.term i.succ →ₗ[R] C.term i.castSucc :=
  C.differential i i.isLt

/-- The alternating tail rank
`rank(C_{i + 1}) - rank(C_{i + 2}) + ⋯ + (-1)^(e - i - 1) rank(C_e)` attached to `φ_i`. -/
def alternatingRank (i : Fin e) : ℤ :=
  List.alternatingSum <|
    List.ofFn fun k : Fin (e - i) ↦ (C.rank (alternatingRankIndex i k) : ℤ)

/-- Each displayed coordinate term of a finite free complex is a free `R`-module. -/
instance (i : Fin (e + 1)) : Module.Free R (C.term i) := inferInstance

/-- Each displayed coordinate term of a finite free complex is a finite `R`-module. -/
instance (i : Fin (e + 1)) : Module.Finite R (C.term i) := inferInstance

/-- The underlying chain complex is termwise free. -/
theorem isTermwiseFree : ChainComplex.IsTermwiseFree C.toChainComplex := by
  intro i
  by_cases hi : i ≤ e
  · let j : Fin (e + 1) := ⟨i, Nat.lt_succ_iff.mpr hi⟩
    simpa [j] using Module.Free.of_equiv (C.termIsoAt j).toLinearEquiv.symm
  · have hi' : e < i := Nat.lt_of_not_ge hi
    let _ : Subsingleton (C.toChainComplex.X i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_toChainComplex_X i hi')
    infer_instance

/-- The underlying chain complex is termwise finite. -/
theorem isTermwiseFinite : ChainComplex.IsTermwiseFinite C.toChainComplex := by
  intro i
  by_cases hi : i ≤ e
  · let j : Fin (e + 1) := ⟨i, Nat.lt_succ_iff.mpr hi⟩
    simpa [j] using Module.Finite.equiv (C.termIsoAt j).toLinearEquiv.symm
  · have hi' : e < i := Nat.lt_of_not_ge hi
    let _ : Subsingleton (C.toChainComplex.X i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_toChainComplex_X i hi')
    exact Module.Finite.of_surjective (0 : (Fin 0 → R) →ₗ[R] C.toChainComplex.X i) <| by
      intro x
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _

/-- Each term of the underlying chain complex is a free `R`-module. -/
instance (i : ℕ) : Module.Free R (C.toChainComplex.X i) :=
  C.isTermwiseFree i

/-- Each term of the underlying chain complex is a finite `R`-module. -/
instance (i : ℕ) : Module.Finite R (C.toChainComplex.X i) :=
  C.isTermwiseFinite i

/-- The short complex on the consecutive differentials in degrees `i + 2 → i + 1 → i`. -/
abbrev shortComplexAt (i : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (C.toChainComplex.d (i + 2) (i + 1))
    (C.toChainComplex.d (i + 1) i)
    (C.toChainComplex.d_comp_d (i + 2) (i + 1) i)

end FiniteFreeComplex

end
