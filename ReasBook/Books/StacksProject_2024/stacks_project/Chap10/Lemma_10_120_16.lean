import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_78_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

/- Domain triage:
- primary domain: commutative algebra of locally principal ideals and finite locally free modules;
- sampled owner declarations:
  `Ideal.FG`,
  `Module.FiniteLocallyFreeOfRank`,
  `Module.finiteLocallyFree_ofRank`,
  `Submodule.FG.of_finite`,
  `module_finite_projective_tfae`;
- owner abstraction: the source-facing conclusion naturally lives in the paired owner predicates
  `I.FG` and `Module.FiniteLocallyFreeOfRank A I 1` for an ideal viewed as an `A`-module;
- primitive data: the ideals `I`, `J`, the regular element `f`, and the factorization
  `I * J = Ideal.span ({f} : Set A)`;
- derived API: the finite-generation half is obtained from rank-one local freeness through the
  canonical bridge `Module.finiteLocallyFree_ofRank`, `module_finite_projective_tfae`, and
  `Submodule.FG.of_finite`.

The numbered theorem is `source-facing`; the rank-one statement is a thin `bridge/view` companion
reusing the chapter owner abstraction.
-/

-- Proof sketch: localize at a standard-open cover obtained from a finite expression
-- `f = ∑ xᵢ yᵢ` with `xᵢ ∈ I` and `yᵢ ∈ J`. On each localized piece one has a factorization
-- `f = x * y` with `x ∈ I` and `y ∈ J`, and regularity of `f` shows `I` and `J` become the
-- principal ideals `(x)` and `(y)`, so the canonical local condition
-- `Module.FiniteLocallyFreeOfRank A _ 1` holds for both ideals.
/-- A companion rank-one local freeness statement for the two factors in a principal product. -/
theorem ideal_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A I 1 ∧ Module.FiniteLocallyFreeOfRank A J 1 := sorry

-- Proof sketch: deduce local freeness of rank `1` for `I` from the companion theorem, and then
-- pass from finite locally free to finite generation for ideals over a commutative ring.
/-- Lemma 10.120.16 (1): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `I` is finitely generated. -/
theorem ideal_left_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) : I.FG := sorry

-- Proof sketch: this is the `I`-component of the companion rank-one local freeness theorem.
/-- Lemma 10.120.16 (2): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `I` is finite locally free of rank `1` as an `A`-module. -/
theorem ideal_left_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A I 1 := sorry

-- Proof sketch: deduce local freeness of rank `1` for `J` from the companion theorem, and then
-- pass from finite locally free to finite generation for ideals over a commutative ring.
/-- Lemma 10.120.16 (3): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `J` is finitely generated. -/
theorem ideal_right_fg_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) : J.FG := sorry

-- Proof sketch: this is the `J`-component of the companion rank-one local freeness theorem.
/-- Lemma 10.120.16 (4): if ideals `I` and `J` satisfy `I * J = (f)` for a nonzerodivisor `f`,
then the ideal `J` is finite locally free of rank `1` as an `A`-module. -/
theorem ideal_right_finiteLocallyFreeOfRank_one_of_mul_eq_span_singleton_regular
    (I J : Ideal A) (f : A) (hf : IsRegular f)
    (hIJ : I * J = Ideal.span ({f} : Set A)) :
    Module.FiniteLocallyFreeOfRank A J 1 := sorry

end
