import StacksProject_2024.stacks_project.Chap31.Lemma_31_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local precedent: `lean_leansearch` surfaced the nilradical and reduced-scheme
-- owners `Scheme.nilradical` and `IsReduced`, while `stacks_project/Chap31/Lemma_31_17_6.lean`
-- now owns the source-facing scheme norm as affine-local `PolynomialLaw` data on section rings.

/-- The scheme-theoretic condition `p \mathcal{O}_X = 0` is expressed affine-locally by
`CharP` on section rings of affine opens. -/
theorem charP_of_eq_zero_on_affineOpens (X : Scheme.{u}) {p : ℕ} (hp : Nat.Prime p)
    (hchar : ∀ (U : X.Opens) (hU : IsAffineOpen U), (p : Γ(X, U)) = 0) :
    ∀ (U : X.Opens) (hU : IsAffineOpen U), CharP (Γ(X, U)) p :=
  fun U hU ↦ (CharP.charP_iff_prime_eq_zero hp).2 (hchar U hU)

/-- Lemma 31.17.8: let `X` be a Noetherian scheme. Let `p` be a prime number such that
`p\mathcal{O}_X = 0`. Then for some `e > 0` there exists a norm of degree `p^e` for
`X_{red} \to X`, where `X_{red}` is the reduction of `X`. Here `X_{red}` is represented by the
nilradical subscheme `X.nilradical.subscheme`. -/
theorem exists_norm_reduction_of_eq_zero_on_affineOpens (X : Scheme.{u}) (p : ℕ) [IsNoetherian X]
    (hp : Nat.Prime p)
    (hchar : ∀ (U : X.Opens) (hU : IsAffineOpen U), (p : Γ(X, U)) = 0) :
    ∃ e : ℕ, 0 < e ∧ ∃ N : Norm X.nilradical.subschemeι,
      IsNorm X.nilradical.subschemeι (p ^ e) N := sorry

/-- Lemma 31.17.8 in affine-local `CharP` form. This is the canonical bridge from the source
condition `p \mathcal{O}_X = 0` to the Chapter 31 norm API on affine-open section rings. -/
theorem exists_norm_reduction_of_charP (X : Scheme.{u}) (p : ℕ) [IsNoetherian X]
    (hp : Nat.Prime p) (hchar : ∀ (U : X.Opens) (hU : IsAffineOpen U), CharP (Γ(X, U)) p) :
    ∃ e : ℕ, 0 < e ∧ ∃ N : Norm X.nilradical.subschemeι,
      IsNorm X.nilradical.subschemeι (p ^ e) N :=
  exists_norm_reduction_of_eq_zero_on_affineOpens X p hp
    (fun U hU ↦ (CharP.charP_iff_prime_eq_zero hp).1 (hchar U hU))

end AlgebraicGeometry.Scheme
