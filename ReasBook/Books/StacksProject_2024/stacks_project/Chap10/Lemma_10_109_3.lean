import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat`, short exact complexes, and projective
  syzygies.
* inspected owner declarations:
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `LinearMap.shortComplexKer`, and `LinearMap.shortExact_shortComplexKer`.
* best owner abstraction: a short exact complex `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with projective middle
  term; a kernel `LinearMap.ker π` is a bridge/view via `LinearMap.shortComplexKer π`.
* layer triage:
  the short-exact corollary below is `core/canonical`,
  `projective_ker_of_surjective_of_hasProjectiveDimensionLE_one` is `bridge/view`,
  and the finite exact-sequence statement remains `source-facing`.
* primitive data: the short exact owner object and the projective-dimension bound on its cokernel.
* derived API: projectivity of the kernel / top syzygy.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules with `X₂` projective, if
`X₃` has projective dimension at most `1`, then `X₁` is projective. This is the `n = 0`
specialization of the canonical owner theorem
`ShortExact.hasProjectiveDimensionLT_X₃_iff`. -/
theorem projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one
    (hS : S.ShortExact) [Projective S.X₂] (hpd : HasProjectiveDimensionLE S.X₃ 1) :
    Projective S.X₁ := sorry

end

end ShortExact
end ShortComplex
end CategoryTheory

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.109.3 (1): if `F₀ ⟶ M ⟶ 0` is exact with `F₀` projective and `M` has projective
dimension at most `1`, then `ker(F₀ ⟶ M)` is projective. This is the `e = 0` case of the
textbook lemma, phrased in terms of the equivalent upper-bound condition on projective
dimension. The raw-kernel formulation is the bridge obtained from the owner theorem
`CategoryTheory.ShortComplex.ShortExact.projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one`
by applying it to `LinearMap.shortComplexKer π`. -/
-- Proof sketch: package `π` as the short exact complex
-- `0 ⟶ ker π ⟶ F₀ ⟶ M ⟶ 0`, apply the owner theorem in
-- `CategoryTheory.ShortComplex.ShortExact`, and then identify the left term with the module
-- `LinearMap.ker π`.
theorem projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
    {F₀ : Type v}
    [AddCommGroup F₀] [Module R F₀]
    (π : F₀ →ₗ[R] M) (hπ : Function.Surjective π)
    [Module.Projective R F₀]
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) 1) :
    Module.Projective R (LinearMap.ker π) := sorry

/-- Lemma 10.109.3 (2): if
`F_{e+1} ⟶ F_e ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
is exact, every `Fᵢ` is projective, and `M` has projective dimension at most `e + 1`, then the
kernel of the top differential `F_{e+1} ⟶ F_e` is projective. This is the canonical upper-bound
reformulation of the textbook hypothesis `e ≥ d - 1` when `M` has projective dimension `d`. -/
-- Proof sketch: prove the statement by induction on `e`. The case `e = 0` is part (1). For the
-- inductive step, replace `M` by the first syzygy `ker(F₀ ⟶ M)`, use the canonical short-exact
-- projective-dimension shift to see that this syzygy has projective dimension at most `e`, and
-- then apply the induction hypothesis to the truncated exact projective sequence.
theorem projective_top_kernel_of_exact_of_hasProjectiveDimensionLE
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module.Projective R (F i)]
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[R] F i.castSucc)
    (π : F 0 →ₗ[R] M)
    (hπ : Function.Surjective π)
    (h_exact₀ : Function.Exact (d 0) π)
    (h_exact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) (e + 1)) :
    Module.Projective R (LinearMap.ker (d (Fin.last e))) := sorry

end
