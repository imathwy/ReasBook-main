import Mathlib
import stacks_project.Chap15.«15_90_8_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ}
variable (M : ModuleCat R)

-- Proof sketch: identify the displayed sequence with the truncation of the cone of the morphism
-- between the extended alternating Cech complexes for `R` and `S`. Lemma `15.90.4` gives that
-- morphism as a quasi-isomorphism, and flatness lets one tensor it with `M`. Equivalently, the
-- computational proof shows `Mono α` using the `I^∞`-torsion comparison map and proves
-- `ker β = range α` by reducing a compatible family to degree-one Koszul homology, then applying
-- Lemmas `15.90.2`, `15.90.3`, and `15.90.7`, yielding the canonical short-complex owner surface
-- `S.Exact ∧ Mono S.f`.
/-- Lemma 15.90.9: let `f : Fin t → R` generate the ideal `I = (f₁, …, fₜ)`. If `R → S` is flat
and the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the formal glueing complex
`0 → M → (S ⊗[R] M) × ∏ i, M_{f_i} → ∏ i, (S ⊗[R] M)_{f_i} × ∏ i j, M_{f_i f_j}` is exact. In
this library-facing formulation, the overlap term `M_{f_i f_j}` is represented by iterated away
localizations, and the exactness statement is expressed by the owner pair
`(formalGlueingModuleComplex S f M).Exact ∧ Mono (formalGlueingModuleComplex S f M).f`. -/
theorem formalGlueingModuleComplex_exact_of_flat_of_quotientMap_bijective
    (f : Fin t → R) (hflat : (algebraMap R S).Flat)
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    (formalGlueingModuleComplex S f M).Exact ∧
      Mono (formalGlueingModuleComplex S f M).f :=
  sorry

end
