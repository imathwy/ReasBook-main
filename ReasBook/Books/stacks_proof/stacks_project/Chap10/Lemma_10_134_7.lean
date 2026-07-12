import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain triage:
* primary domain: the Jacobi-Zariski exact sequence for a tower `A → B → C`, specialized to the
  surjective case `A → C`;
* sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`, the owner exactness of
    `H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A]`;
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`, the next owner exactness
    `H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A]`;
  - `KaehlerDifferential.subsingleton_of_surjective`, the canonical vanishing of `Ω[C⁄A]` for a
    surjective map `A → C`;
  - `surjective_algebra_h1Cotangent_equiv_cotangent`, the previous chapter bridge identifying the
    surjective `H¹` terms with conormal modules.
* best owner abstraction: the public source-facing statement should stay on the canonical owner
  maps `H1Cotangent.map` and `H1Cotangent.δ`; the conormal-module formulation is only the
  bridge/view supplied by the surjective comparison from Lemma `10.134.6`.
* primitive data vs. derived API:
  - primitive data: a tower `A → B → C` and the surjectivity hypothesis on `A → C`;
  - derived API: exactness of `H1Cotangent.map`, `H1Cotangent.δ`, and the surjectivity of `δ`
    forced by the vanishing of `Ω[C⁄A]`.
* layer triage:
  - `source-facing`: the surjective Jacobi-Zariski conormal sequence;
  - `core/canonical`: `H1Cotangent.exact_map_δ`, `H1Cotangent.exact_δ_mapBaseChange`, and
    `KaehlerDifferential.subsingleton_of_surjective`;
  - `bridge/view`: the conormal-module interpretation via
    `surjective_algebra_h1Cotangent_equiv_cotangent`.
-/
-- Proof sketch: start from the Jacobi-Zariski exactness
-- `H1Cotangent.exact_map_δ` for `A → B → C`. If `A → C` is surjective, then `Ω[C⁄A] = 0`, so the
-- next map in the Jacobi-Zariski sequence is zero and `δ` is therefore surjective. By the
-- surjective-case description of Lemma `10.134.6`, the two `H1Cotangent` terms identify with the
-- conormal modules `I / I²` and `J / J²`.
/-- Lemma 10.134.7: if `A → C` is surjective, then the Jacobi-Zariski segment
`H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A]`
is exact and the second map is surjective. Via the canonical identifications for surjective maps,
this is the exact sequence
`I / I² → J / J² → Ω[B⁄A] ⊗[B] B / J → 0`,
where `I = ker(A → C)` and `J = ker(B → C)`. -/
@[stacks 065V]
theorem surjective_jacobi_zariski_conormal_sequence
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Exact (H1Cotangent.map A B C C) (H1Cotangent.δ A B C) ∧
      Function.Surjective (H1Cotangent.δ A B C) := by
  refine ⟨H1Cotangent.exact_map_δ A B C, ?_⟩
  letI : Subsingleton Ω[C⁄A] := KaehlerDifferential.subsingleton_of_surjective A C hAC
  have hExact :
      Function.Exact (H1Cotangent.δ A B C) (KaehlerDifferential.mapBaseChange A B C) :=
    H1Cotangent.exact_δ_mapBaseChange A B C
  have hZero : KaehlerDifferential.mapBaseChange A B C = 0 := by
    ext x
    exact Subsingleton.elim _ _
  have hKer : LinearMap.ker (KaehlerDifferential.mapBaseChange A B C) = ⊤ := by
    rw [hZero, LinearMap.ker_zero]
  rw [← LinearMap.range_eq_top]
  rw [← Function.Exact.linearMap_ker_eq hExact]
  exact hKer

end
