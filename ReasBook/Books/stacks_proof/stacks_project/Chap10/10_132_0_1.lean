import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_132_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain triage:
* primary domain: de Rham differentials on exterior powers of Kähler differentials;
* sampled owner API: `KaehlerDifferential.D`, `IsExteriorPowerDeRhamDifferential`,
  `IsExteriorPowerDeRhamDifferential.degree_one`, and
  `IsExteriorPowerDeRhamDifferential.higher`;
* core/canonical owner: the single recursive differential family
  `δ p : Ω^[p][S⁄R] → Ω^[p + 1][S⁄R]` together with
  `IsExteriorPowerDeRhamDifferential`;
* layer split: this file is a source-facing specialization of the owner fields to
  `KaehlerDifferential.D R S`, so it should use those fields directly rather than
  re-exporting them under parallel local names.
-/
-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner API was
-- verified against `Lemma_10_132_2` and nearby Chapter 10 de Rham files.

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {δ : DeRhamFamily R S Ω[S⁄R]}

/-- 10.132.0.1 (1): the de Rham differential of the exact `1`-form `b₀ \, db₁` is the
two-fold wedge `db₀ ∧ db₁`. -/
theorem de_rham_differential_exact_one_form
    (hd : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D R S) δ)
    (b₀ b₁ : S) :
    δ 1 (b₀ • KaehlerDifferential.D R S b₁) =
      exteriorPower.ιMulti S 2
        (Fin.cases (KaehlerDifferential.D R S b₀) fun _ ↦ KaehlerDifferential.D R S b₁)
    := by
      -- This textbook identity is exactly the degree-one field of the de Rham structure.
      simpa using hd.degree_one b₀ b₁

/-- 10.132.0.1 (2): the de Rham differential of the exact `(p + 2)`-form
`b₀ \, db₁ ∧ ⋯ ∧ db_{p + 2}` is obtained by adjoining `db₀` on the left. -/
theorem de_rham_differential_exact_higher_form
    (hd : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D R S) δ)
    (p : ℕ) (b₀ : S) (b : Fin (p + 2) → S) :
    δ (p + 2) (b₀ • exteriorPower.ιMulti S (p + 2) (fun i ↦ KaehlerDifferential.D R S (b i))) =
      exteriorPower.ιMulti S (p + 3)
        (Fin.cases (KaehlerDifferential.D R S b₀) fun i ↦ KaehlerDifferential.D R S (b i))
    := by
      -- The higher exact-form rule is the corresponding higher-degree field specialized to `b`.
      simpa using hd.higher p b₀ b

end
