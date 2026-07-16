import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_114_7
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_1
import StacksProject_2024.stacks_project.Chap10.Theorem_10_129_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped ENNReal

variable {k : Type u} [Field k]
variable {d : ℕ}
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Domain-style sampling:
- primary domain: flatness loci for finite type algebras over a chosen quasi-finite polynomial
  presentation, compared with Cohen--Macaulayness and the local topological dimension stratum on
  `Spec`;
- sampled owner declarations:
  `Module.flatOverBaseLocus`,
  `AlgHom.QuasiFinite`,
  `Module.CohenMacaulay`,
  `PrimeSpectrum.dimensionStratum`;
- best owner abstraction: `Module.flatOverBaseLocus` for the flat-locus side, together with the
  explicit polynomial presentation map `π : MvPolynomial (Fin d) k →ₐ[k] S` as primitive
  source-facing data and the morphism-level owner `π.QuasiFinite`;
- primitive data: the finite type `k`-algebra structure on `S`, the chosen polynomial presentation
  `π`, and the quasi-finite hypothesis on `π`;
- derived API: the induced `MvPolynomial (Fin d) k`-algebra structure on `S`, the corresponding
  flat locus, and the comparison with the primewise Cohen--Macaulay condition together with the
  canonical dimension-`d` stratum owner.

Source/core/bridge triage:
- `source-facing`: the equality identifying the flat locus for the chosen presentation `π` with the
  Cohen--Macaulay and dimension-`d` locus;
- `core/canonical`: `Module.flatOverBaseLocus`, `AlgHom.QuasiFinite`, `Module.CohenMacaulay`, and
  `PrimeSpectrum.dimensionStratum`;
- `bridge/view`: the local algebra structure on `S` induced by `π`, used only to express the
  canonical flat-locus owner for this specific morphism.
-/
variable [Algebra.FiniteType k S]

-- Proof sketch: use the Chapter 10 owner `Module.flatOverBaseLocus` for the flatness locus of the
-- self-module `S`, with the `MvPolynomial (Fin d) k`-algebra structure induced by the chosen
-- polynomial presentation `π`. For a prime `q : Spec(S)`, let `p = q ∩ k[y₁, …, y_d]`.
-- Quasi-finiteness of `π` gives `dim S_q ≤ dim (k[y₁, …, y_d]_p)`. If `S_q` is flat over the
-- polynomial ring, apply the flat local criterion over the regular local ring
-- `(k[y₁, …, y_d])_p` to deduce that `S_q` is Cohen-Macaulay. Since `π` is quasi-finite, the
-- residue-field extension over `p` is finite, so the local dimension formula over the field `k`
-- identifies `q` with the dimension-`d` stratum of `Spec(S)`. Conversely, if `S_q` is
-- Cohen-Macaulay and `q` lies in that dimension-`d` stratum, the same local dimension comparison
-- forces `dim S_q = dim (k[y₁, …, y_d]_p)`, and the converse flatness criterion over the regular
-- local ring `(k[y₁, …, y_d])_p` gives flatness of `S_q` over `k[y₁, …, y_d]`.
/-- Lemma 10.130.1: for a finite type `k`-algebra `S` over a field `k` and a quasi-finite map
`π : k[y₁, …, y_d] → S`, the primes `q : Spec(S)` for which the local ring `S_q` is flat over
this chosen polynomial presentation are exactly the primes for which `S_q` is Cohen-Macaulay and
`q` lies in the dimension-`d` stratum of `Spec(S)`. -/
theorem flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial
    (π : MvPolynomial (Fin d) k →ₐ[k] S) (hπ : π.QuasiFinite) :
    let _ : Algebra (MvPolynomial (Fin d) k) S := π.toAlgebra
    Module.flatOverBaseLocus (MvPolynomial (Fin d) k) S S =
      { q : PrimeSpectrum S |
          Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) } ∩
        PrimeSpectrum.dimensionStratum S d := sorry

end
