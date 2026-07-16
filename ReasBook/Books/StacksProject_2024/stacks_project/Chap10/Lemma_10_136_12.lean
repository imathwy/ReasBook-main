import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence

namespace Algebra

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

/- Domain-style sampling:
- primary domain: relative global complete intersections for explicit polynomial quotients,
  localized at primes and analyzed through regular sequences and conormal modules;
- sampled owner declarations:
  `Algebra.Presentation.naive`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.toIsRelativeGlobalCompleteIntersection`,
  `PrimeSpectrum.comap`,
  `Ideal.Cotangent`;
- best owner abstraction:
  for the displayed quotient `R[x₁, …, xₙ] / (f₁, …, f_c)`, the source-facing owner layer is the
  naive presentation determined by `f` together with the presentation-level predicate
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`; the intrinsic class
  `Algebra.IsRelativeGlobalCompleteIntersection R S` is only the bridge obtained by forgetting
  which presentation witnesses the fiber-dimension formula;
- primitive vs. derived:
  the primitive source-facing data are the relations `f`; the quotient map, the prime lying over a
  quotient prime, the localized polynomial ring, and the cotangent classes are derived API and
  should not be rebuilt as parallel public wrappers.

Source/core/bridge triage:
- `source-facing`: the three clauses of Lemma `10.136.12` for the explicit quotient
  `R[x₁, …, xₙ] / (f₁, …, f_c)`;
- `core/canonical`: the naive presentation of that quotient, equipped with
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`, and the ambient owners
  `PrimeSpectrum.comap` and `Ideal.Cotangent`;
- `bridge/view`: the localized relation list, the quotients by its initial segments, and the
  explicit cotangent classes of the `fᵢ`, all written directly in terms of the quotient,
  localization, and cotangent owners rather than through local wrapper names.
-/

variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))
local notation "PresentedCotangent" => Ideal.Cotangent PresentedIdeal

-- Proof sketch: view `S = R[x₁, …, xₙ] / (f₁, …, f_c)` as the chosen quotient presentation.
-- For a prime `q` of `S`, descend the relative global complete intersection hypothesis to a
-- finite type `ℤ`-subalgebra, apply the Noetherian fibrewise criterion of Lemma `10.99.3`, and
-- then transport the resulting regularity statement to the localization at the corresponding prime
-- `q'` of the polynomial ring.
/-- Lemma 10.136.12 (1): for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` and a prime `q` of `S`, the defining equations `f₁, …, f_c`
form a regular sequence in the local ring `R[x₁, …, xₙ]_{q'}`, where `q'` is the prime of the
polynomial ring lying over `q`. -/
theorem relativeGCI_localized_relations_isRegular
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    Sequence.IsRegular A ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A)) := sorry

-- Proof sketch: after proving part (1), apply the same Noetherian reduction together with
-- Lemma `10.99.3` to each nonempty prefix of the localized sequence. This yields flatness of the
-- successive quotients over the base ring `R`, and filtered-colimit exactness descends the result
-- from the finite type `ℤ`-subalgebras to the original ring.
/-- Lemma 10.136.12 (2): with the same presentation and prime `q`, every quotient
`R[x₁, …, xₙ]_{q'} / (f₁, …, f_i)` by a nonempty initial segment of the defining equations is flat
over `R`. -/
theorem relativeGCI_localized_prefix_quotients_flat
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation)
    (q : PrimeSpectrum PresentedAlgebra) :
    let q' := PrimeSpectrum.comap (Ideal.Quotient.mk PresentedIdeal) q
    let A := Localization.AtPrime q'.asIdeal
    ∀ i : Fin c,
      Module.Flat R
        (A ⧸ Ideal.ofList (List.take (i + 1) ((List.ofFn f).map (algebraMap (MvPolynomial (Fin n) R) A)))) := sorry

-- Proof sketch: by part (1), the sequence `f₁, …, f_c` is regular in every localization of the
-- quotient presentation. Lemma `10.69.2` upgrades regularity to quasi-regularity, so the images of
-- the `fᵢ` generate the localized conormal module as a basis at every prime. Then apply the local
-- criterion for freeness from Lemma `10.23.1` to globalize those local bases.
/-- Lemma 10.136.12 (3): for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)`, the conormal module `(f₁, …, f_c) / (f₁, …, f_c)^2` is free
over `S`, with basis given by the classes of the defining equations `fᵢ mod (f₁, …, f_c)^2`. -/
theorem relativeGCI_conormalModule_has_basis
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation) :
    ∃ b : Module.Basis (Fin c) PresentedAlgebra PresentedCotangent,
      ∀ i,
        b i =
          Ideal.toCotangent PresentedIdeal ⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ := sorry

end

end

end Algebra
