import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

/- Domain-style sampling for Lemma 10.140.1:
- primary domain: the conormal sequence at a maximal ideal and the closed-point fiber of Kähler
  differentials over an algebraically closed base field;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `finite_residueField_of_isMaximal_of_finiteType`,
  `Ideal.bijective_algebraMap_quotient_residueField`;
- best owner abstraction: the canonical conormal map
  `KaehlerDifferential.kerCotangentToTensor k S m.ResidueField`;
- primitive data: the maximal ideal `m` in the finite type `k`-algebra `S`;
- derived API: exactness of the conormal sequence, the finite closed-point residue field supplied
  by Hilbert Nullstellensatz, and the quotient-residue comparison for maximal ideals.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for a closed point over an algebraically closed field,
  asserting equality of the cotangent-space dimension and the Kähler-fiber dimension at `m`;
- `core/canonical`: the conormal owner map `KaehlerDifferential.kerCotangentToTensor k S
  m.ResidueField` and its exactness API;
- `bridge/view`: the maximal-ideal equivalence between `S ⧸ m` and `m.ResidueField`, used only to
  present the closed-point fiber in the quotient form used downstream. -/

-- Proof sketch: the conormal exact sequence for the surjective residue map `S → m.ResidueField`
-- gives `m / m² → m.ResidueField ⊗[S] Ω[S⁄k] → Ω[m.ResidueField⁄k] → 0`. For a maximal ideal of a
-- finite type algebra over an algebraically closed field, Hilbert Nullstellensatz identifies the
-- closed-point residue field with a finite extension of `k`, and the algebraically closed base
-- hypothesis places this in the source-faithful closed-point case where the terminal Kähler term
-- vanishes. Exactness then identifies the Kähler fiber with the cotangent space, and the
-- quotient-residue comparison rewrites the result in the downstream quotient form.
/-- Lemma 10.140.1: if `k` is algebraically closed, `S` is a finite type `k`-algebra, and `m` is
a maximal ideal of `S`, then the closed-point fiber of `Ω[S⁄k]` at `m` and the cotangent space
`m / m²` have the same `κ(m) = S ⧸ m`-dimension. -/
theorem finrank_kaehlerFiber_eq_finrank_cotangent :
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
      Module.finrank (S ⧸ m) m.Cotangent := sorry

end
