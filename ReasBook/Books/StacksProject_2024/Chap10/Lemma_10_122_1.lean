import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap05.Definition_5_10_1
import StacksProject_2024.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Domain-style sampling for Lemma 10.122.1:
- primary domain: isolated points of `Spec(S)` for a finite type `k`-algebra over a field, together
  with the resulting localization and product-splitting structure;
- sampled owner declarations:
  `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`,
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`,
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap`;
- best owner abstraction: the canonical prime-spectrum owner `PrimeSpectrum`, with the chapter's
  source-facing basic-open notation `D(-)` and canonical localization/product decomposition
  owners supplying the derived structure;
- primitive data: a prime `q : PrimeSpectrum S`;
- derived API: the TFAE clauses, the localized factor `Localization.AtPrime q.asIdeal`, and the
  complementary finite type factor.

Source/core/bridge triage:
- `source-facing`: `isolatedPoint_tfae` and the complementary-factor decomposition theorem;
- `core/canonical`: `PrimeSpectrum`, `D(-)`, `Localization.AtPrime`, and
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`;
- `bridge/view`: the product decomposition theorem, which presents the source-facing splitting
  while deriving it from canonical idempotent/localization owners.
-/

-- Proof sketch: combine the Jacobson-space criterion for isolated points in a Noetherian Jacobson
-- spectrum with the characterization of finite type zero-dimensional algebras over a field as
-- finite algebras. Clause `(3)` is the basic-open reformulation of an isolated point; clauses
-- `(4)`, `(5)`, and `(6)` come from the local Krull-dimension formulas at a point of a finite type
-- `k`-algebra and the finite residue-field criterion for closed points.
/-- Lemma 10.122.1: for a prime `q` of a finite type `k`-algebra `S`, the following are
equivalent: `q` is an isolated point of `Spec(S)`; the local ring `S_q` is finite over `k`; there
exists `g ∉ q` with `D(g) = {q}`; the local topological dimension of `Spec(S)` at `q` is zero;
`q` is a closed point and `S_q` has Krull dimension zero; and the residue field extension
`κ(q) / k` is finite while `S_q` has Krull dimension zero. -/
theorem isolatedPoint_tfae (q : PrimeSpectrum S) :
    List.TFAE
      [ IsOpen ({q} : Set (PrimeSpectrum S))
      , Module.Finite k (Localization.AtPrime q.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧ (D(g) : Set (PrimeSpectrum S)) = {q}
      , topologicalKrullDimAt q = 0
      , IsClosed ({q} : Set (PrimeSpectrum S)) ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      , Module.Finite k q.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      ] := sorry

-- Proof sketch: an isolated point gives a clopen singleton in `Spec(S)`, hence a decomposition of
-- `S` by the standard correspondence between clopen subsets of the spectrum and product
-- decompositions of the ring. The factor corresponding to `{q}` is canonically `S_q`, and finite
-- type over `k` passes to the complementary factor.
/-- If `q` is an isolated point of `Spec(S)`, then `S` splits as the product of `S_q` and another
finite type `k`-algebra, with first projection equal to the localization map `S → S_q`. -/
theorem exists_finiteType_complementary_factor_of_isolatedPoint
    (q : PrimeSpectrum S) (hq : IsOpen ({q} : Set (PrimeSpectrum S))) :
    ∃ (S' : Type w) (_ : CommRing S') (_ : Algebra k S') (_ : Algebra.FiniteType k S')
      (e : S ≃ₐ[k] Localization.AtPrime q.asIdeal × S'),
      (RingHom.fst (Localization.AtPrime q.asIdeal) S').comp e.toRingHom =
        algebraMap S (Localization.AtPrime q.asIdeal) := sorry

/- Canonical owner reuse: the `D(g) = {q}` localization comparison is exactly
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`. -/
recall PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton

end
