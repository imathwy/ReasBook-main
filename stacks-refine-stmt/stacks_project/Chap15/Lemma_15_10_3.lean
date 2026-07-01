import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import stacks_project.Chap10.Lemma_10_36_5
import stacks_project.Chap10.Lemma_10_36_23
import stacks_project.Chap15.Lemma_15_3_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)
variable [Module.Flat A B] [Algebra.IsIntegral A B] [Algebra.FinitePresentation A B]

open LinearMap

local notation "IB" => I.map (algebraMap A B)

/- Domain-style sampling:
- primary domain: flat integral finitely presented algebras over a Jacobson pair, quotient algebra
  equivalences, and finite projective comparison modulo the Jacobson radical;
- sampled owner declarations of the same kind:
  `Algebra.finite_iff_isIntegral_and_finiteType`,
  `Module.FinitePresentation.iff_of_finite_finitePresentation`,
  `Module.Flat.projective_of_finitePresentation`,
  `bijective_of_bijective_mod_jacobson_of_finite_projective`,
  `LinearMap.quotientMapByIdeal`;
- best owner abstraction: the source-facing quotient hypothesis should live on the canonical owner
  `(A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ I B)`, while the module-theoretic core owner remains
  `Module.Projective`;
- primitive data: the flat integral finitely presented `A`-algebra `B`, the ideal `I`, and the
  quotient algebra equivalence modulo `I`;
- derived API: finiteness of `B` over `A`, finite presentation of `B` as an `A`-module,
  projectivity of `B`, and finally bijectivity of `algebraMap A B`; the raw quotient-map
  bijectivity is only an internal bridge extracted from the quotient algebra equivalence.

Layer classification:
- `source-facing`: the present Jacobson-pair lemma for algebras;
- `core/canonical`: `Module.Projective`;
- `bridge/view`: the quotient linear equivalence induced by `hquot`, together with the chapter
  comparison lemma `bijective_of_bijective_mod_jacobson_of_finite_projective`.
-/

-- Proof sketch: the quotient algebra equivalence identifies `B ⧸ I B` with `A ⧸ I`, so
-- `B ⧸ I B` is projective over `A ⧸ I`. Since `B` is integral and finitely presented over `A`, it
-- is finite over `A`, hence finitely presented as an `A`-module via the canonical finite/finitely
-- presented change-of-scalars bridge. Flatness then upgrades `B` to a projective `A`-module, and
-- Lemma `15.3.5` applies to the linear map underlying `A → B` after identifying its quotient
-- `LinearMap.quotientMapByIdeal` with the given quotient algebra equivalence.
/-- Lemma 15.10.3: for a Zariski pair `(A, I)`, a flat integral finitely presented
`A`-algebra `B` whose reduction modulo the extended ideal `I.map (algebraMap A B)` is identified
with `A ⧸ I` by an `(A ⧸ I)`-algebra equivalence already satisfies that the canonical map
`A → B` is bijective. -/
theorem bijective_algebraMap_of_zariskiPair_of_flat_integral_finitePresentation
    (hI : I ≤ Ring.jacobson A)
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ IB)) :
    Function.Bijective (algebraMap A B) := by
  sorry

end

end Algebra
