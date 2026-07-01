import Mathlib
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap15.Definition_15_116_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x y z

/-
Domain-style sampling for Lemma 15.117.5:
- primary domain: Epp-style elimination of inseparability for solution fields of extensions of
  discrete valuation rings;
- sampled owner declarations:
  `IsSolutionFor`,
  `IsSeparableSolutionFor`,
  `solutionFor_of_finite_extension`,
  `exists_separableSolution_of_exists_solution`;
- best owner abstraction: the source-facing content here is still the intermediate-field theorem,
  but its solution predicate should be the chapter owner `IsSolutionFor` from
  `Definition_15_116_1`; `IsSeparableSolutionFor` is only companion API because the source asks
  for `K₃ / K₁` to be separable, not necessarily `K₃ / K`;
- primitive-vs-derived split: the primitive data are the DVR extension `A ⊂ B`, its fraction
  fields `K ⊂ L`, the tower `K ⊂ K₁ ⊂ K₂`, and the hypotheses on separability, Nagata-ness, and
  purely inseparable degree; the characteristic-`p` consequence of a purely inseparable extension
  of degree `p` is derived theorem data, not a primitive ambient assumption; the conclusion that
  `K₃` remains a solution is expressed through the owner predicate `IsSolutionFor`, while the
  `K₁`-separability of `K₃` is derived theorem data, not a new owner.

Source/core/bridge triage:
- `source-facing`: the existence of a finite extension `K₃ / K₁` that is separable over `K₁` and
  still solves `A ⊂ B`;
- `core/canonical`: `IsSolutionFor`;
- `bridge/view`: `IsSeparableSolutionFor`, which packages the stronger special case of
  separability over the base field `K`.
-/

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2]
variable {p : ℕ} [Fact p.Prime]
variable [Algebra.IsSeparable K L] [NagataRing B] [IsPurelyInseparable K1 K2]

-- Proof sketch: start from the given solution over the purely inseparable degree-`p` extension
-- `K₂ / K₁`, use the Nagata and separability hypotheses to compare the integral closures after
-- base change, and then perform the Artin-Schreier deformation argument from the textbook to
-- replace the radicial extension by a finite separable extension `K₃ / K₁` while preserving the
-- solution property for `A ⊂ B`.
/-- Lemma 15.117.5: let `A ⊂ B` be an extension of discrete valuation rings with fraction fields
`K ⊂ L`, let `K₂ / K₁ / K` be a tower of finite field extensions, and assume `L / K` is
separable, `B` is Nagata, `p` is prime, `K₂ / K₁` is purely inseparable of degree `p`, and
`K₂ / K` is a solution for `A ⊂ B`. Then there exists a finite separable extension `K₃ / K₁`
such that
`K₃ / K` is again a solution for `A ⊂ B` in the sense of Definition `15.116.1`. -/
theorem exists_separable_solution_of_solution_of_purelyInseparable_degree_eq_prime
    (hK2 : IsSolutionFor A B K L K2)
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ (K3 : Type (max u v w x y z)) (_ : Field K3) (_ : Algebra A K3) (_ : Algebra K K3)
      (_ : IsScalarTower A K K3) (_ : Algebra K1 K3) (_ : IsScalarTower K K1 K3)
      (_ : FiniteDimensional K1 K3) (_ : Algebra.IsSeparable K1 K3),
      IsSolutionFor A B K L K3 := sorry

end
