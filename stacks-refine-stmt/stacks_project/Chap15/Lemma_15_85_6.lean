import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import stacks_project.Chap15.«15_60_1_1»
import stacks_project.Chap15.Lemma_15_85_3

noncomputable section

open ComplexShape
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
private abbrev extCpx : CpxR ⥤ CpxR' :=
  (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (up ℤ)
local notation "ExtCpx" => (extCpx : CpxR ⥤ CpxR')

/- Domain-style sampling for Lemma 15.85.6:
- primary domain: derived base change for two-term representatives in `D(R)`;
- sampled owner declarations:
  `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`,
  `DerivedCategory.TStructure.t.truncGE`, `Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing datum is the chosen two-term representative `P` of
  `K`, while the core/canonical owners are `IsTwoTermRepresentative`, `K ⊗[R]^L[R']`, and
  `t.truncGE (-1)`;
- primitive vs. derived:
  primitive data are the representative `P` and the flatness of its degree-zero term;
  the scalar-extended complex `ExtCpx.obj P` is only the canonical bridge/view from cochain-level
  base change back to the owner predicate on the truncation target;
- source/core/bridge triage:
  `source-facing`: the statement that two-term representatives stay two-term after flat base
  change and truncation;
  `core/canonical`: `IsTwoTermRepresentative`, `derivedTensorWithAlgebra`, and `t.truncGE`;
  `bridge/view`: the cochain-level scalar extension `ExtCpx.obj P`.

Accordingly, the theorem remains in the owner namespace `IsTwoTermRepresentative` and uses the
imported scalar-extension owner `ExtCpx` directly, rather than introducing a parallel wrapper or
weakening the result to a bare isomorphism statement. -/

-- Proof sketch: write `P` as a two-term complex `P⁻¹ → P⁰` with `P⁰` flat. Tensor the
-- distinguished triangle `P⁰ → P → P⁻¹[1] → P⁰[1]` with `R'`. The flatness of `P⁰` identifies
-- its ordinary tensor product with the derived tensor product, and the degree-support hypothesis
-- on `P` already forces the same cohomological support for `K`, so the scalar-extended complex is
-- concentrated in degrees `-1` and `0`. The induced comparison to `K ⊗[R]^L[R']` is therefore
-- an isomorphism on homology in degrees `≥ -1`, so the scalar-extended complex computes the
-- upper truncation `τ_{\ge -1}` and remains a two-term representative there.
namespace IsTwoTermRepresentative

/-- Lemma 15.85.6: if `P` is a two-term representative of `K` whose degree-zero term is flat,
then the scalar extension of `P` along `R → R'` is a two-term representative of
`τ_{\ge -1}(K ⊗_R^{\mathbf L} R')`. -/
theorem truncGE_derivedTensorWithAlgebra
    {K : DModR} {P : CpxR}
    (hP : IsTwoTermRepresentative K P)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsTwoTermRepresentative ((t.truncGE (-1)).obj (K ⊗[R]^L[R'])) ((ExtCpx).obj P) :=
  sorry

end IsTwoTermRepresentative

end

end CategoryTheory
