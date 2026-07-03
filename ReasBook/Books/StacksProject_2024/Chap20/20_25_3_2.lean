import Mathlib
import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.Chap20.«20_25_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace ComplexShape HomologicalComplex HomologicalComplex₂
open MonoidalCategory
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u v

set_option checkBinderAnnotations false

variable {X : TopCat.{u}} {I : Type v}

local notation "PresheafCochain" => CochainComplex (X.Presheaf AddCommGrpCat) ℤ

/- Domain-style sampling for 20.25.3.2:
- primary domain: Čech double complexes of presheaf-valued cochain complexes, their totalization,
  and the monoidal comparison carried by the resulting total Čech functor;
- sampled owner declarations:
  * `cechDoubleComplexFunctor` and `cechDoubleComplex` from `20_25_0_2`;
  * `HomologicalComplex₂.total.map` and `HomologicalComplex₂.totalFunctor` from mathlib's
    total-complex API;
  * `Functor.LaxMonoidal.μ` from mathlib's monoidal-functor API.
- best owner abstraction in this file: the coefficient-variable functor
  `cechDoubleComplexFunctor 𝒰` imported from `20_25_0_2`, followed by the canonical owner
  `HomologicalComplex₂.totalFunctor`;
- primitive data: the cover `𝒰` together with the objectwise `HasTotal` instances for the
  associated Čech double complexes;
- derived API: totalization of these bicomplex maps and the lax-monoidal comparison map of the
  total Čech functor.

Source/core/bridge triage:
- `source-facing`: the total Čech functor and the tensor comparison of 20.25.3.2;
- `core/canonical`: `cechDoubleComplexFunctor 𝒰`, `HomologicalComplex₂.totalFunctor`, and
  `Functor.LaxMonoidal.μ`;
- `bridge/view`: the specialization of `Functor.LaxMonoidal.μ` to the total Čech functor. -/

/-- The total Čech complex functor `\mathcal F^\bullet \mapsto
\mathrm{Tot}(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet))`. -/
abbrev cechTotalComplexFunctor
    (𝒰 : I → Opens X)
    [∀ F : PresheafCochain, (cechDoubleComplex 𝒰 F).HasTotal (up ℤ)] :
    PresheafCochain ⥤ CochainComplex AddCommGrpCat.{max u v} ℤ :=
  cechDoubleComplexFunctor 𝒰 ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max u v}
      (up ℤ) (up ℤ) (up ℤ)

section TensorComparison

variable [MonoidalCategory (CochainComplex (X.Presheaf AddCommGrpCat) ℤ)]
variable [MonoidalCategory (CochainComplex AddCommGrpCat.{max u v} ℤ)]
variable (𝒰 : I → Opens X)
variable [∀ F : PresheafCochain, (cechDoubleComplex 𝒰 F).HasTotal (up ℤ)]
variable [(cechTotalComplexFunctor 𝒰).LaxMonoidal]
variable (F G : PresheafCochain)

/- 20.25.3.2: the comparison morphism
`\mathrm{Tot}(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet)) \otimes_{\mathbf Z}
\mathrm{Tot}(\check{\mathcal C}^\bullet(\mathcal U, \mathcal G^\bullet)) \to
\mathrm{Tot}(\check{\mathcal C}^\bullet(\mathcal U, \mathcal F^\bullet \otimes \mathcal
G^\bullet))`
is the canonical lax-monoidal structure morphism
`Functor.LaxMonoidal.μ (cechTotalComplexFunctor 𝒰) F G`. -/
#check Functor.LaxMonoidal.μ (cechTotalComplexFunctor 𝒰) F G

end TensorComparison
