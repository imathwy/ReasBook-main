import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_101_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian

noncomputable section

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling for Remark 15.101.9:
- primary domain: the weak `Ext` system on the reduction-side family
  `(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n ≥ 1}` from Chapter `15`;
- sampled owner declarations:
  `IadicFiniteModuleSystem`,
  `extReductionSystem`,
  `extQuotientSystem`,
  `extQuotientSystem_isomorphic_extReductionSystem`;
- best owner abstraction:
  `source-facing`: `extReductionSystem I M N i`, the reduction-side weak `Ext` system itself;
  `core/canonical`: `IadicFiniteModuleSystem A I`, the chapter owner for weak `I`-adic systems;
  `bridge/view`: `extQuotientSystem_isomorphic_extReductionSystem`, identifying the reduction
    system with the quotient-side weak `Ext` system from Lemma `15.101.8`;
- primitive vs. derived:
  the primitive source-facing datum here is the reduction-side weak system itself, not an
  existential morphism in the quotient category;
  the comparison with the quotient-side system is derived bridge API supplied upstream by
  Lemma `15.101.8`.

Source/core/bridge triage:
- `source-facing`: `extReductionSystem`;
- `core/canonical`: `IadicFiniteModuleSystem`;
- `bridge/view`: `extQuotientSystem_isomorphic_extReductionSystem`.

This remark should therefore recall the reduction-side weak-system owner directly, and reuse the
existing comparison theorem rather than restating it as a weaker existential bounded-kernel /
bounded-cokernel package. -/

/- Remark 15.101.9: the family
`(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n ≥ 1}` is itself the source-facing weak
`I`-adic system `extReductionSystem I M N i` from Lemma `15.101.8`. -/
recall extReductionSystem

/- Companion recall: Lemma `15.101.8` identifies this reduction-side weak `Ext` system with the
canonical quotient-side weak `Ext` system
`(\operatorname{Ext}^i_A(M, N) / I^n \operatorname{Ext}^i_A(M, N))_{n ≥ 1}` in the category
`\mathcal C` of Remark `15.101.6`. -/
recall extQuotientSystem_isomorphic_extReductionSystem

end
