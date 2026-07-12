import Mathlib
import StacksProject_2024.Chap10.Lemma_10_73_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: flat base change for `Ext` in `ModuleCat`, expressed through the canonical
  change-of-rings comparison coming from the `extendScalars`/`restrictScalars` adjunction;
- inspected same-domain owners:
  `Functor.mapExtAddHom`,
  `moduleCatExtFlatBaseChangeComparison`,
  `moduleCatExtFlatBaseChangeAdjointComparison`,
  `moduleCat_ext_flat_baseChange_adjoint_bijective`;
- best owner abstraction: the Chapter 10 owner theorem
  `moduleCat_ext_flat_baseChange_adjoint_bijective`, with degree-`1` surjectivity as a thin
  source-facing specialization;
- primitive data: the ring map `R → S`, an `R`-module `M`, an `S`-module `N`, and flatness;
- derived API: the degree-`1` surjectivity consequence.

Source/core/bridge triage:
- `source-facing`: the degree-`1` surjectivity formulation used in this chapter;
- `core/canonical`: `moduleCatExtFlatBaseChangeAdjointComparison` and its owner theorem
  `moduleCat_ext_flat_baseChange_adjoint_bijective`;
- `bridge/view`: `Functor.mapExtAddHom` for `extendScalars (algebraMap R S)` together with the
  `extendScalars`/`restrictScalars` adjunction.
-/

-- Proof sketch: this is exactly the degree-`1` surjectivity half of the canonical flat
-- base-change bijection for `Ext`, already established in Chapter `10`.
/-- Lemma 15.90.8: for a flat ring map `R → S`, the canonical adjoint flat base-change
comparison
`Ext¹_R(M, N|_R) → Ext¹_S(S ⊗[R] M, N)`
is surjective. -/
@[stacks 05EG]
theorem moduleCatExtOneFlatBaseChangeAdjointComparison_surjective
    (M : ModuleCat R) (N : ModuleCat S) (hflat : (algebraMap R S).Flat) :
    Function.Surjective (moduleCatExtFlatBaseChangeAdjointComparison M N hflat 1) :=
  (moduleCat_ext_flat_baseChange_adjoint_bijective M N hflat 1).2

end
