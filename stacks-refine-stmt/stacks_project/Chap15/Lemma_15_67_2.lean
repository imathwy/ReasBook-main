import stacks_project.Chap13.Definition_13_8_1
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap15.Lemma_15_67_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.Limits
open DerivedCategory

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

namespace CochainComplex

/- Domain-style sampling:
- primary domain: lower-bounded tor-amplitude in `D(R)` and the source-facing flatness of the
  syzygy `cokernel (K.dFrom (a - 1))` of a bounded-above flat cochain representative;
- sampled owner declarations:
  `HasTorAmplitudeGE`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.minus`;
- source/core/bridge triage:
  `source-facing`: flatness of `cokernel (K.dFrom (a - 1))` under the source hypotheses on `K`;
  `core/canonical`: the chapter owners `HasTorAmplitudeGE (Q.obj K) a`, `K.IsKFlat`,
    `K.IsTermwiseFlat`, and `CochainComplex.minus (ModuleCat R) K`;
  `bridge/view`: exactness of the degree-zero tensor complexes computing lower tor-amplitude once
    `K` is known to be K-flat.

Primitive data are the bounded-above hypothesis on `K`, its termwise flatness, and the canonical
derived owner `HasTorAmplitudeGE (Q.obj K) a`. The exactness statements after tensoring with
degree-zero modules are derived bridge data, while representative-level K-flatness is supplied by
the existing bridge theorem `CochainComplex.isKFlat_of_boundedAbove_of_flat` rather than by any
parallel local wrapper.
-/

-- Proof sketch: apply `CochainComplex.isKFlat_of_boundedAbove_of_flat` to replace the
-- bounded-above termwise-flat representative by the canonical owner predicate `K.IsKFlat`. Then
-- lower-bounded tor-amplitude of `Q.obj K` gives exactness of `K ⊗ M` at degree `a - 1` for
-- every `R`-module `M`. Since the terms of `K` are flat and `K` is bounded above, the tail
-- ending in `cokernel (K.dFrom (a - 1))` is a flat resolution, so `Tor₁` of that cokernel with
-- any `M` vanishes. Apply the flatness criterion from Lemma `10.75.8`.
/-- Lemma 15.67.2: if the derived object represented by a bounded above cochain complex of flat
`R`-modules has tor-amplitude in `[a, ∞]`, then the cokernel of
`K.dFrom (a - 1) : K^(a - 1) ⟶ K^a` is flat. -/
theorem flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
    (K : CochainComplex (ModuleCat R) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hFlat : K.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj K) a) :
    Module.Flat R ↑((cokernel (K.dFrom (a - 1)) : ModuleCat R)) := sorry

end CochainComplex

end

end CategoryTheory
