import stacks_project.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S M] [Module S' M] [Module R M]
variable [IsScalarTower S S' M] [IsScalarTower R S M] [IsScalarTower R S' M]
variable [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] M

/- Domain-style sampling for the fiberwise flatness criterion with essentially finitely presented
local maps:
* primary domain: local commutative algebra of flatness along local ring maps, with closed fibers
  carried by the canonical owner `Ideal.Fiber`;
* sampled owner declarations:
  `Ideal.Fiber`,
  `RingHom.EssFinitePresentation`,
  `flat_over_middleRing_of_flat_closedFiber_and_flat_over_base`,
  `algebraMap_flat_of_flat_of_faithfullyFlat`;
* best owner abstraction: the closed fiber should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and `ClosedFiberModule = ClosedFiber ⊗[S] M`,
  while the conclusions belong on `Module.Flat S M` and `(algebraMap R S).Flat`; the quotient
  models `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` and
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` are only bridge
  views.

Primitive data vs. derived API:
* primitive data: the local diagram `R → S → S'`, essential finite presentation of `R → S` and
  `R → S'`, a finitely presented `S'`-module `M`, flatness of the canonical closed-fiber module
  `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R`;
* derived API: flatness of `M` over `S`, and with the extra source-facing nontriviality hypothesis,
  flatness of the local map `R → S`.

Source/core/bridge triage:
* `source-facing`: the two clauses of Lemma `10.128.8`;
* `core/canonical`: `RingHom.EssFinitePresentation`, `Ideal.Fiber`, `Module.Flat`, and
  `RingHom.Flat`;
* `bridge/view`: the quotient presentations of the closed fiber ring and module.
-/

-- Proof sketch: approximate the two essentially finitely presented local maps `R → S` and
-- `R → S'` together with the finitely presented `S'`-module `M` by a sufficiently large Noetherian
-- stage using Lemmas `10.127.11` and `10.127.13`. Lemma `10.128.3` descends the flatness of `M`
-- over `R` and of the canonical closed fiber `ClosedFiberModule` over `ClosedFiber` to that stage,
-- where Lemma `10.99.15` applies. Base-changing the resulting stagewise flatness statement back to
-- `R → S → S'` yields flatness of the local map `R → S`.
/-- Lemma 10.128.8 (Critère de platitude par fibres) (1): for local rings `R`, `S`, `S'` and local
homomorphisms `R → S → S'`, assume `R → S` and `R → S'` are essentially of finite presentation,
`M` is a nonzero finitely presented `S'`-module, the canonical closed fiber
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently
`M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))`, is flat over
`ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`, and `M` is flat over `R`. Then `R → S` is
flat. -/
theorem algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S')) [Nontrivial M]
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    (algebraMap R S).Flat := sorry

-- Proof sketch: use the same Noetherian approximation argument as in clause (1). At a large
-- enough stage the data satisfy the Noetherian fiberwise flatness criterion of Lemma `10.99.15`,
-- which gives flatness of the stage module over the stage middle ring. Flatness is preserved under
-- base change along the colimit identification, so the original `S'`-module `M` is flat over `S`.
/-- Lemma 10.128.8 (Critère de platitude par fibres) (2): under the same hypotheses, the
`S'`-module `M` is flat over `S`. Here the fiberwise hypothesis is expressed on the canonical
closed-fiber owner `ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M` over
`ClosedFiber = (maximalIdeal R).Fiber S`, not on a separate quotient-packaged wrapper. -/
theorem flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S'))
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule) (hflat_R : Module.Flat R M) :
    Module.Flat S M := sorry

end
