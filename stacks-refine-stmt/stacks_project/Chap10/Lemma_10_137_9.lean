import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_136_1
import stacks_project.Chap10.Lemma_10_137_3
import stacks_project.Chap10.Lemma_10_137_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.137.9: if `R → S` is smooth, then `Spec S` admits a standard-open cover by
basic opens `D(g)` such that each localization `S[1 / g]` is standard smooth over `R`. This is
exactly the canonical theorem `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`. -/
recall Algebra.Smooth.exists_span_eq_top_isStandardSmooth

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: smooth and syntomic morphisms in commutative algebra, localized on standard-open
  charts and tested fiberwise over residue fields;
- sampled owner declarations:
  `RingHom.smooth_algebraMap`,
  `RingHom.Smooth.flat`,
  `RingHom.Smooth.finitePresentation`,
  `Algebra.Smooth.baseChange`,
  `Algebra.smooth_isLocalCompleteIntersection`;
- best owner abstraction:
  `RingHom.Syntomic` is the canonical owner on the conclusion side, and its primitive fields are
  supplied directly from the owner `Smooth R S` together with the fiberwise smooth-to-local-
  complete-intersection bridge over fields;
- primitive vs. derived:
  the primitive source hypothesis is `[Smooth R S]`; ring-hom smoothness, flatness, finite
  presentation, and the local complete intersection property of the fibers are all derived API
  from the sampled owners and should not be repackaged locally.

Source/core/bridge triage:
- `source-facing`: the bridge theorem that a smooth ring map is syntomic;
- `core/canonical`: `RingHom.Syntomic`;
- `bridge/view`: the ring-hom smoothness view of `[Smooth R S]`, its flatness and finite-
  presentation projections, and the fiberwise base-change view reducing the last field to
  `Algebra.smooth_isLocalCompleteIntersection`.
-/

open PrimeSpectrum

-- Proof sketch: reinterpret `[Smooth R S]` as the ring-hom owner on `algebraMap R S`, whose
-- canonical projections provide flatness and finite presentation. For each prime `p` of `R`, the
-- fiber `κ(p) ⊗[R] S` is smooth over the field `κ(p)` by `Algebra.Smooth.baseChange`, hence a
-- local complete intersection by Lemma `10.137.4`.
/-- A smooth ring map `R → S` is syntomic. -/
theorem smooth_syntomic [Smooth R S] :
    (algebraMap R S).Syntomic := by
  let hsmooth : (algebraMap R S).Smooth := (RingHom.smooth_algebraMap).2 inferInstance
  refine ⟨hsmooth.flat, hsmooth.finitePresentation, ?_⟩
  let _ : Algebra R S := (algebraMap R S).toAlgebra
  let _ : Smooth R S := (RingHom.smooth_algebraMap).1 hsmooth
  intro p
  let _ : Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  exact inferInstance

end Algebra
