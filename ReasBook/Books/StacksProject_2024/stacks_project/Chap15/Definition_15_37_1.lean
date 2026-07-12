import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- The canonical square-zero lifting property for a formally smooth ring map, restated in
ring-hom language. -/
theorem FormallySmooth.exists_lift {f : R →+* S} (hf : f.FormallySmooth) {A : Type*}
    [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥) (g : S →+* A ⧸ J) (g0 : R →+* A)
    (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    ∃ gLift : S →+* A, (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0 := by
  letI := f.toAlgebra
  letI := g0.toAlgebra
  letI : Algebra.FormallySmooth R S := hf.toAlgebra
  let gAlg : S →ₐ[R] A ⧸ J :=
    { toRingHom := g
      commutes' := fun r ↦ by
        change g (f r) = Ideal.Quotient.mk J (g0 r)
        exact (DFunLike.congr_fun comm r).symm }
  obtain ⟨gLift, hgLift⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ gAlg
  refine ⟨gLift.toRingHom, ?_, ?_⟩
  · ext s
    exact DFunLike.congr_fun hgLift s
  · ext r
    exact gLift.commutes r

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/- Domain-style sampling for Definition 15.37.1:
- primary domain: topological formal smoothness for continuous homomorphisms of commutative
  topological rings.
- inspected owner declarations:
  * `TopCommRingCat.of R ⟶ TopCommRingCat.of S`, the canonical ambient owner for continuous ring
    maps;
  * `RingHom.FormallySmooth`, the algebraic owner obtained by forgetting topology;
  * `Algebra.FormallySmooth.iff_comp_surjective`, the canonical square-zero lifting criterion
    upstream;
  * `continuous_le_dom` and `continuous_le_rng`, the canonical topology-change API for continuous
    maps.
- best owner abstraction: the source-facing owner is `RingHom.FormallySmoothTopologically`; the
  algebraic owner `RingHom.FormallySmooth` is only a bridge/view used under stronger hypotheses in
  direct downstream files.
- source/core/bridge triage:
  * `source-facing`: the topological square-zero lifting property for a continuous ring map;
  * `core/canonical`: continuous ring-hom morphisms and the algebraic owner
    `RingHom.FormallySmooth`;
  * `bridge/view`: the adic specialization `RingHom.formally_smooth_for_adic` in
    `Definition_15_37_3` and the pre-adic algebraic-to-topological bridge in `Lemma_15_37_2`.
- primitive data: continuity of `f` and existence of continuous lifts in square-zero problems with
  discrete quotient.
- derived API: `id`, `comp`, and `of_le` below.
-/

/-- Definition 15.37.1: a continuous ring map of commutative topological rings is topologically
formally smooth if every commutative square with square-zero kernel and canonically discrete
quotient `A ⧸ J` admits a continuous lift. -/
class FormallySmoothTopologically (f : R →+* S) : Prop extends Continuous f where
  -- `A ⧸ J` carries mathlib's canonical quotient topology.
  lift_condition {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
      (g : S →+* A ⧸ J) (hg : Continuous g)
      (g0 : R →+* A) (hg0 : Continuous g0)
      (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
      ∃ gLift : S →+* A, Continuous gLift ∧
        (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0

/-- The lifting property packaged by `FormallySmoothTopologically`, exposed as the theorem-level
API for the owner, again with the canonical quotient topology on `A ⧸ J`. -/
theorem FormallySmoothTopologically.exists_lift {f : R →+* S} (hf : f.FormallySmoothTopologically)
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J) (hg : Continuous g)
    (g0 : R →+* A) (hg0 : Continuous g0)
    (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    ∃ gLift : S →+* A, Continuous gLift ∧
      (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0 := by
  sorry

/-- The identity map of a commutative topological ring is formally smooth in the topological
sense. -/
instance FormallySmoothTopologically.id : (RingHom.id R).FormallySmoothTopologically where
  toContinuous := continuous_id
  lift_condition := by
    sorry

/-- Compositions of topologically formally smooth ring maps are topologically formally smooth. -/
theorem FormallySmoothTopologically.comp {T : Type*} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.FormallySmoothTopologically) (hg : g.FormallySmoothTopologically) :
    (g.comp f).FormallySmoothTopologically := by
  sorry

instance {T : Type*} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (f : R →+* S) (g : S →+* T) [hf : f.FormallySmoothTopologically]
    [hg : g.FormallySmoothTopologically] : (g.comp f).FormallySmoothTopologically :=
  hf.comp hg

section

omit [TopologicalSpace S] [IsTopologicalRing S]

/-- Topological formal smoothness persists when the topology on the target ring is weakened. -/
theorem FormallySmoothTopologically.of_le
    (f : R →+* S) {t t' : TopologicalSpace S}
    [ht : letI : TopologicalSpace S := t; IsTopologicalRing S]
    [ht' : letI : TopologicalSpace S := t'; IsTopologicalRing S]
    (h : t ≤ t')
    (hf : letI : TopologicalSpace S := t
          letI : IsTopologicalRing S := ht
          f.FormallySmoothTopologically) :
    letI : TopologicalSpace S := t'
    letI : IsTopologicalRing S := ht'
    f.FormallySmoothTopologically := by
  sorry

end

end

end RingHom
