import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Tactic.Recall
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Ideal

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_37_1 (from Chap15) -/
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

/-! ### Lemma_15_37_2 (from Chap15) -/
open IsLocalRing
open scoped Topology

universe u v

namespace RingHom

/- Domain-style sampling for Lemma 15.37.2:
- primary domain: formal smoothness of commutative topological rings in the adic/linearly
  topologized setting.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.continuous_adic_iff_exists_pow_map_le`
- best owner abstraction: `RingHom.FormallySmoothTopologically` is the source-facing owner, while
  `RingHom.formally_smooth_for_adic` is the chapter bridge/view for the discrete-source adic
  specialization.
- primitive data: an algebraically formally smooth ring map together with continuity, or an adic
  continuity hypothesis relating the source and target ideals.
- derived API: the algebraic-to-topological bridge below and the owner-level equivalence with
  `formally_smooth_for_adic`.
-/

section Target

variable {S : Type v}
variable [CommRing S] [TopologicalSpace S]
variable [TopologicalRing.IsPreadicRing S]

section

variable {R : Type u}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLinearTopology R R]

-- Proof sketch: in a square-zero lifting problem for Definition `15.37.1`, forget the source
-- topology on `R` and use algebraic formal smoothness of `f` to obtain a lift of the underlying
-- ring maps. Because the target `S` is pre-adic, some power of an ideal of definition maps to zero
-- in the discrete quotient, so the lifted map is automatically continuous. The chapter's
-- linearly-topologized commutative-ring owner uses only `[IsLinearTopology R R]`; any right-module
-- linear-topology view is derived internally in the commutative setting and should not appear in
-- the public statement.
/-- Lemma 15.37.2: under the linear-topology hypotheses on `R` and the pre-adic hypothesis on
`S`, algebraic formal smoothness together with continuity of `f` upgrades to the topological
lifting property of Definition `15.37.1`. -/
theorem FormallySmooth.toTopologically {f : R →+* S} (hf : f.FormallySmooth)
    (hcont : Continuous f) : f.FormallySmoothTopologically := sorry

end

end Target

section LocalTarget

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- A formally étale algebra map into a local ring is formally smooth for the
`maximalIdeal B`-adic topology. -/
theorem formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    (hf : (algebraMap A B).FormallyEtale) :
    (algebraMap A B).formally_smooth_for_adic (maximalIdeal B) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
  letI : TopologicalRing.IsPreadicRing B :=
    { toIsTopologicalRing := inferInstance
      exists_ideal_isAdic := ⟨maximalIdeal B, rfl⟩ }
  change (algebraMap A B).FormallySmoothTopologically
  have hfs : (algebraMap A B).FormallySmooth := by
    rw [formallySmooth_algebraMap]
    letI : Algebra.FormallyEtale A B := (formallyEtale_algebraMap).mp hf
    infer_instance
  exact FormallySmooth.toTopologically hfs continuous_of_discreteTopology

end LocalTarget

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

-- Proof sketch: the forward implication forgets the `𝔪`-adic topology on `R`. For the reverse
-- implication, continuity of `f` for the `𝔪`-adic and `𝔫`-adic topologies implies that some power
-- of `𝔪` maps into `𝔫`; if a lifting problem is posed with discrete source, then the induced map
-- `R → A` is automatically continuous for the `𝔪`-adic topology because some power of `𝔫` kills
-- the quotient and `J² = 0`, so the assumed `𝔪`-adic formal smoothness gives the desired lift.
/-- For a ring map continuous from the `𝔪`-adic topology on `R` to the `𝔫`-adic topology on `S`,
topological formal smoothness for the `𝔪`-adic source topology is equivalent to topological formal
smoothness for the discrete source topology. -/
theorem formallySmoothTopologically_adicSource_iff_discreteSource
    (f : R →+* S) (𝔪 : Ideal R) (𝔫 : Ideal S)
    (hcont : letI : TopologicalSpace R := 𝔪.adicTopology
             letI : TopologicalSpace S := 𝔫.adicTopology
             Continuous f) :
    (letI : TopologicalSpace R := 𝔪.adicTopology
     letI : TopologicalSpace S := 𝔫.adicTopology
     f.FormallySmoothTopologically) ↔
      formally_smooth_for_adic f 𝔫 := sorry

end

end RingHom

/-! ### Definition_15_37_3 (from Chap15) -/
open scoped Topology
open scoped TensorProduct

universe u v

namespace RingHom

section

open Algebra.TensorProduct

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- Definition 15.37.3: a ring map `R → S` is formally smooth for the `𝔫`-adic topology if it is
topologically formally smooth when `R` has the discrete topology and `S` has the `𝔫`-adic
topology. -/
abbrev formally_smooth_for_adic (f : R →+* S) (𝔫 : Ideal S) : Prop :=
  letI : TopologicalSpace R := ⊥
  letI : TopologicalSpace S := Ideal.adicTopology 𝔫
  FormallySmoothTopologically.{u, v, 0} f

/-- The `𝔫`-adic formal smoothness predicate is exactly topological formal smoothness for the
discrete topology on the source and the `𝔫`-adic topology on the target. -/
-- Proof sketch: unfold `formally_smooth_for_adic`, introduce the discrete topology on `R` and the
-- `𝔫`-adic topology on `S`, and then simplify the resulting statement to reflexivity.
theorem formally_smooth_for_adic_iff (f : R →+* S) (𝔫 : Ideal S) :
    formally_smooth_for_adic f 𝔫 ↔
      (letI : TopologicalSpace R := ⊥
       letI : TopologicalSpace S := Ideal.adicTopology 𝔫
       FormallySmoothTopologically.{u, v, 0} f) :=
  sorry

/-- If `f : R →+* S` is formally smooth for the `𝔫`-adic topology and `𝔫 ≤ 𝔫'`, then it is
formally smooth for the `𝔫'`-adic topology. -/
theorem formally_smooth_for_adic_of_le (f : R →+* S) {𝔫 𝔫' : Ideal S} (h𝔫 : 𝔫 ≤ 𝔫')
    (hf : formally_smooth_for_adic f 𝔫) : formally_smooth_for_adic f 𝔫' := sorry

section

universe w

variable {R' : Type w}
variable [CommRing R'] [Algebra R S] [Algebra R R']

-- Proof sketch: translate the adic hypothesis `hf` into the core topological owner
-- `RingHom.FormallySmoothTopologically`, then solve the base-changed lifting problem by the
-- algebraic base-change owner `RingHom.FormallySmooth.isStableUnderBaseChange` applied to the
-- underlying square-zero problem. The induced lift is continuous for the discrete-source and
-- extended-adic target topologies, giving the desired adic formal smoothness.
/-- Lemma 15.37.8: if `R → S` is formally smooth for the `𝔫`-adic topology and `R → R'` is any
ring map, then the canonical base-change map `R' → R' ⊗[R] S` is formally smooth for the adic
topology defined by the extended ideal `𝔫 (R' ⊗[R] S)`. -/
theorem formally_smooth_for_adic_baseChange
    (𝔫 : Ideal S) (hf : formally_smooth_for_adic (algebraMap R S) 𝔫) :
    formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫) := by
  sorry

end

end

section

universe w

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

-- Proof sketch: choose a positive exponent `t` with `J ^ (t : ℕ) ≤ I`, then lift the given map
-- successively modulo the discrete quotients `A ⧸ (J ^ n + I ^ m)` using
-- `RingHom.FormallySmoothTopologically.exists_lift`, exactly as in the Stacks proof. The resulting
-- compatible system defines a ring map `S → A`, and continuity follows from continuity modulo `J`
-- together with Lemma `15.36.2` and the inclusion `J ^ (t : ℕ) ≤ I`.
/-- Lemma 15.37.5: if `f : R →+* S` is formally smooth for the `𝔫`-adic topology and the ambient
topology on `S` is `𝔫`-adic, then any commutative square of topological rings
`S → A ⧸ J`, `R → A` with `A` complete and separated for the chosen ideal of definition `I`, `J`
closed, and some positive power of `J` contained in `I` admits a continuous lift
`S →+* A`. -/
theorem exists_continuous_lift_of_formally_smooth_for_adic
    (f : R →+* S) (𝔫 : Ideal S) (hf : formally_smooth_for_adic f 𝔫) (hS : IsAdic 𝔫)
    (I J : Ideal A) (hA : IsAdic I) [IsAdicComplete I A]
    (hJClosed : IsClosed (J : Set A))
    (hpow : ∃ t : ℕ+, J ^ (t : ℕ) ≤ I)
    (ψ : S →+* A ⧸ J) (hψ : Continuous ψ)
    (g : R →+* A)
    (hcomm : (Ideal.Quotient.mk J).comp g = ψ.comp f) :
    ∃ φ : S →+* A, (Ideal.Quotient.mk J).comp φ = ψ ∧ φ.comp f = g ∧ Continuous φ := sorry

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

open AdicCompletion
open Ideal.Quotient

private theorem exists_pow_map_le_of_continuous
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    ∃ n : ℕ, Ideal.map f (I ^ n) ≤ J :=
  (RingHom.continuous_adic_iff_exists_pow_map_le f I J).mp hcont

private noncomputable def adicCompletionMapPow
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    ℕ :=
  by
    classical
    exact Classical.choose (exists_pow_map_le_of_continuous I J f hcont)

private theorem adicCompletionMapPow_spec
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    Ideal.map f (I ^ adicCompletionMapPow I J f hcont) ≤ J :=
  by
    classical
    exact Classical.choose_spec (exists_pow_map_le_of_continuous I J f hcont)

/-- The quotient-level maps from `R^∧` to the canonical quotients `S ⧸ J ^ n` induced by the
continuous map `R → S`. -/
private noncomputable def adicCompletionMapQuotientMap
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f)
    (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  let k := adicCompletionMapPow I J f hcont
  let hk := adicCompletionMapPow_spec I J f hcont
  let hkpow : Ideal.map f (I ^ (k * n)) ≤ J ^ n :=
    calc
      Ideal.map f (I ^ (k * n)) = Ideal.map f ((I ^ k) ^ n) := by
        rw [pow_mul]
      _ = Ideal.map f (I ^ k) ^ n := by
        rw [Ideal.map_pow]
      _ ≤ J ^ n := Ideal.pow_right_mono hk n
  (Ideal.quotientMap (J ^ n) f (Ideal.map_le_iff_le_comap.mp hkpow)).comp (evalₐ I (k * n))

/- The quotient maps defining `RingHom.adicCompletionMap` are compatible with the transition maps
of the inverse system for the target completion. -/
private theorem adicCompletionMapQuotientMap_compatible
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f)
    {m n : ℕ} (hle : m ≤ n) :
    (factorPow J hle).comp (adicCompletionMapQuotientMap I J f hcont n) =
      adicCompletionMapQuotientMap I J f hcont m := sorry

-- Proof sketch: use continuity of `R → S` to get quotient maps
-- `R ⧸ I^(kn) → S ⧸ J^n` for a single exponent `k`; precompose with
-- `AdicCompletion.evalₐ I (kn)`, and then apply the canonical completion lift owner
-- `AdicCompletion.liftRingHom`.
/-- The canonical map from `R^∧` to `S^∧` induced by the continuous map `R → S`. -/
noncomputable def adicCompletionMap
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J
    (adicCompletionMapQuotientMap I J f hcont)
    (adicCompletionMapQuotientMap_compatible I J f hcont)

/-- The canonical map on source completions extends the canonical map from `R` to the completed
target `S^∧`. -/
theorem adicCompletionMap_comp
    (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    (f.adicCompletionMap I J hcont).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f := sorry

-- Proof sketch: use finite generation of `I` and `J` to identify the quotients of `R`, `S`, and
-- their adic completions modulo powers of the defining ideals. The lifting diagrams in
-- `RingHom.FormallySmoothTopologically` for `R → S`, `R → S^∧`, and `R^∧ → S^∧` are then in
-- natural bijection, so the three formal smoothness conditions are equivalent.
/-- Lemma 15.37.4: let `I` be a finitely generated ideal of `R` and `J` a finitely generated ideal
of `S`. Assume also that `f : R →+* S` is continuous from the `I`-adic topology to the `J`-adic
topology. Then the following are equivalent: `R → S` is formally smooth for the `J`-adic
topology; the canonical map `R → S^∧` is formally smooth for the adic topology defined by the
extended ideal `J^∧`; and the induced map `R^∧ → S^∧` is formally smooth for the adic topology
defined by `J^∧`. Here `R^∧` and `S^∧` denote the `I`-adic and `J`-adic completions. -/
theorem formally_smooth_for_adic_tfae_completion_invariance
    (I : Ideal R) (hI : I.FG) (J : Ideal S) (hJ : J.FG) (f : R →+* S)
    (hcont : letI : TopologicalSpace R := I.adicTopology
             letI : TopologicalSpace S := J.adicTopology
             Continuous f) :
    let K := Ideal.map (algebraMap S (AdicCompletion J S)) J
    List.TFAE [
      f.formally_smooth_for_adic J,
      ((algebraMap S (AdicCompletion J S)).comp f).formally_smooth_for_adic K,
      (f.adicCompletionMap I J hcont).formally_smooth_for_adic K
    ] := sorry

end

end RingHom

/-! ### Lemma_15_37_4 (from Chap15) -/
/- Domain-style sampling for Lemma 15.37.4:
- primary domain: adic completion and adic formal smoothness of commutative ring maps.
- inspected owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.adicCompletionMap`
  * `RingHom.adicCompletionMap_comp`
  * `AdicCompletion.liftRingHom`
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the source-facing owner for the
  formal-smoothness statements, while `RingHom.adicCompletionMap` is the owner-level bridge from a
  continuous adic ring map to the induced map on completions; the lower-level completion lift API
  `AdicCompletion.liftRingHom` is core/canonical implementation.
- primitive data: the ideals `I`, `J`, the ring map `f`, finite generation of `I` and `J`, and
  the continuity witness from the `I`-adic topology to the `J`-adic topology.
- derived API: the canonical completion map `R^∧ → S^∧`, its extension property, and the `TFAE`
  completion-invariance statement.
- source/core/bridge triage:
  * `source-facing`: the completion-invariance `TFAE` below.
  * `core/canonical`: `AdicCompletion.liftRingHom`.
  * `bridge/view`: `RingHom.adicCompletionMap` and
    `RingHom.formally_smooth_for_adic_tfae_completion_invariance`. -/

/- Lemma 15.37.4 now lives with the owner-level bridge API on `RingHom`, so this file is a direct
canonical check of that theorem. -/
#check RingHom.formally_smooth_for_adic_tfae_completion_invariance

/-! ### Lemma_15_37_5 (from Chap15) -/
/- Domain-style sampling for Lemma 15.37.5:
- primary domain: topological formal smoothness for adic topologies on commutative rings.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_iff`
  * `IsAdic`
  * `IsAdicComplete`
- owner abstraction: `RingHom.formally_smooth_for_adic`.
- source/core/bridge triage:
  * source-facing: the adic lifting theorem for a formally smooth-for-adic map, with a chosen
    ideal of definition `I` on the target.
  * core/canonical: `RingHom.FormallySmoothTopologically`.
  * bridge/view: the ambient-topology witnesses `hS : IsAdic 𝔫` and `hA : IsAdic I`.
- primitive data: the formally smooth-for-adic hypothesis `hf` and the target-side ideal-of-
  definition data `hA : IsAdic I`, together with the complete-separated owner
  `[IsAdicComplete I A]` and the eventual containment `∃ t : ℕ+, J ^ (t : ℕ) ≤ I`.
- derived API: ambient-topology continuity of the given quotient map `ψ` and of the resulting lift
  `φ`, recovered through the adic witnesses.
-/

/- Lemma 15.37.5: the adic lifting theorem is derived API for the owner
`RingHom.formally_smooth_for_adic`, so the theorem now lives in the owner file
`Definition_15_37_3`. -/
recall RingHom.exists_continuous_lift_of_formally_smooth_for_adic

/-! ### Lemma_15_37_6 (from Chap15) -/
/- Domain-style sampling for Lemma 15.37.6:
- primary domain: adic topologies and topological formal smoothness of commutative ring maps.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmoothTopologically.of_le`
  * `RingHom.formally_smooth_for_adic`
  * `Ideal.adicTopology_mono`
- best owner abstraction: the owner for the present bridge is
  `RingHom.formally_smooth_for_adic`; the monotonicity theorem belongs next to that owner and is
  derived from the core theorem `RingHom.FormallySmoothTopologically.of_le`.
- primitive data: the ring map `f`, the two ideals `𝔫 ≤ 𝔫'`, and formal smoothness for the finer
  `𝔫`-adic topology.
- derived API: monotonicity for `RingHom.formally_smooth_for_adic`.
- source/core/bridge triage:
  * `source-facing`: formal smoothness for the `𝔫'`-adic topology.
  * `core/canonical`: `RingHom.FormallySmoothTopologically.of_le`.
  * `bridge/view`: `RingHom.formally_smooth_for_adic` and its monotonicity theorem.
-/

/- Lemma 15.37.6: if `R → S` is formally smooth for the `𝔫`-adic topology and `𝔫 ≤ 𝔫'`, then it
is formally smooth for the `𝔫'`-adic topology. This source-facing bridge is now used directly from
the owner file of `RingHom.formally_smooth_for_adic`. -/
recall RingHom.formally_smooth_for_adic_of_le

/-! ### Lemma_15_37_7 (from Chap15) -/
/- Domain-style sampling for Lemma 15.37.7:
- primary domain: topological formal smoothness of continuous homomorphisms of commutative
  topological rings.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmoothTopologically.comp`
  * `RingHom.FormallySmoothTopologically.id`
  * `RingHom.formally_smooth_for_adic`
- best owner abstraction: the source-facing and canonical owner for this file is
  `RingHom.FormallySmoothTopologically`; this lemma is the owner-level derived API
  `RingHom.FormallySmoothTopologically.comp`.
- primitive data: formal smoothness of the two factors.
- derived API: formal smoothness of the composite map, together with the instance form in the
  owner file.

Source/core/bridge triage:
- `source-facing`: the topological lifting property `RingHom.FormallySmoothTopologically`.
- `core/canonical`: the owner-level composition theorem
  `RingHom.FormallySmoothTopologically.comp`.
- `bridge/view`: adic reformulations such as `RingHom.formally_smooth_for_adic`. -/

/- Lemma 15.37.7: a composition of formally smooth continuous homomorphisms of commutative
topological rings is formally smooth. This is exactly the owner-level theorem
`RingHom.FormallySmoothTopologically.comp`. -/
recall RingHom.FormallySmoothTopologically.comp

/-! ### Lemma_15_37_8 (from Chap15) -/
/- Domain-style sampling for Lemma 15.37.8:
- primary domain: adic topological formal smoothness of commutative ring maps under tensor-product
  base change.
- inspected owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_of_le`
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmooth.isStableUnderBaseChange`
- best owner abstraction: the source-facing theorem belongs to the chapter owner
  `RingHom.formally_smooth_for_adic`; the lower-level topological owner and the algebraic
  base-change owner are implementation/core layers.
- primitive data: the ideal `𝔫 : Ideal S`, the adic formal smoothness hypothesis for
  `algebraMap R S`, and the algebra structures needed to form `R' ⊗[R] S`.
- derived API: formal smoothness for the canonical base-change map with respect to the extended
  ideal on the tensor product.
- source/core/bridge triage:
  * `source-facing`: adic formal smoothness of the base-changed map.
  * `core/canonical`: `RingHom.FormallySmoothTopologically` and
    `RingHom.FormallySmooth.isStableUnderBaseChange`.
  * `bridge/view`: `RingHom.formally_smooth_for_adic`. -/

/- Lemma 15.37.8: base change for adic formal smoothness is now owner-level derived API on
`RingHom.formally_smooth_for_adic`, so this file is a direct recall of that theorem. -/
recall RingHom.formally_smooth_for_adic_baseChange

/-! ### Lemma_15_37_9 (from Chap15) -/
open scoped TensorProduct

universe u v w

namespace RingHom

section

open Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling for Lemma 15.37.9:
- primary domain: descent of adic topological formal smoothness along a split base change in
  commutative algebra.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`, the core topological lifting owner from Definition
    `15.37.1`;
  * `RingHom.formally_smooth_for_adic`, the chapter owner bridge for the discrete-source adic
    specialization from Definition `15.37.3`;
  * `RingHom.formally_smooth_for_adic_baseChange`, the forward base-change theorem from
    Lemma `15.37.8`;
  * `RingHom.formallySmoothTopologically_adicSource_iff_discreteSource`, the source-topology bridge
    from Lemma `15.37.2`.
- best owner abstraction: the source-facing theorem in this file should use the chapter adic owner
  `RingHom.formally_smooth_for_adic`; the lower-level owner
  `RingHom.FormallySmoothTopologically` is the core/canonical implementation layer.
- primitive data: the ideal `𝔫 : Ideal S`, the split `R`-linear retraction of `R → R'`, and
  formal smoothness for the base-changed map with respect to the extended ideal.
- derived API: descent of formal smoothness for the original map `R → S`.

Source/core/bridge triage:
- `source-facing`: formal smoothness of `R → S` for the `𝔫`-adic topology.
- `core/canonical`: `RingHom.FormallySmoothTopologically`.
- `bridge/view`: `RingHom.formally_smooth_for_adic`. -/

-- Proof sketch: given a square-zero lifting problem for `R → S`, base change it along `R → R'`
-- to a lifting problem for `R' → R' ⊗[R] S`. The assumed topological formal smoothness over `R'`
-- gives a lift after base change. Choose an `R`-linear retraction `R' → R`, use it to split
-- `A ⊗[R] R'` as `A ⊕ (A ⊗[R] C)`, and then project the lifted map back to the summand `A`,
-- exactly as in the Stacks Project argument.
/-- Lemma 15.37.9: if `R` is an `R`-linear direct summand of `R'` and the canonical base-change map
`R' → R' ⊗[R] S` is formally smooth for the adic topology defined by the extended ideal
`𝔫 (R' ⊗[R] S)`, then `R → S` is formally smooth for the `𝔫`-adic topology. -/
theorem formally_smooth_for_adic_of_split_baseChange
    (𝔫 : Ideal S)
    (hsplit : ∃ σ : R' →ₗ[R] R, Function.LeftInverse σ (Algebra.linearMap R R'))
    (hf : formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫)) :
    formally_smooth_for_adic (algebraMap R S) 𝔫 := sorry

end

end RingHom
