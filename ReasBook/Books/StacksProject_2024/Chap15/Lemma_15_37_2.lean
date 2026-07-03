import Mathlib
import stacks_project.Chap15.Definition_15_36_1_Topological_rings
import stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

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
