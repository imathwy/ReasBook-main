import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.36.2:
- primary domain: adic topologies on commutative rings and continuity of ring homomorphisms.
- inspected owner declarations:
  * `Ideal.adicTopology`
  * `Ideal.hasBasis_nhds_zero_adic`
  * `Ideal.WithIdeal.uniformContinuous_of_map_le`
- best owner abstraction: the ambient topologies are owned by `Ideal.adicTopology`; the Stacks
  lemma itself is a source-facing continuity criterion and should live on `RingHom`.
- source/core/bridge triage:
  * `source-facing`: the iff criterion for continuity from the `I`-adic topology to the
    `J`-adic topology;
  * `core/canonical`: `Ideal.adicTopology` and the basis theorem
    `Ideal.hasBasis_nhds_zero_adic`;
  * `bridge/view`: `Ideal.WithIdeal.uniformContinuous_of_map_le` for the one-sided
    map-into-the-defining-ideal criterion when the source and target carry preferred ideals.
- primitive data: the ring homomorphism `φ` and the ideals `I`, `J`.
- derived API: the continuity criterion below and the direct downstream monotonicity lemma for
  adic topologies.
-/

namespace RingHom

-- Proof sketch: for the forward direction, continuity at `0` for the additive homomorphism `φ`
-- means some basic open neighborhood `J` of `0` in the `J`-adic topology has open preimage, and
-- the `I`-adic basis identifies that preimage condition with `I ^ n ⊆ φ ⁻¹' J`, i.e.
-- `Ideal.map φ (I ^ n) ≤ J`. For the reverse direction, such an inclusion gives continuity at `0`
-- from the neighborhood bases, and `continuous_of_continuousAt_zero` upgrades this to continuity
-- of the ring homomorphism.
/-- Lemma 15.36.2: a ring homomorphism from `R` with the `I`-adic topology to `S` with the
`J`-adic topology is continuous if and only if the image of some power of `I` is contained in
`J`. -/
theorem continuous_adic_iff_exists_pow_map_le
    (φ : R →+* S) (I : Ideal R) (J : Ideal S) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace S := J.adicTopology
    Continuous φ ↔
      ∃ n : ℕ, Ideal.map φ (I ^ n) ≤ J := by
  letI : TopologicalSpace R := I.adicTopology
  letI : TopologicalSpace S := J.adicTopology
  constructor
  · intro hφ
    have hzero : Filter.Tendsto φ (𝓝 (0 : R)) (𝓝 (0 : S)) := by
      simpa [ContinuousAt, map_zero] using (hφ.continuousAt : ContinuousAt φ (0 : R))
    rw [I.hasBasis_nhds_zero_adic.tendsto_iff J.hasBasis_nhds_zero_adic] at hzero
    obtain ⟨n, -, hn⟩ := hzero 1 trivial
    refine ⟨n, ?_⟩
    simpa [pow_one] using
      (Ideal.map_le_iff_le_comap.mpr hn : Ideal.map φ (I ^ n) ≤ J ^ 1)
  · rintro ⟨n, hmap⟩
    apply continuous_of_continuousAt_zero φ
    rw [ContinuousAt, map_zero, I.hasBasis_nhds_zero_adic.tendsto_iff J.hasBasis_nhds_zero_adic]
    intro m _
    refine ⟨n * m, trivial, ?_⟩
    intro x hx
    have hpow : Ideal.map φ (I ^ (n * m)) ≤ J ^ m := by
      calc
        Ideal.map φ (I ^ (n * m)) = Ideal.map φ ((I ^ n) ^ m) := by rw [pow_mul]
        _ = Ideal.map φ (I ^ n) ^ m := by rw [Ideal.map_pow]
        _ ≤ J ^ m := Ideal.pow_right_mono hmap m
    exact (Ideal.map_le_iff_le_comap.mp hpow) hx

end RingHom

namespace Ideal

/-- If `I ≤ J`, then the `I`-adic topology is finer than the `J`-adic topology. -/
theorem adicTopology_mono {I J : Ideal R} (hIJ : I ≤ J) :
    I.adicTopology ≤ J.adicTopology := by
  have hid : @Continuous R R I.adicTopology J.adicTopology (RingHom.id R) := by
    rw [RingHom.continuous_adic_iff_exists_pow_map_le]
    exact ⟨1, by simpa using hIJ⟩
  simpa [induced_id] using (continuous_iff_le_induced.mp hid)

end Ideal
