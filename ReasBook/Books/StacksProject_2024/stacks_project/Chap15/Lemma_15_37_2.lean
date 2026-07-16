import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_36_1_Topological_rings
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3

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

section Helpers

variable {R : Type u} {S : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Helper for Lemma 15.37.2: if an open ideal of the source lies in the kernel of a ring
homomorphism, then the homomorphism is continuous. -/
theorem continuous_of_open_ideal_le_ker (φ : R →+* S) (I : Ideal R)
    (hIopen : IsOpen (I : Set R)) (hIker : I ≤ RingHom.ker φ) :
    Continuous φ := by
  -- Check continuity at `0`; the open kernel ideal is a neighborhood that maps entirely to `0`.
  apply continuous_of_continuousAt_zero φ
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  refine Filter.mem_of_superset (hIopen.mem_nhds I.zero_mem) ?_
  intro x hx
  have hxker : φ x = 0 := RingHom.mem_ker.mp (hIker hx)
  simpa [hxker] using mem_of_mem_nhds hU

end Helpers

section Helpers

variable {R : Type u} {S : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [DiscreteTopology S]

/-- Helper for Lemma 15.37.2: a continuous map from an adic ring to a discrete ring kills some
power of the ideal of definition. -/
theorem pow_le_ker_of_continuous_to_discrete_quotient
    (I : Ideal R) (hI : IsAdic I) (φ : R →+* S) (hφ : Continuous φ) :
    ∃ n : ℕ, I ^ n ≤ RingHom.ker φ := by
  have hbot : IsAdic (⊥ : Ideal S) := by
    rw [is_bot_adic_iff]
    infer_instance
  -- Rewrite the given continuity statement into the adic-topology criterion with target ideal `⊥`.
  letI : TopologicalSpace R := I.adicTopology
  letI : TopologicalSpace S := Ideal.adicTopology (⊥ : Ideal S)
  have hφ' : Continuous φ := by
    cases hI
    cases hbot
    simpa using hφ
  rcases (RingHom.continuous_adic_iff_exists_pow_map_le φ I (⊥ : Ideal S)).mp hφ' with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [RingHom.ker_eq_comap_bot] using
    (Ideal.map_le_iff_le_comap.mp hn : I ^ n ≤ Ideal.comap φ ⊥)

end Helpers

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
    (hcont : Continuous f) : f.FormallySmoothTopologically := by
  rcases (inferInstance : TopologicalRing.IsPreadicRing S).exists_ideal_isAdic with ⟨I, hI⟩
  refine
    { toContinuous := hcont
      lift_condition := ?_ }
  intro A _ _ _ J _ hJ g hg g0 hg0 hcomm
  -- First forget the topology and solve the square-zero problem algebraically.
  rcases hf.exists_lift J hJ g g0 hcomm with ⟨gLift, hgLift, hgLift₀⟩
  -- Continuity of the quotient map forces a power of the ideal of definition into the kernel.
  rcases pow_le_ker_of_continuous_to_discrete_quotient I hI g hg with ⟨n, hn⟩
  have hmapJ : Ideal.map gLift (I ^ n) ≤ J := by
    refine Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx
    have hxzero : g x = 0 := RingHom.mem_ker.mp (hn hx)
    have hxquot : Ideal.Quotient.mk J (gLift x) = 0 := by
      simpa [hxzero] using DFunLike.congr_fun hgLift x
    simpa [Ideal.mem_comap] using (Ideal.Quotient.eq_zero_iff_mem.mp hxquot)
  -- Square-zero then upgrades that inclusion to an open power contained in the kernel of the lift.
  have hmapBot : Ideal.map gLift (I ^ (n * 2)) ≤ ⊥ := by
    calc
      Ideal.map gLift (I ^ (n * 2)) = Ideal.map gLift ((I ^ n) ^ 2) := by
        rw [pow_mul]
      _ = Ideal.map gLift (I ^ n) ^ 2 := by
        rw [Ideal.map_pow]
      _ ≤ J ^ 2 := Ideal.pow_right_mono hmapJ 2
      _ = ⊥ := hJ
  have hkerLift : I ^ (n * 2) ≤ RingHom.ker gLift := by
    simpa [RingHom.ker_eq_comap_bot] using
      (Ideal.map_le_iff_le_comap.mp hmapBot : I ^ (n * 2) ≤ Ideal.comap gLift ⊥)
  have hopen : IsOpen ((I ^ (n * 2) : Ideal S) : Set S) := by
    exact (isAdic_iff.mp hI).1 (n * 2)
  have hgLiftCont : Continuous gLift :=
    continuous_of_open_ideal_le_ker gLift (I ^ (n * 2)) hopen hkerLift
  exact ⟨gLift, hgLiftCont, hgLift, hgLift₀⟩

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
      formally_smooth_for_adic f 𝔫 := by
  constructor
  · intro hf
    rw [RingHom.formally_smooth_for_adic_iff]
    letI : TopologicalSpace R := ⊥
    letI : DiscreteTopology R := ⟨rfl⟩
    letI : TopologicalSpace S := Ideal.adicTopology 𝔫
    refine
      { toContinuous := continuous_of_discreteTopology
        lift_condition := ?_ }
    intro A _ _ _ J _ hJ g hg g0 hg0 hcomm
    letI : TopologicalSpace R := 𝔪.adicTopology
    letI : TopologicalSpace S := 𝔫.adicTopology
    have hgf : Continuous (g.comp f) := hg.comp hcont
    have hmadic : IsAdic 𝔪 := rfl
    rcases pow_le_ker_of_continuous_to_discrete_quotient 𝔪 hmadic (g.comp f) hgf with
      ⟨n, hn⟩
    have hkerComp : 𝔪 ^ n ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g0) := by
      simpa [hcomm] using hn
    have hmapJ : Ideal.map g0 (𝔪 ^ n) ≤ J := by
      refine Ideal.map_le_iff_le_comap.mpr ?_
      intro x hx
      have hxzero :
          Ideal.Quotient.mk J (g0 x) = 0 := RingHom.mem_ker.mp (hkerComp hx)
      simpa [Ideal.mem_comap] using (Ideal.Quotient.eq_zero_iff_mem.mp hxzero)
    have hmapBot : Ideal.map g0 (𝔪 ^ (n * 2)) ≤ ⊥ := by
      calc
        Ideal.map g0 (𝔪 ^ (n * 2)) = Ideal.map g0 ((𝔪 ^ n) ^ 2) := by
          rw [pow_mul]
        _ = Ideal.map g0 (𝔪 ^ n) ^ 2 := by
          rw [Ideal.map_pow]
        _ ≤ J ^ 2 := Ideal.pow_right_mono hmapJ 2
        _ = ⊥ := hJ
    have hkerG0 : 𝔪 ^ (n * 2) ≤ RingHom.ker g0 := by
      simpa [RingHom.ker_eq_comap_bot] using
        (Ideal.map_le_iff_le_comap.mp hmapBot : 𝔪 ^ (n * 2) ≤ Ideal.comap g0 ⊥)
    have hopen : IsOpen ((𝔪 ^ (n * 2) : Ideal R) : Set R) := by
      exact (isAdic_iff.mp hmadic).1 (n * 2)
    have hg0' : Continuous g0 :=
      continuous_of_open_ideal_le_ker g0 (𝔪 ^ (n * 2)) hopen hkerG0
    exact RingHom.FormallySmoothTopologically.exists_lift hf J hJ g hg g0 hg0' hcomm
  · intro hf
    have hf' :
        (letI : TopologicalSpace R := ⊥
         letI : TopologicalSpace S := Ideal.adicTopology 𝔫
         f.FormallySmoothTopologically) :=
      (RingHom.formally_smooth_for_adic_iff f 𝔫).mp hf
    letI : TopologicalSpace R := 𝔪.adicTopology
    letI : TopologicalSpace S := 𝔫.adicTopology
    refine
      { toContinuous := hcont
        lift_condition := ?_ }
    intro A _ _ _ J _ hJ g hg g0 hg0 hcomm
    letI : TopologicalSpace R := ⊥
    letI : DiscreteTopology R := ⟨rfl⟩
    letI : TopologicalSpace S := Ideal.adicTopology 𝔫
    exact
      RingHom.FormallySmoothTopologically.exists_lift
        hf' J hJ g hg g0 continuous_of_discreteTopology hcomm

end

end RingHom
