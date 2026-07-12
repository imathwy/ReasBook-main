import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Data.PNat.Notation
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import StacksProject_2024.Chap15.Definition_15_36_1_Topological_rings
import StacksProject_2024.Chap15.Definition_15_37_1
import StacksProject_2024.Chap15.Lemma_15_36_2

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 07NI]
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
