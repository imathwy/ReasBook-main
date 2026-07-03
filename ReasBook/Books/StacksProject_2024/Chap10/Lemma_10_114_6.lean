import Mathlib
import StacksProject_2024.Chap10.Lemma_10_114_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for closed-point local dimension in affine schemes of finite type over a
field:
- primary domain: local Krull dimension on `Spec(S)` in the finite-type-over-a-field setting of
  Lemmas `10.114.5` and `10.114.6`;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`,
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `Ideal.IsMaximal.eq_of_le`;
- best owner abstraction: the source-facing owner remains `topologicalKrullDimAt`, and the closed
  point formula is a thin specialization of the chapter owner theorem
  `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`;
- primitive data: the finite type `k`-algebra `S` and the closed point `m : MaximalSpectrum S`;
- derived API: the equality between `topologicalKrullDimAt m.toPrimeSpectrum` and the Krull
  dimension of the canonical local ring `Localization.AtPrime m.asIdeal`.

Source/core/bridge triage:
* `source-facing`: Lemma 10.114.6 for a closed point of `Spec(S)` with `S` finite type over a
  field;
* `core/canonical`: `topologicalKrullDimAt`, `MaximalSpectrum S`, `Localization.AtPrime`, and the
  owner theorem `topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over`;
* `bridge/view`: collapsing the infimum over maximal ideals containing `m.asIdeal` to the unique
  maximal ideal `m`.
-/

-- Proof sketch: apply Lemma `10.114.5 (2)` to the closed point `m.toPrimeSpectrum`. The indexing
-- subtype of maximal ideals containing `m.asIdeal` is a singleton, because any maximal ideal above
-- `m.asIdeal` equals `m` by maximality. The resulting infimum therefore evaluates at `m`.
/-- Lemma 10.114.6: if `S` is a finite type `k`-algebra and `m` is a maximal ideal of `S`, then
the local Krull dimension of `X = Spec(S)` at the closed point corresponding to `m` equals the
Krull dimension of the local ring `Sₘ`, formalized as `Localization.AtPrime m.asIdeal`. -/
  theorem topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal
    (m : MaximalSpectrum S) :
    topologicalKrullDimAt m.toPrimeSpectrum =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  rw [topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over m.toPrimeSpectrum]
  letI : Subsingleton {n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal} := by
    refine ⟨fun a b ↦ Subtype.ext <| MaximalSpectrum.ext <| ?_⟩
    have ha : m.asIdeal = a.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal a.1.isMaximal.ne_top a.2
    have hb : m.asIdeal = b.1.asIdeal :=
      Ideal.IsMaximal.eq_of_le m.isMaximal b.1.isMaximal.ne_top b.2
    exact ha.symm.trans hb
  let e : {n : MaximalSpectrum S // m.asIdeal ≤ n.asIdeal} := ⟨m, le_rfl⟩
  simpa [e] using
    (ciInf_subsingleton e fun n ↦ ringKrullDim (Localization.AtPrime n.1.asIdeal))

end
