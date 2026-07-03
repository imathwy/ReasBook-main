import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Proposition_10_158_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.5:
- primary domain: field extensions, formal smoothness, and the Stacks-project separability owner
  `Algebra.IsSeparableOver`;
- sampled owner declarations:
  `Algebra.IsSeparableOver`,
  `PerfectField.ofCharZero`,
  `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`,
  `List.TFAE.out`;
- best owner abstraction: the source-facing owner `Algebra.IsSeparableOver k K`, with the
  characteristic-zero perfect-field instance and the characteristic-`p` owner TFAE supplying the
  two canonical bridges;
- primitive data: the field extension `K / k` together with `[Algebra.FormallySmooth k K]`;
- derived API: the characteristic split and the positive-characteristic reduction through
  the six-way field-extension TFAE.

Source/core/bridge triage:
- `source-facing`: the implication from formal smoothness to Stacks-project separability;
- `core/canonical`: `Algebra.FormallySmooth k K` and `Algebra.IsSeparableOver k K`;
- `bridge/view`: `PerfectField.ofCharZero` in characteristic zero, and the characteristic-`p`
  projection from Proposition `10.158.9`.
-/
-- Proof sketch: split on the characteristic of `k`. In characteristic zero, `k` is perfect, so
-- the owner instance `Algebra.IsSeparableOver.of_perfectField` applies directly. In
-- characteristic `p > 0`, Proposition `10.158.9` already packages the equivalence among
-- separability, reducedness criteria, Kähler-differential injectivity, vanishing of
-- `H₁(L_{K/k})`, and formal smoothness. Project the implication from formal smoothness to
-- `Algebra.IsSeparableOver k K` from that owner theorem.
/-- Lemma 10.158.5: a formally smooth field extension is separable in the Stacks Project sense. -/
theorem isSeparableOver_of_formallySmooth [Algebra.FormallySmooth k K] :
    Algebra.IsSeparableOver k K := by
  rcases CharP.exists' k with hchar0 | ⟨p, hp, hcharp⟩
  · letI : CharZero k := hchar0
    letI : PerfectField k := PerfectField.ofCharZero
    infer_instance
  · letI : Fact p.Prime := hp
    letI : CharP k p := hcharp
    letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : IsScalarTower (ZMod p) k K := by infer_instance
    let l : List Prop := [
      Algebra.IsSeparableOver k K,
      IsReduced (K ⊗[k] onePthRootExtension k p),
      Algebra.IsGeometricallyReduced k K,
      Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
      Subsingleton (Algebra.H1Cotangent k K),
      Algebra.FormallySmooth k K
    ]
    have htfae : List.TFAE l := by
      simpa [l] using
        Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth
    simpa [l] using
      (htfae.out 0 5 (by simp [l]) (by simp [l])).2 (show Algebra.FormallySmooth k K from inferInstance)

end

end Algebra
