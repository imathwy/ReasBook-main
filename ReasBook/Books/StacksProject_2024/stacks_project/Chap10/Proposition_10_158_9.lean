import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_43_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_44_2
import StacksProject_2024.stacks_project.Chap10.Lemma_10_138_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_158_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Proposition 10.158.9:
- primary domain: field extensions over a base field, with the source-facing properties
  separability in the Stacks Project sense, geometric reducedness, formal smoothness, vanishing of
  `H¹(L_)`, and injectivity of the Jacobi-Zariski base-change map on Kähler differentials;
- sampled owner declarations:
  `Algebra.IsSeparableOver.of_perfectField`,
  `_root_.isGeometricallyReduced_of_isSeparableOver`,
  `Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field`,
  `kaehlerDifferential_transitivity_sequence_splits_of_formallySmooth`;
- best owner abstraction: the existing owner predicates
  `Algebra.IsSeparableOver k K`, `Algebra.IsGeometricallyReduced k K`,
  `Algebra.FormallySmooth k K`, and the owner maps on `Algebra.H1Cotangent` and
  `KaehlerDifferential`;
- primitive data: only the field extension `K / k` and the characteristic assumptions;
- derived API: the characteristic-zero specializations and the characteristic-`p` six-way TFAE.

Source/core/bridge triage:
- `source-facing`: the numbered proposition parts, especially the characteristic-`p` TFAE;
- `core/canonical`: the owner predicates above and the canonical Jacobi-Zariski maps;
- `bridge/view`: perfect-field reduction in characteristic zero, geometric reducedness from
  Stacks-separability, the field-level `FormallySmooth ↔ Subsingleton H1Cotangent` bridge, and the
  split transitivity sequence for Kähler differentials.
-/

-- Proof sketch: in characteristic zero every finitely generated intermediate extension is
-- separably generated, since after choosing a transcendence basis the remaining algebraic part is
-- automatically separable. This is exactly the Stacks Project notion `Algebra.IsSeparableOver`.
/-- Proposition 10.158.9 (1): if the characteristic of `k` is zero, then the field extension
`K / k` is separable in the Stacks Project sense. -/
theorem isSeparableOver_of_charZero [CharZero k] :
    Algebra.IsSeparableOver k K := by
  letI : PerfectField k := PerfectField.ofCharZero
  exact Algebra.IsSeparableOver.of_perfectField

-- Proof sketch: combine part (1) with the equivalence between separability and geometric
-- reducedness for field extensions in characteristic `p`, and use the characteristic-zero argument
-- that every finitely generated intermediate extension is separably generated.
/-- Proposition 10.158.9 (2): if the characteristic of `k` is zero, then `K` is geometrically
reduced over `k`. -/
theorem isGeometricallyReduced_of_charZero [CharZero k] :
    Algebra.IsGeometricallyReduced k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact _root_.isGeometricallyReduced_of_isSeparableOver

-- Proof sketch: every finitely generated intermediate extension of a characteristic-zero field is
-- separably generated, so the Stacks Project notion of separability holds; then Lemma `10.158.7`
-- upgrades separability to formal smoothness.
/-- Proposition 10.158.9 (3): if the characteristic of `k` is zero, then `K` is formally smooth
over `k`. -/
theorem formallySmooth_of_charZero [CharZero k] :
    Algebra.FormallySmooth k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact Algebra.formallySmooth_of_isSeparableOver

-- Proof sketch: apply Proposition `10.158.9 (3)` together with Lemma `10.158.6`, which identifies
-- formal smoothness of a field extension with vanishing of the first cotangent homology module.
/-- Proposition 10.158.9 (4): if the characteristic of `k` is zero, then `H_1(L_{K/k}) = 0`.
In the canonical mathlib formulation, this is `Subsingleton (Algebra.H1Cotangent k K)`. -/
theorem subsingleton_h1Cotangent_of_charZero [CharZero k] :
    Subsingleton (Algebra.H1Cotangent k K) := by
  exact
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).1
      formallySmooth_of_charZero

-- Proof sketch: apply Proposition `10.158.9 (3)` and then use the split short exact sequence for
-- Kähler differentials of a formally smooth algebra map from Lemma `10.138.9` with base ring `ℤ`.
/-- Proposition 10.158.9 (5): if the characteristic of `k` is zero, then the canonical map
`K ⊗[k] Ω[k⁄ℤ] → Ω[K⁄ℤ]` is injective. -/
theorem kaehlerDifferential_mapBaseChange_int_injective_of_charZero [CharZero k] :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) := sorry

variable {p : ℕ} [Fact p.Prime] [CharP k p]

-- Proof sketch: clauses `(1)`, `(2)`, and `(3)` come from Lemma `10.44.2`; clause `(6)` is the
-- formal-smoothness owner bridge from Lemma `10.158.7`; clause `(5)` is the field-level
-- cotangent-homology reformulation from Lemma `10.158.6`; and clause `(4)` is the
-- Kähler-differential injectivity clause singled out by the owner theorem below, whose
-- `(1) ↔ (4)` and `(6) → (1)` projections are recorded downstream in Lemmas `10.158.4` and
-- `10.158.5`.
/-- Proposition 10.158.9 (6): if the characteristic of `k` is `p > 0`, then the following are
equivalent for the field extension `K / k`: `K` is separable over `k`, `K ⊗[k] k^{1/p}` is
reduced, `K` is geometrically reduced over `k`, the canonical map
`K ⊗[k] Ω[k⁄ZMod p] → Ω[K⁄ZMod p]` is injective, `H_1(L_{K/k}) = 0`, and `K` is formally smooth
over `k`. The chosen model of `k^{1/p}` is `onePthRootExtension k p`, and the vanishing of
`H_1(L_{K/k})` is expressed as `Subsingleton (Algebra.H1Cotangent k K)`. -/
theorem char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth :
    by
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
      letI : Algebra (ZMod p) K := ZMod.algebra K p
      letI : IsScalarTower (ZMod p) k K := by infer_instance
      exact
        List.TFAE [
          Algebra.IsSeparableOver k K,
          IsReduced (K ⊗[k] onePthRootExtension k p),
          Algebra.IsGeometricallyReduced k K,
          Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
          Subsingleton (Algebra.H1Cotangent k K),
          Algebra.FormallySmooth k K
        ] := sorry

end

end Algebra
