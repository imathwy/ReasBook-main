import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_43_6
import stacks_proof.stacks_project.Chap10.Lemma_10_44_2
import stacks_proof.stacks_project.Chap10.Lemma_10_138_9
import stacks_proof.stacks_project.Chap10.Lemma_10_140_9
import stacks_proof.stacks_project.Chap10.Lemma_10_158_2
import stacks_proof.stacks_project.Chap10.Lemma_10_158_6
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

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
@[stacks 0322]
theorem isSeparableOver_of_charZero [CharZero k] :
    Algebra.IsSeparableOver k K := by
  letI : PerfectField k := PerfectField.ofCharZero
  exact Algebra.IsSeparableOver.of_perfectField

-- Proof sketch: combine part (1) with the equivalence between separability and geometric
-- reducedness for field extensions in characteristic `p`, and use the characteristic-zero argument
-- that every finitely generated intermediate extension is separably generated.
/-- Proposition 10.158.9 (2): if the characteristic of `k` is zero, then `K` is geometrically
reduced over `k`. -/
@[stacks 0322]
theorem isGeometricallyReduced_of_charZero [CharZero k] :
    Algebra.IsGeometricallyReduced k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact _root_.isGeometricallyReduced_of_isSeparableOver

-- Proof sketch: every finitely generated intermediate extension of a characteristic-zero field is
-- separably generated, so the Stacks Project notion of separability holds; then Lemma `10.158.7`
-- upgrades separability to formal smoothness.
/-- Proposition 10.158.9 (3): if the characteristic of `k` is zero, then `K` is formally smooth
over `k`. -/
@[stacks 0322]
theorem formallySmooth_of_charZero [CharZero k] :
    Algebra.FormallySmooth k K := by
  letI : Algebra.IsSeparableOver k K := isSeparableOver_of_charZero
  exact Algebra.formallySmooth_of_isSeparableOver

-- Proof sketch: apply Proposition `10.158.9 (3)` together with Lemma `10.158.6`, which identifies
-- formal smoothness of a field extension with vanishing of the first cotangent homology module.
/-- Proposition 10.158.9 (4): if the characteristic of `k` is zero, then `H_1(L_{K/k}) = 0`.
In the canonical mathlib formulation, this is `Subsingleton (Algebra.H1Cotangent k K)`. -/
@[stacks 0322]
theorem subsingleton_h1Cotangent_of_charZero [CharZero k] :
    Subsingleton (Algebra.H1Cotangent k K) := by
  exact
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).1
      formallySmooth_of_charZero

-- Proof sketch: apply Proposition `10.158.9 (3)` and then use the split short exact sequence for
-- Kähler differentials of a formally smooth algebra map from Lemma `10.138.9` with base ring `ℤ`.
/-- Proposition 10.158.9 (5): if the characteristic of `k` is zero, then the canonical map
`K ⊗[k] Ω[k⁄ℤ] → Ω[K⁄ℤ]` is injective. -/
@[stacks 0322]
theorem kaehlerDifferential_mapBaseChange_int_injective_of_charZero [CharZero k] :
    Function.Injective (KaehlerDifferential.mapBaseChange ℤ k K) := by
  letI : Subsingleton (Algebra.H1Cotangent k K) := subsingleton_h1Cotangent_of_charZero
  -- Proof comment: Proposition `10.158.9 (4)` gives vanishing of `H₁(L_{K/k})`, and Jacobi-Zariski
  -- exactness converts that vanishing into injectivity of the base-change map over `ℤ`.
  exact
    kaehlerDifferentialMapBaseChange_injective_of_subsingletonH1
      (A := ℤ) (k := k) (K := K)

variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- Helper for Chap10 Proposition 10 158 9: over the prime field `ZMod p`, the connecting map
`H₁(L_{K/k}) → K ⊗[k] Ω[k⁄ZMod p]` is injective because `K / ZMod p` is separable and hence has
vanishing first cotangent homology. -/
private theorem h1CotangentDeltaInjectiveOverPrimeField :
    by
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : CharP K p :=
        CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
      letI : Algebra (ZMod p) K := ZMod.algebra K p
      letI : IsScalarTower (ZMod p) k K := by infer_instance
      exact Function.Injective (Algebra.H1Cotangent.δ (ZMod p) k K) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP K p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : IsScalarTower (ZMod p) k K := by infer_instance
  letI : PerfectField (ZMod p) := inferInstance
  letI : Algebra.IsSeparableOver (ZMod p) K := Algebra.IsSeparableOver.of_perfectField
  letI : Algebra.FormallySmooth (ZMod p) K := Algebra.formallySmooth_of_isSeparableOver
  have hsub :
      Subsingleton (Algebra.H1Cotangent (ZMod p) K) :=
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field
      (ZMod p) K).1 Algebra.formallySmooth_of_isSeparableOver
  intro x y hxy
  have hxy0 : Algebra.H1Cotangent.δ (ZMod p) k K (x - y) = 0 := by
    -- Proof comment: injectivity reduces to showing the difference lands in the zero fiber.
    rw [LinearMap.map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ :=
    (Algebra.H1Cotangent.exact_map_δ (ZMod p) k K (x - y)).1 hxy0
  have hz0 : z = 0 := Subsingleton.elim _ _
  have hsub_eq : x - y = 0 := by
    -- Proof comment: the exactness witness comes from a subsingleton source, so it vanishes.
    simpa [hz0] using hz.symm
  exact sub_eq_zero.mp hsub_eq

/-- Helper for Chap10 Proposition 10 158 9: injectivity of the canonical Kähler comparison over
`ZMod p` forces the first cotangent homology of `K / k` to vanish. -/
private theorem subsingletonH1CotangentOfKaehlerInjectiveCharP
    (hinj :
      by
        letI : Algebra (ZMod p) k := ZMod.algebra k p
        letI : CharP K p :=
          CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
        letI : Algebra (ZMod p) K := ZMod.algebra K p
        letI : IsScalarTower (ZMod p) k K := by infer_instance
        exact Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K)) :
    Subsingleton (Algebra.H1Cotangent k K) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP K p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : IsScalarTower (ZMod p) k K := by infer_instance
  have hδ_exact :
      Function.Exact
        (Algebra.H1Cotangent.δ (ZMod p) k K)
        (KaehlerDifferential.mapBaseChange (ZMod p) k K) :=
    Algebra.H1Cotangent.exact_δ_mapBaseChange (ZMod p) k K
  have hδ_range :
      LinearMap.range (Algebra.H1Cotangent.δ (ZMod p) k K) = ⊥ := by
    -- Proof comment: exactness identifies the range of `δ` with the kernel of the injective
    -- differential comparison map.
    rw [← hδ_exact.linearMap_ker_eq]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hδ_zero : Algebra.H1Cotangent.δ (ZMod p) k K = 0 := by
    -- Proof comment: a linear map with zero range is the zero map.
    ext x
    have hx :
        Algebra.H1Cotangent.δ (ZMod p) k K x ∈
          LinearMap.range (Algebra.H1Cotangent.δ (ZMod p) k K) := ⟨x, rfl⟩
    rw [hδ_range] at hx
    simpa using hx
  have hδ_injective :
      Function.Injective (Algebra.H1Cotangent.δ (ZMod p) k K) :=
    h1CotangentDeltaInjectiveOverPrimeField (k := k) (K := K) (p := p)
  refine ⟨fun x y ↦ ?_⟩
  -- Proof comment: once `δ = 0`, injectivity of `δ` forces every two elements to agree.
  exact hδ_injective (by simpa [hδ_zero])

omit [CharP k p] in
/-- Helper for Chap10 Proposition 10 158 9: separability in characteristic `p` gives injectivity
of the Jacobi-Zariski base-change map on Kähler differentials over `ZMod p`. -/
private theorem kaehlerDifferentialMapBaseChange_injective_of_isSeparableOver_charP
    [CharP K p] [Algebra (ZMod p) k] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) k K]
    [Algebra.IsSeparableOver k K] :
    Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K) := by
  letI : Algebra.FormallySmooth k K := Algebra.formallySmooth_of_isSeparableOver
  letI : Subsingleton (Algebra.H1Cotangent k K) :=
    (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).1 inferInstance
  -- Proof comment: separability gives formal smoothness, formal smoothness kills `H₁`, and
  -- Jacobi-Zariski exactness turns that vanishing into injectivity of the comparison map.
  exact
    kaehlerDifferentialMapBaseChange_injective_of_subsingletonH1
      (A := ZMod p) (k := k) (K := K)

/-- Helper for Chap10 Proposition 10 158 9: formal smoothness of a field extension gives
Stacks-project separability. -/
private theorem isSeparableOverOfFormallySmoothCharP
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.FormallySmooth k K] :
    Algebra.IsSeparableOver k K := by
  -- Proof comment: reuse the earlier field-extension bridge instead of duplicating the
  -- characteristic-`p` Frobenius-minimal-support argument in this proposition.
  exact
    isSeparableOver_of_formallySmooth_fieldExtension
      (k := k) (K := K) (inferInstance : Algebra.FormallySmooth k K)

-- Proof sketch: clauses `(1)`, `(2)`, and `(3)` come from Lemma `10.44.2`; clause `(6)` is the
-- formal-smoothness owner bridge from Lemma `10.158.7`; clause `(5)` is the field-level
-- cotangent-homology reformulation from Lemma `10.158.6`; and clause `(4)` is the
-- Kähler-differential injectivity clause singled out by the owner theorem below, whose
-- `(1) ↔ (4)` and `(6) → (1)` projections are recorded downstream in Lemmas `10.158.4` and
-- `10.158.5`.
/-- Chap10 Proposition 10 158 9 (6): if the characteristic of `k` is `p > 0`, then the following are
equivalent for the field extension `K / k`: `K` is separable over `k`, `K ⊗[k] k^{1/p}` is
reduced, `K` is geometrically reduced over `k`, the canonical map
`K ⊗[k] Ω[k⁄ZMod p] → Ω[K⁄ZMod p]` is injective, `H_1(L_{K/k}) = 0`, and `K` is formally smooth
over `k`. The chosen model of `k^{1/p}` is `onePthRootExtension k p`, and the vanishing of
`H_1(L_{K/k})` is expressed as `Subsingleton (Algebra.H1Cotangent k K)`. -/
@[stacks 0322]
theorem char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth
    {p : ℕ} [Fact p.Prime] [CharP k p] :
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
        ] := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP K p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
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
  -- Proof comment: clauses `(1)`, `(2)`, and `(3)` are exactly Lemma `10.44.2`.
  tfae_have 1 ↔ 2 := by
    simpa [l] using
      (isSeparableOver_iff_isReduced_tensorProduct_onePthRootExtension
        (k := k) (K := K) (p := p))
  tfae_have 1 ↔ 3 := by
    simpa [l] using
      (isSeparableOver_iff_isGeometricallyReduced_of_charP
        (k := k) (K := K) p)
  -- Proof comment: separability gives formal smoothness, hence injectivity of the Kähler
  -- comparison map over the prime field.
  tfae_have 1 → 4 := by
    intro hsep
    letI : Algebra.IsSeparableOver k K := hsep
    simpa [l] using
      (kaehlerDifferentialMapBaseChange_injective_of_isSeparableOver_charP
        (k := k) (K := K) (p := p))
  -- Proof comment: exactness of the Jacobi-Zariski sequence converts this injectivity back into
  -- vanishing of `H₁(L_{K/k})`.
  tfae_have 4 → 5 := by
    intro hinj
    simpa [l] using
      (subsingletonH1CotangentOfKaehlerInjectiveCharP
        (k := k) (K := K) (p := p) hinj)
  -- Proof comment: Lemma `10.158.6` identifies vanishing of `H₁` with formal smoothness.
  tfae_have 5 ↔ 6 := by
    simpa [l] using
      (Algebra.formallySmooth_iff_subsingleton_h1Cotangent_of_field k K).symm
  -- Proof comment: the imported formal-smooth-to-separable bridge closes the final implication.
  tfae_have 6 → 1 := by
    intro hformal
    letI : Algebra.FormallySmooth k K := hformal
    simpa [l] using
      (isSeparableOverOfFormallySmoothCharP (k := k) (K := K) (p := p))
  tfae_finish

end

end Algebra
