import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap10.Lemma_10_136_4
import StacksProject_2024.Chap10.Lemma_10_168_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain-style sampling:
* primary domain: descent of relative global complete intersections and syntomic morphisms along
  directed ring colimits via tensor-product base change;
* sampled owner declarations of the same kind:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.IsRelativeGlobalCompleteIntersection.syntomic`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`;
* best owner abstraction:
  `source-facing`: the direct-limit descent theorems below;
  `core/canonical`: `Algebra.IsRelativeGlobalCompleteIntersection` for the base-changed codomain
    over the base-changed source, together with `RingHom.Syntomic` for the map-level conclusion;
  `bridge/view`: the tensor-product base-change maps `Algebra.TensorProduct.map φ₀ (...)`.
* primitive vs. derived:
  primitive data are the directed system, the distinguished stage `i₀`, and the stagewise/direct-
  limit tensor-product base-change maps;
  derived API is any map-based reformulation of relative global complete intersection via the
  induced algebra structure on such a map, so it should not remain as a parallel public owner.
-/
variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ C₀ : Type w} [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

-- Proof sketch: view the colimit base change of `φ0` as a map over the direct limit ring and use
-- a finite-type witness `R → S'` for the relative global complete intersection from Lemma
-- `10.136.11`. Finite presentation of `φ0` descends the structural map to some stage by Lemma
-- `10.127.3`, Lemma `10.168.6` upgrades the descended comparison map to an isomorphism, and Lemma
-- `10.136.9` then transports the relative global complete intersection structure to that stage.
/-- Lemma 10.168.9 (1): if the base change of `φ₀ : B₀ → C₀` to the direct limit ring is a
relative global complete intersection and `C₀` is finitely presented over `B₀`, then after
passing to some later stage the corresponding stagewise base change is already a relative global
complete intersection. -/
theorem exists_relativeGlobalCompleteIntersection_stage_base_change_of_direct_limit_base_change
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hGCI :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A∞) (C₀ ⊗[A i₀] A∞)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A i) (C₀ ⊗[A i₀] A i) := sorry

-- Proof sketch: choose finitely many elements generating the unit ideal on the colimit base
-- change so that each basic localization is a relative global complete intersection by Lemma
-- `10.136.15`. Descend those finitely many generators to one stage, enlarge so they still
-- generate the unit ideal there, apply the previous clause to each localization, and conclude by
-- the locality criterion for syntomic maps from Lemma `10.136.4`.
/-- Lemma 10.168.9 (2): if the base change of `φ₀ : B₀ → C₀` to the direct limit ring is syntomic
and `C₀` is finitely presented over `B₀`, then after passing to some later stage the corresponding
stagewise base change is already syntomic. -/
theorem exists_syntomic_stage_base_change_of_direct_limit_base_change
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsyntomic :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.Syntomic) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toRingHom.Syntomic := sorry

end
