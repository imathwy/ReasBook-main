import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.IsLocalHomeomorph
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_04.Example_1_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

universe u

variable {n : ℕ}

namespace Projectivization

section BasisEquiv

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type u} [AddCommGroup V] [Module 𝕜 V]

/-- The linear equivalence sending the standard coordinates on `𝕜^(n+1)` to the basis `b` of
`V`. -/
abbrev basisLinearEquiv (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    EuclideanSpace 𝕜 (Fin (n + 1)) ≃ₗ[𝕜] V :=
  (EuclideanSpace.equiv (Fin (n + 1)) 𝕜).toLinearEquiv.trans b.equivFun.symm

/-- The map on projectivizations induced by the basis `b`. -/
def basisMap (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) → ℙ 𝕜 V :=
  Projectivization.map (basisLinearEquiv b).toLinearMap (basisLinearEquiv b).injective

/-- The inverse projectivization map induced by the inverse basis equivalence. -/
private def basisMapSymm (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 V → ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) :=
  Projectivization.map (basisLinearEquiv b).symm.toLinearMap (basisLinearEquiv b).symm.injective

/-- The basis-induced equivalence between the standard projective space and `ℙ 𝕜 V`. -/
private def basisEquiv (b : Module.Basis (Fin (n + 1)) 𝕜 V) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ ℙ 𝕜 V :=
  { toFun := basisMap b
    invFun := basisMapSymm b
    left_inv := fun x ↦ by
      let e := basisLinearEquiv b
      have hcomp :
          basisMapSymm b (basisMap b x) =
            Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective x := by
        simpa [basisMap, basisMapSymm, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.toLinearMap e.injective e.symm.toLinearMap e.symm.injective).symm
      have hid :
          Projectivization.map (e.trans e.symm).toLinearMap (e.trans e.symm).injective = id := by
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.self_trans_symm]
      calc
        basisMapSymm b (basisMap b x)
            = Projectivization.map
                (e.trans e.symm).toLinearMap
                (e.trans e.symm).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid
    right_inv := fun x ↦ by
      let e := basisLinearEquiv b
      have hcomp :
          basisMap b (basisMapSymm b x) =
            Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective x := by
        simpa [basisMap, basisMapSymm, Function.comp, e] using
          congrArg (fun f ↦ f x) <|
            (Projectivization.map_comp
              e.symm.toLinearMap e.symm.injective e.toLinearMap e.injective).symm
      have hid :
          Projectivization.map (e.symm.trans e).toLinearMap (e.symm.trans e).injective = id := by
        ext y
        induction y using ind with
        | h v hv =>
            simp [Projectivization.map_mk, LinearEquiv.symm_trans_self]
      calc
        basisMap b (basisMapSymm b x)
            = Projectivization.map
                (e.symm.trans e).toLinearMap
                (e.symm.trans e).injective x := hcomp
        _ = x := by
          simpa using congrArg (fun f ↦ f x) hid }

/-- The canonical bundled diffeomorphism attached to a basis once the forward and inverse
projectivization maps are known to be smooth. -/
private def basisDiffeomorph
    [TopologicalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω)
      (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [TopologicalSpace (ℙ 𝕜 V)]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V)]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V)]
    (b : Module.Basis (Fin (n + 1)) 𝕜 V)
    (h_to : ContMDiff (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)))
      (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) ∞ (basisMap b))
    (h_inv : ContMDiff (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)))
      (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) ∞ (basisMapSymm b)) :
    ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ₘ⟮𝓘(ℝ, EuclideanSpace 𝕜 (Fin n)),
      𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))⟯ ℙ 𝕜 V where
  toEquiv := basisEquiv b
  contMDiff_toFun := h_to
  contMDiff_invFun := h_inv

end BasisEquiv

section Real

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

private abbrev topologicalSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    TopologicalSpace (ℙ ℝ V) :=
  (basisEquiv b).symm.topologicalSpace

/-- Transport a standard chart on `ℝP[n]` across the basis homeomorphism. -/
private def chartOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V)
    (e : OpenPartialHomeomorph ℝP[n] (EuclideanSpace ℝ (Fin n))) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    OpenPartialHomeomorph (ℙ ℝ V) (EuclideanSpace ℝ (Fin n)) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  ((basisEquiv b).symm.homeomorph).toOpenPartialHomeomorph.trans e

private abbrev chartedSpaceOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
  (ChartedSpace.mk
    {e | ∃ e' ∈ atlas (EuclideanSpace ℝ (Fin n)) (ℝP[n]), e = chartOfBasis b e'}
    (fun x ↦ chartOfBasis b (chartAt (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x)))
    (by
      intro x
      dsimp [chartOfBasis]
      refine ⟨by simp, ?_⟩
      change (basisEquiv b).symm x ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x)).source
      exact mem_chart_source (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x))
    (by
      intro x
      refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x), ?_, rfl⟩
      exact chart_mem_atlas (EuclideanSpace ℝ (Fin n)) ((basisEquiv b).symm x)) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V))

private theorem isManifoldOfBasis (b : Module.Basis (Fin (n + 1)) ℝ V) :
    let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b
    let _ : @ChartedSpace (EuclideanSpace ℝ (Fin n)) _ (ℙ ℝ V) (topologicalSpaceOfBasis b) :=
      chartedSpaceOfBasis b
    IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := by
  sorry

end Real

end Projectivization

namespace Projectivization

/-- A smooth structure on `ℙ 𝕜 V` is basis-compatible if every basis-induced map from the
standard projective space `ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))` extends to the canonical
basis-induced diffeomorphism for that ambient manifold structure, and if `V` actually admits
an `(n + 1)`-indexed basis. This is the source-facing basis-independence condition used for the
real and complex projectivization problems in this section. -/
def BasisCompatible (n : ℕ) {𝕜 : Type*} [RCLike 𝕜] (V : Type u) [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    [IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω)
      (ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))))]
    (t : TopologicalSpace (ℙ 𝕜 V))
    (c : let _ : TopologicalSpace (ℙ 𝕜 V) := t
      ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V))
    (m : let _ : TopologicalSpace (ℙ 𝕜 V) := t
      let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V) := c
      IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V)) : Prop :=
  let _ : TopologicalSpace (ℙ 𝕜 V) := t
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin n)) (ℙ 𝕜 V) := c
  let _ : IsManifold (𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))) (⊤ : ℕ∞ω) (ℙ 𝕜 V) := m
  let I := 𝓘(ℝ, EuclideanSpace 𝕜 (Fin n))
  ∃ _ : Module.Basis (Fin (n + 1)) 𝕜 V,
    ∀ b : Module.Basis (Fin (n + 1)) 𝕜 V,
      ∃ Φ : ℙ 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) ≃ₘ⟮I, I⟯ ℙ 𝕜 V,
        ∀ x, Φ x = basisMap b x

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

private theorem basisCompatible_ofBasis (b₀ : Module.Basis (Fin (n + 1)) ℝ V) :
    BasisCompatible n V (topologicalSpaceOfBasis b₀) (chartedSpaceOfBasis b₀)
      (isManifoldOfBasis b₀) := by
  let _ : TopologicalSpace (ℙ ℝ V) := topologicalSpaceOfBasis b₀
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := chartedSpaceOfBasis b₀
  let _ : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := isManifoldOfBasis b₀
  refine ⟨b₀, ?_⟩
  intro b
  have h_to : ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMap b) := by
    sorry
  have h_inv : ContMDiff (𝓡 n) (𝓡 n) ∞ (basisMapSymm b) := by
    sorry
  refine ⟨basisDiffeomorph b h_to h_inv, ?_⟩
  intro x
  rfl

end Projectivization

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- Problem 2-11: if `V` is a real vector space of dimension `n + 1`, then `ℙ ℝ V` carries a
basis-compatible smooth structure modeled on `ℝ^n`; any basis-induced map `ℝP[n] → ℙ ℝ V` is a
diffeomorphism. The public owner is the ambient topological, charted, and manifold structure on
`ℙ ℝ V`; the chosen-basis transport used to construct those instances remains internal. -/
theorem real_projectivization_exists_basisCompatible_smoothStructure
    (hn : Module.finrank ℝ V = n + 1) :
    ∃ t : TopologicalSpace (ℙ ℝ V),
      ∃ c : let _ : TopologicalSpace (ℙ ℝ V) := t
        ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V),
      ∃ m : let _ : TopologicalSpace (ℙ ℝ V) := t
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := c
          IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V),
          Projectivization.BasisCompatible n V t c m := by
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hn
  let b := Module.finBasisOfFinrankEq ℝ V hn
  let t : TopologicalSpace (ℙ ℝ V) := Projectivization.topologicalSpaceOfBasis b
  let c : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) :=
    Projectivization.chartedSpaceOfBasis b
  let m : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := Projectivization.isManifoldOfBasis b
  refine ⟨t, c, m, ?_⟩
  letI : TopologicalSpace (ℙ ℝ V) := t
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ℙ ℝ V) := c
  letI : IsManifold (𝓡 n) (⊤ : ℕ∞ω) (ℙ ℝ V) := m
  simpa [b, t, c, m] using Projectivization.basisCompatible_ofBasis b
