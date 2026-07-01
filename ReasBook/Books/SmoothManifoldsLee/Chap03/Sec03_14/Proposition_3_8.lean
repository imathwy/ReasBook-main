import Mathlib.Geometry.Manifold.BumpFunction
import SmoothManifoldsLee.Chap03.Sec03_13.Lemma_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [T2Space M]

namespace PointDerivation

/-- Proposition 3.8: on a smooth real manifold modeled on a finite-dimensional vector space, if
smooth real-valued functions `f` and `g` agree on an open neighborhood of `p`, then every point
derivation at `p` assigns them the same value. -/
theorem congr_of_eqOn_nhds {p : M} (v : PointDerivation I p) (f g : C^∞⟮I, M; ℝ⟯) (U : Set M)
    (hU : IsOpen U) (hpU : p ∈ U) (hfg : Set.EqOn f g U) :
    v f = v g := by
  -- Rewrite the target in terms of the difference function that vanishes on `U`.
  let h : C^∞⟮I, M; ℝ⟯ := f - g
  have hU_mem : U ∈ nhds p := hU.mem_nhds hpU
  have hbasis :
      (nhds p).HasBasis (fun b : SmoothBumpFunction I p ↦ tsupport b ⊆ U)
        fun b ↦ Function.support b :=
    SmoothBumpFunction.nhds_basis_support hU_mem
  obtain ⟨b, _, hsupport⟩ :=
    hbasis.mem_iff.mp hU_mem
  let φ : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  -- The difference vanishes at `p` because `f` and `g` agree on the chosen neighborhood.
  have hp : h p = 0 := by
    simpa [h, sub_eq_zero] using hfg hpU
  have hφp : φ p = 1 := by
    simp [φ]
  -- Replace `h` by a product whose two factors both vanish at `p`.
  have hfactor : h = (1 - φ) * h := by
    ext x
    by_cases hx : x ∈ Function.support b
    · have hhx : h x = 0 := by
        simpa [h, sub_eq_zero] using hfg (hsupport hx)
      simp [φ, hhx]
    · have hbx : b x = 0 := Function.notMem_support.mp hx
      simp [φ, hbx]
  -- Lemma 3.4 kills this product because both factors vanish at the base point.
  have hOneSubφp : (1 - φ) p = 0 := by
    simp [hφp]
  have hvh : v h = 0 := by
    rw [hfactor]
    exact tangent_vector_mul_eq_zero_of_vanish_at v (1 - φ) h hOneSubφp hp
  -- Translate the vanishing of the difference back to the desired equality.
  have hvsub : v f - v g = 0 := by
    simpa [h] using (v.map_sub f g).symm.trans hvh
  exact sub_eq_zero.mp hvsub

end PointDerivation
