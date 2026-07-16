import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_13.Definition_3_13_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

-- Proof sketch: regard a constant smooth function as a scalar multiple of `1`, use
-- `Derivation.map_one_eq_zero`, and transport the scalar action to evaluation at the base point.
/-- Lemma 3.4 (1): if a smooth real-valued function on `M` is constant, then every tangent vector
at `p`, viewed as a point derivation, annihilates it. -/
theorem tangent_vector_apply_const {p : M} (v : PointDerivation I p) (c : ℝ) :
    v (ContMDiffMap.const c) = 0 := by
  change v ((algebraMap ℝ C^∞⟮I, M; ℝ⟯) c) = 0
  exact v.map_algebraMap c

-- Proof sketch: apply the canonical derivation Leibniz rule to `f * g`, rewrite the scalar
-- actions with `PointedContMDiffMap.smul_def`, and use that `f p = 0` and `g p = 0`.
/-- Lemma 3.4 (2): if smooth functions `f` and `g` both vanish at `p`, then every tangent vector
at `p`, viewed as a point derivation, annihilates their product. -/
theorem tangent_vector_mul_eq_zero_of_vanish_at {p : M} (v : PointDerivation I p)
    (f g : C^∞⟮I, M; ℝ⟯) (hf : f p = 0) (hg : g p = 0) :
    v (f * g) = 0 := by
  have hleib : v (f * g) = f p * v g + g p * v f := by
    simpa only [PointedContMDiffMap.smul_def] using v.leibniz f g
  rw [hleib]
  simp [hf, hg]
