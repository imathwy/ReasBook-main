import SmoothManifolds_Lee_2012.Chap02.Sec02_08.Notation_2_8_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/- Exercise 2.1: building on the bundled smooth-function space recalled in
`Notation_2_8_extra_3`, the canonical mathlib ring structure makes the smooth real-valued
functions on a smooth manifold into a commutative ring under pointwise multiplication. -/
#check (inferInstance : CommRing C^∞⟮I, M; ℝ⟯)

/- Exercise 2.1, pointwise multiplication: this is the canonical owner theorem
`ContMDiffMap.coe_mul`, specialized to smooth real-valued functions on `M`. -/
#check (ContMDiffMap.coe_mul : ∀ f g : C^∞⟮I, M; ℝ⟯, ⇑(f * g) = f * g)

/- The same space of smooth real-valued functions carries its canonical `ℝ`-algebra structure. -/
#check (inferInstance : Algebra ℝ C^∞⟮I, M; ℝ⟯)

/- Exercise 2.1, scalar multiplication: this is the canonical owner theorem
`ContMDiffMap.coe_smul`, specialized to the canonical `ℝ`-algebra structure on
`C^∞⟮I, M; ℝ⟯`. -/
#check (ContMDiffMap.coe_smul : ∀ r : ℝ, ∀ f : C^∞⟮I, M; ℝ⟯, ⇑(r • f) = r • ⇑f)
