import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- `lean_leansearch` was unavailable in this environment, so the canonical owner was checked
-- locally against mathlib's `ContMDiffSection` tangent-bundle API and nearby Chapter 8 files.

/- Notation 8.54-extra-3: the canonical bundled type of smooth vector fields on `M` is
`Cₛ^∞⟮I; E, TangentSpace I⟯`. It carries the pointwise `ℝ`-vector-space structure, and smooth
scalar multiplication by a smooth real-valued function is expressed by `ContMDiff.smul_section`
on the underlying section `Π p : M, TangentSpace I p`. -/
#check (Cₛ^∞⟮I; E, TangentSpace I⟯ : Type _)

#check (inferInstance : Module ℝ Cₛ^∞⟮I; E, TangentSpace I⟯)

#check fun (f : C^∞⟮I, M; ℝ⟯) {X : Π p : M, TangentSpace I p}
    (hX : ContMDiff I I.tangent ∞ (T% X)) ↦
  f.contMDiff.smul_section hX

end
