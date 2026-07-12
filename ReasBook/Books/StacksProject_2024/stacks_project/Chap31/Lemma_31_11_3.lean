import StacksProject_2024.Chap31.Definition_31_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

-- Semantic recall: the canonical ring-level owner is `Module.IsTorsionFree`. The Chapter 31
-- scheme-level owner remains the source-facing Definition 31.11.2 predicate, and this lemma is
-- the quasi-coherent affine-open bridge promised by the Stacks statement.

/-- Lemma 31.11.3: let `X` be an integral scheme and let `ℱ` be a quasi-coherent
`\mathcal O_X`-module. Then `ℱ` is torsion free if and only if, for every affine open
`U ⊆ X`, the module of sections `Γ(U, ℱ)` is torsion free over `Γ(U, \mathcal O_X)`. -/
theorem isTorsionFree_iff_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- Affine-open sections of a torsion-free quasi-coherent `\mathcal O_X`-module on an integral
scheme are torsion free over the corresponding ring of functions. -/
theorem IsTorsionFree.torsionFree_sections
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] (hℱ : IsTorsionFree ℱ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) :=
  (isTorsionFree_iff_affineOpen ℱ).1 hℱ U hU

/-- The affine-open form of Lemma 31.11.3, packaged using `X.affineOpens`. -/
theorem isTorsionFree_iff_affineOpens
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ U : X.affineOpens, Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  constructor
  · intro hℱ U
    exact hℱ.torsionFree_sections U.1 U.2
  · intro hℱ
    exact (isTorsionFree_iff_affineOpen ℱ).2 fun U hU ↦ by
      simpa using hℱ ⟨U, hU⟩

/-- Affine sections of a torsion-free quasi-coherent `\mathcal O_X`-module on an integral scheme
are torsion free over the corresponding ring of functions, packaged as an element of
`X.affineOpens`. -/
theorem IsTorsionFree.torsionFree_sections_affineOpen
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] (hℱ : IsTorsionFree ℱ) (U : X.affineOpens) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  simpa using hℱ.torsionFree_sections U.1 U.2

/-- Companion bridge: if every affine-open section module of a quasi-coherent
`\mathcal O_X`-module on an integral scheme is torsion free, then the module is torsion free. -/
theorem isTorsionFree_of_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U))) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_affineOpen ℱ).2 hℱ

/-- Companion bridge: affine-open sections indexed by `X.affineOpens` suffice to prove
torsion-freeness of a quasi-coherent `\mathcal O_X`-module on an integral scheme. -/
theorem isTorsionFree_of_affineOpens
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ U : X.affineOpens, Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U))) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_affineOpens ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
