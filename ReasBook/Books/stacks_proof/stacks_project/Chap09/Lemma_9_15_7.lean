import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {K : Type u} {M : Type v} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

/- If `M/K` is normal, then any `K`-automorphism `τ` of `L` induces the canonical restricted
`K`-automorphism `τ.restrictNormal M` of `M`. -/
recall AlgEquiv.restrictNormal

/-
The canonical owner of the extension construction into a normal extension is `AlgHom.liftNormal`.
-/
recall AlgHom.liftNormal

/- For a normal target, the lifted endomorphism is bijective by `AlgHom.normal_bijective`. -/
recall AlgHom.normal_bijective

/-- Lemma 9.15.7: if `L/K` is normal, then any `K`-algebra map `σ : M →ₐ[K] L` extends to a
`K`-algebra automorphism of `L`. This source-facing bridge packages the canonical lift
`σ.liftNormal L` into an element of `Gal(L / K)`. -/
@[stacks 0BME]
lemma exists_gal_extending_algHom [Normal K L] (σ : M →ₐ[K] L) :
    ∃ τ : Gal(L/K), τ.toAlgHom.comp (IsScalarTower.toAlgHom K M L) = σ := by
  refine ⟨AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _), ?_⟩
  ext x
  exact σ.liftNormal_commutes L x
