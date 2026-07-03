import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_2
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

namespace Representation

open Rep

section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {V W : Type (max u v w)} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

variable (H : Subgroup G) (E : Representation k G V) (θ : Representation k H W)

/-
Source/core/bridge triage:
* source-facing: Proposition 7-7.2-2 is Frobenius reciprocity for multiplicities of restriction
  and induction.
* core/canonical owners sampled in this domain: `Rep.indResHomEquiv`, `Rep.homLinearEquiv`,
  `Representation.finrank_intertwiningMap_eq_isotypicMultiplicity`, and
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`.
* primitive data: the subgroup `H`, the `H`-representation `θ`, and the `G`-representation `E`.
* bridge/view: the canonical Frobenius equivalence
  `θ ⟶ Res_H^G(E) ≃ Ind_H^G(θ) ⟶ E`, obtained by transporting `Rep.indResHomEquiv`
  to intertwining spaces through `Rep.homLinearEquiv`.
-/
/-- The canonical Frobenius reciprocity bridge on intertwining spaces. -/
theorem frobenius_reciprocity_intertwining_finrank_eq :
    Module.finrank k (θ.IntertwiningMap (E.comp H.subtype)) =
      Module.finrank k ((ind H.subtype θ).IntertwiningMap E) := by
  let e :
      θ.IntertwiningMap (E.comp H.subtype) ≃ₗ[k] (ind H.subtype θ).IntertwiningMap E :=
    (homLinearEquiv (of θ) (res H.subtype (of E))).symm ≪≫ₗ
      (indResHomEquiv H.subtype (of θ) (of E)).symm ≪≫ₗ
        homLinearEquiv (Rep.ind H.subtype (of θ)) (of E)
  simpa using e.finrank_eq

-- Proof sketch: identify the multiplicity of `θ` in `Res_H^G(E)` by
-- `finrank_intertwiningMap_eq_isotypicMultiplicity`, identify the multiplicity of `E` in any
-- irreducible decomposition of `Ind_H^G(θ)` by
-- `card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`, and compare the resulting
-- two owner expressions through `frobenius_reciprocity_intertwining_finrank_eq`.
section IrreducibleMultiplicity

variable {ι : Type*} [Finite ι]

local instance instDecidableEqIotaChap7722 : DecidableEq ι := Classical.decEq ι

/-- Proposition 7-7.2-2: if `θ` is an irreducible representation of `H` and `E` is an
irreducible representation of `G`, then the multiplicity of `θ` in `Res_H^G(E)` equals the
number of irreducible summands isomorphic to `E` in any irreducible decomposition of
`Ind_H^G(θ)`. -/
theorem frobenius_reciprocity_irreducible_multiplicity_eq
    [Finite G] [IsAlgClosed k] [Invertible (Nat.card H : k)]
    [E.IsIrreducible] [θ.IsIrreducible]
    (σ : ι → Subrepresentation (ind H.subtype θ))
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, ((σ i).toRepresentation).IsIrreducible) :
    Module.finrank k ((isotypicSubrepresentation (E.comp H.subtype) θ).toSubmodule) /
        Module.finrank k W =
      Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv E) } := by
  let Eres : Representation k H V := E.comp H.subtype
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite E
  letI : FiniteDimensional k W := IsIrreducible.finiteDimensional_of_finite θ
  letI (i : ι) : FiniteDimensional k ((σ i).toSubmodule) := by
    letI : ((σ i).toRepresentation).IsIrreducible := hσ i
    exact IsIrreducible.finiteDimensional_of_finite ((σ i).toRepresentation)
  let ℳ : ι → Submodule k (IndV H.subtype θ) := fun i ↦ (σ i).toSubmodule
  letI := DirectSum.IsInternal.chooseDecomposition ℳ hinternal
  letI : FiniteDimensional k (IndV H.subtype θ) :=
    FiniteDimensional.of_injective (DirectSum.decomposeLinearEquiv ℳ).toLinearMap
      (DirectSum.decomposeLinearEquiv ℳ).injective
  calc
    Module.finrank k ((isotypicSubrepresentation Eres θ).toSubmodule) /
        Module.finrank k W =
        Module.finrank k (θ.IntertwiningMap Eres) := by
          symm
          simpa [Eres] using finrank_intertwiningMap_eq_isotypicMultiplicity Eres θ
    _ = Module.finrank k ((ind H.subtype θ).IntertwiningMap E) :=
      frobenius_reciprocity_intertwining_finrank_eq H E θ
    _ = Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv E) } := by
      symm
      simpa using
        card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
          (ind H.subtype θ) σ hinternal hσ E inferInstance

end IrreducibleMultiplicity

end

end Representation
