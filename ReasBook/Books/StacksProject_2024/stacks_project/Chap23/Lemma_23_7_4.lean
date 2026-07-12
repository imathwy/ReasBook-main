import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Semantic search note: `lean_leansearch` surfaced the quotient-linear-map owner
`Submodule.mapQ` as the canonical way to formalize the induced map on
`I / (maximalIdeal A) I → J / (maximalIdeal A) J`. The quotient-ring side was then aligned with
local Chapter 23 precedent using `ModuleHasFiniteTorDimension`. -/

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Ideal

/-- The canonical quotient algebra structure on `A / J` over `A / I` for `I ≤ J`. -/
instance quotientFactorAlgebra
    {I J : Ideal A} (hIJ : I ≤ J) : Algebra (A ⧸ I) (A ⧸ J) :=
  RingHom.toAlgebra (Ideal.Quotient.factor hIJ)

/-- The subideal `𝔪 I` of `I` maps into the subideal `𝔪 J` of `J` under the inclusion
`I ↪ J`. -/
theorem maximalIdeal_mul_le_comap_inclusion
    {I J : Ideal A} (hIJ : I ≤ J) :
    Submodule.comap I.subtype (((IsLocalRing.maximalIdeal A) * I : Ideal A) : Submodule A A) ≤
      Submodule.comap (Submodule.inclusion hIJ)
        (Submodule.comap J.subtype
          (((IsLocalRing.maximalIdeal A) * J : Ideal A) : Submodule A A)) := sorry

/-- The inclusion-induced linear map `I / (maximalIdeal A) I → J / (maximalIdeal A) J`. -/
def quotientMapByMaximalIdealMul
    {I J : Ideal A} (hIJ : I ≤ J) :
    I ⧸ Submodule.comap I.subtype (((IsLocalRing.maximalIdeal A) * I : Ideal A) : Submodule A A) →ₗ[A]
      J ⧸ Submodule.comap J.subtype (((IsLocalRing.maximalIdeal A) * J : Ideal A) : Submodule A A) :=
  Submodule.mapQ
    (Submodule.comap I.subtype (((IsLocalRing.maximalIdeal A) * I : Ideal A) : Submodule A A))
    (Submodule.comap J.subtype (((IsLocalRing.maximalIdeal A) * J : Ideal A) : Submodule A A))
    (Submodule.inclusion hIJ)
    (maximalIdeal_mul_le_comap_inclusion hIJ)

/-- On quotient classes, `Ideal.quotientMapByMaximalIdealMul` is induced by the inclusion
`I ↪ J`. -/
theorem quotientMapByMaximalIdealMul_apply
    {I J : Ideal A} (hIJ : I ≤ J) (x : I) :
    quotientMapByMaximalIdealMul hIJ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion hIJ x) := sorry

end Ideal

section

variable [IsNoetherianRing A]
variable {I J : Ideal A}

/-- Lemma 23.7.4: let `(A, 𝔪)` be a Noetherian local ring. Let `I ⊆ J ⊆ A` be proper ideals. If
`A / J` has finite tor dimension over `A / I`, then `I / 𝔪 I → J / 𝔪 J` is injective. -/
@[stacks 09PV]
theorem injective_quotientMapByMaximalIdealMul_of_moduleHasFiniteTorDimension
    (hI : I ≠ ⊤) (hJ : J ≠ ⊤) (hIJ : I ≤ J)
    (hTor :
      let _inst : Algebra (A ⧸ I) (A ⧸ J) := Ideal.quotientFactorAlgebra hIJ
      CategoryTheory.ModuleHasFiniteTorDimension (ModuleCat.of (A ⧸ I) (A ⧸ J))) :
    Function.Injective (Ideal.quotientMapByMaximalIdealMul hIJ) := sorry

end

end
