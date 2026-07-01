import Mathlib
import stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: derived-complete modules over a commutative ring, with quotient-vanishing and
  submodule-saturation criteria for zero modules;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`,
  `subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson`;
- best owner abstraction: the project owner predicate `ModuleCat.IsDerivedCompleteWithRespectTo`,
  with the primitive zero-criterion expressed by the owner-level equality
  `I • (⊤ : Submodule A M) = ⊤`;
- primitive data: the ideal `I`, the module `M`, derived completeness of `M`, and the submodule
  equality `I • ⊤ = ⊤`;
- derived API: the source-facing quotient formulation
  `Subsingleton (M ⧸ I • (⊤ : Submodule A M))`.

Layer triage:
- `source-facing`: the quotient-vanishing statement `M / IM = 0`;
- `core/canonical`: `M.IsDerivedCompleteWithRespectTo I` together with `I • ⊤ = ⊤`;
- `bridge/view`: the quotient-subsingleton companion theorem below. -/

variable {I : Ideal A} {M : ModuleCat A}

local notation "IM" => I • (⊤ : Submodule A M)

-- Proof sketch: write `I = (f₁, …, f_r)` and choose the largest `i` such that
-- `M / (f₁, …, fᵢ) M` is nonzero. Lemma `15.92.6` shows this quotient is still derived complete.
-- Then `fᵢ₊₁` acts surjectively on it because `(M ⧸ I • ⊤)` is zero, producing a nonzero derived
-- limit of the constant tower with transition map `fᵢ₊₁`, contradicting derived completeness.
/-- Lemma 15.92.7, owner-level form: if `I` is finitely generated and a derived-complete module
`M` satisfies `IM = M`, then `M` is zero. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hIM : IM = ⊤) :
    Subsingleton M := sorry

/-- Lemma 15.92.7: if `I` is finitely generated and an `A`-module `M` is derived complete with
respect to `I`, then the vanishing condition `M / I M = 0`, formalized by the quotient
`M ⧸ I • (⊤ : Submodule A M)` being subsingleton, forces `M` itself to be zero. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_subsingleton_quotient_smul_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hquot : Subsingleton (M ⧸ IM)) :
    Subsingleton M := by
  apply subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top hI hM
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  have hx : Submodule.mkQ IM x = 0 := Subsingleton.elim _ _
  simpa [Submodule.Quotient.mk_eq_zero] using hx

end ModuleCat

end
