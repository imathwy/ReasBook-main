import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall:
- `lean_leansearch` surfaced mathlib's canonical local owner `LocallyQuasiFinite` and the
  finite-type/quasi-finite scheme-morphism API.
- Local Chapter 29 precedent introduces the Stacks-facing global owner `Scheme.Hom.QuasiFinite`
  and expresses point-set finite fibres as `Set.Finite ((fun x : X ↦ f x) ⁻¹' {s})`.
- The Stacks tag evidence is consistent: item tag `02NH` and source URL
  `https://stacks.math.columbia.edu/tag/02NH`.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.20.10 (1): a quasi-finite morphism of schemes is locally of finite type. -/
@[stacks 02NH]
theorem locallyOfFiniteType_of_quasiFinite (hf : QuasiFinite f) :
    LocallyOfFiniteType f := sorry

/-- Lemma 29.20.10 (2): a quasi-finite morphism of schemes is quasi-compact. -/
@[stacks 02NH]
theorem quasiCompact_of_quasiFinite (hf : QuasiFinite f) :
    QuasiCompact f := sorry

/-- Lemma 29.20.10 (3): a quasi-finite morphism of schemes has finite fibres over points
of the target. -/
@[stacks 02NH]
theorem finite_fibers_of_quasiFinite (hf : QuasiFinite f) :
    ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)) := sorry

/-- Lemma 29.20.10 (4): a locally of finite type, quasi-compact morphism of schemes with
finite fibres is quasi-finite. -/
@[stacks 02NH]
theorem quasiFinite_of_locallyOfFiniteType_quasiCompact_finite_fibers
    (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hfib : ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S))) :
    QuasiFinite f := sorry

end Scheme.Hom
end AlgebraicGeometry
