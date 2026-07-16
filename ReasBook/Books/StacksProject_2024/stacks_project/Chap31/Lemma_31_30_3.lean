import Mathlib
import StacksProject_2024.stacks_project.Chap24.Definition_24_3_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_30_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open TopCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced the canonical affine `Proj.toSpecZero` universally-closed instance,
-- `AlgebraicGeometry.IsIntegralHom.instUniversallyClosed`, and the composition instance
-- `AlgebraicGeometry.universallyClosedTypeComp`. Local Chapter 31 inspection found the existing
-- relative-`Proj` presentation owner `RelativeProjPresentation`, but no scheme-side relative
-- `Proj_S` construction with sheaf-level "finite type over `\mathcal A_0`" and integral
-- `\mathcal O_S → \mathcal A_0` hypotheses. The source-facing statement therefore keeps the
-- relative presentation and records the proof's explicit degree-zero factorization.

/-- The commutative-ring-valued structure sheaf of a scheme, as a sheaf on its open subsets. -/
private abbrev schemeCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u} :=
  S.sheaf

/-- The source hypotheses of Lemma 31.30.3 on a relative `Proj` presentation, expressed through
the proof's degree-zero factorization `p = q ≫ r`.

The map `r` represents the integral morphism induced by
`\mathcal O_S ⟶ \mathcal A_0`, while `q` represents the absolute `Proj` morphism over
`Spec(\mathcal A_0)` obtained from the finite-type `\mathcal A_0`-algebra structure. -/
@[stacks 07ZZ]
class RelativeProjIntegralDegreeZeroFiniteTypeHypothesis
    {S X T : Scheme.{u}} (p : X ⟶ S) (q : outParam (X ⟶ T))
    (r : outParam (T ⟶ S)) : Prop where
  /-- The relative `Proj` morphism factors through its degree-zero affine base. -/
  factorization : p = q ≫ r
  /-- The finite-type-over-degree-zero part gives a universally closed absolute `Proj` morphism. -/
  proj_universallyClosed : UniversallyClosed q
  /-- The map induced by `\mathcal O_S ⟶ \mathcal A_0` is integral. -/
  degreeZero_integral : IsIntegralHom r

/-- The degree-zero factorization hypothesis exposes universal closedness of the absolute `Proj`
piece. -/
@[stacks 07ZZ]
theorem RelativeProjIntegralDegreeZeroFiniteTypeHypothesis.proj_universallyClosed'
    {S X T : Scheme.{u}} {p : X ⟶ S} {q : X ⟶ T} {r : T ⟶ S}
    (h : RelativeProjIntegralDegreeZeroFiniteTypeHypothesis p q r) :
    UniversallyClosed q := sorry

/-- The degree-zero factorization hypothesis exposes integrality of the degree-zero base map. -/
@[stacks 07ZZ]
theorem RelativeProjIntegralDegreeZeroFiniteTypeHypothesis.degreeZero_integral'
    {S X T : Scheme.{u}} {p : X ⟶ S} {q : X ⟶ T} {r : T ⟶ S}
    (h : RelativeProjIntegralDegreeZeroFiniteTypeHypothesis p q r) :
    IsIntegralHom r := sorry

/-- A relative `Proj` satisfying the degree-zero integral finite-type hypothesis factors through
the corresponding degree-zero affine base. -/
@[stacks 07ZZ]
theorem RelativeProjIntegralDegreeZeroFiniteTypeHypothesis.factorization_eq
    {S X T : Scheme.{u}} {p : X ⟶ S} {q : X ⟶ T} {r : T ⟶ S}
    (h : RelativeProjIntegralDegreeZeroFiniteTypeHypothesis p q r) :
    p = q ≫ r := sorry

/-- Lemma 31.30.3: let `S` be a scheme, let `\mathcal A` be a quasi-coherent graded
`\mathcal O_S`-algebra, and let `p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the
relative `Proj` morphism. If `\mathcal O_S ⟶ \mathcal A_0` is integral and `\mathcal A` is of
finite type as a `\mathcal A_0`-algebra, then `p` is universally closed.

In the current environment, the scheme-side relative `Proj_S` construction and the corresponding
sheaf-level finite-type-over-degree-zero owner are not yet available. The two source hypotheses are
therefore represented by the source-facing degree-zero factorization hypothesis above. -/
@[stacks 07ZZ]
theorem relativeProj_universallyClosed_of_integral_degreeZero_finiteTypeAlgebra
    {S X T : Scheme.{u}} {p : X ⟶ S} {q : X ⟶ T} {r : T ⟶ S}
    {𝒜 : GradedAlgebraSheaf.{u, u} (schemeCommRingSheaf S)}
    (h𝒜qc : ∀ n : ℤ, (𝒜 n).IsQuasicoherent)
    (P : RelativeProjPresentation p)
    (hdeg0 : RelativeProjIntegralDegreeZeroFiniteTypeHypothesis p q r) :
    UniversallyClosed p := sorry

end AlgebraicGeometry.Scheme.Hom
