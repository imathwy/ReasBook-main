import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]

-- Semantic recall: `lean_leansearch` surfaced the `Subobject`-lattice/colimit interface, and
-- local Chapter 28 precedent in Lemma 28.23.3 packages "directed colimit of subobjects" as a
-- directed subset of `Subobject F` with supremum `⊤`.

/-- A family of subobjects of `F` whose members are quasi-coherent and finite type, are directed,
and have supremum `⊤`. -/
class FiniteTypeQuasiCoherentSubobjectFamily
    (F : X.Modules) (S : Set (Subobject F)) : Prop where
  /-- Every member of the family is quasi-coherent. -/
  isQuasicoherent : ∀ G ∈ S, ((G : X.Modules)).IsQuasicoherent
  /-- Every member of the family is of finite type. -/
  isFiniteType : ∀ G ∈ S, ((G : X.Modules)).IsFiniteType
  /-- The family is directed by inclusion. -/
  directed : DirectedOn (· ≤ ·) S
  /-- The family has supremum `⊤`. -/
  isLUB : IsLUB S (⊤ : Subobject F)

/-- The quasi-coherent subobjects of `F` that are of finite type. -/
def finiteTypeQuasiCoherentSubobjects (F : X.Modules) : Set (Subobject F) :=
  { G | ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType }

/-- Lemma 28.22.3: let `X` be a quasi-compact and quasi-separated scheme. Any quasi-coherent
sheaf of `\mathcal{O}_X`-modules is the directed colimit of its quasi-coherent
`\mathcal{O}_X`-submodules which are of finite type. In `Subobject F`, this is recorded on the
canonical family of all finite type quasi-coherent subobjects, with directedness and supremum
`⊤`. -/
@[stacks 01PG]
theorem finiteTypeQuasiCoherentSubobjects_isDirectedColimit
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    FiniteTypeQuasiCoherentSubobjectFamily F (finiteTypeQuasiCoherentSubobjects F) := sorry

end AlgebraicGeometry.Scheme.Modules
