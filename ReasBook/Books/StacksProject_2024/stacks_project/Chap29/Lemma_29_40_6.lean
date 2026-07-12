import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Restrict

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced `Scheme.OpenCover`, `Scheme.OpenCover.isOpenCover_opensRange`, and
`morphismRestrict` as the canonical open-cover and restriction surfaces for this statement.

The intended local owners are `LocallyQuasiProjective` and `HQuasiProjective` from
`Definition_29_40_1`, but that file currently depends on the broken `Definition_29_37_1`
relative-ampleness import path. This file therefore records the source lemma as a labeled recall
block and checks the dependency-closed open-cover and restriction surfaces instead of introducing
fake replacement predicates. The Stacks tag evidence is consistent: item tag and source URL both
give `01VZ`. -/

/- Lemma 29.40.6 (Stacks tag `01VZ`): a morphism of schemes is locally quasi-projective if and
only if the target has an open cover on which all restricted morphisms are H-quasi-projective.

When `Definition_29_40_1` is dependency-closed, the intended source-facing theorem is:
`theorem locallyQuasiProjective_iff_exists_openCover_hQuasiProjective
  {X S : Scheme} {f : X ⟶ S} :
  LocallyQuasiProjective f ↔
    ∃ 𝒰 : Scheme.OpenCover S, ∀ i : 𝒰.I₀,
      HQuasiProjective (f ∣_ ((𝒰.f i).opensRange))`.
-/
#check fun {S : Scheme.{u}} ↦ Scheme.OpenCover.{u} S
#check Scheme.OpenCover.isOpenCover_opensRange
#check fun {X S : Scheme.{u}} (f : X ⟶ S) (𝒰 : Scheme.OpenCover.{u} S) (i : 𝒰.I₀) ↦
  f ∣_ ((𝒰.f i).opensRange)
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ LocallyOfFiniteType f
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ QuasiCompact f
#check fun {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S) ↦
  i ≫ p

end AlgebraicGeometry
