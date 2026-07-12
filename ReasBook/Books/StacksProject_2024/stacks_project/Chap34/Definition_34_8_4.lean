import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` pointed to `IsProper`, `Surjective`,
-- `LocallyOfFiniteType`, and `Scheme.affineOpens` as the matching mathlib surfaces.

/-- A standard ph covering of an affine scheme, presented by a proper surjective map
and a finite affine open covering of its source. -/
structure StandardPhCovering (T : Scheme) [IsAffine T] where
  /-- The number of affine pieces in the chosen presentation. -/
  m : ℕ
  /-- The source of the proper surjective morphism presenting the covering. -/
  source : Scheme
  /-- The proper surjective morphism to the affine base scheme. -/
  toBase : source ⟶ T
  /-- Properness of the presenting morphism. -/
  isProper_toBase : IsProper toBase
  /-- Surjectivity of the presenting morphism. -/
  surjective_toBase : Surjective toBase
  /-- A finite affine open covering of the source. -/
  cover : Fin m → source.affineOpens
  /-- The chosen affine opens cover the source. -/
  cover_eq_top : ⨆ j, ((cover j : source.Opens)) = ⊤

/-- A standard ph covering inherits properness of its presenting morphism. -/
instance {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T) : IsProper Φ.toBase :=
  Φ.isProper_toBase

/-- A standard ph covering inherits surjectivity of its presenting morphism. -/
instance {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T) : Surjective Φ.toBase :=
  Φ.surjective_toBase

/-- The `j`-th affine piece of a standard ph covering, viewed as a scheme over the base. -/
abbrev StandardPhCovering.obj {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T)
    (j : Fin Φ.m) : Scheme :=
  ((Φ.cover j : Φ.source.Opens)).toScheme

/-- The structure morphism from the `j`-th affine piece of a standard ph covering to the base. -/
abbrev StandardPhCovering.map {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T)
    (j : Fin Φ.m) : Φ.obj j ⟶ T :=
  ((Φ.cover j : Φ.source.Opens)).ι ≫ Φ.toBase

/-- A standard ph covering can be used as its underlying finite family of morphisms into the base
scheme. -/
instance {T : Scheme} [IsAffine T] :
    CoeFun (StandardPhCovering T) (fun Φ ↦ (j : Fin Φ.m) → Φ.obj j ⟶ T) where
  coe Φ := Φ.map

/-- Each affine piece of a standard ph covering is affine. -/
instance {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T) (j : Fin Φ.m) :
    IsAffine (Φ.obj j) := by
  change IsAffine (((Φ.cover j : Φ.source.Opens)).toScheme)
  infer_instance

/-- Source-facing specification for Definition 34.8.4: a standard ph covering consists of a proper
surjective morphism together with a finite affine open covering of its source. -/
theorem StandardPhCovering.source_spec {T : Scheme} [IsAffine T] (Φ : StandardPhCovering T) :
    IsProper Φ.toBase ∧
      Surjective Φ.toBase ∧
        (∀ j, IsAffine (Φ.obj j)) ∧
          (⨆ j, ((Φ.cover j : Φ.source.Opens)) = ⊤) := by
  exact ⟨Φ.isProper_toBase, Φ.surjective_toBase, fun j ↦ inferInstance, Φ.cover_eq_top⟩

/-- Definition 34.8.4: a ph covering of a scheme is a family of locally finite type morphisms
whose pullbacks to every affine open are refined by a standard ph covering. -/
class PhCovering {ι : Type u} {T : Scheme} (X : ι → Scheme) (π : ∀ i, X i ⟶ T) : Prop where
  /-- Every morphism in the family is locally of finite type. -/
  locallyOfFiniteType : ∀ i, LocallyOfFiniteType (π i)
  /-- Over each affine open of the target, some standard ph covering refines the pulled back family. -/
  refinesOnAffineOpens :
    ∀ U : T.affineOpens, ∃ Φ : StandardPhCovering U,
      ∀ j : Fin Φ.m, ∃ i : ι, ∃ g : Φ.obj j ⟶ pullback (π i) U.1.ι,
        g ≫ pullback.snd (π i) U.1.ι = Φ.map j

/-- A ph covering consists of morphisms that are locally of finite type. -/
instance {ι : Type u} {T : Scheme} {X : ι → Scheme} {π : ∀ i, X i ⟶ T}
    [h : PhCovering X π] (i : ι) : LocallyOfFiniteType (π i) :=
  h.locallyOfFiniteType i

/-- Over every affine open of the target, a ph covering admits a standard ph refinement of the
pulled back family. -/
theorem PhCovering.exists_standardPhRefinement
    {ι : Type u} {T : Scheme} {X : ι → Scheme} {π : ∀ i, X i ⟶ T} [h : PhCovering X π]
    (U : T.affineOpens) :
    ∃ Φ : StandardPhCovering U,
      ∀ j : Fin Φ.m, ∃ i : ι, ∃ g : Φ.obj j ⟶ pullback (π i) U.1.ι,
        g ≫ pullback.snd (π i) U.1.ι = Φ.map j :=
  h.refinesOnAffineOpens U
