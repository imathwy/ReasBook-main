import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap29.Definition_29_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical cover owners `Scheme.affineCover`,
  `Scheme.affineOpenCover`, and `Scheme.AffineOpenCover.openCover`;
- local project precedent supplies the scheme owner `UniversallyCatenary` and the catenary
  affine-open cover shape in `Chap28/Lemma_28_11_2`.
-/

section

variable (S : Scheme.{u}) [IsLocallyNoetherian S]

/-- Lemma 29.17.2 (1): for a locally Noetherian scheme `S`, universal catenarity is equivalent to
admitting an open cover by universally catenary open subschemes, to all affine-open coordinate
rings being universally catenary, and to admitting an affine open cover by spectra of universally
catenary rings. -/
@[stacks 02J9]
theorem universallyCatenary_tfae :
    List.TFAE
      [ UniversallyCatenary S,
        ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, UniversallyCatenary (𝒰.X i),
        ∀ U : S.affineOpens, UniversallyCatenaryRing (Γ(S, U)),
        ∃ 𝒰 : S.AffineOpenCover,
          ∀ i : 𝒰.I₀, UniversallyCatenaryRing (Γ(S, (𝒰.f i).opensRange)) ] :=
  sorry

/-- Lemma 29.17.2 (1): a locally Noetherian scheme is universally catenary if and only if it
admits an open covering by universally catenary open subschemes. -/
@[stacks 02J9]
theorem universallyCatenary_iff_exists_openCover :
    UniversallyCatenary S ↔
      ∃ 𝒰 : S.OpenCover, ∀ i : 𝒰.I₀, UniversallyCatenary (𝒰.X i) :=
  sorry

/-- Lemma 29.17.2 (1): a locally Noetherian scheme is universally catenary if and only if every
affine open has universally catenary coordinate ring. -/
@[stacks 02J9]
theorem universallyCatenary_iff_forall_affineOpen_sectionsRing_universallyCatenaryRing :
    UniversallyCatenary S ↔
      ∀ U : S.affineOpens, UniversallyCatenaryRing (Γ(S, U)) :=
  sorry

/-- Lemma 29.17.2 (1): a locally Noetherian scheme is universally catenary if and only if it
admits an affine open cover whose coordinate rings are universally catenary. -/
@[stacks 02J9]
theorem universallyCatenary_iff_exists_affineOpenCover_sectionsRing_universallyCatenaryRing :
    UniversallyCatenary S ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, UniversallyCatenaryRing (Γ(S, (𝒰.f i).opensRange)) :=
  sorry

end

section

variable {S : Scheme.{u}}

/-- Lemma 29.17.2 (2): if `S` is universally catenary, then every scheme locally of finite type
over `S` is universally catenary. -/
@[stacks 02J9]
theorem universallyCatenary_of_locallyOfFiniteType
    {X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f] :
    UniversallyCatenary X :=
  sorry

/-- Restriction to an open subscheme preserves universal catenarity. -/
instance instUniversallyCatenaryToScheme [UniversallyCatenary S] (U : S.Opens) :
    UniversallyCatenary U.toScheme := by
  simpa using universallyCatenary_of_locallyOfFiniteType U.ι

/-- Every open subscheme of a universally catenary scheme is universally catenary. -/
@[stacks 02J9]
theorem universallyCatenary_toScheme (hS : UniversallyCatenary S) (U : S.Opens) :
    UniversallyCatenary U.toScheme := by
  let _ : UniversallyCatenary S := hS
  infer_instance

end

end AlgebraicGeometry
