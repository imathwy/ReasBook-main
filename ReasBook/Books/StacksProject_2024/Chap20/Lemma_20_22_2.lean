import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Y : TopCat.{u}} [SpectralSpace X] [SpectralSpace Y]
variable (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (X.Sheaf AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (X.Sheaf AddCommGrpCat.{u})]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]

/-- The specializing subset of a point `y` in a spectral space `Y`. -/
abbrev specializationSubset (y : Y) : Set Y :=
  nhdsKer ({y} : Set Y)

/-- The subspace of `X` lying over the specializing subset of `y`. -/
abbrev preimageSpecializationSubspace (f : X ⟶ Y) (y : Y) : TopCat.{u} :=
  TopCat.of ↥(f ⁻¹' specializationSubset y)

/-- The inclusion of the inverse image of the specializing subset of `y` into `X`. -/
private abbrev preimageSpecializationInclusion (f : X ⟶ Y) (y : Y) :
    preimageSpecializationSubspace f y ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of `ℱ` to the inverse image of the specializing subset of `y`. -/
abbrev preimageSpecializationSheaf
    (f : X ⟶ Y) (y : Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (preimageSpecializationSubspace f y).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (preimageSpecializationInclusion f y)).obj ℱ

-- Proof sketch: identify the stalk of `R^p f_* ℱ` with the filtered colimit over the
-- quasi-compact open neighbourhoods of `y` of the groups `H^p(f⁻¹(V), ℱ)`. The set of points
-- specializing to `y` is the canonical subset `nhdsKer ({y} : Set Y)`, and Lemma `20.19.3`
-- computes the cohomology of its inverse image as this filtered colimit.
/-- Lemma 20.22.2: for a spectral map of spectral spaces, the stalk at `y` of the `p`-th higher
direct image of an abelian sheaf `ℱ` is canonically isomorphic to the degree-`p` cohomology of
the restriction of `ℱ` to the inverse image of the canonical specializing subset
`nhdsKer ({y} : Set Y)`. -/
theorem higher_direct_image_stalk_isomorphic_preimage_specialization_cohomology
    (hf : IsSpectralMap f) (y : Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify
      (Opens.grothendieckTopology (preimageSpecializationSubspace f y))
      AddCommGrpCat.{u}]
    [HasExt ((preimageSpecializationSubspace f y).Sheaf AddCommGrpCat.{u})] :
    IsIsomorphic
      (TopCat.Presheaf.stalk
        ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived p).obj ℱ).obj) y)
      ((preimageSpecializationSheaf f y ℱ).H' p
        (⊤ : Opens (preimageSpecializationSubspace f y))) := sorry

end Sheaf
end CategoryTheory
