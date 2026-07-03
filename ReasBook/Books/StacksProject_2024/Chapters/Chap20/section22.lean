import Mathlib
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_22_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The preorder of quasi-compact open neighborhoods of `E` in the spectral space `X`. -/
abbrev qcOpenNeighborhoods (E : Set X) :=
  { U : CompactOpens X // E ⊆ (U : Set X) }

/-- The inclusion of quasi-compact open neighborhoods of `E` into the lattice of open subsets of
`X`. -/
def qcOpenNeighborhoodsToOpens (E : Set X) : qcOpenNeighborhoods E →o Opens X where
  toFun U := U.1.toOpens
  monotone' := fun _ _ hUV ↦ hUV

/-- The canonical cohomology diagram on quasi-compact open neighborhoods of `E`, ordered by
reverse inclusion, with values `U ↦ H^p(U, \mathcal F)`. -/
abbrev qcOpenNeighborhoodCohomologyDiagram
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (p : ℕ) :
    (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (qcOpenNeighborhoodsToOpens E).toFunctor.op ⋙ ℱ.cohomologyPresheaf p

/-- The inclusion `nhdsKer E ↪ X` of the specializing subset of `E` into the ambient spectral
space. -/
abbrev specializingSubsetInclusion (E : Set X) :
    TopCat.of ↥(nhdsKer E) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the specializing subset `nhdsKer E`. -/
abbrev specializingSubsetSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (TopCat.of ↥(nhdsKer E)).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (specializingSubsetInclusion E)).obj ℱ

/-- The inclusion `(nhdsKer E \ E) ↪ X` of the complement of `E` inside its specializing subset. -/
abbrev specializingSubsetSDiffInclusion (E : Set X) :
    TopCat.of ↥((nhdsKer E \ E : Set X)) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the spectral subspace `nhdsKer E \ E`. -/
abbrev specializingSubsetSDiffSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) :
    (TopCat.of ↥((nhdsKer E \ E : Set X))).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (specializingSubsetSDiffInclusion E)).obj ℱ

/-- The inclusion `(U \ E) ↪ X` for a quasi-compact open neighborhood `U` of `E`. -/
abbrev neighborhoodComplementInclusion
    (E : Set X) (U : qcOpenNeighborhoods E) :
    TopCat.of ↥((((U.1 : Set X) \ E : Set X))) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of an abelian sheaf on `X` to the locally closed complement `U \ E` inside a
quasi-compact open neighborhood `U` of `E`. -/
abbrev neighborhoodComplementSheaf
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (U : qcOpenNeighborhoods E) :
    (TopCat.of ↥((((U.1 : Set X) \ E : Set X)))).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (neighborhoodComplementInclusion E U)).obj ℱ

variable {ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}} {E : Set X}

variable [HasSheafify (Opens.grothendieckTopology ↥(nhdsKer E)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥(nhdsKer E)) AddCommGrpCat.{u})]

-- Proof sketch: identify `nhdsKer E` with the cofiltered limit of the quasi-compact open
-- neighborhoods of `E` using Lemma `5.24.7`, then apply the inverse-limit cohomology comparison of
-- Lemma `20.19.3` to the restriction of `ℱ` along the projection maps.
/-- Lemma 20.22.1 (1): if `E ⊆ X` is quasi-compact and `W = nhdsKer E` is the subset of points
specializing to a point of `E`, then the cohomology of `\mathcal F|_W` is the filtered colimit of
the cohomology groups over the quasi-compact open neighborhoods of `E`. -/
theorem specializingSubset_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : IsCompact E) (p : ℕ)
    [HasColimit (qcOpenNeighborhoodCohomologyDiagram ℱ E p)] :
    IsIsomorphic
      (colimit (qcOpenNeighborhoodCohomologyDiagram ℱ E p))
      ((specializingSubsetSheaf ℱ E).H' p (⊤ : Opens ↥(nhdsKer E))) := sorry

variable [HasSheafify (Opens.grothendieckTopology ↥((nhdsKer E \ E : Set X)))
  AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology ↥((nhdsKer E \ E : Set X)))
  AddCommGrpCat.{u})]

-- Proof sketch: use Lemma `5.24.8` to identify `nhdsKer E \ E` with the inverse limit of the
-- complements `U \ E` over quasi-compact open neighborhoods `U` of `E`, and then apply the same
-- inverse-limit cohomology comparison as in part `(1)` to any chosen diagram realizing the groups
-- `H^p(U \ E, \mathcal F|_{U \ E})`.
/-- Lemma 20.22.1 (2): if `E ⊆ X` is constructible and `W = nhdsKer E`, then the cohomology of
`\mathcal F|_{W \setminus E}` is the filtered colimit of the cohomology groups
`H^p(U \setminus E, \mathcal F|_{U \setminus E})` over quasi-compact open neighborhoods `U` of
`E`, expressed using a chosen neighborhood-complement cohomology diagram. -/
theorem specializingSubset_sdiff_cohomology_isomorphic_colimit_of_qcOpenNeighborhoods
    (ℱ : (TopCat.of X).Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : Topology.IsConstructible E)
    (p : ℕ)
    (D : (qcOpenNeighborhoods E)ᵒᵖ ⥤ AddCommGrpCat.{u}) [HasColimit D]
    (hD :
      ∀ U : qcOpenNeighborhoods E,
        IsIsomorphic
          (D.obj (Opposite.op U))
          ((neighborhoodComplementSheaf ℱ E U).H' p
            (⊤ : Opens ↥((((U.1 : Set X) \ E : Set X)))))) :
    IsIsomorphic
      (colimit D)
      ((specializingSubsetSDiffSheaf ℱ E).H' p
        (⊤ : Opens ↥((nhdsKer E \ E : Set X)))) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_20_22_2 (from Chap20) -/
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

/-! ### Lemma_20_22_3 (from Chap20) -/
open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

/-
Domain-style sampling for Lemma 20.22.3:
- primary domain: higher sheaf cohomology vanishing on spectral spaces and its profinite
  specialization;
- same-domain owner declarations inspected:
  `Profinite`,
  `topologicalKrullDim_eq_zero_of_nonempty_t2`,
  `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq`;
- best owner abstractions: the bundled topological owner `Profinite` for the source-facing
  specialization, and the spectral-space vanishing theorem as the core/canonical owner;
- primitive-vs-derived split: the primitive input here is only the profinite space `X`; the
  zero-dimensionality statement and the vanishing result are derived API, so this file should be a
  thin bridge from `Profinite` to the spectral-space owner rather than a parallel standalone
  vanishing theorem.

Layer triage:
- `source-facing`: vanishing of higher cohomology on a profinite space
- `core/canonical`: `isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq`
- `bridge/view`: specialization along `topologicalKrullDim_eq_zero_of_nonempty_t2`

Primitive data is just the profinite space itself. Clopen-refinement statements, unbundled
compact/Hausdorff/totally disconnected hypotheses, and zero-dimensional reformulations are all
derived topology-side API, so the public statement here should stay at the bundled `Profinite`
owner while its proof and surrounding commentary reuse the spectral-space owner directly.
-/

variable {X : Profinite.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Lemma 20.22.3: if `X` is a profinite topological space, then every abelian sheaf on `X` has
vanishing higher global cohomology. -/
theorem isZero_higherCohomology_of_profinite
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q (⊤ : Opens X)) := by
  simpa using
    (isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq
      (X := Profinite.toTopCat.obj X)
      (d := 0)
      (hXdim := topologicalKrullDim_eq_zero_of_nonempty_t2 X)
      (F := F)
      (hq := hq))

end Sheaf
end CategoryTheory

/-! ### Proposition_20_22_4 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped ClosedSubsetSectionsWithSupport

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X : TopCat.{u}} [SpectralSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/-- The cohomology of an abelian sheaf on `X` with support in a closed subset `Z`, modeled as the
ordinary cohomology of the sheaf of sections with support on the subspace `Z`. -/
noncomputable abbrev closedSubsetCohomologyWithSupport
    {Z : Set X} (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  ((𝓗[hZ]).obj F).H' q
    (⊤ : Opens (TopCat.of Z))

-- Proof sketch: unfold `closedSubsetCohomologyWithSupport`; it is defined to be the degree-`q`
-- cohomology of the sheaf of sections with support in `Z` on the closed subspace.
/-- The support-cohomology abbreviation is given by sheaf cohomology of the sections-with-support
sheaf on the closed subspace. -/
theorem closedSubsetCohomologyWithSupport_def
    {Z : Set X} (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    closedSubsetCohomologyWithSupport hZ F q =
      (((𝓗[hZ]).obj F).H' q
        (⊤ : Opens (TopCat.of Z))) := sorry

-- Proof sketch: this is the induction-on-dimension vanishing statement proved in the text; the
-- base case uses profinite vanishing and the inductive step uses the surjectivity statement in
-- part `(2)` together with Leray acyclicity for the image sheaf occurring in an injective
-- resolution.
/-- Proposition 20.22.4 (1): if `X` is a spectral space of Krull dimension `d`, then every
abelian sheaf on `X` has vanishing global cohomology in degrees strictly larger than `d`. -/
theorem isZero_higherCohomology_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u}) {q : ℕ}
    (hq : d < q) :
    IsZero (F.H' q (⊤ : Opens ↑X)) := sorry

-- Proof sketch: let `Z = X \ U` and consider the specializing locus `W` of `Z`. By the
-- colimit description from Lemma `20.22.1`, the restriction of a class in `H^d(U, F)` to
-- `W \ Z` vanishes after shrinking around `Z`; Mayer-Vietoris for the cover `X = U ∪ V` then
-- lifts the class to `H^d(X, F)`.
/-- Proposition 20.22.4 (2): if `X` is a spectral space of Krull dimension `d`, then for every
quasi-compact open subset `U ⊆ X` the restriction map `H^d(X, \mathcal F) → H^d(U, \mathcal F)`
is surjective. -/
theorem surjective_restriction_topCohomology_to_compactOpen_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u})
    (U : CompactOpens ↑X) :
    Function.Surjective
      (((F.cohomologyPresheaf d).map
          (homOfLE
            (show U.toOpens ≤ (⟨Set.univ, isOpen_univ⟩ : Opens ↑X) from
              fun _ _ ↦ Set.mem_univ _)).op) :
        F.H' d (⊤ : Opens ↑X) ⟶ F.H' d U.toOpens) := sorry

-- Proof sketch: apply the long exact sequence for cohomology with support of the pair
-- `(X, X \ Z)`. Since `Z` is constructible and closed, the complement `X \ Z` is again a
-- quasi-compact open spectral subspace of dimension at most `d`; combine part `(1)` on `X` and on
-- `X \ Z` with the surjectivity from part `(2)` to force the supported cohomology to vanish in
-- degrees above `d`.
/-- Proposition 20.22.4 (3): if `X` is a spectral space of Krull dimension `d`, then for every
constructible closed subset `Z ⊆ X` the cohomology with support in `Z` vanishes in degrees
strictly larger than `d`. -/
theorem isZero_higherClosedSubsetCohomologyWithSupport_of_spectralSpace_of_topologicalKrullDim_eq
    (d : ℕ) (hXdim : topologicalKrullDim X = d) (F : X.Sheaf AddCommGrpCat.{u})
    {Z : Set X} (hZclosed : IsClosed Z) (hZconstructible : Topology.IsConstructible Z) {q : ℕ}
    (hq : d < q)
    [HasSheafify (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}]
    [HasExt.{u} ((TopCat.of Z).Sheaf AddCommGrpCat.{u})] :
    IsZero (closedSubsetCohomologyWithSupport hZclosed F q) := sorry

end Sheaf
end CategoryTheory
