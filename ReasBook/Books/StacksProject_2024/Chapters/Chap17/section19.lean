import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_19_1 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

/-- The lower-shriek image `j_{U!}\underline{S}` of the constant sheaf with value `S` on the open
subspace `U`. -/
abbrev extensionByZeroConstantSheaf (U : Opens X) (S : Type u) :
    Sh(X) :=
  ((j! U).obj
    ((constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj S) :
    Sh(X))

notation:max "j![" U ", " S "]" => extensionByZeroConstantSheaf U S

/-- A family of sheaves of the form `j_{U_i!}\underline{A_i}` admits its coproduct in
`Sh(X, Type)`. -/
private noncomputable instance lowerShriekConstantSheaf_hasCoproduct
    {I : Type u} (U : I → Opens X) (S : I → Type u) :
    HasCoproduct (fun i : I ↦ j![U i, S i]) := by
  let _ : HasColimitsOfShape (Discrete I) (Type u) := inferInstance
  let _ : HasColimitsOfShape (Discrete I) (Sh(X)) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete I) (Sh(X)))
  infer_instance

-- Proof sketch: for each stalk element `s ∈ ℱ_x`, choose a basis open `U(x,s)` and a section of
-- `ℱ` over `U(x,s)` representing `s`; Lemma 6.31.4 identifies such a section with a morphism
-- `j_{U(x,s)!}\underline{*} ⟶ ℱ`, and the induced coproduct map is stalkwise surjective, hence
-- epimorphic.
/-- Lemma 17.19.1: every sheaf of sets on `X` is an epimorphic image of a coproduct of lower-shriek
images `j_{U_i!}\underline{S_i}` with each `U_i` in the basis `B` and each `S_i` finite. -/
theorem exists_epi_from_coproduct_of_basis_extension_by_empty_constant_sheaves
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (ℱ : Sh(X)) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u)
      (hU : ∀ i, U i ∈ B) (hS : ∀ i, Finite (S i))
      (φ : (∐ fun i : I ↦ j![U i, S i]) ⟶ ℱ), Epi φ := sorry

end

/-! ### Lemma_17_19_2 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.19.2:
- primary domain: filtered-colimit presentations of set-valued sheaves by finite coequalizers of
  lower-shriek constant sheaves;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.ind`,
  `ColimitPresentation`,
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `j![U, S]`;
- best owner abstraction: the filtered-colimit statement itself should use the canonical owner
  `CategoryTheory.ObjectProperty.ind` applied to the source-facing stagewise predicate
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B)`, rather than
  restating the `ColimitPresentation` witness data explicitly in the theorem surface;
- primitive data: a filtered colimit presentation of `ℱ`;
- derived API: the `ObjectProperty.ind` packaging of that presentation together with the stagewise
  owner predicate for the diagram objects.

Source/core/bridge triage:
- `source-facing`: the filtered-colimit presentation relative to the basis `B`;
- `core/canonical`: `CategoryTheory.ObjectProperty.ind` applied to the owner from `17.19.2.1`;
- `bridge/view`: the later spectral-space consequences deduced from that stagewise owner.
-/

-- Proof sketch: start from the epimorphic coproduct presentation of Lemma `17.19.1`, apply the
-- same construction to the kernel pair, and then restrict to finite subdiagrams. Quasi-compactness
-- of the basis opens and Lemma `6.29.1` let sections over the relevant opens commute with the
-- filtered colimit, so the resulting finite coequalizer stages indexed by finite subsets form a
-- filtered colimit presentation of `ℱ`.
/-- Lemma 17.19.2: if `X` has a basis `B` of quasi-compact opens, then every sheaf of sets on `X`
is a filtered colimit of sheaves admitting finite coequalizer presentations by lower-shriek
constant sheaves on members of `B` with finite fibres. We state this in the canonical owner form
`ObjectProperty.ind` applied to
`HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B)`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_open_extensionByZeroConstantSheaf_coequalizers
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hqc : ∀ U, U ∈ B → IsCompact (U : Set X))
    (ℱ : Sh(X)) :
    ind
      (HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (· ∈ B))
      ℱ := sorry

end

/-! ### Lemma_17_19_3 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe u

/- Domain-style sampling for Lemma 17.19.3:
- primary domain: set-valued sheaves on spectral spaces, descended along spectral maps to finite
  sober spaces;
- sampled owner declarations:
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`,
  `IsSpectralMap`,
  `QuasiSober`;
- best owner abstraction: the source-facing hypothesis is already the chapter owner
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn` specialized to quasi-compact
  opens, while the spectral-space input is governed upstream by the chapter-5 directed-limit
  characterization `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`; the chapter-5
  owner for the source sober conclusion is the pair `T0Space Y` and `QuasiSober Y`, so the finite
  stage returned here should expose both pieces directly;
- primitive data: a sheaf `ℱ` on a spectral space `X` with the finite coequalizer presentation
  from `17.19.2.1` on quasi-compact opens;
- derived API: the descended finite `T₀` space `Y`, the spectral map `f : X ⟶ Y`, the model sheaf
  `𝒢`, its finite stalk condition, and the resulting inverse-image isomorphism.

Source/core/bridge triage:
- `source-facing`: the existence of a finite sober model for a constructible sheaf presentation,
  expressed canonically as `Finite Y`, `T0Space Y`, and `QuasiSober Y`;
- `core/canonical`: `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `spectralSpace_iff_homeomorphic_directed_limit_finite_sober`, `IsSpectralMap`, and
  `QuasiSober`;
- `bridge/view`: the comparison isomorphism identifying `ℱ` with the inverse image of `𝒢` along the
  spectral map `f`.
-/

-- Proof sketch: combine the finite coequalizer presentation from `17.19.2.1` with the directed
-- inverse-limit presentation of a spectral space by finite `T₀` stages from Lemma `5.23.14`,
-- together with the canonical sober-space owner form `T0Space ∧ QuasiSober`.
-- Descend the finitely many quasi-compact opens and the finitely many structure maps defining the
-- coequalizer to one finite `T₀` stage, then take on that stage the corresponding coequalizer
-- sheaf `𝒢`; its stalks are finite because it is built from finitely many finite constant sheaves
-- by finite colimits, and inverse image along the projection recovers `ℱ`.
/-- Lemma 17.19.3: a sheaf of sets on a spectral space admitting the finite coequalizer
presentation of `17.19.2.1` is the inverse image of a sheaf with finite stalks along some spectral
map
to a finite sober topological space, expressed canonically by `Finite Y`, `T0Space Y`, and
`QuasiSober Y`. Here the source-facing hypothesis is the owner predicate
`HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (fun U ↦ IsCompact (U : Set X))`. -/
theorem exists_finite_sober_sheaf_model_of_constructible_set_presentation
    {X : TopCat.{u}} [SpectralSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    (ℱ : Sh(X))
    (hℱ :
      HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn
        (fun U ↦ IsCompact (U : Set X)) ℱ) :
    ∃ (Y : TopCat.{u}) (_ : Finite Y) (_ : T0Space Y) (_ : QuasiSober Y) (f : X ⟶ Y)
      (_ : IsSpectralMap f) (𝒢 : Sh(Y)) (e : ((f⁻¹).obj 𝒢) ≅ ℱ),
      ∀ y : Y, Finite (𝒢.presheaf.stalk y) := sorry

/-! ### Lemma_17_19_4 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Topology
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

local notation:max "i[" Z "]" => X.closedSubsetInclusion (Z : Set X)

/- Domain-style sampling for Lemma 17.19.4:
- primary domain: set-valued sheaves on spectral spaces and embeddings into finite products of
  pushforwards from closed subspaces;
- sampled owner declarations:
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `exists_finite_sober_sheaf_model_of_constructible_set_presentation`,
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `constantSheaf`;
- best owner abstraction: on the spectral-space branch, the source-facing hypothesis should use
  the compact-open owner
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (fun U ↦ IsCompact (U : Set X))`,
  while the individual product factors should be stated directly using the canonical closed-subset
  inclusion and ambient sheaf pushforward rather than a local wrapper built from `TopCat.of Z` and
  `Subtype.val`;
- primitive data: a finite family of constructible closed subsets of `X` together with finite
  value types, indexed by an arbitrary finite type rather than a numbered model;
- derived API: the product sheaf built from those factors and the monomorphism from `ℱ`.

Source/core/bridge triage:
- `source-facing`: the finite-product embedding statement from constructible closed pieces;
- `core/canonical`: `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `TopCat.closedSubsetInclusion`, `Sheaf.pushforward`, `constantSheaf`;
- `bridge/view`: the finite-sober descent input from Lemma `17.19.3`.
-/

-- Proof sketch: use Lemma `17.19.3` to descend `ℱ` to a sheaf with finite stalks on a finite sober
-- space `Y`. On `Y`, the canonical map into the product of the skyscraper sheaves
-- `∏_{y ∈ Y} i_{y, *} \underline{\mathcal G_y}` is monic. Pull this embedding back along the
-- spectral map `X ⟶ Y`; the inverse images of the point closures in `Y` are constructible closed
-- subsets of `X`, and the corresponding finite stalk sets give the required finite product.
/-- Lemma 17.19.4: a set-valued sheaf on a spectral space satisfying the finite coequalizer
presentation from `17.19.2.1` on quasi-compact opens embeds into a finite product of pushforwards
of constant finite sheaves from constructible closed subsets. -/
theorem exists_mono_to_finite_product_of_constructible_closed_pushforward_constant_sheaves
    [SpectralSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    (ℱ : Sh(X))
    (hℱ :
      HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn
        (fun U ↦ IsCompact (U : Set X)) ℱ) :
    ∃ (ι : Type u) (_ : Fintype ι) (Z : ι → Closeds X)
      (hZ_constructible : ∀ a, IsConstructible (Z a : Set X))
      (A : ι → Type u) (hA_finite : ∀ a, Finite (A a)),
      let factor : Closeds X → Type u → Sh(X) := fun Z A ↦
        (Sheaf.pushforward (Type u) i[Z]).obj
          ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
              (Type u)).obj A)
      ∃ φ : ℱ ⟶ ∏ᶜ fun a : ι ↦ factor (Z a) (A a),
        Mono φ := sorry

end
