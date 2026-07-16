import StacksProject_2024.stacks_project.Chap34.Definition_34_10_1

open CategoryTheory Limits AlgebraicGeometry

universe u v

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-cover owners
-- `Scheme.affineOpenCover` and `Scheme.OpenCover.affineRefinement`; local Chapter 34 already
-- packages standard `V` coverings of affine schemes as `AffineFamilyOver` with
-- `AffineFamilyOver.IsStandardVCover`. For this item, the source-facing API is therefore cleaner
-- with an affine-family refinement witness than with a second covering owner.

/-- Definition 34.10.7: a family of morphisms `Tᵢ ⟶ T` is a `V` covering if every affine open
`U ⊆ T` admits a standard `V` covering refining the base-changed family
`Tᵢ ×[T] U ⟶ U`. -/
class IsVCovering {I : Type v} (T : Scheme.{u}) (Ti : I → Scheme.{u})
    (f : ∀ i, Ti i ⟶ T) : Prop where
  /-- Every affine open of the target admits a standard `V` covering refining the pullback of the
  original family to that affine open. -/
  affineOpen_refinement :
    ∀ U : T.affineOpens,
      ∃ 𝒱 : AffineFamilyOver U,
        AffineFamilyOver.IsStandardVCover 𝒱 ∧
          ∃ c : Fin 𝒱.n → I,
            ∀ j,
              ∃ φ : 𝒱.U j ⟶ pullback (f (c j)) ((U : T.Opens).ι),
                φ ≫ pullback.snd (f (c j)) ((U : T.Opens).ι) = 𝒱.map j

/-- Over every affine open of the target, a `V` covering admits a standard `V` refinement of the
pulled back family. -/
theorem IsVCovering.exists_affineOpen_refinement
    {I : Type v} {T : Scheme.{u}} {Ti : I → Scheme.{u}} {f : ∀ i, Ti i ⟶ T}
    (h : IsVCovering T Ti f) (U : T.affineOpens) :
    ∃ 𝒱 : AffineFamilyOver U,
      AffineFamilyOver.IsStandardVCover 𝒱 ∧
        ∃ c : Fin 𝒱.n → I,
          ∀ j,
            ∃ φ : 𝒱.U j ⟶ pullback (f (c j)) ((U : T.Opens).ι),
              φ ≫ pullback.snd (f (c j)) ((U : T.Opens).ι) = 𝒱.map j :=
  h.affineOpen_refinement U
