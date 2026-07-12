import StacksProject_2024.Chap34.Definition_34_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the coproduct/descent API `Limits.Sigma.desc`,
-- while Chapter 34 fixes `PhCovering` from `Definition_34_8_4` as the source-facing owner for
-- ph covering families.

variable {T : Scheme.{u}} {ι : Type u}

/-- The singleton family over `T` whose sole morphism is the coproduct map `∐ i, X i ⟶ T`. This
is the canonical singleton-family bridge used in Lemma 34.8.7 (2). -/
abbrev sigmaDescSingletonObj (X : ι → Scheme.{u}) : PUnit → Scheme.{u} :=
  fun _ ↦ ∐ X

/-- The unique arrow in the singleton family on the coproduct `∐ i, X i`, namely the coproduct
descent morphism `Sigma.desc π`. -/
abbrev sigmaDescSingletonMap (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T) :
    ∀ p : PUnit, sigmaDescSingletonObj X p ⟶ T :=
  fun _ ↦ Limits.Sigma.desc π

/-- Lemma 34.8.7 (1): for a family of locally finite type morphisms to `T`, being a ph covering is
equivalent to admitting a refinement by some ph covering family. -/
@[stacks 0DET]
theorem phCovering_iff_exists_refinement
    (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T) :
    PhCovering X π ↔
      ∃ (κ : Type u) (Y : κ → Scheme.{u}) (φ : ∀ k, Y k ⟶ T),
        PhCovering Y φ ∧
          ∀ k : κ, ∃ i : ι, ∃ g : Y k ⟶ X i, g ≫ π i = φ k := sorry

/-- Lemma 34.8.7 (2): for a family of locally finite type morphisms to `T`, being a ph covering is
equivalent to the singleton family whose unique arrow is the coproduct map
`∐ i, X i ⟶ T`. -/
@[stacks 0DET]
theorem phCovering_iff_sigmaDesc
    (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T) :
    PhCovering X π ↔
      PhCovering (sigmaDescSingletonObj X) (sigmaDescSingletonMap X π) := sorry

end AlgebraicGeometry
