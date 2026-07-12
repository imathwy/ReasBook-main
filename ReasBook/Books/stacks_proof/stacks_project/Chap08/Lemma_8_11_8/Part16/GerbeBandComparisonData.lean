import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part01

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Chap08 Lemma 8 11 8/Part16: the `IsGerbeBand` predicate is exactly the
existence of a local comparison family satisfying conjugation compatibility. -/
theorem isGerbeBand_iff
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v}) :
    IsGerbeBand hAbelian G ↔
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Unfold the source-facing predicate once, so the final packaging proof can use this stable
  -- comparison-data interface without expanding the definition again.
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: a global sheaf together with compatible local
comparisons is exactly a gerbe band for the abelian automorphism sheaves. -/
theorem isGerbeBand_of_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v})
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    IsGerbeBand hAbelian G := by
  -- Move through the explicit predicate API: this keeps final assembly at the comparison-data
  -- layer and leaves the reconstruction theorem as the only remaining mathematical frontier.
  exact (isGerbeBand_iff (𝒮 := 𝒮) hAbelian G).2 ⟨comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: once the global additive sheaf and its compatible
comparison family have been reconstructed, package them as the existential band statement. -/
theorem exists_gerbe_band_of_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v})
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ = comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- The final theorem can now finish by supplying only the reconstructed global sheaf and
  -- comparison data; this helper handles the last predicate packaging step.
  exact
    ⟨G, isGerbeBand_of_comparison (𝒮 := 𝒮) hAbelian G comparison compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: an existential package of a reconstructed global
additive sheaf and compatible comparison family immediately gives the gerbe-band existential. -/
theorem exists_gerbe_band_of_reconstructed_comparison_data
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (data :
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G := by
  -- Peel off the reconstructed datum once, then reuse the comparison-data packaging lemma.
  obtain ⟨G, comparison, compatibility⟩ := data
  exact exists_gerbe_band_of_comparison (𝒮 := 𝒮) hAbelian G comparison compatibility

/-- Helper for Chap08 Lemma 8 11 8/Part16: a gerbe-band sheaf carries a local comparison
family to the canonical abelian automorphism sheaves, compatible with conjugation. -/
theorem comparison_data_of_isGerbeBand
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {G : Sheaf J AddCommGrpCat.{max u v}} (hG : IsGerbeBand hAbelian G) :
    ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
      ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
        comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
          comparison y := by
  -- Project the source-facing predicate through the explicit comparison-data equivalence.
  exact (isGerbeBand_iff (𝒮 := 𝒮) hAbelian G).1 hG

/-- Helper for Chap08 Lemma 8 11 8/Part16: a fixed gerbe-band sheaf exposes the reconstructed
comparison-data package with the same underlying global sheaf. -/
theorem exists_reconstructed_comparison_data_of_band
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {G : Sheaf J AddCommGrpCat.{max u v}} (hG : IsGerbeBand hAbelian G) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Extract the comparison family from the band predicate and repackage it at the explicit
  -- reconstruction-data interface used by the final theorem.
  obtain ⟨comparison, compatibility⟩ :=
    comparison_data_of_isGerbeBand (𝒮 := 𝒮) hAbelian hG
  exact ⟨G, comparison, compatibility⟩

/-- Helper for Chap08 Lemma 8 11 8/Part16: a previously reconstructed gerbe-band existential
can be converted back to the explicit comparison-data interface used by the final reconstruction
frontier. -/
theorem exists_reconstructed_comparison_data_of_gerbe_band
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (band : ∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Destructure the band existential once, then use the fixed-band projection helper above.
  obtain ⟨G, hG⟩ := band
  exact exists_reconstructed_comparison_data_of_band (𝒮 := 𝒮) hAbelian hG

/-- Helper for Chap08 Lemma 8 11 8/Part16: the final gerbe-band existential is equivalent to
exhibiting one global additive sheaf with a conjugation-compatible comparison family. -/
theorem exists_gerbe_band_iff_reconstructed_comparison_data
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) :
    (∃ G : Sheaf J AddCommGrpCat.{max u v}, IsGerbeBand hAbelian G) ↔
      ∃ G : Sheaf J AddCommGrpCat.{max u v},
        ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
          G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
          ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
            comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
              comparison y := by
  -- Forward exposes the comparison family stored in `IsGerbeBand`; backward reuses the existing
  -- packaging helper so the reconstruction frontier remains a single explicit existential.
  constructor
  · intro h
    -- Use the existential projection helper so both directions of the equivalence share the same
    -- explicit reconstruction-data interface.
    exact exists_reconstructed_comparison_data_of_gerbe_band (𝒮 := 𝒮) hAbelian h
  · intro data
    exact exists_gerbe_band_of_reconstructed_comparison_data (𝒮 := 𝒮) hAbelian data

/-- Helper for Chap08 Lemma 8 11 8/Part16: a reconstructed global additive sheaf and a
conjugation-compatible comparison family give exactly the comparison-data package needed by the
remaining reconstruction frontier. -/
theorem exists_reconstructed_comparison_data_of_comparison
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (G : Sheaf J AddCommGrpCat.{max u v})
    (comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
      G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x)
    (compatibility : ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
      comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
        comparison y) :
    ∃ G : Sheaf J AddCommGrpCat.{max u v},
      ∃ comparison : ∀ {U : C} (x : 𝒮.p.Fiber U),
        G.over U ≅ 𝒮.automorphismAddCommSheaf hAbelian x,
        ∀ {U : C} {x y : 𝒮.p.Fiber U} (φ : x ⟶ y),
          comparison x ≪≫ automorphismAddCommSheafConj (𝒮 := 𝒮) hAbelian φ =
            comparison y := by
  -- Keep the final reconstruction interface explicit: later absolute-glueing work only needs to
  -- supply `G`, its comparison family, and the conjugation law.
  exact ⟨G, comparison, compatibility⟩

end CategoryTheory
