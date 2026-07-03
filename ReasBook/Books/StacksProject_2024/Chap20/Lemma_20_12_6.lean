import Mathlib
import StacksProject_2024.Chap20.Lemma_20_11_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {ι κ : Type u}

/-- The open subset obtained by taking an arbitrary union of finite Čech intersections of a
covering `𝒰`. -/
abbrev cech_union_of_finite_intersections
    (𝒰 : ι → Opens X) (s : κ → Σ n : ℕ, Fin (n + 1) → ι) : Opens X :=
  iSup fun k ↦ cech_intersection 𝒰 (s k).2

-- Proof sketch: each finite Čech intersection `U_{i_0 ... i_p}` is contained in every one of its
-- factors, hence in the union of the covering. Taking the supremum over the family `s` preserves
-- this containment.
/-- Any union of finite intersections of the members of `𝒰` is contained in the open set covered
by `𝒰`. -/
theorem cech_union_of_finite_intersections_le_cover
    (U : Opens X) (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U)
    (s : κ → Σ n : ℕ, Fin (n + 1) → ι) :
    cech_union_of_finite_intersections 𝒰 s ≤ U := sorry

-- Proof sketch: follow the textbook reduction to a flasque sheaf on the auxiliary space of
-- nonempty subsets of the index set. The surjectivity hypothesis exactly gives flasqueness of the
-- transported sheaf there, its Čech complex for the basic cover agrees with the Čech complex of
-- `(𝒰, ℱ)`, and Lemma `20.12.4` then forces the positive-degree Čech cohomology to vanish.
/-- Lemma 20.12.6: if every restriction map from `ℱ(U)` to an arbitrary union of finite
intersections of the covering opens is surjective, then the positive-degree Čech cohomology of
the covering with coefficients in `ℱ` vanishes. -/
theorem cech_cohomology_isZero_of_surjective_restrictions_to_unions_of_finite_intersections
    (U : Opens X) (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U)
    (ℱ : X.Sheaf AddCommGrpCat.{u})
    (hres : ∀ {κ : Type u} (s : κ → Σ n : ℕ, Fin (n + 1) → ι),
      Function.Surjective
        (ℱ.1.map (homOfLE (cech_union_of_finite_intersections_le_cover U 𝒰 h𝒰 s)).op))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cech_cohomology 𝒰 ℱ.1 p) := sorry
