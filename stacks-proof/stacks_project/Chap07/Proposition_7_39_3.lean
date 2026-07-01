import Mathlib
import stacks_project.Chap07.«7_32_1_1»
import stacks_project.Chap07.Definition_7_38_1
import stacks_project.Chap07.Lemma_7_17_2
import stacks_project.Chap07.Lemma_7_39_2
import stacks_project.Chap07.Proposition_7_33_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Opposite
open GrothendieckTopology
open GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] initiallySmall_of_essentiallySmall

/- Domain-style sampling for Proposition 7.39.3:
- primary domain: enough points on a Grothendieck site, built from point fibers of cofiltered
  inverse systems and the canonical conservative-family criterion;
- sampled owner API:
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `GrothendieckTopology.isConservativePointFamily_iff_exists_point_separating_sections`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `HasFiniteRefinementProperty`;
- source/core/bridge triage:
  `source-facing`: the site-level theorem that the finite-refinement hypothesis implies enough
    points;
  `core/canonical`: `J.HasEnoughPoints` and the owner notion `GrothendieckTopology.Point`;
  `bridge/view`: the separation criterion for conservative families of points and the
    inverse-system fiber construction used to manufacture the required points.

Primitive data are only the finite-limit hypothesis on `C` and the source-facing finite-refinement
assumption `∀ X, J.HasFiniteRefinementProperty X`. Conservative-family packaging and the passage
from a cofiltered inverse system to a point are derived API from the owner layer above, so this
file should stay a thin theorem at the `HasEnoughPoints` owner rather than introducing any local
wrapper around conservative point families or point data.
-/
/-- Helper for Proposition 7.39.3: the raw presheaf fiber map attached to the trivial one-object
inverse system is injective, so distinct sections remain distinct before applying
Lemma 7.39.2. -/
lemma trivial_inverse_system_toPresheafFiber_injective
    {ℱ : Sheaf J (Type (max u v))} (U : C) :
    let I₀ := ULift.{max u v} PUnit
    let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
    let x₀ : (fiber.{max u v} S₀).obj U :=
      fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
    Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj) := by
  let I₀ := ULift.{max u v} PUnit
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  change Function.Injective ((fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj)
  intro s s' hss
  let u₀ : C ⥤ Type (max u v) := fiber.{max u v} S₀
  have hpullback :
      ∃ (Y : C) (f : Y ⟶ U) (y : u₀.obj Y), u₀.map f y = x₀ ∧
        ℱ.obj.map f.op s = ℱ.obj.map f.op s' := by
    -- Compare the two germs by the canonical point-fiber equality criterion.
    simpa [u₀] using
      ((fiber.{max u v} S₀).toPresheafFiber_eq_iff' U x₀ s s').1 hss
  obtain ⟨Y, f, y, hy, hpullback⟩ := hpullback
  -- Represent the witness `y` by an actual stage map in the one-object inverse system.
  obtain ⟨V, g, rfl⟩ := fiberMk_jointly_surjective y
  have hfiberMk :
      fiberMk.{max u v} (g ≫ f) = fiberMk.{max u v} (𝟙 U) := by
    simpa [x₀, u₀] using hy
  -- Since the indexing category has one object, that pullback arrow has a section.
  obtain ⟨W, q, hq⟩ := exists_of_fiberMk_eq_fiberMk (p := S₀) hfiberMk
  have hsection : g ≫ f = 𝟙 U := by
    simpa [S₀] using hq
  -- Apply the section to the pullback equality to recover equality of the original sections.
  calc
    s = ℱ.obj.map (g ≫ f).op s := by simpa [hsection]
    _ = ℱ.obj.map g.op (ℱ.obj.map f.op s) := by simp
    _ = ℱ.obj.map g.op (ℱ.obj.map f.op s') := by rw [hpullback]
    _ = ℱ.obj.map (g ≫ f).op s' := by simp
    _ = s' := by simpa [hsection]

/-- Helper for Proposition 7.39.3: once every finite covering family lifts elements of the fiber
functor, the finite-refinement hypothesis upgrades that to the covering-sieve lifting condition
needed in Proposition 7.33.3. -/
lemma coversLiftToFunctorFibers_of_finite_family_lifting
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
    {ι : Type _} [Preorder ι] [IsDirected ι (· ≤ ·)] [InitiallySmall ιᵒᵖ] (T : ιᵒᵖ ⥤ C)
    (hlift :
      ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{max u v} W) [Finite 𝒰.index],
        𝒰.toSieve ∈ J W →
          ∀ f : (fiber.{max u v} T).obj W,
            ∃ i : 𝒰.index, ∃ y : (fiber.{max u v} T).obj (𝒰.obj i).left,
              (fiber.{max u v} T).map (𝒰.obj i).hom y = f) :
    CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
  intro W R hR f
  -- Refine the arbitrary covering sieve by a finite covering family.
  obtain ⟨𝒱, h𝒱fin, h𝒱, hle⟩ :=
    (hfinite W).finite_refinement (R : Presieve W) (by simpa using hR)
  have hle' : 𝒱.toSieve ≤ R := by
    simpa using hle
  let _ : Finite 𝒱.index := h𝒱fin
  -- The assumed finite-family lifting produces a lift through one member of that refinement.
  obtain ⟨i, y, hy⟩ := hlift (W := W) 𝒱 h𝒱 f
  refine ⟨(𝒱.obj i).left, (𝒱.obj i).hom, ?_, y, hy⟩
  have hi : 𝒱.toSieve (𝒱.obj i).hom := by
    exact (Sieve.le_generate 𝒱.toPresieve) _ _ (Presieve.ofArrows.mk i)
  exact hle' _ hi

/-- Helper for Proposition 7.39.3: every unequal pair of sections of a set-valued sheaf is
separated by the germs at some point obtained from the refinement construction of Lemma 7.39.2. -/
lemma exists_point_separating_sections_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X)
  {ℱ : Sheaf J (Type (max u v))} (U : C) (s s' : ℱ.obj.obj (op U))
    (hs : s ≠ s') :
    ∃ p : GrothendieckTopology.Point.{max u v} J, ∃ x : p.fiber.obj U,
      p.toPresheafFiber U x ℱ.obj s ≠ p.toPresheafFiber U x ℱ.obj s' := by
  let I₀ := ULift.{max u v} PUnit
  letI : IsDirected I₀ (· ≤ ·) := ⟨fun _ _ ↦ ⟨ULift.up PUnit.unit, trivial, trivial⟩⟩
  let S₀ : I₀ᵒᵖ ⥤ C := (Functor.const I₀ᵒᵖ).obj U
  let x₀ : (fiber.{max u v} S₀).obj U :=
    fiberMk (show S₀.obj (op (ULift.up PUnit.unit)) ⟶ U from 𝟙 U)
  let a : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s
  let a' : (sheafToPresheaf J (Type (max u v)) ⋙ (fiber.{max u v} S₀).presheafFiber).obj ℱ :=
    (fiber.{max u v} S₀).toPresheafFiber U x₀ ℱ.obj s'
  have hraw : a ≠ a' := by
    -- The trivial inverse system records the original sections faithfully.
    intro haa'
    exact hs ((trivial_inverse_system_toPresheafFiber_injective (J := J) (ℱ := ℱ) U) haa')
  -- Route correction: keep the source proof's trivial-system-to-refinement architecture rather
  -- than replacing it with a direct conservative-family argument.
  obtain ⟨ι', _, _, T, j, e, hsep, hlift⟩ :=
    exists_refined_inverse_system_separating_sections_and_lifting_all_finite_covers
      (J := J) (S' := S₀) (ℱ := ℱ) (s := a) (s' := a') hraw
  have hcover : CoversLiftToFunctorFibers J (fiber.{max u v} T) := by
    -- Upgrade the finite-cover lifting output of Lemma 7.39.2 to arbitrary coverings.
    exact coversLiftToFunctorFibers_of_finite_family_lifting (J := J) hfinite T hlift
  obtain ⟨p, rfl⟩ :=
    (exists_point_with_fiber_iff_preservesFiniteLimits_and_covering_jointlySurjective
      (J := J) (u := fiber.{max u v} T)).2
      ⟨inferInstance, hcover⟩
  refine ⟨_, (refinementFiber j T e).app U x₀, ?_⟩
  -- The separating raw-fiber inequality is exactly the inequality of germs at the refined point.
  simpa [a, a'] using hsep

/-- Helper for Proposition 7.39.3: once a family of points separates every unequal pair of
sections, Lemma 7.38.3 identifies that family as conservative. -/
lemma section_separating_family_isConservative
    {ι : Type _}
    (p : ι → GrothendieckTopology.Point.{max u v} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s') :
    (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
  -- TODO: re-establish Lemma 7.38.3 in this dependency closure by reconstructing the missing
  -- stalk-faithfulness bridge from separating sections, or repair the broken earlier file
  -- `Lemma_7_38_3.lean` and import its owner theorem here.
  sorry

-- Proof sketch: for any two distinct sections of a sheaf, start with the trivial one-object
-- inverse system at the ambient object and apply Lemma 7.39.2 to obtain a refined inverse system
-- that still separates the sections and whose associated fiber functor is jointly surjective for
-- every finite covering family. The finite-refinement hypothesis upgrades this to all covering
-- families, so Proposition 7.33.3 turns the resulting functor into a point; Lemma 7.38.3 then
-- shows that the resulting family of points is conservative.
/-- Proposition 7.39.3: if finite limits exist in `C` and every covering family in `(C, J)`
admits a finite covering refinement, then `(C, J)` has enough points. -/
theorem hasEnoughPoints_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    J.HasEnoughPoints := by
  classical
  let ι :=
    Σ (ℱ : Sheaf J (Type (max u v))) (U : C),
      { ss : ℱ.obj.obj (op U) × ℱ.obj.obj (op U) // ss.1 ≠ ss.2 }
  let p : ι → GrothendieckTopology.Point.{max u v} J
    | ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩ =>
        Classical.choose <|
          exists_point_separating_sections_of_finite_cover_refinement
            (J := J) (ℱ := ℱ) hfinite U s s' hs
  have hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠
              (p i).toPresheafFiber U x ℱ.obj s' := by
    intro ℱ U s s' hs
    let i : ι := ⟨ℱ, U, ⟨⟨s, s'⟩, hs⟩⟩
    refine ⟨i, ?_⟩
    -- Index the conservative family by all unequal pairs of sections and use the chosen witness.
    simpa [p, i] using
      (Classical.choose_spec <|
        exists_point_separating_sections_of_finite_cover_refinement
          (J := J) (ℱ := ℱ) hfinite U s s' hs)
  have hconservative : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints := by
    -- First record the verified source-faithful frontier: the chosen family is conservative.
    exact section_separating_family_isConservative (J := J) p hsep
  -- Package the conservative family through the owner-level enough-points bridge.
  have hEnough :
      GrothendieckTopology.HasEnoughPoints.{max (max (u + 1) (v + 1)) u v} J := by
    -- The owner theorem accepts a conservative family indexed in the same universe as `ι`.
    exact
    (GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily
      (J := J) (w := max (max (u + 1) (v + 1)) u v)).2 ⟨ι, p, hconservative⟩
  exact hEnough

end CategoryTheory
