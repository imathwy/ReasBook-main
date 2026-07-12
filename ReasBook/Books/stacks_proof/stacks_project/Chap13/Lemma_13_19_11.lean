import Mathlib
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_19_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ComplexShape
  DerivedCategory HomotopyCategory HomologicalComplex

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {E L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: homotopy lifting for bounded-above projective cochain complexes, detected via
  mapping cones, distinguished triangles, and homology-vanishing criteria;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`,
  `DerivedCategory.mappingCone_triangle_distinguished`,
  `Triangle.coyoneda_exact₂`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source complex, while the lift itself is most canonically extracted from the
  distinguished mapping-cone triangle via `Triangle.coyoneda_exact₂`;
- primitive data: the projective-minus source complex `P`, the maps `β : P ⟶ L` and `α : E ⟶ L`,
  the lower-support bound `P.IsStrictlyGE n`, and the homology conditions on `α`;
- derived API: vanishing of maps from `P` to `mappingCone α` in the homotopy category, and the
  resulting lift `γ : P ⟶ E` whose composite with `α` is homotopic to `β`.

Source/core/bridge triage:
- `source-facing`: the lifting statement in this file;
- `core/canonical`: the owner `ProjectiveMinus 𝒜` and the exactness of represented Hom on a
  distinguished triangle via `Triangle.coyoneda_exact₂`;
- `bridge/view`: the mapping-cone reduction from the homology hypotheses on `α` to vanishing of
  `H^i(mappingCone α)` for `i ≥ n`, then to vanishing of maps out of `P` by Lemma `13.19.10`.
-/

/-- If `H^j(α)` is an isomorphism for all `j > n` and an epimorphism for `j = n`, then the
mapping cone of `α` has zero homology in every degree `i ≥ n`. This is the canonical bridge from
the source-facing homology hypotheses on `α` to the mapping-cone vanishing used in
Lemma `13.19.11`. -/
theorem isZero_mappingCone_homology_of_homologyMap_iso_above_and_epi_at
    (α : E ⟶ L) (n i : ℤ)
    (hα_iso : ∀ j : ℤ, n < j → IsIso (homologyMap α j))
    (hα_epi : Epi (homologyMap α n))
    (hi : n ≤ i) :
    IsZero ((mappingCone α).homology i) := by
  let T : Triangle (CochainComplex 𝒜 ℤ) := mappingCone.triangle α
  have hT : Q.mapTriangle.obj T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using DerivedCategory.mappingCone_triangle_distinguished α
  have hmor₁_epi : Epi (homologyMap T.mor₁ i) := by
    by_cases hni : i = n
    · subst hni
      simpa [T] using hα_epi
    · have hni' : n < i := lt_of_le_of_ne hi (fun h ↦ hni h.symm)
      haveI : IsIso (homologyMap α i) := hα_iso i hni'
      simpa [T] using (show Epi (homologyMap α i) by infer_instance)
  have hmor₁_mono : Mono (homologyMap T.mor₁ (i + 1)) := by
    haveI : IsIso (homologyMap α (i + 1)) := hα_iso (i + 1) (by omega)
    simpa [T] using (show Mono (homologyMap α (i + 1)) by infer_instance)
  have hmor₂_zero : homologyMap T.mor₂ i = 0 := by
    exact ((homologyMap_exact₂_of_distTriang T hT i).epi_f_iff).1 hmor₁_epi
  have hδ_zero : homologyδOfTriangle T i (i + 1) rfl = 0 := by
    exact ((homologyMap_exact₁_of_distTriang T hT i (i + 1) rfl).mono_g_iff).1 hmor₁_mono
  simpa [T] using
    (homologyMap_exact₃_of_distTriang T hT i (i + 1) rfl).isZero_X₂ hmor₂_zero hδ_zero
/-- Lemma 13.19.11: let `β : P^• ⟶ L^•` and `α : E^• ⟶ L^•` be morphisms of cochain complexes in
an abelian category, with `P^•` a bounded-above complex of projective objects satisfying
`P^i = 0` for `i < n`. If the induced map on homology `H^i(α)` is an isomorphism for `i > n` and
an epimorphism for `i = n`, then there exists a morphism `γ : P^• ⟶ E^•` such that `α ∘ γ` is
homotopic to `β`. -/
@[stacks 064E]
theorem exists_homotopy_lift_of_bounded_projective_strictlyGE_of_homologyMap_iso_above_and_epi_at
    (P : ProjectiveMinus 𝒜) (α : E ⟶ L)
    (β : (P : CochainComplex 𝒜 ℤ) ⟶ L) (n : ℤ)
    (hP_ge : ((P : CochainComplex 𝒜 ℤ)).IsStrictlyGE n)
    (hα_iso : ∀ i : ℤ, n < i → IsIso (homologyMap α i))
    (hα_epi : Epi (homologyMap α n)) :
    ∃ γ : (P : CochainComplex 𝒜 ℤ) ⟶ E, Nonempty (Homotopy (γ ≫ α) β) := by
  let Ho := HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)
  let T : Triangle (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) := mappingCone.triangleh α
  have hT : T ∈ distTriang (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) := by
    simpa [T] using HomotopyCategory.mappingCone_triangleh_distinguished α
  have hβ_zero : Ho.map β ≫ T.mor₂ = 0 := by
    change Ho.map (β ≫ mappingCone.inr α) = 0
    simpa [Ho] using
      homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
        n hP_ge
        (fun i hi ↦
          isZero_mappingCone_homology_of_homologyMap_iso_above_and_epi_at α n i hα_iso hα_epi hi)
        (Ho.map (β ≫ mappingCone.inr α))
  obtain ⟨γ, hγ⟩ := T.coyoneda_exact₂ hT (Ho.map β) hβ_zero
  obtain ⟨γ, rfl⟩ := Ho.map_surjective γ
  refine ⟨γ, ⟨homotopyOfEq _ _ ?_⟩⟩
  simpa [Ho, T, Functor.map_comp] using hγ.symm

end CochainComplex
