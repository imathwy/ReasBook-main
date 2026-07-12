import Mathlib.Geometry.Manifold.Algebra.LieGroup
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Theorem_5_53
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

universe u𝕜 uH uE uG uE'

-- Semantic recall via `lean_leansearch` did not return a useful manifold-specific hit; the owner
-- choice was fixed by local repository precedent: §7.49 uses `LieSubgroup` as the source-facing
-- notion, while Proposition 7.16 reuses the induced `LieGroup` structure as a helper.

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [LieGroup I (⊤ : WithTop ℕ∞) G]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

/-- Helper for Proposition 7.11: the subtype inclusion of an embedded subgroup is smooth. -/
lemma subgroupSubtypeVal_contMDiff
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    ContMDiff (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) (Subtype.val : S → G) := by
  -- The Chapter 5 embedded-submanifold bridge makes the subtype inclusion smooth.
  simpa using
    subtype_val_contMDiff_of_isSmoothEmbedding
      (I := I) (J := modelWithCornersSelf 𝕜 E') (S := (S : Set G))
      hS.isSmoothEmbedding_subtype_val

/-- Helper for Proposition 7.11: multiplication on an embedded subgroup is smooth in the induced
manifold structure. -/
lemma subgroupMul_codRestrict_eq
    (S : Subgroup G) :
    Set.codRestrict
      (fun p : S × S ↦ (p.1 : G) * (p.2 : G))
      (S : Set G)
      (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)
      =
      (fun p : S × S ↦ p.1 * p.2) := rfl

/-- Helper for Proposition 7.11: multiplication on an embedded subgroup is smooth in the induced
manifold structure. -/
lemma subgroupMul_contMDiff
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞)
      (fun p : S × S ↦ p.1 * p.2) := by
  letI : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G) := hS
  have hfst : ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      I (⊤ : WithTop ℕ∞) fun p : S × S ↦ (p.1 : G) := by
    -- Each projection becomes an ambient smooth map after composing with the subtype inclusion.
    simpa using
      (subgroupSubtypeVal_contMDiff (𝕜 := 𝕜) (I := I) (E' := E') S hS).comp
        (contMDiff_fst :
          ContMDiff
            ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
            (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) fun p : S × S ↦ p.1)
  have hsnd : ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      I (⊤ : WithTop ℕ∞) fun p : S × S ↦ (p.2 : G) := by
    -- The same restriction argument applies to the second projection.
    simpa using
      (subgroupSubtypeVal_contMDiff (𝕜 := 𝕜) (I := I) (E' := E') S hS).comp
        (contMDiff_snd :
          ContMDiff
            ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
            (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) fun p : S × S ↦ p.2)
  have hmulAmbient : ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      I (⊤ : WithTop ℕ∞) fun p : S × S ↦ (p.1 : G) * (p.2 : G) := by
    -- Ambient multiplication is smooth, so the restricted ambient product is smooth as well.
    simpa using hfst.mul hsnd
  have hmulSubtype : ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞)
      (Set.codRestrict
        (fun p : S × S ↦ (p.1 : G) * (p.2 : G))
        (S : Set G)
        (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)) :=
    contMDiff_toSubtype_of_isEmbeddedSubmanifold
      (I := I)
      (J := modelWithCornersSelf 𝕜 E')
      (K := (modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      hmulAmbient
      (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)
  -- Rewrite the codomain-restricted ambient product into the subgroup multiplication.
  rw [subgroupMul_codRestrict_eq (S := S)] at hmulSubtype
  exact hmulSubtype

/-- Helper for Proposition 7.11: inversion on an embedded subgroup is smooth in the induced
manifold structure. -/
lemma subgroupInv_codRestrict_eq
    (S : Subgroup G) :
    Set.codRestrict
      (fun x : S ↦ ((x : G)⁻¹))
      (S : Set G)
      (fun x : S ↦ S.inv_mem x.property)
      =
      (fun x : S ↦ x⁻¹) := rfl

/-- Helper for Proposition 7.11: inversion on an embedded subgroup is smooth in the induced
manifold structure. -/
lemma subgroupInv_contMDiff
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    ContMDiff (modelWithCornersSelf 𝕜 E') (modelWithCornersSelf 𝕜 E')
      (⊤ : WithTop ℕ∞) (fun x : S ↦ x⁻¹) := by
  letI : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G) := hS
  have hinvAmbient : ContMDiff (modelWithCornersSelf 𝕜 E') I
      (⊤ : WithTop ℕ∞) fun x : S ↦ ((x : G)⁻¹) := by
    -- Ambient inversion is smooth after precomposing with the smooth subtype inclusion.
    simpa using
      (subgroupSubtypeVal_contMDiff (𝕜 := 𝕜) (I := I) (E' := E') S hS).inv
  have hinvSubtype : ContMDiff
      (modelWithCornersSelf 𝕜 E') (modelWithCornersSelf 𝕜 E')
      (⊤ : WithTop ℕ∞)
      (Set.codRestrict
        (fun x : S ↦ ((x : G)⁻¹))
        (S : Set G)
        (fun x : S ↦ S.inv_mem x.property)) :=
    contMDiff_toSubtype_of_isEmbeddedSubmanifold
      (I := I)
      (J := modelWithCornersSelf 𝕜 E')
      (K := modelWithCornersSelf 𝕜 E')
      hinvAmbient
      (fun x : S ↦ S.inv_mem x.property)
  -- Rewrite the codomain-restricted ambient inverse into the subgroup inverse.
  rw [subgroupInv_codRestrict_eq (S := S)] at hinvSubtype
  exact hinvSubtype

/-- Helper for Proposition 7.11: an embedded subgroup of a Lie group inherits the induced `C^∞`
Lie-group structure on its carrier. -/
theorem subgroup_lieGroup_of_isEmbeddedSubmanifold
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    LieGroup (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S := by
  -- The Lie-group axioms reduce exactly to smoothness of multiplication and inversion.
  refine
    { contMDiff_mul := subgroupMul_contMDiff (𝕜 := 𝕜) (I := I) (E' := E') S hS
      contMDiff_inv := subgroupInv_contMDiff (𝕜 := 𝕜) (I := I) (E' := E') S hS }

/-- Proposition 7.11. Let `G` be a Lie group, and suppose `H ≤ G` is a subgroup whose carrier is
also an embedded submanifold of `G`. Then `H` is a Lie subgroup of `G`. -/
theorem subgroup_has_lieSubgroup_structure_of_isEmbeddedSubmanifold
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    ∃ K : LieSubgroup.{u𝕜, uE, uH, uG, uE'} (𝕜 := 𝕜) (E := E) (H := H) (G := G) I,
      K.carrier = S := by
  -- Package the induced Lie-group structure together with the immersion of the inclusion.
  let K : LieSubgroup.{u𝕜, uE, uH, uG, uE'} (𝕜 := 𝕜) (E := E) (H := H) (G := G) I := {
    carrier := S
    ModelSpace := E'
    instNormedAddCommGroupModelSpace := inferInstance
    instNormedSpaceModelSpace := inferInstance
    instTopologicalSpaceCarrier := inferInstance
    instChartedSpaceCarrier := inferInstance
    instLieGroupCarrier :=
      subgroup_lieGroup_of_isEmbeddedSubmanifold (𝕜 := 𝕜) (I := I) (E' := E') S hS
    subtype_val_isImmersion := hS.isSmoothEmbedding_subtype_val.isImmersion
  }
  exact ⟨K, rfl⟩

end
