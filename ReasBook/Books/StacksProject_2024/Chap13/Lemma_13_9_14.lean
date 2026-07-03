import Mathlib
import StacksProject_2024.Chap13.Lemma_13_4_7
import StacksProject_2024.Chap13.Lemma_13_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.9.14:
- primary domain: homotopy-category triangles of cochain complexes, mapping cones, and
  degreewise split short complexes;
- sampled owner declarations:
  `CochainComplex.mappingCone.triangleh`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.splitMonoFactorizationShortComplex`,
  `CochainComplex.splitMonoFactorizationSplitting`,
  `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`,
  `CategoryTheory.exists_iso_of_arrow_iso`,
  `HomotopyCategory.isoOfHomotopyEquiv`;
- best owner abstraction: the source-facing public content is the existence of a comparison
  isomorphism between the owner triangles `mappingCone.triangleh S.f` and
  `trianglehOfDegreewiseSplit S σ`, with identity first two components; that comparison should be
  exposed through the chapter-level uniqueness theorem for distinguished triangles with fixed first
  morphism, not as a chosen public witness. For part (2), the primitive source-facing data are the
  canonical split-mono factorization short complex and its degreewise splitting from
  Lemma 13.9.6, not a second local recreation of that owner-level data;
- source/core/bridge triage:
  `source-facing`: the comparison between the mapping-cone triangle of `f` and a triangle coming
    from a degreewise split short complex;
  `core/canonical`: the owner triangles `mappingCone.triangleh S.f` and
    `trianglehOfDegreewiseSplit S σ`;
  `bridge/view`: the existence statement for the owner triangle comparison in part (1), and the
    specialization in part (2) of the canonical distinguished-triangle bridge to a mapping-cone
    triangle.
- primitive data: for part (1), the short complex `S` and its degreewise splitting family `σ`;
  for part (2), the short complex `splitMonoFactorizationShortComplex f` together with
  `splitMonoFactorizationSplitting f`;
- derived API: any concrete witness for the comparison in part (1), used only internally, and the
  resulting triangle comparison in part (2). -/

-- Proof sketch: both triangles are distinguished and have the same first morphism, so the
-- comparison follows from the chapter-level uniqueness theorem for distinguished triangles with
-- fixed first morphism. Any homotopy equivalence between `mappingCone S.f` and `S.X₃` is then
-- derived from a locally chosen witness, not exported as public data.
/-- Lemma 13.9.14 (1): for a degreewise split short complex of cochain complexes, the standard
mapping-cone triangle of its first map is isomorphic to the triangle in `K(\mathcal A)` attached
to the degreewise split sequence, through the identity on the first two vertices. -/
theorem exists_mappingCone_triangleh_iso_of_degreewiseSplit
    (S : ShortComplex (CochainComplex 𝒜 ℤ))
    (σ : ∀ n, (S.map (eval 𝒜 _ n)).Splitting) :
    ∃ e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ,
      e.hom.hom₁ = 𝟙 ((Q).obj S.X₁) ∧
        e.hom.hom₂ = 𝟙 ((Q).obj S.X₂) := by
  simpa [CochainComplex.triangleOfDegreewiseSplit] using
    (CategoryTheory.exists_distinguished_triangle_unique_up_to_iso
      (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
      (by
        rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
        exact ⟨S, σ, ⟨Iso.refl _⟩⟩))

-- Proof sketch: apply part (1) to the canonical short complex
-- `splitMonoFactorizationShortComplex f` and then compare
-- `mappingCone.triangleh (splitMonoFactorizationι f)` with `mappingCone.triangleh f` using the
-- projection homotopy equivalence from Lemma 13.9.6.
/-- Companion clause (2): the canonical degreewise split short complex
`splitMonoFactorizationShortComplex f` yields a triangle in `K(\mathcal A)` isomorphic to
the standard mapping-cone triangle of `f`, through the identity on the first vertex. -/
theorem exists_degreewiseSplit_triangleh_iso_mappingCone
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) :
    ∃ e :
        trianglehOfDegreewiseSplit
          (splitMonoFactorizationShortComplex f)
          (splitMonoFactorizationSplitting f) ≅
        mappingCone.triangleh f,
      e.hom.hom₁ = 𝟙 ((Q).obj K) := by
  obtain ⟨eSplit, heSplit₁, _heSplit₂⟩ :=
    exists_mappingCone_triangleh_iso_of_degreewiseSplit
      (splitMonoFactorizationShortComplex f)
      (splitMonoFactorizationSplitting f)
  let pIso :
      (Q).obj (splitMonoFactorizationObj K L) ≅ (Q).obj L :=
    HomotopyCategory.isoOfHomotopyEquiv (splitMonoFactorizationProjectionHomotopyEquiv K L)
  obtain ⟨eMap, heMap₁, _heMap₂⟩ :=
    exists_iso_of_arrow_iso
      (mappingCone.triangleh (splitMonoFactorizationι f))
      (mappingCone.triangleh f)
      (HomotopyCategory.mappingCone_triangleh_distinguished (splitMonoFactorizationι f))
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Arrow.isoMk (Iso.refl _) pIso (by
        dsimp [pIso, splitMonoFactorizationProjectionHomotopyEquiv]
        simp only [Category.id_comp]
        rw [← Functor.map_comp, splitMonoFactorizationι_comp_fst]))
  refine ⟨eSplit.symm ≪≫ eMap, ?_⟩
  change eSplit.inv.hom₁ ≫ eMap.hom.hom₁ = 𝟙 ((Q).obj K)
  have hInv : eSplit.inv.hom₁ = 𝟙 ((Q).obj K) := by
    simpa [heSplit₁] using Iso.inv_hom_id_triangle_hom₁ eSplit
  simpa [hInv, heMap₁]

end CochainComplex
