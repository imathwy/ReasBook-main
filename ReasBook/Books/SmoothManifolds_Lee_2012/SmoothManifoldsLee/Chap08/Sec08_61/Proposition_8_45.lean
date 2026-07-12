import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_61.Definition_8_61_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff ContMDiffMonoidMorphism

universe u𝕜 uEG uHG uG uEH uHH uH uEK uHK uK

-- Domain sampling pass:
-- * source-facing layer here: identities, composites, and Lie-group-isomorphism invariance for
--   induced Lie algebra maps;
-- * core/canonical owners: `ContMDiffMonoidMorphism` for smooth homomorphisms and
--   `LieGroupIsomorphism` for smooth group isomorphisms;
-- * derived API below: functoriality of
--   `inducedLieAlgebraHomomorphism`, and the induced Lie algebra equivalence of a
--   `LieGroupIsomorphism`.
-- The owner-level `ContMDiffMonoidMorphism.id/comp` API already lives upstream in
-- `Definition_7_47_extra_1`, so this file reuses it directly.

section LieGroupInducedHomomorphisms

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {EK : Type uEK} [NormedAddCommGroup EK] [NormedSpace 𝕜 EK] [CompleteSpace EK]
variable {HK : Type uHK} [TopologicalSpace HK]
variable {I : ModelWithCorners 𝕜 EG HG}
variable {J : ModelWithCorners 𝕜 EH HH}
variable {K : ModelWithCorners 𝕜 EK HK}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable {K' : Type uK} [Group K'] [TopologicalSpace K'] [ChartedSpace HK K']
variable [LieGroup I (minSmoothness 𝕜 3) G]
variable [LieGroup J (minSmoothness 𝕜 3) H]
variable [LieGroup K (minSmoothness 𝕜 3) K']

namespace ContMDiffMonoidMorphism

/-- Proposition 8.45 (1): the Lie algebra homomorphism induced by the identity map of a Lie group
is the identity of the Lie algebra. -/
@[simp] theorem id_inducedLieAlgebraHomomorphism :
    ((ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism I I ∞ G G))_* = 1 := sorry

/-- Proposition 8.45 (2): the Lie algebra homomorphism induced by a composite of Lie group
homomorphisms is the composite of the induced Lie algebra homomorphisms. -/
@[simp] theorem inducedLieAlgebraHomomorphism_comp
    (F₂ : ContMDiffMonoidMorphism J K ∞ H K')
    (F₁ : ContMDiffMonoidMorphism I J ∞ G H) :
    (F₂.comp F₁)_* = ((F₂)_*).comp ((F₁)_*) := sorry

end ContMDiffMonoidMorphism

namespace LieGroupIsomorphism

local notation "LieGroupIso" => _root_.LieGroupIsomorphism I J G H
open ContMDiffMonoidMorphism (comp)

@[simp] theorem symmToContMDiffMonoidMorphism_comp_toContMDiffMonoidMorphism
    (F : LieGroupIso) :
    comp F.symm.toContMDiffMonoidMorphism F.toContMDiffMonoidMorphism =
      (ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism I I ∞ G G) := sorry

@[simp] theorem toContMDiffMonoidMorphism_comp_symmToContMDiffMonoidMorphism
    (F : LieGroupIso) :
    comp F.toContMDiffMonoidMorphism F.symm.toContMDiffMonoidMorphism =
      (ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism J J ∞ H H) := sorry

@[simp] theorem symm_inducedLieAlgebraHomomorphism_comp
    (F : LieGroupIso) :
    ((F.symm.toContMDiffMonoidMorphism)_*).comp ((F.toContMDiffMonoidMorphism)_*) = 1 := by
  calc
    ((F.symm.toContMDiffMonoidMorphism)_*).comp ((F.toContMDiffMonoidMorphism)_*) =
      (comp F.symm.toContMDiffMonoidMorphism F.toContMDiffMonoidMorphism)_* := by
        symm
        exact ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism_comp
          F.symm.toContMDiffMonoidMorphism F.toContMDiffMonoidMorphism
    _ = ((ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism I I ∞ G G))_* := by
        rw [symmToContMDiffMonoidMorphism_comp_toContMDiffMonoidMorphism]
    _ = 1 := ContMDiffMonoidMorphism.id_inducedLieAlgebraHomomorphism

@[simp] theorem inducedLieAlgebraHomomorphism_comp_symm
    (F : LieGroupIso) :
    ((F.toContMDiffMonoidMorphism)_*).comp ((F.symm.toContMDiffMonoidMorphism)_*) = 1 := by
  calc
    ((F.toContMDiffMonoidMorphism)_*).comp ((F.symm.toContMDiffMonoidMorphism)_*) =
      (comp F.toContMDiffMonoidMorphism F.symm.toContMDiffMonoidMorphism)_* := by
        symm
        exact ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism_comp
          F.toContMDiffMonoidMorphism F.symm.toContMDiffMonoidMorphism
    _ = ((ContMDiffMonoidMorphism.id : ContMDiffMonoidMorphism J J ∞ H H))_* := by
        rw [toContMDiffMonoidMorphism_comp_symmToContMDiffMonoidMorphism]
    _ = 1 := ContMDiffMonoidMorphism.id_inducedLieAlgebraHomomorphism

/-- Proposition 8.45 (3): a Lie group isomorphism induces an isomorphism of Lie algebras. -/
noncomputable def inducedLieAlgebraEquiv (F : LieGroupIso) :
    GroupLieAlgebra I G ≃ₗ⁅𝕜⁆ GroupLieAlgebra J H :=
  { ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism F.toContMDiffMonoidMorphism with
    invFun :=
      ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism F.symm.toContMDiffMonoidMorphism
    left_inv := by
      intro X
      exact DFunLike.congr_fun
        (symm_inducedLieAlgebraHomomorphism_comp F) X
    right_inv := by
      intro Y
      exact DFunLike.congr_fun
        (inducedLieAlgebraHomomorphism_comp_symm F) Y }

end LieGroupIsomorphism

end LieGroupInducedHomomorphisms
