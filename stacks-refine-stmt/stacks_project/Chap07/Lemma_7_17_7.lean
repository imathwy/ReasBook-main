import Mathlib
import stacks_project.Chap07.Definition_7_17_1
import stacks_project.Chap07.Lemma_7_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily.Over

universe z w v u

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C] {U : C}
variable (𝒰 : SemiRepresentableFamily.Over.{v, u, w} U)
variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- Pairwise pullbacks for a covering family provide the canonical pullback object of any two
members of that family. -/
instance (i j : 𝒰.index) : HasPullback (𝒰.obj i).hom (𝒰.obj j).hom := by
  let hpair : 𝒰.toPresieve.HasPairwisePullbacks := inferInstance
  exact hpair.has_pullbacks (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j)

end CategoryTheory.SemiRepresentableFamily.Over

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C}

/-- A covering family of `U` has quasi-compact pairwise overlaps if each canonical overlap
`Uᵢ ×[U] Uⱼ` is quasi-compact. -/
def HasQuasiCompactPairwiseOverlaps (J : GrothendieckTopology C)
    {U : C} (𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U)
    [𝒰.toPresieve.HasPairwisePullbacks] : Prop :=
  ∀ i j : 𝒰.index, J.QuasiCompactObject (Limits.pullback (𝒰.obj i).hom (𝒰.obj j).hom)

/-- Every covering family of `U` is refined by a finite covering family whose pairwise fiber
products exist and are quasi-compact. This is the family-based strengthening of
`HasFiniteRefinementProperty` appearing in Lemma 7.17.7 (4), stated without a global pullback
hypothesis on `C`. -/
class HasCofinalFiniteQuasiCompactOverlapCoverings
    (J : GrothendieckTopology C) (U : C) : Prop where
  finite_refinement
    (𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U)
    (h𝒰 : 𝒰.toSieve ∈ J U) :
    ∃ (𝒱 : SemiRepresentableFamily.Over.{v, u, max u v} U) (_ : Finite 𝒱.index)
      (_ : 𝒱 ⟶ 𝒰) (_ : 𝒱.toPresieve.HasPairwisePullbacks),
      𝒱.toSieve ∈ J U ∧ J.HasQuasiCompactPairwiseOverlaps 𝒱

/-- Forgetting the overlap data recovers the existing finite-refinement owner abstraction. -/
theorem HasCofinalFiniteQuasiCompactOverlapCoverings.hasFiniteRefinementProperty
    (hU : J.HasCofinalFiniteQuasiCompactOverlapCoverings U) :
    HasFiniteRefinementProperty J U := by
  refine
    { finite_refinement := fun R hR ↦ by
        let 𝒰 : SemiRepresentableFamily.Over.{v, u, max u v} U :=
          ofArrows
            (fun i : R.uncurry ↦ i.1.1)
            (fun i ↦ i.1.2)
        have h𝒰toPresieve : 𝒰.toPresieve = R := by
          simpa [𝒰, toPresieve, ofArrows] using presieve_of_uncurry_eq R
        have h𝒰 : 𝒰.toSieve ∈ J U := by
          rw [toSieve, h𝒰toPresieve]
          exact hR
        obtain ⟨𝒱, h𝒱fin, φ, _, h𝒱, _⟩ := hU.finite_refinement 𝒰 h𝒰
        refine ⟨𝒱, h𝒱fin, h𝒱, ?_⟩
        simpa [toSieve, h𝒰toPresieve] using toSieve_le_of_hom φ }

/-- In particular, the overlap hypothesis implies quasi-compactness of `U`. -/
theorem HasCofinalFiniteQuasiCompactOverlapCoverings.quasiCompactObject
    (hU : J.HasCofinalFiniteQuasiCompactOverlapCoverings U) :
    J.QuasiCompactObject U :=
  hasFiniteRefinementProperty_implies_quasiCompactObject hU.hasFiniteRefinementProperty

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory
open CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v z))]
variable {I : Type w} [Category I] [Small.{max u v z} I]

variable [IsFiltered I]

/- Source/core/bridge triage for 7.17.7:
- source-facing owner: `HasCofinalFiniteQuasiCompactOverlapCoverings`
- core/canonical owners: `GrothendieckTopology.HasFiniteRefinementProperty`,
  `GrothendieckTopology.QuasiCompactObject`, and `Limits.colimit.post`
- bridge/view layer in this file: `HasQuasiCompactPairwiseOverlaps` records the source-facing
  overlap hypothesis using the canonical pairwise pullback object
- bridge/view role: the overlap-covering owner implies the finite-refinement and quasi-compactness
  owners, and the four theorem statements below record the Stacks-project consequences for the
  canonical comparison morphism `colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))`
  without introducing a parallel owner for that map
-/

-- Proof sketch: view the presheaf colimit as the underlying presheaf of a separated presheaf when
-- all transition morphisms are monomorphisms, identify the sheaf colimit with its sheafification,
-- and apply injectivity of the map to sheafification for separated presheaves.
/-- Lemma 7.17.7 (1): if all transition morphisms in the filtered diagram are injective, then for
every object `U` the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
injective. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z)))
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) (U : C) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := sorry

-- Proof sketch: if two classes become equal in the sheaf colimit over `U`, then they agree
-- locally on some covering. Quasi-compactness lets one refine to finitely many pieces, choose one
-- common stage of the filtered diagram, and conclude equality already in the presheaf colimit.
/-- Lemma 7.17.7 (2): if `U` is quasi-compact, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
injective. -/
theorem sheafFilteredColimitSectionsComparison_injective_of_quasiCompactObject
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U) :
    Function.Injective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := sorry

-- Proof sketch: combine the injectivity from part (1) on overlaps with quasi-compactness of `U`
-- to choose finitely many local representatives in a common stage; these representatives then
-- glue in that stage sheaf, giving surjectivity, while part (2) gives injectivity.
/-- Lemma 7.17.7 (3): if `U` is quasi-compact and all transition morphisms in the filtered diagram
are injective, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is an
isomorphism. -/
theorem sheafFilteredColimitSectionsComparison_isIso_of_quasiCompactObject_of_transitionMonomorphisms
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C) (hU : J.QuasiCompactObject U)
    (hF : ∀ ⦃i j : I⦄ (f : i ⟶ j), Mono (F.map f)) :
    IsIso (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := sorry

-- Proof sketch: use the assumed cofinal finite cover basis to choose a finite refinement of the
-- local representing cover of a target section. Quasi-compact pairwise pullbacks give eventual
-- agreement on overlaps, so after passing to one stage the local sections glue and produce a
-- preimage; injectivity follows from part (2) because this hypothesis implies `U` is
-- quasi-compact.
/-- Lemma 7.17.7 (4): if every covering family of `U` is refined by a finite covering family
whose pairwise fiber products are quasi-compact, then the canonical map
`\operatorname{colim}_i \mathcal F_i(U) \to (\operatorname{colim}_i \mathcal F_i)(U)` is
bijective. -/
theorem sheafFilteredColimitSectionsComparison_bijective_of_cofinalFiniteQuasiCompactOverlapCoverings
    (F : I ⥤ Sheaf J (Type (max u v z))) (U : C)
    (hU : J.HasCofinalFiniteQuasiCompactOverlapCoverings U) :
    Function.Bijective
      (colimit.post F ((sheafSections J (Type (max u v z))).obj (op U))) := sorry

end CategoryTheory
