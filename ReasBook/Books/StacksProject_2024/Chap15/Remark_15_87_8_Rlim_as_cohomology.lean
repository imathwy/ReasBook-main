import StacksProject_2024.Chap15.«15_87_1_1»
import StacksProject_2024.Chap19.Proposition_19_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Sheaf

noncomputable section

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat
local notation "NatSite" => (⊥ : GrothendieckTopology ℕ)
private abbrev rightDerivedLimitOnSequentialAbelianGroups (p : ℕ) :
    AbSeq ⥤ AddCommGrpCat :=
  ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)

local notation:max "R^" p:max " lim(" A ")" =>
  Functor.obj (rightDerivedLimitOnSequentialAbelianGroups p) A

/- Domain-style sampling for Remark 15.87.8:
- primary domain: inverse limit on sequential inverse systems of abelian groups, compared with
  sheaf cohomology on the chaotic site of `ℕ`;
- sampled owner declarations:
  `SequentialInverseSystem`,
  `CategoryTheory.Limits.lim`,
  `sheafBotEquivalence`,
  `Sheaf.ΓNatIsoLim`,
  `Sheaf.Γ`,
  `Sheaf.cohomologyFunctor`,
  `Functor.rightDerived`;
- best owner abstraction: the source-facing sheaf-side owner is
  `Sheaf.cohomologyFunctor NatSite p`; the inverse-limit side owner is
  `lim : AbSeq ⥤ AddCommGrpCat`; the passage from inverse systems to sheaves is the bridge
  `(sheafBotEquivalence AddCommGrpCat).inverse`, while `Sheaf.ΓNatIsoLim` is the canonical
  underived comparison identifying global sections with inverse limit on the chaotic site;
- primitive data: the inverse-limit functor, the global-sections functor on the chaotic site, the
  bottom-topology sheaf equivalence, and the sheaf-cohomology owner `Sheaf.cohomologyFunctor`;
- derived API: `Functor.rightDerived`, plus the bridge from right derived global sections to
  `Sheaf.cohomologyFunctor`.

Source/core/bridge triage:
- `source-facing`: the comparison between `R lim` and the sheaf cohomology functors
  `Sheaf.cohomologyFunctor NatSite p` on the chaotic site;
- `core/canonical`: `lim : AbSeq ⥤ AddCommGrpCat` and `Sheaf.cohomologyFunctor NatSite p`;
- `bridge/view`: `(sheafBotEquivalence AddCommGrpCat).inverse`, `Sheaf.ΓNatIsoLim NatSite
  AddCommGrpCat`, and the comparison from right derived global sections to sheaf cohomology. -/

/-- The bottom-topology equivalence identifies global sections of the corresponding sheaf on
`NatSite` with inverse limit on sequential inverse systems of abelian groups. -/
noncomputable def naturalNumbersSiteInverseΓIsoLim :
    (sheafBotEquivalence AddCommGrpCat).inverse ⋙ Sheaf.Γ NatSite AddCommGrpCat ≅
      (lim : AbSeq ⥤ AddCommGrpCat) :=
  Functor.isoWhiskerLeft
      ((sheafBotEquivalence AddCommGrpCat).inverse)
      (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafBotEquivalence AddCommGrpCat).counitIso _ ≪≫
    Functor.leftUnitor _

local instance sheafBotEquivalenceInverse_additive :
    ((sheafBotEquivalence AddCommGrpCat).inverse :
      AbSeq ⥤ Sheaf NatSite AddCommGrpCat).Additive where
  map_add := by
    intro A B f g
    rfl

local instance gammaNatSite_additive :
    (Sheaf.Γ NatSite AddCommGrpCat).Additive :=
  Functor.additive_of_iso (Sheaf.ΓNatIsoLim NatSite AddCommGrpCat).symm

/- The Ext-based sheaf-cohomology owner on `NatSite` is `Sheaf.cohomologyFunctor NatSite`. -/
recall Sheaf.cohomologyFunctor

/-- Bridge/view companion for Remark 15.87.8: the `p`-th right derived functor of inverse limit is
canonically isomorphic to the `p`-th right derived functor of global sections of the corresponding
sheaf on the chaotic site of `ℕ`. -/
noncomputable def rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite
    (p : ℕ) :
    ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p) ≅
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.Γ NatSite AddCommGrpCat).rightDerived p) := by
  refine
    { hom := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.symm.hom p
      inv := NatTrans.rightDerived naturalNumbersSiteInverseΓIsoLim.hom p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        naturalNumbersSiteInverseΓIsoLim.hom
        p).symm
  · simpa using
      (NatTrans.rightDerived_comp
        naturalNumbersSiteInverseΓIsoLim.hom
        naturalNumbersSiteInverseΓIsoLim.symm.hom
        p).symm

/-- Bridge/view companion for Remark 15.87.8: after identifying a sequential inverse system of
abelian groups with its sheaf on the chaotic site of `ℕ`, the right derived functors of global
sections agree with the canonical sheaf-cohomology owner `Sheaf.cohomologyFunctor NatSite`. -/
theorem rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology
    (p : ℕ) :
    IsIsomorphic
      (((sheafBotEquivalence AddCommGrpCat).inverse ⋙
          Sheaf.Γ NatSite AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  sorry

/-- Remark 15.87.8, functor form: the `p`-th right derived functor of inverse limit on sequential
inverse systems of abelian groups is canonically isomorphic to the `p`-th sheaf cohomology functor
of the associated sheaf on the chaotic site of `ℕ`. -/
theorem rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology
    (p : ℕ) :
    IsIsomorphic
      ((lim : AbSeq ⥤ AddCommGrpCat).rightDerived p)
      ((sheafBotEquivalence AddCommGrpCat).inverse ⋙
        Sheaf.cohomologyFunctor NatSite p) := by
  rcases rightDerivedGlobalSectionsOfNaturalNumbersSite_isIsomorphic_toCohomology p with ⟨e⟩
  exact ⟨rightDerivedLimitIsoRightDerivedGlobalSectionsOfNaturalNumbersSite p ≪≫ e⟩

/-- Remark 15.87.8, source-facing object form: for a sequential inverse system `A` of abelian
groups, the object `R^p lim(A)` is canonically isomorphic to the sheaf cohomology
`H^p(\mathbf N, \mathcal F_A)` of the corresponding sheaf on the chaotic site of `ℕ`. -/
theorem rightDerivedLimitObj_isIsomorphic_toNaturalNumbersSiteCohomology
    (A : AbSeq) (p : ℕ) :
    IsIsomorphic
      (R^p lim(A))
      ((Sheaf.cohomologyFunctor NatSite p).obj
        ((sheafBotEquivalence AddCommGrpCat).inverse.obj A)) := by
  rcases rightDerivedLimit_isIsomorphic_toNaturalNumbersSiteCohomology p with ⟨e⟩
  exact ⟨e.app A⟩
