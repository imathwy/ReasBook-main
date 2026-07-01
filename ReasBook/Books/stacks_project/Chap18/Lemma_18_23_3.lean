import Mathlib
import stacks_project.Chap18.Definition_18_17_1
import stacks_project.Chap18.Definition_18_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ V : Over U, ((J.over U).over V).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/- Domain-style sampling for Lemma 18.23.3:
- primary domain: local module-theoretic properties of sheaves of modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory` from `Definition_18_23_1`,
  `SheafOfModules.RingedSite.IsLocallyGeneratedBySections`,
  `SheafOfModules.RingedSite.IsFiniteType`,
  `SheafOfModules.RingedSite.IsQuasicoherent`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction:
  the ambient owner category `ringedSiteModuleCategory J 𝒪` together with the existing
  `SheafOfModules` owner predicates/data on each restriction `ℱ.over U`, and the
  source-facing ringed-site owners from `Definition_18_23_1` for the corresponding
  localized ringed sites;
- primitive data:
  a covering family of the terminal object and the corresponding owner-level property on each
  restriction `ℱ.over (X i)`;
- derived API:
  the fifteen local-on-the-base equivalences stated below.

Source/core/bridge triage:
- `source-facing`: the local-on-the-base criteria in Stacks Lemma 18.23.3;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsLocallyGeneratedBySections`,
  `SheafOfModules.RingedSite.IsFiniteType`,
  `SheafOfModules.RingedSite.IsQuasicoherent`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `SheafOfModules.IsFree`,
  `SheafOfModules.IsFiniteFree`,
  `SheafOfModules.IsGeneratedBy`,
  `SheafOfModules.LocalGeneratorsData`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFinitePresentation`;
- `bridge/view`: the restriction operation `ℱ.over (X i)` to localized ringed sites.

Accordingly, this file reuses the owner `ringedSiteModuleCategory` imported from
`Definition_18_23_1` and does not redeclare parallel aliases such as `ringedSiteRingSheaf` or
`localizedModuleCategory`. -/

-- Proof sketch: for `→`, local freeness is already local on a cover, so restrict the chosen local
-- trivializations further along the induced covers. For `←`, a cover by locally free
-- restrictions is exactly the data needed to witness that `ℱ` is locally free.
/-- Lemma 18.23.3 (1): `\mathcal F` is locally free if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is locally free. -/
theorem isLocallyFree_iff_exists_cover_isLocallyFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyFree M := sorry

-- Proof sketch: the forward direction refines the local trivializing cover from the definition of
-- local freeness. For the reverse direction, free restrictions are in particular locally free, so
-- the preceding local criterion applies.
/-- Lemma 18.23.3 (2): `\mathcal F` is locally free if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is free. -/
theorem isLocallyFree_iff_exists_cover_isFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFree (ℱ.over (X i)) := sorry

-- Proof sketch: as in the locally free case, finite local freeness is stable under restriction and
-- can be checked on a covering family of the terminal object.
/-- Lemma 18.23.3 (3): `\mathcal F` is finite locally free if and only if there is a covering of
the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is finite locally
free. -/
theorem isFiniteLocallyFree_iff_exists_cover_isFiniteLocallyFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFiniteLocallyFree M := sorry

-- Proof sketch: the given finite free restrictions directly witness finite local freeness after
-- passing to the corresponding cover, and the converse uses the defining finite free local models.
/-- Lemma 18.23.3 (4): `\mathcal F` is finite locally free if and only if there is a covering of
the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is finite free. -/
theorem isFiniteLocallyFree_iff_exists_cover_isFiniteFree_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteLocallyFree ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteFree (ℱ.over (X i)) := sorry

-- Proof sketch: local generators remain local generators after restricting to any over-site, and
-- conversely a cover by restrictions which are locally generated by sections already exhibits the
-- required local generator data for `ℱ`.
/-- Lemma 18.23.3 (5): `\mathcal F` is locally generated by sections if and only if there is a
covering of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is
locally generated by sections. -/
theorem isLocallyGeneratedBySections_iff_exists_cover_isLocallyGeneratedBySections_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyGeneratedBySections ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyGeneratedBySections M := sorry

-- Proof sketch: if `ℱ` is locally generated by sections, refine the local-generator cover to one
-- where the restrictions are globally generated. Conversely, global generators on a covering
-- family give local generators by definition.
/-- Lemma 18.23.3 (6): `\mathcal F` is locally generated by sections if and only if there is a
covering of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is
globally generated by sections. -/
theorem isLocallyGeneratedBySections_iff_exists_cover_isGloballyGenerated_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsLocallyGeneratedBySections ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty (ℱ.over (X i)).GeneratingSections := sorry

-- Proof sketch: local generation by `r` sections is preserved by restriction, and a cover by
-- restrictions which are locally generated by `r` sections is exactly the local data demanded by
-- the definition.
/-- Lemma 18.23.3 (7): for a fixed `r : ℕ`, `\mathcal F` is locally generated by `r` sections if
and only if there is a covering of the terminal object such that each restriction
`\mathcal F|_{\mathcal C / X_i}` is locally generated by `r` sections. -/
theorem isLocallyGeneratedBy_iff_exists_cover_isLocallyGeneratedBy_over
    (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) :
    IsLocallyGeneratedBy ℱ r ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsLocallyGeneratedBy M r := sorry

-- Proof sketch: a local surjection `\mathcal O_U^{\oplus r} \to \mathcal F|_U` on a further
-- cover yields global generation by `r` sections on each member of that cover, and the converse
-- is immediate from the definition of local generation by `r` sections.
/-- Lemma 18.23.3 (8): for a fixed `r : ℕ`, `\mathcal F` is locally generated by `r` sections if
and only if there is a covering of the terminal object such that each restriction
`\mathcal F|_{\mathcal C / X_i}` is globally generated by `r` sections. -/
theorem isLocallyGeneratedBy_iff_exists_cover_isGloballyGeneratedBy_over
    (ℱ : ringedSiteModuleCategory J 𝒪) (r : ℕ) :
    IsLocallyGeneratedBy ℱ r ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsGeneratedBy (ℱ.over (X i)) r := sorry

-- Proof sketch: finite type is defined by finite local generator data, so restricting a witness
-- keeps finite type on each over-site; conversely, a covering by finite type restrictions is the
-- local criterion for finite type.
/-- Lemma 18.23.3 (9): `\mathcal F` is of finite type if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is of finite type. -/
theorem isFiniteType_iff_exists_cover_isFiniteType_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteType ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFiniteType M := sorry

-- Proof sketch: finite type means locally generated by finitely many sections, and after choosing
-- a rank on each local piece one obtains the stated owner-level cover; conversely such a cover
-- directly implies finite type.
/-- Lemma 18.23.3 (10): `\mathcal F` is of finite type if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is globally generated
by finitely many sections. -/
theorem isFiniteType_iff_exists_cover_isFiniteGloballyGenerated_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFiniteType ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, SheafOfModules.IsFiniteGloballyGenerated (ℱ.over (X i)) := sorry

-- Proof sketch: quasi-coherent data restricts to quasi-coherent data on every over-site, while a
-- cover by quasi-coherent restrictions is precisely the local criterion built into the definition
-- of quasi-coherence.
/-- Lemma 18.23.3 (11): `\mathcal F` is quasi-coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is quasi-coherent. -/
theorem isQuasicoherent_iff_exists_cover_isQuasicoherent_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsQuasicoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsQuasicoherent M := sorry

-- Proof sketch: by choosing local presentations for a quasi-coherent sheaf and refining along the
-- site axioms, one gets a cover on which each restriction has a global presentation; conversely,
-- these global presentations are exactly the local presentation data needed for quasi-coherence.
/-- Lemma 18.23.3 (12): `\mathcal F` is quasi-coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` has a global
presentation. -/
theorem isQuasicoherent_iff_exists_cover_hasGlobalPresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsQuasicoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty (ℱ.over (X i)).Presentation := sorry

-- Proof sketch: finite presentation on a ringed site is defined by finite local presentations, so
-- it is preserved by restriction and detected on a covering family of the terminal object.
/-- Lemma 18.23.3 (13): `\mathcal F` is of finite presentation if and only if there is a covering
of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is of finite
presentation. -/
theorem isFinitePresentation_iff_exists_cover_isFinitePresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFinitePresentation ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsFinitePresentation M := sorry

-- Proof sketch: finite local presentations refine to a cover by restrictions with finite
-- presentations, and such a cover is exactly the local datum appearing in the definition of finite
-- presentation.
/-- Lemma 18.23.3 (14): `\mathcal F` is of finite presentation if and only if there is a covering
of the terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` has a finite
global presentation. -/
theorem isFinitePresentation_iff_exists_cover_finitePresentation_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFinitePresentation ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I, Nonempty {P : (ℱ.over (X i)).Presentation // P.IsFinite} := sorry

-- Proof sketch: coherence is local on the base in the sense of the source lemma, so restricting a
-- coherent sheaf along a cover keeps coherence; conversely, coherence on a covering family
-- supplies the local criterion for the original sheaf.
/-- Lemma 18.23.3 (15): `\mathcal F` is coherent if and only if there is a covering of the
terminal object such that each restriction `\mathcal F|_{\mathcal C / X_i}` is coherent. -/
theorem isCoherent_iff_exists_cover_isCoherent_over
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsCoherent ℱ ↔
      ∃ (I : Type (max u v)) (X : I → C), J.CoversTop X ∧
        ∀ i : I,
          let M : ringedSiteModuleCategory (J.over (X i)) (𝒪.over (X i)) := ℱ.over (X i)
          IsCoherent M := sorry

end SheafOfModules.RingedSite
