import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap07.Lemma_7_40_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_3_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_15_2
import StacksProject_2024.stacks_project.Chap19.Theorem_19_7_4
import StacksProject_2024.stacks_project.Chap21.SiteAbelianDerived
import StacksProject_2024.stacks_project.Chap21.Lemma_21_10_5
import StacksProject_2024.stacks_project.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.51.1:
- primary domain: weakly contractible objects of a Grothendieck site and the resulting exactness,
  cohomology-vanishing, and torsor-section consequences;
- sampled owner declarations:
  `GrothendieckTopology.IsWeaklyContractible`,
  `sheafSections`,
  `higherCohomology_isZero_of_vanishingHigherCech_on_cofinal_coverings`,
  `Sheaf.Torsor.isTrivial_iff_nonempty_globalSections`;
- owner abstraction:
  `source-facing`: the three consequences listed in Lemma `21.51.1`;
  `core/canonical`: `J.IsWeaklyContractible U`, `((sheafSections J AddCommGrpCat).obj (op U))`,
    `F.H' p U`, and `Sheaf.Torsor G`;
  `bridge/view`: the Čech-vanishing owners from `21.10.8` and `21.10.9`, and the
    torsor-triviality/global-sections bridge from `21.4.2`.
- primitive data: the site `(C, J)`, the object `U`, and `[J.IsWeaklyContractible U]`;
- derived API: exactness of sections over `U`, vanishing of `F.H' p U` for `p > 0`, and
  nonemptiness of `P.Sections U`.
-/

variable (U : C) [J.IsWeaklyContractible U]

/-- Lemma 21.51.1 (1): if `U` is weakly contractible in the site `(C, J)`, then the
sections functor `F ↦ F(U)` on abelian sheaves is exact. -/
@[stacks 0946]
theorem weaklyContractible_sectionsFunctor_exact :
    exactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v}
      (siteAbelianSectionsFunctor J U) := by
  let ΓU : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
    siteAbelianSectionsFunctor J U
  letI : PreservesFiniteLimits ΓU := by
    -- Proof comment: evaluation of the underlying presheaf at `U` preserves finite limits, so it
    -- is left exact on abelian sheaves.
    simpa [ΓU, siteAbelianSectionsFunctor] using
      siteAbelianSectionsFunctor_preservesFiniteLimits J U
  have hLeft :
      leftExactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} ΓU := by
    simpa [leftExactFunctor_iff] using (inferInstance : PreservesFiniteLimits ΓU)
  have hRight :
      rightExactFunctor (Sheaf J AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} ΓU := by
    refine (functor_rightExact_iff_maps_shortExact_to_exact_epi ΓU).2 ?_
    intro S hS
    have hLeftMap :
        (ComposableArrows.mk₂ (ΓU.map S.f) (ΓU.map S.g)).Exact ∧ Mono (ΓU.map S.f) :=
      (functor_leftExact_iff_maps_shortExact_to_exact_mono ΓU).1 hLeft S hS
    let q :
        ((sheafCompose J (forget AddCommGrpCat.{max u v})).obj S.X₂) ⟶
          ((sheafCompose J (forget AddCommGrpCat.{max u v})).obj S.X₃) :=
      (sheafCompose J (forget AddCommGrpCat.{max u v})).map S.g
    have hqLoc : Sheaf.IsLocallySurjective q := by
      have hLoc : Sheaf.IsLocallySurjective S.g :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} S.g).2 hS.epi_g
      -- Proof comment: weak contractibility is stated for set-valued sheaves, so first forget
      -- the additive structure on the locally surjective map `S.g`.
      simpa [q] using
        Functor.underlyingLocallySurjectiveOfAdditiveSheafMap S.g hLoc
    have hsurj := (inferInstance : J.IsWeaklyContractible U).surjective_sections q hqLoc
    have hEpi : Epi (ΓU.map S.g) := by
      -- Proof comment: surjectivity of the underlying function is exactly the `AddCommGrpCat`
      -- criterion for the mapped map to be epic.
      simpa [ΓU, q, sheafSections] using
        (AddCommGrpCat.epi_iff_surjective (ΓU.map S.g)).2 hsurj
    exact ⟨hLeftMap.1, hEpi⟩
  letI : PreservesFiniteColimits ΓU := by
    simpa [rightExactFunctor_iff] using hRight
  exact (exactFunctor_iff ΓU).2 ⟨inferInstance, inferInstance⟩

/-- For a weakly contractible object `U`, the sections functor `Γ(U, -)` on abelian sheaves
preserves finite colimits. -/
instance siteAbelianSectionsFunctor_preservesFiniteColimits_of_isWeaklyContractible :
    PreservesFiniteColimits (siteAbelianSectionsFunctor J U) :=
  (exactFunctor_iff
      (siteAbelianSectionsFunctor J U : Sheaf J AddCommGrpCat.{max u v} ⥤
        AddCommGrpCat.{max u v})).1
    (weaklyContractible_sectionsFunctor_exact U) |>.2

section

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 21.51.1: abelian sheaves on a site admit injective resolutions. -/
private theorem sheaf_has_injective_resolutions :
    HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v}) := by
  let _ : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
    siteAbelianSheaf_hasEnoughInjectives J
  infer_instance

/-- Helper for Lemma 21.51.1: exact short complexes of abelian sheaves remain exact after taking
sections over a weakly contractible object. -/
private theorem sections_over_weakly_contractible_map_exact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}))
    (hS : S.Exact) :
    (S.map (siteAbelianSectionsFunctor J U)).Exact := by
  -- Once `Γ(U,-)` is packaged as an exact functor, `ShortComplex.Exact.map` is the canonical
  -- transport of exactness to sections.
  simpa using hS.map (siteAbelianSectionsFunctor J U)

/-- Helper for Lemma 21.51.1: the sections complex of an injective resolution is exact in every
positive degree. -/
private theorem sections_of_injective_resolution_exact_succ
    (F : Sheaf J AddCommGrpCat.{max u v})
    (I : InjectiveResolution F) (n : ℕ) :
    (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt (n + 1) := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
    ShortComplex.mk
      (I.cocomplex.d n (n + 1))
      (I.cocomplex.d (n + 1) (n + 2))
      (by simpa using I.cocomplex.d_comp_d n)
  have hExact : S.Exact := by
    -- The defining exactness of an injective resolution starts at degree `1`.
    simpa [S] using I.exact_succ n
  -- Apply clause `(1)` to the successor short complex of the injective resolution.
  have hMapped :
      (S.map (siteAbelianSectionsFunctor J U)).Exact :=
    sections_over_weakly_contractible_map_exact U S hExact
  simpa [S, HomologicalComplex.exactAt_iff, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor] using hMapped

/-- Helper for Lemma 21.51.1: positive-degree homology of the sections complex of an injective
resolution vanishes over a weakly contractible object. -/
private theorem sections_of_injective_resolution_homology_isZero_succ
    (F : Sheaf J AddCommGrpCat.{max u v})
    (I : InjectiveResolution F) (n : ℕ) :
    IsZero
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
          (ComplexShape.up ℕ) (n + 1)).obj
        (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  let K :=
    (((siteAbelianSectionsFunctor J U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex)
  have hExactAt : K.ExactAt (n + 1) :=
    sections_of_injective_resolution_exact_succ U F I n
  have hHomology : IsZero (K.homology (n + 1)) := by
    -- Exactness at the relevant degree identifies the homology object with zero.
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExactAt
  simpa [K] using hHomology

variable [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]

-- Proof sketch: clause `(1)` makes `Γ(U, -)` exact on abelian sheaves, so when an injective
-- resolution of `F` is evaluated at `U`, the resulting sections complex is exact in every
-- positive degree. The canonical comparison isomorphism from `F.H' p U` to the corresponding
-- homology object then identifies higher cohomology with zero.
/-- Lemma 21.51.1 (2): if `U` is weakly contractible, then every higher cohomology group
`H^p(U, F)` of an abelian sheaf `F` vanishes for `p > 0`. -/
@[stacks 0946]
theorem weaklyContractible_higherCohomology_isZero
    (F : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := by
  let ΓU := siteAbelianSectionsFunctor J U
  letI : HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v}) :=
    sheaf_has_injective_resolutions
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  let I : InjectiveResolution F := injectiveResolution F
  let K :=
    ((ΓU.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  have hHomology :
      IsZero
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
            (ComplexShape.up ℕ) (n + 1)).obj K) :=
    sections_of_injective_resolution_homology_isZero_succ U F I n
  rcases Sheaf.cohomologyAtObject_isomorphic J U (n + 1) F with ⟨eH'⟩
  let e :
      F.H' (n + 1) U ≅
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
            (ComplexShape.up ℕ) (n + 1)).obj K) :=
    eH'.symm ≪≫
      (by
        simpa [K, ΓU] using
          Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex J I U (n + 1))
  -- The mapped injective resolution has zero homology in every positive degree, and objectwise
  -- cohomology is computed by that homology model.
  simpa [K, ΓU] using IsZero.of_iso hHomology e

end

section

variable {G : Sheaf J GrpCat.{max u v}}

/-- Helper for Lemma 21.51.1: the underlying sheaf of a torsor has its canonical map to the
terminal sheaf. -/
private abbrev torsor_carrier_to_terminal (P : Sheaf.Torsor G) :
    P.carrier ⟶ Sheaf.terminal J Limits.Types.isTerminalPUnit :=
  (Sheaf.isTerminalTerminal J Limits.Types.isTerminalPUnit).from P.carrier

omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 21.51.1: local nonemptiness of a torsor makes its carrier map to the
terminal sheaf locally surjective. -/
private theorem torsor_carrier_to_terminal_isLocallySurjective
    (P : Sheaf.Torsor G) :
    Sheaf.IsLocallySurjective (torsor_carrier_to_terminal P) := by
  change Presheaf.IsLocallySurjective J (torsor_carrier_to_terminal P).hom
  refine Presheaf.IsLocallySurjective.mk ?_
  intro V s
  rcases P.locallyNonempty V with ⟨S, hSJ, hS⟩
  -- Any local section of the torsor maps to the unique section of the terminal sheaf.
  refine J.superset_covering ?_ hSJ
  intro W f hf
  rcases hS f hf with ⟨t⟩
  refine ⟨t, ?_⟩
  simp [torsor_carrier_to_terminal]

end

-- Proof sketch: the structure morphism from the underlying sheaf of sets of a `G`-torsor to the
-- terminal sheaf is locally surjective by local nonemptiness. Weak contractibility of `U`
-- upgrades this local surjectivity to a genuine section over `U`; equivalently, on the localized
-- site at `U`, Lemma `21.4.2` identifies the resulting global section with a trivialization of
-- the restricted torsor.
/- Lemma 21.51.1 (3): if `U` is weakly contractible, then every `G`-torsor on the site
has a section over `U`. -/
omit [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
@[stacks 0946] theorem weaklyContractible_torsor_sections_nonempty
    (G : Sheaf J GrpCat.{max u v}) (P : Sheaf.Torsor G) :
    Nonempty (P.Sections U) := by
  let π := torsor_carrier_to_terminal P
  have hsurj :=
    (inferInstance : J.IsWeaklyContractible U).surjective_sections π
      (torsor_carrier_to_terminal_isLocallySurjective P)
  -- Surjectivity onto the unique terminal section produces the desired section of the torsor.
  rcases hsurj PUnit.unit with ⟨x, hx⟩
  exact ⟨x⟩

end

end CategoryTheory
