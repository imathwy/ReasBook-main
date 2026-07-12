import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap17.Lemma_17_3_1
import StacksProject_2024.Chap15.Lemma_15_59_6
import StacksProject_2024.Chap20.Lemma_20_26_4
import StacksProject_2024.Chap21.Definition_21_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.CochainComplex

noncomputable section

/- Domain-style sampling for Lemma 20.26.7:
- primary domain: K-flat cochain complexes of `𝒪_X`-modules in a short exact sequence of
  complexes on a ringed space;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `AlgebraicGeometry.RingedSpace.isKFlat_iff_stalkwise_isKFlat`,
  `stalkShortComplex`,
  `isKFlat_X₃`;
- best owner abstraction: the primitive owner data are a short complex
  `S : ShortComplex (CochainComplex (RingedSpace.Modules X) ℤ)` together with `hS : S.ShortExact`;
  the three K-flatness conclusions are derived API attached to that owner, not separate ringed
  space wrapper data;
- primitive vs derived: primitive data are only `S`, `hS`, and the termwise flatness hypothesis on
  `S.X₃`; the conclusions that `S.X₁`, `S.X₂`, or `S.X₃` are K-flat are derived theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the short-exact two-out-of-three K-flatness
  statements from the Stacks Project;
- `core/canonical`: `CochainComplex.IsKFlat` and the short-exact owner
  `CategoryTheory.ShortComplex.ShortExact`;
- `bridge/view`: the stalkwise K-flat criterion
  `AlgebraicGeometry.RingedSpace.isKFlat_iff_stalkwise_isKFlat` together with
  `stalkShortComplex`, which reduces the ringed-space statement to the module-valued owner
  theorems `isKFlat_X₁`, `isKFlat_X₂`, and `isKFlat_X₃` on each stalk complex. -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : RingedSpace}
local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "SiteTermwiseFlat" =>
  @IsTermwiseFlat _ _ (Opens.grothendieckTopology X) _ X.sheaf _

variable {S : ShortComplex CpxX}

namespace RingedSpace

/-- Helper for Lemma 20.26.7: the stalk maps of a short complex of `𝒪_X`-modules compose
to zero. -/
private theorem moduleStalkHom_comp_eq_zero
    (S : ShortComplex (RingedSpace.Modules X)) (x : X) :
    RingedSpace.moduleStalkHom x S.f ≫ RingedSpace.moduleStalkHom x S.g = 0 := by
  -- Proof comment: apply the stalk-module functor to the defining relation `S.f ≫ S.g = 0`.
  calc
    RingedSpace.moduleStalkHom x S.f ≫ RingedSpace.moduleStalkHom x S.g =
        RingedSpace.moduleStalkHom x (S.f ≫ S.g) := by
          simpa [RingedSpace.stalkModuleFunctor] using
            ((RingedSpace.stalkModuleFunctor x).map_comp S.f S.g).symm
    _ = RingedSpace.moduleStalkHom x 0 := by rw [S.zero]
    _ = 0 := by
          simpa [RingedSpace.stalkModuleFunctor] using
            (Functor.map_zero (RingedSpace.stalkModuleFunctor x) S.X₁ S.X₃)

/-- Helper for Lemma 20.26.7: the short complex on stalk modules induced by a short complex of
`𝒪_X`-modules. -/
private noncomputable abbrev moduleStalkShortComplex
    (S : ShortComplex (RingedSpace.Modules X)) (x : X) :
    ShortComplex (ModuleCat (X.presheaf.stalk x)) :=
  ShortComplex.mk
    (RingedSpace.moduleStalkHom x S.f)
    (RingedSpace.moduleStalkHom x S.g)
    (moduleStalkHom_comp_eq_zero S x)

/-- Helper for Lemma 20.26.7: exactness of the module-valued stalk short complex follows from the
Chapter 17 stalkwise exactness criterion. -/
private theorem stalkModuleShortComplex_exact
    {S : ShortComplex (RingedSpace.Modules X)} (hS : S.ShortExact) (x : X) :
    (moduleStalkShortComplex S x).Exact := by
  have hstalk :
    (AlgebraicGeometry.RingedSpace.stalkShortComplex S x).Exact :=
    (AlgebraicGeometry.RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).1 hS.exact x
  have hforget :
      ((moduleStalkShortComplex S x).map
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).Exact := by
    simpa [moduleStalkShortComplex, AlgebraicGeometry.RingedSpace.stalkShortComplex,
      RingedSpace.moduleStalkMap] using hstalk
  exact
    ((moduleStalkShortComplex S x).exact_map_iff_of_faithful
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).mp hforget

end RingedSpace

/-- Helper for Lemma 20.26.7: a short exact sequence of `𝒪_X`-modules induces a short
exact sequence on each stalk module. -/
private theorem stalkModuleShortExact
    {S : ShortComplex (RingedSpace.Modules X)} (hS : S.ShortExact) (x : X) :
    (RingedSpace.moduleStalkShortComplex S x).ShortExact := by
  let toAbelianSheaf := SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let hExact :
      ∀ T : ShortComplex (RingedSpace.Modules X), T.Exact → (T.map toAbelianSheaf).Exact :=
    fun T hT ↦ (T.exact_map_iff_of_faithful toAbelianSheaf).mpr hT
  letI : toAbelianSheaf.PreservesMonomorphisms :=
    CategoryTheory.Functor.preservesMonomorphisms_of_map_exact toAbelianSheaf hExact
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf hExact
  refine ModuleCat.shortComplex_shortExact (RingedSpace.moduleStalkShortComplex S x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (RingedSpace.stalkModuleShortComplex_exact hS x))
    ?_ ?_
  · have hmono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.f).hom) := by
      letI : Mono S.f := hS.mono_f
      exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
        (Functor.map_mono toAbelianSheaf S.f) x
    simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono
  · have hsurj :
        Function.Surjective
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (toAbelianSheaf.map S.g).hom).hom) := by
      letI : Epi S.g := hS.epi_g
      have hloc :
          TopCat.Presheaf.IsLocallySurjective (toAbelianSheaf.map S.g).hom :=
        (TopCat.Sheaf.isLocallySurjective_iff_epi (toAbelianSheaf.map S.g)).2 <|
          Functor.map_epi toAbelianSheaf S.g
      exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (toAbelianSheaf.map S.g).hom).1 hloc x
    simpa [RingedSpace.moduleStalkMap] using hsurj

section

variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/-- Helper for Lemma 20.26.7: the stalk-complex functor on cochain complexes of
`𝒪_X`-modules. -/
private abbrev stalkComplexFunctor (x : X) :
    CpxX ⥤ CochainComplex (ModuleCat (X.presheaf.stalk x)) ℤ :=
  (RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)

omit [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)] in
/-- Helper for Lemma 20.26.7: mapping a short exact sequence of complexes to stalk complexes
remains short exact. -/
private theorem stalkMapShortExact
    {S : ShortComplex CpxX} (hS : S.ShortExact) (x : X) :
    (S.map (stalkComplexFunctor x)).ShortExact := by
  refine (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map (stalkComplexFunctor x))).2 ?_
  intro n
  have hSn :
      (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
  simpa [stalkComplexFunctor, RingedSpace.moduleStalkShortComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (stalkModuleShortExact hSn x)

omit [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)] in
/-- Helper for Lemma 20.26.7: degreewise flatness of the third term passes to each stalk
complex. -/
private theorem stalkMapTermwiseFlat_X₃
    {S : ShortComplex CpxX}
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n)) (x : X) :
    (S.map (stalkComplexFunctor x)).X₃.IsTermwiseFlat := by
  intro n
  simpa [stalkComplexFunctor, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (SheafOfModules.isFlat_stalk (hFlat₃ n) x)

end

section

variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable [CategoryTheory.Limits.HasZeroObject (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ,
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSpace.Modules X))]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ, HomologicalComplex.HasTensor K L]

set_option linter.unusedSectionVars false in
/-- Helper for Lemma 20.26.7: K-flatness of the first term passes to each stalk complex. -/
private theorem stalkMap_isKFlat_X₁_of_isKFlat
    {S : ShortComplex CpxX} (hK₁ : S.X₁.IsKFlat) (x : X) :
    (S.map (stalkComplexFunctor x)).X₁.IsKFlat :=
  (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    S.X₁ x).mp
    (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_of_isKFlat S.X₁ hK₁ x)

set_option linter.unusedSectionVars false in
/-- Helper for Lemma 20.26.7: K-flatness of the middle term passes to each stalk complex. -/
private theorem stalkMap_isKFlat_X₂_of_isKFlat
    {S : ShortComplex CpxX} (hK₂ : S.X₂.IsKFlat) (x : X) :
    (S.map (stalkComplexFunctor x)).X₂.IsKFlat :=
  (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    S.X₂ x).mp
    (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_of_isKFlat S.X₂ hK₂ x)

set_option linter.unusedSectionVars false in
/-- Helper for Lemma 20.26.7: K-flatness of the third term passes to each stalk complex. -/
private theorem stalkMap_isKFlat_X₃_of_isKFlat
    {S : ShortComplex CpxX} (hK₃ : S.X₃.IsKFlat) (x : X) :
    (S.map (stalkComplexFunctor x)).X₃.IsKFlat :=
  (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    S.X₃ x).mp
    (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_of_isKFlat S.X₃ hK₃ x)

set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Lemma 20.26.7 (1): in a short exact sequence
`0 ⟶ 𝒦₁ ⟶ 𝒦₂ ⟶ 𝒦₃ ⟶ 0`
of cochain complexes of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, if every
term of `𝒦₃` is flat and `𝒦₁` and `𝒦₂` are K-flat, then `𝒦₃` is K-flat. -/
@[stacks 0G6U]
theorem isKFlat_X₃_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := by
  exact AlgebraicGeometry.RingedSpace.isKFlat_of_stalkComplex_isKFlat S.X₃ <|
    fun x ↦
      (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
        S.X₃ x).mpr <|
        isKFlat_X₃
          (stalkMapShortExact hS x)
          (stalkMapTermwiseFlat_X₃ hFlat₃ x)
          (stalkMap_isKFlat_X₁_of_isKFlat hK₁ x)
          (stalkMap_isKFlat_X₂_of_isKFlat hK₂ x)

set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Canonical termwise-flat companion to Lemma 20.26.7 (1). -/
theorem isKFlat_X₃_of_termwiseFlat
    (hS : S.ShortExact)
    (hFlat₃ : SiteTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := by
  have hFlat₃' : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n) :=
    (isTermwiseFlat_iff S.X₃).1 hFlat₃
  exact isKFlat_X₃_of_flat_X₃ hS hFlat₃' hK₁ hK₂

-- Proof sketch: reduce stalkwise by `isKFlat_iff_stalkwise_isKFlat`, use
-- `stalkShortComplex` for short exactness on stalk
-- complexes, transport flatness of `(S.X₃).X n` to its stalks with `SheafOfModules.isFlat_stalk`,
-- and apply the module-valued owner theorem `isKFlat_X₂`.
set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Lemma 20.26.7 (2): in a short exact sequence
`0 ⟶ 𝒦₁ ⟶ 𝒦₂ ⟶ 𝒦₃ ⟶ 0`
of cochain complexes of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, if every
term of `𝒦₃` is flat and `𝒦₁` and `𝒦₃` are K-flat, then `𝒦₂` is K-flat. -/
@[stacks 0G6U]
theorem isKFlat_X₂_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := by
  exact AlgebraicGeometry.RingedSpace.isKFlat_of_stalkComplex_isKFlat S.X₂ <|
    fun x ↦
      (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
        S.X₂ x).mpr <|
        isKFlat_X₂
          (stalkMapShortExact hS x)
          (stalkMapTermwiseFlat_X₃ hFlat₃ x)
          (stalkMap_isKFlat_X₁_of_isKFlat hK₁ x)
          (stalkMap_isKFlat_X₃_of_isKFlat hK₃ x)

set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Canonical termwise-flat companion to Lemma 20.26.7 (2). -/
theorem isKFlat_X₂_of_termwiseFlat
    (hS : S.ShortExact)
    (hFlat₃ : SiteTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := by
  have hFlat₃' : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n) :=
    (isTermwiseFlat_iff S.X₃).1 hFlat₃
  exact isKFlat_X₂_of_flat_X₃ hS hFlat₃' hK₁ hK₃

set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Lemma 20.26.7 (3): in a short exact sequence
`0 ⟶ 𝒦₁ ⟶ 𝒦₂ ⟶ 𝒦₃ ⟶ 0`
of cochain complexes of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, if every
term of `𝒦₃` is flat and `𝒦₂` and `𝒦₃` are K-flat, then `𝒦₁` is K-flat. -/
@[stacks 0G6U]
theorem isKFlat_X₁_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := by
  exact AlgebraicGeometry.RingedSpace.isKFlat_of_stalkComplex_isKFlat S.X₁ <|
    fun x ↦
      (AlgebraicGeometry.RingedSpace.stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
        S.X₁ x).mpr <|
        isKFlat_X₁
          (stalkMapShortExact hS x)
          (stalkMapTermwiseFlat_X₃ hFlat₃ x)
          (stalkMap_isKFlat_X₂_of_isKFlat hK₂ x)
          (stalkMap_isKFlat_X₃_of_isKFlat hK₃ x)

set_option warn.sorry false in
set_option linter.unusedVariables false in
/-- Canonical termwise-flat companion to Lemma 20.26.7 (3). -/
theorem isKFlat_X₁_of_termwiseFlat
    (hS : S.ShortExact)
    (hFlat₃ : SiteTermwiseFlat S.X₃)
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := by
  have hFlat₃' : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n) :=
    (isTermwiseFlat_iff S.X₃).1 hFlat₃
  exact isKFlat_X₁_of_flat_X₃ hS hFlat₃' hK₂ hK₃

end

end CategoryTheory.ShortComplex.ShortExact
