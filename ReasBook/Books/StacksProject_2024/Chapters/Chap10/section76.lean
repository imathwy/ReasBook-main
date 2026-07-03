import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Tor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_76_1 (from Chap10) -/
open CategoryTheory CategoryTheory.Limits ModuleCat MonoidalCategory
open Functor.OplaxMonoidal

universe u

instance extendScalars_additive
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Additive where
  map_add := by
    intro X Y g h
    letI := f.toAlgebra
    change ModuleCat.ofHom ((g.hom + h.hom).baseChange S) =
      ModuleCat.ofHom (g.hom.baseChange S + h.hom.baseChange S)
    rw [LinearMap.baseChange_add]

/-
Domain triage:
- `source-facing`: `torBaseChangeHom` is the textbook flat base-change morphism
  `Tor_i^R(M, N) ⊗[R] S → Tor_i^S(M ⊗[R] S, N ⊗[R] S)`.
- `core/canonical`: the owner abstraction is the bifunctor `Tor (ModuleCat R) i`.
- `bridge/view`: the chain-level comparison is the oplax monoidal morphism
  `δ (ModuleCat.extendScalars f) M N`.

Primitive data are only the ring map, the flatness hypothesis, and the two modules. The
comparison map is derived from `Tor` and `extendScalars`; no public wrapper functors are kept.
-/

namespace ModuleCat

/-- The canonical comparison between extending scalars after tensoring with `M` and tensoring with
the extended module `M ⊗[R] S` after extending scalars. -/
noncomputable def extendScalarsTensorLeftNatIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat R) :
    tensorLeft M ⋙ extendScalars f ≅
      extendScalars f ⋙ tensorLeft ((extendScalars f).obj M) :=
  NatIso.ofComponents
    (fun X ↦ (Functor.Monoidal.μIso (extendScalars f) M X).symm)
    (by
      intro X Y g
      exact (Functor.OplaxMonoidal.δ_natural_right (extendScalars f) M g).symm)

end ModuleCat

private noncomputable def torBaseChangeSourceIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
        (((tensorLeft M ⋙ ModuleCat.extendScalars f).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  (ModuleCat.extendScalars f).mapIso ((projectiveResolution N).isoLeftDerivedObj (tensorLeft M) i) ≪≫
    (((((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (projectiveResolution N).complex).sc i).mapHomologyIso
      (ModuleCat.extendScalars f)).symm

private noncomputable def torBaseChangeTargetIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      (((ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
      ((ModuleCat.extendScalars f).obj N)) :=
  letI : (ModuleCat.extendScalars f).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj f)
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  ((ModuleCat.extendScalars f).mapProjectiveResolution (projectiveResolution N)).isoLeftDerivedObj
    (tensorLeft ((ModuleCat.extendScalars f).obj M)) i |>.symm

/-- The canonical flat base-change morphism
`Tor_i^R(M, N) ⊗[R] S → Tor_i^S(M ⊗[R] S, N ⊗[R] S)`. -/
noncomputable def torBaseChangeHom
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ⟶
      (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
      ((ModuleCat.extendScalars f).obj N)) :=
  (torBaseChangeSourceIso f hf M N i).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).map
      ((NatTrans.mapHomologicalComplex
        (ModuleCat.extendScalarsTensorLeftNatIso f M).hom (ComplexShape.down ℕ)).app
          (projectiveResolution N).complex) ≫
    (torBaseChangeTargetIso f hf M N i).hom

/-- Helper for Lemma 10.76.1: applying homology to the chain-level tensor/base-change comparison
produces the middle isomorphism in the `Tor` base-change map. -/
private noncomputable def torBaseChangeMiddleIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M N : ModuleCat R) (i : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      ((Functor.mapHomologicalComplex (tensorLeft M ⋙ ModuleCat.extendScalars f)
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) ≅
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).obj
      ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars f ⋙ tensorLeft ((ModuleCat.extendScalars f).obj M))
          (ComplexShape.down ℕ)).obj (projectiveResolution N).complex) :=
  -- Apply homology to the chain-level natural isomorphism commuting tensor and scalar extension.
  (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) i).mapIso
    ((NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsTensorLeftNatIso f M) (ComplexShape.down ℕ)).app
        (projectiveResolution N).complex)

/-- Helper for Lemma 10.76.1: the flat base-change morphism on `Tor` is the hom of a composite
of the source, middle, and target comparison isomorphisms. -/
private noncomputable def torBaseChangeIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat R) (i : ℕ) :
    (ModuleCat.extendScalars f).obj ((((Tor (ModuleCat R) i).obj M).obj N)) ≅
      (((Tor (ModuleCat S) i).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N)) :=
  -- Compose the two resolution identifications with the homology comparison in the middle.
  torBaseChangeSourceIso f hf M N i ≪≫
    torBaseChangeMiddleIso f M N i ≪≫
      torBaseChangeTargetIso f hf M N i

/-- Lemma 10.76.1: for a flat ring map `f : R →+* S` and `R`-modules `M` and `N`, the canonical
base-change map on `Tor_i` is an isomorphism for every `i`. -/
-- Proof sketch: compute `Tor` from a projective resolution, apply extension of scalars termwise,
-- and use flatness of `f` to preserve the exactness of that resolution after tensoring with `S`.
theorem flat_tor_base_change_map_isIso
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) :
    IsIso (torBaseChangeHom f hf (ModuleCat.of R M) (ModuleCat.of R N) i) := by
  -- Package the source proof's three comparison steps into a single isomorphism.
  have hcomp :
      torBaseChangeHom f hf (ModuleCat.of R M) (ModuleCat.of R N) i =
        (torBaseChangeIso f hf (ModuleCat.of R M) (ModuleCat.of R N) i).hom := by
    -- Unfold both constructions to identify the textbook map with the composite iso morphism.
    dsimp [torBaseChangeHom, torBaseChangeIso, torBaseChangeMiddleIso, NatIso.mapHomologicalComplex]
  -- After rewriting, the goal is the standard fact that the hom of an isomorphism is invertible.
  rw [hcomp]
  exact (torBaseChangeIso f hf (ModuleCat.of R M) (ModuleCat.of R N) i).isIso_hom

/-! ### Lemma_10_76_2 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 10.76.2: tensor the fixed projective resolution of `N` termwise with the
varying left module. -/
private noncomputable def tor_fixed_right_resolution_complex_functor
    (N : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M :=
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (projectiveResolution N).complex
  map f :=
    ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f)
      (ComplexShape.down ℕ)).app (projectiveResolution N).complex)
  map_id M := by
    -- The chain map induced by the identity tensor morphism is the identity.
    ext k
    simp
  map_comp f g := by
    -- Tensoring the fixed resolution is functorial in the left module.
    ext k
    simp

/-- Helper for Lemma 10.76.2: in degree `k`, the fixed-resolution complex functor is just right
tensoring with the `k`-th term of the projective resolution. -/
private noncomputable def tor_fixed_right_resolution_eval_iso
    (N : ModuleCat.{u} R) (k : ℕ) :
    tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k ≅
      tensorRight ((projectiveResolution N).complex.X k) :=
  Iso.refl _

/-- Helper for Lemma 10.76.2: the canonical `Tor` functor with right variable fixed at `N`
identifies with homology of the fixed tensorized projective resolution. -/
private noncomputable def tor_fixed_right_resolution_homology_iso
    (N : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) n).flip.obj N) ≅
      tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n :=
  NatIso.ofComponents
    (fun M ↦ (projectiveResolution N).isoLeftDerivedObj (tensorLeft M) n)
    (fun {X Y} f ↦ by
      -- Compute the `Tor` map from the chosen projective resolution of `N`.
      have h :=
        CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          (((tensoringLeft (ModuleCat.{u} R)).map f))
          (projectiveResolution N) n
      have h' :=
        congrArg
          (fun z ↦ z ≫ ((projectiveResolution N).isoLeftDerivedObj (tensorLeft Y) n).hom)
          h
      simpa [Category.assoc, tor_fixed_right_resolution_complex_functor] using h')

/-- Helper for Lemma 10.76.2: tensoring a fixed projective resolution commutes with filtered
colimits because each degree is right tensoring with a fixed module. -/
private theorem tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (N : ModuleCat.{u} R) :
    PreservesColimitsOfShape J
      (tor_fixed_right_resolution_complex_functor (R := R) N) := by
  -- Check preservation degreewise, then transport from `tensorRight` to `tensorLeft` using the
  -- braiding so that the existing module-colimit instance applies.
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ ?_
  intro k
  let e :
      tensorLeft ((projectiveResolution N).complex.X k) ≅
        tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) k :=
    (BraidedCategory.tensorLeftIsoTensorRight ((projectiveResolution N).complex.X k)) ≪≫
      (tor_fixed_right_resolution_eval_iso (R := R) N k).symm
  exact preservesColimitsOfShape_of_natIso e

/-- Helper for Lemma 10.76.2: the filtered colimit of the tensorized fixed resolution identifies
with the tensorized fixed resolution of the filtered colimit module. -/
private noncomputable def tor_fixed_right_resolution_colimit_iso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) :
    colimit (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N) ≅
      (tor_fixed_right_resolution_complex_functor (R := R) N).obj (colimit F) :=
  letI := tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    (R := R) (J := J) N
  (preservesColimitIso
    (tor_fixed_right_resolution_complex_functor (R := R) N) F).symm

/-- Helper for Lemma 10.76.2: the colimit comparison map for the tensorized fixed resolution is
an isomorphism. -/
private theorem tor_fixed_right_resolution_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) :
    IsIso (colimit.post F (tor_fixed_right_resolution_complex_functor (R := R) N)) := by
  -- The explicit comparison isomorphism is the inverse of `preservesColimitIso`.
  letI := tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    (R := R) (J := J) N
  infer_instance

/-- Helper for Lemma 10.76.2: the categorical colimit of a short-complex diagram agrees with the
short complex obtained by taking colimits componentwise. -/
private noncomputable def shortComplex_diagram_colimit_iso
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ShortComplex (ModuleCat.{u} R)) :
    colimit F ≅ (ShortComplex.colimitCocone F).pt :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F)
    (ShortComplex.isColimitColimitCocone F)

/-- Helper for Lemma 10.76.2: the comparison isomorphism from the categorical colimit of a
short-complex diagram to the pointwise-colimit short complex intertwines the cocone legs. -/
private theorem shortComplex_diagram_colimit_iso_hom_ι
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ShortComplex (ModuleCat.{u} R)) (j : J) :
    colimit.ι F j ≫ (shortComplex_diagram_colimit_iso (R := R) F).hom =
      (ShortComplex.colimitCocone F).ι.app j := by
  exact
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit F)
      (ShortComplex.isColimitColimitCocone F)
      j

/-- Helper for Lemma 10.76.2: the universal stage map into a module colimit is natural in the
diagram. -/
private theorem evaluation_to_colim_naturality
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (j : J) {F G : J ⥤ ModuleCat.{u} R} (α : F ⟶ G) :
    α.app j ≫ colimit.ι G j = colimit.ι F j ≫ colim.map α := by
  simpa using (colimit.ι_map α j).symm

/-- Helper for Lemma 10.76.2: the natural transformation from evaluation at `j` to the colimit
functor whose component on a diagram is the canonical map into its colimit. -/
private noncomputable def module_colimit_evaluation_to_colim
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (j : J) :
    (evaluation J (ModuleCat.{u} R)).obj j ⟶ colim (J := J) (C := ModuleCat.{u} R) where
  app F := colimit.ι F j
  naturality _ _ α := evaluation_to_colim_naturality (R := R) (J := J) j α

/-- Helper for Lemma 10.76.2: the stage cocone map into the pointwise-colimit short complex is
the map induced by the natural transformation from evaluation at `j` to colimit. -/
@[simp]
private theorem shortComplex_colimitCocone_ι_eq_mapNatTrans_module_colimit
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) (j : J) :
    (ShortComplex.colimitCocone
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j =
      T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
  ext <;> rfl

/-- Helper for Lemma 10.76.2: the categorical colimit of the short-complex diagram attached to an
owner short complex identifies with the short complex obtained by applying the module colimit
functor objectwise. -/
private noncomputable def shortComplex_owner_colimit_iso
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    colimit ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) ≅
      T.map (colim (J := J) (C := ModuleCat.{u} R)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
    (ShortComplex.isColimitColimitCocone
      ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))

/-- Helper for Lemma 10.76.2: the owner-side colimit isomorphism intertwines stage cocone maps
with the short-complex maps induced by the canonical stage-to-colimit natural transformation. -/
private theorem shortComplex_owner_colimit_iso_hom_ι
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) (j : J) :
    colimit.ι ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) j ≫
        (shortComplex_owner_colimit_iso (R := R) (J := J) T).hom =
      T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
  have h₁ :
      colimit.ι ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T) j ≫
          (shortComplex_owner_colimit_iso (R := R) (J := J) T).hom =
        (ShortComplex.colimitCocone
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j := by
    exact
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
        (ShortComplex.isColimitColimitCocone
          ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
        j
  have h₂ :
      (ShortComplex.colimitCocone
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)).ι.app j =
        T.mapNatTrans (module_colimit_evaluation_to_colim (R := R) (J := J) j) := by
    simpa using
      (shortComplex_colimitCocone_ι_eq_mapNatTrans_module_colimit
        (R := R) (J := J) T j)
  exact h₁.trans h₂

/-- Helper for Lemma 10.76.2: exactness of filtered colimits in `ModuleCat R` makes the module
colimit functor preserve homology of short complexes. -/
private theorem filtered_colimit_functor_preserves_homology
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)] :
    (colim (J := J) (C := ModuleCat.{u} R)).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  simpa using
    (colim.exact_mapShortComplex (J := J) (C := ModuleCat.{u} R)
      (S := S) (hS := hS)
      (hc₁ := colimit.isColimit S.X₁)
      (c₂ := colimit.cocone S.X₂) (hc₂ := colimit.isColimit S.X₂)
      (c₃ := colimit.cocone S.X₃) (hc₃ := colimit.isColimit S.X₃)
      (f := colim.map S.f) (g := colim.map S.g)
      (hf := by intro j; simp)
      (hg := by intro j; simp))

/-- Helper for Lemma 10.76.2: after precomposing an owner short complex by a functor `x`, the
stagewise relation `f ≫ g = 0` still holds on every presented object. -/
private theorem shortComplex_owner_precomp_comp_eq_zero
    {J : Type v} [Category.{v} J]
    {I : Type v} [Preorder I]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R))
    (i : I) :
    T.f.app (x.obj i) ≫ T.g.app (x.obj i) = 0 := by
  -- Evaluate the owner relation of `T` at the object selected by the presentation functor `x`.
  change ((T.f ≫ T.g).app (x.obj i)) = (0 : T.X₁ ⟶ T.X₃).app (x.obj i)
  simpa only [NatTrans.comp_app, Zero.zero] using
    congrArg (fun α : T.X₁ ⟶ T.X₃ => α.app (x.obj i)) T.zero

/-- Helper for Lemma 10.76.2: the owner short complex obtained after precomposing by `x` is the
canonical module-system short complex for the presented objects and maps. -/
private theorem shortComplex_owner_precomp_eq_module_system_shortComplex
    {J : Type v} [Category.{v} J]
    {I : Type v} [Preorder I]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    let U :=
      (ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj
        (x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
    let hcomp : ∀ i : I, U.f.app i ≫ U.g.app i = 0 := fun i ↦ by
      simpa [U] using shortComplex_owner_precomp_comp_eq_zero (R := R) x T i
    module_system_shortComplex (R := R) (I := I)
      (L := U.X₁) (M := U.X₂) (N := U.X₃) (φ := U.f) (ψ := U.g) hcomp = U := by
  -- The pulled-back owner object is determined by its displayed maps, so reconstruction is
  -- purely structural once we package those maps and the pointwise zero relation.
  cases T
  simp [module_system_shortComplex, ShortComplex.functorEquivalence,
    ShortComplex.FunctorEquivalence.inverse]

/-- Helper for Lemma 10.76.2: after pulling back an owner short complex along a directed
presentation, the resulting homology comparison is the canonical comparison from Lemma 10.8.8. -/
private theorem shortComplex_owner_precomp_canonical_post_eq_module_system_homology_comparison
    {J : Type v} [Category.{v} J]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    let S := x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
    let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
    let U : ShortComplex (I ⥤ ModuleCat.{u} R) := E.inverse.obj S
    let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
      ShortComplex.homologyFunctor (ModuleCat.{u} R)
    let hcomp : ∀ i : I, U.f.app i ≫ U.g.app i = 0 :=
      fun i ↦ shortComplex_owner_precomp_comp_eq_zero (R := R) x T i
    colimit.post (E.functor.obj U) H =
    colimit.post
        ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
          (module_system_shortComplex
            (R := R) (I := I) (L := U.X₁) (M := U.X₂) (N := U.X₃)
            (φ := U.f) (ψ := U.g) hcomp))
        H := by
  let S : I ⥤ ShortComplex (ModuleCat.{u} R) :=
    x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
  let E : ShortComplex (I ⥤ ModuleCat.{u} R) ≌ I ⥤ ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.functorEquivalence I (ModuleCat.{u} R)
  let U : ShortComplex (I ⥤ ModuleCat.{u} R) := E.inverse.obj S
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let hcomp : ∀ i : I, U.f.app i ≫ U.g.app i = 0 :=
    fun i ↦ shortComplex_owner_precomp_comp_eq_zero (R := R) x T i
  -- Apply the owner reconstruction equality under `colimit.post` instead of asking `rw` to see
  -- through the `FunctorEquivalence` object map.
  change colimit.post (E.functor.obj U) H =
    colimit.post
      ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
        (module_system_shortComplex
          (R := R) (I := I) (L := U.X₁) (M := U.X₂) (N := U.X₃)
          (φ := U.f) (ψ := U.g) hcomp))
      H
  have hU :
      U =
        module_system_shortComplex
          (R := R) (I := I) (L := U.X₁) (M := U.X₂) (N := U.X₃)
          (φ := U.f) (ψ := U.g) hcomp := by
    simpa using
      (shortComplex_owner_precomp_eq_module_system_shortComplex
        (R := R) (I := I) (x := x) (T := T)).symm
  cases hU
  rfl

/-- Helper for Lemma 10.76.2: the owner short complex reconstructed from explicit module-system
data has an isomorphic homology comparison map by the same-universe form of Lemma 10.8.8. -/
private theorem module_system_shortComplex_post_isIso
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (L M N : I ⥤ ModuleCat.{u} R)
    (φ : L ⟶ M) (ψ : M ⟶ N)
    (hcomp : ∀ i : I, φ.app i ≫ ψ.app i = 0) :
    IsIso
      (colimit.post
        ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
          (module_system_shortComplex
            (R := R) (I := I) (L := L) (M := M) (N := N)
            (φ := φ) (ψ := ψ) hcomp))
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  -- TODO: `module_system_homology_comparison_isIso` from Lemma 10.8.8 elaborates with a larger
  -- `ModuleCat` universe than this file's explicit `ModuleCat.{u} R`. Add a same-universe adapter
  -- for that theorem, or reprove this special case directly from filtered-colimit preservation of
  -- homology in `ModuleCat.{u} R`.
  sorry

/-- Helper for Lemma 10.76.2: after pulling back an owner short complex along a directed
presentation, the resulting homology comparison is the canonical comparison from Lemma 10.8.8. -/
private theorem shortComplex_owner_precomp_canonical_post_isIso
    {J : Type v} [Category.{v} J]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    let S := x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
    let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
    let U := E.inverse.obj S
    let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
    let hcomp : ∀ i : I, U.f.app i ≫ U.g.app i = 0 :=
      fun i ↦ shortComplex_owner_precomp_comp_eq_zero (R := R) x T i
    IsIso (colimit.post (E.functor.obj U) H) := by
  let S : I ⥤ ShortComplex (ModuleCat.{u} R) :=
    x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
  let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
  let U : ShortComplex (I ⥤ ModuleCat.{u} R) := E.inverse.obj S
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let hcomp : ∀ i : I, U.f.app i ≫ U.g.app i = 0 :=
    fun i ↦ shortComplex_owner_precomp_comp_eq_zero (R := R) x T i
  let L : I ⥤ ModuleCat.{u} R := U.X₁
  let M : I ⥤ ModuleCat.{u} R := U.X₂
  let N₀ : I ⥤ ModuleCat.{u} R := U.X₃
  let φ : L ⟶ M := U.f
  let ψ : M ⟶ N₀ := U.g
  let hcomp' : ∀ i : I, φ.app i ≫ ψ.app i = 0 := fun i ↦ by
    simpa [φ, ψ] using hcomp i
  -- Route correction: first rewrite the owner map to the explicit module-system comparison, then
  -- invoke the same-universe specialization of Lemma 10.8.8 on the displayed data.
  have hrewrite :
      colimit.post (E.functor.obj U) H =
        colimit.post
          ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
            (module_system_shortComplex
              (R := R) (I := I) (L := L) (M := M) (N := N₀)
              (φ := φ) (ψ := ψ) hcomp'))
          (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
    simpa [S, E, U, H, hcomp, L, M, N₀, φ, ψ] using
      (shortComplex_owner_precomp_canonical_post_eq_module_system_homology_comparison
        (R := R) (I := I) (x := x) (T := T))
  dsimp [S, E, U, H, hcomp]
  have hrewrite' :
      colimit.post
          ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
            ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj
              (x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))))
          (ShortComplex.homologyFunctor (ModuleCat.{u} R)) =
        colimit.post
          ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
            (module_system_shortComplex
              (R := R) (I := I) (L := L) (M := M) (N := N₀)
              (φ := φ) (ψ := ψ) hcomp'))
          (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
    simpa [S, E, U, H, hcomp] using hrewrite
  have hcanonical :
      IsIso
        (colimit.post
          ((ShortComplex.functorEquivalence I (ModuleCat.{u} R)).functor.obj
            (module_system_shortComplex
              (R := R) (I := I) (L := L) (M := M) (N := N₀)
              (φ := φ) (ψ := ψ) hcomp'))
          (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
    simpa [L, M, N₀, φ, ψ] using
      (module_system_shortComplex_post_isIso
        (R := R) (I := I) (L := L) (M := M) (N := N₀)
        (φ := φ) (ψ := ψ) hcomp')
  simpa [hrewrite'] using hcanonical

/-- Helper for Lemma 10.76.2: the counit of `ShortComplex.functorEquivalence` transports the
owner-side `colimit.post` map for a precomposed diagram to the concrete pulled-back diagram. -/
private theorem shortComplex_owner_precomp_post_transport
    {J : Type v} [Category.{v} J]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    let S := x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
    let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
    let U := E.inverse.obj S
    let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
    let ε : E.functor.obj U ≅ S := E.counitIso.app S
    colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H =
      colimit.post (E.functor.obj U) H ≫ H.map (colim.map ε.hom) := by
  -- This is the right-whiskered naturality identity for `colimit.post` applied to the counit.
  dsimp
  let S := x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
  let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
  let U := E.inverse.obj S
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj U ≅ S := E.counitIso.app S
  simpa only [S, E, U, H, ε]
    using
      (colimit.map_post (F := E.functor.obj U) (G := S) (α := ε.hom) H).symm

/-- Helper for Lemma 10.76.2: after pulling back an owner short complex along a directed
presentation, the resulting homology comparison is the canonical comparison from Lemma 10.8.8. -/
private theorem shortComplex_owner_precomp_post_isIso
    {J : Type v} [Category.{v} J]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (x : I ⥤ J)
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    IsIso
      (colimit.post
        (x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T))
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let S := x ⋙ ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
  let E := ShortComplex.functorEquivalence I (ModuleCat.{u} R)
  let U : ShortComplex (I ⥤ ModuleCat.{u} R) := E.inverse.obj S
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj U ≅ S := E.counitIso.app S
  have hcanonical :
      IsIso (colimit.post (E.functor.obj U) H) :=
    shortComplex_owner_precomp_canonical_post_isIso
      (R := R) (I := I) (x := x) T
  have hmap :
      IsIso (H.map (colim.map ε.hom)) := by
    infer_instance
  -- Route correction: transport the canonical owner comparison across the counit rather than
  -- forcing a definitional equality with the pulled-back diagram.
  have hcomp :
      IsIso (colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H) := by
    rw [shortComplex_owner_precomp_post_transport (R := R) (I := I) (x := x) T]
    simpa [S, E, U, H, ε] using CategoryTheory.IsIso.comp_isIso' hcanonical hmap
  exact IsIso.of_isIso_comp_left
    (colim.map (Functor.whiskerRight ε.hom H))
    (colimit.post S H)

/-- Helper for Lemma 10.76.2: once the filtered diagram is presented by a final functor from a
directed preorder, the owner-side homology comparison is exactly Lemma 10.8.8. -/
private theorem shortComplex_owner_post_isIso_of_final_directed_presentation
    {J : Type v} [Category.{v} J]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (x : I ⥤ J) [x.Final]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    IsIso
      (colimit.post
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let S := (ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  have hprecomp :
      IsIso (colimit.post (x ⋙ S) H) :=
    shortComplex_owner_precomp_post_isIso (R := R) (x := x) T
  have hsource :
      IsIso (H.map (colimit.pre S x)) := by
    infer_instance
  have htarget :
      IsIso (colimit.pre (S ⋙ H) x) := by
    infer_instance
  -- The final functor moves the precomposed comparison back to the original indexing category.
  have hcomp :
      IsIso (colimit.pre (S ⋙ H) x ≫ colimit.post S H) := by
    have hleft :
        IsIso (colimit.post (x ⋙ S) H ≫ H.map (colimit.pre S x)) :=
      CategoryTheory.IsIso.comp_isIso' hprecomp hsource
    rw [colimit.pre_post x S H] at hleft
    exact hleft
  exact IsIso.of_isIso_comp_left (colimit.pre (S ⋙ H) x) (colimit.post S H)

/-- Helper for Lemma 10.76.2: the owner-side comparison is reduced to a final directed
presentation exactly as in the source proof. -/
private theorem shortComplex_owner_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (T : ShortComplex (J ⥤ ModuleCat.{u} R)) :
    IsIso
      (colimit.post
        ((ShortComplex.functorEquivalence J (ModuleCat.{u} R)).functor.obj T)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  letI : EssentiallySmall.{v} J := by
    infer_instance
  letI : FinallySmall.{v} J :=
    CategoryTheory.finallySmall_of_essentiallySmall (J := J)
  obtain ⟨I, hI, hInonempty, hIdir, x, hx⟩ := CategoryTheory.exists_final_from_directed.{v, v, v} J
  letI : PartialOrder I := hI
  letI : Nonempty I := hInonempty
  letI : IsDirectedOrder I := hIdir
  letI : x.Final := hx
  -- TODO: `exists_final_from_directed` currently returns a directed model whose universe does not
  -- come with the `HasColimitsOfShape I (ModuleCat.{u} R)` instance needed by the owner-side
  -- comparison theorem. Supply a same-universe directed presentation, or a transport lemma that
  -- moves the comparison across a larger-universe `ModuleCat` without changing this theorem.
  sorry

/-- Helper for Lemma 10.76.2: the owner short complex attached to the degree-`n` window of the
fixed tensorized resolution satisfies `f ≫ g = 0` at each stage. -/
private theorem tor_fixed_right_resolution_window_owner_comp_eq_zero
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) (i : I) :
    let S :=
      F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
    let T := (ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj S
    T.f.app i ≫ T.g.app i = 0 := by
  -- Evaluate the short-complex relation carried by the owner object at the stage `i`.
  dsimp
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let T := (ShortComplex.functorEquivalence I (ModuleCat.{u} R)).inverse.obj S
  simpa [T] using congrArg (fun α ↦ α.app i) T.zero

/-- Helper for Lemma 10.76.2: rebuilding the owner short complex from its maps recovers the
original owner object. -/
private theorem tor_fixed_right_resolution_window_owner_eq
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (T : ShortComplex (I ⥤ ModuleCat.{u} R))
    (hcomp : ∀ i : I, T.f.app i ≫ T.g.app i = 0) :
    module_system_shortComplex (R := R) (I := I)
      (L := T.X₁) (M := T.X₂) (N := T.X₃) (φ := T.f) (ψ := T.g) hcomp = T := by
  -- The `ShortComplex` structure is determined by its two maps; the proof field is propositional.
  cases T
  simp [module_system_shortComplex]

/-- Helper for Lemma 10.76.2: right-whiskering a diagram map transports `colimit.post` by the
standard `colimit.map_post` identity. -/
private theorem colimit_post_whisker_right_hom
    {I : Type*} [Category I] {C : Type*} [Category C] {D : Type*} [Category D]
    [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    {A B : I ⥤ C} (ε : A ⟶ B) (H : C ⥤ D) :
    colim.map (Functor.whiskerRight ε H) ≫ colimit.post B H =
      colimit.post A H ≫ H.map (colim.map ε) := by
  -- This is exactly the right-whiskered naturality relation of `colimit.post`.
  simpa using (colimit.map_post (F := A) (G := B) (α := ε) H).symm

/-- Helper for Lemma 10.76.2: left-whiskering a functor isomorphism transports `colimit.post`
by naturality on each colimit leg. -/
private theorem colimit_post_whisker_left_iso_hom
    {I : Type*} [Category I] {C : Type*} [Category C] {D : Type*} [Category D]
    [HasColimitsOfShape I C] [HasColimitsOfShape I D]
    (F : I ⥤ C) {G H : C ⥤ D} (e : G ≅ H) :
    colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
      colimit.post F G ≫ (e.app (colimit F)).hom := by
  -- After precomposing with each cocone leg, the claim is exactly naturality of `e`.
  apply colimit.hom_ext
  intro i
  have h₁ :
      colimit.ι (F ⋙ G) i ≫ colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
        (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) := by
    calc
      colimit.ι (F ⋙ G) i ≫ colim.map (Functor.isoWhiskerLeft F e).hom ≫ colimit.post F H =
          (Functor.isoWhiskerLeft F e).hom.app i ≫
            (colimit.ι (F ⋙ H) i ≫ colimit.post F H) := by
        simpa [Category.assoc] using
          (colimit.ι_map_assoc (α := (Functor.isoWhiskerLeft F e).hom)
            (h := colimit.post F H) i)
      _ = (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) := by
        simpa using congrArg
          (fun k ↦ (Functor.isoWhiskerLeft F e).hom.app i ≫ k)
          (colimit.ι_post (F := F) (G := H) i)
  have h₂ :
      (Functor.isoWhiskerLeft F e).hom.app i ≫ H.map (colimit.ι F i) =
        G.map (colimit.ι F i) ≫ (e.app (colimit F)).hom := by
    simpa only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using
      (e.hom.naturality (colimit.ι F i)).symm
  have h₃ :
      G.map (colimit.ι F i) ≫ (e.app (colimit F)).hom =
        colimit.ι (F ⋙ G) i ≫ colimit.post F G ≫ (e.app (colimit F)).hom := by
    simpa [Category.assoc] using congrArg
      (fun k ↦ k ≫ (e.app (colimit F)).hom)
      (colimit.ι_post (F := F) (G := G) i).symm
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 10.76.2: the canonical owner short complex can be rewritten back from a
concrete owner object `T` once the pointwise relation `f ≫ g = 0` is fixed. -/
private theorem tor_fixed_right_resolution_window_owner_eq_symm
    {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    [HasColimitsOfShape I (ModuleCat.{u} R)]
    (T : ShortComplex (I ⥤ ModuleCat.{u} R))
    (hcomp : ∀ i : I, T.f.app i ≫ T.g.app i = 0) :
    T =
      module_system_shortComplex
        (R := R) (I := I) (L := T.X₁) (M := T.X₂) (N := T.X₃) (φ := T.f) (ψ := T.g) hcomp := by
  -- This is exactly the symmetric form of the canonical owner reconstruction lemma.
  symm
  exact tor_fixed_right_resolution_window_owner_eq (R := R) (I := I) T hcomp

/-- Helper for Lemma 10.76.2: the directed-system comparison on the degree-`n` short-complex
window transports the owner-side `colimit.post` map to the concrete diagram using the counit of
`ShortComplex.functorEquivalence`. -/
private theorem tor_fixed_right_resolution_window_owner_transport_eq
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    let S :=
      F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
    let E := ShortComplex.functorEquivalence J (ModuleCat.{u} R)
    let T := E.inverse.obj S
    let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
    let ε : E.functor.obj T ≅ S := E.counitIso.app S
    colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H =
      colimit.post (E.functor.obj T) H ≫ H.map (colim.map ε.hom) := by
  -- Freeze the concrete short-complex diagram and transport the owner comparison in one step.
  dsimp
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let E := ShortComplex.functorEquivalence J (ModuleCat.{u} R)
  let T := E.inverse.obj S
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj T ≅ S := E.counitIso.app S
  -- This is exactly the right-whiskered naturality identity for the typed counit.
  simpa only [S, E, T, H, ε]
    using
      (colimit_post_whisker_right_hom
        (I := J)
        (C := ShortComplex (ModuleCat.{u} R))
        (D := ModuleCat.{u} R)
        ε.hom H)

/-- Helper for Lemma 10.76.2: the directed-system comparison on the degree-`n` short-complex
window is an isomorphism. -/
private theorem tor_fixed_right_resolution_shortComplex_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (colimit.post
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R))) := by
  let S :=
    F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let E := ShortComplex.functorEquivalence J (ModuleCat.{u} R)
  let T : ShortComplex (J ⥤ ModuleCat.{u} R) := E.inverse.obj S
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let ε : E.functor.obj T ≅ S := E.counitIso.app S
  have howner :
      IsIso (colimit.post (E.functor.obj T) H) :=
    shortComplex_owner_post_isIso (R := R) (J := J) T
  have hmap :
      IsIso (H.map (colim.map ε.hom)) := by
    infer_instance
  have hcomp :
      IsIso (colim.map (Functor.whiskerRight ε.hom H) ≫ colimit.post S H) := by
    rw [tor_fixed_right_resolution_window_owner_transport_eq
      (R := R) (J := J) F N n]
    simpa [E, T, H, ε] using CategoryTheory.IsIso.comp_isIso' howner hmap
  exact IsIso.of_isIso_comp_left
    (colim.map (Functor.whiskerRight ε.hom H))
    (colimit.post S H)

/-- Helper for Lemma 10.76.2: the homology comparison after taking the degree-`n` short-complex
window factors through `colimit.post_post` for that window. -/
private theorem tor_fixed_right_resolution_homology_post_eq_post_post_window
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    colimit.post
        (F ⋙ tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
        (ShortComplex.homologyFunctor (ModuleCat.{u} R)) ≫
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
        (colimit.post F
          (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
            HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)) =
    colimit.post F
      (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
          ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  -- This is the standard `colimit.post_post` factorization for the degree-`n` short-complex
  -- window of the tensorized fixed resolution.
  simpa using
    (colimit.post_post
      (F := F)
      (G := tor_fixed_right_resolution_complex_functor (R := R) N ⋙
        HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
      (H := ShortComplex.homologyFunctor (ModuleCat.{u} R)))

/-- Helper for Lemma 10.76.2: a functor into `ShortComplex` preserves `J`-colimits once each of
its three projection functors does. -/
private theorem shortComplex_preservesColimitsOfShape_of_pi
    {D : Type*} [Category D]
    {J : Type*} [Category J]
    [HasColimitsOfShape J D]
    (G : D ⥤ ShortComplex (ModuleCat.{u} R))
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₁)]
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₂)]
    [PreservesColimitsOfShape J (G ⋙ ShortComplex.π₃)] :
    PreservesColimitsOfShape J G := by
  refine ⟨fun {F} => ?_⟩
  -- Rebuild the colimit in `ShortComplex` from the colimits of the three component diagrams.
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply ShortComplex.isColimitOfIsColimitπ
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₁) (colimit.isColimit F)
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₂) (colimit.isColimit F)
  · exact isColimitOfPreserves (G ⋙ ShortComplex.π₃) (colimit.isColimit F)

/-- Helper for Lemma 10.76.2: the degree-`n` short-complex window on chain complexes preserves
filtered colimits of the current shape. -/
private theorem shortComplexFunctor_preserves_filtered_colimits
    {J : Type v} [Category.{v} J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (n : ℕ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor
        (ModuleCat.{u} R) (ComplexShape.down ℕ) n) := by
  letI : HasColimitsOfShape J
      (HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) := by
    infer_instance
  let W := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  -- Route correction: check the three components of the short-complex window separately.
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₁) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval
        (ModuleCat.{u} R) (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n))
    infer_instance
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₂) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    infer_instance
  letI : PreservesColimitsOfShape J (W ⋙ ShortComplex.π₃) := by
    change PreservesColimitsOfShape J
      (HomologicalComplex.eval
        (ModuleCat.{u} R) (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next n))
    infer_instance
  exact shortComplex_preservesColimitsOfShape_of_pi (R := R) W

/-- Helper for Lemma 10.76.2: after passing to homology in degree `n`, the fixed-resolution
complex functor still sends the directed-colimit comparison morphism to an isomorphism. -/
private theorem tor_fixed_right_resolution_homology_post_isIso
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso
      (colimit.post F
        (tor_fixed_right_resolution_complex_functor (R := R) N ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n)) := by
  let K := tor_fixed_right_resolution_complex_functor (R := R) N
  let W := HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let H : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
    ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let e :
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n ≅
        W ⋙ H :=
    HomologicalComplex.homologyFunctorIso
      (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  letI := tor_fixed_right_resolution_complex_functor_preserves_filtered_colimits
    (R := R) (J := J) N
  letI : PreservesColimitsOfShape J W :=
    shortComplexFunctor_preserves_filtered_colimits (R := R) (J := J) n
  have hpostComplex :
      IsIso (W.map (colimit.post F K)) := by
    have hcomplex :
        IsIso (colimit.post F K) :=
      tor_fixed_right_resolution_post_isIso (R := R) (J := J) F N
    infer_instance
  have hwindowPost :
      IsIso (colimit.post (F ⋙ K) W) := by
    infer_instance
  have hwindow :
      IsIso (colimit.post F (K ⋙ W)) := by
    rw [← colimit.post_post (F := F) (G := K) (H := W)]
    simpa [K, W] using CategoryTheory.IsIso.comp_isIso' hwindowPost hpostComplex
  have hshort :
      IsIso (colimit.post (F ⋙ K ⋙ W) H) :=
    tor_fixed_right_resolution_shortComplex_post_isIso (R := R) (J := J) F N n
  have hmap :
      IsIso (H.map (colimit.post F (K ⋙ W))) := by
    infer_instance
  -- First pass to the degree-`n` short-complex window, then take homology there.
  have hwindowHomology :
      IsIso (colimit.post F (K ⋙ W ⋙ H)) := by
    rw [← tor_fixed_right_resolution_homology_post_eq_post_post_window
      (R := R) (J := J) F N n]
    simpa [K, W, H] using CategoryTheory.IsIso.comp_isIso' hshort hmap
  have hleft :
      IsIso
        (colim.map
          (Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft K e)).hom) := by
    infer_instance
  -- Then transport from short-complex homology back to homology of the chain complex.
  have htransport :
      IsIso
        (colimit.post F (K ⋙ HomologicalComplex.homologyFunctor
            (ModuleCat.{u} R) (ComplexShape.down ℕ) n) ≫
          ((Functor.isoWhiskerLeft K e).app (colimit F)).hom) := by
    rw [← colimit_post_whisker_left_iso_hom
      (F := F) (e := Functor.isoWhiskerLeft K e)]
    simpa [K, W, H, e] using CategoryTheory.IsIso.comp_isIso' hleft hwindowHomology
  exact IsIso.of_isIso_comp_right
    (colimit.post F
      (K ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{u} R) (ComplexShape.down ℕ) n))
    (((Functor.isoWhiskerLeft K e).app (colimit F)).hom)

end

/-- Helper for Lemma 10.76.2: for a directed system, the canonical Tor comparison is obtained by
transporting the degree-`n` homology comparison of the fixed tensorized resolution. -/
private theorem tor_filteredColimitComparison_isIso_of_directed
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J] [IsFiltered J]
    [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)) := by
  let G := ((Tor (ModuleCat.{u} R) n).flip.obj N)
  let H :=
    tor_fixed_right_resolution_complex_functor (R := R) N ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n
  let e := tor_fixed_right_resolution_homology_iso (R := R) N n
  have hleft :
      IsIso (colim.map (Functor.isoWhiskerLeft F e).hom) := by
    infer_instance
  have hright :
      IsIso (colimit.post F H) :=
    tor_fixed_right_resolution_homology_post_isIso (R := R) (J := J) F N n
  have hcomp :
      IsIso (colimit.post F G ≫ (e.app (colimit F)).hom) := by
    rw [← colimit_post_whisker_left_iso_hom (F := F) e]
    simpa [G, H, e] using CategoryTheory.IsIso.comp_isIso' hleft hright
  exact IsIso.of_isIso_comp_right (colimit.post F G) ((e.app (colimit F)).hom)

end

-- Proof sketch: compute `Tor_n^R(-, N)` from a projective resolution of `N`. Tensoring that fixed
-- resolution termwise with the filtered diagram `F` commutes with filtered colimits by Lemma
-- `10.12.9`, and homology commutes with filtered colimits by Lemma `10.8.8`, so the canonical
-- comparison map is an isomorphism.
/-- Lemma 10.76.2: for a filtered diagram `i ↦ M_i` of `R`-modules and a fixed `R`-module `N`,
the canonical map
`\mathop{\mathrm{colim}}_i \operatorname{Tor}_n^R(M_i, N) \to
\operatorname{Tor}_n^R(\mathop{\mathrm{colim}}_i M_i, N)`
is an isomorphism. -/
theorem tor_filteredColimitComparison_isIso
    {R : Type u} [CommRing R]
    {J : Type v} [Category.{v} J] [IsFiltered J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (F : J ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)) := by
  exact tor_filteredColimitComparison_isIso_of_directed
    (R := R) (J := J) F N n
