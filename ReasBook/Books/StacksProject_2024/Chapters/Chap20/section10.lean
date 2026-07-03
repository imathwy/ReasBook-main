import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_10_1 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

variable (U : Opens X.carrier) {ι : Type u}
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

-- Proof sketch: by `20.10.0.1`, the functor is the composite of the restricted-sections functor
-- `moduleSectionsOnOverPresheaf U` with the Čech complex functor on `(Over U)ᵒᵖ`. For each
-- `V : Over U`, evaluation at `V` is exact on presheaves of modules, and restriction of scalars is
-- exact on module categories. Hence `moduleSectionsOnOverPresheaf U` is exact. The functor
-- `CategoryTheory.cechComplexFunctor 𝒰` is exact because each degree is a product of exact
-- evaluation functors, and finite limits and colimits in cochain complexes are computed
-- degreewise. Therefore the composite is exact.
/-- Lemma 20.10.1: for an indexed family `𝒰` of objects of `Over U`, the Čech complex functor of
Equation `20.10.0.1`
`ringedSpaceModuleCechComplexFunctor U 𝒰 :
  PMod(\mathcal O_X) ⥤ \operatorname{CochainComplex}(\operatorname{Mod}(\mathcal O_X(U)), \mathbf N)`
is an exact functor. -/
theorem ringedSpaceModuleCechComplexFunctor_exact (𝒰 : ι → Over U) :
    exactFunctor
      (ringedSpacePresheafModules X)
      (CochainComplex (ModuleCat.{u} (X.presheaf.obj (op U))) ℕ)
      (ringedSpaceModuleCechComplexFunctor U 𝒰) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_10_2 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The Čech complex functor on presheaves of `\mathcal O_X`-modules is additive. -/
noncomputable instance ringedSpaceModuleCechComplexFunctor_additive :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).Additive := sorry

/-- The Čech complex functor on presheaves of `\mathcal O_X`-modules preserves zero morphisms. -/
instance ringedSpaceModuleCechComplexFunctor_preservesZeroMorphisms :
    (ringedSpaceModuleCechComplexFunctor U 𝒰).PreservesZeroMorphisms := inferInstance

/-- The degree-`n` Čech cohomology functor on presheaves of `\mathcal O_X`-modules for the cover
`𝒰`. -/
abbrev ringedSpaceCechCohomologyDegree (n : ℕ) :
    ringedSpacePresheafModules X ⥤+ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  AdditiveFunctor.of
    (ringedSpaceModuleCechComplexFunctor U 𝒰 ⋙
      HomologicalComplex.homologyFunctor
        (ModuleCat.{u} (X.presheaf.obj (op U))) (ComplexShape.up ℕ) n)

-- Proof sketch: apply Lemma `20.10.1`, which states that
-- `ringedSpaceModuleCechComplexFunctor U 𝒰` is exact. In an abelian category, exact functors send
-- short exact sequences to short exact sequences.
/-- A short exact sequence of presheaves of `\mathcal O_X`-modules induces a short exact sequence
of Čech complexes of `\mathcal O_X(U)`-modules. -/
theorem ringedSpaceCechComplex_map_shortExact
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) :
    (S.map (ringedSpaceModuleCechComplexFunctor U 𝒰)).ShortExact := sorry

/-- The connecting morphism in degree `n` for the Čech cohomology of a short exact sequence of
presheaves of `\mathcal O_X`-modules. -/
noncomputable def ringedSpaceCechCohomologyConnectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.obj S.X₃ ⟶
      (ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.obj S.X₁ :=
  (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

-- Proof sketch: by construction
-- `ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n` is the boundary morphism in the long
-- exact homology sequence of the short exact sequence of Čech complexes from
-- `ringedSpaceCechComplex_map_shortExact U 𝒰 hS`.
/-- The Čech cohomology connecting morphism is the boundary map of the mapped short exact sequence
of Čech complexes. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_def
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n =
      (ringedSpaceCechComplex_map_shortExact U 𝒰 hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl) := sorry

-- Proof sketch: use the leftmost exactness statement of the homology long exact sequence attached
-- to the short exact sequence of Čech complexes from `ringedSpaceCechComplex_map_shortExact`.
/-- In degree `0`, the map induced by the first arrow of a short exact sequence is a monomorphism
on Čech cohomology. -/
theorem ringedSpaceCechCohomology_mono_map_f_zero
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) :
    Mono ((ringedSpaceCechCohomologyDegree U 𝒰 0).obj.map S.f) := sorry

-- Proof sketch: this is the relation
-- `\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
-- \check H^{n+1}(\mathcal U, S.X₁) = 0`
-- in the long exact homology sequence of the mapped short exact sequence of Čech complexes.
/-- The Čech connecting morphism annihilates the image of the middle map in the long exact
sequence. -/
theorem ringedSpaceCechCohomology_map_g_comp_connectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g ≫
        ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n =
      0 := sorry

-- Proof sketch: this is the next exactness relation in the same long exact homology sequence.
/-- The Čech connecting morphism factors through the kernel of the next map induced by `f`. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_comp_map_f
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n ≫
        (ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f =
      0 := sorry

-- Proof sketch: exactness at the middle term
-- `\check H^n(\mathcal U, S.X₁) ⟶ \check H^n(\mathcal U, S.X₂) ⟶
-- \check H^n(\mathcal U, S.X₃)`
-- in the long exact homology sequence gives the exactness of the mapped short complex.
/-- In every degree, the short complex obtained by applying Čech cohomology is exact. -/
theorem ringedSpaceCechCohomology_map_exact
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (ringedSpaceCechCohomologyDegree U 𝒰 n).obj).Exact := sorry

-- Proof sketch: this is exactness at `\check H^n(\mathcal U, S.X₃)` in the long exact homology
-- sequence of the mapped short exact sequence of Čech complexes.
/-- The short complex
`\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
\check H^{n+1}(\mathcal U, S.X₁)`. -/
abbrev ringedSpaceCechCohomologyMapGConnectingShortComplex
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex (ModuleCat.{u} (X.presheaf.obj (op U))) :=
  ShortComplex.mk
    ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
    (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
    (ringedSpaceCechCohomology_map_g_comp_connectingMorphism U 𝒰 hS n)

/-- The sequence
`\check H^n(\mathcal U, S.X₂) ⟶ \check H^n(\mathcal U, S.X₃) ⟶
\check H^{n+1}(\mathcal U, S.X₁)` is exact. -/
-- Proof sketch: this is exactness at `\check H^n(\mathcal U, S.X₃)` in the long exact homology
-- sequence of the mapped short exact sequence of Čech complexes.
theorem ringedSpaceCechCohomology_exact_map_g_connectingMorphism
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyMapGConnectingShortComplex U 𝒰 hS n).Exact := sorry

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, S.X₁)` in the same long exact
-- homology sequence.
/-- The short complex
`\check H^n(\mathcal U, S.X₃) ⟶ \check H^{n+1}(\mathcal U, S.X₁) ⟶
\check H^{n+1}(\mathcal U, S.X₂)`. -/
abbrev ringedSpaceCechCohomologyConnectingMapFShortComplex
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    ShortComplex (ModuleCat.{u} (X.presheaf.obj (op U))) :=
  ShortComplex.mk
    (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
    ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
    (ringedSpaceCechCohomologyConnectingMorphism_comp_map_f U 𝒰 hS n)

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, S.X₁)` in the same long exact
-- homology sequence.
/-- The sequence
`\check H^n(\mathcal U, S.X₃) ⟶ \check H^{n+1}(\mathcal U, S.X₁) ⟶
\check H^{n+1}(\mathcal U, S.X₂)` is exact. -/
theorem ringedSpaceCechCohomology_exact_connectingMorphism_map_f
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ringedSpaceCechCohomologyConnectingMapFShortComplex U 𝒰 hS n).Exact := sorry

/-- The five-term window in the long exact Čech cohomology sequence is exact. -/
theorem ringedSpaceCechCohomology_exact₅
    {S : ShortComplex (ringedSpacePresheafModules X)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map S.g)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.f)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map S.g)).Exact :=
  CohomologicalDeltaFunctor.exact₅_of_adjacent_exactness
    (fun {_} hS n ↦ ringedSpaceCechCohomology_map_g_comp_connectingMorphism U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomologyConnectingMorphism_comp_map_f U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_map_exact U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_exact_map_g_connectingMorphism U 𝒰 hS n)
    (fun {_} hS n ↦ ringedSpaceCechCohomology_exact_connectingMorphism_map_f U 𝒰 hS n)
    hS n

-- Proof sketch: a morphism of short exact sequences of presheaves of `\mathcal O_X`-modules maps
-- to a morphism of short exact sequences of Čech complexes, and the naturality of the homology
-- boundary morphism gives the resulting commutative square.
/-- The Čech cohomology connecting morphisms are natural in morphisms of short exact sequences of
presheaves of `\mathcal O_X`-modules. -/
theorem ringedSpaceCechCohomologyConnectingMorphism_naturality
    {S T : ShortComplex (ringedSpacePresheafModules X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq
      ((ringedSpaceCechCohomologyDegree U 𝒰 n).obj.map φ.τ₃)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n)
      (ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hT n)
      ((ringedSpaceCechCohomologyDegree U 𝒰 (n + 1)).obj.map φ.τ₁) := sorry

/-- Lemma 20.10.2: for an open covering `𝒰` of `U` on a ringed space `X`, the functors
`ℱ ↦ \check H^n(𝒰, ℱ)` form a cohomological `δ`-functor from presheaves of
`\mathcal O_X`-modules to `\mathcal O_X(U)`-modules. -/
noncomputable def ringedSpaceCechCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor
      (ringedSpacePresheafModules X)
      (ModuleCat.{u} (X.presheaf.obj (op U))) where
  F := ringedSpaceCechCohomologyDegree U 𝒰
  δ := fun {_} hS n ↦ ringedSpaceCechCohomologyConnectingMorphism U 𝒰 hS n
  mono_map_f_zero := fun {_} hS ↦ ringedSpaceCechCohomology_mono_map_f_zero U 𝒰 hS
  exact₅ := fun {_} hS n ↦ ringedSpaceCechCohomology_exact₅ U 𝒰 hS n
  δ_naturality := fun {_ _} hS hT φ n ↦
    ringedSpaceCechCohomologyConnectingMorphism_naturality U 𝒰 hS hT φ n

-- Proof sketch: unfold `ringedSpaceCechCohomologyDeltaFunctor`; the degree-`n` term is defined to
-- be `ringedSpaceCechCohomologyDegree U 𝒰 n`.
/-- The degree-`n` term of the Čech cohomology `δ`-functor is the degree-`n` Čech cohomology
functor. -/
theorem ringedSpaceCechCohomologyDeltaFunctor_F_eq (n : ℕ) :
    (ringedSpaceCechCohomologyDeltaFunctor U 𝒰 n).obj =
      (ringedSpaceCechCohomologyDegree U 𝒰 n).obj := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_10_3 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/- Domain-style sampling for Lemma 20.10.3:
- primary domain: Čech complexes of presheaf `\mathcal O_X`-modules and the canonical cover chain
  complex built from free Yoneda summands;
- sampled owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `PresheafOfModules.localizedStructureModuleExtensionByZero`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- best owner abstraction: the source-facing owner in this file is the cover chain complex
  `openCoverChainComplex 𝒰`, while the canonical `Hom(K_\bullet,-)` cochain functor is obtained by
  applying `preadditiveCoyoneda` to `K.op` and then viewing the resulting complex of functors via
  `HomologicalComplex.asFunctor`; the Čech target remains the canonical owner
  `CategoryTheory.cechComplexFunctor 𝒰`.

Primitive data is only the ringed space `X` and the indexed open family `𝒰`. The formal-coproduct
realization of the cover is derived bridge data, and the `Hom(K_\bullet,-)` cochain construction
should be reused from the owner-level homological-complex API rather than rebuilt degreewise in
this file.

Source/core/bridge triage:
- `source-facing`: `openCoverChainComplex 𝒰` and the comparison theorem with the Čech complex;
- `core/canonical`: `CategoryTheory.cechComplexFunctor 𝒰`,
  `PresheafOfModules.localizedStructureModuleExtensionByZero`,
  `preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- `bridge/view`: the formal-coproduct module functor realizing the cover. -/

private noncomputable abbrev openSubsetFreeModuleFunctor (X : RingedSpace.{u}) :
    Opens X.carrier ⥤ ringedSpacePresheafModules X :=
  yoneda ⋙ PresheafOfModules.free ((RingedSpace.ringCatSheaf X)).obj

/-- The extension of the open-subset module functor to formal coproducts of open subsets. -/
private noncomputable def coverFormalCoproductModuleFunctor (X : RingedSpace.{u}) :
    CategoryTheory.Limits.FormalCoproduct.{u} (Opens X.carrier) ⥤ ringedSpacePresheafModules X where
  obj U := ∐ fun i : U.I ↦ (openSubsetFreeModuleFunctor X).obj (U.obj i)
  map {U V} f :=
    Sigma.desc fun i ↦
      (openSubsetFreeModuleFunctor X).map (f.φ i) ≫
        Sigma.ι (fun j : V.I ↦ (openSubsetFreeModuleFunctor X).obj (V.obj j)) (f.f i)
  map_id U := by
    apply Sigma.hom_ext
    intro i
    simpa using
      (Sigma.ι_desc
        (p := fun j : U.I ↦
          Sigma.ι (fun k : U.I ↦ (openSubsetFreeModuleFunctor X).obj (U.obj k)) j)
        i)
  map_comp f g := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
    dsimp
    rw [Category.assoc, Sigma.ι_desc]
    have hmap :
        (openSubsetFreeModuleFunctor X).map (f.φ i ≫ g.φ (f.f i)) =
          (openSubsetFreeModuleFunctor X).map (f.φ i) ≫
            (openSubsetFreeModuleFunctor X).map (g.φ (f.f i)) :=
      Functor.map_comp (openSubsetFreeModuleFunctor X) (f.φ i) (g.φ (f.f i))
    simpa [Category.assoc] using
      congrArg
        (fun h ↦ h ≫ Sigma.ι _ (g.f (f.f i)))
        hmap

/-- The simplicial presheaf-module object attached to an indexed open covering. -/
private noncomputable abbrev openCoverSimplicialObject (𝒰 : ι → Opens X.carrier) :
    SimplicialObject (ringedSpacePresheafModules X) :=
  letI : OrderTop (Opens X.carrier) := opensOrderTop X.carrier
  letI : HasFiniteLimits (Opens X.carrier) :=
    hasFiniteLimits_of_semilatticeInf_orderTop
  letI : HasFiniteProducts (Opens X.carrier) := opensHasFiniteProducts X.carrier
  (FormalCoproduct.mk _ 𝒰).cech ⋙ coverFormalCoproductModuleFunctor X

/-- The chain complex of presheaf modules associated with an indexed open covering. -/
noncomputable abbrev openCoverChainComplex (𝒰 : ι → Opens X.carrier) :
    ChainComplex (ringedSpacePresheafModules X) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ringedSpacePresheafModules X)).obj
    (openCoverSimplicialObject 𝒰)

-- Proof sketch: realize the cover as the formal coproduct `∐ i, U_i` in `Opens X`, apply the Čech
-- simplicial formal-coproduct construction, and then evaluate it in presheaf modules via the
-- Yoneda-free module functor `U ↦ (free \circ yoneda)(U)`. Morphisms from the resulting degree-`p`
-- term to a presheaf module `ℱ` identify with sections of `ℱ` on the corresponding
-- `(p + 1)`-fold intersections, and the alternating face differential becomes the usual Čech
-- differential. These identifications are natural in `ℱ`, yielding the desired natural
-- isomorphism of functors.
/-- Lemma 20.10.3: for a ringed space `X` and an indexed open covering `𝒰`, the functor
`Hom_{\mathcal O_X}(K(\mathcal U)_\bullet,-)` associated with the canonical cover chain complex is
isomorphic to the canonical Čech complex functor of the cover. -/
theorem openCoverChainComplex_homFunctor_iso_cechComplexFunctor
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic
      (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (openCoverChainComplex 𝒰).op).asFunctor)
      (PresheafOfModules.toPresheaf ((RingedSpace.ringCatSheaf X)).obj ⋙
        cechComplexFunctor 𝒰) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_10_4 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

/-- The structure presheaf of a ringed space, viewed as a presheaf of modules over itself. -/
abbrev structurePresheafModule (X : RingedSpace.{u}) : ringedSpacePresheafModules X :=
  PresheafOfModules.unit ((RingedSpace.ringCatSheaf X)).obj

/-- The degree-zero term of the canonical Čech cover chain complex, written as the coproduct of the
free Yoneda modules attached to the members of the open family. -/
noncomputable abbrev openCoverDegreeZeroModule (𝒰 : ι → Opens X.carrier) :
    ringedSpacePresheafModules X :=
  ∐ fun i : ι ↦ (yoneda ⋙ PresheafOfModules.free ((RingedSpace.ringCatSheaf X)).obj).obj (𝒰 i)

/-- The canonical augmentation from degree `0` of the Čech cover chain complex to the structure
presheaf, sending the distinguished generator of each summand to `1`. -/
noncomputable def openCoverDegreeZeroToStructure (𝒰 : ι → Opens X.carrier) :
    openCoverDegreeZeroModule 𝒰 ⟶ structurePresheafModule X :=
  Sigma.desc fun i ↦
    (PresheafOfModules.freeYonedaEquiv.symm
      (show (structurePresheafModule X).obj (op (𝒰 i)) from
        (1 : ((RingedSpace.ringCatSheaf X)).obj.obj (op (𝒰 i)))))

/-- The image presheaf of the canonical augmentation from degree `0` of the cover chain complex to
the structure presheaf. -/
noncomputable abbrev openCoverStructureImage (𝒰 : ι → Opens X.carrier) :
    ringedSpacePresheafModules X :=
  image (openCoverDegreeZeroToStructure 𝒰)

/-- The canonical monomorphism from the image presheaf of the cover augmentation into the
structure presheaf. -/
noncomputable abbrev openCoverStructureImageι (𝒰 : ι → Opens X.carrier) :
    openCoverStructureImage 𝒰 ⟶ structurePresheafModule X :=
  image.ι (openCoverDegreeZeroToStructure 𝒰)

-- Proof sketch: augment `openCoverChainComplex 𝒰` by the canonical map from degree `0` to the
-- structure presheaf. On sections over any open subset, this becomes the extended alternating
-- Čech complex from the textbook, and the explicit contracting homotopy there shows the augmented
-- complex is exact. Therefore the positive homology objects vanish, while degree-zero homology is
-- the image of the augmentation.
/-- Lemma 20.10.4: for a ringed space `X` and an open family `𝒰`, the homology presheaf of the
cover chain complex `K(\mathcal U)_\bullet` is canonically the image presheaf of the degree-zero
augmentation in degree `0`, and is zero in every other degree. -/
theorem openCoverChainComplex_homology_iso_coverImage_or_zero
    (𝒰 : ι → Opens X.carrier) (i : ℕ) :
    IsIsomorphic ((openCoverChainComplex 𝒰).homology i)
      (if h : i = 0 then openCoverStructureImage 𝒰 else 0) := sorry

-- Proof sketch: specialize the main homology computation to an index `i ≠ 0`; then the
-- right-hand side becomes the zero object, so the corresponding homology object is zero.
/-- Away from degree `0`, the homology of the cover chain complex vanishes. -/
theorem openCoverChainComplex_homology_isZero_of_ne_zero
    (𝒰 : ι → Opens X.carrier) {i : ℕ} (hi : i ≠ 0) :
    IsZero ((openCoverChainComplex 𝒰).homology i) := sorry

-- Proof sketch: evaluate the main homology computation at `i = 0`; the case distinction collapses
-- to the image presheaf of the canonical degree-zero augmentation.
/-- The degree-zero homology of the cover chain complex is the image presheaf of the canonical
augmentation to the structure presheaf. -/
theorem openCoverChainComplex_homology_zero_isomorphic_coverStructureImage
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic ((openCoverChainComplex 𝒰).homology 0)
      (openCoverStructureImage 𝒰) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_10_5 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable (U : Opens X.carrier) {ι : Type u} (𝒰 : ι → Over U)
variable [HasFiniteProducts (Over U)]
variable [HasProducts (ModuleCat.{u} (X.presheaf.obj (op U)))]

/-- The degree-zero Čech cohomology functor of the covering `𝒰` on presheaves of
`\mathcal O_X`-modules. -/
abbrev ringedSpaceCechH0Functor :
    ringedSpacePresheafModules X ⥤ ModuleCat.{u} (X.presheaf.obj (op U)) :=
  (ringedSpaceCechCohomologyDegree U 𝒰 0).obj

-- Proof sketch: Lemma `20.10.2` provides the cohomological `δ`-functor structure on Čech
-- cohomology. For an injective presheaf module `ℐ`, Lemmas `20.10.3` and `20.10.4` identify the
-- Čech complex with a Hom complex out of a chain complex whose positive-degree homology vanishes,
-- so `\check H^p(\mathcal U, ℐ) = 0` for every `p > 0`. Hence the positive degrees are weakly
-- effaceable, and Lemma `12.12.4` yields universality.
/-- Lemma 20.10.5 (1): the Čech cohomology functors of the covering `𝒰` form a universal
cohomological `δ`-functor on presheaves of `\mathcal O_X`-modules. -/
theorem ringedSpaceCechCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (ringedSpaceCechCohomologyDeltaFunctor U 𝒰) := sorry

section

variable [HasInjectiveResolutions (ringedSpacePresheafModules X)]

-- Proof sketch: the degree-zero term of the universal `δ`-functor is `\check H^0`, while part
-- `(1)` shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of `\check H^0`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. In positive degree this gives the canonical
-- functor isomorphism.
/-- Lemma 20.10.5 (2): for each `p`, the higher Čech cohomology functor
`\check H^{p+1}(\mathcal U, -)` is canonically isomorphic to the `(p + 1)`-st right derived
functor of `\check H^0(\mathcal U, -)`. -/
theorem ringedSpaceHigherCechCohomologyFunctor_isomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((ringedSpaceCechCohomologyDegree U 𝒰 (p + 1)).obj)
      ((ringedSpaceCechH0Functor U 𝒰).rightDerived (p + 1)) := sorry

-- Proof sketch: choose the canonical injective resolution of `ℱ`, form the double complex whose
-- `q`-th column is the Čech complex of the `q`-th injective term, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, \mathcal F)` and the complex computing
-- `R\check H^0(\mathcal U, \mathcal F)` to the corresponding total complex using Lemma `12.25.4`.
-- The injective-resolution complex on the right computes the derived value by the standard
-- `InjectiveResolution.isoRightDerivedObj` comparison.
/-- Lemma 20.10.5 (3): for a presheaf `\mathcal F` of `\mathcal O_X`-modules, the complex obtained
by applying `\check H^0(\mathcal U, -)` termwise to an injective resolution of `\mathcal F`
computes the right derived functors of `\check H^0(\mathcal U, -)` at `\mathcal F`. This is the
canonical complex model underlying the source functorial quasi-isomorphism. -/
theorem ringedSpaceRightDerivedCechH0_obj_isomorphic_homology_chosenInjectiveResolution
    (ℱ : ringedSpacePresheafModules X) :
    ∀ p : ℕ,
      IsIsomorphic (((ringedSpaceCechH0Functor U 𝒰).rightDerived p).obj ℱ)
        ((HomologicalComplex.homologyFunctor
            (ModuleCat.{u} (X.presheaf.obj (op U)))
            (ComplexShape.up ℕ) p).obj
          (((ringedSpaceCechH0Functor U 𝒰).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj
            (injectiveResolution ℱ).cocomplex)) := sorry

end

end AlgebraicGeometry.RingedSpace
