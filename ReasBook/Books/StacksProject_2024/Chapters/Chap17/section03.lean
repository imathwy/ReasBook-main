import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_17_3_1 (from Chap17) -/
open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.3.1:
- primary domain: exactness in the abelian category of `\mathcal O_X`-modules and detection of
  exactness by stalks of `\mathcal O_X`-modules;
- inspected owner declarations:
  `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`,
  `SheafOfModules.toSheaf`,
  `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`,
  `Functor.reflects_exact_of_faithful`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X` together with the
  induced stalk-module short complex `stalkShortComplex S x`; the underlying additive sheaf stalk
  functor is only an internal bridge to the generic sheaf exactness criterion;
- primitive-vs-derived split:
  the primitive data are the ringed space `X`, a short complex
  `S : ShortComplex (RingedSpace.Modules X)`, and its canonical stalk-module realization
  `stalkShortComplex S x`;
  the underlying abelian-sheaf forgetful composite and the stalkwise exactness criterion for
  abelian sheaves are derived bridge API and should stay internal.

Source/core/bridge triage:
- `source-facing`: the two Stacks assertions that `Mod(\mathcal O_X)` is abelian and that
  exactness is stalkwise;
- `core/canonical`: `RingedSpace.Modules X`, `RingedSpace.stalkModuleCat`,
  `RingedSpace.moduleStalkHom`, and `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`;
- `bridge/view`: the private comparison between the module-valued stalk complex and the underlying
  abelian-sheaf stalk complex obtained through `SheafOfModules.toSheaf`. -/

local notation "𝒪X" => RingedSpace.ringCatSheaf X
local notation "ModX" => RingedSpace.Modules X
local notation "toAbelianSheaf" => (SheafOfModules.toSheaf 𝒪X)

private noncomputable abbrev stalkAddCommGrpFunctor (x : X) :
    ModX ⥤ AddCommGrpCat.{u} :=
  toAbelianSheaf ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

local instance toAbelianSheaf_preservesZeroMorphisms :
    (SheafOfModules.toSheaf 𝒪X).PreservesZeroMorphisms :=
  { map_zero _ _ := by rfl }

local instance stalkwiseAddCommGrpFunctor_preservesZeroMorphisms (x : X) :
    (stalkAddCommGrpFunctor x).PreservesZeroMorphisms := by
  let F : ModX ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toAbelianSheaf
  let G : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  letI : F.PreservesZeroMorphisms := toAbelianSheaf_preservesZeroMorphisms
  letI : G.PreservesZeroMorphisms := by infer_instance
  simpa [stalkAddCommGrpFunctor, F, G] using
    (inferInstance : (F ⋙ G).PreservesZeroMorphisms)

/-- The short complex on stalk modules induced by a short complex of `\mathcal O_X`-modules. -/
noncomputable abbrev stalkShortComplex (S : ShortComplex ModX) (x : X) :
    ShortComplex (ModuleCat (X.presheaf.stalk x)) :=
  ShortComplex.mk
    (RingedSpace.moduleStalkHom x S.f)
    (RingedSpace.moduleStalkHom x S.g)
    (by sorry)

-- Proof sketch: `SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))` is exact, so exactness of a
-- short complex of `\mathcal O_X`-modules is equivalent to exactness of the underlying short
-- complex of abelian sheaves.
/-- Exactness of a short complex of `\mathcal O_X`-modules agrees with exactness of its underlying
short complex of abelian sheaves. -/
private theorem exact_iff_toAbelianSheaf_exact (S : ShortComplex ModX) :
    S.Exact ↔ (S.map toAbelianSheaf).Exact := sorry

/-- The stalk-module short complex is exact if and only if its underlying additive stalk complex
is exact. This is the internal bridge from the intrinsic stalk-module layer to the generic sheaf
criterion on abelian sheaves. -/
private theorem stalkShortComplex_exact_iff_stalkAddCommGrp_exact
    (S : ShortComplex ModX) (x : X) :
    (stalkShortComplex S x).Exact ↔ (S.map (stalkAddCommGrpFunctor x)).Exact := by
  sorry

/- Lemma 17.3.1 (1): for a ringed space `(X, 𝒪_X)`, the category `Mod(𝒪_X)` of sheaves of
`𝒪_X`-modules is abelian. This is the canonical owner instance on `RingedSpace.Modules X`. -/
#synth Abelian ModX

-- Proof sketch: first forget the `\mathcal O_X`-module structure to a short complex of sheaves of
-- abelian groups, then apply the generic stalkwise exactness criterion for sheaves.
/-- Lemma 17.3.1 (2): a short complex of `𝒪_X`-modules is exact in the middle if and only if all
its stalk-module complexes are exact in the middle. -/
theorem ringedSpaceModule_exact_iff_stalkwise_exact (S : ShortComplex ModX) :
    S.Exact ↔ ∀ x : X, (stalkShortComplex S x).Exact := by
  let F : ModX ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toAbelianSheaf
  letI : F.PreservesZeroMorphisms := toAbelianSheaf_preservesZeroMorphisms
  rw [exact_iff_toAbelianSheaf_exact]
  constructor
  · intro h x
    have hx : (S.map (stalkAddCommGrpFunctor x)).Exact := by
      simpa [stalkAddCommGrpFunctor] using
        (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mp h x
    exact (stalkShortComplex_exact_iff_stalkAddCommGrp_exact S x).mpr hx
  · intro h
    refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map F)).mpr ?_
    intro x
    have hx : (S.map (stalkAddCommGrpFunctor x)).Exact :=
      (stalkShortComplex_exact_iff_stalkAddCommGrp_exact S x).mp (h x)
    simpa [stalkAddCommGrpFunctor] using hx

end AlgebraicGeometry.RingedSpace

namespace CategoryTheory.ShortComplex.ShortExact

open AlgebraicGeometry

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (RingedSpace.Modules X)}

/-- A short exact sequence of `\mathcal O_X`-modules induces a short exact sequence on each stalk
module. -/
theorem stalkShortComplex (hS : S.ShortExact) (x : X) :
    (RingedSpace.stalkShortComplex S x).ShortExact := by
  let toAbelianSheaf : RingedSpace.Modules X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  letI : toAbelianSheaf.PreservesZeroMorphisms := by
    change (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).PreservesZeroMorphisms
    exact { map_zero _ _ := by rfl }
  let hExact :
      ∀ T : ShortComplex (RingedSpace.Modules X), T.Exact → (T.map toAbelianSheaf).Exact :=
    fun T hT ↦ (AlgebraicGeometry.RingedSpace.exact_iff_toAbelianSheaf_exact T).mp hT
  letI : toAbelianSheaf.PreservesMonomorphisms :=
    CategoryTheory.Functor.preservesMonomorphisms_of_map_exact toAbelianSheaf hExact
  letI : toAbelianSheaf.PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_map_exact toAbelianSheaf hExact
  refine ModuleCat.shortComplex_shortExact (RingedSpace.stalkShortComplex S x)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).mp hS.exact x))
    ?_ ?_
  · have hmono :
        Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.f).hom) := by
      letI : Mono S.f := hS.mono_f
      exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
        (Functor.map_mono toAbelianSheaf S.f) x
    simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono
  · have hsurj :
        Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (toAbelianSheaf.map S.g).hom) := by
      letI : Epi S.g := hS.epi_g
      have hloc :
          TopCat.Presheaf.IsLocallySurjective (toAbelianSheaf.map S.g).hom :=
        (TopCat.Sheaf.isLocallySurjective_iff_epi (toAbelianSheaf.map S.g)).2 <|
          Functor.map_epi toAbelianSheaf S.g
      exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (toAbelianSheaf.map S.g).hom).1 hloc x
    simpa [RingedSpace.moduleStalkMap, toAbelianSheaf] using hsurj

end CategoryTheory.ShortComplex.ShortExact

/-! ### Lemma_17_3_2 (from Chap17) -/
open CategoryTheory Limits AlgebraicGeometry Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (x : X) (U : Opens X)

local notation "𝒪X" => (RingedSpace.ringCatSheaf X)

/- Domain-style sampling for Lemma 17.3.2:
- primary domain: categorical limits, colimits, filtered-colimit exactness, and stalk functors for
  sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.forget`,
  `SheafOfModules.evaluation`,
  `Mod`,
  `PresheafOfModules.sheafification`,
  `CategoryTheory.point_sheaf_module_stalk_functor`;
- best owner abstraction: the source-facing owner notation `Mod(𝒪X)` on top of the canonical
  `SheafOfModules` owner `SheafOfModules (RingedSpace.ringCatSheaf X)`, with the site-point stalk
  functor as the core stalk owner and the ringed-space specialization below as the only needed
  bridge/view;
- primitive-vs-derived split:
  the primitive data are the structure sheaf `(RingedSpace.ringCatSheaf X)`, the source-facing
  owner `Mod(𝒪X)`, and the point `x`;
  all limit, colimit, `AB5`, and biproduct statements are derived owner-level API, while the
  module-valued stalk functor is the direct specialization of the canonical site-point stalk
  functor to `Opens.pointGrothendieckTopology x`.

Source/core/bridge triage:
- `source-facing`: the Stacks statements that `Mod(𝒪_X)` has limits/colimits, that sections over
  `U : Opens X` and stalks commute with those constructions, and that filtered colimits are exact;
- `core/canonical`: the canonical owner `SheafOfModules 𝒪X`, the source-facing notation `Mod(𝒪X)`,
  the anonymous mathlib instances on that owner, and the site-level owner
  `CategoryTheory.point_sheaf_module_stalk_functor`;
- `bridge/view`: the ringed-space specialization obtained by evaluating the site-point stalk
  functor at `Opens.pointGrothendieckTopology x`. -/

/- Lemma 17.3.2 (1): the category `Mod(𝒪_X)` of sheaves of `𝒪_X`-modules has all small limits. -/
#synth HasLimits (Mod(𝒪X))

/- Lemma 17.3.2 (2): limits in `Mod(𝒪_X)` agree with the corresponding limits of presheaves of
`𝒪_X`-modules after forgetting the sheaf condition. -/
#synth PreservesLimits (SheafOfModules.forget.{u} 𝒪X)

/- Lemma 17.3.2 (3): taking sections over any open set commutes with limits of
`𝒪_X`-modules. -/
#synth PreservesLimits (SheafOfModules.evaluation 𝒪X (op U))

/- Lemma 17.3.2 (4): the category `Mod(𝒪_X)` of sheaves of `𝒪_X`-modules has all small
colimits. -/
#synth HasColimits (Mod(𝒪X))

/- Lemma 17.3.2 (5): colimits in `Mod(𝒪_X)` are obtained by sheafifying the corresponding
colimits of presheaves of `𝒪_X`-modules. -/
#synth PreservesColimits
  (PresheafOfModules.sheafification (𝟙 (𝒪X).obj))

/- Lemma 17.3.2 (6): taking stalks commutes with colimits of `\mathcal O_X`-modules. This is the
ringed-space specialization of the canonical site-point module-stalk functor. -/
#synth PreservesColimits
  (point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) 𝒪X)

/- Lemma 17.3.2 (7): filtered colimits are exact in the category `Mod(𝒪_X)`. In canonical form,
this says that `Mod(𝒪_X)` satisfies `AB5`. -/
local instance : AB5 (Mod(𝒪X)) := by
  let _ : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  infer_instance

#synth AB5 (Mod(𝒪X))

/- Lemma 17.3.2 (8): finite direct sums of `𝒪_X`-modules are computed on the underlying
presheaves of modules. -/
#synth PreservesFiniteBiproducts (SheafOfModules.forget.{u} 𝒪X)

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_3_3 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped TopCat AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.3.3:
- primary domain: adjunctions and exactness properties of pullback and pushforward functors on
  sheaves of modules and abelian sheaves over ringed spaces;
- inspected owner declarations:
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `Adjunction.leftAdjoint_preservesColimits`,
  `leftExactFunctor`, `rightExactFunctor`, `exactFunctor_iff`;
- best owner abstraction: `SheafOfModules.pullbackPushforwardAdjunction` for module sheaves, and
  for the abelian-sheaf clause the site-level inverse-image owner
  `(Opens.map f.hom.base).sheafPullback AddCommGrpCat _ _` attached to the underlying continuous
  map, viewed through the canonical exactness predicate `exactFunctor`;
- primitive data: the ringed-space morphism `f`, packaged upstream as
  `RingedSpace.Hom.toRingCatSheafHom f`, together with the underlying continuous map
  `f.hom.base` for the abelian-sheaf clause;
- derived API: preservation of limits and colimits, left/right exactness, and exactness. -/

/- Source/core/bridge triage for Lemma 17.3.3:
- `source-facing`: the Stacks assertions that `f_*` is left exact, `f^*` is right exact, and the
  inverse-image functor on abelian sheaves attached to a morphism of ringed spaces is exact;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction` together with the owner
  predicates `leftExactFunctor`, `rightExactFunctor`, and `exactFunctor`, plus the canonical
  site-level pullback owner for `Opens.map f.hom.base`;
- `bridge/view`: the ringed-space specializations for module sheaves and the abelian-sheaf
  specialization along the underlying continuous map `f.hom.base`. -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

local notation "OX" => (RingedSpace.ringCatSheaf X)
local notation "OY" => (RingedSpace.ringCatSheaf Y)

/- Lemma 17.3.3: for a morphism of ringed spaces
`f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)`, the pushforward functor on module sheaves
commutes with all limits. -/
#synth PreservesLimits (f _*)

/- The direct image functor `f_*` on `\mathcal O_X`-modules is left exact. -/
#check
  (show leftExactFunctor (Mod(OX)) (Mod(OY)) (f _*) from
    by
      simpa [leftExactFunctor_iff] using
        (inferInstance : PreservesFiniteLimits (f _*)))

/- The pullback of `\mathcal O_Y`-modules along a morphism of ringed spaces commutes with all
colimits. -/
#synth PreservesColimits (f^*)

/- The inverse-image module functor `f^*` is right exact. -/
#check
  (show rightExactFunctor (Mod(OY)) (Mod(OX)) (f^*) from
    by
      simpa [rightExactFunctor_iff] using
        (inferInstance : PreservesFiniteColimits (f^*)))

/-- The inverse-image functor on abelian sheaves along the underlying continuous map of a morphism
of ringed spaces is exact. This is the abelian-sheaf clause of Lemma 17.3.3, stated at the
ringed-space bridge layer and derived from the canonical site-level pullback owner. -/
theorem ringedSpaceAbelianSheafPullback_exact :
    exactFunctor (Ab((Y : TopCat))) (Ab((X : TopCat))) ((f.hom.base)⁻¹) := by
  let G := Opens.map f.hom.base
  let JY := Opens.grothendieckTopology (Y : TopCat)
  let JX := Opens.grothendieckTopology (X : TopCat)
  change exactFunctor (Sheaf JY AddCommGrpCat) (Sheaf JX AddCommGrpCat)
    (G.sheafPullback AddCommGrpCat JY JX)
  let _ : HasSheafify JY AddCommGrpCat := inferInstance
  let _ : HasSheafify JX AddCommGrpCat := inferInstance
  let _ : RepresentablyFlat G := inferInstance
  let _ : PreservesFiniteLimits
      (G.op.lan :
        ((Opens (Y : TopCat))ᵒᵖ ⥤ AddCommGrpCat) ⥤
          ((Opens (X : TopCat))ᵒᵖ ⥤ AddCommGrpCat)) := by
    infer_instance
  let _ : PreservesFiniteLimits (G.sheafPullback AddCommGrpCat JY JX) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G AddCommGrpCat JY JX
  let _ : PreservesFiniteColimits (G.sheafPullback AddCommGrpCat JY JX) := by
    let _ : (G.sheafPullback AddCommGrpCat JY JX).IsLeftAdjoint :=
      (G.sheafAdjunctionContinuous AddCommGrpCat JY JX).isLeftAdjoint
    infer_instance
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry

/-! ### Lemma_17_3_4 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace

universe u

/-
Domain-style sampling for Lemma 17.3.4:
- primary domain: extension by zero / by the initial object for sheaves of abelian groups along an
  open immersion of topological spaces;
- sampled owner declarations:
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `Topology.IsEmbedding.toHomeomorph`,
  `TopCat.isoOfHomeo`;
- owner abstraction: the Chapter 6 owner remains the open-subset functor
  `openSubsetSheafExtensionByInitialObject U`; for a general open immersion `j : U ⟶ X`, the
  source-facing `j_!` functor should be obtained by transporting sheaves along the canonical
  homeomorphism `U ≃ j(U)` and then applying that owner. Since `TopCat` keeps open immersions
  unbundled as a morphism together with `Topology.IsOpenEmbedding j`, the public source-facing
  surface in this file should be a short `j_!`-style notation for that transport bridge rather
  than a second owner declaration;
- primitive data: the open immersion `j`, its open image `j(U)`, and the canonical isomorphism
  from `U` to the corresponding open subspace of `X`;
- derived API: the owner-level exactness statement for `j! U` and the thin general open-immersion
  bridge theorem obtained by transport along `U ≅ j(U)`.

Source/core/bridge triage:
- `source-facing`: exactness of `j_!` for a general open immersion `j : U ⟶ X`;
- `core/canonical`: `openSubsetSheafExtensionByInitialObject` on an open subset of `X`;
- `bridge/view`: the thin implementation bridge underlying the notation `j![j; hj]`, which
  transports sheaves along the canonical homeomorphism `U ≅ j(U)` and then applies the Chapter 6
  owner. -/

section AbelianExtensionByZero

variable {X U : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

private abbrev AbCat (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :=
  TopCat.Sheaf AddCommGrpCat.{u} Y

local notation "Ab(" X ")" => AbCat X

private abbrev openImmersionImage
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) : Opens X :=
  ⟨Set.range j, hj.isOpen_range⟩

private noncomputable abbrev openImmersionImageIso
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    U ≅ extensionByZeroOpenSubsetSpace (openImmersionImage j hj) :=
  show U ≅ extensionByZeroOpenSubsetSpace (openImmersionImage j hj) from
    TopCat.isoOfHomeo hj.1.toHomeomorph

/-- The open-subset owner-level form of Lemma 17.3.4: for an open subset `U ⊆ X`, the Chapter 6
extension-by-zero functor `j! U : Ab(U) ⥤ Ab(X)` is exact. -/
theorem openSubsetAbelianSheafExtensionByZero_exact
    (U : Opens X) :
    exactFunctor (Ab(extensionByZeroOpenSubsetSpace U)) (Ab(X)) (j! U) := sorry

/-- The implementation bridge for extension by zero along an open immersion `j : U ⟶ X`,
underlying the source-facing notation `j![j; hj]`. It transports sheaves from `U` to the open
image `j(U)` and then applies the Chapter 6 owner `j!`. -/
noncomputable abbrev openImmersionAbelianSheafExtensionByZero
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    Ab(U) ⥤ Ab(X) :=
  TopCat.Sheaf.pushforward AddCommGrpCat (openImmersionImageIso j hj).hom ⋙
    j! (openImmersionImage j hj)

notation:max "j![" j:max "; " hj:max "]" =>
  openImmersionAbelianSheafExtensionByZero j hj

-- Proof sketch: reduce the statement to the open-subset owner
-- `openSubsetSheafExtensionByInitialObject ⟨Set.range j, hj.isOpen_range⟩` via the canonical
-- homeomorphism `U ≃ j(U)`. Stalkwise, `OpenSubsetExtensionByInitial.sheafExtensionByInitial_
-- stalkDescription` identifies the stalks over points in the image with the original stalks and
-- the stalks off the image with zero, so exactness is checked on stalks.
/-- Lemma 17.3.4: if `j : U ⟶ X` is an open immersion, then the extension-by-zero functor
`j_! : Ab(U) ⥤ Ab(X)` is exact. In this formalization the source-facing functor is written
`j![j; hj]`; the extra `hj` is the Lean witness that the unbundled morphism `j` is an open
immersion. -/
theorem openImmersionAbelianSheafExtensionByZero_exact
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    exactFunctor (Ab(U)) (Ab(X)) (j![j; hj]) := sorry

end AbelianExtensionByZero

/-! ### Lemma_17_3_5 (from Chap17) -/
open CategoryTheory Limits AlgebraicGeometry Opposite TopCat TopologicalSpace

noncomputable section

universe w u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.3.5:
- primary domain: coproducts of `\mathcal O_X`-modules and sections over quasi-compact opens of a
  ringed space;
- inspected owner declarations:
  `SheafOfModules.evaluation`,
  `Limits.sigmaComparison`,
  `quasiCompactObject_module_evaluation_preserves_direct_sums`;
- best owner abstraction: the ambient owner is the structure-sheaf module category
  `SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)`, while the comparison map is the canonical
  `sigmaComparison` for the evaluation functor on `U`;
- primitive data: a ringed space `X`, an open subset `U`, and a family
  `ℱ : I → SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)` with universe-polymorphic index type `I`;
- derived API: the compactness specialization identifying the direct sum of sections with the
  sections of the coproduct sheaf.

Source/core/bridge triage:
- `source-facing`: the canonical morphism `⨁ Γ(U, ℱ i) ⟶ Γ(U, ⨁ ℱ i)` from the Stacks item;
- `core/canonical`: `SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)`,
  `SheafOfModules.evaluation`, and `sigmaComparison`;
- `bridge/view`: the passage from `IsCompact (U : Set X)` to preservation of coproducts by
  sections over `U`. -/

variable {X : RingedSpace.{u}} {I : Type w}

local notation "𝒪X" => X.ringCatSheaf
local notation "ModX" => RingedSpace.Modules X

private theorem quasiCompactObject_of_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology X).QuasiCompactObject U := by
  sorry

-- Proof sketch: Chapter 18 gives the owner-level statement that evaluation on a quasi-compact
-- open preserves direct sums in `SheafOfModules`. The canonical comparison map for the coproduct
-- is therefore an isomorphism.
/-- Lemma 17.3.5: for a quasi-compact open `U`, the canonical comparison map
`⨁ Γ(U, ℱ i) ⟶ Γ(U, ⨁ ℱ)` is an isomorphism. -/
lemma ringedSpaceModule_sigmaComparison_isIso_of_isCompact
    (ℱ : I → ModX) [HasCoproduct ℱ]
    (U : Opens X)
    [HasCoproduct (fun b ↦ (SheafOfModules.evaluation 𝒪X (op U)).obj (ℱ b))]
    (hU : IsCompact (U : Set X)) :
    IsIso (sigmaComparison (SheafOfModules.evaluation 𝒪X (op U)) ℱ) := by
  let _ : PreservesColimit (Discrete.functor ℱ) (SheafOfModules.evaluation 𝒪X (op U)) := by
    let _ : PreservesColimitsOfShape (Discrete I) (SheafOfModules.evaluation 𝒪X (op U)) :=
      quasiCompactObject_module_evaluation_preserves_direct_sums 𝒪X U
        (quasiCompactObject_of_isCompact U hU) I
    infer_instance
  infer_instance

end AlgebraicGeometry.RingedSpace
