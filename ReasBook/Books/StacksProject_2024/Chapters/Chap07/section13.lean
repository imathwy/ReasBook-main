import Mathlib
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_13_1 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 7.13.1:
- primary domain: continuous functors between sites presented by precoverages;
- sampled owner API:
  `CategoryTheory.Precoverage.PullbacksPreservedBy`,
  `CategoryTheory.Functor.IsContinuous`,
  `CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`,
  `CategoryTheory.CoverPreserving`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project continuity condition at the precoverage level;
  `core/canonical`: `Precoverage.PullbacksPreservedBy` and `Functor.IsContinuous`;
  `bridge/view`: the relation `J ≤ K.comap u` and the passage to `Precoverage.toGrothendieck`.

Primitive data are the cover-preservation relation `J ≤ K.comap u` and pullback preservation along
members of covering families. Under the source pullback hypothesis, these data induce the
canonical owner `J.PullbacksPreservedBy u`; the resulting Grothendieck-topology continuity
statement and the cover-preservation result after passing to topologies are derived API.
-/

/-- Definition 7.13.1: for sites presented by covering families, a functor is continuous in the
Stacks Project sense if it sends covering families to covering families and the canonical
comparison map from the image of an induced fiber product to the induced fiber product of the
images is an isomorphism. -/
class IsContinuousSiteFunctor
    (u : C ⥤ D) (J : Precoverage C) (K : Precoverage D) : Prop where
  /-- Covering families are preserved, expressed via the canonical precoverage comap. -/
  toLeComap : J ≤ K.comap u
  /-- Pullbacks along arrows of covering families are preserved. Equivalently, the canonical
  pullback-comparison map into the induced image pullback is an isomorphism whenever the source
  pullback exists. -/
  preservesPullback
    {V : C} {R : Presieve V} (hR : R ∈ J V) {Y : C} {i : Y ⟶ V} (hi : R i)
    {T : C} (f : T ⟶ V) [HasPullback f i] :
    PreservesLimit (cospan f i) u

variable {J : Precoverage C} {K : Precoverage D} {u : C ⥤ D}

section

variable [J.HasPullbacks]

/-- Under the ambient pullback hypothesis on the source site, the Stacks Project continuity data
recover the canonical owner expressing preservation of pairwise pullbacks of covering families. -/
theorem IsContinuousSiteFunctor.pullbacksPreservedBy (h : IsContinuousSiteFunctor u J K) :
    J.PullbacksPreservedBy u := by
  refine ⟨?_⟩
  intro X R hR
  refine { preservesLimit := ?_ }
  intro Y Z f i hf hi
  let _ : HasPullback f i := (J.hasPairwisePullbacks_of_mem hR).has_pullbacks hf hi
  exact h.preservesPullback hR hi f

end

section

variable [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]
variable [J.HasPullbacks]

/-- A continuous site functor in the Stacks Project sense is cover-preserving for the associated
Grothendieck topologies. -/
theorem IsContinuousSiteFunctor.coverPreserving (h : IsContinuousSiteFunctor u J K) :
    CoverPreserving J.toGrothendieck K.toGrothendieck u where
  cover_preserve {U} {S} hS := by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
    rcases hS with ⟨R, hR, hRS⟩
    have hgen : Sieve.generate R ≤ S := (Sieve.giGenerate.gc R S).2 hRS
    apply K.toGrothendieck.superset_covering
      (Sieve.functorPushforward_monotone u U hgen)
    simpa [Sieve.generate_map_eq_functorPushforward] using
      Precoverage.generate_mem_toGrothendieck
        (show R.map u ∈ K (u.obj U) from h.toLeComap U hR)

end

section

variable [J.IsStableUnderBaseChange] [J.HasPullbacks]
variable [K.IsStableUnderBaseChange] [K.HasPullbacks]

/-- A continuous site functor in the Stacks Project sense is continuous in the canonical
sheaf-theoretic sense after passing from the source-facing sites to their associated
Grothendieck topologies. -/
instance instIsContinuousOfIsContinuousSiteFunctor
    [h : IsContinuousSiteFunctor u J K] :
    Functor.IsContinuous u J.toGrothendieck K.toGrothendieck :=
  by
    let _ : J.PullbacksPreservedBy u := h.pullbacksPreservedBy
    exact Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy u J K h.toLeComap

end

/-- The identity functor on a source-facing site is continuous in the Stacks Project sense. -/
instance isContinuousSiteFunctor_id (J : Precoverage C) :
    IsContinuousSiteFunctor (𝟭 C) J J where
  toLeComap := by
    intro X R hR
    simpa using hR
  preservesPullback _ _ _ := by infer_instance

end Functor

end CategoryTheory

/-! ### Lemma_7_13_2 (from Chap07) -/
open CategoryTheory

/- Domain-style sampling for Lemma 7.13.2:
- primary domain: continuous functors of Grothendieck sites and inverse-image preservation of
  sheaves of sets;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.op_comp_isSheaf_of_types`,
  `Functor.op_comp_isSheaf`,
  `Functor.sheafPushforwardContinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project statement that the inverse-image presheaf of a sheaf of
  sets along a continuous functor is again a sheaf;
  `core/canonical`: the continuity owner `Functor.IsContinuous` together with the theorem
  `Functor.op_comp_isSheaf_of_types`;
  `bridge/view`: `Functor.op_comp_isSheaf` and `Functor.sheafPushforwardContinuous`, which
  package the same preservation result for arbitrary target categories and as a functor on
  sheaves.

Primitive data are only the functor of sites, the two Grothendieck topologies, the continuity
instance, and the input sheaf. The resulting sheaf condition on `u.op ⋙ ℱ.obj` is derived API
from the canonical owner theorem, so this file should recall that theorem directly rather than
reintroducing a parallel local wrapper. -/

/- Lemma 7.13.2: if `u : C ⥤ D` is a continuous functor of sites and `ℱ` is a sheaf of sets on
`(D, K)`, then the inverse-image presheaf `u.op ⋙ ℱ.obj` on `(C, J)` is again a sheaf. This is
exactly the canonical site-theoretic owner
`Functor.op_comp_isSheaf_of_types`. -/
recall Functor.op_comp_isSheaf_of_types

/-! ### Lemma_7_13_3 (from Chap07) -/
open CategoryTheory Opposite

universe t u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ (ℱ : Cᵒᵖ ⥤ Type t), u.op.HasLeftKanExtension ℱ]
variable [HasWeakSheafify K (Type t)]

/- Domain-style sampling for Lemma 7.13.3:
- primary domain: inverse-image/direct-image adjunctions for continuous functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafAdjunctionContinuous`;
- source/core/bridge triage:
  `source-facing`: the sheafified left Kan extension `(u_p -)^#`;
  `core/canonical`: the constructed adjunction owner
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`;
  `bridge/view`: the abstract adjunction owner `Functor.sheafAdjunctionContinuous`,
  compared via `Functor.sheafPullbackConstruction.sheafPullbackIso`.

The primitive data are continuity, left Kan extensions, and weak sheafification; the adjunction is
derived API and should be recalled directly from the owner theorem. -/
/- Lemma 7.13.3: in the situation of Lemma 7.13.2, the functor sending a sheaf `\mathcal G` on
`(\mathcal C, J)` to the sheafification `(u_p \mathcal G)^\#` on `(\mathcal D, K)` is left
adjoint to the inverse-image functor `u^s` on sheaves. -/
recall Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

end

/-! ### Lemma_7_13_4 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/- Domain-style sampling for Lemma 7.13.4:
- primary domain: sheafification and continuous functors between Grothendieck sites;
- sampled owner API:
  `GrothendieckTopology.toSheafify`,
  `GrothendieckTopology.sheafifyMap`,
  `CategoryTheory.plusPlusIsoSheafify`,
  `CategoryTheory.toSheafify_plusPlusIsoSheafify_hom`,
  `Functor.W_map_of_adjunction_of_isContinuous`,
  `GrothendieckTopology.W_iff`;
- source/core/bridge triage:
  `source-facing`: the Stacks comparison morphism `(u_p G)^# ⟶ (u_p (G^#))^#`;
  `core/canonical`: the localization class `J.W` and its transport to `K.W` along `u.op.lan`;
  `bridge/view`: `K.W_iff`, which turns the owner-level `K.W` statement into the desired
  sheaf-level `IsIso` for `K.sheafifyMap ((u.op.lan).map (J.toSheafify G))`.

Primitive data are the sheafification unit `J.toSheafify G` and continuity of `u`. The isomorphism
statement is derived API from the canonical localization owner `W`, so the proof should use
the bridge from the concrete `P⁺⁺` map `J.toSheafify G` to the generic localization unit
`CategoryTheory.toSheafify J G`, transport along `u.op.lan`, and then convert back by `K.W_iff`.
-/

/-- Lemma 7.13.4: for a continuous functor of sites, the canonical comparison morphism
`(u_p G)^# ⟶ (u_p (G^#))^#`, namely the sheafification of the left Kan extension of
`J.toSheafify G`, is an isomorphism. -/
-- Proof sketch: compare the concrete `P⁺⁺` map `J.toSheafify G` with the generic localization
-- unit `CategoryTheory.toSheafify J G` via `plusPlusIsoSheafify`; the latter lies in `J.W` by
-- `J.W_toSheafify`. Transport that `W`-fact across `u.op.lan`, convert it back to a generic
-- sheafification isomorphism using `K.W_iff`, and finally conjugate by the `plusPlus`-to-generic
-- comparison on the target side to recover the concrete `K.sheafifyMap`.
theorem continuous_pullback_sheafification_comparison_isIso
    (G : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify G))) := by
  let A := Type (max u₁ u₂ v₁ v₂)
  let f := (u.op.lan).map (J.toSheafify G)
  have hJG : J.W (J.toSheafify G) := by
    refine (J.W.cancel_right_of_respectsIso (J.toSheafify G) (plusPlusIsoSheafify J A G).hom).1 ?_
    simpa [toSheafify_plusPlusIsoSheafify_hom J A G] using
      (J.W_toSheafify G : J.W (CategoryTheory.toSheafify J G))
  have hGeneric : IsIso ((presheafToSheaf K A).map f) := (K.W_iff _).1 <|
    u.W_map_of_adjunction_of_isContinuous J K (u.op.lan)
      (u.op.lanAdjunction A) (J.toSheafify G)
      hJG
  let e₁ := plusPlusIsoSheafify K A ((u.op.lan).obj G)
  let e₂ := plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify G))
  have hConcreteToGeneric :
      K.sheafifyMap f ≫ e₂.hom = e₁.hom ≫ CategoryTheory.sheafifyMap K f := by
    simpa [A, f, GrothendieckTopology.sheafification, CategoryTheory.sheafification] using
      (plusPlusFunctorIsoSheafification K A).hom.naturality f
  have hEq :
      K.sheafifyMap f = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
    calc
      K.sheafifyMap f = (K.sheafifyMap f ≫ e₂.hom) ≫ e₂.inv := by
        simp [Category.assoc]
      _ = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₂.inv) hConcreteToGeneric
  rw [hEq]
  let eGeneric :
      (presheafToSheaf K A).obj ((u.op.lan).obj G) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify G)) :=
    asIso ((presheafToSheaf K A).map f)
  have : IsIso (CategoryTheory.sheafifyMap K f) := by
    have hIsoPresheaf : IsIso ((sheafToPresheaf K A).map eGeneric.hom) := by infer_instance
    simpa [A, f, CategoryTheory.sheafifyMap] using hIsoPresheaf
  infer_instance

end

/-! ### Lemma_7_13_5 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Presheaf

universe u₁ u₂ v₁ v₂

/-
Domain-style sampling:
- primary domain: pullback of sheaves along a continuous functor of sites and its action on
  sheafified representables;
- sampled owner API:
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`,
  `GrothendieckTopology.uliftSheafifiedRepresentable`,
  `Presheaf.compULiftYonedaIsoULiftYonedaCompLan`;
- source-facing layer: the Stacks comparison `h_{u(U)}^# ⟶ u_sh(h_U^#)`;
- core/canonical owners: `K.uliftSheafifiedRepresentable (u.obj U)` and
  `(u.sheafPullback (Type ...) J K).obj (J.uliftSheafifiedRepresentable U)`;
- bridge/view: the proof passes through the explicit Kan-extension model
  `Functor.sheafPullbackConstruction.sheafPullback`, and only at the end moves to the chosen
  owner `u.sheafPullback` via `sheafPullbackIso`.

Primitive data are the continuous functor `u`, the sheafified representable owner
`uliftSheafifiedRepresentable`, and the Kan-extension comparison
`compULiftYonedaIsoULiftYonedaCompLan`. The public isomorphism is derived from that canonical data,
so the file should expose the owner-level comparison directly rather than storing a parallel raw
comparison morphism as a separate local API.
-/

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
variable [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
variable [Functor.IsContinuous u J K]
variable [∀ P : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]

/-- Lemma 7.13.5: for a continuous functor of sites, the sheaf pullback of the sheafified
representable `h_U^#` is canonically isomorphic to the sheafified representable `h_{u(U)}^#`. -/
noncomputable def continuous_sheafified_representable_iso (U : C) :
    uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K (u.obj U) ≅
      (u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) J K).obj
        (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) :=
  let A := Type (max u₁ u₂ v₁ v₂)
  let P : Cᵒᵖ ⥤ A := uliftYoneda.{max (max u₁ u₂ v₁ v₂) v₂, v₁, u₁}.obj U
  let e₁ :
      uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K (u.obj U) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj P) :=
    Functor.mapIso (presheafToSheaf K A)
      ((compULiftYonedaIsoULiftYonedaCompLan.{max u₁ u₂ v₁ v₂} u).app U)
  let _ : IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) :=
    continuous_pullback_sheafification_comparison_isIso u J K P
  let e₂Presheaf :
      (sheafToPresheaf K A).obj ((presheafToSheaf K A).obj ((u.op.lan).obj P)) ≅
        (sheafToPresheaf K A).obj
          ((presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P))) :=
    (plusPlusIsoSheafify K A ((u.op.lan).obj P)).symm ≪≫
      asIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) ≪≫
        plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify P))
  let e₂ :
      (presheafToSheaf K A).obj ((u.op.lan).obj P) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) :=
    (fullyFaithfulSheafToPresheaf K A).preimageIso e₂Presheaf
  let e₃ :
      (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) ≅
        (sheafPullback u A J K).obj
          (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) :=
    Functor.mapIso (presheafToSheaf K A)
      (Functor.mapIso (u.op.lan) (plusPlusIsoSheafify J A P))
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
    (sheafPullbackIso u (Type (max u₁ u₂ v₁ v₂)) J K).symm.app
      (uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U)

/-- The morphism underlying `continuous_sheafified_representable_iso` is an isomorphism. -/
-- Proof sketch: use the explicit isomorphism `continuous_sheafified_representable_iso u J K U`
-- and take the `IsIso` instance of its `hom`.
theorem continuous_sheafified_representable_iso_isIso
    (U : C) :
    IsIso (continuous_sheafified_representable_iso u J K U).hom := by
  -- The comparison map is the forward morphism of an explicit isomorphism.
  infer_instance

end

/-! ### Remark_7_13_6 (from Chap07) -/
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Helper for Remark 7.13.6: the componentwise image of a fixed-target family along a functor. -/
private def imageFamily (u : C ⥤ D) {V : C} (S : SemiRepresentableFamily.Over V) :
    SemiRepresentableFamily.Over (u.obj V) where
  index := S.index
  obj := fun i ↦ (Over.post u).obj (S.obj i)

/- Domain-style sampling for Remark 7.13.6:
- primary domain: quasi-continuous functors between sites and their canonical continuity owners;
- sampled owner API:
  `CategoryTheory.Functor.IsContinuousSiteFunctor`,
  `CategoryTheory.Functor.IsContinuous`,
  `CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`,
  `CategoryTheory.Over.post`,
  `CategoryTheory.SemiRepresentableFamily.map`,
  `CategoryTheory.SemiRepresentableFamily.Over.TautologicallyEquivalent`;
- source/core/bridge triage:
  `source-facing`: `Functor.IsQuasiContinuousSiteFunctor`;
  `core/canonical`: `Functor.IsContinuousSiteFunctor` and `Functor.IsContinuous`;
  `bridge/view`: the instance upgrading quasi-continuity to continuity.

Primitive data are:
1. mapped covering families being tautologically equivalent to covering families in the target
   site;
2. pullback-comparison isomorphisms for arrows in covering presieves, assuming only the
   pointwise source and target pullbacks needed to form that comparison map.

Derived API are the induced `IsContinuousSiteFunctor` structure and the resulting canonical
`Functor.IsContinuous` instance; the latter additionally uses global source and target pullbacks
through the existing precoverage-to-topology bridge.
-/

/-- Remark 7.13.6: a functor of sites is quasi-continuous if every `J`-covering family over `V`
maps to a family tautologically equivalent to some `K`-covering family over `u(V)`, and if base
change along each member of a covering family is preserved up to the canonical
pullback-comparison isomorphism. -/
class IsQuasiContinuousSiteFunctor
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) : Prop where
  image_cover_tautologicallyEquivalent :
    ∀ {V : C} (S : SemiRepresentableFamily.Over.{max u₁ v₁} V),
      IsCovering J.toPrecoverage S →
      ∃ T : SemiRepresentableFamily.Over.{max u₁ v₁} (u.obj V),
        IsCovering K.toPrecoverage T ∧
        TautologicallyEquivalent (imageFamily u S) T
  pullbackComparison_isIso_of_mem :
    ∀ {V : C} {R : Presieve V}, R ∈ J.toPrecoverage V →
      ∀ {Y : C} {i : Y ⟶ V}, R i →
      ∀ {T : C} (f : T ⟶ V) [HasPullback f i] [HasPullback (u.map f) (u.map i)],
        IsIso (pullbackComparison u f i)

theorem pullbackComparison_isIso_of_coveringFamily (h : IsQuasiContinuousSiteFunctor u J K)
    {V : C} (S : SemiRepresentableFamily.Over.{max u₁ v₁} V)
    (hS : IsCovering J.toPrecoverage S) {Y : C} {i : Y ⟶ V} (hi : S.toPresieve i)
    {T : C} (f : T ⟶ V) [HasPullback f i] [HasPullback (u.map f) (u.map i)] :
    IsIso (pullbackComparison u f i) :=
  h.pullbackComparison_isIso_of_mem hS hi f

/- Route correction: the local API does not provide `SemiRepresentableFamily.map`, so the mapped
family is expressed explicitly by `imageFamily` and compared through the generated sieve. -/
private theorem map_mem_of_image_cover_tautologicallyEquivalent
    {V : C} {R : Presieve V} (h : IsQuasiContinuousSiteFunctor u J K)
    (hR : R ∈ J.toPrecoverage V) :
    R.map u ∈ K.toPrecoverage (u.obj V) := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  let S : SemiRepresentableFamily.Over.{max u₁ v₁} V := ofArrows Y f
  -- Repackage the covering presieve as a covering family so the quasi-continuity hypothesis applies.
  rcases h.image_cover_tautologicallyEquivalent S (by simpa [S, IsCovering]) with ⟨T, hT, hST⟩
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  have hT' : Sieve.generate T.toPresieve ∈ K (u.obj V) := by
    exact (GrothendieckTopology.mem_toPrecoverage_iff K T.toPresieve).1 hT
  -- Tautological equivalence identifies the generated sieve of the mapped family with that of `T`.
  have hSieve :
      Sieve.generate ((Presieve.ofArrows Y f).map u) = Sieve.generate T.toPresieve := by
    simpa [S, imageFamily, toSieve, Presieve.map_ofArrows] using
      toSieve_eq_of_tautologicallyEquivalent hST
  rw [hSieve]
  exact hT'

private theorem preservesPullback_of_pullbackComparison_isIso_of_mem
    [HasPullbacks D]
    {V : C} {R : Presieve V} (h : IsQuasiContinuousSiteFunctor u J K)
    (hR : R ∈ J.toPrecoverage V) {Y : C} {i : Y ⟶ V} (hi : R i)
    {T : C} (f : T ⟶ V) [HasPullback f i] :
    PreservesLimit (cospan f i) u := by
  -- The ambient target pullback gives the comparison map, and quasi-continuity makes it an isomorphism.
  let _ : HasPullback (u.map f) (u.map i) := inferInstance
  let _ : IsIso (pullbackComparison u f i) := h.pullbackComparison_isIso_of_mem hR hi f
  exact PreservesPullback.of_iso_comparison u

instance instIsContinuousSiteFunctorOfIsQuasiContinuousSiteFunctor
    [HasPullbacks D]
    [h : IsQuasiContinuousSiteFunctor u J K] :
    IsContinuousSiteFunctor u J.toPrecoverage K.toPrecoverage where
  toLeComap := by
    intro V R hR
    exact map_mem_of_image_cover_tautologicallyEquivalent h hR
  preservesPullback {V} {R} hR {Y} {i} hi {T} f := by
    exact preservesPullback_of_pullbackComparison_isIso_of_mem h hR hi f

private theorem toPrecoverage_toGrothendieck_eq
    {E : Type*} [Category E] [HasPullbacks E] (L : GrothendieckTopology E) :
    L.toPrecoverage.toGrothendieck = L := by
  rw [← L.toPrecoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact (@Pretopology.gi E _ _).l_u_eq L

-- Proof sketch: the two source-facing clauses of quasi-continuity first recover the Chapter 7
-- precoverage-level owner `IsContinuousSiteFunctor u J.toPrecoverage K.toPrecoverage`, and then
-- the existing bridge from that owner yields mathlib's `Functor.IsContinuous`.
variable [HasPullbacks C] [HasPullbacks D]
variable (u : C ⥤ D)

/-- A quasi-continuous functor is continuous in the canonical sheaf-theoretic sense. -/
instance instIsContinuousOfIsQuasiContinuousSiteFunctor
    [IsQuasiContinuousSiteFunctor u J K] : Functor.IsContinuous u J K := by
  let _ :
      Functor.IsContinuousSiteFunctor
        u J.toPrecoverage K.toPrecoverage :=
    inferInstance
  simpa [toPrecoverage_toGrothendieck_eq J, toPrecoverage_toGrothendieck_eq K] using
    (inferInstance :
      Functor.IsContinuous
        u J.toPrecoverage.toGrothendieck K.toPrecoverage.toGrothendieck)

end Functor

end CategoryTheory
