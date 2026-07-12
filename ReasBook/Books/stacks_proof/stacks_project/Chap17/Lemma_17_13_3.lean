import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry ZeroObject

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.13.3:
- primary domain: finite-type module sheaves on ringed spaces under pushforward along a closed
  embedding;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFiniteType`,
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.commRingSheafPushforwardMap`,
  `Topology.IsClosedEmbedding`,
  `Sheaf.IsLocallySurjective`,
  `RingedSpace.IsClosedImmersion`;
- best owner abstraction: the canonical owner predicate `SheafOfModules.IsFiniteType` on the
  direct-image object `(i _*).obj ℱ` inside the owner categories `Z.Modules` and `X.Modules`,
  with the ambient morphism data expressed at the weaker core layer by
  `Topology.IsClosedEmbedding i.hom.base` and
  `Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)`;
- primitive data: a morphism `i : Z ⟶ X`, a module sheaf `ℱ : Z.Modules`, the closed-embedding
  condition on `i.hom.base`, and local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z`;
- derived API: the finite-type reflection/preservation equivalence and its closed-immersion
  specialization.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for a closed immersion of ringed spaces;
- `core/canonical`: `RingedSpace.Modules`, `SheafOfModules.IsFiniteType`, the direct-image
  functor `i _*`, `Topology.IsClosedEmbedding i.hom.base`, and
  `Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)`;
- `bridge/view`: `RingedSpace.IsClosedImmersion i`, which packages the two hypotheses above with
  extra ideal-sheaf local-generation data not used in this finite-type statement.

The file should therefore expose a weaker core theorem at the closed-embedding plus locally
surjective layer, and keep the closed-immersion statement as the thin source-facing bridge. -/

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Z : RingedSpace.{u}}

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback

private instance opensOrderTop (X : RingedSpace.{u}) : OrderTop (Opens X) :=
  (inferInstance : CompleteLattice (Opens X)).toOrderTop

private instance opensHasFiniteLimits (X : RingedSpace.{u}) : HasFiniteLimits (Opens X) :=
  hasFiniteLimits_of_semilatticeInf_orderTop

private instance hasFiniteProducts_over {U : Opens X} :
    HasFiniteProducts (Over U) := by
  let _ : HasPullbacks (Opens X) := by infer_instance
  let _ : HasBinaryProducts (Over U) := inferInstance
  exact hasFiniteProducts_of_has_binary_and_terminal

/-- Helper for Lemma 17.13.3: at every point of the source, the induced map on local rings is
surjective once the structure-sheaf map `\mathcal O_X \to i_* \mathcal O_Z` is locally
surjective and the underlying map is a closed embedding. -/
lemma stalkMap_surjective_of_isClosedEmbedding_of_isLocallySurjective
    (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (z : Z) :
    Function.Surjective (PresheafedSpace.Hom.stalkMap i.hom z).hom := by
  let hloc :
      Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    inferInstance
  have hsurj :
      Function.Surjective
        ((TopCat.Presheaf.stalkFunctor CommRingCat (i.hom.base z)).map
          (RingedSpace.Hom.commRingSheafPushforwardMap i).hom) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
      (RingedSpace.Hom.commRingSheafPushforwardMap i).hom).1
      (show TopCat.Presheaf.IsLocallySurjective
          (RingedSpace.Hom.commRingSheafPushforwardMap i).hom from hloc)
      (i.hom.base z)
  haveI :
      IsIso (Z.presheaf.stalkPushforward CommRingCat i.hom.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
      hi.isInducing Z.presheaf z
  have hpush :
      Function.Surjective (Z.presheaf.stalkPushforward CommRingCat i.hom.base z) :=
    (ConcreteCategory.bijective_of_isIso _).2
  -- Proof comment: the ringed-space stalk map is exactly the locally surjective stalk map
  -- followed by the pushforward-stalk comparison isomorphism for the closed embedding.
  simpa using hpush.comp hsurj

/-- Helper for Lemma 17.13.3: a source open lying over `U` along a closed embedding is the exact
preimage of some ambient open contained in `U`. -/
private theorem ambientOpenOfPreimage_eq_of_isClosedEmbedding
    {f : Z → X} (hf : Topology.IsClosedEmbedding f)
    {U : Opens X} {V : Opens Z} (hV : V ≤ (Opens.map ⟨f, hf.continuous⟩).obj U) :
    ∃ W : Opens X, W ≤ U ∧ (Opens.map ⟨f, hf.continuous⟩).obj W = V := by
  rcases (hf.isInducing.isOpen_iff).1 V.isOpen with ⟨T, hTopen, hT⟩
  let W : Opens X := ⟨(U : Set X) ∩ T, U.isOpen.inter hTopen⟩
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · ext z
    constructor
    · intro hz
      have hzT : z ∈ f ⁻¹' T := hz.2
      simpa [hT] using hzT
    · intro hz
      refine ⟨?_, ?_⟩
      · exact hV hz
      ·
        have hzT : z ∈ f ⁻¹' T := by
          simpa [hT] using hz
        exact hzT

/-- Helper for Lemma 17.13.3: a point outside the image of a closed embedding admits an open
neighborhood disjoint from that image. -/
private theorem exists_open_neighborhood_disjoint_range_of_isClosedEmbedding
    {f : Z → X} (hf : Topology.IsClosedEmbedding f)
    {x : X} (hx : x ∉ Set.range f) :
    ∃ W : Opens X, x ∈ W ∧ Disjoint (W : Set X) (Set.range f) := by
  let W : Opens X := ⟨(Set.range f)ᶜ, by
    -- Proof comment: the image of a closed embedding is closed, so its complement is open.
    simpa using hf.isClosed_range.isOpen_compl⟩
  refine ⟨W, hx, ?_⟩
  -- Proof comment: the chosen neighborhood is exactly the complement of the image.
  rw [Set.disjoint_left]
  intro y hyW hyRange
  exact hyW hyRange

/-- Helper for Lemma 17.13.3: a surjective restriction of scalars does not shrink the span of a
family of module elements. -/
lemma span_eq_top_restrictScalars_of_surjective
    {R S M : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hf : Function.Surjective (algebraMap R S))
    {ι : Type u} (g : ι → M)
    (hspan : Submodule.span S (Set.range g) = ⊤) :
    Submodule.span R (Set.range g) = ⊤ := by
  let P : Submodule R M := Submodule.span R (Set.range g)
  let Q : Submodule S M :=
    { carrier := P
      zero_mem' := P.zero_mem
      add_mem' := fun hm₁ hm₂ ↦ P.add_mem hm₁ hm₂
      smul_mem' := by
        intro s m hm
        rcases hf s with ⟨r, rfl⟩
        -- Surjectivity lifts `S`-scalars back to `R`-scalars inside the restricted span.
        simpa using P.smul_mem r hm }
  have hle : Submodule.span S (Set.range g) ≤ Q := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  -- Once the `S`-span is all of `M`, the auxiliary `S`-submodule `Q` must also be all of `M`.
  refine le_antisymm le_top ?_
  intro m hm_top
  have hmS : m ∈ Submodule.span S (Set.range g) := by
    simpa [hspan] using hm_top
  have hmQ : m ∈ Q := by
    exact hle hmS
  exact hmQ

/-- Helper for Lemma 17.13.3: if a family spans after restricting scalars, then it already spans
over the larger coefficient ring. -/
lemma span_eq_top_of_span_eq_top_restrictScalars
    {R S M : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    {ι : Type u} (g : ι → M)
    (hspan : Submodule.span R (Set.range g) = ⊤) :
    Submodule.span S (Set.range g) = ⊤ := by
  let P : Submodule R M := (Submodule.span S (Set.range g)).restrictScalars R
  have hle : Submodule.span R (Set.range g) ≤ P := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  refine le_antisymm le_top ?_
  intro m hm_top
  have hmR : m ∈ Submodule.span R (Set.range g) := by
    simpa [hspan] using hm_top
  exact hle hmR

/-- Helper for Lemma 17.13.3: sections of the restriction `M.over U` are recovered by evaluating
at the terminal object `U → U` of the slice over `U`. -/
private noncomputable def restrictSectionEquiv
    (M : RingedSpace.Modules X) (U : Opens X) :
    (M.over U).sections ≃ M.val.obj (op U) := by
  refine
    { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
      invFun := fun m ↦
        (M.over U).val.sectionsMk
          (fun V ↦ (M.over U).val.map ((Over.mkIdTerminal.from V.unop).op) m)
          ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro V Y f
    -- Proof comment: every object of `Over U` has a unique morphism to the terminal object
    -- `Over.mk (𝟙 U)`, so the compatibility condition reduces to functoriality.
    have h :
        (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
      apply Quiver.Hom.unop_inj
      simp only [Quiver.Hom.unop_op]
      exact Over.mkIdTerminal.hom_ext
        (f.unop ≫ Over.mkIdTerminal.from V.unop)
        (Over.mkIdTerminal.from Y.unop)
    rw [← PresheafOfModules.map_comp_apply, h]
  · intro s
    -- Proof comment: a section on the slice is determined by its restrictions from the terminal
    -- object.
    ext V
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)
  · intro m
    -- Proof comment: evaluating the constructed section back at the terminal object recovers the
    -- original ambient section.
    change (M.over U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (M.over U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.13.3: sections of a further restriction `M.over W` inside the slice over
`U` are recovered by evaluating at the terminal object `W → W`. -/
private noncomputable def overSectionsEquivObj
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U)) (W : Over U) :
    (M.over W).sections ≃ M.val.obj (op W) := by
  refine
    { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 W)))
      invFun := fun m ↦
        (M.over W).val.sectionsMk
          (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m)
          ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro V Y f
    -- Proof comment: every object of `Over W` has a unique morphism to the terminal object
    -- `Over.mk (𝟙 W)`, so compatibility is just functoriality.
    have h :
        (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
      apply Quiver.Hom.unop_inj
      simp only [Quiver.Hom.unop_op]
      exact Over.mkIdTerminal.hom_ext
        (f.unop ≫ Over.mkIdTerminal.from V.unop)
        (Over.mkIdTerminal.from Y.unop)
    rw [← PresheafOfModules.map_comp_apply, h]
  · intro s
    -- Proof comment: a section on the iterated slice is determined by its restrictions from the
    -- terminal object.
    ext V
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)
  · intro m
    -- Proof comment: evaluating the reconstructed section back at the terminal object recovers the
    -- original objectwise section.
    change (M.over W).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 W))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 W)) = 𝟙 (Over.mk (𝟙 W)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using (M.over W).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.13.3: restriction to a slice object `W : Over U` is the canonical
pushforward functor into the iterated slice module category. -/
private abbrev overRestrictionFunctor
    {U : Opens X} (W : Over U) :
    SheafOfModules (X.ringCatSheaf.over U) ⥤
      SheafOfModules ((X.ringCatSheaf.over U).over W) :=
  SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf.over U).over W))

/-- Helper for Lemma 17.13.3: restricting the generating epimorphism of a generating family keeps
it epic on the slice over `W`. -/
private theorem restrictedGeneratingPiEpi
    {U : Opens X} {M : SheafOfModules (X.ringCatSheaf.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    Epi ((overRestrictionFunctor W).map σ.π) := by
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤
      SheafOfModules ((X.ringCatSheaf.over U).over W) :=
    overRestrictionFunctor W
  letI : Functor.PreservesEpimorphisms F :=
    Functor.preservesEpimorphisms_of_adjunction
      (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf.over U) W)
  -- Proof comment: restriction to `W` is a left adjoint on module sheaves, so it preserves the
  -- epimorphic generating map `σ.π`.
  change Epi (F.map σ.π)
  infer_instance

/-- Helper for Lemma 17.13.3: restriction to the iterated slice over `W` preserves the coproducts
used in the free sheaf on generators indexed by `I`. -/
private instance overRestrictionFunctorPreservesColimitsOfShape
    {U : Opens X} (W : Over U) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (overRestrictionFunctor W) := by
  dsimp [overRestrictionFunctor]
  infer_instance

/-- Helper for Lemma 17.13.3: `mapFree` identifies restriction of the ambient free sheaf with the
canonical free sheaf on the slice over `W`. -/
private abbrev overRestrictionFreeIso
    {U : Opens X} (W : Over U) (I : Type u) :
    (overRestrictionFunctor W).obj
        (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules ((X.ringCatSheaf.over U).over W)) :=
  SheafOfModules.mapFree
    (overRestrictionFunctor W)
    (Iso.refl (SheafOfModules.unit ((X.ringCatSheaf.over U).over W)))
    I

/-- Helper for Lemma 17.13.3: the `mapFree` comparison carries each ambient free basis morphism to
the corresponding basis morphism on the slice free sheaf. -/
private theorem overRestrictionFreeIso_hom_ιFree
    {U : Opens X} (W : Over U) (I : Type u) (i : I) :
    (overRestrictionFunctor W).map
        (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i) ≫
        (overRestrictionFreeIso W I).hom =
      SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over W) i := by
  -- Proof comment: this is the basis-vector computation built into `mapFree`.
  simpa [overRestrictionFunctor, overRestrictionFreeIso] using
    (SheafOfModules.map_ιFree_mapFree_hom
      (F := SheafOfModules.pushforward (𝟙 ((X.ringCatSheaf.over U).over W)))
      (η := Iso.refl (SheafOfModules.unit ((X.ringCatSheaf.over U).over W)))
      (I := I) (i := i))

/-- Helper for Lemma 17.13.3: the inverse `mapFree` transport sends the slice free basis section
to the restricted ambient free basis section. -/
private theorem restrictedFreeBasisTransport
    {U : Opens X} (I : Type u) (W : Over U) (i : I) :
    SheafOfModules.sectionsMap
        ((overRestrictionFreeIso W I).inv)
        (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over W) i) =
      (overSectionsEquivObj
          (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) W).symm
        ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op W)) := by
  -- Route correction: avoid unfolding the section equivalence at the terminal object by hand.
  -- The stable route is to compare the basis inclusions through `mapFree.hom` and then read the
  -- resulting section equality through `overSectionsEquivObj`.
  let e := overRestrictionFreeIso W I
  have hiota :
      (overRestrictionFunctor W).map
          (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i) =
        SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over W) i ≫ e.inv := by
    -- Proof comment: compare the basis inclusions through `mapFree.hom` and cancel the
    -- isomorphism.
    apply (cancel_mono e.hom).1
    simpa [Category.assoc] using overRestrictionFreeIso_hom_ιFree (X := X) W I i
  calc
    SheafOfModules.sectionsMap e.inv
        (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over W) i) =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over W))
        (SheafOfModules.ιFree (R := (X.ringCatSheaf.over U).over W) i ≫ e.inv) := by
          rfl
    _ =
      SheafOfModules.unitHomEquiv
        (((SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)).over W))
        ((overRestrictionFunctor W).map
          (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i)) := by
          rw [← hiota]
  apply (overSectionsEquivObj
      (SheafOfModules.free.{u} I : SheafOfModules (X.ringCatSheaf.over U)) W).injective
  -- Proof comment: evaluating the restricted ambient basis morphism at the terminal object gives
  -- the ambient basis section restricted to `W`.
  rfl

/-- Helper for Lemma 17.13.3: under the canonical section equivalence, the restricted morphism
acts on sections by the ambient component map on `W`. -/
private theorem overSectionsEquivObj_sectionsMap
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (W : Over U) (s : (M.over W).sections) :
    (overSectionsEquivObj N W)
      (SheafOfModules.sectionsMap ((overRestrictionFunctor W).map ψ) s) =
        (ψ.val.app (op W)) ((overSectionsEquivObj M W) s) := by
  -- Proof comment: evaluating the restricted section map at the terminal object of the iterated
  -- slice recovers the original component map on `W`.
  change (((overRestrictionFunctor W).map ψ).val.app
      (op (Over.mk (𝟙 W)))) (s.1 (op (Over.mk (𝟙 W)))) =
    (ψ.val.app (op W)) (s.1 (op (Over.mk (𝟙 W))))
  rfl

/-- Helper for Lemma 17.13.3: the inverse of the section equivalence is natural in the sheaf
morphism. -/
private theorem sectionsMap_overSectionsEquivObj_symm
    {U : Opens X} {M N : SheafOfModules (X.ringCatSheaf.over U)}
    (ψ : M ⟶ N) (W : Over U) (m : M.val.obj (op W)) :
    SheafOfModules.sectionsMap ((overRestrictionFunctor W).map ψ)
        ((overSectionsEquivObj M W).symm m) =
      (overSectionsEquivObj N W).symm ((ψ.val.app (op W)) m) := by
  -- Proof comment: compare the two sections after evaluating them at the terminal object of
  -- `Over W`.
  apply (overSectionsEquivObj N W).injective
  rw [overSectionsEquivObj_sectionsMap]
  simp

/-- Helper for Lemma 17.13.3: restricting a generating family to `W` gives, after the canonical
slice identification, the free morphism attached to the restricted sections. -/
private theorem restrictedGeneratingPiEqFreeHom
    {U : Opens X} {M : SheafOfModules (X.ringCatSheaf.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    (overRestrictionFreeIso W σ.I).inv ≫
      (overRestrictionFunctor W).map σ.π =
      (((M.over W).freeHomEquiv).symm
        (fun i ↦ (overSectionsEquivObj M W).symm ((σ.s i).1 (op W)))) := by
  -- Route correction: compare the two morphisms by their free-basis coordinates instead of
  -- unfolding the restricted generating map directly.
  apply ((M.over W).freeHomEquiv).injective
  funext i
  calc
    (M.over W).freeHomEquiv
        ((overRestrictionFreeIso W σ.I).inv ≫
          (overRestrictionFunctor W).map σ.π) i =
      SheafOfModules.sectionsMap
        ((overRestrictionFunctor W).map σ.π)
        ((((SheafOfModules.free.{u} σ.I :
            SheafOfModules (X.ringCatSheaf.over U)).over W).freeHomEquiv)
          ((overRestrictionFreeIso W σ.I).inv) i) := by
            simpa using
              (SheafOfModules.freeHomEquiv_comp_apply
                (f := (overRestrictionFreeIso W σ.I).inv)
                (p := (overRestrictionFunctor W).map σ.π)
                (i := i))
    _ = SheafOfModules.sectionsMap
        ((overRestrictionFunctor W).map σ.π)
        (SheafOfModules.sectionsMap
          ((overRestrictionFreeIso W σ.I).inv)
          (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over W) i)) := by
            simpa using
              (SheafOfModules.freeHomEquiv_apply
                (M := ((SheafOfModules.free.{u} σ.I :
                  SheafOfModules (X.ringCatSheaf.over U)).over W))
                (f := (overRestrictionFreeIso W σ.I).inv)
                (i := i))
    _ = SheafOfModules.sectionsMap
        ((overRestrictionFunctor W).map σ.π)
        ((overSectionsEquivObj
            (SheafOfModules.free.{u} σ.I : SheafOfModules (X.ringCatSheaf.over U)) W).symm
          ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op W))) := by
            rw [restrictedFreeBasisTransport]
    _ = (overSectionsEquivObj M W).symm
          ((σ.s i).1 (op W)) := by
            exact sectionsMap_overSectionsEquivObj_symm (ψ := σ.π) W
              ((SheafOfModules.freeSection (R := X.ringCatSheaf.over U) i).1 (op W))
    _ = SheafOfModules.sectionsMap
        (((M.over W).freeHomEquiv).symm
          (fun j ↦ (overSectionsEquivObj M W).symm ((σ.s j).1 (op W))))
        (SheafOfModules.freeSection (R := (X.ringCatSheaf.over U).over W) i) := by
            symm
            simpa using
              (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
                (R := (X.ringCatSheaf.over U).over W)
                (f := fun j ↦ (overSectionsEquivObj M W).symm ((σ.s j).1 (op W)))
                i)

/-- Helper for Lemma 17.13.3: the restricted free morphism attached to the restricted generators
is epic because it is an isomorphic transport of the restricted ambient generating map. -/
private theorem restrictedGeneratingSections_epi
    {U : Opens X} {M : SheafOfModules (X.ringCatSheaf.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    Epi ((((M.over W).freeHomEquiv).symm
      (fun i ↦ (overSectionsEquivObj M W).symm ((σ.s i).1 (op W))))) := by
  -- Proof comment: rewrite the desired map as the restricted ambient generating map preceded by
  -- the canonical free-sheaf isomorphism, then preserve epimorphicity across that transport.
  rw [← restrictedGeneratingPiEqFreeHom (σ := σ) W]
  let _ : Epi ((overRestrictionFunctor W).map σ.π) :=
    restrictedGeneratingPiEpi σ W
  infer_instance

/-- Helper for Lemma 17.13.3: restricting a generating family along `W : Over U` yields a
generating family on the iterated slice. -/
private noncomputable def restrictedGeneratingSections
    {U : Opens X} {M : SheafOfModules (X.ringCatSheaf.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    (M.over W).GeneratingSections :=
  { I := σ.I
    s := fun i ↦ (overSectionsEquivObj M W).symm ((σ.s i).1 (op W))
    epi := restrictedGeneratingSections_epi σ W }

/-- Helper for Lemma 17.13.3: any zero module sheaf on a slice site is generated by one trivial
global section. -/
private noncomputable def generatingSectionsOfIsZero
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (hM : Limits.IsZero M) :
    M.GeneratingSections := by
  let σfree :
      (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit)).GeneratingSections :=
    { I := ULift.{u, 0} Unit
      s := SheafOfModules.freeSection (R := X.ringCatSheaf.over U)
      epi := by
        -- Proof comment: the tautological free basis is the identity morphism under
        -- `freeHomEquiv`.
        change Epi
          (((SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit)).freeHomEquiv).symm
            (((SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit)).freeHomEquiv)
              (𝟙 (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit)))))
        simpa using
          (show Epi (𝟙 (SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit)))
            from inferInstance) }
  let π :
      SheafOfModules.free (R := X.ringCatSheaf.over U) (ULift.{u, 0} Unit) ⟶
        (0 : SheafOfModules (X.ringCatSheaf.over U)) :=
    0
  let _ : Epi π := inferInstance
  let σzero : (0 : SheafOfModules (X.ringCatSheaf.over U)).GeneratingSections := σfree.ofEpi π
  -- Proof comment: transport the trivial generating family across the canonical zero isomorphism.
  exact (SheafOfModules.GeneratingSections.equivOfIso hM.isoZero.symm) σzero

/-- Helper for Chap17 Lemma 17 13 3: a point-indexed family of open neighborhoods gives a
Grothendieck cover of the terminal object. -/
private theorem pointwiseFiniteOpenCoverCoversTop
    (U : X → Opens X) (hU : ∀ x : X, x ∈ U x) :
    (Opens.grothendieckTopology X).CoversTop U := by
  -- Proof comment: refine any point of an open `V` to the smaller neighborhood `V ∩ U x`.
  intro V x hx
  refine ⟨V ⊓ U x, CategoryTheory.homOfLE inf_le_left, ?_, ?_⟩
  · exact ⟨x, ⟨CategoryTheory.homOfLE inf_le_right⟩⟩
  · exact ⟨hx, hU x⟩

/-- Helper for Chap17 Lemma 17 13 3: pointwise neighborhoods carrying finitely many generating
sections package into the canonical finite-type owner. -/
private theorem isFiniteTypeOfPointwiseFiniteGeneratingNeighborhoods
    (M : RingedSpace.Modules X)
    (h :
      ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (σ : (M.over U).GeneratingSections), σ.IsFiniteType) :
    M.IsFiniteType := by
  classical
  -- Proof comment: choose one finite generating neighborhood for each point and package them into
  -- a point-indexed `LocalGeneratorsData`.
  choose U hU σ hσ using h
  let τ : M.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := pointwiseFiniteOpenCoverCoversTop U hU
      generators := σ }
  have hτ : τ.IsFiniteType := by
    -- Proof comment: each chosen neighborhood already comes with finitely many generators.
    refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk (p := τ) ?_
    intro x
    exact hσ x
  exact SheafOfModules.IsFiniteType.mk (M := M) ⟨τ, hτ⟩

-- Proof sketch: for the forward implication, finite local generators of `ℱ` on opens in `Z`
-- induce finite local generators of `i_* ℱ` on the corresponding opens in `X`, using the closed
-- embedding to identify neighborhoods on the image and the local surjectivity of
-- `𝒪_X ⟶ i_* 𝒪_Z` to lift the module coefficients. For the converse implication, restrict finite
-- local generators of `i_* ℱ` near points of the image back to `Z` and identify stalks along the
-- closed embedding.
/-- Core companion: if `i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` has underlying map a closed
embedding and the canonical map `\mathcal O_X \to i_* \mathcal O_Z` is locally surjective, then
`i_* ℱ` is of finite type if and only if `ℱ` is of finite type. -/
theorem pushforward_isFiniteType_iff_of_isClosedEmbedding_of_isLocallySurjective
    (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (ℱ : Z.Modules) :
    ((i _*).obj ℱ).IsFiniteType ↔ ℱ.IsFiniteType := by
  constructor
  · intro hpush
    -- Route correction: the adjunction-counit route kept stalling on tensor normalization.
    -- The intended next step is the matched-open route, pulling finite generators of `i_* ℱ`
    -- back to generators of `ℱ` on preimage opens.
    refine isFiniteTypeOfPointwiseFiniteGeneratingNeighborhoods ℱ ?_
    intro z
    obtain ⟨τ, hτ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData ((i _*).obj ℱ)
    obtain ⟨V, _iV, hmem, hzV⟩ := τ.coversTop ⊤ (i.hom.base z) (by trivial)
    obtain ⟨j, ⟨f⟩⟩ := hmem
    let U : Opens X := τ.X j
    let σ : (((i _*).obj ℱ).over U).GeneratingSections := τ.generators j
    let _ : σ.IsFiniteType := hτ.isFiniteType j
    -- TODO: transfer the finite generating family `σ` on `((i_* ℱ)|_U)` to a finite generating
    -- family on `ℱ|_{i^{-1}(U)}` by identifying the pulled-back sections via
    -- `restrictSectionEquiv` and proving stalkwise span-surjectivity using
    -- `span_eq_top_of_span_eq_top_restrictScalars`.
    let _ := f
    let _ := hzV
    let _ := σ
    sorry
  · intro hℱ
    -- Route correction: work on ambient opens chosen by
    -- `ambientOpenOfPreimage_eq_of_isClosedEmbedding`, then push generators forward on those
    -- matched opens and add the complement-open zero branch off the image.
    refine isFiniteTypeOfPointwiseFiniteGeneratingNeighborhoods ((i _*).obj ℱ) ?_
    intro x
    by_cases hx : x ∈ Set.range i.hom.base
    · rcases hx with ⟨z, rfl⟩
      obtain ⟨τ, hτ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData ℱ
      obtain ⟨V, _iV, hmem, hzV⟩ := τ.coversTop ⊤ z (by trivial)
      obtain ⟨j, ⟨f⟩⟩ := hmem
      let W : Opens Z := τ.X j
      let σ : (ℱ.over W).GeneratingSections := τ.generators j
      let _ : σ.IsFiniteType := hτ.isFiniteType j
      -- TODO: choose an ambient open `U` with `i^{-1}(U) = W`, transport the source generators
      -- to `((i_* ℱ)|_U)` through that equality, and prove they generate stalkwise using
      -- `stalkMap_surjective_of_isClosedEmbedding_of_isLocallySurjective` together with
      -- `span_eq_top_restrictScalars_of_surjective`.
      let _ := f
      let _ := hzV
      let _ := σ
      sorry
    · obtain ⟨U, hxU, hdisj⟩ :=
        exists_open_neighborhood_disjoint_range_of_isClosedEmbedding hi hx
      -- TODO: show `((i_* ℱ)|_U)` is zero when `U` is disjoint from the image, then reuse
      -- `generatingSectionsOfIsZero` to get a finite generating family on that branch.
      let _ := hdisj
      let _ := hxU
      sorry

-- Closed-immersion bridge: `RingedSpace.IsClosedImmersion i` supplies the weaker closed
-- embedding and local-surjectivity hypotheses used by the core finite-type equivalence.
/-- Lemma 17.13.3: for a morphism of ringed spaces
`i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` that is a closed immersion, the pushforward `i_* ℱ`
is of finite type if and only if `ℱ` is of finite type. -/
@[stacks 01C4]
theorem pushforward_isFiniteType_iff_of_isClosedImmersion
    (i : Z ⟶ X)
    [RingedSpace.IsClosedImmersion i]
    (ℱ : Z.Modules) :
    ((i _*).obj ℱ).IsFiniteType ↔ ℱ.IsFiniteType := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact
    pushforward_isFiniteType_iff_of_isClosedEmbedding_of_isLocallySurjective i
      hi.isClosedEmbedding ℱ

end AlgebraicGeometry.RingedSpace.Hom
