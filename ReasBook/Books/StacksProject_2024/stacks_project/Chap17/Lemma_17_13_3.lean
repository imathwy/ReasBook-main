import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped AlgebraicGeometry

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

/-- Helper for Lemma 17.13.3: any zero module sheaf on a slice site is generated by one trivial
global section. -/
private theorem generatingSectionsOfIsZero
    {U : Opens X} (M : SheafOfModules (X.ringCatSheaf.over U))
    (hM : IsZero M) :
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
    sorry
  · intro hℱ
    -- Route correction: work on ambient opens chosen by
    -- `ambientOpenOfPreimage_eq_of_isClosedEmbedding`, then push generators forward on those
    -- matched opens and add the complement-open zero branch off the image.
    sorry

-- Closed-immersion bridge: `RingedSpace.IsClosedImmersion i` supplies the weaker closed
-- embedding and local-surjectivity hypotheses used by the core finite-type equivalence.
/-- Lemma 17.13.3: for a morphism of ringed spaces
`i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` that is a closed immersion, the pushforward `i_* ℱ`
is of finite type if and only if `ℱ` is of finite type. -/
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
