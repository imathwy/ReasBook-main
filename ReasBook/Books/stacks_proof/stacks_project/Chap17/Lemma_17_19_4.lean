import Mathlib
import StacksProject_2024.Chap05.Lemma_5_23_3
import StacksProject_2024.Chap06.ClosedSubsetInclusion
import StacksProject_2024.Chap06.Lemma_6_16_1
import StacksProject_2024.Chap06.Lemma_6_21_5
import StacksProject_2024.Chap06.Lemma_6_27_2
import StacksProject_2024.Chap06.Lemma_6_32_1
import StacksProject_2024.Chap06.Lemma_6_32_2
import StacksProject_2024.Chap17.Lemma_17_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Topology
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

local notation:max "i[" Z "]" => X.closedSubsetInclusion (Z : Set X)

/- Domain-style sampling for Lemma 17.19.4:
- primary domain: set-valued sheaves on spectral spaces and embeddings into finite products of
  pushforwards from closed subspaces;
- sampled owner declarations:
  `HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation`,
  `exists_finite_sober_sheaf_model_of_constructible_set_presentation`,
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `constantSheaf`;
- best owner abstraction: on the spectral-space branch, the source-facing hypothesis should use
  the Chapter 17 compact-open coequalizer-presentation owner, while the individual product factors
  should be stated directly using the canonical closed-subset inclusion and ambient sheaf
  pushforward rather than a local wrapper built from `TopCat.of Z` and `Subtype.val`;
- primitive data: a compact-open finite lower-shriek constant coequalizer presentation of `ℱ`;
- derived API: the finite family of constructible closed subsets of `X`, the corresponding product
  sheaf, and the monomorphism from `ℱ`.

Source/core/bridge triage:
- `source-facing`: the finite-product embedding statement from constructible closed pieces;
- `core/canonical`: the Chapter 17 compact-open presentation owner,
  `TopCat.closedSubsetInclusion`, `Sheaf.pushforward`, `constantSheaf`;
- `bridge/view`: the finite-sober descent input from Lemma `17.19.3`.
-/

-- Proof sketch: use Lemma `17.19.3` to descend `ℱ` to a sheaf with finite stalks on a finite sober
-- space `Y`. On `Y`, the canonical map into the product of the skyscraper sheaves
-- `∏_{y ∈ Y} i_{y, *} \underline{\mathcal G_y}` is monic. Pull this embedding back along the
-- spectral map `X ⟶ Y`; the inverse images of the point closures in `Y` are constructible closed
-- subsets of `X`, and the corresponding finite stalk sets give the required finite product.
/-- Helper for Lemma 17.19.4: on a finite space, the canonical map from a sheaf to the product of
the skyscraper sheaves of its stalks is a monomorphism. -/
lemma mono_finiteSkyscraperUnitProduct {Y : TopCat.{u}} [Finite Y] (𝒢 : Sh(Y)) :
    Mono
      (Limits.Pi.lift
        (fun y : Y ↦ ((stalkSkyscraperSheafAdjunction (C := Type u) y).unit.app 𝒢).hom)) := by
  classical
  -- Reduce monomorphy to injectivity on every stalk.
  rw [sheaf_mono_iff_stalk_injective]
  intro x
  intro a b hab
  have hproj :=
    congrArg
      (fun z ↦
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (Limits.Pi.π (fun y : Y ↦ skyscraperSheaf y (𝒢.presheaf.stalk y)) x).hom) z)
      hab
  have hunit :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((stalkSkyscraperSheafAdjunction (C := Type u) x).unit.app 𝒢).hom)) ≫
        (skyscraperSheaf_stalk_iso_of_mem_closure
          (A := 𝒢.presheaf.stalk x) x x (by simp)).hom =
          𝟙 (𝒢.presheaf.stalk x) := by
    -- The stalk map of the adjunction unit is the inverse of the canonical skyscraper stalk
    -- identification at the distinguished point.
    simpa [skyscraperSheaf_stalk_iso_of_mem_closure,
      StalkSkyscraperPresheafAdjunctionAuxs.unit_app] using
      (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper
        (p₀ := x) (f := 𝟙 (𝒢.presheaf.stalk x)))
  have hleft :
      Function.LeftInverse
        (skyscraperSheaf_stalk_iso_of_mem_closure
          (A := 𝒢.presheaf.stalk x) x x (by simp)).hom
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((stalkSkyscraperSheafAdjunction (C := Type u) x).unit.app 𝒢).hom)) := by
    intro s
    exact congrFun hunit s
  -- Projecting the product equality to the `x`-component recovers equality under the unit map.
  have hmap :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((stalkSkyscraperSheafAdjunction (C := Type u) x).unit.app 𝒢).hom)) a =
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((stalkSkyscraperSheafAdjunction (C := Type u) x).unit.app 𝒢).hom)) b := by
    simpa using hproj
  exact hleft.injective hmap

/-- Helper for Lemma 17.19.4: away from `closure {y}`, the stalk of the pullback of the
skyscraper sheaf at `y` is terminal. -/
private theorem pullbackSkyscraper_stalk_isTerminal_of_not_mem_preimageClosure
    {Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) (A : Type u) {x : X}
    (hx : x ∉ f ⁻¹' closure ({y} : Set Y)) :
    IsTerminal ((((f⁻¹).obj (skyscraperSheaf y A)).presheaf.stalk x)) := by
  classical
  let _ : HasFilteredColimits (Type u) := hasFilteredColimitsOfSize_of_hasColimitsOfSize
  let _ : PreservesLimits (forget (Type u)) :=
    CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeHom
  let _ : PreservesFilteredColimits (forget (Type u)) := by
    let _ : PreservesColimits (forget (Type u)) :=
      CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeHom
    exact PreservesColimits.preservesFilteredColimits (forget (Type u))
  let _ : (forget (Type u)).ReflectsIsomorphisms :=
    CategoryTheory.instReflectsIsomorphismsForgetTypeHom
  -- Transport the skyscraper stalk computation on `Y` across the pullback stalk comparison.
  let e := TopCat.Sheaf.stalkPullbackIso (A := Type u) f (skyscraperSheaf y A) x
  refine IsTerminal.ofIso
    (skyscraperSheaf_stalk_isTerminal_of_not_mem_closure (x := y) (A := A) (x' := f x) ?_)
    e.symm
  simpa [Set.mem_preimage] using hx

/-- Helper for Lemma 17.19.4: a constant sheaf pushed forward from a closed subset has terminal
stalk away from that closed subset. -/
private theorem closedSubsetConstantFactor_stalk_isIso_terminal_from_of_not_mem
    (Z : Closeds X) (A : Type u) {x : X} (hx : x ∉ (Z : Set X)) :
    IsIso
      (terminal.from
        (((Sheaf.pushforward (Type u) i[Z]).obj
          ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
              (Type u)).obj A)).presheaf.stalk x)) := by
  -- This is exactly the closed-subset stalk computation specialized to the constant sheaf on `Z`.
  simpa using
    (closedSubsetTypeSheaf_pushforward_stalk_unique_of_not_mem
      (X := X) (Z := (Z : Set X)) (hZ := Z.2)
      (((constantSheaf (Opens.grothendieckTopology (TopCat.of (Z : Set X))) (Type u)).obj A))
      (x := x) hx)

/-- Helper for Lemma 17.19.4: the pullback of a skyscraper sheaf is supported on the preimage of
the closure of its support point, so it already lies in the essential image of pushforward from
that closed subset. -/
private theorem pullbackSkyscraper_memEssImage_preimageClosure
    {Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) (A : Type u) :
    let Z : Closeds X :=
      ⟨f ⁻¹' closure ({y} : Set Y), isClosed_closure.preimage f.hom.continuous⟩
    (Sheaf.pushforward (Type u) i[Z]).essImage ((f⁻¹).obj (skyscraperSheaf y A)) := by
  intro Z
  -- The closed-subset essential-image criterion reduces the claim to the already-proved
  -- off-support stalk terminality for the pulled-back skyscraper sheaf.
  rw [closedSubsetTypeSheafPushforward_essImage_iff_stalk_isTerminal_of_not_mem
    (X := X) (Z := (Z : Set X)) (hZ := Z.2) ((f⁻¹).obj (skyscraperSheaf y A))]
  intro x hx
  exact IsTerminal.isIso_from
    (pullbackSkyscraper_stalk_isTerminal_of_not_mem_preimageClosure
      (X := X) f y A (x := x) (by simpa [Z] using hx))
    _

/-- Helper for Lemma 17.19.4: because the pulled-back skyscraper factor lies in the essential
image of closed-subset pushforward from its support, the adjunction unit is an isomorphism. -/
private theorem pullbackSkyscraper_unit_isIso_preimageClosure
    {Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) (A : Type u) :
    let Z : Closeds X :=
      ⟨f ⁻¹' closure ({y} : Set Y), isClosed_closure.preimage f.hom.continuous⟩
    IsIso
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i[Z]).unit.app
        ((f⁻¹).obj (skyscraperSheaf y A))) := by
  intro Z
  let _ : (Sheaf.pushforward (Type u) i[Z]).Full := inferInstance
  let _ : (Sheaf.pushforward (Type u) i[Z]).Faithful := inferInstance
  -- The pullback/pushforward unit is invertible exactly on the essential image of the fully
  -- faithful pushforward functor.
  exact
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i[Z]).isIso_unit_app_iff_mem_essImage :
      IsIso
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i[Z]).unit.app
          ((f⁻¹).obj (skyscraperSheaf y A))) ↔
            (Sheaf.pushforward (Type u) i[Z]).essImage
              ((f⁻¹).obj (skyscraperSheaf y A)))).2
      (by simpa [Z] using pullbackSkyscraper_memEssImage_preimageClosure (X := X) f y A)

/-- Helper for Lemma 17.19.4: the pulled-back skyscraper factor is canonically the pushforward of
its restriction to the preimage of the closure of its support point. -/
private noncomputable theorem pullbackSkyscraper_iso_preimageClosurePushforward
    {Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) (A : Type u) :
    let Z : Closeds X :=
      ⟨f ⁻¹' closure ({y} : Set Y), isClosed_closure.preimage f.hom.continuous⟩
    ((f⁻¹).obj (skyscraperSheaf y A)) ≅
      (Sheaf.pushforward (Type u) i[Z]).obj
        ((i[Z]⁻¹).obj ((f⁻¹).obj (skyscraperSheaf y A))) := by
  intro Z
  -- The previous helper upgrades the support calculation into the comparison isomorphism needed
  -- for the remaining factor-transport step.
  let _ :
      IsIso
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i[Z]).unit.app
          ((f⁻¹).obj (skyscraperSheaf y A))) :=
    by simpa [Z] using pullbackSkyscraper_unit_isIso_preimageClosure (X := X) f y A
  exact asIso
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i[Z]).unit.app
      ((f⁻¹).obj (skyscraperSheaf y A)))

/-- Helper for Lemma 17.19.4: inverse image preserves the finite-space product monomorphism into
the skyscraper factors. -/
private theorem pullbackFiniteSkyscraperUnitProduct_mono
    {Y : TopCat.{u}} [Finite Y] (f : X ⟶ Y) (𝒢 : Sh(Y)) :
    Mono
      ((f⁻¹).map
        (Limits.Pi.lift
          (fun y : Y ↦ ((stalkSkyscraperSheafAdjunction (C := Type u) y).unit.app 𝒢).hom))) := by
  -- Proof comment: the inverse-image functor preserves monomorphisms, so we reuse the finite-space
  -- monomorphism already proved before pulling back.
  exact Functor.map_mono (f⁻¹)
    (Limits.Pi.lift
      (fun y : Y ↦ ((stalkSkyscraperSheafAdjunction (C := Type u) y).unit.app 𝒢).hom))

/-- Helper for Lemma 17.19.4: after pulling back the finite-space product, each skyscraper factor
can already be rewritten as pushforward from the preimage of the corresponding point closure. -/
private noncomputable theorem pullbackFiniteSkyscraperProductIso_preimageClosurePushforward
    {Y : TopCat.{u}} (f : X ⟶ Y) (A : Y → Type u) :
    let Z : Y → Closeds X := fun y ↦
      ⟨f ⁻¹' closure ({y} : Set Y), isClosed_closure.preimage f.hom.continuous⟩
    (∏ᶜ fun y : Y ↦ ((f⁻¹).obj (skyscraperSheaf y (A y)))) ≅
      ∏ᶜ fun y : Y ↦
        (Sheaf.pushforward (Type u) i[Z y]).obj
          ((i[Z y]⁻¹).obj ((f⁻¹).obj (skyscraperSheaf y (A y)))) := by
  intro Z
  -- Proof comment: upgrade the factorwise comparison from
  -- `pullbackSkyscraper_iso_preimageClosurePushforward` to the full finite product using the
  -- canonical product transport `Pi.mapIso`.
  exact Pi.mapIso (fun y ↦
    pullbackSkyscraper_iso_preimageClosurePushforward (X := X) f y (A y))

/-- Lemma 17.19.4: a set-valued sheaf on a spectral space satisfying the finite coequalizer
presentation from `17.19.2.1` on quasi-compact opens embeds into a finite product of pushforwards
of constant finite sheaves from constructible closed subsets, indexed by a finite type. -/
@[stacks 0CAL]
theorem exists_mono_to_finite_product_of_constructible_closed_pushforward_constant_sheaves
    [SpectralSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    (ℱ : Sh(X))
    (hℱ : HasFiniteCompactOpenLowerShriekConstantCoequalizerPresentation ℱ) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → Closeds X)
      (hZ_constructible : ∀ a, IsConstructible (Z a : Set X))
      (A : ι → Type u) (hA_finite : ∀ a, Finite (A a)),
      ∃ φ : ℱ ⟶
        ∏ᶜ fun a : ι ↦
          (Sheaf.pushforward (Type u) i[Z a]).obj
            ((constantSheaf
                (Opens.grothendieckTopology (TopCat.of (Z a : Set X)))
                (Type u)).obj (A a)),
        Mono φ := by
  classical
  -- First descend `ℱ` to a finite sober model with finite stalks.
  obtain ⟨Y, hYfin, hY, f, hf, 𝒢, descIso, hstalk⟩ :=
    exists_finite_sober_sheaf_model_of_constructible_set_presentation ℱ hℱ
  letI : Finite Y := hYfin
  letI : T0Space Y := hY.1
  letI : QuasiSober Y := hY.2
  letI : SpectralSpace Y :=
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  let Z : Y → Closeds X := fun y ↦
    ⟨f ⁻¹' closure ({y} : Set Y), isClosed_closure.preimage f.hom.continuous⟩
  let A : Y → Type u := fun y ↦ 𝒢.presheaf.stalk y
  have hZ_constructible : ∀ y : Y, IsConstructible (Z y : Set X) := by
    intro y
    have hclosure_constructible : IsConstructible (closure ({y} : Set Y)) := by
      -- On the finite sober model, closed subsets are constructible because their open
      -- complements are compact.
      have hopen : IsOpen (closure ({y} : Set Y))ᶜ := isClosed_closure.isOpen_compl
      have hcompact : IsCompact (closure ({y} : Set Y))ᶜ := by
        exact Set.Finite.isCompact (Set.toFinite _)
      exact Topology.IsConstructible.of_compl (IsCompact.isConstructible hcompact hopen)
    simpa [Z] using hf.isConstructible_preimage hclosure_constructible
  have hA_finite : ∀ y : Y, Finite (A y) := hstalk
  refine ⟨Y, inferInstance, Z, hZ_constructible, A, hA_finite, ?_⟩
  -- Route correction: the pulled-back finite-space mono is now isolated by
  -- `pullbackFiniteSkyscraperUnitProduct_mono`, and the product target already rewrites to
  -- pushforwards from the preimages of the point closures via
  -- `pullbackFiniteSkyscraperProductIso_preimageClosurePushforward`.
  -- TODO: identify each restricted pullbacked skyscraper factor on `Z y` with the constant sheaf
  -- on `Z y` having value `A y`; this is the remaining generic-point/constant-sheaf bridge before
  -- composing the monomorphism `descIso.inv.hom ≫ (f⁻¹).map (...)`.
  sorry

end
