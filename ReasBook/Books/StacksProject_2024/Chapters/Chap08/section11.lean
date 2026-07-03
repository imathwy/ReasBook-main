import Mathlib
import Mathlib.CategoryTheory.Sites.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_11_1 (from Chap08) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Definition 8.11.1:
- primary domain: stacks in groupoids over a site and their fiberwise local geometry;
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `StackInGroupoidsOver`,
  `Functor.Fiber`,
  `canonicalPullbackChoice`;
- best owner abstraction: the source-facing property `IsGerbe J p` on a projection functor
  `p : S ⥤ C` already known to be a stack in groupoids over `(C, J)`;
- primitive data: the parent owner `IsStackInGroupoids J p`, local inhabitedness of fibers, and
  local isomorphism of any two objects in a fixed fiber after pullback along a cover;
- derived API: later reformulations in terms of gerbes over morphisms, local essential
  surjectivity, and local lifting of fiber morphisms.

Source/core/bridge triage:
- `source-facing`: `IsGerbe J p`;
- `core/canonical`: `IsStackInGroupoids J p`, `Functor.Fiber`, and the canonical pullback choice
  on `p`;
- `bridge/view`: later characterizations such as `IsGerbeOver` and the equivalence with local
  lifting conditions. -/

/-- Definition 8.11.1: a gerbe over the site `(C, J)` is a stack in groupoids whose fibers are
locally inhabited and such that any two objects of the same fiber become isomorphic after passing
to a covering. The site `J` is a genuine owner parameter of this notion and remains explicit in
the public API. -/
class IsGerbe (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsStackInGroupoids J p where
  /-- Every object of the base admits a covering by objects over which the gerbe has a section. -/
  locally_inhabited (U : C) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      Nonempty (p.Fiber I.Y)
  /-- Any two objects of the same fiber become isomorphic after restricting to a covering. -/
  locally_isomorphic {U : C} (x y : p.Fiber U) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      Nonempty
        (I.f ^*[canonicalPullbackChoice p] x ≅
          I.f ^*[canonicalPullbackChoice p] y)

/-- A gerbe over the site `(C, J)` is canonically a stack in groupoids over `(C, J)`. -/
instance (J : GrothendieckTopology C) [h : IsGerbe J p] : IsStackInGroupoids J p :=
  h.toIsStackInGroupoids

end

end CategoryTheory

/-! ### Lemma_8_11_2 (from Chap08) -/
universe u v

namespace CategoryTheory

open BasedFunctor
open Functor
open Functor IsStronglyCartesian
open StackInGroupoidsOver.Hom

attribute [local instance] FibredCategoryOver.isFibred

namespace FibredCategoryMor

section

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver C}

/-- Helper for Lemma 8.11.2: mapping a strongly cartesian lift over `f` along a fibred-category
morphism again yields a strongly cartesian lift over the same base arrow `f`. -/
private theorem map_stronglyCartesian_of_lift
    (F : X ⟶ Y) {a b : X.S} {U V : C} (f : V ⟶ U) (φ : a ⟶ b)
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f (F.toHom.map φ) := by
  letI : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    subst_hom_lift X.p f φ
    simpa using hφ
  letI : Y.p.IsHomLift f (F.toHom.map φ) := by
    infer_instance
  have hY :
      Y.p.IsStronglyCartesian (Y.p.map (F.toHom.map φ)) (F.toHom.map φ) :=
    map_stronglyCartesian F φ hφ'
  subst_hom_lift Y.p f (F.toHom.map φ)
  exact hY

/-- Helper for Lemma 8.11.2: the canonical comparison isomorphism exists in the fiber over the
domain of `f`, identifying the chosen pullback of `F(x)` with the image under `F` of the chosen
pullback of `x`. -/
private theorem pullbackComparison_nonempty
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    Nonempty
      (f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
        ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x)) := by
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  let φ :
      (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    F.toHom.map (hcX.map f x)
  let ψ :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ⟶
        (((F.toHom).fiberFunctor U).obj x).1 :=
    hcY.map f (((F.toHom).fiberFunctor U).obj x)
  have hφ : Y.p.IsStronglyCartesian f φ :=
    map_stronglyCartesian_of_lift F f (hcX.map f x) (hcX.isStronglyCartesian f x)
  have hψ : Y.p.IsStronglyCartesian f ψ :=
    hcY.isStronglyCartesian f (((F.toHom).fiberFunctor U).obj x)
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :
      (f ^*[hcY] (((F.toHom).fiberFunctor U).obj x)).1 ≅
        (((F.toHom).fiberFunctor V).obj (f ^*[hcX] x)).1 :=
    domainIsoOfBaseIso Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.hom := by
    change Y.p.IsHomLift (Iso.refl V).hom e.hom
    exact domainUniqueUpToIso_inv_isHomLift Y.p hf φ ψ
  letI : Y.p.IsHomLift (𝟙 V) e.inv := by
    change Y.p.IsHomLift (Iso.refl V).inv e.inv
    exact domainUniqueUpToIso_hom_isHomLift Y.p hf φ ψ
  exact
    ⟨{ hom := Functor.Fiber.homMk Y.p V e.hom
       inv := Functor.Fiber.homMk Y.p V e.inv
       hom_inv_id := by
         apply Functor.Fiber.hom_ext
         change e.hom ≫ e.inv = 𝟙 _
         exact e.hom_inv_id
       inv_hom_id := by
         apply Functor.Fiber.hom_ext
         change e.inv ≫ e.hom = 𝟙 _
         exact e.inv_hom_id }⟩

/-- Helper for Lemma 8.11.2: the canonical comparison isomorphism in the fiber over the domain of
`f`, identifying the chosen pullback of `F(x)` with the image under `F` of the chosen pullback of
`x`. -/
noncomputable def pullbackComparison
    (F : X ⟶ Y) {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    f ^*[canonicalPullbackChoice Y.p] ((F.toHom).fiberFunctor U).obj x ≅
      ((F.toHom).fiberFunctor V).obj (f ^*[canonicalPullbackChoice X.p] x) :=
  Classical.choice (pullbackComparison_nonempty F f x)

end

end FibredCategoryMor

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮₁ 𝒮₂ : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.11.2:
- primary domain: stacks in groupoids over a site, gerbes, and equivalences in `Cat/C`;
- inspected owner-level declarations:
  `IsGerbe`,
  `StackInGroupoidsOver`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`,
  `StackInGroupoidsOver.isStackInGroupoids_p`,
  `BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase`;
- best owner abstraction: the source-facing gerbe predicate `IsGerbe J p`, transported along the
  owner morphism `F : 𝒮₁ ⟶ 𝒮₂` in `StackInGroupoidsOver J` rather than a parallel raw
  based-functor API;
- primitive data: the gerbe fields `locally_inhabited` and `locally_isomorphic` together with the
  over-base equivalence datum on the owner morphism;
- derived API: transport of those owner fields along the induced fibre equivalences and the
  `iff` statement below.

Source/core/bridge triage:
- `source-facing`: `IsGerbe J p`;
- `core/canonical`: `StackInGroupoidsOver J`, `StackInGroupoidsOver.Hom.IsEquivalenceOverBase`,
  `IsStackInGroupoids`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`, fibre functors, chosen pullback functors, and
  `FibredCategoryMor.pullbackComparison`;
- `bridge/view`: the equivalence-invariant restatement
  `IsGerbe J 𝒮₁.p ↔ IsGerbe J 𝒮₂.p`. -/

/-- Helper for Lemma 8.11.2: an equivalence over the base category transports the gerbe
structure from the source stack in groupoids to the target stack in groupoids. -/
theorem isGerbe_of_equivalence_over_base
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase)
    (h₁ : IsGerbe J 𝒮₁.p) :
    IsGerbe J 𝒮₂.p := by
  refine
    { toIsStackInGroupoids := inferInstance
      locally_inhabited := ?_
      locally_isomorphic := ?_ }
  · intro U
    -- Keep the same cover and push each chosen local object forward along the fiber functor.
    obtain ⟨S, hS⟩ := h₁.locally_inhabited U
    refine ⟨S, fun I ↦ ?_⟩
    obtain ⟨x⟩ := hS I
    exact ⟨(F.fiberFunctor I.Y).obj x⟩
  · intro U x y
    -- Choose inverse images of `x` and `y` in the source fiber using the fiber equivalence.
    let F' := F.toFibredCategoryMor
    let fiberU := F.fiberFunctor U
    letI : fiberU.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF U
    let eU := fiberU.asEquivalence
    let x₁ : 𝒮₁.p.Fiber U := eU.inverse.obj x
    let y₁ : 𝒮₁.p.Fiber U := eU.inverse.obj y
    let εx : fiberU.obj x₁ ≅ x := eU.counitIso.app x
    let εy : fiberU.obj y₁ ≅ y := eU.counitIso.app y
    -- Apply the gerbe local-isomorphism datum in the source fiber.
    obtain ⟨S, hS⟩ := h₁.locally_isomorphic x₁ y₁
    refine ⟨S, fun I ↦ ?_⟩
    let fiberI := F.fiberFunctor I.Y
    letI : fiberI.IsEquivalence :=
      fiberFunctor_isEquivalence_of_isEquivalenceOverBase F.toBasedFunctor hF I.Y
    let hc₂ := canonicalPullbackChoice 𝒮₂.p
    obtain ⟨α⟩ := hS I
    -- Transport the source pullback isomorphism across pullback comparison and counit isomorphisms.
    exact
      ⟨(hc₂.pullbackFunctor I.f).mapIso εx.symm ≪≫
        FibredCategoryMor.pullbackComparison F' I.f x₁ ≪≫
        fiberI.mapIso α ≪≫
        (FibredCategoryMor.pullbackComparison F' I.f y₁).symm ≪≫
        (hc₂.pullbackFunctor I.f).mapIso εy⟩

-- Proof sketch: the ambient objects already lie in `StackInGroupoidsOver J`, so the stack part
-- of the gerbe structure is inherited directly. The remaining work is to transport the two
-- fiberwise gerbe conditions along the equivalence on each fiber.
/-- Lemma 8.11.2: if `𝒮₁` and `𝒮₂` are equivalent as categories over `C`, then `𝒮₁` is a gerbe
over `(C, J)` if and only if `𝒮₂` is a gerbe over `(C, J)`. -/
theorem isGerbe_iff_of_equivalence_over_base
    (F : 𝒮₁ ⟶ 𝒮₂)
    (hF : F.IsEquivalenceOverBase) :
    IsGerbe J 𝒮₁.p ↔ IsGerbe J 𝒮₂.p := by
  constructor
  · exact isGerbe_of_equivalence_over_base F hF
  · intro h₂
    -- Use a chosen inverse equivalence over the base and reuse the forward transport theorem.
    let e : EquivalenceOverBase F.toBasedFunctor := Classical.choice hF.nonempty
    let G : 𝒮₂ ⟶ 𝒮₁ := ofBasedFunctor e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    simpa [G] using isGerbe_of_equivalence_over_base G hG h₂

end

end CategoryTheory

/-! ### Lemma_8_11_3 (from Chap08) -/
open CategoryTheory
open BasedFunctor
open Functor
open Functor.Fiber
open Functor.IsStronglyCartesian
open FibredCategoryOver

universe w v₁ u₁

namespace CategoryTheory

namespace FibredCategoryMor

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : FibredCategoryOver C} [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

/- Domain-style sampling for Lemma 8.11.3:
- primary domain: morphisms of fibred categories over a site, expressed through canonical
  pullback functors on fibers and comparison isomorphisms between `f^*F(x)` and `F(f^*x)`;
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `PullbackChoice.pullbackFunctor`,
  `canonicalPullbackChoice`,
  `Functor.IsStronglyCartesian.domainIsoOfBaseIso`;
- best owner abstraction: the source-facing predicate
  `FibredCategoryMor.LocallyLiftsFiberMorphisms`, stated in the fiber categories using the
  canonical pullback functors and the comparison square they induce;
- primitive data: a morphism `b` in the target fiber over `U`, together with local lifts `a` in
  the pulled-back source fibers over a covering family;
- derived API: the canonical stack-morphism shorthand
  `StackInGroupoidsOver.Hom.LocallyLiftsFiberMorphisms` and the gerbe characterization theorem at
  the end of the file.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryMor.LocallyLiftsFiberMorphisms`;
- `core/canonical`: `BasedFunctor.fiberFunctor`, `canonicalPullbackChoice`,
  `PullbackChoice.pullbackFunctor`, `FibredCategoryMor.pullbackComparison`, and
  `IsStronglyCartesian.domainIsoOfBaseIso`;
- `bridge/view`: `FibredCategoryMor.pullbackComparison`, reused here to express the source
  condition as a commuting square in the pulled-back target fiber. -/

/-- Any morphism between two objects in the image of a fiber is locally lifted after restricting
to a covering family. This is condition `(2)(b)` in Lemma `8.11.3`. -/
def LocallyLiftsFiberMorphisms
    (J : GrothendieckTopology C) (F : FibredCategoryMor X Y) : Prop :=
  let hcX := canonicalPullbackChoice X.p
  let hcY := canonicalPullbackChoice Y.p
  ∀ {U : C} (x x' : X.p.Fiber U)
      (b : (fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj x'),
      ∃ S : J.Cover U, ∀ I : S.Arrow,
        ∃ a : I.f ^*[hcX] x ⟶ I.f ^*[hcX] x',
          CommSq
            ((hcY.pullbackFunctor I.f).map b)
            (pullbackComparison F I.f x).hom
            (pullbackComparison F I.f x').hom
            ((fiberFunctor F I.Y).map a)

end

end FibredCategoryMor

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Owner-level shorthand for the local lifting condition on a `1`-morphism of stacks in
groupoids. -/
abbrev LocallyLiftsFiberMorphisms (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyLiftsFiberMorphisms J (toFibredCategoryMor F)

end

end StackInGroupoidsOver.Hom

namespace StackInGroupoidsOver.Hom

section

variable {C : Type u₁} [Category.{v₁} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/- Domain-style sampling for the main gerbe characterization in Lemma 8.11.3:
- primary domain: gerbes over morphisms of stacks in groupoids, compared across different
  factorizations of the same morphism through a functor fibred in groupoids over the target;
- inspected owner-level declarations:
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`,
  `isStackInGroupoids_iff_of_equivalence_over_base`,
  `isGerbe_iff_of_equivalence_over_base`,
  `fibredInGroupoidsFactorizationToTarget`;
- best owner abstraction: the source-facing gerbe predicate
  `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor` on an arbitrary factorization of `F`
  through a functor `F'` fibred in groupoids over `Yₛ`;
- primitive data: a factorization `a ⋙ F' = toBasedFunctor F` with `a` an equivalence over `C`;
- derived API: the canonical explicit-factorization specialization below.

Source/core/bridge triage:
- `source-facing`: the factorization-independent equivalence below for an arbitrary factorization
  `a ⋙ F' = toBasedFunctor F`;
- `core/canonical`: `IsGerbe (inheritedTopology J Yₛ) F'.toFunctor`,
  `exists_equivalence_over_target_between_fibred_groupoid_factorizations`, and the transport
  lemmas `isStackInGroupoids_iff_of_equivalence_over_base` and
  `isGerbe_iff_of_equivalence_over_base`;
- `bridge/view`: the canonical explicit factorization
  `fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)`. -/

-- Proof sketch: compare the given factorization `a ⋙ F' = toBasedFunctor F` with the canonical
-- explicit factorization from Lemma `4.35.16` using Lemma `4.35.17`, which gives an equivalence
-- over the target stack. Transport the inherited-topology stack and gerbe predicates across that
-- equivalence by Lemmas `8.5.4` and `8.11.2`, and then identify the canonical factorization with
-- conditions `(2)(a)` and `(2)(b)` via the specialization below.
/-- Lemma 8.11.3: let `F : Xₛ ⟶ Yₛ` be a morphism of stacks in groupoids over `(C, J)`, and let
`a : Xₛ ⥤ᵇ X'` be an equivalence over `C` such that `a ⋙ F' = toBasedFunctor F`, where
`F' : X' ⟶ Yₛ` is fibred in groupoids over `Yₛ`. Then `F'`, viewed over the topology on `Yₛ`
inherited from `(C, J)`, is a gerbe if and only if `F` is locally essentially surjective on
objects and locally lifts fiber morphisms after passing to a cover. -/
theorem isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms_of_factorization
    (F : Xₛ ⟶ Yₛ)
    {X' : BasedCategory C}
    (a : Xₛ.toBasedCategory ⥤ᵇ X')
    (F' : X' ⥤ᵇ Yₛ.toBasedCategory)
    [IsFibredInGroupoids F'.toFunctor]
    (ha : a.IsEquivalenceOverBase)
    (hfactor : a ⋙ F' = toBasedFunctor F) :
    IsGerbe (inheritedTopology J Yₛ) F'.toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  sorry

-- Proof sketch: apply the main factorization-independent statement to the canonical explicit
-- factorization `X ×_{F,Y,\mathrm{id}} Y ⟶ Y`, where the source comparison
-- `X ⟶ X ×_{F,Y,\mathrm{id}} Y` is an equivalence over `C` by Lemma `4.35.16`.
/-- Canonical specialization of Lemma 8.11.3 to the explicit factorization
`X ×_{F,Y,\mathrm{id}} Y ⟶ Y`. This is the bridge from the source-facing factorization statement
to the chapter's canonical factorization owner. -/
theorem factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms
    (F : Xₛ ⟶ Yₛ) :
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F := by
  letI :
      IsFibredInGroupoids
        (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor F)
  exact
    isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms_of_factorization
      F
      (fibredInGroupoidsFactorizationFromSource (toBasedFunctor F))
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F))
      (fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor F))
      (fibredInGroupoidsFactorization_comp (toBasedFunctor F))

end

end StackInGroupoidsOver.Hom

end CategoryTheory

/-! ### Definition_8_11_4 (from Chap08) -/
universe u v

namespace CategoryTheory

open FibredCategoryOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/- Domain-style sampling for Definition 8.11.4:
- primary domain: gerbes over morphisms of stacks in groupoids, expressed through the canonical
  factorization-to-target projection over the topology on the target stack inherited from the
  ambient site;
- inspected owner-level declarations:
  `IsGerbe`,
  `fibredInGroupoidsFactorizationToTarget`,
  `inheritedTopology`,
  `factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms`;
- best owner abstraction: the canonical gerbe predicate
  `IsGerbe (inheritedTopology J Yₛ)
    (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor`;
- primitive-vs-derived split:
  primitive data: none in this file, since Definition 8.11.4 only specializes the upstream gerbe
    owner to the canonical factorization attached to `F`;
  derived API: the short owner-level names `IsGerbeOver F` and
    `LocallyLiftsFiberMorphisms F`, plus the gerbe characterization specialized from
    Lemma 8.11.3.

Source/core/bridge triage:
- source-facing: the phrase “`F` is a gerbe over `Yₛ`” for a morphism of stacks in groupoids;
- core/canonical: `IsGerbe` on the factorization-to-target projection over `inheritedTopology`;
- bridge/view: the short property alias `IsGerbeOver F` and its companion
  characterization theorem below. -/

namespace StackInGroupoidsOver.Hom

variable (F : Xₛ ⟶ Yₛ)

/- Definition 8.11.4: the phrase “`F` is a gerbe over `Yₛ`” is the canonical gerbe predicate on
the factorization-to-target projection over the topology on `Yₛ` inherited from `(C, J)`. The
source-facing characterization from Lemma `8.11.3` is recovered by its canonical explicit-
factorization specialization. -/
#check IsGerbe (inheritedTopology J Yₛ)
  (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor

/-- Bridge/view shorthand for the source-facing phrase “`F` is a gerbe over `Yₛ`”. -/
abbrev IsGerbeOver (F : Xₛ ⟶ Yₛ) : Prop :=
  IsGerbe (inheritedTopology J Yₛ)
    (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor

/-- Lemma 8.11.3 identifies a gerbe over the target stack with the two local lifting conditions on
the original morphism. -/
theorem isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    (F : Xₛ ⟶ Yₛ) :
    IsGerbeOver F ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F :=
by
  change
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F
  exact
    factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms
      F

-- Proof sketch: apply the forward implication of the equivalence from Lemma `8.11.3` and project
-- to the local essential-surjectivity clause.
/-- A gerbe over the target stack is locally essentially surjective on objects after refining by a
cover of the base object. -/
theorem IsGerbeOver.locallyEssentiallySurjectiveOnObjects {F : Xₛ ⟶ Yₛ}
    (hF : IsGerbeOver F) :
    LocallyEssentiallySurjectiveOnObjects F :=
  (isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    F).mp hF |>.1

/-- A gerbe over the target stack locally lifts morphisms in fibers after refining by a cover. -/
theorem IsGerbeOver.locallyLiftsFiberMorphisms {F : Xₛ ⟶ Yₛ} (hF : IsGerbeOver F) :
    LocallyLiftsFiberMorphisms F :=
  (isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    F).mp hF |>.2

end StackInGroupoidsOver.Hom

end CategoryTheory

/-! ### Lemma_8_11_5 (from Chap08) -/
universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Y' : StackInGroupoidsOver J}

/- Domain-style sampling for Lemma 8.11.5:
- primary domain: gerbes over morphisms of stacks in groupoids and their stability under
  bicategorical `2`-cartesian base change;
- sampled owner-level declarations:
  `StackInGroupoidsOver.Hom.IsGerbeOver`,
  `StackInGroupoidsOver.Hom.isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- sampled bridge/model declaration:
  `StackInGroupoidsOver.twoFibreProductSquare`;
- best owner abstraction: the source-facing theorem should use the stack-morphism square owner
  `BicategoricalTwoCommutativeSquare F G`; the explicit pullback square from Lemma `8.5.6`
  remains only the bridge/model used in the proof;
- primitive-vs-derived split:
  primitive data: the four stack morphisms, the invertible `2`-morphism on stack morphisms,
    the `2`-cartesian hypothesis on the resulting stack-level square, and the gerbe hypothesis
    on `F`;
  derived API: transport of `IsGerbeOver` to the base-changed morphism `F'`.

Source/core/bridge triage:
- `source-facing`: the gerbe base-change statement of Lemma `8.11.5`;
- `core/canonical`: `F.IsGerbeOver`, `BicategoricalTwoCommutativeSquare F G`,
  and `Bicategory.IsFinal`;
- `bridge/view`: the explicit pullback square from Lemma `8.5.6`, used only in the proof. -/

-- Proof sketch: replace the given stack-level `2`-cartesian square by the canonical explicit
-- `2`-fibre product from Lemma `8.5.6`. Check the local essential-surjectivity and local lifting
-- conditions of Lemma `8.11.3` on that explicit pullback object, then transport them back across
-- the equivalence of `2`-fibre product squares.
/-- Lemma 8.11.5: in a `2`-cartesian square of stacks in groupoids over `(C, J)`,
`X' --G'--> X`, `X' --F'--> Y'`, `Y' --G--> Y`, `X --F--> Y`, if `F` is a gerbe over `Y`,
then `F'` is a gerbe over `Y'`. -/
theorem isGerbeOver_of_twoCartesian
    {X' : StackInGroupoidsOver J}
    (F : X ⟶ Y)
    (G : Y' ⟶ Y)
    (F' : X' ⟶ Y')
    (G' : X' ⟶ X)
    (α : G' ≫ F ≅ F' ≫ G)
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := G'
           q := F'
           ψ := α } :
          BicategoricalTwoCommutativeSquare F G))
    (hF : StackInGroupoidsOver.Hom.IsGerbeOver F) :
    StackInGroupoidsOver.Hom.IsGerbeOver F' := by
  sorry

end

end CategoryTheory

/-! ### Lemma_8_11_6 (from Chap08) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ Zₛ : StackInGroupoidsOver J}

-- Proof sketch: by Lemma `8.11.3`, a gerbe morphism is exactly a morphism that is locally
-- essentially surjective on objects and locally lifts fiber morphisms. These local conditions are
-- stable under composition after refining covers, so they apply to `F ≫ G`.
/-- Lemma 8.11.6: if `F : Xₛ ⟶ Yₛ` and `G : Yₛ ⟶ Zₛ` are gerbes over their targets, then the
composite `F ≫ G : Xₛ ⟶ Zₛ` is again a gerbe over `Zₛ`. -/
theorem isGerbeOver_comp
    (F : Xₛ ⟶ Yₛ) (G : Yₛ ⟶ Zₛ)
    (hF : StackInGroupoidsOver.Hom.IsGerbeOver F)
    (hG : StackInGroupoidsOver.Hom.IsGerbeOver G) :
    StackInGroupoidsOver.Hom.IsGerbeOver (F ≫ G) := by
  sorry

end CategoryTheory

/-! ### Lemma_8_11_7 (from Chap08) -/
open CategoryTheory
universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

variable {X Y Y' X' : StackInGroupoidsOver J}
variable (F : X ⟶ Y)
variable (G : Y' ⟶ Y)
variable (F' : X' ⟶ Y')
variable (G' : X' ⟶ X)
variable (α : F' ≫ G ≅ G' ≫ F)

/-
Domain-style sampling for Lemma 8.11.7:
- primary domain: gerbes over morphisms of stacks in groupoids and their behavior under
  bicategorical `2`-cartesian squares;
- inspected owner-level declarations:
  `IsGerbeOver`,
  `StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing theorem should be stated directly in terms of stack
  morphisms and the chapter's square owner `BicategoricalTwoCommutativeSquare G F`; the
  based-functor coercions are only bridge/view data and should not appear in the public statement;
- primitive data: the four stack morphisms, the comparison `2`-isomorphism `α`, the
  `2`-cartesian hypothesis on the resulting square, the local essential-image hypothesis on `G`,
  and the gerbe hypothesis on `F'`;
- derived API: descent of the gerbe-over property to `F`.

Source/core/bridge triage:
- `source-facing`: the gerbe descent statement of Lemma `8.11.7`;
- `core/canonical`: `IsGerbeOver`, `LocallyEssentiallySurjectiveOnObjects`,
  `BicategoricalTwoCommutativeSquare G F`, and `Bicategory.IsFinal`;
- `bridge/view`: the coercions from stack morphisms to based functors, which are not part of the
  refined theorem surface. -/

-- Proof sketch: the `2`-cartesian square identifies `X'` with the pullback `Y' ×_Y X`. Prove
-- conditions `(2)(a)` and `(2)(b)` of Lemma `8.11.3` for `F : X ⟶ Y`: first lift target objects
-- locally along `G`, then use that `F'` is a gerbe over `Y'`; for morphisms, pull the source
-- object back to `Y'`, form the corresponding objects of `X'`, and apply the local lifting
-- condition supplied by the gerbe structure on `F'`.
/-- Lemma 8.11.7: let
`X' --G'--> X`,
`X' --F'--> Y'`,
`Y' --G--> Y`,
and `X --F--> Y`
be a `2`-cartesian square of stacks in groupoids over a site `(C, J)`. If every object of every
fiber of `Y` is locally in the essential image of `G`, and if `X'` is a gerbe over `Y'`, then
`X` is a gerbe over `Y`. -/
theorem isGerbeOver_of_twoCartesian_of_locallyEssentiallySurjective
    (hcart :
      Bicategory.IsFinal
        ({ obj := X'
           p := F'
           q := G'
           ψ := α } :
          BicategoricalTwoCommutativeSquare G F))
    (hG : StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects G)
    (hF' : StackInGroupoidsOver.Hom.IsGerbeOver F') :
    StackInGroupoidsOver.Hom.IsGerbeOver F := by
  sorry

end

end CategoryTheory
