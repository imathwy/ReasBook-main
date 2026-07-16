import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_8_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_7
import StacksProject_2024.stacks_project.Chap07.Definition_7_14_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open scoped TopCat

universe u

/-
Domain-style sampling for Lemma 17.3.4:
- primary domain: extension by zero / by the initial object for sheaves of abelian groups along an
  open immersion of topological spaces;
- sampled owner declarations:
  `Ab`,
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso`,
  `Topology.IsEmbedding.toHomeomorph`,
  `TopCat.isoOfHomeo`;
- owner abstraction: the Chapter 6 owner remains the open-subset functor
  `openSubsetSheafExtensionByInitialObject U`; for a general open immersion `j : U ⟶ X`, the
  source-facing `j_!` functor should be obtained by transporting sheaves along the canonical
  homeomorphism `U ≃ j(U)` and then applying that owner. Since `TopCat` keeps open immersions
  unbundled as a morphism together with `Topology.IsOpenEmbedding j`, the public source-facing
  surface in this file should therefore be a thin bridge functor `Ab(U) ⥤ Ab(X)`, not a parallel
  local owner and not notation that depends on hidden elaboration choices;
- primitive data: the open immersion `j`, its open image `j(U)`, and the canonical isomorphism
  from `U` to the corresponding open subspace of `X`;
- derived API: the owner-level exactness statement for `j! U` and the thin general open-immersion
  bridge functor obtained by transport along `U ≅ j(U)`.

Source/core/bridge triage:
- `source-facing`: exactness of `j_!` for a general open immersion `j : U ⟶ X`;
- `core/canonical`: `openSubsetSheafExtensionByInitialObject` on an open subset of `X`;
- `bridge/view`: the thin public functor `openImmersionAbelianSheafExtensionByZero j hj`, which
  transports sheaves along the canonical homeomorphism `U ≅ j(U)` and then applies the Chapter 6
  owner. -/

section AbelianExtensionByZero

variable {X U : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]

/-- Helper for Lemma 17.3.4: abelian sheaves form a preadditive category. -/
noncomputable local instance abelianSheafPreadditive (Y : TopCat.{u}) : Preadditive (Ab(Y)) :=
  inferInstanceAs
    (Preadditive (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

/-- Helper for Lemma 17.3.4: abelian sheaves carry the canonical zero morphisms. -/
noncomputable local instance abelianSheafHasZeroMorphisms (Y : TopCat.{u}) :
    Limits.HasZeroMorphisms (Ab(Y)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- Helper for Lemma 17.3.4: abelian sheaves form an abelian category. -/
noncomputable local instance abelianSheafAbelian (Y : TopCat.{u}) : Abelian (Ab(Y)) :=
  inferInstanceAs
    (Abelian (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

/-- Helper for Lemma 17.3.4: the open-subspace functor on opens is continuous for the canonical
Grothendieck topologies. -/
noncomputable local instance openSubsetFunctorIsContinuous (U : Opens X) :
    U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Opens.grothendieckTopology X) :=
  Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding

/-- Helper for Lemma 17.3.4: the stalk functor on abelian sheaves at a point. -/
private noncomputable abbrev abelianSheafStalkFunctor (Y : TopCat.{u}) (x : Y) :
    Ab(Y) ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

/-- Helper for Lemma 17.3.4: exactness of a mapped short complex is invariant under a natural
isomorphism of functors. -/
private theorem shortComplex_exact_iff_of_functor_iso
    {A B : Type u} [Category.{u} A] [Category.{u} B]
    [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B]
    {F G : A ⥤ B} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G) (S : ShortComplex A) :
    (S.map F).Exact ↔ (S.map G).Exact := by
  -- Compare the mapped short complexes degreewise using the components of `e`.
  let i : S.map F ≅ S.map G :=
    ShortComplex.isoMk (e.app S.X₁) (e.app S.X₂) (e.app S.X₃)
      (by simpa using e.hom.naturality S.f)
      (by simpa using e.hom.naturality S.g)
  -- Exactness is invariant under isomorphism of short complexes.
  exact ShortComplex.exact_iff_of_iso i

/-- Helper for Lemma 17.3.4: any two morphisms into a zero object in `AddCommGrpCat` agree. -/
private theorem addCommGrp_hom_eq_of_isZero
    {A B : AddCommGrpCat.{u}} (hB : Limits.IsZero B) (f g : A ⟶ B) :
    f = g :=
  hB.eq_of_tgt _ _

/-- Helper for Lemma 17.3.4: a short complex of abelian groups with zero middle term is exact. -/
private theorem addCommGrp_shortComplex_exact_of_isZero_X₂
    (S : ShortComplex AddCommGrpCat.{u}) (hX₂ : Limits.IsZero S.X₂) :
    S.Exact := by
  -- Exactness is automatic when the middle object is zero.
  exact ShortComplex.exact_of_isZero_X₂ S hX₂

/-- Helper for Lemma 17.3.4: stalks commute naturally with pullback of abelian sheaves. -/
private noncomputable def abelianSheafStalkPullbackFunctorIso
    {Y Z : TopCat.{u}} (f : Y ⟶ Z) (y : Y) :
    abelianSheafStalkFunctor Z (f y) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ⋙ abelianSheafStalkFunctor Y y := by
  refine NatIso.ofComponents (fun ℱ ↦ TopCat.Sheaf.stalkPullbackIso f ℱ y) ?_
  intro ℱ 𝒢 g
  -- Route correction: consume the owner-level naturality theorem directly, instead of rebuilding
  -- the hidden sheafification comparison locally in this file.
  simpa [abelianSheafStalkFunctor] using
    TopCat.Sheaf.stalkPullbackIso_hom_naturality (A := AddCommGrpCat.{u}) (f := f) (x := y) g

/-- Helper for Lemma 17.3.4: outside `U`, the stalk functor after extension by zero is naturally
isomorphic to the constant zero functor. -/
private noncomputable def openSubsetExtensionByZero_outsideStalkFunctorIso
    (U : Opens X) (x : X) (hx : x ∉ (U : Set X)) :
    j! U ⋙ abelianSheafStalkFunctor X x ≅
      (Functor.const (Ab((extensionByZeroOpenSubsetSpace U)))).obj
        (⊥_ AddCommGrpCat.{u}) := by
  -- Route correction: package the Chapter 6 outside-stalk description as a functor isomorphism
  -- once, instead of rebuilding a transport-heavy exactness argument for each short complex.
  refine NatIso.ofComponents (fun ℱ ↦ ?_) ?_
  · -- On the branch `x ∉ U`, the Chapter 6 stalk description identifies the stalk with zero.
    simpa [abelianSheafStalkFunctor, hx] using
      (OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso
        (C := AddCommGrpCat.{u}) U ℱ x)
  · intro ℱ 𝒢 f
    -- Both sides are morphisms into the zero object, so naturality is forced by uniqueness.
    let h0 : Limits.IsZero (⊥_ AddCommGrpCat.{u}) := Limits.initialIsInitial.isZero
    exact addCommGrp_hom_eq_of_isZero h0 _ _

/-- Helper for Lemma 17.3.4: on the inside branch `x ∈ U`, the stalk of `j! U` identifies
naturally with the original stalk on the open subspace. -/
private noncomputable def openSubsetExtensionByZero_insideStalkFunctorIso
    (U : Opens X) (x : X) (hx : x ∈ (U : Set X)) :
    j! U ⋙ abelianSheafStalkFunctor X x ≅
      abelianSheafStalkFunctor (extensionByZeroOpenSubsetSpace U) ⟨x, hx⟩ := by
  -- Route correction: build the inside comparison from the canonical pullback-stalk comparison and
  -- the Chapter 6 unit isomorphism, so later exactness transport only uses functor isomorphisms.
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  exact
    Functor.isoWhiskerLeft (j! U)
        (by
          simpa using
            (abelianSheafStalkPullbackFunctorIso
              (extensionByZeroOpenSubsetInclusion U) xU)) ≪≫
      (Functor.associator (j! U)
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U))
        (abelianSheafStalkFunctor (extensionByZeroOpenSubsetSpace U) xU)).symm ≪≫
      Functor.isoWhiskerRight
        (OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).symm
        (abelianSheafStalkFunctor (extensionByZeroOpenSubsetSpace U) xU) ≪≫
      Functor.leftUnitor
        (abelianSheafStalkFunctor (extensionByZeroOpenSubsetSpace U) xU)

/-- Helper for Lemma 17.3.4: the zero abelian group is a zero object, which is the outside-stalk
target in the Chapter 6 description of extension by zero. -/
private theorem openSubsetExtensionByZero_zero_isZero :
    Limits.IsZero (⊥_ AddCommGrpCat.{u}) :=
  Limits.initialIsInitial.isZero

/-- Helper for Lemma 17.3.4: a mapped short complex of abelian sheaves is exact exactly when all
of its stalkwise images are exact. -/
private theorem abelianSheaf_map_exact_iff_stalkFunctor_map_exact
    {Y Z : TopCat.{u}} (F : Ab(Y) ⥤ Ab(Z)) [F.PreservesZeroMorphisms]
    (S : ShortComplex (Ab(Y))) :
    (S.map F).Exact ↔ ∀ z : Z, ((S.map F).map (abelianSheafStalkFunctor Z z)).Exact := by
  let T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Z) := S.map F
  -- Proof comment: freeze the codomain short complex at the owner sheaf category `Ab(Z)` before
  -- applying the stalkwise exactness criterion, so later uses avoid universe-elaboration churn.
  change T.Exact ↔ ∀ z : Z, (T.map (abelianSheafStalkFunctor Z z)).Exact
  exact TopCat.Sheaf.exact_iff_stalkFunctor_map_exact T

/-- Helper for Lemma 17.3.4: exactness is preserved under a natural isomorphism of functors. -/
private theorem exactFunctor_of_natIso
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) :
    exactFunctor C D F → exactFunctor C D G := by
  intro hF
  -- Proof comment: transfer finite-limit and finite-colimit preservation across the comparison
  -- isomorphism so the exactness proof can stay at the canonical owner.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 17.3.4: the Chapter 6 owner `j! U` agrees with the canonical sheaf pullback
functor for the open-embedding functor on opens. -/
private noncomputable abbrev openSubsetExtensionByZeroOwnerIsoSheafPullback
    (U : Opens X) :
    j! U ≅
      U.isOpenEmbedding.functor.sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) :=
  sorry

/-- Helper for Lemma 17.3.4: the canonical pullback functor on abelian sheaves for the open
subset inclusion is exact. -/
private theorem openSubsetExtensionByZeroSheafPullback_exact
    (U : Opens X) :
    exactFunctor (Ab((extensionByZeroOpenSubsetSpace U))) (Ab(X))
      (U.isOpenEmbedding.functor.sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X)) := by
  -- TODO: prove exactness at the canonical owner by installing the right `RepresentablyFlat`
  -- instance for `U.isOpenEmbedding.functor` and then using the finite-limits-plus-left-adjoint
  -- route from `Lemma_17_3_3`.
  sorry

/-- The open-subset owner-level form of Lemma 17.3.4: for an open subset `U ⊆ X`, the Chapter 6
extension-by-zero functor `j! U : Ab(U) ⥤ Ab(X)` is exact. -/
theorem openSubsetAbelianSheafExtensionByZero_exact
    (U : Opens X) :
    exactFunctor (Ab((extensionByZeroOpenSubsetSpace U))) (Ab(X)) (j! U) := by
  -- TODO: transport the canonical pullback exactness theorem across
  -- `openSubsetExtensionByZeroOwnerIsoSheafPullback`.
  sorry

/-- The source-facing lower-shriek functor `j_! : Ab(U) ⥤ Ab(X)` attached to an open immersion
`j : U ⟶ X`. This is the canonical bridge from an unbundled open immersion to the Chapter 6 owner
`j!` on the image open subset. -/
noncomputable abbrev openImmersionAbelianSheafExtensionByZero
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    Ab(U) ⥤ Ab(X) :=
  show Ab(U) ⥤ Ab(X) from
    TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.isoOfHomeo hj.1.toHomeomorph).hom ⋙
      j! ⟨Set.range j, hj.isOpen_range⟩

/-- Helper for Lemma 17.3.4: pushforward along a homeomorphism is exact on abelian sheaves. -/
private theorem homeomorphismAbelianSheafPushforward_exact
    {Y Z : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat]
    [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat]
    (e : Y ≅ Z) :
    exactFunctor (Ab(Y)) (Ab(Z)) (TopCat.Sheaf.pushforward AddCommGrpCat e.hom) := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat e.hom
  let G := TopCat.Sheaf.pushforward AddCommGrpCat e.inv
  let _ : Functor.IsEquivalence F := by
    -- Proof comment: for a homeomorphism, pushforward along the inverse is a strict quasi-inverse
    -- because pushforward composes definitionally with composition of continuous maps.
    refine Functor.IsEquivalence.mk' G ?_ ?_
    · have hcomp : F ⋙ G = TopCat.Sheaf.pushforward AddCommGrpCat (e.hom ≫ e.inv) := rfl
      have hid : TopCat.Sheaf.pushforward AddCommGrpCat (𝟙 Y) = 𝟭 (Ab(Y)) := rfl
      refine (eqToIso ?_).symm
      rw [hcomp, e.hom_inv_id, hid]
    · have hcomp : G ⋙ F = TopCat.Sheaf.pushforward AddCommGrpCat (e.inv ≫ e.hom) := rfl
      have hid : TopCat.Sheaf.pushforward AddCommGrpCat (𝟙 Z) = 𝟭 (Ab(Z)) := rfl
      refine eqToIso ?_
      rw [hcomp, e.inv_hom_id, hid]
  -- Proof comment: pushforward along a homeomorphism is an equivalence of sheaf categories, hence
  -- preserves finite limits and finite colimits automatically.
  exact (CategoryTheory.exactFunctor_iff F).2 ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 17.3.4: exact functors remain exact after composition. -/
private theorem exactFunctor_comp
    {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    {F : A ⥤ B} {G : B ⥤ C}
    (hF : exactFunctor A B F) (hG : exactFunctor B C G) :
    exactFunctor A C (F ⋙ G) := by
  -- Proof comment: exactness is preservation of finite limits and finite colimits, and both are
  -- stable under functor composition.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  let _ : PreservesFiniteLimits G := hG.1
  let _ : PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

-- Proof sketch: reduce the statement to the open-subset owner
-- `openSubsetSheafExtensionByInitialObject ⟨Set.range j, hj.isOpen_range⟩` via the canonical
-- homeomorphism `U ≃ j(U)`. Stalkwise, `OpenSubsetExtensionByInitial.sheafExtensionByInitial_
-- stalkIso` identifies the stalks over points in the image with the original stalks and the
-- stalks off the image with zero, so exactness is checked on stalks.
/-- Lemma 17.3.4: if `j : U ⟶ X` is an open immersion, then the extension-by-zero functor
`j_! : Ab(U) ⥤ Ab(X)` is exact. In this formalization the source-facing functor is the thin
bridge `openImmersionAbelianSheafExtensionByZero j hj` from the unbundled open immersion data to
the Chapter 6 owner on the image open subset. -/
theorem openImmersionAbelianSheafExtensionByZero_exact
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    exactFunctor (Ab(U)) (Ab(X)) (openImmersionAbelianSheafExtensionByZero j hj) := by
  -- TODO: compose the homeomorphism exactness theorem with
  -- `openSubsetAbelianSheafExtensionByZero_exact` once the owner comparison is stabilized without
  -- the current `whnf/isDefEq` timeout.
  sorry

end AbelianExtensionByZero
