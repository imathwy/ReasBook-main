import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_8_1
import stacks_proof.stacks_project.Chap06.Lemma_6_31_7
import stacks_proof.stacks_project.Chap07.Definition_7_14_1
import stacks_proof.stacks_project.Chap12.Lemma_12_29_1

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

/-- Helper for Lemma 17.3.4: the presheaf stalk-pullback comparison is natural in the sheaf
argument. -/
private theorem presheafStalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η) := by
  -- Proof comment: compare both maps after precomposing with every germ, where the owner
  -- pullback-stalk morphism is defined.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro V hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) V (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f 𝒢 x V hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f ℱ x V hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) ((Opens.map f).obj V) x
    hx ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let A :=
    ℱ.germ V (f x) hx ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let B :=
    η.app (Opposite.op V) ≫ 𝒢.germ V (f x) hx ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let C :=
    η.app (Opposite.op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app 𝒢).app
        (Opposite.op V) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η).app
        (Opposite.op ((Opens.map f).obj V)) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ).germ ((Opens.map f).obj V) x hx ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let Z :=
    ℱ.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using
      congrArg (fun k ↦ k ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x) h₁
  have hB : B = C := by
    simpa [B, C, Category.assoc] using
      congrArg (fun k ↦ η.app (Opposite.op V) ≫ k) h₂𝒢
  have hC : C = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.naturality η)
      (Opposite.op V)
    simpa [C, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V)
            x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using
      congrArg
        (fun k ↦
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
              (Opposite.op V) ≫
            k)
        h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η))
        h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 17.3.4: the sheaf stalk-pullback comparison is natural in the sheaf
argument. -/
private theorem sheafStalkPullbackIso_hom_naturality
    {Y Z : TopCat.{u}} (f : Y ⟶ Z) {ℱ 𝒢 : Z.Sheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : Y) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
  -- Proof comment: unwind the sheaf-level comparison into the presheaf-level comparison,
  -- sheafification, and `pullbackIso`, then transport naturality across each factor.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology Y)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology Y)
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).map k)
          (((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv).naturality η))
  have h₁ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      (presheafStalkPullbackIso_hom_naturality f η.hom x)
  have h₂ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          k ≫ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      hsheafify
  have h₃ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    have hpost :
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))) =
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                  (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)))) := by
      exact congrArg
        (fun k ↦
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫ k))
        hpullbackIso
    simpa [Category.assoc] using hpost
  simpa [σ, τ𝒢, τℱ, π𝒢, πℱ, Category.assoc] using h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 17.3.4: stalks commute naturally with pullback of abelian sheaves. -/
private noncomputable def abelianSheafStalkPullbackFunctorIso
    {Y Z : TopCat.{u}} (f : Y ⟶ Z) (y : Y) :
    abelianSheafStalkFunctor Z (f y) ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{u} f ⋙ abelianSheafStalkFunctor Y y := by
  refine NatIso.ofComponents (fun ℱ ↦ TopCat.Sheaf.stalkPullbackIso f ℱ y) ?_
  intro ℱ 𝒢 g
  -- Route correction: consume the owner-level naturality theorem directly, instead of rebuilding
  -- the hidden sheafification comparison locally in this file.
  simpa [abelianSheafStalkFunctor] using sheafStalkPullbackIso_hom_naturality f g y

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
  by
    let JU : GrothendieckTopology (Opens (extensionByZeroOpenSubsetSpace U)) :=
      Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U)
    let JX : GrothendieckTopology (Opens X) :=
      Opens.grothendieckTopology X
    letI : U.isOpenEmbedding.functor.IsContinuous JU JX :=
      openSubsetFunctorIsContinuous U
    -- Proof comment: reuse the Chapter 6 owner comparison to the pullback-construction owner, then
    -- pass to the chosen `sheafPullback` surface via the canonical construction iso.
    exact
      (OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction
          (C := AddCommGrpCat.{u}) U).leftAdjointUniq
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            U.isOpenEmbedding.functor AddCommGrpCat.{u} JU JX).ofNatIsoRight
          (Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}
            U.isOpenEmbedding).symm)) ≪≫
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          U.isOpenEmbedding.functor AddCommGrpCat.{u} JU JX).symm

/-- Helper for Lemma 17.3.4: the canonical pullback functor on abelian sheaves for the open
subset inclusion is exact. -/
private theorem openSubsetExtensionByZeroSheafPullback_exact
    (U : Opens X) :
    exactFunctor (Ab((extensionByZeroOpenSubsetSpace U))) (Ab(X))
      (U.isOpenEmbedding.functor.sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X)) := by
  let JU : GrothendieckTopology (Opens (extensionByZeroOpenSubsetSpace U)) :=
    Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U)
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let G := U.isOpenEmbedding.functor
  let _ : G.IsContinuous JU JX := openSubsetFunctorIsContinuous U
  -- Proof comment: stay on the canonical `sheafPullback` owner and assemble the two exactness
  -- inputs directly, as in the ringed-space pullback exactness template from Lemma 17.3.3.
  let _ : PreservesFiniteLimits
      (G.op.lan :
        ((Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})) := by
    infer_instance
  let _ : PreservesFiniteLimits (G.sheafPullback AddCommGrpCat.{u} JU JX) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G AddCommGrpCat.{u} JU JX
  let _ : PreservesFiniteColimits (G.sheafPullback AddCommGrpCat.{u} JU JX) := by
    let _ : (G.sheafPullback AddCommGrpCat.{u} JU JX).IsLeftAdjoint :=
      (G.sheafAdjunctionContinuous AddCommGrpCat.{u} JU JX).isLeftAdjoint
    infer_instance
  exact (CategoryTheory.exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- The open-subset owner-level form of Lemma 17.3.4: for an open subset `U ⊆ X`, the Chapter 6
extension-by-zero functor `j! U : Ab(U) ⥤ Ab(X)` is exact. -/
theorem openSubsetAbelianSheafExtensionByZero_exact
    (U : Opens X) :
    exactFunctor (Ab((extensionByZeroOpenSubsetSpace U))) (Ab(X)) (j! U) := by
  -- Proof comment: transport exactness from the canonical pullback owner back to the Chapter 6
  -- extension-by-zero owner.
  exact exactFunctor_of_natIso
    (openSubsetExtensionByZeroOwnerIsoSheafPullback U).symm
    (openSubsetExtensionByZeroSheafPullback_exact U)

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
@[stacks 01AK]
theorem openImmersionAbelianSheafExtensionByZero_exact
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    exactFunctor (Ab(U)) (Ab(X)) (openImmersionAbelianSheafExtensionByZero j hj) := by
  -- Proof comment: factor the source-facing `j_!` through the canonical homeomorphism onto the
  -- image open subset, then compose the two exact functors.
  let V : Opens X := ⟨Set.range j, hj.isOpen_range⟩
  -- Route correction: close the public theorem by the visible composition, rather than rebuilding
  -- exactness on a transport-heavy owner for the whole open immersion at once.
  simpa [openImmersionAbelianSheafExtensionByZero, V] using
    exactFunctor_comp
      (homeomorphismAbelianSheafPushforward_exact (TopCat.isoOfHomeo hj.1.toHomeomorph).hom)
      (openSubsetAbelianSheafExtensionByZero_exact V)

end AbelianExtensionByZero
