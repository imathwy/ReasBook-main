import Mathlib
import StacksProject_2024.Chap04.Definition_4_31_2
import StacksProject_2024.Internal.Chap08.StackInGroupoidsTwoFibreProductSquare
import StacksProject_2024.Chap08.Lemma_8_4_6
import StacksProject_2024.Chap08.Lemma_8_11_2
import StacksProject_2024.Chap08.Definition_8_11_4
import StacksProject_2024.Chap08.Lemma_8_11_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

/-- Helper for Lemma 8.11.5: an equality morphism does not depend on the proof of the
object equality. -/
theorem eqToHom_eq_of_eq_proof {D : Type*} [Category D] {X Y : D} (h h' : X = Y) :
    (eqToHom h : X ⟶ Y) = eqToHom h' := by
  cases h
  simp

/-- Helper for Lemma 8.11.5: composing inverse equality transport with another proof of the
same equality gives the identity. -/
theorem eqToHom_symm_comp_of_eq_proof {D : Type*} [Category D] {X Y : D}
    (h h' : X = Y) :
    eqToHom h.symm ≫ eqToHom h' = 𝟙 Y := by
  rw [eqToHom_trans]
  exact eqToHom_eq_of_eq_proof _ rfl

/-- Helper for Lemma 8.11.5: equality transport cancels the target transport in the inverse of
an isomorphism conjugated by equality transports. -/
theorem eqToHom_symm_comp_isoTrans_inv {D : Type*} [Category D]
    {X X' Y Y' : D} (hX : X = X') (hY : Y = Y') (e : X' ≅ Y') :
    eqToHom hY.symm ≫ (eqToIso hX ≪≫ e ≪≫ eqToIso hY.symm).inv =
      e.inv ≫ eqToHom hX.symm := by
  cases hX
  cases hY
  simp

/-- Helper for Lemma 8.11.5: equality transport cancels the target transport in the forward
map of an isomorphism conjugated by equality transports. -/
theorem isoTrans_hom_comp_eqToHom {D : Type*} [Category D]
    {X X' Y Y' : D} (hX : X = X') (hY : Y = Y') (e : X' ≅ Y') :
    (eqToIso hX ≪≫ e ≪≫ eqToIso hY.symm).hom ≫ eqToHom hY =
      eqToHom hX ≫ e.hom := by
  cases hX
  cases hY
  simp

/-- Helper for Lemma 8.11.5: conjugating a morphism by equality transports cancels inside a
larger composite. -/
theorem comp_eqToHom_symm_comp_conjugated_comp_eqToHom {D : Type*} [Category D]
    {X X' Y Y' Z W : D} (hX : X = X') (hY : Y = Y')
    (a : Z ⟶ X') (f : X' ⟶ Y') (d : Y' ⟶ W) :
    a ≫ eqToHom hX.symm ≫ (eqToHom hX ≫ f ≫ eqToHom hY.symm) ≫
        eqToHom hY ≫ d =
      a ≫ f ≫ d := by
  cases hX
  cases hY
  simp

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Y' : StackInGroupoidsOver.{u, v, max u v, v} J}


namespace StackInGroupoidsOver.Hom

/-- Helper for Lemma 8.11.5: local essential surjectivity descends along a source map when the
composite is isomorphic to the locally essentially surjective morphism. -/
theorem locallyEssentiallySurjectiveOnObjects_of_comp_iso
    {A B S : StackInGroupoidsOver J}
    (E : A ⟶ B) (H : B ⟶ S) (K : A ⟶ S)
    (e : E ≫ H ≅ K)
    (hK : LocallyEssentiallySurjectiveOnObjects K) :
    LocallyEssentiallySurjectiveOnObjects H := by
  intro U y
  -- Lift `y` locally through `K`, then push the chosen source object forward along `E`.
  obtain ⟨𝒰, h𝒰⟩ := hK U y
  refine ⟨𝒰, ?_⟩
  intro I
  obtain ⟨x, hx⟩ := h𝒰 I
  refine ⟨(E.fiberFunctor I.Y).obj x, ?_⟩
  obtain ⟨η⟩ := hx
  -- The stack-morphism isomorphism identifies `H(E x)` with `K x` in the refined fiber.
  refine ⟨?_⟩
  exact
    (by
      simpa [BasedFunctor.comp] using
        fiberIsoOfStackHomIso (J := J) e (U := I.Y) x) ≪≫ η

/-- Helper for Lemma 8.11.5: local essential surjectivity descends along a source map when a
`2`-morphism identifies the composite with the locally essentially surjective morphism. -/
theorem locallyEssentiallySurjectiveOnObjects_of_comp_hom
    {A B S : StackInGroupoidsOver J}
    (E : A ⟶ B) (H : B ⟶ S) (K : A ⟶ S)
    (τ : E ≫ H ⟶ K)
    (hK : LocallyEssentiallySurjectiveOnObjects K) :
    LocallyEssentiallySurjectiveOnObjects H := by
  intro U y
  -- Lift `y` locally through `K`, then push the source object forward along `E`.
  obtain ⟨𝒰, h𝒰⟩ := hK U y
  refine ⟨𝒰, ?_⟩
  intro I
  obtain ⟨x, hx⟩ := h𝒰 I
  refine ⟨(E.fiberFunctor I.Y).obj x, ?_⟩
  obtain ⟨η⟩ := hx
  -- The `2`-cell supplies the required fiber isomorphism between `H(E x)` and `K x`.
  refine ⟨?_⟩
  exact
    (by
      simpa [BasedFunctor.comp] using
        fiberIsoOfStackHom (J := J) τ (U := I.Y) x) ≪≫ η

/-- Helper for Lemma 8.11.5: a gerbe-over property descends along an equivalence on the source
when the composite is identified by a `2`-morphism. -/
theorem isGerbeOver_of_source_equivalence_comp_hom
    {A B S : StackInGroupoidsOver J}
    (E : A ⟶ B) (H : B ⟶ S) (K : A ⟶ S)
    (hE : E.IsEquivalenceOverBase)
    (τ : E ≫ H ⟶ K)
    (hK : IsGerbeOver K) :
    IsGerbeOver H := by
  classical
  -- Compare the factorization of `K` with the factorization of `H` precomposed by `E`.
  let a := BasedFunctor.comp E.toBasedFunctor
    (fibredInGroupoidsFactorizationFromSource (toBasedFunctor H))
  let f := fibredInGroupoidsFactorizationToTarget (toBasedFunctor H)
  let b := fibredInGroupoidsFactorizationFromSource (toBasedFunctor K)
  let g := fibredInGroupoidsFactorizationToTarget (toBasedFunctor K)
  letI : IsFibredInGroupoids f.toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor H)
  letI : IsFibredInGroupoids g.toFunctor :=
    fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids (toBasedFunctor K)
  have ha : a.IsEquivalenceOverBase := by
    exact BasedFunctor.IsEquivalenceOverBase.comp hE
      (fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor H))
  have hb : b.IsEquivalenceOverBase :=
    fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase (toBasedFunctor K)
  have hfactorH :
      BasedFunctor.comp a f = BasedFunctor.comp E.toBasedFunctor H.toBasedFunctor := by
    -- Normalize both sides through the functorial factorization of `H`.
    exact
      (BasedFunctor.comp_assoc E.toBasedFunctor
        (fibredInGroupoidsFactorizationFromSource (toBasedFunctor H))
        (fibredInGroupoidsFactorizationToTarget (toBasedFunctor H))).trans
      (congrArg (BasedFunctor.comp E.toBasedFunctor)
        (fibredInGroupoidsFactorization_comp (toBasedFunctor H)))
  letI : IsIso τ := stackHom_isIso (J := J) τ
  have hτiso : BasedFunctor.comp E.toBasedFunctor H.toBasedFunctor ≅ K.toBasedFunctor := by
    simpa [BasedFunctor.comp] using basedFunctorIsoOfStackHomIso (J := J) (asIso τ)
  have haComm : Nonempty (BasedFunctor.comp a f ≅ toBasedFunctor K) :=
    ⟨eqToIso hfactorH ≪≫ hτiso⟩
  have hbComm : Nonempty (BasedFunctor.comp b g ≅ toBasedFunctor K) :=
    ⟨eqToIso (fibredInGroupoidsFactorization_comp (toBasedFunctor K))⟩
  obtain ⟨h, hEquiv, _⟩ :=
    exists_equivalence_over_target_between_fibred_groupoid_factorizations
      (F := toBasedFunctor K) (a := a) (f := f) (b := b) (g := g)
      ha hb haComm hbComm
  -- Transport the inherited-target gerbe structure across the comparison equivalence.
  letI : IsGerbe (inheritedTopology J S) g.toFunctor := hK
  have hHstack : IsStackInGroupoids (inheritedTopology J S) f.toFunctor := by
    exact (isStackInGroupoids_iff_of_equivalence_over_base
      (inheritedTopology J S) g.toFunctor f.toFunctor h hEquiv).1 inferInstance
  letI : IsStackInGroupoids (inheritedTopology J S) f.toFunctor := hHstack
  let sourceStack : StackInGroupoidsOver (inheritedTopology J S) :=
    StackInGroupoidsOver.ofProjection (inheritedTopology J S) g.toFunctor
  let targetStack : StackInGroupoidsOver (inheritedTopology J S) :=
    StackInGroupoidsOver.ofProjection (inheritedTopology J S) f.toFunctor
  let Hmap : sourceStack ⟶ targetStack :=
    StackInGroupoidsOver.Hom.ofBasedFunctor h
  have hHmap : Hmap.IsEquivalenceOverBase := by
    change h.IsEquivalenceOverBase
    exact hEquiv
  change IsGerbe (inheritedTopology J S) f.toFunctor
  simpa [sourceStack, targetStack, Hmap] using
    isGerbe_of_equivalence_over_base (J := inheritedTopology J S) Hmap hHmap hK

/-- Helper for Lemma 8.11.5: applying a stack morphism to a chosen pullback object is
canonically isomorphic to the chosen pullback of the image object. -/
noncomputable abbrev fiber_pullback_comparison_iso
    {B S : StackInGroupoidsOver J} (G : B ⟶ S)
      {U V : C} (f : V ⟶ U) (y : B.p.Fiber U) :
      (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.obj
          ((G.toBasedFunctor.fiberFunctor U).obj y)) ≅
        (G.toBasedFunctor.fiberFunctor V).obj
          (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj y) :=
    FibredCategoryMor.pullbackComparison (F := G.toFibredCategoryMor) f y

/-- Helper for Lemma 8.11.5: the projection of a morphism in the explicit stack
`2`-fibre product to the base category is its stored base arrow. -/
theorem stackTwoFibreProduct_base_map
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {P Q : (stackTwoFibreProduct (J := J) F G).S}
    (φ : P ⟶ Q) :
    (stackTwoFibreProduct (J := J) F G).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 8.11.5: the left projection of an explicit stack
`2`-fibre-product morphism is its stored left component. -/
theorem stackTwoFibreProduct_left_map
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {P Q : (stackTwoFibreProduct (J := J) F G).S}
    (φ : P ⟶ Q) :
    ((stackTwoFibreProductSquare (J := J) F G).p.toBasedFunctor).map φ = φ.a := by
  rfl

/-- Helper for Lemma 8.11.5: the right projection of an explicit stack
`2`-fibre-product morphism is its stored right component. -/
theorem stackTwoFibreProduct_right_map
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {P Q : (stackTwoFibreProduct (J := J) F G).S}
    (φ : P ⟶ Q) :
    ((stackTwoFibreProductSquare (J := J) F G).q.toBasedFunctor).map φ = φ.b := by
  rfl

/-- Helper for Lemma 8.11.5: pull back an object of a fiberwise categorical pullback along a
base arrow, using the pullback-comparison isomorphisms for the two legs. -/
noncomputable def pullbackOfFiberProductObj
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U V : C} (f : V ⟶ U)
    (P : Limits.CategoricalPullback (F.fiberFunctor U) (G.fiberFunctor U)) :
    Limits.CategoricalPullback (F.fiberFunctor V) (G.fiberFunctor V) :=
  { fst := ((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj P.fst
    snd := ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj P.snd
    iso := (FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f P.fst).symm ≪≫
      (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.mapIso P.iso) ≪≫
      FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f P.snd }

/-- Helper for Lemma 8.11.5: under the standard fiber-pullback equivalence, the first projection
is the left projection of the explicit stack `2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) (U : C) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor ⋙
      Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U) =
        FibredCategoryMor.fiberFunctor
          (toFibredCategoryMor (stackTwoFibreProductSquare (J := J) F G).p) U := by
  -- Reuse the owner computation for the explicit pullback, in the stack-square spelling.
  change
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor ⋙
      Limits.CategoricalPullback.π₁ (F.fiberFunctor U) (G.fiberFunctor U) =
        (stackTwoFibreProductSquare (J := J) F G).p.fiberFunctor U
  simpa using
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
      F.toBasedFunctor G.toBasedFunctor U)

/-- Helper for Lemma 8.11.5: under the standard fiber-pullback equivalence, the second projection
is the right projection of the explicit stack `2`-fibre product. -/
theorem fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S) (U : C) :
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor ⋙
      Limits.CategoricalPullback.π₂ (F.fiberFunctor U) (G.fiberFunctor U) =
        FibredCategoryMor.fiberFunctor
          (toFibredCategoryMor (stackTwoFibreProductSquare (J := J) F G).q) U := by
  -- Reuse the owner computation for the explicit pullback, in the stack-square spelling.
  change
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor ⋙
      Limits.CategoricalPullback.π₂ (F.fiberFunctor U) (G.fiberFunctor U) =
        (stackTwoFibreProductSquare (J := J) F G).q.fiberFunctor U
  simpa using
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
      F.toBasedFunctor G.toBasedFunctor U)

/-- Helper for Lemma 8.11.5: equality of functors transports mapped arrows by the
object-level `eqToHom` transports. -/
private theorem functorMap_eqToHom_comp_of_functor_eq
    {D E : Type*} [Category D] [Category E]
    {F G : D ⥤ E} (h : F = G) {X Y : D} (f : X ⟶ Y) :
    F.map f ≫ eqToHom (congrArg (fun H : D ⥤ E => H.obj Y) h) =
      eqToHom (congrArg (fun H : D ⥤ E => H.obj X) h) ≫ G.map f := by
  cases h
  simp

/-- Helper for Lemma 8.11.5: the structural isomorphism stored in the explicit stack
`2`-fibre product is the fiber isomorphism coming from the square comparison, up to the projection
transports supplied by the standard fiber-pullback equivalence. -/
private theorem fiberPullbackStructuralIso_hom
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U : C}
    (y : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)
    (leftY :
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj y).fst =
        ((stackTwoFibreProductSquare (J := J) F G).p.fiberFunctor U).obj y)
    (rightY :
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj y).snd =
        ((stackTwoFibreProductSquare (J := J) F G).q.fiberFunctor U).obj y) :
    (F.fiberFunctor U).map (eqToHom leftY) ≫
        (fiberIsoOfStackHom (J := J)
          (stackTwoFibreProductSquare (J := J) F G).ψ.hom y).hom =
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj y).iso.hom ≫
        (G.fiberFunctor U).map (eqToHom rightY) := by
  cases y with
  | mk P hP =>
      cases P with
      | mk UP Pobj =>
          change UP = U at hP
          cases hP
          cases Pobj with
          | mk Pfst Psnd Piso =>
              cases leftY
              cases rightY
              apply Functor.Fiber.hom_ext
              -- Forget to the total category, where the comparison is the stored `Piso`.
              change
                Functor.Fiber.fiberInclusion.map
                    ((F.fiberFunctor U).map (eqToHom rfl) ≫
                      (fiberIsoOfStackHom (J := J)
                        (stackTwoFibreProductSquare (J := J) F G).ψ.hom
                        (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                          (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).hom) =
                  Functor.Fiber.fiberInclusion.map
                    (Piso.hom ≫ (G.fiberFunctor U).map (eqToHom rfl))
              simp only [eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id]
              change
                (fiberIsoOfStackHom (J := J) (stackTwoFibreProductSquare (J := J) F G).ψ.hom
                  (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                    (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).hom.1 =
                    Piso.hom.1
              exact fiberIsoOfStackHom_hom_val (J := J)
                (τ := (stackTwoFibreProductSquare (J := J) F G).ψ.hom)
                (x := (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                  (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U))

/-- Helper for Lemma 8.11.5: the same structural isomorphism comparison as
`fiberPullbackStructuralIso_hom`, with the projection transports oriented from the projection
fibers back to the standard fiber-pullback object. -/
private theorem fiberPullbackStructuralIso_hom_invTransports
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U : C}
    (y : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)
    (leftY :
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj y).fst =
        ((stackTwoFibreProductSquare (J := J) F G).p.fiberFunctor U).obj y)
    (rightY :
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj y).snd =
        ((stackTwoFibreProductSquare (J := J) F G).q.fiberFunctor U).obj y) :
    (F.fiberFunctor U).map (eqToHom leftY.symm) ≫
        ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          F.toBasedFunctor G.toBasedFunctor U).functor.obj y).iso.hom =
      (fiberIsoOfStackHom (J := J)
        (stackTwoFibreProductSquare (J := J) F G).ψ.hom y).hom ≫
        (G.fiberFunctor U).map (eqToHom rightY.symm) := by
  cases y with
  | mk P hP =>
      cases P with
      | mk UP Pobj =>
          change UP = U at hP
          cases hP
          cases Pobj with
          | mk Pfst Psnd Piso =>
              cases leftY
              cases rightY
              apply Functor.Fiber.hom_ext
              -- With the transports gone, the inverse-oriented statement is the same
              -- stored comparison in the total category.
              change
                Functor.Fiber.fiberInclusion.map
                    ((F.fiberFunctor U).map (eqToHom rfl) ≫
                      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                        F.toBasedFunctor G.toBasedFunctor U).functor.obj
                        (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                          (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).iso.hom) =
                  Functor.Fiber.fiberInclusion.map
                    ((fiberIsoOfStackHom (J := J)
                        (stackTwoFibreProductSquare (J := J) F G).ψ.hom
                        (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                          (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).hom ≫
                      (G.fiberFunctor U).map (eqToHom rfl))
              simp only [eqToHom_refl, Functor.map_id, Category.id_comp]
              change
                Functor.Fiber.fiberInclusion.map
                    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
                      F.toBasedFunctor G.toBasedFunctor U).functor.obj
                      (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                        (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).iso.hom =
                  Functor.Fiber.fiberInclusion.map
                    ((fiberIsoOfStackHom (J := J)
                        (stackTwoFibreProductSquare (J := J) F G).ψ.hom
                        (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                          (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U)).hom ≫ 𝟙 _)
              simp only [Category.comp_id, Functor.Fiber.fiberInclusion]
              exact (fiberIsoOfStackHom_hom_val (J := J)
                (τ := (stackTwoFibreProductSquare (J := J) F G).ψ.hom)
                (x := (⟨{ U := U, obj := { fst := Pfst, snd := Psnd, iso := Piso } }, rfl⟩ :
                  (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U))).symm

/-- Helper for Lemma 8.11.5: the first component of the normalized pullback object agrees with
the first component of the canonical pullback in the explicit stack `2`-fibre product. -/
noncomputable def fibreOfPullback_pullbackObjIsoLeft
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U V : C} (f : V ⟶ U)
    (x : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U) :
    (pullbackOfFiberProductObj (J := J) F G f
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj x)).fst ≅
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      F.toBasedFunctor G.toBasedFunctor V).functor.obj
      (f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x)).fst :=
  let eU := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor U
  let eV := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor V
  let p := (stackTwoFibreProductSquare (J := J) F G).p
  let xpb := f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x
  let hπ₁U :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
      (J := J) F G U
  let hπ₁V :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
      (J := J) F G V
  let leftU : (eU.functor.obj x).fst = (p.fiberFunctor U).obj x :=
    congrArg (fun H ↦ H.obj x) hπ₁U
  let leftV : (eV.functor.obj xpb).fst = (p.fiberFunctor V).obj xpb :=
    congrArg (fun H ↦ H.obj xpb) hπ₁V
  eqToIso (congrArg
      (fun y ↦ ((canonicalPullbackChoice A.p).pullbackFunctor f).obj y) leftU) ≪≫
    FibredCategoryMor.pullbackComparison p.toFibredCategoryMor f x ≪≫
    eqToIso leftV.symm

/-- Helper for Lemma 8.11.5: the second component of the normalized pullback object agrees with
the second component of the canonical pullback in the explicit stack `2`-fibre product. -/
noncomputable def fibreOfPullback_pullbackObjIsoRight
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U V : C} (f : V ⟶ U)
    (x : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U) :
    (pullbackOfFiberProductObj (J := J) F G f
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj x)).snd ≅
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      F.toBasedFunctor G.toBasedFunctor V).functor.obj
      (f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x)).snd :=
  let eU := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor U
  let eV := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor V
  let q := (stackTwoFibreProductSquare (J := J) F G).q
  let xpb := f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x
  let hπ₂U :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G U
  let hπ₂V :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G V
  let rightU : (eU.functor.obj x).snd = (q.fiberFunctor U).obj x :=
    congrArg (fun H ↦ H.obj x) hπ₂U
  let rightV : (eV.functor.obj xpb).snd = (q.fiberFunctor V).obj xpb :=
    congrArg (fun H ↦ H.obj xpb) hπ₂V
  eqToIso (congrArg
      (fun y ↦ ((canonicalPullbackChoice B.p).pullbackFunctor f).obj y) rightU) ≪≫
    FibredCategoryMor.pullbackComparison q.toFibredCategoryMor f x ≪≫
    eqToIso rightV.symm

/-- Helper for Lemma 8.11.5: the two component comparisons for the normalized pullback object
respect the categorical-pullback structural isomorphisms. -/
theorem fibreOfPullback_pullbackObjIso_components_compatible
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U V : C} (f : V ⟶ U)
    (x : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U) :
    let P := pullbackOfFiberProductObj (J := J) F G f
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj x)
    let Q := (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      F.toBasedFunctor G.toBasedFunctor V).functor.obj
      (f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x)
    (F.fiberFunctor V).map
        (fibreOfPullback_pullbackObjIsoLeft (J := J) F G f x).hom ≫
      Q.iso.hom =
        P.iso.hom ≫
          (G.fiberFunctor V).map
            (fibreOfPullback_pullbackObjIsoRight (J := J) F G f x).hom := by
  dsimp
  let eU := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor U
  let eV := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor V
  let p := (stackTwoFibreProductSquare (J := J) F G).p
  let q := (stackTwoFibreProductSquare (J := J) F G).q
  let xpb := f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x
  let hπ₁U :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
      (J := J) F G U
  let hπ₁V :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection
      (J := J) F G V
  let hπ₂U :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G U
  let hπ₂V :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G V
  let leftU : (eU.functor.obj x).fst = (p.fiberFunctor U).obj x :=
    congrArg (fun H ↦ H.obj x) hπ₁U
  let leftV : (eV.functor.obj xpb).fst = (p.fiberFunctor V).obj xpb :=
    congrArg (fun H ↦ H.obj xpb) hπ₁V
  let rightU : (eU.functor.obj x).snd = (q.fiberFunctor U).obj x :=
    congrArg (fun H ↦ H.obj x) hπ₂U
  let rightV : (eV.functor.obj xpb).snd = (q.fiberFunctor V).obj xpb :=
    congrArg (fun H ↦ H.obj xpb) hπ₂V
  -- Compatibility is the defining square of the pulled-back object, with the projection
  -- transports moved through the pullback-comparison isomorphisms.
  let ψ := (stackTwoFibreProductSquare (J := J) F G).ψ
  have hnat := fiberIsoOfStackHom_pullbackComparison_hom_naturality (J := J) ψ.hom f x
  have hleftComp := pullbackComparison_comp_hom (J := J) p F f x
  have hrightComp := pullbackComparison_comp_hom (J := J) q G f x
  rw [← hleftComp, ← hrightComp] at hnat
  let Sf := ((canonicalPullbackChoice S.p).pullbackFunctor f)
  let cF :=
    FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f ((p.fiberFunctor U).obj x)
  let cG :=
    FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f ((q.fiberFunctor U).obj x)
  let cFe :=
    FibredCategoryMor.pullbackComparison F.toFibredCategoryMor f (eU.functor.obj x).fst
  let cGe :=
    FibredCategoryMor.pullbackComparison G.toFibredCategoryMor f (eU.functor.obj x).snd
  let cP := FibredCategoryMor.pullbackComparison p.toFibredCategoryMor f x
  let cQ := FibredCategoryMor.pullbackComparison q.toFibredCategoryMor f x
  let sourceIso := (fiberIsoOfStackHom (J := J) ψ.hom x).hom
  let targetIso := (fiberIsoOfStackHom (J := J) ψ.hom xpb).hom
  have hcancelled :
      (F.fiberFunctor V).map cP.hom ≫ targetIso =
        cF.inv ≫
          (((canonicalPullbackChoice S.p).pullbackFunctor f).map sourceIso ≫
            cG.hom ≫ (G.fiberFunctor V).map cQ.hom) := by
    calc
      (F.fiberFunctor V).map cP.hom ≫ targetIso =
          (cF.inv ≫ cF.hom) ≫ (F.fiberFunctor V).map cP.hom ≫ targetIso := by
            simp only [Iso.inv_hom_id, Category.id_comp]
      _ = cF.inv ≫ ((cF.hom ≫ (F.fiberFunctor V).map cP.hom) ≫ targetIso) := by
            simp only [Category.assoc]
      _ = cF.inv ≫
          (((canonicalPullbackChoice S.p).pullbackFunctor f).map sourceIso ≫
            cG.hom ≫ (G.fiberFunctor V).map cQ.hom) := by
            exact congrArg (fun k ↦ cF.inv ≫ k) hnat.symm
  let lU : (eU.functor.obj x).fst ⟶ (p.fiberFunctor U).obj x := eqToHom leftU
  let rU : (eU.functor.obj x).snd ⟶ (q.fiberFunctor U).obj x := eqToHom rightU
  let lVpb := ((canonicalPullbackChoice A.p).pullbackFunctor f).map lU
  let rVpb := ((canonicalPullbackChoice B.p).pullbackFunctor f).map rU
  let lVtarget : (p.fiberFunctor V).obj xpb ⟶ (eV.functor.obj xpb).fst :=
    eqToHom leftV.symm
  let rVtarget : (q.fiberFunctor V).obj xpb ⟶ (eV.functor.obj xpb).snd :=
    eqToHom rightV.symm
  have hsourceStruct :
      (F.fiberFunctor U).map lU ≫ sourceIso =
        (eU.functor.obj x).iso.hom ≫ (G.fiberFunctor U).map rU := by
    simpa only [eU, p, q, ψ, lU, rU, sourceIso] using
      fiberPullbackStructuralIso_hom (J := J) F G x leftU rightU
  have htargetStruct :
      (F.fiberFunctor V).map lVtarget ≫ (eV.functor.obj xpb).iso.hom =
        targetIso ≫ (G.fiberFunctor V).map rVtarget := by
    simpa only [eV, p, q, ψ, lVtarget, rVtarget, targetIso] using
      fiberPullbackStructuralIso_hom_invTransports (J := J) F G xpb leftV rightV
  have hleftNat :
      (F.fiberFunctor V).map lVpb ≫ cF.inv =
        cFe.inv ≫ Sf.map ((F.fiberFunctor U).map lU) := by
    simpa only [lVpb, cF, cFe, Sf] using
      (stack_morphism_pullbackComparison_inv_naturality_over_vertical
        F.toFibredCategoryMor f lU)
  have hrightNat :
      Sf.map ((G.fiberFunctor U).map rU) ≫ cG.hom =
        cGe.hom ≫ (G.fiberFunctor V).map rVpb := by
    simpa only [rVpb, cG, cGe, Sf] using
      (stack_morphism_pullbackComparison_naturality_over_vertical
        G.toFibredCategoryMor f rU)
  have hsourceMap :
      Sf.map ((F.fiberFunctor U).map lU) ≫ Sf.map sourceIso =
        Sf.map (eU.functor.obj x).iso.hom ≫
          Sf.map ((G.fiberFunctor U).map rU) := by
    have hmap := congrArg (fun k ↦ Sf.map k) hsourceStruct
    calc
      Sf.map ((F.fiberFunctor U).map lU) ≫ Sf.map sourceIso =
          Sf.map ((F.fiberFunctor U).map lU ≫ sourceIso) := by
            exact (Sf.map_comp ((F.fiberFunctor U).map lU) sourceIso).symm
      _ = Sf.map ((eU.functor.obj x).iso.hom ≫
          (G.fiberFunctor U).map rU) := hmap
      _ = Sf.map (eU.functor.obj x).iso.hom ≫
          Sf.map ((G.fiberFunctor U).map rU) := by
            exact Sf.map_comp (eU.functor.obj x).iso.hom
              ((G.fiberFunctor U).map rU)
  have htransported :
      (F.fiberFunctor V).map lVpb ≫ (F.fiberFunctor V).map cP.hom ≫
          (F.fiberFunctor V).map lVtarget ≫ (eV.functor.obj xpb).iso.hom =
        cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫ cGe.hom ≫
          (G.fiberFunctor V).map rVpb ≫ (G.fiberFunctor V).map cQ.hom ≫
            (G.fiberFunctor V).map rVtarget := by
    calc
      (F.fiberFunctor V).map lVpb ≫ (F.fiberFunctor V).map cP.hom ≫
          (F.fiberFunctor V).map lVtarget ≫ (eV.functor.obj xpb).iso.hom =
        (F.fiberFunctor V).map lVpb ≫
          (((F.fiberFunctor V).map cP.hom ≫ targetIso) ≫
            (G.fiberFunctor V).map rVtarget) := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦
                (F.fiberFunctor V).map lVpb ≫ (F.fiberFunctor V).map cP.hom ≫ k)
                htargetStruct
      _ = (F.fiberFunctor V).map lVpb ≫
          ((cF.inv ≫ (Sf.map sourceIso ≫ cG.hom ≫
            (G.fiberFunctor V).map cQ.hom)) ≫
            (G.fiberFunctor V).map rVtarget) := by
            exact congrArg (fun k ↦
              (F.fiberFunctor V).map lVpb ≫ (k ≫ (G.fiberFunctor V).map rVtarget))
              hcancelled
      _ = ((F.fiberFunctor V).map lVpb ≫ cF.inv) ≫
          (Sf.map sourceIso ≫ cG.hom ≫ (G.fiberFunctor V).map cQ.hom) ≫
          (G.fiberFunctor V).map rVtarget := by
            simp only [Category.assoc]
      _ = (cFe.inv ≫ Sf.map ((F.fiberFunctor U).map lU)) ≫
          (Sf.map sourceIso ≫ cG.hom ≫ (G.fiberFunctor V).map cQ.hom) ≫
          (G.fiberFunctor V).map rVtarget := by
            exact congrArg (fun k ↦
              k ≫ (Sf.map sourceIso ≫ cG.hom ≫ (G.fiberFunctor V).map cQ.hom) ≫
                (G.fiberFunctor V).map rVtarget) hleftNat
      _ = cFe.inv ≫
          (Sf.map ((F.fiberFunctor U).map lU) ≫ Sf.map sourceIso) ≫ cG.hom ≫
          (G.fiberFunctor V).map cQ.hom ≫ (G.fiberFunctor V).map rVtarget := by
            simp only [Category.assoc]
      _ = cFe.inv ≫
          (Sf.map (eU.functor.obj x).iso.hom ≫
            Sf.map ((G.fiberFunctor U).map rU)) ≫ cG.hom ≫
          (G.fiberFunctor V).map cQ.hom ≫ (G.fiberFunctor V).map rVtarget := by
            exact congrArg (fun k ↦
              cFe.inv ≫ k ≫ cG.hom ≫ (G.fiberFunctor V).map cQ.hom ≫
                (G.fiberFunctor V).map rVtarget) hsourceMap
      _ = cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
          (Sf.map ((G.fiberFunctor U).map rU) ≫ cG.hom) ≫
          (G.fiberFunctor V).map cQ.hom ≫ (G.fiberFunctor V).map rVtarget := by
            simp only [Category.assoc]
      _ = cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
          (cGe.hom ≫ (G.fiberFunctor V).map rVpb) ≫
          (G.fiberFunctor V).map cQ.hom ≫ (G.fiberFunctor V).map rVtarget := by
            exact congrArg (fun k ↦
              cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫ k ≫
                (G.fiberFunctor V).map cQ.hom ≫ (G.fiberFunctor V).map rVtarget)
              hrightNat
      _ = cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫ cGe.hom ≫
          (G.fiberFunctor V).map rVpb ≫ (G.fiberFunctor V).map cQ.hom ≫
            (G.fiberFunctor V).map rVtarget := by
            simp only [Category.assoc]
  have htransportedPacked :
      (F.fiberFunctor V).map (lVpb ≫ cP.hom ≫ lVtarget) ≫
          (eV.functor.obj xpb).iso.hom =
        cFe.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫ cGe.hom ≫
          (G.fiberFunctor V).map (rVpb ≫ cQ.hom ≫ rVtarget) := by
    simpa only [Functor.map_comp, Category.assoc] using htransported
  simpa only [fibreOfPullback_pullbackObjIsoLeft, fibreOfPullback_pullbackObjIsoRight,
    pullbackOfFiberProductObj, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    eqToIso.hom, eqToHom_map, Functor.mapIso_hom,
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductLeftProjection,
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection,
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁,
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂,
    stackTwoFibreProductSquare, stackTwoFibreProduct,
    StackInGroupoidsOver.ofAmbientHom, StackInGroupoidsOver.Hom.ofAmbientHomIso,
    FibredInGroupoidsOver.twoFibreProductSquare,
    FibredInGroupoidsOver.twoFibreProductLeftProjection,
    FibredInGroupoidsOver.twoFibreProductRightProjection,
    FibredInGroupoidsOver.twoFibreProduct,
    FibredCategoryOver.twoFibreProductSquare,
    Functor.Fiber.fiberInclusion,
    hπ₁U, hπ₁V, hπ₂U, hπ₂V,
    cFe, cGe, cP, cQ, lU, rU, lVpb, rVpb, lVtarget, rVtarget,
    Sf] using htransportedPacked

/-- Helper for Lemma 8.11.5: the chosen pullback in the explicit pullback fiber corresponds to
the normalized categorical pullback of the associated fiber-product object. -/
noncomputable def fibreOfPullback_pullbackObjIso
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    {U V : C} (f : V ⟶ U)
    (x : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U) :
    pullbackOfFiberProductObj (J := J) F G f
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        F.toBasedFunctor G.toBasedFunctor U).functor.obj x) ≅
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      F.toBasedFunctor G.toBasedFunctor V).functor.obj
      (f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p] x) :=
  Limits.CategoricalPullback.mkIso
    (fibreOfPullback_pullbackObjIsoLeft (J := J) F G f x)
    (fibreOfPullback_pullbackObjIsoRight (J := J) F G f x)
    (fibreOfPullback_pullbackObjIso_components_compatible (J := J) F G f x)

/-- Helper for Lemma 8.11.5: the right projection from the canonical stack `2`-fibre product is
locally essentially surjective on objects when the left leg is. -/
theorem twoFibreProductRightProjection_locallyEssentiallySurjectiveOnObjects
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    (hFess : LocallyEssentiallySurjectiveOnObjects F) :
    LocallyEssentiallySurjectiveOnObjects (stackTwoFibreProductSquare (J := J) F G).q := by
  intro U y
  -- Lift `G(y)` locally through `F`, then package the lifted object with the pulled-back `y`.
  obtain ⟨𝒰, h𝒰⟩ := hFess U ((G.toBasedFunctor.fiberFunctor U).obj y)
  refine ⟨𝒰, ?_⟩
  intro I
  obtain ⟨x, hx⟩ := h𝒰 I
  let e₀ :
      (F.toBasedFunctor.fiberFunctor I.Y).obj x ≅
        (((canonicalFiberPseudofunctor S.p).map I.f.op.toLoc).toFunctor.obj
          ((G.toBasedFunctor.fiberFunctor U).obj y)) :=
    Classical.choice hx
  let P :
      Limits.CategoricalPullback
        (F.toBasedFunctor.fiberFunctor I.Y)
        (G.toBasedFunctor.fiberFunctor I.Y) :=
    { fst := x
      snd := (((canonicalFiberPseudofunctor B.p).map I.f.op.toLoc).toFunctor.obj y)
      iso := e₀ ≪≫ fiber_pullback_comparison_iso (J := J) G I.f y }
  let e := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor I.Y
  refine ⟨e.inverse.obj P, ?_⟩
  -- The standard fiber-pullback equivalence identifies the right projection with `π₂`.
  change Nonempty
    ((BasedFunctor.fiberFunctor
        (CategoryOver.explicitTwoFibreProductRightProjection F.toBasedFunctor G.toBasedFunctor)
        I.Y).obj (e.inverse.obj P) ≅ _)
  let hπ₂ :
      e.functor ⋙
          Limits.CategoricalPullback.π₂
            (F.toBasedFunctor.fiberFunctor I.Y)
            (G.toBasedFunctor.fiberFunctor I.Y) =
        BasedFunctor.fiberFunctor
          (CategoryOver.explicitTwoFibreProductRightProjection F.toBasedFunctor G.toBasedFunctor)
          I.Y :=
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
      F.toBasedFunctor G.toBasedFunctor I.Y
  refine ⟨(eqToIso (congrArg (fun H ↦ H.obj (e.inverse.obj P)) hπ₂.symm)) ≪≫ ?_⟩
  simpa [P] using
    Functor.mapIso
      (Limits.CategoricalPullback.π₂
        (F.toBasedFunctor.fiberFunctor I.Y)
        (G.toBasedFunctor.fiberFunctor I.Y))
      (e.counitIso.app P)

/-- Helper for Lemma 8.11.5: the right projection from the canonical stack `2`-fibre product
locally lifts fiber morphisms when the left leg does. -/
theorem twoFibreProductRightProjection_locallyLiftsFiberMorphisms
    {A B S : StackInGroupoidsOver J}
    (F : A ⟶ S) (G : B ⟶ S)
    (hFlift : LocallyLiftsFiberMorphisms F) :
    LocallyLiftsFiberMorphisms (stackTwoFibreProductSquare (J := J) F G).q := by
  intro U x x' b
  let eU := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor U
  let q := (stackTwoFibreProductSquare (J := J) F G).q
  let hπ₂U :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G U
  let rightU : (eU.functor.obj x).snd = (q.fiberFunctor U).obj x :=
    congrArg (fun H : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U ⥤
        B.p.Fiber U ↦ H.obj x) hπ₂U
  let rightU' : (eU.functor.obj x').snd = (q.fiberFunctor U).obj x' :=
    congrArg (fun H : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber U ⥤
        B.p.Fiber U ↦ H.obj x') hπ₂U
  let bCat : (eU.functor.obj x).snd ⟶ (eU.functor.obj x').snd :=
    eqToHom rightU ≫ b ≫ eqToHom rightU'.symm
  let β : (F.fiberFunctor U).obj (eU.functor.obj x).fst ⟶
      (F.fiberFunctor U).obj (eU.functor.obj x').fst :=
    (eU.functor.obj x).iso.hom ≫
      (G.fiberFunctor U).map bCat ≫
      (eU.functor.obj x').iso.inv
  -- Lift the induced morphism on the left leg locally through the original gerbe morphism `F`.
  obtain ⟨R, hR⟩ := hFlift (eU.functor.obj x).fst (eU.functor.obj x').fst β
  refine ⟨R, ?_⟩
  intro I
  obtain ⟨aF, haF⟩ := hR I
  let eV := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    F.toBasedFunctor G.toBasedFunctor I.Y
  let hπ₂V :=
    fibreOfPullback_equiv_pullbackOfFibres_functor_comp_stackTwoFibreProductRightProjection
      (J := J) F G I.Y
  let bPBCat := ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map bCat
  let Pstd := pullbackOfFiberProductObj (J := J) F G I.f (eU.functor.obj x)
  let Pstd' := pullbackOfFiberProductObj (J := J) F G I.f (eU.functor.obj x')
  let δstd : Pstd ⟶ Pstd' :=
    { fst := aF
      snd := bPBCat
      w := by
        -- In the normalized categorical pullback, the compatibility square is exactly the
        -- local lifting square for `F`, after moving across pullback-comparison naturality
        -- for the right leg.
        let cFx :=
          FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f
            (eU.functor.obj x).fst
        let cFx' :=
          FibredCategoryMor.pullbackComparison F.toFibredCategoryMor I.f
            (eU.functor.obj x').fst
        let cGx :=
          FibredCategoryMor.pullbackComparison G.toFibredCategoryMor I.f
            (eU.functor.obj x).snd
        let cGx' :=
          FibredCategoryMor.pullbackComparison G.toFibredCategoryMor I.f
            (eU.functor.obj x').snd
        let Sf := ((canonicalFiberPseudofunctor S.p).map I.f.op.toLoc).toFunctor
        have hFmove :
            (F.fiberFunctor I.Y).map aF ≫ cFx'.inv =
              cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫
                  Sf.map (eU.functor.obj x').iso.inv := by
          calc
            (F.fiberFunctor I.Y).map aF ≫ cFx'.inv =
                (cFx.inv ≫ cFx.hom) ≫ (F.fiberFunctor I.Y).map aF ≫ cFx'.inv := by
                  simp only [Iso.inv_hom_id, Category.id_comp]
            _ = cFx.inv ≫ (cFx.hom ≫ (F.fiberFunctor I.Y).map aF) ≫ cFx'.inv := by
                  simp only [Category.assoc]
            _ = cFx.inv ≫ (Sf.map β ≫ cFx'.hom) ≫ cFx'.inv := by
                  exact congrArg (fun k ↦ cFx.inv ≫ k ≫ cFx'.inv) haF.w.symm
            _ = cFx.inv ≫ Sf.map β := by
                  have hcancel :
                      (cFx.inv ≫ Sf.map β) ≫ (cFx'.hom ≫ cFx'.inv) =
                        (cFx.inv ≫ Sf.map β) ≫ 𝟙 _ := by
                    exact congrArg (fun k ↦ (cFx.inv ≫ Sf.map β) ≫ k) cFx'.hom_inv_id
                  simpa only [Category.assoc, Category.comp_id] using hcancel
            _ = cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                  Sf.map ((G.fiberFunctor U).map bCat) ≫
                    Sf.map (eU.functor.obj x').iso.inv := by
                  have hβ :
                      β = (eU.functor.obj x).iso.hom ≫
                        (G.fiberFunctor U).map bCat ≫
                          (eU.functor.obj x').iso.inv := rfl
                  have hβmap :
                      Sf.map β =
                        Sf.map (eU.functor.obj x).iso.hom ≫
                          Sf.map ((G.fiberFunctor U).map bCat) ≫
                            Sf.map (eU.functor.obj x').iso.inv := by
                    rw [hβ]
                    exact (Sf.map_comp (eU.functor.obj x).iso.hom
                      ((G.fiberFunctor U).map bCat ≫
                        (eU.functor.obj x').iso.inv)).trans (by
                        rw [Functor.map_comp])
                  simpa only [Category.assoc] using
                    congrArg (fun k ↦ cFx.inv ≫ k) hβmap
        have hGnat :
            Sf.map ((G.fiberFunctor U).map bCat) ≫ cGx'.hom =
              cGx.hom ≫ (G.fiberFunctor I.Y).map bPBCat := by
          simpa only [Sf, cGx, cGx', bPBCat] using
            (stack_morphism_pullbackComparison_naturality_over_vertical
              G.toFibredCategoryMor (f := I.f) (φ := bCat))
        have hGnatAssoc :
            cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫ cGx'.hom =
              cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                cGx.hom ≫ (G.fiberFunctor I.Y).map bPBCat := by
          simpa only [Category.assoc] using
            congrArg (fun k ↦ cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫ k) hGnat
        have hexpandTarget :
            (F.fiberFunctor I.Y).map aF ≫ Pstd'.iso.hom =
              ((F.fiberFunctor I.Y).map aF ≫ cFx'.inv) ≫
                Sf.map (eU.functor.obj x').iso.hom ≫ cGx'.hom := by
          simp only [Pstd', pullbackOfFiberProductObj, cFx', cGx', Sf, Iso.trans_hom,
            Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
          rfl
        have hmoveTarget :
            ((F.fiberFunctor I.Y).map aF ≫ cFx'.inv) ≫
                Sf.map (eU.functor.obj x').iso.hom ≫ cGx'.hom =
              (cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                  Sf.map ((G.fiberFunctor U).map bCat) ≫
                    Sf.map (eU.functor.obj x').iso.inv) ≫
                Sf.map (eU.functor.obj x').iso.hom ≫ cGx'.hom := by
          rw [hFmove]
          rfl
        have hcancelTarget :
            (cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                  Sf.map ((G.fiberFunctor U).map bCat) ≫
                    Sf.map (eU.functor.obj x').iso.inv) ≫
                Sf.map (eU.functor.obj x').iso.hom ≫ cGx'.hom =
              cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫ cGx'.hom := by
          have hcancelIso :
              Sf.map (eU.functor.obj x').iso.inv ≫
                  Sf.map (eU.functor.obj x').iso.hom = 𝟙 _ := by
            exact Eq.trans
              (Eq.symm (Sf.map_comp (eU.functor.obj x').iso.inv
                (eU.functor.obj x').iso.hom))
              (Eq.trans (congrArg Sf.map (eU.functor.obj x').iso.inv_hom_id)
                (Sf.map_id _))
          calc
            (cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                  Sf.map ((G.fiberFunctor U).map bCat) ≫
                    Sf.map (eU.functor.obj x').iso.inv) ≫
                Sf.map (eU.functor.obj x').iso.hom ≫ cGx'.hom =
              cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫
                  (Sf.map (eU.functor.obj x').iso.inv ≫
                    Sf.map (eU.functor.obj x').iso.hom) ≫ cGx'.hom := by
                simp only [Category.assoc]
            _ = cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫ 𝟙 _ ≫ cGx'.hom := by
                exact congrArg
                  (fun k ↦ cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                    Sf.map ((G.fiberFunctor U).map bCat) ≫ k ≫ cGx'.hom)
                  hcancelIso
            _ = cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫ cGx'.hom := by
                simp only [Category.id_comp]
        have hsourceTarget :
            cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                Sf.map ((G.fiberFunctor U).map bCat) ≫ cGx'.hom =
              Pstd.iso.hom ≫ (G.fiberFunctor I.Y).map bPBCat := by
          have hnormalize :
              cFx.inv ≫ Sf.map (eU.functor.obj x).iso.hom ≫
                  cGx.hom ≫ (G.fiberFunctor I.Y).map bPBCat =
                Pstd.iso.hom ≫ (G.fiberFunctor I.Y).map bPBCat := by
            simp only [Pstd, pullbackOfFiberProductObj, cFx, cGx, Sf, Iso.trans_hom,
              Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
            rfl
          exact hGnatAssoc.trans hnormalize
        exact hexpandTarget.trans (hmoveTarget.trans (hcancelTarget.trans hsourceTarget)) }
  let ix := fibreOfPullback_pullbackObjIso (J := J) F G I.f x
  let ix' := fibreOfPullback_pullbackObjIso (J := J) F G I.f x'
  let δcat :
      eV.functor.obj
          (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
            x) ⟶
        eV.functor.obj
          (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
            x') :=
    ix.inv ≫ δstd ≫ ix'.hom
  letI : eV.functor.Full := by infer_instance
  let a := eV.functor.preimage δcat
  refine ⟨a, ?_⟩
  refine ⟨?_⟩
  -- Reading the second projection through the fiber-pullback equivalence gives the required
  -- commutative square for the right projection.
  have hmap : eV.functor.map a = δcat := eV.functor.map_preimage δcat
  apply Functor.Fiber.hom_ext
  let rightV : (eV.functor.obj
        (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
          x)).snd =
      (q.fiberFunctor I.Y).obj
        (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
          x) :=
    congrArg (fun H : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber I.Y ⥤
        B.p.Fiber I.Y ↦ H.obj
          (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
            x)) hπ₂V
  let rightV' : (eV.functor.obj
        (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
          x')).snd =
      (q.fiberFunctor I.Y).obj
        (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
          x') :=
    congrArg (fun H : (stackTwoFibreProductSquare (J := J) F G).obj.p.Fiber I.Y ⥤
        B.p.Fiber I.Y ↦ H.obj
          (I.f ^*[canonicalPullbackChoice (stackTwoFibreProductSquare (J := J) F G).obj.p]
            x')) hπ₂V
  have htransport :
      (eV.functor.map a).snd ≫ eqToHom rightV' =
        eqToHom rightV ≫ (q.fiberFunctor I.Y).map a := by
    simpa only [rightV, rightV', Functor.comp_map, Limits.CategoricalPullback.comp_snd] using
      (functorMap_eqToHom_comp_of_functor_eq hπ₂V a)
  have hqmap :
      (q.fiberFunctor I.Y).map a =
        eqToHom rightV.symm ≫ (eV.functor.map a).snd ≫ eqToHom rightV' := by
    calc
      (q.fiberFunctor I.Y).map a = 𝟙 _ ≫ (q.fiberFunctor I.Y).map a := by
        simp only [Category.id_comp]
      _ = (eqToHom rightV.symm ≫ eqToHom rightV) ≫ (q.fiberFunctor I.Y).map a := by
        simp only [eqToHom_trans, eqToHom_refl]
      _ = eqToHom rightV.symm ≫ (eqToHom rightV ≫ (q.fiberFunctor I.Y).map a) := by
        simp only [Category.assoc]
      _ = eqToHom rightV.symm ≫ ((eV.functor.map a).snd ≫ eqToHom rightV') := by
        exact congrArg (fun k ↦ eqToHom rightV.symm ≫ k) htransport.symm
      _ = eqToHom rightV.symm ≫ (eV.functor.map a).snd ≫ eqToHom rightV' := by
        rfl
  let cQ := FibredCategoryMor.pullbackComparison q.toFibredCategoryMor I.f x
  let cQ' := FibredCategoryMor.pullbackComparison q.toFibredCategoryMor I.f x'
  have hδsnd :
      eqToHom rightV.symm ≫ δcat.snd ≫ eqToHom rightV' =
        cQ.inv ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫ cQ'.hom := by
    let rU : ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj
          (eU.functor.obj x).snd =
        ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj ((q.fiberFunctor U).obj x) :=
      congrArg (fun y ↦ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj y) rightU
    let rU' : ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj
          (eU.functor.obj x').snd =
        ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj ((q.fiberFunctor U).obj x') :=
      congrArg (fun y ↦ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).obj y) rightU'
    have hbPBCat :
        bPBCat =
          eqToHom rU ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫
            eqToHom rU'.symm := by
      simp only [bPBCat, bCat, Functor.map_comp, eqToHom_map]
    have hleft :
        eqToHom rightV.symm ≫ (fibreOfPullback_pullbackObjIsoRight
            (J := J) F G I.f x).inv =
          cQ.inv ≫ eqToHom rU.symm := by
      simpa only [fibreOfPullback_pullbackObjIsoRight, q, cQ, rU, rightU, rightV,
        hπ₂U, hπ₂V] using
        (eqToHom_symm_comp_isoTrans_inv rU rightV cQ)
    have hright :
        (fibreOfPullback_pullbackObjIsoRight (J := J) F G I.f x').hom ≫
            eqToHom rightV' =
          eqToHom rU' ≫ cQ'.hom := by
      simpa only [fibreOfPullback_pullbackObjIsoRight, q, cQ', rU', rightU', rightV',
        hπ₂U, hπ₂V] using
        (isoTrans_hom_comp_eqToHom rU' rightV' cQ')
    calc
      eqToHom rightV.symm ≫ δcat.snd ≫ eqToHom rightV' =
          (eqToHom rightV.symm ≫
              (fibreOfPullback_pullbackObjIsoRight (J := J) F G I.f x).inv) ≫
            bPBCat ≫
            ((fibreOfPullback_pullbackObjIsoRight (J := J) F G I.f x').hom ≫
              eqToHom rightV') := by
        simp only [δcat, ix, ix', δstd, Pstd, Pstd',
          Limits.CategoricalPullback.comp_snd, Limits.CategoricalPullback.mkIso_inv_snd,
          Limits.CategoricalPullback.mkIso_hom_snd,
          fibreOfPullback_pullbackObjIso, Category.assoc]
        rfl
      _ = (cQ.inv ≫ eqToHom rU.symm) ≫ bPBCat ≫
            ((fibreOfPullback_pullbackObjIsoRight (J := J) F G I.f x').hom ≫
              eqToHom rightV') := by
        exact congrArg
          (fun k ↦ k ≫ bPBCat ≫
            ((fibreOfPullback_pullbackObjIsoRight (J := J) F G I.f x').hom ≫
              eqToHom rightV'))
          hleft
      _ = (cQ.inv ≫ eqToHom rU.symm) ≫ bPBCat ≫ (eqToHom rU' ≫ cQ'.hom) := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ (cQ.inv ≫ eqToHom rU.symm) ≫ bPBCat ≫ k) hright
      _ = cQ.inv ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫
          cQ'.hom := by
        rw [hbPBCat]
        simpa only [Category.assoc] using
          (comp_eqToHom_symm_comp_conjugated_comp_eqToHom rU rU' cQ.inv
            (((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b) cQ'.hom)
  have hqmap' :
      (q.fiberFunctor I.Y).map a =
        cQ.inv ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫ cQ'.hom := by
    calc
      (q.fiberFunctor I.Y).map a =
          eqToHom rightV.symm ≫ (eV.functor.map a).snd ≫ eqToHom rightV' := hqmap
      _ = eqToHom rightV.symm ≫ δcat.snd ≫ eqToHom rightV' := by
        exact congrArg
          (fun k ↦ eqToHom rightV.symm ≫ k ≫ eqToHom rightV')
          (congrArg (fun k ↦ k.snd) hmap)
      _ = cQ.inv ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫
          cQ'.hom := hδsnd
  have hcancel :
      ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫ cQ'.hom =
        cQ.hom ≫
          (cQ.inv ≫ ((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫ cQ'.hom) := by
    simpa only [Category.assoc] using
      (cQ.hom_inv_id_assoc
        (((canonicalPullbackChoice B.p).pullbackFunctor I.f).map b ≫ cQ'.hom)).symm
  rw [hqmap']
  simpa only [q, cQ, cQ', Category.assoc, Functor.Fiber.fiberInclusion] using
    congrArg (fun k ↦ Functor.Fiber.fiberInclusion.map k) hcancel

/-- Lemma 8.11.5: in a `2`-cartesian square of stacks in groupoids over `(C, J)`,
`X' --G'--> X`, `X' --F'--> Y'`, `Y' --G--> Y`, `X --F--> Y`, if `F` is a gerbe over `Y`,
then `F'` is a gerbe over `Y'`. -/
@[stacks 06P3]
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
  let P : BicategoricalTwoCommutativeSquare F G :=
    { obj := X'
      p := G'
      q := F'
      ψ := α }
  let Q : BicategoricalTwoCommutativeSquare F G :=
    StackInGroupoidsOver.Hom.stackTwoFibreProductSquare (J := J) F G
  letI : Bicategory.IsFinal P := hcart
  have hQ : Bicategory.IsFinal Q := by
    exact StackInGroupoidsOver.Hom.stackTwoFibreProductSquare_isTwoFibreProduct
      (J := J) F G
  letI : Bicategory.IsFinal Q := hQ
  let u : Q ⟶ P := ⊤_ (Q ⟶ P)
  have hu : u.hom.IsEquivalenceOverBase :=
    StackInGroupoidsOver.Hom.apexMap_isEquivalenceOverBase_of_final_squares
      (J := J) P Q hcart hQ u
  have hQgerbe : StackInGroupoidsOver.Hom.IsGerbeOver Q.q := by
    -- The canonical pullback right projection is a gerbe by the two local conditions proved above.
    rw [StackInGroupoidsOver.Hom.isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms]
    exact
      ⟨StackInGroupoidsOver.Hom.twoFibreProductRightProjection_locallyEssentiallySurjectiveOnObjects
          (J := J) F G hF.locallyEssentiallySurjectiveOnObjects,
        StackInGroupoidsOver.Hom.twoFibreProductRightProjection_locallyLiftsFiberMorphisms
          (J := J) F G hF.locallyLiftsFiberMorphisms⟩
  -- The comparison map from the canonical final square to the given final square is an
  -- equivalence on sources, so whole-gerbe transport gives the requested right leg.
  exact
    StackInGroupoidsOver.Hom.isGerbeOver_of_source_equivalence_comp_hom
      (J := J) u.hom F' Q.q hu u.right hQgerbe

end Hom

end StackInGroupoidsOver

end

end CategoryTheory
