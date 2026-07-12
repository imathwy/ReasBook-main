import StacksProject_2024.Chap22.Lemma_22_4_2
import StacksProject_2024.Chap22.DGModuleModel
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

universe u v

noncomputable section

section

variable {A : Type u} [Ring A]

/- Source/core/bridge triage:
- `source-facing`: Lemma 22.5.4 that `K(Mod_(A,d))` has arbitrary direct sums and products;
- `core/canonical`: the canonical categorical owners `HasCoproducts` and `HasProducts` on
  `HomotopyCategory (ModuleCat A) (up ℤ)`;
- `bridge/view`: the Chapter 22 owner `ModuleCat.KDGMod A` for this canonical homotopy-category
  specialization.
-/

/- Lemma 22.5.4
In the current Chapter 22 Lean model, differential graded `A`-modules are represented by
cochain complexes of `A`-modules, and `K(Mod_(A,d))` is their homotopy category
`ModuleCat.KDGMod A`.
The source lemma is therefore formalized directly at the canonical owners
`HasCoproducts (ModuleCat.KDGMod A)` and `HasProducts (ModuleCat.KDGMod A)`.
-/

/-- Helper for Lemma 22.5.4: a homotopy `f ∼ 0` recovers `f` as the chain map built from the
underlying homotopy data. -/
lemma nullHomotopicMap_eq_of_homotopy {C D : ModuleCat.DGMod A} {f : C ⟶ D}
    (h : Homotopy f 0) :
    Homotopy.nullHomotopicMap h.hom = f := by
  -- The degreewise formula of `nullHomotopicMap` is exactly the homotopy relation.
  apply HomologicalComplex.hom_ext
  intro i
  simpa [Homotopy.nullHomotopicMap] using (h.comm i).symm

/-- Helper for Lemma 22.5.4: every family in `ModuleCat.KDGMod A` is naturally isomorphic to a
family lying in the essential image of the quotient functor `Q`. -/
theorem representativeFamilyNonempty {J : Type v} (X : J → ModuleCat.KDGMod A) :
    Nonempty (Σ M : J → ModuleCat.DGMod A,
      Discrete.functor
          (fun j => (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (M j)) ≅
        Discrete.functor X) := by
  classical
  choose M hM using fun j => HomotopyCategory.quotient_obj_surjective (X j)
  have hObj :
      ∀ j : Discrete J,
        (Discrete.functor
            (fun j => (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (M j))).obj j =
          (Discrete.functor X).obj j := fun j =>
      hM j.as
  exact ⟨⟨M, Discrete.natIso (fun j => eqToIso (hObj j))⟩⟩

/-- Helper for Lemma 22.5.4: postcomposition by a DG-module map acts additively on fixed-degree
Hom-complex cochains. -/
private theorem homComplexPostcomp_map_add
    {K L M : ModuleCat.DGMod A}
    (σ : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain K L n) :
    (z + z').comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) =
      z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) +
        z'.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n) := by
  -- Proof comment: composition in the Hom complex is bilinear, so fixed-degree postcomposition
  -- preserves addition.
  simpa only using
    (CochainComplex.HomComplex.Cochain.add_comp
      (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n) z z'
      (CochainComplex.HomComplex.Cochain.ofHom σ))

/-- Helper for Lemma 22.5.4: postcomposition by a DG-module map gives an additive map on a fixed
Hom-complex degree. -/
private noncomputable def homComplexPostcompAddMonoidHom
    {K L M : ModuleCat.DGMod A}
    (σ : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K L n →+
      CochainComplex.HomComplex.Cochain K M n :=
  { toFun := fun z ↦ z.comp (CochainComplex.HomComplex.Cochain.ofHom σ) (add_zero n)
    map_zero' := by
      -- Proof comment: postcomposing the zero cochain is still zero.
      simpa only using
        (CochainComplex.HomComplex.Cochain.zero_comp
          (n₁ := n) (n₂ := 0) (n₁₂ := n) (h := add_zero n)
          (CochainComplex.HomComplex.Cochain.ofHom σ))
    map_add' := homComplexPostcomp_map_add σ n }

/-- Helper for Lemma 22.5.4: postcomposition commutes with the Hom-complex differential. -/
private theorem homComplexPostcomp_comm
    {K L M : ModuleCat.DGMod A}
    (σ : L ⟶ M) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom σ i) ≫
        (CochainComplex.HomComplex K M).d i j =
      (CochainComplex.HomComplex K L).d i j ≫
        AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom σ j) := by
  -- Proof comment: this is the standard naturality of the Hom-complex differential under
  -- postcomposition.
  ext z
  simpa only using
    (CochainComplex.HomComplex.δ_comp_ofHom (n := i) z σ j)

/-- Helper for Lemma 22.5.4: postcomposition by a DG-module map defines a chain map on Hom
complexes. -/
private noncomputable def homComplexPostcomp
    {K L M : ModuleCat.DGMod A}
    (σ : L ⟶ M) :
    CochainComplex.HomComplex K L ⟶ CochainComplex.HomComplex K M :=
  { f := fun n ↦ AddCommGrpCat.ofHom (homComplexPostcompAddMonoidHom σ n)
    comm' := homComplexPostcomp_comm σ }

/-- Helper for Lemma 22.5.4: precomposition by a DG-module map acts additively on fixed-degree
Hom-complex cochains. -/
private theorem homComplexPrecomp_map_add
    {L M I : ModuleCat.DGMod A} (f : L ⟶ M) (n : ℤ)
    (z z' : CochainComplex.HomComplex.Cochain M I n) :
    (CochainComplex.HomComplex.Cochain.ofHom f).comp (z + z') (zero_add n) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n) +
        (CochainComplex.HomComplex.Cochain.ofHom f).comp z' (zero_add n) := by
  -- Proof comment: precomposition is also bilinear because composition in the ambient category is
  -- bilinear.
  ext p q hpq
  simp

/-- Helper for Lemma 22.5.4: precomposition by a DG-module map gives an additive map on a fixed
Hom-complex degree. -/
private noncomputable def homComplexPrecompAddMonoidHom
    {L M I : ModuleCat.DGMod A} (f : L ⟶ M) (n : ℤ) :
    CochainComplex.HomComplex.Cochain M I n →+
      CochainComplex.HomComplex.Cochain L I n where
  toFun := fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n)
  map_zero' := by
    -- Proof comment: precomposing the zero cochain is still zero.
    ext p q hpq
    simp
  map_add' := homComplexPrecomp_map_add f n

/-- Helper for Lemma 22.5.4: precomposition commutes with the Hom-complex differential. -/
private theorem homComplexPrecomp_comm
    {L M I : ModuleCat.DGMod A} (f : L ⟶ M) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) i) ≫
        (CochainComplex.HomComplex L I).d i j =
      (CochainComplex.HomComplex M I).d i j ≫
        AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) j) := by
  -- Proof comment: this is the naturality of the Hom-complex differential under precomposition.
  ext z
  change
    CochainComplex.HomComplex.δ i j
        ((CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add i)) =
      (CochainComplex.HomComplex.Cochain.ofHom f).comp
        (CochainComplex.HomComplex.δ i j z) (zero_add j)
  simpa only using
    (CochainComplex.HomComplex.δ_ofHom_comp (n := i) f z j)

/-- Helper for Lemma 22.5.4: precomposition by a DG-module map defines a chain map on Hom
complexes. -/
private noncomputable def homComplexPrecomp
    {L M I : ModuleCat.DGMod A} (f : L ⟶ M) :
    CochainComplex.HomComplex M I ⟶ CochainComplex.HomComplex L I where
  f n := AddCommGrpCat.ofHom (homComplexPrecompAddMonoidHom (f := f) (I := I) n)
  comm' := homComplexPrecomp_comm (f := f)

/-- Helper for Lemma 22.5.4: the evaluated coproduct cofan is colimiting after testing by
`yoneda`. -/
private theorem dgModuleCoproductDegreeIsColimit_nonempty {J : Type v}
    (M : J → ModuleCat.DGMod A) (n : ℤ) :
    Nonempty (IsColimit (Cofan.mk ((∐ M).X n) fun j ↦ (Sigma.ι M j).f n)) := by
  -- Proof comment: evaluation computes coproducts degreewise, so the canonical cofan in degree
  -- `n` is the preserved coproduct owner for `HomologicalComplex.eval`.
  refine ⟨?_⟩
  simpa using
    (CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat A) (up ℤ) n) M)

/-- Helper for Lemma 22.5.4: evaluating the coproduct DG-module in a fixed degree yields the
chosen coproduct in `ModuleCat A`. -/
private noncomputable abbrev dgModuleCoproductDegreeIsColimit {J : Type v}
    (M : J → ModuleCat.DGMod A) (n : ℤ) :
    IsColimit (Cofan.mk ((∐ M).X n) fun j ↦ (Sigma.ι M j).f n) :=
  Classical.choice (dgModuleCoproductDegreeIsColimit_nonempty M n)

/-- Helper for Lemma 22.5.4: null-homotopies on all coproduct components assemble to a
null-homotopy of the induced map out of the coproduct. -/
lemma homotopicZeroOfCoproductComponents {J : Type v} (M : J → ModuleCat.DGMod A)
    {N : ModuleCat.DGMod A} {f : (∐ M) ⟶ N}
    (h : ∀ j, Nonempty (Homotopy (Sigma.ι M j ≫ f) 0)) :
    Nonempty (Homotopy f 0) := by
  classical
  let αt : ∀ j, CochainComplex.HomComplex.Cochain (M j) N (-1) := fun j ↦
    ((CochainComplex.HomComplex.Cochain.equivHomotopy (Sigma.ι M j ≫ f) 0)
      (Classical.choice (h j))).1
  have hαt :
      ∀ j,
        CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j ≫ f) =
          CochainComplex.HomComplex.δ (-1) 0 (αt j) := by
    intro j
    -- Proof comment: each chosen component null-homotopy identifies the corresponding map with a
    -- degree `-1` coboundary.
    simpa only [αt, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero] using
      ((CochainComplex.HomComplex.Cochain.equivHomotopy (Sigma.ι M j ≫ f) 0)
        (Classical.choice (h j))).2
  let α : CochainComplex.HomComplex.Cochain (∐ M) N (-1) :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
      (dgModuleCoproductDegreeIsColimit M p).desc
        (Cofan.mk (N.X q) fun j ↦ (αt j).v p q hpq)
  have hα_fac (j : J) :
      (CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp α (zero_add (-1)) = αt j := by
    ext p q hpq x
    -- Proof comment: the assembled cochain has the prescribed value on every coproduct summand.
    simpa [α] using
      congrArg (fun k ↦ k x)
        (Cofan.IsColimit.fac (dgModuleCoproductDegreeIsColimit M p)
          (fun t ↦ (αt t).v p q hpq) j)
  have hα_eq :
      CochainComplex.HomComplex.Cochain.ofHom f =
        CochainComplex.HomComplex.δ (-1) 0 α := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    -- Proof comment: two maps out of a coproduct agree once they agree after every inclusion.
    apply Cofan.IsColimit.hom_ext (dgModuleCoproductDegreeIsColimit M p)
    intro j
    have hcomp :
        (CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp
            (CochainComplex.HomComplex.Cochain.ofHom f) (zero_add 0) =
          (CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp
            (CochainComplex.HomComplex.δ (-1) 0 α) (zero_add 0) := by
      calc
        (CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp
            (CochainComplex.HomComplex.Cochain.ofHom f) (zero_add 0) =
          CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j ≫ f) := by
            simpa only using
              (CochainComplex.HomComplex.Cochain.ofHom_comp (Sigma.ι M j) f).symm
        _ = CochainComplex.HomComplex.δ (-1) 0 (αt j) := hαt j
        _ = CochainComplex.HomComplex.δ (-1) 0
              ((CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp α
                (zero_add (-1))) := by
              rw [hα_fac j]
        _ = (CochainComplex.HomComplex.Cochain.ofHom (Sigma.ι M j)).comp
              (CochainComplex.HomComplex.δ (-1) 0 α) (zero_add 0) := by
              simpa only using
                (CochainComplex.HomComplex.δ_ofHom_comp (n := -1) (Sigma.ι M j) α 0)
    have hcomp_v :=
      CochainComplex.HomComplex.Cochain.congr_v hcomp p p (add_zero p)
    simpa using hcomp_v
  -- Proof comment: the assembled degree `-1` cochain is exactly the data of a null-homotopy.
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm ?_⟩
  refine ⟨α, ?_⟩
  rw [hα_eq, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

/-- Helper for Lemma 22.5.4: every component isomorphism in a represented family cancels with its
inverse on the right. This is the basic transport identity needed when rewriting discrete-family
legs. -/
lemma representativeFamilyComponent_hom_inv_id {J : Type v} {X : J → ModuleCat.KDGMod A}
    {M : J → ModuleCat.DGMod A}
    (e :
      Discrete.functor
          (fun j => (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (M j)) ≅
        Discrete.functor X)
    (j : J) :
    (e.app (Discrete.mk j)).hom ≫ (e.app (Discrete.mk j)).inv =
      𝟙 ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (M j)) := by
  -- Each component of the discrete-family isomorphism is itself an isomorphism in `KDGMod`.
  simpa using Iso.hom_inv_id (e.app (Discrete.mk j))

/-- Helper for Lemma 22.5.4: the evaluated product fan is limiting after testing by `coyoneda`.
-/
private theorem dgModuleProductDegreeIsLimit_nonempty {J : Type v}
    (M : J → ModuleCat.DGMod A) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((∏ᶜ M).X n) fun j ↦ (Pi.π M j).f n)) := by
  -- Proof comment: evaluation computes products degreewise, so the canonical fan in degree `n`
  -- is the preserved product owner for `HomologicalComplex.eval`.
  refine ⟨?_⟩
  simpa using
    (CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval (ModuleCat A) (up ℤ) n) M)

/-- Helper for Lemma 22.5.4: evaluating the product DG-module in a fixed degree yields the chosen
product in `ModuleCat A`. -/
private noncomputable abbrev dgModuleProductDegreeIsLimit {J : Type v}
    (M : J → ModuleCat.DGMod A) (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ M).X n) fun j ↦ (Pi.π M j).f n) :=
  Classical.choice (dgModuleProductDegreeIsLimit_nonempty M n)

/-- Helper for Lemma 22.5.4: null-homotopies on all product components assemble to a
null-homotopy of the induced map into the product. -/
lemma homotopicZeroOfProductComponents {J : Type v} (M : J → ModuleCat.DGMod A)
    {N : ModuleCat.DGMod A} {f : N ⟶ ∏ᶜ M}
    (h : ∀ j, Nonempty (Homotopy (f ≫ Pi.π M j) 0)) :
    Nonempty (Homotopy f 0) := by
  classical
  let αt : ∀ j, CochainComplex.HomComplex.Cochain N (M j) (-1) := fun j ↦
    ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ Pi.π M j) 0)
      (Classical.choice (h j))).1
  have hαt :
      ∀ j,
        CochainComplex.HomComplex.Cochain.ofHom (f ≫ Pi.π M j) =
          CochainComplex.HomComplex.δ (-1) 0 (αt j) := by
    intro j
    -- Proof comment: each chosen factorwise null-homotopy identifies the corresponding
    -- projection with a degree `-1` coboundary.
    simpa only [αt, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero] using
      ((CochainComplex.HomComplex.Cochain.equivHomotopy (f ≫ Pi.π M j) 0)
        (Classical.choice (h j))).2
  let α : CochainComplex.HomComplex.Cochain N (∏ᶜ M) (-1) :=
    CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
      (dgModuleProductDegreeIsLimit M q).lift
        (Fan.mk (N.X p) fun j ↦ (αt j).v p q hpq)
  have hα_fac (j : J) :
      α.comp (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j)) (add_zero (-1)) = αt j := by
    ext p q hpq x
    -- Proof comment: the assembled cochain has the prescribed value on every product factor.
    simpa [α] using
      congrArg (fun k ↦ k x)
        (Fan.IsLimit.fac (dgModuleProductDegreeIsLimit M q)
          (fun t ↦ (αt t).v p q hpq) j)
  have hα_eq :
      CochainComplex.HomComplex.Cochain.ofHom f =
        CochainComplex.HomComplex.δ (-1) 0 α := by
    apply CochainComplex.HomComplex.Cochain.ext₀
    intro p
    -- Proof comment: two maps into a product agree once they agree after every projection.
    apply Fan.IsLimit.hom_ext (dgModuleProductDegreeIsLimit M p)
    intro j
    have hcomp :
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j)) (add_zero 0) =
          (CochainComplex.HomComplex.δ (-1) 0 α).comp
            (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j)) (add_zero 0) := by
      calc
        (CochainComplex.HomComplex.Cochain.ofHom f).comp
            (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j)) (add_zero 0) =
          CochainComplex.HomComplex.Cochain.ofHom (f ≫ Pi.π M j) := by
            simpa only using
              (CochainComplex.HomComplex.Cochain.ofHom_comp f (Pi.π M j)).symm
        _ = CochainComplex.HomComplex.δ (-1) 0 (αt j) := hαt j
        _ = CochainComplex.HomComplex.δ (-1) 0
              (α.comp (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j))
                (add_zero (-1))) := by
              rw [hα_fac j]
        _ = (CochainComplex.HomComplex.δ (-1) 0 α).comp
              (CochainComplex.HomComplex.Cochain.ofHom (Pi.π M j)) (add_zero 0) := by
              symm
              simpa only using
                (CochainComplex.HomComplex.δ_comp_ofHom (n := -1) α (Pi.π M j) 0).symm
    have hcomp_v :=
      CochainComplex.HomComplex.Cochain.congr_v hcomp p p (add_zero p)
    simpa using hcomp_v
  -- Proof comment: the assembled degree `-1` cochain is exactly the data of a null-homotopy.
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy f 0).symm ?_⟩
  refine ⟨α, ?_⟩
  rw [hα_eq, CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]

/-- Helper for Lemma 22.5.4: the quotient-image coproduct cofan of a DG-module family is
colimiting in the homotopy category. -/
private theorem quotientCofanIsColimit_nonempty {J : Type v} (M : J → ModuleCat.DGMod A) :
    Nonempty (
    IsColimit
      (Cofan.mk
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (∐ M))
        (fun j ↦ (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map (Sigma.ι M j)))) := by
  classical
  let Q := HomotopyCategory.quotient (ModuleCat A) (up ℤ)
  -- Route correction: the unstable representative-family route is replaced by one fixed
  -- `Q.objPreimage` spelling, and the coproduct mediator is compared after composing with the
  -- chosen transport isomorphism.
  refine ⟨mkCofanColimit
    (Cofan.mk (Q.obj (∐ M)) fun j ↦ Q.map (Sigma.ι M j))
    (fun s ↦ ?_)
    ?_
    ?_⟩
  · let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, M j ⟶ Q.objPreimage s.pt := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose
    have hu' : ∀ j, Q.map (u' j) = s.ι.app ⟨j⟩ ≫ e.inv := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose_spec
    -- Proof comment: lift each coproduct leg to the chosen representative of `s.pt`, assemble
    -- them by the coproduct universal property, then transport back to `s.pt`.
    exact Q.map (Sigma.desc u') ≫ e.hom
  · intro s j
    let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, M j ⟶ Q.objPreimage s.pt := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose
    have hu' : ∀ j, Q.map (u' j) = s.ι.app ⟨j⟩ ≫ e.inv := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose_spec
    have hcancel :
        (s.ι.app ⟨j⟩ ≫ e.inv) ≫ e.hom = s.ι.app ⟨j⟩ := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ s.ι.app ⟨j⟩ ≫ k) e.inv_hom_id
    have hleg :
        Q.map (u' j) ≫ e.hom = s.ι.app ⟨j⟩ := by
      rw [hu' j]
      exact hcancel
    -- Proof comment: the assembled lift has the prescribed coproduct inclusions by
    -- `Sigma.ι_desc`, and the final transport cancels by `e.inv ≫ e.hom = 𝟙`.
    calc
      Q.map (Sigma.ι M j) ≫ (Q.map (Sigma.desc u') ≫ e.hom) =
        (Q.map (Sigma.ι M j) ≫ Q.map (Sigma.desc u')) ≫ e.hom := by
          simp [Category.assoc]
      _ = Q.map (Sigma.ι M j ≫ Sigma.desc u') ≫ e.hom := by
          simp [Functor.map_comp, Category.assoc]
      _ = Q.map (u' j) ≫ e.hom := by
          rw [Sigma.ι_desc]
      _ = s.ι.app ⟨j⟩ := hleg
  · intro s m hm
    let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, M j ⟶ Q.objPreimage s.pt := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose
    have hu' : ∀ j, Q.map (u' j) = s.ι.app ⟨j⟩ ≫ e.inv := fun j ↦
      (Q.map_surjective (s.ι.app ⟨j⟩ ≫ e.inv)).choose_spec
    obtain ⟨m', hm'⟩ := Q.map_surjective (m ≫ e.inv)
    have hfactor :
        ∀ j, Nonempty (Homotopy (Sigma.ι M j ≫ (m' - Sigma.desc u')) 0) := by
      intro j
      -- Proof comment: equality after quotienting forces each coproduct component of the
      -- source-side difference to be null-homotopic.
      apply (HomotopyCategory.quotient_map_eq_zero_iff
        (Sigma.ι M j ≫ (m' - Sigma.desc u'))).1
      rw [Functor.map_comp, Functor.map_sub, Preadditive.comp_sub, hm']
      have hmj :
          Q.map (Sigma.ι M j) ≫ (m ≫ e.inv) = s.ι.app ⟨j⟩ ≫ e.inv := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e.inv) (hm j)
      have hdescj :
          Q.map (Sigma.ι M j) ≫ Q.map (Sigma.desc u') = s.ι.app ⟨j⟩ ≫ e.inv := by
        calc
          Q.map (Sigma.ι M j) ≫ Q.map (Sigma.desc u') =
            Q.map (Sigma.ι M j ≫ Sigma.desc u') := by
              simp [Functor.map_comp]
          _ = Q.map (u' j) := by
              rw [Sigma.ι_desc]
          _ = s.ι.app ⟨j⟩ ≫ e.inv := hu' j
      exact sub_eq_zero.mpr (hmj.trans hdescj.symm)
    have hnull :
        Nonempty (Homotopy (m' - Sigma.desc u') 0) :=
      homotopicZeroOfCoproductComponents M hfactor
    have hzero : Q.map (m' - Sigma.desc u') = 0 :=
      (HomotopyCategory.quotient_map_eq_zero_iff (m' - Sigma.desc u')).2 hnull
    have hm_eq : Q.map m' = Q.map (Sigma.desc u') := by
      apply sub_eq_zero.mp
      simpa using hzero
    have hm_eq' : m ≫ e.inv = Q.map (Sigma.desc u') := by
      simpa [hm'] using hm_eq
    -- Proof comment: compare inside the chosen representative of `s.pt`, then postcompose with
    -- `e.hom` to recover the original morphism `m`.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e.hom) hm_eq'

/-- Helper for Lemma 22.5.4: the quotient-image product fan of a DG-module family is limiting in
the homotopy category. -/
private theorem quotientFanIsLimit_nonempty {J : Type v} (M : J → ModuleCat.DGMod A) :
    Nonempty (
    IsLimit
      (Fan.mk
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (∏ᶜ M))
        (fun j ↦ (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map (Pi.π M j)))) := by
  classical
  let Q := HomotopyCategory.quotient (ModuleCat A) (up ℤ)
  refine ⟨mkFanLimit
    (Fan.mk (Q.obj (∏ᶜ M)) fun j ↦ Q.map (Pi.π M j))
    (fun s ↦ ?_)
    ?_
    ?_⟩
  · let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, Q.objPreimage s.pt ⟶ M j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose
    have hu' : ∀ j, Q.map (u' j) = e.hom ≫ s.proj j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose_spec
    -- Proof comment: lift the cone legs to the chosen representative of `s.pt`, assemble them by
    -- the product universal property, then transport back.
    exact e.inv ≫ Q.map (Pi.lift u')
  · intro s j
    let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, Q.objPreimage s.pt ⟶ M j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose
    have hu' : ∀ j, Q.map (u' j) = e.hom ≫ s.proj j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose_spec
    -- Proof comment: the assembled lift has the prescribed projections by the defining product
    -- equation and then cancels the transport isomorphism.
    calc
      (e.inv ≫ Q.map (Pi.lift u')) ≫ Q.map (Pi.π M j) =
        e.inv ≫ (Q.map (Pi.lift u') ≫ Q.map (Pi.π M j)) := by
          simp [Category.assoc]
      _ = e.inv ≫ Q.map (Pi.lift u' ≫ Pi.π M j) := by
          simp [Functor.map_comp]
      _ = e.inv ≫ Q.map (u' j) := by
          rw [Pi.lift_π]
      _ = e.inv ≫ (e.hom ≫ s.proj j) := by
          rw [hu' j]
      _ = s.proj j := by
          simpa [Category.assoc] using
            Iso.inv_hom_id_assoc e (s.proj j)
  · intro s m hm
    let e := Q.objObjPreimageIso s.pt
    let u' : ∀ j, Q.objPreimage s.pt ⟶ M j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose
    have hu' : ∀ j, Q.map (u' j) = e.hom ≫ s.proj j := fun j ↦
      (Q.map_surjective (e.hom ≫ s.proj j)).choose_spec
    obtain ⟨m', hm'⟩ := Q.map_surjective (e.hom ≫ m)
    have hfactor :
        ∀ j, Nonempty (Homotopy ((m' - Pi.lift u') ≫ Pi.π M j) 0) := by
      intro j
      -- Proof comment: equality of the projections in the quotient means each factor of the
      -- source-side difference is null-homotopic.
      apply (HomotopyCategory.quotient_map_eq_zero_iff
        ((m' - Pi.lift u') ≫ Pi.π M j)).1
      rw [Functor.map_comp, Functor.map_sub, Preadditive.sub_comp, hm']
      have hmj :
          (e.hom ≫ m) ≫ Q.map (Pi.π M j) = e.hom ≫ s.proj j := by
        simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) (hm j)
      have hliftj :
          Q.map (Pi.lift u') ≫ Q.map (Pi.π M j) = e.hom ≫ s.proj j := by
        calc
          Q.map (Pi.lift u') ≫ Q.map (Pi.π M j) =
            Q.map (Pi.lift u' ≫ Pi.π M j) := by
              simp [Functor.map_comp]
          _ = Q.map (u' j) := by
              rw [Pi.lift_π]
          _ = e.hom ≫ s.proj j := hu' j
      exact sub_eq_zero.mpr (hmj.trans hliftj.symm)
    have hnull :
        Nonempty (Homotopy (m' - Pi.lift u') 0) :=
      homotopicZeroOfProductComponents M hfactor
    have hzero : Q.map (m' - Pi.lift u') = 0 :=
      (HomotopyCategory.quotient_map_eq_zero_iff (m' - Pi.lift u')).2 hnull
    have hm_eq : Q.map m' = Q.map (Pi.lift u') := by
      apply sub_eq_zero.mp
      simpa using hzero
    have hm_eq' : e.hom ≫ m = Q.map (Pi.lift u') := by
      simpa [hm'] using hm_eq
    -- Proof comment: compare inside the chosen representative of `s.pt`, then transport back.
    simpa [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) hm_eq'

/-- Helper for Lemma 22.5.4: the represented-family quotient coproduct cofan is the chosen
colimit owner used in the final coproduct instance. -/
private noncomputable abbrev quotientCofanIsColimit {J : Type v} (M : J → ModuleCat.DGMod A) :
    IsColimit
      (Cofan.mk
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (∐ M))
        (fun j ↦ (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map (Sigma.ι M j))) :=
  Classical.choice (quotientCofanIsColimit_nonempty M)

/-- Helper for Lemma 22.5.4: the represented-family quotient product fan is the chosen limit owner
used in the final product instance. -/
private noncomputable abbrev quotientFanIsLimit {J : Type v} (M : J → ModuleCat.DGMod A) :
    IsLimit
      (Fan.mk
        ((HomotopyCategory.quotient (ModuleCat A) (up ℤ)).obj (∏ᶜ M))
        (fun j ↦ (HomotopyCategory.quotient (ModuleCat A) (up ℤ)).map (Pi.π M j))) :=
  Classical.choice (quotientFanIsLimit_nonempty M)

/-- Helper for Lemma 22.5.4: `J`-indexed coproducts in `K(Mod_(A,d))` are obtained by taking
the quotient-image coproduct of chosen DG-module representatives and transporting it along the
canonical `objPreimage` isomorphisms. -/
instance homotopyCategoryDgModulesHasCoproductsOfShape (J : Type v) :
    HasCoproductsOfShape J (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) where
  has_colimit F := by
    let Q :
        CochainComplex (ModuleCat.{max u v} A) ℤ ⥤
          HomotopyCategory (ModuleCat.{max u v} A) (up ℤ) :=
      HomotopyCategory.quotient (ModuleCat.{max u v} A) (up ℤ)
    let X : J → HomotopyCategory (ModuleCat.{max u v} A) (up ℤ) := fun j ↦ F.obj ⟨j⟩
    let K : J → CochainComplex (ModuleCat.{max u v} A) ℤ := fun j ↦ Q.objPreimage (X j)
    let _ : HasColimitsOfShape (Discrete J) (CochainComplex (ModuleCat.{max u v} A) ℤ) :=
      inferInstance
    let eK : ∀ j, Q.obj (K j) ≅ X j := fun j ↦ Q.objObjPreimageIso (X j)
    let e : Discrete.functor (fun j ↦ Q.obj (K j)) ≅ Discrete.functor X :=
      Discrete.natIso fun j : Discrete J ↦ eK j.as
    let eF : F ≅ Discrete.functor X := Discrete.natIso fun j : Discrete J ↦ Iso.refl _
    -- Route correction: package the colimit directly from the represented family instead of
    -- asking typeclass search to synthesize an anonymous `HasCoproduct`.
    have hX :
        IsColimit (Cofan.mk (Q.obj (∐ K)) fun j ↦ (eK j).inv ≫ Q.map (Sigma.ι K j)) := by
      -- Proof comment: transport the represented-family quotient coproduct owner exactly once
      -- along the canonical componentwise `objPreimage` isomorphisms.
      exact (IsColimit.precomposeInvEquiv e
        (Cofan.mk (Q.obj (∐ K)) fun j ↦ Q.map (Sigma.ι K j))).symm
        (quotientCofanIsColimit K)
    refine HasColimit.mk
      ⟨(Cocone.precompose eF.hom).obj
          (Cofan.mk (Q.obj (∐ K)) fun j ↦ (eK j).inv ≫ Q.map (Sigma.ι K j)),
        ?_⟩
    -- Proof comment: the discrete-family transport finishes the packaging from `X` to the
    -- original diagram `F`.
    exact (IsColimit.precomposeHomEquiv eF _).symm hX

/-- Helper for Lemma 22.5.4: `J`-indexed products in `K(Mod_(A,d))` are obtained by taking the
quotient-image product of chosen DG-module representatives and transporting it along the
canonical `objPreimage` isomorphisms. -/
instance homotopyCategoryDgModulesHasProductsOfShape (J : Type v) :
    HasProductsOfShape J (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) where
  has_limit F := by
    let Q :
        CochainComplex (ModuleCat.{max u v} A) ℤ ⥤
          HomotopyCategory (ModuleCat.{max u v} A) (up ℤ) :=
      HomotopyCategory.quotient (ModuleCat.{max u v} A) (up ℤ)
    let X : J → HomotopyCategory (ModuleCat.{max u v} A) (up ℤ) := fun j ↦ F.obj ⟨j⟩
    let K : J → CochainComplex (ModuleCat.{max u v} A) ℤ := fun j ↦ Q.objPreimage (X j)
    let _ : HasLimitsOfShape (Discrete J) (CochainComplex (ModuleCat.{max u v} A) ℤ) :=
      inferInstance
    let eK : ∀ j, Q.obj (K j) ≅ X j := fun j ↦ Q.objObjPreimageIso (X j)
    let e : Discrete.functor (fun j ↦ Q.obj (K j)) ≅ Discrete.functor X :=
      Discrete.natIso fun j : Discrete J ↦ eK j.as
    let eF : F ≅ Discrete.functor X := Discrete.natIso fun j : Discrete J ↦ Iso.refl _
    -- Route correction: keep the representative family in one explicit spelling and package the
    -- product by transport, mirroring the completed represented-family owner.
    have hX :
        IsLimit (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j) ≫ (eK j).hom) := by
      -- Proof comment: transport the represented-family quotient product owner exactly once along
      -- the canonical `objPreimage` isomorphisms.
      exact (IsLimit.postcomposeHomEquiv e
        (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j))).symm
        (quotientFanIsLimit K)
    refine HasLimit.mk
      ⟨(Cone.postcompose eF.inv).obj
          (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j) ≫ (eK j).hom),
        ?_⟩
    -- Proof comment: the discrete-family transport finishes the packaging from `X` to the
    -- original diagram `F`.
    exact (IsLimit.postcomposeHomEquiv eF.symm _).symm hX

/-- Lemma 22.5.4, coproduct half: the homotopy category `K(Mod_(A,d))` has arbitrary direct sums.
This is the canonical coproduct owner used by the chapter model. -/
@[stacks 09JR]
instance homotopyCategoryDgModulesHasCoproducts :
    HasCoproducts.{v} (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) := by
  change ∀ J : Type v,
      HasColimitsOfShape (Discrete J) (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ))
  intro J
  change HasCoproductsOfShape J (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ))
  exact homotopyCategoryDgModulesHasCoproductsOfShape (A := A) (J := J)

/-- Products half of Lemma 22.5.4: the homotopy category `K(Mod_(A,d))` has arbitrary products.
On the
canonical Lean owner side, this is the product structure
`HasProducts (ModuleCat.KDGMod A)`. -/
@[stacks 09JR]
instance homotopyCategoryDgModulesHasProducts :
    HasProducts.{v} (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) := by
  change ∀ J : Type v,
      HasLimitsOfShape (Discrete J) (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ))
  intro J
  change HasProductsOfShape J (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ))
  exact homotopyCategoryDgModulesHasProductsOfShape (A := A) (J := J)

/-- Corollary for Lemma 22.5.4: the canonical Lean model realizes the textbook statement by the
two instance declarations above, giving both
`HasCoproducts (HomotopyCategory (ModuleCat A) (up ℤ))` and
`HasProducts (HomotopyCategory (ModuleCat A) (up ℤ))`. -/
theorem homotopyCategoryDgModulesHasProductsAndCoproducts :
    HasCoproducts.{v} (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) ∧
      HasProducts.{v} (HomotopyCategory (ModuleCat.{max u v} A) (up ℤ)) := by
  -- Proof comment: the two source assertions are exactly the canonical instance owners proved
  -- just above.
  constructor <;> infer_instance

end
