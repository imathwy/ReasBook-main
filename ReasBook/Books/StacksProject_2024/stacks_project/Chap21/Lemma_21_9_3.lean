import StacksProject_2024.Chap21.Lemma_21_9_4
import StacksProject_2024.Chap20.«20_9_0_1»
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe w u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C]
variable [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Limits.HasProducts AddCommGrpCat.{u}]
variable {ι : Type w}

/- Domain-style sampling for Lemma 21.9.3:
- primary domain: Čech complexes of additive presheaves and the canonical `Hom(K,-)` cochain
  functor attached to a chain complex of free-abelian representables;
- sampled owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `CategoryTheory.freeAbelianCechChainComplex`,
  `CategoryTheory.preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- best owner abstraction: the source-facing comparison is between the canonical Čech cochain owner
  `cechComplexFunctor U` and the canonical Hom-complex owner obtained from the chain complex
  `freeAbelianCechChainComplex U`.

Source/core/bridge triage:
- `source-facing`: the comparison between the Hom complex of the free-abelian Čech cover complex
  and the usual Čech complex of an abelian presheaf;
- `core/canonical`: `cechComplexFunctor U`, `freeAbelianCechChainComplex U`,
  `preadditiveCoyoneda.mapHomologicalComplex`, and `HomologicalComplex.asFunctor`;
- `bridge/view`: the degreewise comparison maps obtained from the free-abelian/Yoneda adjunction.

Primitive data versus derived API:
- primitive data: the family `U : ι → C`;
- derived API: the cover chain complex, the Hom-complex functor `cechCoverHomFunctor U`, and the
  degreewise component comparisons. -/

/-- The canonical cochain-complex functor `Hom(K(U)_•,-)` attached to the free-abelian Čech
cover chain complex of the family `U`. -/
abbrev cechCoverHomFunctor (U : ι → C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (freeAbelianCechChainComplex U).op).asFunctor)

/-- Helper for Lemma 21.9.3: the free-abelian Yoneda copresheaf used to build the Čech cover
chain complex. -/
private abbrev freeAbelianYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free

private abbrev cechCover (U : ι → C) : FormalCoproduct.{w} C :=
  FormalCoproduct.mk ι U

private abbrev cechPowerObject (U : ι → C) (n : ℕ) : FormalCoproduct.{w} C :=
  (cechCover U).cech.obj (op (SimplexCategory.mk n))

private abbrev cechPowerIndex (U : ι → C) (n : ℕ) :=
  (cechPowerObject U n).I

private abbrev cechPowerComponent (U : ι → C) (n : ℕ) (i : cechPowerIndex U n) : C :=
  (cechPowerObject U n).obj i

private abbrev cechCoverSummand (U : ι → C) (n : ℕ) (i : cechPowerIndex U n) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj (cechPowerComponent U n i) ⋙ AddCommGrpCat.free.{u}

/-- The component of the canonical comparison map corresponding to the intersection indexed by `i`.
It sends a morphism from the degree-`n` free-abelian Čech cover term to the corresponding section
of `F`. -/
private def cechCoverDegreeComparisonComponentToFun (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) (i : cechPowerIndex U n) :
    ((freeAbelianCechChainComplex U).X n ⟶ F) → F.obj (op (cechPowerComponent U n i)) :=
  fun α ↦
    (Sigma.ι (cechCoverSummand U n) i ≫ α).app (op (cechPowerComponent U n i))
      (FreeAbelianGroup.of (𝟙 (cechPowerComponent U n i)))

-- Proof sketch: composition with the coproduct injection and the Yoneda/free-abelian equivalence
-- are both additive, so their composite sends zero to zero.
/-- The component comparison map sends the zero morphism to the zero section. -/
private theorem cechCoverDegreeComparisonComponentToFun_map_zero (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n) :
    cechCoverDegreeComparisonComponentToFun U F n i 0 = 0 := by
  let s :=
    AddCommGrpCat.Hom.hom
      ((Sigma.ι (cechCoverSummand U n) i).app (op (cechPowerComponent U n i)))
  let g := FreeAbelianGroup.of (𝟙 (cechPowerComponent U n i))
  change (0 : _ →+ _) (s g) = 0
  simp

-- Proof sketch: composition with the coproduct injection and the Yoneda/free-abelian equivalence
-- are both additive, so their composite preserves addition.
/-- The component comparison map is additive in the source morphism. -/
private theorem cechCoverDegreeComparisonComponentToFun_map_add (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n)
    (α β : (freeAbelianCechChainComplex U).X n ⟶ F) :
    cechCoverDegreeComparisonComponentToFun U F n i (α + β) =
      cechCoverDegreeComparisonComponentToFun U F n i α +
        cechCoverDegreeComparisonComponentToFun U F n i β := by
  let s :=
    AddCommGrpCat.Hom.hom
      ((Sigma.ι (cechCoverSummand U n) i).app (op (cechPowerComponent U n i)))
  let g := FreeAbelianGroup.of (𝟙 (cechPowerComponent U n i))
  change
    AddCommGrpCat.Hom.hom ((α + β).app (op (cechPowerComponent U n i))) (s g) =
      AddCommGrpCat.Hom.hom (α.app (op (cechPowerComponent U n i))) (s g) +
        AddCommGrpCat.Hom.hom (β.app (op (cechPowerComponent U n i))) (s g)
  simpa using
    AddCommGrpCat.hom_add_apply
      (α.app (op (cechPowerComponent U n i)))
      (β.app (op (cechPowerComponent U n i)))
      (s g)

/-- The additive map from degree-`n` morphisms out of the free-abelian Čech cover complex to the
`i`-th Čech cochain component. -/
private def cechCoverDegreeComparisonComponent (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) (i : cechPowerIndex U n) :
    AddCommGrpCat.of ((freeAbelianCechChainComplex U).X n ⟶ F) ⟶
      F.obj (op (cechPowerComponent U n i)) :=
  AddCommGrpCat.ofHom
    { toFun := cechCoverDegreeComparisonComponentToFun U F n i
      map_zero' := cechCoverDegreeComparisonComponentToFun_map_zero U F n i
      map_add' := cechCoverDegreeComparisonComponentToFun_map_add U F n i }

/-- The canonical degree-`n` comparison map from the degree-`n` part of the Hom complex of the
free-abelian Čech cover complex into the degree-`n` Čech cochains of `F`. -/
def cechCoverDegreeComparison (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    AddCommGrpCat.of ((freeAbelianCechChainComplex U).X n ⟶ F) ⟶
      ((cechComplexFunctor U).obj F).X n :=
  Pi.lift (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i)

/-- Helper for Lemma 21.9.3: projecting the degreewise comparison to one Čech coordinate recovers
the corresponding component map. -/
private theorem cechCoverDegreeComparison_comp_π (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n) :
    cechCoverDegreeComparison U F n ≫
        Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i =
      cechCoverDegreeComparisonComponent U F n i := by
  -- Proof comment: `cechCoverDegreeComparison` is assembled by `Pi.lift`, so each projection
  -- immediately recovers the chosen coordinate map.
  simpa [cechCoverDegreeComparison] using
    (Pi.lift_π (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i) i)

omit [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}] in
/-- Helper for Lemma 21.9.3: the summandwise form of Lemma 18.4.2 evaluates a morphism out of the
free representable summand on the canonical free generator at the identity. -/
private theorem cechCoverSummandHomEquiv_apply (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n)
    (α : cechCoverSummand U n i ⟶ F) :
    ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F).trans
        yonedaEquiv) α) =
      α.app (op (cechPowerComponent U n i))
        (FreeAbelianGroup.of (𝟙 (cechPowerComponent U n i))) := by
  -- First unwrap the Yoneda leg into evaluation at the identity morphism.
  simpa using
    (yonedaEquiv_apply
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F) α))

/-- Helper for Lemma 21.9.3: the summandwise Hom-to-sections equivalence from Lemma 18.4.2. -/
private noncomputable def cechCoverSummandHomAddEquiv (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n) :
    (cechCoverSummand U n i ⟶ F) ≃+ F.obj (op (cechPowerComponent U n i)) where
  toEquiv :=
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F).trans
      yonedaEquiv)
  map_add' α β := by
    -- Proof comment: evaluate the equivalence on the canonical generator of the free representable.
    let e :=
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F).trans
        yonedaEquiv)
    let g := FreeAbelianGroup.of (𝟙 (cechPowerComponent U n i))
    have hsum : e.toFun (α + β) = AddCommGrpCat.Hom.hom ((α + β).app (op (cechPowerComponent U n i))) g := by
      simpa [e, g] using cechCoverSummandHomEquiv_apply U F n i (α + β)
    have hα : e.toFun α = AddCommGrpCat.Hom.hom (α.app (op (cechPowerComponent U n i))) g := by
      simpa [e, g] using cechCoverSummandHomEquiv_apply U F n i α
    have hβ : e.toFun β = AddCommGrpCat.Hom.hom (β.app (op (cechPowerComponent U n i))) g := by
      simpa [e, g] using cechCoverSummandHomEquiv_apply U F n i β
    have hsum' :
        AddCommGrpCat.Hom.hom ((α + β).app (op (cechPowerComponent U n i))) g =
          AddCommGrpCat.Hom.hom (α.app (op (cechPowerComponent U n i))) g +
            AddCommGrpCat.Hom.hom (β.app (op (cechPowerComponent U n i))) g := by
      simpa [g] using
        AddCommGrpCat.hom_add_apply
          (α.app (op (cechPowerComponent U n i)))
          (β.app (op (cechPowerComponent U n i)))
          g
    exact hsum.trans <| hsum'.trans <| by simpa [hα, hβ]

/-- Helper for Lemma 21.9.3: each coordinate of `cechCoverDegreeComparison` is the coproduct
projection followed by the summandwise Lemma 18.4.2 equivalence. -/
private theorem cechCoverDegreeComparisonComponent_eq_summandHomAddEquiv (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n)
    (α : (freeAbelianCechChainComplex U).X n ⟶ F) :
    cechCoverDegreeComparisonComponentToFun U F n i α =
      cechCoverSummandHomAddEquiv U F n i (Sigma.ι (cechCoverSummand U n) i ≫ α) := by
  -- Proof comment: the component map is the summandwise equivalence applied to the coproduct leg.
  simpa [cechCoverDegreeComparisonComponentToFun] using
    (cechCoverSummandHomEquiv_apply U F n i (Sigma.ι (cechCoverSummand U n) i ≫ α)).symm

/-- Helper for Lemma 21.9.3: the inverse of the degree-`n` comparison map is assembled by
recovering a morphism from each Čech component and then using `Sigma.desc`. -/
private noncomputable def cechCoverDegreeComparisonInvToFun (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor U).obj F).X n → ((freeAbelianCechChainComplex U).X n ⟶ F) :=
  fun x ↦
    Sigma.desc fun i ↦
      (cechCoverSummandHomAddEquiv U F n i).symm
        (AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x)

/-- Helper for Lemma 21.9.3: precomposing the explicit inverse with a coproduct injection
recovers the chosen summand map. -/
private theorem cechCoverDegreeComparisonInv_component (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : ((cechComplexFunctor U).obj F).X n) (i : cechPowerIndex U n) :
    Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n x =
      (cechCoverSummandHomAddEquiv U F n i).symm
        (AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x) := by
  -- Proof comment: `cechCoverDegreeComparisonInvToFun` is defined by `Sigma.desc`.
  simpa [cechCoverDegreeComparisonInvToFun] using
    (Limits.Sigma.ι_desc
      (fun i ↦
        (cechCoverSummandHomAddEquiv U F n i).symm
          (AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x))
      i)

/-- Helper for Lemma 21.9.3: the inverse of the degreewise comparison preserves zero. -/
private theorem cechCoverDegreeComparisonInvToFun_map_zero (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechCoverDegreeComparisonInvToFun U F n 0 = 0 := by
  -- Proof comment: coproduct injections reduce the claim to the zero law on each summand.
  apply Limits.Sigma.hom_ext
  intro i
  calc
    Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n 0 =
        (cechCoverSummandHomAddEquiv U F n i).symm
          (AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) 0) :=
      cechCoverDegreeComparisonInv_component U F n 0 i
    _ = (cechCoverSummandHomAddEquiv U F n i).symm 0 := by
      exact congrArg (fun z ↦ (cechCoverSummandHomAddEquiv U F n i).symm z)
        ((AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)).map_zero)
    _ = 0 := by
      simpa using (cechCoverSummandHomAddEquiv U F n i).symm.map_zero
    _ = Sigma.ι (cechCoverSummand U n) i ≫ (0 : (freeAbelianCechChainComplex U).X n ⟶ F) := by
      symm
      exact Limits.comp_zero

/-- Helper for Lemma 21.9.3: the inverse of the degreewise comparison is additive. -/
private theorem cechCoverDegreeComparisonInvToFun_map_add (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x y : ((cechComplexFunctor U).obj F).X n) :
    cechCoverDegreeComparisonInvToFun U F n (x + y) =
      cechCoverDegreeComparisonInvToFun U F n x +
        cechCoverDegreeComparisonInvToFun U F n y := by
  -- Proof comment: coproduct injections reduce additivity to the additive equivalence on each summand.
  apply Limits.Sigma.hom_ext
  intro i
  calc
    Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n (x + y) =
        (cechCoverSummandHomAddEquiv U F n i).symm
          (AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) (x + y)) :=
      cechCoverDegreeComparisonInv_component U F n (x + y) i
    _ =
        (cechCoverSummandHomAddEquiv U F n i).symm
          ((AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x) +
            (AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) y)) := by
      exact congrArg (fun z ↦ (cechCoverSummandHomAddEquiv U F n i).symm z)
        ((AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)).map_add x y)
    _ =
        (cechCoverSummandHomAddEquiv U F n i).symm
            (AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x) +
          (cechCoverSummandHomAddEquiv U F n i).symm
            (AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) y) := by
      simpa using
        (cechCoverSummandHomAddEquiv U F n i).symm.map_add
          (AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x)
          (AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) y)
    _ =
        Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n x +
          (Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n y) := by
      rw [cechCoverDegreeComparisonInv_component, cechCoverDegreeComparisonInv_component]
    _ = Sigma.ι (cechCoverSummand U n) i ≫
          (cechCoverDegreeComparisonInvToFun U F n x + cechCoverDegreeComparisonInvToFun U F n y) := by
      simpa using
        (Preadditive.comp_add (cechCoverSummand U n i) ((freeAbelianCechChainComplex U).X n) F
          (Sigma.ι (cechCoverSummand U n) i)
          (cechCoverDegreeComparisonInvToFun U F n x)
          (cechCoverDegreeComparisonInvToFun U F n y)).symm

/-- Helper for Lemma 21.9.3: the explicit inverse to the degree-`n` comparison map. -/
private noncomputable def cechCoverDegreeComparisonInv (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechComplexFunctor U).obj F).X n ⟶
      AddCommGrpCat.of ((freeAbelianCechChainComplex U).X n ⟶ F) :=
  AddCommGrpCat.ofHom
    { toFun := cechCoverDegreeComparisonInvToFun U F n
      map_zero' := cechCoverDegreeComparisonInvToFun_map_zero U F n
      map_add' := cechCoverDegreeComparisonInvToFun_map_add U F n }

/-- Helper for Lemma 21.9.3: the explicit inverse satisfies both triangle identities. -/
private theorem cechCoverDegreeComparison_inverse_spec (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechCoverDegreeComparison U F n ≫ cechCoverDegreeComparisonInv U F n = 𝟙 _ ∧
      cechCoverDegreeComparisonInv U F n ≫ cechCoverDegreeComparison U F n = 𝟙 _ := by
  constructor
  · -- Proof comment: compare the two maps after evaluating on one source morphism and one coproduct leg.
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro α
    change cechCoverDegreeComparisonInvToFun U F n ((cechCoverDegreeComparison U F n) α) = α
    apply Limits.Sigma.hom_ext
    intro i
    have hπ :
        cechCoverDegreeComparison U F n ≫
            Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i =
          cechCoverDegreeComparisonComponent U F n i := by
      simpa [cechCoverDegreeComparison] using
        (Pi.lift_π (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i) i)
    have hπα :
        AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
            ((cechCoverDegreeComparison U F n) α) =
          cechCoverDegreeComparisonComponentToFun U F n i α := by
      simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m α) hπ
    calc
      Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n ((cechCoverDegreeComparison U F n) α) =
          (cechCoverSummandHomAddEquiv U F n i).symm
            (AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
              ((cechCoverDegreeComparison U F n) α)) :=
        cechCoverDegreeComparisonInv_component U F n ((cechCoverDegreeComparison U F n) α) i
      _ = (cechCoverSummandHomAddEquiv U F n i).symm (cechCoverDegreeComparisonComponentToFun U F n i α) := by
        rw [hπα]
      _ = Sigma.ι (cechCoverSummand U n) i ≫ α := by
        rw [cechCoverDegreeComparisonComponent_eq_summandHomAddEquiv]
        simp
  · -- Proof comment: compare the two maps after each product projection and then use the inverse formula.
    apply Limits.Pi.hom_ext
    intro i
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    have hπ :
        cechCoverDegreeComparison U F n ≫
            Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i =
          cechCoverDegreeComparisonComponent U F n i := by
      simpa [cechCoverDegreeComparison] using
        (Pi.lift_π (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i) i)
    have hπx :
        AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
            ((cechCoverDegreeComparison U F n) (cechCoverDegreeComparisonInvToFun U F n x)) =
          cechCoverDegreeComparisonComponentToFun U F n i (cechCoverDegreeComparisonInvToFun U F n x) := by
      simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m (cechCoverDegreeComparisonInvToFun U F n x)) hπ
    calc
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
          ((cechCoverDegreeComparison U F n) (cechCoverDegreeComparisonInvToFun U F n x)) =
        cechCoverDegreeComparisonComponentToFun U F n i (cechCoverDegreeComparisonInvToFun U F n x) := hπx
      _ = cechCoverSummandHomAddEquiv U F n i
            (Sigma.ι (cechCoverSummand U n) i ≫ cechCoverDegreeComparisonInvToFun U F n x) := by
        rw [cechCoverDegreeComparisonComponent_eq_summandHomAddEquiv]
      _ = cechCoverSummandHomAddEquiv U F n i
            ((cechCoverSummandHomAddEquiv U F n i).symm
              (AddCommGrpCat.Hom.hom
                (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x)) := by
        rw [cechCoverDegreeComparisonInv_component]
      _ = AddCommGrpCat.Hom.hom
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i) x := by
        simp

-- Proof sketch: the source degree-`n` term is a coproduct of free abelian representables indexed
-- by the Čech `n`-simplices; the adjunction `AddCommGrpCat.free ⊣ forget` together with Yoneda
-- identifies each summand map with the corresponding section of `F`, and the product universal
-- property assembles these componentwise identifications into an isomorphism.
/-- Helper for Lemma 21.9.3: in each degree, morphisms from the free-abelian Čech cover complex
to `F` identify with the degree-`n` Čech cochains of `F`. -/
@[stacks 03AS]
instance cechCoverDegreeComparison_isIso (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (cechCoverDegreeComparison U F n) := by
  -- Use the explicit inverse assembled from the summandwise Lemma 18.4.2 equivalences.
  refine ⟨⟨cechCoverDegreeComparisonInv U F n, ?_, ?_⟩⟩
  · exact (cechCoverDegreeComparison_inverse_spec U F n).1
  · exact (cechCoverDegreeComparison_inverse_spec U F n).2

/-- Helper for Lemma 21.9.3: the `j`th Čech face map between consecutive Čech powers. -/
private abbrev cechFaceMap (U : ι → C) {n : ℕ} (j : Fin (n + 2)) :
    cechPowerObject U (n + 1) ⟶ cechPowerObject U n :=
  FormalCoproduct.mapPower (cechCover U) (SimplexCategory.δ j).toOrderHom.toFun

omit [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}] in
/-- Helper for Lemma 21.9.3: postcomposition by a map of presheaves commutes with the
summandwise Lemma 18.4.2 equivalence. -/
private theorem cechCoverSummandHomAddEquiv_postcompose (U : ι → C)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) (i : cechPowerIndex U n)
    (α : cechCoverSummand U n i ⟶ F) :
    cechCoverSummandHomAddEquiv U G n i (α ≫ φ) =
      AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
        (cechCoverSummandHomAddEquiv U F n i α) := by
  -- Proof comment: both sides evaluate `α` on the identity generator and then apply `φ`.
  change
    ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) G).trans
        yonedaEquiv) (α ≫ φ)) =
      AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
        ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F).trans
            yonedaEquiv) α)
  rw [cechCoverSummandHomEquiv_apply, cechCoverSummandHomEquiv_apply]
  rfl

omit [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}] in
/-- Helper for Lemma 21.9.3: under the summandwise Lemma 18.4.2 equivalence, precomposing with a
single Čech face map becomes restriction along the corresponding projection morphism. -/
private theorem cechCoverSummandHomAddEquiv_precomp_face (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (j : Fin (n + 2))
    (i : cechPowerIndex U (n + 1))
    (α : cechCoverSummand U n ((cechFaceMap U (n := n) j).f i) ⟶ F) :
    cechCoverSummandHomAddEquiv U F (n + 1) i
        ((Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
            AddCommGrpCat.free) ≫ α) =
      AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op)
        (cechCoverSummandHomAddEquiv U F n ((cechFaceMap U (n := n) j).f i) α) := by
  -- Proof comment: transpose across the free/forget adjunction, then use Yoneda naturality for
  -- the projection morphism defining the chosen face.
  change
    yonedaEquiv
        (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
              AddCommGrpCat.free) ≫ α)) =
      AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op)
        (yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) α))
  have hpre :
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
          ((Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
              AddCommGrpCat.free) ≫ α) =
        yoneda.map ((cechFaceMap U (n := n) j).φ i) ≫
          (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) α) := by
    simpa using
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left
        (yoneda.map ((cechFaceMap U (n := n) j).φ i)) α
  rw [hpre]
  simpa using
    (yonedaEquiv_naturality
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) α)
      ((cechFaceMap U (n := n) j).φ i)).symm

/-- Helper for Lemma 21.9.3: the degree-`n` map of `cechCoverHomFunctor U` is postcomposition by
the presheaf morphism. -/
private theorem cechCoverHomMap_component_eq_postcompose (U : ι → C)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ) (i : cechPowerIndex U n)
    (α : (freeAbelianCechChainComplex U).X n ⟶ F) :
    cechCoverDegreeComparisonComponentToFun U G n i
        (AddCommGrpCat.Hom.hom (((cechCoverHomFunctor U).map φ).f n) α) =
      AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
        (cechCoverDegreeComparisonComponentToFun U F n i α) := by
  -- Proof comment: after unfolding `Hom(K,-)` at degree `n`, the functor map is definitionally
  -- postcomposition by `φ`.
  rfl

omit [Limits.HasProducts AddCommGrpCat.{u}] in
/-- Helper for Lemma 21.9.3: projecting one coproduct leg through the source Čech face map exposes
the explicit Yoneda/free-abelian restriction map on that leg. -/
private theorem cechCoverEval_faceLeg_assoc (U : ι → C) (n : ℕ) (j : Fin (n + 2))
    (i : cechPowerIndex U (n + 1)) :
    Sigma.ι (cechCoverSummand U (n + 1)) i ≫
        SimplicialObject.δ
          ((cechCover U).cech ⋙
            (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
          j =
      Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i)) AddCommGrpCat.free ≫
        Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) := by
  -- Route correction: normalize the `FormalCoproduct.eval` coproduct leg once before handling the
  -- alternating sum, so later proofs can consume a stable owner-level face formula.
  simp [SimplicialObject.δ, FormalCoproduct.eval, freeAbelianYoneda]
  simpa [freeAbelianYoneda] using
    (Limits.Sigma.ι_desc_assoc
      (fun i : cechPowerIndex U (n + 1) ↦
        freeAbelianYoneda.map ((cechFaceMap U (n := n) j).φ i) ≫
          Sigma.ι
            (fun i : cechPowerIndex U n ↦
              freeAbelianYoneda.obj (cechPowerComponent U n i))
            ((cechFaceMap U (n := n) j).f i))
      i (𝟙 _))

omit [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.9.3: projecting one coordinate of the target Čech coface map exposes the
corresponding restriction map between Čech coordinates. -/
private theorem cechComplexFunctor_faceProjection_assoc (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (j : Fin (n + 2))
    (i : cechPowerIndex U (n + 1)) :
    ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j ≫
        Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i =
      Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
          ((cechFaceMap U (n := n) j).f i) ≫
        F.map ((cechFaceMap U (n := n) j).φ i).op := by
  -- Proof comment: unfold the owner boundary once so the projection is a single `Pi.lift` leg.
  simp [FormalCoproduct.cosimplicialObjectFunctor, FormalCoproduct.evalOp, CosimplicialObject.δ]
  simpa using
    (Limits.Pi.lift_π
      (fun i : cechPowerIndex U (n + 1) ↦
        Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
          ((cechFaceMap U (n := n) j).f i) ≫
          F.map ((cechFaceMap U (n := n) j).φ i).op)
      i)

/-- Helper for Lemma 21.9.3: after projecting to one coproduct summand, the source Hom
differential is the alternating sum of the face-precomposition terms. -/
private theorem cechCoverHomDifferentialPrecomp_eq_alternatingSum (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (α : (freeAbelianCechChainComplex U).X n ⟶ F)
    (i : cechPowerIndex U (n + 1)) :
    Sigma.ι (cechCoverSummand U (n + 1)) i ≫
        ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
            AddCommGrpCat.free ≫
          Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α) := by
  -- Route correction: the owner-level face formula is now available as
  -- `cechCoverEval_faceLeg_assoc`; the remaining blocker is to package
  -- fixed-leg precomposition and postcomposition by `α` as rewrite-friendly additive maps so the
  -- alternating face sum can be pushed through without reopening the `preadditiveCoyoneda` term.
  dsimp [cechCoverHomFunctor]
  let legPostcompose :
      (((freeAbelianCechChainComplex U).X (n + 1) ⟶ (freeAbelianCechChainComplex U).X n)) →+
        (cechCoverSummand U (n + 1) i ⟶ F) :=
    { toFun := fun β ↦ Sigma.ι (cechCoverSummand U (n + 1)) i ≫ β ≫ α
      map_zero' := by
        have hcomp :
            Sigma.ι (cechCoverSummand U (n + 1)) i ≫
                (0 : (freeAbelianCechChainComplex U).X (n + 1) ⟶
                  (freeAbelianCechChainComplex U).X n) =
              0 := by
          simpa using
            (Limits.comp_zero :
              Sigma.ι (cechCoverSummand U (n + 1)) i ≫
                  (0 : (freeAbelianCechChainComplex U).X (n + 1) ⟶
                    (freeAbelianCechChainComplex U).X n) =
                0)
        have hzero :
            (0 : cechCoverSummand U (n + 1) i ⟶ (freeAbelianCechChainComplex U).X n) ≫ α =
              0 := by
          simpa using
            (zero_comp :
              (0 : cechCoverSummand U (n + 1) i ⟶ (freeAbelianCechChainComplex U).X n) ≫ α =
                0)
        calc
          Sigma.ι (cechCoverSummand U (n + 1)) i ≫ (0 : _ ⟶ _) ≫ α =
              (0 : cechCoverSummand U (n + 1) i ⟶ (freeAbelianCechChainComplex U).X n) ≫ α := by
            simpa using congrArg (fun f ↦ f ≫ α) hcomp
          _ = 0 := hzero
      map_add' := by
        intro β γ
        calc
          Sigma.ι (cechCoverSummand U (n + 1)) i ≫ (β + γ) ≫ α =
              (Sigma.ι (cechCoverSummand U (n + 1)) i ≫ β +
                Sigma.ι (cechCoverSummand U (n + 1)) i ≫ γ) ≫ α := by
            simpa using congrArg
              (fun f ↦ f ≫ α)
              (Preadditive.comp_add (cechCoverSummand U (n + 1) i)
                ((freeAbelianCechChainComplex U).X (n + 1))
                ((freeAbelianCechChainComplex U).X n)
                (Sigma.ι (cechCoverSummand U (n + 1)) i) β γ)
          _ =
              Sigma.ι (cechCoverSummand U (n + 1)) i ≫ β ≫ α +
                Sigma.ι (cechCoverSummand U (n + 1)) i ≫ γ ≫ α := by
            simpa [Category.assoc] using
              (Preadditive.add_comp
                (cechCoverSummand U (n + 1) i)
                ((freeAbelianCechChainComplex U).X n)
                F
                (Sigma.ι (cechCoverSummand U (n + 1)) i ≫ β)
                (Sigma.ι (cechCoverSummand U (n + 1)) i ≫ γ)
                α) }
  change
      legPostcompose
          ((AlgebraicTopology.AlternatingFaceMapComplex.obj
              ((cechCover U).cech ⋙
                (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)).d
            (n + 1) n) =
        _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  have hsum :
      legPostcompose
          (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
            SimplicialObject.δ
              ((cechCover U).cech ⋙
                (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
              j) =
        ∑ j : Fin (n + 2), legPostcompose ((-1 : ℤ) ^ (j : ℕ) •
          SimplicialObject.δ
            ((cechCover U).cech ⋙
              (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
            j) := by
    simpa using map_sum legPostcompose
      (fun j : Fin (n + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
        SimplicialObject.δ
          ((cechCover U).cech ⋙
            (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
          j)
      Finset.univ
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hz :
      legPostcompose
          ((-1 : ℤ) ^ (j : ℕ) •
            SimplicialObject.δ
              ((cechCover U).cech ⋙
                (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
              j) =
        (-1 : ℤ) ^ (j : ℕ) •
          legPostcompose
            (SimplicialObject.δ
              ((cechCover U).cech ⋙
                (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
              j) := by
    simpa using map_zsmul legPostcompose ((-1 : ℤ) ^ (j : ℕ))
      (SimplicialObject.δ
        ((cechCover U).cech ⋙
          (FormalCoproduct.eval C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj freeAbelianYoneda)
        j)
  rw [hz]
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (j : ℕ) • (z ≫ α))
    (by simpa [legPostcompose, Category.assoc] using cechCoverEval_faceLeg_assoc U n j i)

/-- Helper for Lemma 21.9.3: transporting a single normalized source face term through the
summandwise Lemma 18.4.2 equivalence gives the corresponding Čech restriction term. -/
private theorem cechCoverDegreeComparison_faceTerm (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (j : Fin (n + 2))
    (i : cechPowerIndex U (n + 1))
    (α : (freeAbelianCechChainComplex U).X n ⟶ F) :
    cechCoverSummandHomAddEquiv U F (n + 1) i
        (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
            AddCommGrpCat.free ≫
          Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α) =
      AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op)
        (cechCoverDegreeComparisonComponentToFun U F n ((cechFaceMap U (n := n) j).f i) α) := by
  -- Proof comment: first move the face-precomposition across Lemma 18.4.2, then rewrite the
  -- remaining coproduct leg by the component formula for `cechCoverDegreeComparison`.
  rw [cechCoverSummandHomAddEquiv_precomp_face]
  rw [← cechCoverDegreeComparisonComponent_eq_summandHomAddEquiv U F n
    ((cechFaceMap U (n := n) j).f i) α]

omit [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.9.3: after projecting to one Čech coordinate, the target differential is
the alternating sum of the corresponding restriction maps. -/
private theorem cechComplexFunctorComponent_d_eq_alternatingSum (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U (n + 1)) :
    (((cechComplexFunctor U).obj F).d n (n + 1)) ≫
        Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
            ((cechFaceMap U (n := n) j).f i) ≫
          F.map ((cechFaceMap U (n := n) j).φ i).op) := by
  -- Proof comment: rewrite the public Čech differential as the alternating coface sum, then use
  -- the fixed-coordinate projection lemma to identify each summand with the expected restriction.
  rw [cechComplexFunctor_d_eq_objD]
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  let postcompose :
      (((cechComplexFunctor U).obj F).X n ⟶ ((cechComplexFunctor U).obj F).X (n + 1)) →+
        (((cechComplexFunctor U).obj F).X n ⟶ F.obj (op (cechPowerComponent U (n + 1) i))) :=
    { toFun := fun f ↦ f ≫ Pi.π _ i
      map_zero' := by simp
      map_add' := by
        intro f g
        simp }
  change postcompose
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j) = _
  have hsum :
      postcompose
          (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
            ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j) =
        ∑ j : Fin (n + 2), postcompose ((-1 : ℤ) ^ (j : ℕ) •
          ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j) := by
    simpa using map_sum postcompose
      (fun j : Fin (n + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j)
      Finset.univ
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hz :
      postcompose ((-1 : ℤ) ^ (j : ℕ) •
          ((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j) =
        (-1 : ℤ) ^ (j : ℕ) •
          postcompose (((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j) := by
    simpa using map_zsmul postcompose ((-1 : ℤ) ^ (j : ℕ))
      (((FormalCoproduct.cosimplicialObjectFunctor (cechCover U).cech).obj F).δ j)
  rw [hz]
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (j : ℕ) • z)
    (by simpa [postcompose] using cechComplexFunctor_faceProjection_assoc U F n j i)

/-- Helper for Lemma 21.9.3: after projecting to one coordinate and evaluating at `α`, the source
and target differentials both become the same alternating sum of restriction terms. -/
private theorem cechCoverDegreeComparison_comm_d_component (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (α : (freeAbelianCechChainComplex U).X n ⟶ F)
    (i : cechPowerIndex U (n + 1)) :
    AddCommGrpCat.Hom.hom
        (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
        ((((cechComplexFunctor U).obj F).d n (n + 1))
          ((cechCoverDegreeComparison U F n) α)) =
      AddCommGrpCat.Hom.hom
        (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
        ((cechCoverDegreeComparison U F (n + 1))
          ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α)) := by
  let componentTerm : Fin (n + 2) → F.obj (op (cechPowerComponent U (n + 1) i)) :=
    fun j ↦
      AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op)
        (cechCoverDegreeComparisonComponentToFun U F n ((cechFaceMap U (n := n) j).f i) α)
  let evaluate :
      ((((cechComplexFunctor U).obj F).X n) ⟶
          F.obj (op (cechPowerComponent U (n + 1) i))) →+
        F.obj (op (cechPowerComponent U (n + 1) i)) :=
    { toFun := fun f ↦ AddCommGrpCat.Hom.hom f ((cechCoverDegreeComparison U F n) α)
      map_zero' := by simp
      map_add' := by
        intro f g
        simp }
  let transport :
      (cechCoverSummand U (n + 1) i ⟶ F) →+
        F.obj (op (cechPowerComponent U (n + 1) i)) :=
    (cechCoverSummandHomAddEquiv U F (n + 1) i).toAddMonoidHom
  have hleft :
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
          ((((cechComplexFunctor U).obj F).d n (n + 1))
            ((cechCoverDegreeComparison U F n) α)) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • componentTerm j := by
    -- Proof comment: evaluate the already-normalized target differential at the degree-`n`
    -- comparison value and identify each projected term by `cechCoverDegreeComparison_comp_π`.
    calc
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
          ((((cechComplexFunctor U).obj F).d n (n + 1))
            ((cechCoverDegreeComparison U F n) α)) =
        evaluate ((((cechComplexFunctor U).obj F).d n (n + 1)) ≫
          Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i) := by
        rfl
      _ =
          evaluate
            (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                  ((cechFaceMap U (n := n) j).f i) ≫
                F.map ((cechFaceMap U (n := n) j).φ i).op)) := by
        exact congrArg evaluate (cechComplexFunctorComponent_d_eq_alternatingSum U F n i)
      _ =
          ∑ j : Fin (n + 2), evaluate ((-1 : ℤ) ^ (j : ℕ) •
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                ((cechFaceMap U (n := n) j).f i) ≫
              F.map ((cechFaceMap U (n := n) j).φ i).op)) := by
        simpa using map_sum evaluate
          (fun j : Fin (n + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
            (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                ((cechFaceMap U (n := n) j).f i) ≫
              F.map ((cechFaceMap U (n := n) j).φ i).op))
          Finset.univ
      _ =
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
            evaluate
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                  ((cechFaceMap U (n := n) j).f i) ≫
                F.map ((cechFaceMap U (n := n) j).φ i).op) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simpa using map_zsmul evaluate ((-1 : ℤ) ^ (j : ℕ))
          (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
              ((cechFaceMap U (n := n) j).f i) ≫
            F.map ((cechFaceMap U (n := n) j).φ i).op)
      _ = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • componentTerm j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hπj :
            AddCommGrpCat.Hom.hom
                (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                  ((cechFaceMap U (n := n) j).f i))
                ((cechCoverDegreeComparison U F n) α) =
              cechCoverDegreeComparisonComponentToFun U F n
                ((cechFaceMap U (n := n) j).f i) α := by
          simpa using congrArg
            (fun m ↦ AddCommGrpCat.Hom.hom m α)
            (cechCoverDegreeComparison_comp_π U F n ((cechFaceMap U (n := n) j).f i))
        calc
          (-1 : ℤ) ^ (j : ℕ) •
              evaluate
                (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                    ((cechFaceMap U (n := n) j).f i) ≫
                  F.map ((cechFaceMap U (n := n) j).φ i).op) =
            (-1 : ℤ) ^ (j : ℕ) •
              AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op)
                (AddCommGrpCat.Hom.hom
                  (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i)))
                    ((cechFaceMap U (n := n) j).f i))
                  ((cechCoverDegreeComparison U F n) α)) := by
            rfl
          _ = (-1 : ℤ) ^ (j : ℕ) • componentTerm j := by
            simpa [componentTerm] using congrArg
              (fun z ↦ (-1 : ℤ) ^ (j : ℕ) •
                AddCommGrpCat.Hom.hom (F.map ((cechFaceMap U (n := n) j).φ i).op) z)
              hπj
  have hright :
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
          ((cechCoverDegreeComparison U F (n + 1))
            ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α)) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • componentTerm j := by
    -- Proof comment: rewrite the projected source side through the summandwise equivalence, then
    -- push the normalized source alternating sum through that additive equivalence termwise.
    calc
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U (n + 1) ↦ F.obj (op (cechPowerComponent U (n + 1) i))) i)
          ((cechCoverDegreeComparison U F (n + 1))
            ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α)) =
        cechCoverDegreeComparisonComponentToFun U F (n + 1) i
          ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α) := by
        simpa using congrArg
          (fun m ↦ AddCommGrpCat.Hom.hom m ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α))
          (cechCoverDegreeComparison_comp_π U F (n + 1) i)
      _ = cechCoverSummandHomAddEquiv U F (n + 1) i
            (Sigma.ι (cechCoverSummand U (n + 1)) i ≫
              ((((cechCoverHomFunctor U).obj F).d n (n + 1)) α)) := by
        rw [cechCoverDegreeComparisonComponent_eq_summandHomAddEquiv]
      _ =
          transport
            (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
              (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
                  AddCommGrpCat.free ≫
                Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α)) := by
        exact congrArg transport (cechCoverHomDifferentialPrecomp_eq_alternatingSum U F n α i)
      _ =
          ∑ j : Fin (n + 2), transport ((-1 : ℤ) ^ (j : ℕ) •
            (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
                AddCommGrpCat.free ≫
              Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α)) := by
        simpa using map_sum transport
          (fun j : Fin (n + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
            (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
                AddCommGrpCat.free ≫
              Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α))
          Finset.univ
      _ =
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
            transport
              (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
                  AddCommGrpCat.free ≫
                Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simpa using map_zsmul transport ((-1 : ℤ) ^ (j : ℕ))
          (Functor.whiskerRight (yoneda.map ((cechFaceMap U (n := n) j).φ i))
              AddCommGrpCat.free ≫
            Sigma.ι (cechCoverSummand U n) ((cechFaceMap U (n := n) j).f i) ≫ α)
      _ = ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • componentTerm j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simpa [transport, componentTerm] using congrArg
          (fun z ↦ (-1 : ℤ) ^ (j : ℕ) • z)
          (cechCoverDegreeComparison_faceTerm U F n j i α)
  exact hleft.trans hright.symm

-- Proof sketch: both differentials are alternating sums over the coface maps induced by forgetting
-- one index. On each summand, the comparison map is the adjunction-plus-Yoneda identification from
-- Lemma `18.4.2`, and `FormalCoproduct.mapPower_π` identifies the induced restriction maps, so the
-- two alternating sums agree.
/-- Lemma 21.9.3 (2): the degreewise comparison maps intertwine the Hom differential on the
free-abelian Čech cover complex with the usual Čech differential. -/
@[stacks 03AS]
theorem cechCoverDegreeComparison_comm_d (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    CommSq
      (cechCoverDegreeComparison U F n)
      (((cechCoverHomFunctor U).obj F).d n (n + 1))
      (((cechComplexFunctor U).obj F).d n (n + 1))
      (cechCoverDegreeComparison U F (n + 1)) := by
  -- Route correction: the target-side differential is already normalized by
  -- `cechComplexFunctorComponent_d_eq_alternatingSum`. Once
  -- `cechCoverHomDifferentialPrecomp_eq_alternatingSum` is closed, project to one coordinate,
  -- rewrite both sides to the same alternating sum, and transport each source summand with
  -- `cechCoverSummandHomAddEquiv_precomp_face`.
  refine CommSq.mk ?_
  apply Limits.Pi.hom_ext
  intro i
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro α
  exact cechCoverDegreeComparison_comm_d_component U F n α i

-- Proof sketch: the source map is the degree-`n` component of `cechCoverHomFunctor U` applied to
-- `φ`, while the target map is the degree-`n` component of `cechComplexFunctor U` applied to `φ`.
-- Componentwise, both sides send a morphism out of the corresponding summand to the same
-- transported section of `G`.
/-- Helper for Lemma 21.9.3: the comparison maps are natural in the abelian presheaf `F`. -/
@[stacks 03AS]
theorem cechCoverDegreeComparison_natural (U : ι → C) {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    CommSq
      (cechCoverDegreeComparison U F n)
      (((cechCoverHomFunctor U).map φ).f n)
      (((cechComplexFunctor U).map φ).f n)
      (cechCoverDegreeComparison U G n) := by
  -- Proof comment: project to one Čech coordinate and compare both sides as postcomposition by `φ`.
  refine CommSq.mk ?_
  apply Limits.Pi.hom_ext
  intro i
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro α
  have hπG :
      cechCoverDegreeComparison U G n ≫
          Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i =
        cechCoverDegreeComparisonComponent U G n i := by
    simpa [cechCoverDegreeComparison] using
      (Pi.lift_π (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U G n i) i)
  have hmapπ :
      (((cechComplexFunctor U).map φ).f n) ≫
          Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i =
        Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i ≫
          φ.app (op (cechPowerComponent U n i)) := by
    change Limits.Pi.map (fun i : cechPowerIndex U n ↦ φ.app (op (cechPowerComponent U n i))) ≫
        Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i =
      Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i ≫
        φ.app (op (cechPowerComponent U n i))
    simpa using
      (Pi.map_π (fun i : cechPowerIndex U n ↦ φ.app (op (cechPowerComponent U n i))) i)
  have hleft :
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i)
          ((((cechComplexFunctor U).map φ).f n) ((cechCoverDegreeComparison U F n) α)) =
        AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
          (cechCoverDegreeComparisonComponentToFun U F n i α) := by
    calc
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i)
          ((((cechComplexFunctor U).map φ).f n) ((cechCoverDegreeComparison U F n) α)) =
        AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i)
          ((Limits.Pi.map (fun i : cechPowerIndex U n ↦ φ.app (op (cechPowerComponent U n i))))
            ((cechCoverDegreeComparison U F n) α)) := by
        rfl
      _ = AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
            (AddCommGrpCat.Hom.hom
              (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
              ((cechCoverDegreeComparison U F n) α)) := by
        simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m ((cechCoverDegreeComparison U F n) α)) hmapπ
      _ = AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
            (cechCoverDegreeComparisonComponentToFun U F n i α) := by
        have hπF :
            cechCoverDegreeComparison U F n ≫
                Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i =
              cechCoverDegreeComparisonComponent U F n i := by
          simpa [cechCoverDegreeComparison] using
            (Pi.lift_π (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i) i)
        have hπFα :
            AddCommGrpCat.Hom.hom
                (Pi.π (fun i : cechPowerIndex U n ↦ F.obj (op (cechPowerComponent U n i))) i)
                ((cechCoverDegreeComparison U F n) α) =
              cechCoverDegreeComparisonComponentToFun U F n i α := by
          simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m α) hπF
        exact congrArg (fun z ↦ AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i))) z) hπFα
  have hright :
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i)
          ((cechCoverDegreeComparison U G n)
            (AddCommGrpCat.Hom.hom (((cechCoverHomFunctor U).map φ).f n) α)) =
        AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
          (cechCoverDegreeComparisonComponentToFun U F n i α) := by
    calc
      AddCommGrpCat.Hom.hom
          (Pi.π (fun i : cechPowerIndex U n ↦ G.obj (op (cechPowerComponent U n i))) i)
          ((cechCoverDegreeComparison U G n)
            (AddCommGrpCat.Hom.hom (((cechCoverHomFunctor U).map φ).f n) α)) =
        cechCoverDegreeComparisonComponentToFun U G n i
          (AddCommGrpCat.Hom.hom (((cechCoverHomFunctor U).map φ).f n) α) := by
        simpa using congrArg (fun m ↦ AddCommGrpCat.Hom.hom m (AddCommGrpCat.Hom.hom (((cechCoverHomFunctor U).map φ).f n) α)) hπG
      _ = AddCommGrpCat.Hom.hom (φ.app (op (cechPowerComponent U n i)))
            (cechCoverDegreeComparisonComponentToFun U F n i α) := by
        simpa using cechCoverHomMap_component_eq_postcompose U φ n i α
  exact hleft.trans hright.symm

/-- The canonical comparison natural transformation from the Hom complex of the free-abelian Čech
cover complex to the usual Čech complex functor. Its degree-`n` component is
`cechCoverDegreeComparison U F n`. -/
@[stacks 03AS]
noncomputable def cechCoverComparison (U : ι → C) :
    cechCoverHomFunctor U ⟶ cechComplexFunctor U where
  app F :=
    { f := cechCoverDegreeComparison U F
      comm' := by
        intro n j hnj
        subst j
        simpa using (cechCoverDegreeComparison_comm_d U F n).w }
  naturality := by
    intro F G φ
    apply HomologicalComplex.Hom.ext
    funext n
    simpa using (cechCoverDegreeComparison_natural U φ n).w.symm

/-- The degree-`n` component of `cechCoverComparison U` is `cechCoverDegreeComparison U F n`. -/
@[simp]
theorem cechCoverComparison_app_f (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    ((cechCoverComparison U).app F).f n = cechCoverDegreeComparison U F n :=
  rfl

instance cechCoverComparison_app_f_isIso (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (((cechCoverComparison U).app F).f n) := by
  change IsIso (cechCoverDegreeComparison U F n)
  infer_instance

/-- Helper for Lemma 21.9.3: the canonical comparison natural transformation is a natural
isomorphism. -/
@[stacks 03AS]
instance cechCoverComparison_isIso (U : ι → C) : IsIso (cechCoverComparison U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  exact HomologicalComplex.Hom.isIso_of_components ((cechCoverComparison U).app F)

/-- Helper for Lemma 21.9.3: there is a unique natural isomorphism from the Hom complex of the
free-abelian Čech cover complex to the usual Čech complex functor whose degree-`n` components are
the canonical comparison maps `cechCoverDegreeComparison U F n`. This packages the concrete owner
`cechCoverComparison U` together with its uniqueness. -/
@[stacks 03AS]
theorem cechCoverComparison_existsUnique (U : ι → C) :
    ∃! α : cechCoverHomFunctor U ⟶ cechComplexFunctor U,
      IsIso α ∧ ∀ F n, (α.app F).f n = cechCoverDegreeComparison U F n := by
  refine ⟨cechCoverComparison U, ?_, ?_⟩
  · refine ⟨by infer_instance, ?_⟩
    intro F n
    simp [cechCoverComparison_app_f]
  · intro α hα
    apply NatTrans.ext
    funext F
    apply HomologicalComplex.Hom.ext
    funext n
    simpa [cechCoverComparison_app_f] using hα.2 F n

end CategoryTheory
