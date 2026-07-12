import Mathlib
import StacksProject_2024.Chap14.Lemma_14_25_1
import StacksProject_2024.Chap14.Definition_14_26_1
import StacksProject_2024.Chap14.Lemma_14_27_1
import StacksProject_2024.Chap14.Lemma_14_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.28.6:
- primary domain: simplicial/cosimplicial homotopy and the Dold-Kan comparison functors
  `alternatingCofaceMapComplex` and `normalizedCochainComplexFunctor`;
- sampled same-kind declarations:
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`,
  `CategoryTheory.CosimplicialObject.deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`,
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `AlgebraicTopology.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`,
  `CategoryTheory.CosimplicialObject.normalizedCochainComplexFunctor`;
- best owner abstraction: the source-facing relation in this file is
  `CategoryTheory.CosimplicialObject.DeltaOneHomotopic`; the opposite simplicial zigzag relation
  is only the bridge from Lemma 14.28.3, and the normalized complex owner in this chapter is
  `normalizedCochainComplexFunctor`;
- primitive data: directed `Δ[1]`-indexed cosimplicial homotopies and the canonical Moore-complex
  inclusion and retraction on the opposite simplicial side;
- derived API: the resulting existence of chain/cochain homotopies on the alternating and
  normalized complexes after passage through the opposite/unop bridges.

Source/core/bridge triage:
- `source-facing`: the two Stacks statements about homotopic cosimplicial maps inducing homotopic
  maps on `s(U)` and `Q(U)`;
- `core/canonical`: `DeltaOneHomotopic`, `toChainHomotopy`, and the Chapter 14 owner
  `normalizedCochainComplexFunctor`;
- `bridge/view`: `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, passage to opposite
  simplicial objects, and transport of chain homotopies through `HomologicalComplex.unopFunctor`.
  -/

section HomotopyTransport

variable [Preadditive A]
variable {K L : ChainComplex Aᵒᵖ ℕ} {f g : K ⟶ L}

/-- Transport a chain homotopy in `Aᵒᵖ` across `HomologicalComplex.unopFunctor` to the
corresponding cochain homotopy in `A`. This is the only local bridge theorem needed below. -/
private theorem unopFunctor_map_homotopy
    (h : _root_.Homotopy f g) :
    Nonempty
      (_root_.Homotopy
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map f.op)
        ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map g.op)) := by
  -- Proof comment: mathlib already packages the componentwise `unop` transport of homotopies.
  refine ⟨{ hom := fun i j ↦ (h.hom j i).unop, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    exact Quiver.Hom.op_inj (h.zero _ _ hij)
  · intro n
    exact Quiver.Hom.op_inj (by
      dsimp
      rw [h.comm n]
      nth_rw 2 [add_comm]
      rfl)

end HomotopyTransport

section AlternatingCofaceMapComplex

variable [Preadditive A]
variable {U V : CosimplicialObject A} {a b : U ⟶ V}

/-- Helper for Lemma 14.28.6: the alternating coface complex obtained by transporting the
alternating face map complex of the opposite simplicial object back to `A`. -/
private abbrev alternatingCofaceMapComplexViaOpposite :
    CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      (AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ)).rightOp ⋙
    (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))

/-- Helper for Lemma 14.28.6: the identity degreewise components intertwine the source-facing
alternating coface differential with its opposite/unop realization. -/
private theorem alternatingCofaceMapComplexIsoViaOpposite_comm
    (U : CosimplicialObject A) (i j : ℕ) (h : (ComplexShape.up ℕ).Rel i j) :
    ((Iso.refl ((AlternatingCofaceMapComplex.obj U).X i)).hom ≫
        (alternatingCofaceMapComplexViaOpposite.obj U).d i j) =
      (AlternatingCofaceMapComplex.obj U).d i j ≫
        (Iso.refl ((AlternatingCofaceMapComplex.obj U).X j)).hom := by
  -- Proof comment: both complexes are degreewise `U_[n]`, and the public differential formula
  -- `d_eq_unop_d` identifies their unique nonzero differential.
  have h' : i + 1 = j := by
    simpa using h
  subst h'
  simpa [alternatingCofaceMapComplexViaOpposite, AlternatingCofaceMapComplex.obj] using
    (AlternatingCofaceMapComplex.d_eq_unop_d (C := A) U i).symm

/-- Helper for Lemma 14.28.6: the source-facing alternating coface complex is canonically
identified with its opposite/unop realization. -/
private def alternatingCofaceMapComplexIsoViaOpposite (U : CosimplicialObject A) :
    AlternatingCofaceMapComplex.obj U ≅
      (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _)
    (alternatingCofaceMapComplexIsoViaOpposite_comm (A := A) U)

/-- Helper for Lemma 14.28.6: the transported alternating coface map acts degreewise by the same
component map as the public source-facing alternating coface map. -/
private theorem alternatingCofaceMapComplexViaOpposite_map_f
    {U V : CosimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    ((alternatingCofaceMapComplexViaOpposite (A := A)).map f).f n = f.app { len := n } := by
  rfl

/-- Helper for Lemma 14.28.6: the comparison isomorphism with the opposite/unop realization is
degreewise the identity on both the forward and inverse maps. -/
private theorem alternatingCofaceMapComplexIsoViaOpposite_component_identities
    (U : CosimplicialObject A) (n : ℕ) :
    (((alternatingCofaceMapComplexIsoViaOpposite (A := A) U).hom).f n = 𝟙 _) ∧
      (((alternatingCofaceMapComplexIsoViaOpposite (A := A) U).inv).f n = 𝟙 _) := by
  constructor
  · -- Proof comment: the forward comparison is assembled from identity components.
    simpa [alternatingCofaceMapComplexIsoViaOpposite] using
      (HomologicalComplex.Hom.isoOfComponents_hom_f
        (C₁ := AlternatingCofaceMapComplex.obj U)
        (C₂ := (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤
          CochainComplex A ℕ).obj U)
        (fun _ ↦ Iso.refl _)
        (alternatingCofaceMapComplexIsoViaOpposite_comm (A := A) U)
        n)
  · -- Proof comment: the inverse comparison is assembled from the same identity components.
    simpa [alternatingCofaceMapComplexIsoViaOpposite, AlternatingCofaceMapComplex.obj] using
      (HomologicalComplex.Hom.isoOfComponents_inv_f
        (C₁ := AlternatingCofaceMapComplex.obj U)
        (C₂ := (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤
          CochainComplex A ℕ).obj U)
        (fun _ ↦ Iso.refl _)
        (alternatingCofaceMapComplexIsoViaOpposite_comm (A := A) U)
        n)

/-- Helper for Lemma 14.28.6: the inverse comparison from the opposite/unop realization back to
the public alternating coface complex is natural in the cosimplicial object. -/
@[reassoc]
private theorem alternatingCofaceMapComplexIsoViaOpposite_inv_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplexViaOpposite (A := A)).map f ≫
        (alternatingCofaceMapComplexIsoViaOpposite (A := A) V).inv =
      (alternatingCofaceMapComplexIsoViaOpposite (A := A) U).inv ≫
        (alternatingCofaceMapComplex A).map f := by
  ext n
  rcases alternatingCofaceMapComplexIsoViaOpposite_component_identities (A := A) U n with
    ⟨_, hU⟩
  rcases alternatingCofaceMapComplexIsoViaOpposite_component_identities (A := A) V n with
    ⟨_, hV⟩
  -- Proof comment: after exposing that the comparison maps are identity degreewise, both sides
  -- are the same component map `f.app ⦋n⦌`.
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    alternatingCofaceMapComplexViaOpposite_map_f, hU, hV]
  calc
    f.app { len := n } ≫ 𝟙 (V.obj { len := n }) = f.app { len := n } := Category.comp_id _
    _ = 𝟙 (U.obj { len := n }) ≫ f.app { len := n } := (Category.id_comp _).symm

/-- Helper for Lemma 14.28.6: conjugating the transported opposite/unop map by the comparison
isomorphism recovers the public alternating coface map. -/
private theorem alternatingCofaceMapComplex_conjugated_map_eq
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (((alternatingCofaceMapComplexIsoViaOpposite (A := A) U).hom ≫
        (alternatingCofaceMapComplexViaOpposite (A := A)).map f) ≫
      (alternatingCofaceMapComplexIsoViaOpposite (A := A) V).inv) =
    (alternatingCofaceMapComplex A).map f := by
  let eU := alternatingCofaceMapComplexIsoViaOpposite (A := A) U
  let eV := alternatingCofaceMapComplexIsoViaOpposite (A := A) V
  -- Proof comment: rewrite the transported map by naturality of the inverse comparison and then
  -- cancel the comparison isomorphism on the left.
  simpa [eU, eV, Category.assoc] using
    congrArg (fun k ↦ eU.hom ≫ k)
      (alternatingCofaceMapComplexIsoViaOpposite_inv_naturality (A := A) f)

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.alternatingFaceMapComplex_map_homotopic`, and identify the resulting chain
-- homotopy in `Aᵒᵖ` with the desired cochain homotopy on `alternatingCofaceMapComplex`.
/-- Lemma 14.28.6 (1): if two morphisms of cosimplicial objects in an additive category are
`Δ[1]`-homotopic, then the induced morphisms on the alternating coface map complexes
`s(U) ⟶ s(V)` are homotopic as maps of cochain complexes. -/
theorem alternatingCofaceMapComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        ((alternatingCofaceMapComplex A).map a)
        ((alternatingCofaceMapComplex A).map b)) := by
  -- Route correction: the transported homotopy really lives first on the opposite simplicial
  -- model, so we conjugate it back through the explicit comparison isomorphism instead of trying
  -- to force the endpoint equalities definitionally.
  let hOpp :
      SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) :=
    (deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag a b).1 h
  rcases
      SimplicialObject.alternatingFaceMapComplex_map_homotopic
        (A := Aᵒᵖ) (a := NatTrans.op a) (b := NatTrans.op b) hOpp with
    ⟨hFace⟩
  rcases unopFunctor_map_homotopy (A := A) hFace with ⟨hViaRaw⟩
  have hVia :
      _root_.Homotopy
        ((alternatingCofaceMapComplexViaOpposite (A := A)).map a)
        ((alternatingCofaceMapComplexViaOpposite (A := A)).map b) := by
    -- Proof comment: `alternatingCofaceMapComplexViaOpposite` is definitionally the unop image
    -- of the opposite simplicial alternating face map complex.
    simpa [alternatingCofaceMapComplexViaOpposite] using hViaRaw
  let eU := alternatingCofaceMapComplexIsoViaOpposite (A := A) U
  let eV := alternatingCofaceMapComplexIsoViaOpposite (A := A) V
  let hConj := (hVia.compLeft eU.hom).compRight eV.inv
  have ha :
      (alternatingCofaceMapComplex A).map a =
        ((eU.hom ≫ (alternatingCofaceMapComplexViaOpposite (A := A)).map a) ≫ eV.inv) := by
    -- Proof comment: this identifies the left endpoint of the conjugated homotopy with the
    -- public source-facing alternating coface map.
    symm
    simpa [eU, eV] using alternatingCofaceMapComplex_conjugated_map_eq (A := A) a
  have hb :
      ((eU.hom ≫ (alternatingCofaceMapComplexViaOpposite (A := A)).map b) ≫ eV.inv) =
        (alternatingCofaceMapComplex A).map b := by
    -- Proof comment: the same comparison rewrite identifies the right endpoint.
    simpa [eU, eV] using alternatingCofaceMapComplex_conjugated_map_eq (A := A) b
  exact ⟨(_root_.Homotopy.ofEq ha).trans (hConj.trans (_root_.Homotopy.ofEq hb))⟩

end AlternatingCofaceMapComplex

section NormalizedCochainComplex

variable [Abelian A]
local instance : CategoryTheory.Limits.HasZeroObject Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasBinaryCoproducts Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasImages Aᵒᵖ := inferInstance
local instance : CategoryTheory.Limits.HasCokernels (CochainComplex A ℕ) := inferInstance

variable {U V : CosimplicialObject A} {a b : U ⟶ V}

/-- Helper for Lemma 14.28.6: the normalized summand inclusion followed by the normalized
projection in the public biproduct `D ⊞ Q` is the identity. -/
private theorem degenerate_normalized_biprod_inr_snd_app
    (X : CosimplicialObject A) :
    ((Limits.biprod.inr :
        normalizedCochainComplexFunctor ⟶
          (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app X) ≫
      ((Limits.biprod.snd :
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
          normalizedCochainComplexFunctor).app X) =
      𝟙 (normalizedCochainComplexFunctor.obj X) := by
  -- Proof comment: this is the objectwise right-summand identity for a binary biproduct.
  exact congrArg (fun η ↦ η.app X)
    (Limits.biprod.inr_snd :
      (Limits.biprod.inr :
        normalizedCochainComplexFunctor ⟶
          (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor) ≫
        (Limits.biprod.snd :
          (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
            normalizedCochainComplexFunctor) =
      𝟙 normalizedCochainComplexFunctor)

/-- Helper for Lemma 14.28.6: projecting the functorial map on `D ⊞ Q` to the normalized
summand recovers the public map on `Q`. -/
private theorem degenerate_normalized_biprod_inr_map_snd
    (f : U ⟶ V) :
    ((Limits.biprod.inr :
        normalizedCochainComplexFunctor ⟶
          (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
      (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
      ((Limits.biprod.snd :
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
          normalizedCochainComplexFunctor).app V) =
      normalizedCochainComplexFunctor.map f := by
  let ιQ :
      normalizedCochainComplexFunctor.obj U ⟶
        ((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).obj U :=
    ((Limits.biprod.inr :
      normalizedCochainComplexFunctor ⟶
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U)
  let πQ :
      ((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).obj V ⟶
        normalizedCochainComplexFunctor.obj V :=
    ((Limits.biprod.snd :
      (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
        normalizedCochainComplexFunctor).app V)
  have hNat :=
    (Limits.biprod.inr :
      normalizedCochainComplexFunctor ⟶
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).naturality f
  have hPost := congrArg (fun k ↦ k ≫ πQ) hNat
  -- Proof comment: naturality moves `normalizedCochainComplexFunctor.map f` across the inclusion,
  -- and the right inverse from the previous lemma collapses the terminal projection.
  calc
    ιQ ≫ (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫ πQ =
        normalizedCochainComplexFunctor.map f ≫
          (((Limits.biprod.inr :
              normalizedCochainComplexFunctor ⟶
                (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app V) ≫
            πQ) := by
      simpa [ιQ, πQ, Category.assoc] using hPost.symm
    _ = normalizedCochainComplexFunctor.map f := by
      rw [degenerate_normalized_biprod_inr_snd_app (A := A) V, Category.comp_id]

/-- Helper for Lemma 14.28.6: after conjugating the alternating-coface map by the public
splitting `s ≅ D ⊞ Q`, projecting to the normalized summand recovers the map on `Q`. -/
private theorem normalized_component_endpoint_rewrite
    (f : U ⟶ V) :
    ((Limits.biprod.inr :
        normalizedCochainComplexFunctor ⟶
          (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
      (((alternatingCofaceMapComplexIsoDegenerateNormalizedBiprod (A := A)).inv.app U) ≫
        (alternatingCofaceMapComplex A).map f ≫
        ((alternatingCofaceMapComplexIsoDegenerateNormalizedBiprod (A := A)).hom.app V)) ≫
      ((Limits.biprod.snd :
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
          normalizedCochainComplexFunctor).app V) =
      normalizedCochainComplexFunctor.map f := by
  let e := alternatingCofaceMapComplexIsoDegenerateNormalizedBiprod (A := A)
  -- Proof comment: rewrite the middle term using naturality of `e.inv` so the transported
  -- alternating map becomes the functorial map on `D ⊞ Q`.
  have hNat :
      e.inv.app U ≫ (alternatingCofaceMapComplex A).map f =
        (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
          e.inv.app V := by
    simpa [e] using (e.inv.naturality f).symm
  have hConj :
      ((Limits.biprod.inr :
            normalizedCochainComplexFunctor ⟶
              (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
          e.inv.app U ≫
            (alternatingCofaceMapComplex A).map f ≫
              e.hom.app V ≫
                ((Limits.biprod.snd :
                    (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                      normalizedCochainComplexFunctor).app V) =
        ((Limits.biprod.inr :
            normalizedCochainComplexFunctor ⟶
              (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
          (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
            e.inv.app V ≫ e.hom.app V ≫
              ((Limits.biprod.snd :
                  (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                    normalizedCochainComplexFunctor).app V) := by
    -- Proof comment: we rewrite only the transported middle composite and keep the endpoints fixed.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ((Limits.biprod.inr :
              normalizedCochainComplexFunctor ⟶
                (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
            k ≫ e.hom.app V ≫
              ((Limits.biprod.snd :
                  (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                    normalizedCochainComplexFunctor).app V))
        hNat
  -- Proof comment: after reassociation, the comparison isomorphism cancels on the right.
  calc
    ((Limits.biprod.inr :
          normalizedCochainComplexFunctor ⟶
            (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
        (e.inv.app U ≫
          (alternatingCofaceMapComplex A).map f ≫
            e.hom.app V) ≫
              ((Limits.biprod.snd :
                  (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                    normalizedCochainComplexFunctor).app V) =
        ((Limits.biprod.inr :
              normalizedCochainComplexFunctor ⟶
                (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
          (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
            e.inv.app V ≫ e.hom.app V ≫
              ((Limits.biprod.snd :
                  (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                    normalizedCochainComplexFunctor).app V) := by
      simpa [Category.assoc] using hConj
    _ =
        ((Limits.biprod.inr :
              normalizedCochainComplexFunctor ⟶
                (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
          (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
            ((Limits.biprod.snd :
                (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                  normalizedCochainComplexFunctor).app V) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            ((Limits.biprod.inr :
                normalizedCochainComplexFunctor ⟶
                  (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U) ≫
              (((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).map f) ≫
                k ≫
                  ((Limits.biprod.snd :
                      (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
                        normalizedCochainComplexFunctor).app V))
          (e.inv_hom_id_app V)
    _ = normalizedCochainComplexFunctor.map f := by
      simpa [e, Category.assoc] using degenerate_normalized_biprod_inr_map_snd (A := A) f

/-- Helper for Lemma 14.28.6: a homotopy on the alternating coface complexes induces a homotopy
on the normalized summands by conjugating across the public splitting and projecting to `Q`. -/
private noncomputable def normalized_component_homotopy_of_alternating_homotopy
    (h :
      _root_.Homotopy
        ((alternatingCofaceMapComplex A).map a)
        ((alternatingCofaceMapComplex A).map b)) :
    _root_.Homotopy
      (normalizedCochainComplexFunctor.map a)
      (normalizedCochainComplexFunctor.map b) := by
  let e := alternatingCofaceMapComplexIsoDegenerateNormalizedBiprod (A := A)
  let ιQ :
      normalizedCochainComplexFunctor.obj U ⟶
        ((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).obj U :=
    ((Limits.biprod.inr :
      normalizedCochainComplexFunctor ⟶
        (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).app U)
  let πQ :
      ((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).obj V ⟶
        normalizedCochainComplexFunctor.obj V :=
    ((Limits.biprod.snd :
      (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
        normalizedCochainComplexFunctor).app V)
  let hB := (h.compLeft (e.inv.app U)).compRight (e.hom.app V)
  let hQ := (hB.compLeft ιQ).compRight πQ
  have ha :
      (ιQ ≫
          (e.inv.app U ≫ (alternatingCofaceMapComplex A).map a ≫ e.hom.app V)) ≫
            πQ =
        normalizedCochainComplexFunctor.map a :=
    by
      simpa [Category.assoc] using normalized_component_endpoint_rewrite (A := A) a
  have hb :
      (ιQ ≫
          (e.inv.app U ≫ (alternatingCofaceMapComplex A).map b ≫ e.hom.app V)) ≫
            πQ =
        normalizedCochainComplexFunctor.map b :=
    by
      simpa [Category.assoc] using normalized_component_endpoint_rewrite (A := A) b
  -- Proof comment: the conjugated homotopy already lives on `D ⊞ Q`; composing with the
  -- biproduct inclusion and projection extracts the normalized component.
  exact (_root_.Homotopy.ofEq (by simpa [Category.assoc] using ha.symm)).trans
    (hQ.trans (_root_.Homotopy.ofEq (by simpa [Category.assoc] using hb)))

-- Proof sketch: transport the given `DeltaOneHomotopic` relation across
-- `deltaOneHomotopic_iff_opposite_simplicial_homotopy_zigzag`, apply
-- `SimplicialObject.normalizedMooreComplex_map_homotopic` in `Aᵒᵖ`, and transport the resulting
-- chain homotopy back to a cochain homotopy using `HomologicalComplex.unopFunctor`.
/-- Lemma 14.28.6 (2): if `A` is abelian and two morphisms of cosimplicial objects are homotopic,
then the induced morphisms on the normalized cochain complexes `Q(U) ⟶ Q(V)` are homotopic as
maps of cochain complexes. -/
theorem normalizedCochainComplex_map_homotopic
    (h : DeltaOneHomotopic a b) :
    Nonempty
      (_root_.Homotopy
        (normalizedCochainComplexFunctor.map a)
        (normalizedCochainComplexFunctor.map b)) := by
  -- Route correction: the direct `Q(U)' = N(U')` comparison is private in Lemma 14.25.1, so we
  -- follow the public splitting `s ≅ D ⊞ Q` and project the normalized summand.
  rcases alternatingCofaceMapComplex_map_homotopic (A := A) (U := U) (V := V) (a := a) (b := b) h
      with ⟨hAlt⟩
  -- Proof comment: once the alternating homotopy is available, the normalized statement is its
  -- projected `Q`-summand via the public splitting helper above.
  exact ⟨normalized_component_homotopy_of_alternating_homotopy (A := A) hAlt⟩

end NormalizedCochainComplex

end CategoryTheory.CosimplicialObject
