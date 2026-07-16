import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_59_15
import stacks_proof.stacks_project.Chap15.Lemma_15_74_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom
open scoped DerivedTensorProduct

/- Domain-style sampling for Lemma 15.74.1:
- primary domain: tensor/internal-Hom currying in the closed monoidal derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedCategory_tensorObj_iso_derivedTensorProduct`,
  `CategoryTheory.tensoringRightIsoDerivedTensorProduct`,
  `CategoryTheory.Adjunction.rightAdjointUniq`;
  `source-facing`: the textbook objectwise currying isomorphism
    `RHom_R(K, RHom_R(L, M)) ≅ RHom_R(K ⊗^L_R L, M)`;
  `core/canonical`: a chosen owner `H : MonoidalClosed DMod`, together with the canonical
    internal Hom functors `ihom K` and the derived tensor functors `derivedTensorProduct K`;
  `bridge/view`: the comparison isomorphism between iterated fixed-right-factor derived tensoring
    and tensoring by the derived tensor product `K ⊗[R]^L L`, reused from the upstream bridge
    `derivedTensorProductTensorIso`, and the resulting functor-level right-adjoint uniqueness
    isomorphism.
- primitive data: only the owner `H : MonoidalClosed DMod`;
- derived API: the objectwise textbook isomorphism and its naturality squares; the functor-level
  uniqueness isomorphism is only an internal bridge.

Source/core/bridge triage:
- `source-facing`: `derivedInternalHomTensorIso`;
- `core/canonical`: `H.derivedTensorAdj`, `ihom`, and the monoidal coherence isomorphisms on
  `D(R)`;
- `bridge/view`: the upstream tensor-functor comparison `derivedTensorProductTensorIso`, used to
  transport the composite adjunction to the source-facing derived tensor notation, together with
  the private functor-level right-adjoint-uniqueness isomorphism whose component at `M` is
  `derivedInternalHomTensorIso`. -/

private noncomputable def derivedInternalHomTensorNatIso
    (H : RHomPkg) (K L : DMod) :
    letI := H
    ihom L ⋙ ihom K ≅ ihom (K ⊗[R]^L L) :=
  letI := H
  (conjugateIsoEquiv
      (H.derivedTensorAdj (K ⊗[R]^L L))
      ((H.derivedTensorAdj K).comp (H.derivedTensorAdj L))
      (derivedTensorProductTensorIso K L)).symm

/-- Lemma 15.74.1: for a chosen derived internal Hom on `D(R)` and objects `K`, `L`, `M`, there is
a canonical isomorphism
`R\mathrm{Hom}_R(K, R\mathrm{Hom}_R(L, M)) \cong
R\mathrm{Hom}_R(K \otimes_R^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. This is the component at `M` of the canonical right-adjoint
uniqueness isomorphism comparing `ihom L ⋙ ihom K` with `ihom (K ⊗[R]^L L)`. -/
@[stacks 0A65]
noncomputable def derivedInternalHomTensorIso
    (H : RHomPkg) (K L M : DMod) :
    RHom[H](K, (RHom[H](L, M))) ≅ RHom[H]((K ⊗[R]^L L), M) :=
  (derivedInternalHomTensorNatIso H K L).app M

/-- Helper for Lemma 15.74.1: after transporting the currying isomorphism across
`- ⊗[R]^L (K ⊗[R]^L L) ⊣ RHom_R(K ⊗[R]^L L,-)`, its component is the counit of the composite
adjunction reassociated by `derivedTensorProductTensorIso`. -/
private theorem derivedInternalHomTensorNatIso_hom_app_eq_rightAdjointUniq_hom_app
    (H : RHomPkg) (K L M : DMod) :
    letI := H
    (derivedInternalHomTensorNatIso H K L).hom.app M =
      ((((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
          (derivedTensorProductTensorIso K L)).rightAdjointUniq
        (H.derivedTensorAdj (K ⊗[R]^L L))).hom.app M := by
  letI := H
  let adjTensor : derivedTensorProduct (K ⊗[R]^L L) ⊣ ihom (K ⊗[R]^L L) :=
    H.derivedTensorAdj (K ⊗[R]^L L)
  let adjComp :
      derivedTensorProduct (K ⊗[R]^L L) ⊣ ihom L ⋙ ihom K :=
    ((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
      (derivedTensorProductTensorIso K L)
  -- Proof comment: the definition of `derivedInternalHomTensorNatIso` is exactly the
  -- right-adjoint-uniqueness isomorphism between the transported composite adjunction and the
  -- source-facing tensor adjunction.
  simpa [derivedInternalHomTensorNatIso, adjTensor, adjComp, Adjunction.rightAdjointUniq,
    conjugateIsoEquiv, conjugateEquiv]

/-- Helper for Lemma 15.74.1: after transporting the currying isomorphism across
`- ⊗[R]^L (K ⊗[R]^L L) ⊣ RHom_R(K ⊗[R]^L L,-)`, its component is the counit of the composite
adjunction reassociated by `derivedTensorProductTensorIso`. -/
private theorem derivedInternalHomTensorNatIso_hom_app_symm
    (H : RHomPkg) (K L M : DMod) :
    letI := H
    ((H.derivedTensorAdj (K ⊗[R]^L L)).homEquiv _ _).symm
        ((derivedInternalHomTensorNatIso H K L).hom.app M) =
      ((((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
          (derivedTensorProductTensorIso K L)).counit.app M) := by
  letI := H
  let adjTensor : derivedTensorProduct (K ⊗[R]^L L) ⊣ ihom (K ⊗[R]^L L) :=
    H.derivedTensorAdj (K ⊗[R]^L L)
  let adjComp :
      derivedTensorProduct (K ⊗[R]^L L) ⊣ ihom L ⋙ ihom K :=
    ((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
      (derivedTensorProductTensorIso K L)
  -- Route correction: first identify the currying map with the canonical uniqueness comparison of
  -- right adjoints, then take its mate using the standard `rightAdjointUniq` counit formula.
  rw [derivedInternalHomTensorNatIso_hom_app_eq_rightAdjointUniq_hom_app H K L M]
  simpa [adjTensor, adjComp] using
    (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adjComp adjTensor M)

/-- Helper for Lemma 15.74.1: postcomposing with the right-adjoint-uniqueness comparison
transports a transpose from one chosen right adjoint to the other. -/
private theorem homEquiv_symm_rightAdjointUniq_hom_app_comp
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G G' : D ⥤ C}
    (adj₁ : F ⊣ G)
    (adj₂ : F ⊣ G')
    {A : C}
    {B : D}
    (φ : A ⟶ G.obj B) :
    (adj₂.homEquiv A B).symm (φ ≫ (Adjunction.rightAdjointUniq adj₁ adj₂).hom.app B) =
      (adj₁.homEquiv A B).symm φ := by
  -- Proof comment: expand both transposes and rewrite the counit using the standard
  -- right-adjoint-uniqueness compatibility.
  simpa [Adjunction.homEquiv, Functor.map_comp, Category.assoc] using
    congrArg
      (fun ψ ↦ F.map φ ≫ ψ)
      (Adjunction.rightAdjointUniq_hom_app_counit adj₁ adj₂ (x := B))

/-- Helper for Lemma 15.74.1: the left-variable internal-Hom naturality square becomes the mate
of the corresponding tensor square after replacing the currying comparison by its
right-adjoint-uniqueness component. -/
private theorem derivedInternalHomTensorNatIso_mate_left_source
    (H : RHomPkg) {K₁ K₂ L M : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    ((H.derivedTensorAdj (K₁ ⊗[R]^L L)).homEquiv _ _).symm
        (((Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f)).app M) ≫
          (derivedInternalHomTensorNatIso H K₁ L).hom.app M) =
      ((((H.derivedTensorAdj K₁).comp (H.derivedTensorAdj L)).ofNatIsoLeft
          (derivedTensorProductTensorIso K₁ L)).homEquiv _ _).symm
        ((Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f)).app M) := by
  letI := H
  let adjTensor : derivedTensorProduct (K₁ ⊗[R]^L L) ⊣ ihom (K₁ ⊗[R]^L L) :=
    H.derivedTensorAdj (K₁ ⊗[R]^L L)
  let adjComp :
      derivedTensorProduct (K₁ ⊗[R]^L L) ⊣ ihom L ⋙ ihom K₁ :=
    ((H.derivedTensorAdj K₁).comp (H.derivedTensorAdj L)).ofNatIsoLeft
      (derivedTensorProductTensorIso K₁ L)
  -- Proof comment: replace the currying component by the corresponding
  -- `rightAdjointUniq` map and then strip it off with the generic mate-transport lemma.
  rw [derivedInternalHomTensorNatIso_hom_app_eq_rightAdjointUniq_hom_app H K₁ L M]
  simpa [adjTensor, adjComp] using
    homEquiv_symm_rightAdjointUniq_hom_app_comp adjComp adjTensor
      ((Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f)).app M)

/-- Helper for Lemma 15.74.1: the middle-variable internal-Hom naturality square becomes the mate
of the corresponding tensor square after replacing the currying comparison by its
right-adjoint-uniqueness component. -/
private theorem derivedInternalHomTensorNatIso_mate_middle_source
    (H : RHomPkg) (K : DMod) {L₁ L₂ M : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    ((H.derivedTensorAdj (K ⊗[R]^L L₁)).homEquiv _ _).symm
        (((Functor.whiskerRight (MonoidalClosed.pre f) (ihom K)).app M) ≫
          (derivedInternalHomTensorNatIso H K L₁).hom.app M) =
      ((((H.derivedTensorAdj K).comp (H.derivedTensorAdj L₁)).ofNatIsoLeft
          (derivedTensorProductTensorIso K L₁)).homEquiv _ _).symm
        ((Functor.whiskerRight (MonoidalClosed.pre f) (ihom K)).app M) := by
  letI := H
  let adjTensor : derivedTensorProduct (K ⊗[R]^L L₁) ⊣ ihom (K ⊗[R]^L L₁) :=
    H.derivedTensorAdj (K ⊗[R]^L L₁)
  let adjComp :
      derivedTensorProduct (K ⊗[R]^L L₁) ⊣ ihom L₁ ⋙ ihom K :=
    ((H.derivedTensorAdj K).comp (H.derivedTensorAdj L₁)).ofNatIsoLeft
      (derivedTensorProductTensorIso K L₁)
  -- Proof comment: this is the same mate transport as above, now for the right-whiskered
  -- contravariant map in the middle tensor factor.
  rw [derivedInternalHomTensorNatIso_hom_app_eq_rightAdjointUniq_hom_app H K L₁ M]
  simpa [adjTensor, adjComp] using
    homEquiv_symm_rightAdjointUniq_hom_app_comp adjComp adjTensor
      ((Functor.whiskerRight (MonoidalClosed.pre f) (ihom K)).app M)

/-- Helper for Lemma 15.74.1: the tensor/derived-tensor comparison is natural in the left
variable, written in the direction used by the reassociation square. -/
@[reassoc]
private theorem tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit
    (L : DMod) {K₁ K₂ : DMod} (f : K₁ ⟶ K₂) :
    (derivedCategory_tensorObj_iso_derivedTensorProduct K₁ L).hom ≫
        (derivedTensorProduct L).map f =
      (f ▷ L) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct K₂ L).hom := by
  -- Proof comment: this is just the componentwise naturality of the comparison
  -- `tensoringRightIsoDerivedTensorProduct L`.
  simpa using
    ((tensoringRightIsoDerivedTensorProduct L).hom.naturality f).symm

/-- Helper for Lemma 15.74.1: transporting the mate defining `derivedTensorProductMap` across the
ambient tensor/derived-tensor comparison recovers the ordinary right-tensor morphism `K ◁ f`. -/
private theorem derivedTensorProductMap_homEquiv
    (H : RHomPkg) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) (K : DMod) :
    letI := H
    ((H.derivedTensorAdj L₁).homEquiv K ((derivedTensorProduct L₂).obj K))
        ((derivedTensorProductMap H f).app K) =
      (H.derivedTensorAdj L₂).unit.app K ≫
        (MonoidalClosed.pre f).app ((derivedTensorProduct L₂).obj K) := by
  letI := H
  -- Proof comment: `derivedTensorProductMap` is defined as the mate of `MonoidalClosed.pre f`;
  -- the generic unit formula for `conjugateEquiv` identifies its transpose immediately.
  simpa [Adjunction.homEquiv, derivedTensorProductMap, Category.assoc] using
    (unit_conjugateEquiv_symm
      (H.derivedTensorAdj L₂)
      (H.derivedTensorAdj L₁)
      (MonoidalClosed.pre f)
      K).symm

/-- Helper for Lemma 15.74.1: after peeling off the two `ofNatIsoLeft` transports inside
`H.derivedTensorAdj`, the transpose of the ambient comparison morphism is the same unit/pre
composite that defines `derivedTensorProductMap`. -/
-- TODO: re-plan this transport step by isolating the braiding-side mate of `K ◁ f` under the
-- intermediate `ofNatIsoLeft` adjunction, then reassemble the two transports without relying on a
-- brittle `simp`/`rw` normalization.
private theorem derivedTensorProduct_comparison_homEquiv
    (H : RHomPkg) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) (K : DMod) :
    letI := H
    ((H.derivedTensorAdj L₁).homEquiv K ((derivedTensorProduct L₂).obj K))
        ((derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
          (K ◁ f) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom) =
      (H.derivedTensorAdj L₂).unit.app K ≫
        (MonoidalClosed.pre f).app ((derivedTensorProduct L₂).obj K) := sorry

/-- Helper for Lemma 15.74.1: transporting the mate defining `derivedTensorProductMap` across the
ambient tensor/derived-tensor comparison recovers the ordinary right-tensor morphism `K ◁ f`. -/
private theorem derivedTensorProductMap_transport_hom_app
    (H : RHomPkg) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) (K : DMod) :
    letI := H
    (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).hom ≫
        (derivedTensorProductMap H f).app K =
      (K ◁ f) ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom := by
  letI := H
  -- Route correction: the mate side is now normalized by `derivedTensorProductMap_homEquiv`, so
  -- only the ambient comparison map still needs to be transported back through
  -- `tensoringRightIsoDerivedTensorProduct`.
  have hMate :
      ((H.derivedTensorAdj L₁).homEquiv K ((derivedTensorProduct L₂).obj K))
          ((derivedTensorProductMap H f).app K) =
        (H.derivedTensorAdj L₂).unit.app K ≫
          (MonoidalClosed.pre f).app ((derivedTensorProduct L₂).obj K) :=
    derivedTensorProductMap_homEquiv H f K
  have hComparison :
      ((H.derivedTensorAdj L₁).homEquiv K ((derivedTensorProduct L₂).obj K))
          ((derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
            (K ◁ f) ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom) =
        (H.derivedTensorAdj L₂).unit.app K ≫
          (MonoidalClosed.pre f).app ((derivedTensorProduct L₂).obj K) :=
    derivedTensorProduct_comparison_homEquiv H f K
  have hUnderlying :
      (derivedTensorProductMap H f).app K =
        (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
          (K ◁ f) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom := by
    -- Proof comment: the two candidate source maps have the same transpose under
    -- `H.derivedTensorAdj L₁`, so injectivity of the Hom-equivalence identifies them.
    apply ((H.derivedTensorAdj L₁).homEquiv K ((derivedTensorProduct L₂).obj K)).injective
    exact hMate.trans hComparison.symm
  -- Proof comment: compose the identified source map with the comparison isomorphism on the left
  -- to recover the source-facing transport statement.
  calc
    (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).hom ≫
        (derivedTensorProductMap H f).app K
        =
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).hom ≫
            ((derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
              (K ◁ f) ≫
              (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom) := by
                rw [hUnderlying]
    _ = (K ◁ f) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom := by
            simp [Category.assoc]

/-- Helper for Lemma 15.74.1: applying `derivedTensorProduct L` to the source-side transport
identity for `derivedTensorProductMap H f` rewrites the two successive functor maps into the
source-facing morphism `(X ◁ f)`. -/
private theorem derivedTensorProductMap_transport_map
    (H : RHomPkg) {K₁ K₂ L X : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    (derivedTensorProduct L).map
        ((derivedCategory_tensorObj_iso_derivedTensorProduct X K₁).hom ≫
          (derivedTensorProductMap H f).app X) =
      (derivedTensorProduct L).map
        ((X ◁ f) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct X K₂).hom) := by
  letI := H
  -- Proof comment: functoriality carries the source-side comparison identity through
  -- `derivedTensorProduct L`.
  simpa using congrArg ((derivedTensorProduct L).map)
    (derivedTensorProductMap_transport_hom_app H f X)

/-- Helper for Lemma 15.74.1: cancelling the comparison isomorphism on the right rewrites the
derived-tensor map as the source-facing ambient tensor morphism. -/
private theorem derivedTensorProductMap_transport_inv_app
    (H : RHomPkg) {L₁ L₂ K : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    (derivedTensorProductMap H f).app K ≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).inv =
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
        (K ◁ f) := by
  letI := H
  -- Proof comment: compose the source-side transport identity with the inverse comparison map and
  -- cancel the resulting isomorphism on the right.
  calc
    (derivedTensorProductMap H f).app K ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).inv
        =
        (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
          ((derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).hom ≫
            (derivedTensorProductMap H f).app K) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).inv := by
            simp [Category.assoc]
    _ =
        (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
          ((K ◁ f) ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).hom) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct K L₂).inv := by
            rw [derivedTensorProductMap_transport_hom_app H f K]
    _ = (derivedCategory_tensorObj_iso_derivedTensorProduct K L₁).inv ≫
          (K ◁ f) := by
            simp [Category.assoc]

/-- Helper for Lemma 15.74.1: objectwise expansion of the inverse tensor reassociation comparison
into the five source-facing comparison morphisms used in `derivedTensorProductTensorIso`. -/
private theorem derivedTensorProductTensorIso_inv_app_explicit
    (K L M : DMod) :
    (derivedTensorProductTensorIso L M).inv.app K =
      (tensoringRightIsoDerivedTensorProduct (L ⊗[R]^L M)).inv.app K ≫
        (((tensoringRight DMod).mapIso
          (derivedCategory_tensorObj_iso_derivedTensorProduct L M)).inv.app K) ≫
        (tensorRightTensor L M).hom.app K ≫
        ((Functor.isoWhiskerLeft
          ((tensoringRight DMod).obj L)
          (tensoringRightIsoDerivedTensorProduct M)).hom.app K) ≫
        ((Functor.isoWhiskerRight
          (tensoringRightIsoDerivedTensorProduct L)
          (derivedTensorProduct M)).hom.app K) := by
  -- Proof comment: unfold the five comparison factors defining
  -- `derivedTensorProductTensorIso`; the inverse component is the same five-term composite read
  -- from right to left, with the whiskered inverses rewritten as whiskered forward components.
  simpa [derivedTensorProductTensorIso, Functor.isoWhiskerRight, Functor.whiskerRight_app,
    Functor.map_comp, Functor.isoWhiskerLeft_hom, Category.assoc]

/-- Helper for Lemma 15.74.1: the inverse component of `tensoringRight.mapIso` is the
right-whiskering of the inverse comparison morphism. -/
private theorem tensoringRight_mapIso_inv_app_explicit
    (X K L : DMod) :
    (((tensoringRight DMod).mapIso
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L)).inv.app X) =
      X ◁ (derivedCategory_tensorObj_iso_derivedTensorProduct K L).inv := by
  -- Proof comment: `Functor.mapIso` applies the right-tensor functor to the inverse comparison
  -- isomorphism, so the component is definitionally the corresponding right whisker.
  rfl

/-- Helper for Lemma 15.74.1: the component of `tensorRightTensor` is the inverse associator. -/
private theorem tensorRightTensor_hom_app_explicit
    (X K L : DMod) :
    ((tensorRightTensor K L).hom.app X) = (α_ X K L).inv := by
  -- Proof comment: `tensorRightTensor` is the canonical reassociation for successive right
  -- tensor functors, and its forward component is definitionally the inverse associator.
  rfl

/-- Helper for Lemma 15.74.1: whiskering `tensoringRightIsoDerivedTensorProduct` on the left by a
fixed right tensor factor evaluates to the corresponding source-facing comparison morphism. -/
private theorem isoWhiskerLeft_tensoringRightIsoDerivedTensorProduct_hom_app
    (X K L : DMod) :
    ((Functor.isoWhiskerLeft ((tensoringRight DMod).obj K)
      (tensoringRightIsoDerivedTensorProduct L)).hom.app X) =
      (derivedCategory_tensorObj_iso_derivedTensorProduct (X ⊗ K) L).hom := by
  -- Proof comment: left whiskering evaluates the natural isomorphism at the tensor-right image
  -- of `X`, which here is the object `X ⊗ K`.
  rfl

/-- Helper for Lemma 15.74.1: whiskering `tensoringRightIsoDerivedTensorProduct` on the right by
`derivedTensorProduct L` applies that functor to the source-facing comparison map. -/
private theorem isoWhiskerRight_tensoringRightIsoDerivedTensorProduct_hom_app
    (X K L : DMod) :
    ((Functor.isoWhiskerRight (tensoringRightIsoDerivedTensorProduct K)
      (derivedTensorProduct L)).hom.app X) =
      (derivedTensorProduct L).map
        (derivedCategory_tensorObj_iso_derivedTensorProduct X K).hom := by
  -- Proof comment: right whiskering evaluates by applying `derivedTensorProduct L` to the
  -- comparison morphism in the first tensor variable.
  rfl

/-- Helper for Lemma 15.74.1: the tensor associativity comparison intertwines the map induced by a
map in the first tensor factor with the corresponding map on the derived tensor product. -/
-- TODO: re-plan this square with an explicit owner-level reassociation helper that rewrites the
-- comparison prefix before the final associator naturality step.
private theorem derivedTensorProductTensorIso_natural_left
    (H : RHomPkg) {K₁ K₂ L : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    (derivedTensorProductTensorIso K₁ L).inv ≫
        Functor.whiskerRight (derivedTensorProductMap H f) (derivedTensorProduct L) =
      derivedTensorProductMap H ((derivedTensorProduct L).map f) ≫
        (derivedTensorProductTensorIso K₂ L).inv := sorry

/-- Helper for Lemma 15.74.1: the tensor associativity comparison intertwines the map induced by a
map in the middle tensor factor with the canonical map on the iterated derived tensor product. -/
-- TODO: re-plan this square in parallel with the left-variable tensor square; the remaining gap is
-- the same reassociation-prefix normalization for the `Functor.whiskerLeft` variant.
private theorem derivedTensorProductTensorIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    (derivedTensorProductTensorIso K L₁).inv ≫
        Functor.whiskerLeft (derivedTensorProduct K) (derivedTensorProductMap H f) =
      derivedTensorProductMap H ((derivedTensorProductMap H f).app K) ≫
        (derivedTensorProductTensorIso K L₂).inv := sorry

private theorem derivedInternalHomTensorNatIso_natural_left
    (H : RHomPkg) {K₁ K₂ L : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f) ≫
        (derivedInternalHomTensorNatIso H K₁ L).hom =
      (derivedInternalHomTensorNatIso H K₂ L).hom ≫
        MonoidalClosed.pre ((derivedTensorProduct L).map f) := sorry

private theorem derivedInternalHomTensorNatIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    Functor.whiskerRight (MonoidalClosed.pre f) (ihom K) ≫
        (derivedInternalHomTensorNatIso H K L₁).hom =
      (derivedInternalHomTensorNatIso H K L₂).hom ≫
        MonoidalClosed.pre ((derivedTensorProductMap H f).app K) := sorry

/-- Lemma 15.74.1 is contravariantly natural in the first variable `K`. -/
@[stacks 0A65]
theorem derivedInternalHomTensorIso_natural_left
    (H : RHomPkg) {K₁ K₂ L M : DMod} (f : K₁ ⟶ K₂) :
    CommSq
      (derivedInternalHomMap H f (𝟙 (RHom[H](L, M))))
      (derivedInternalHomTensorIso H K₂ L M).hom
      (derivedInternalHomTensorIso H K₁ L M).hom
      (derivedInternalHomMap H ((derivedTensorProduct L).map f) (𝟙 M)) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    NatTrans.congr_app (derivedInternalHomTensorNatIso_natural_left H f) M

/-- Lemma 15.74.1 is contravariantly natural in the middle variable `L`. -/
@[stacks 0A65]
theorem derivedInternalHomTensorIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ M : DMod} (f : L₁ ⟶ L₂) :
    CommSq
      (derivedInternalHomMap H (𝟙 K) (derivedInternalHomMap H f (𝟙 M)))
      (derivedInternalHomTensorIso H K L₂ M).hom
      (derivedInternalHomTensorIso H K L₁ M).hom
      (derivedInternalHomMap H ((derivedTensorProductMap H f).app K) (𝟙 M)) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    NatTrans.congr_app (derivedInternalHomTensorNatIso_natural_middle H K f) M

/-- Lemma 15.74.1 is functorial in the target variable `M`. -/
@[stacks 0A65]
theorem derivedInternalHomTensorIso_natural_right
    (H : RHomPkg) (K L : DMod) {M₁ M₂ : DMod} (f : M₁ ⟶ M₂) :
    CommSq
      (derivedInternalHomMap H (𝟙 K) (derivedInternalHomMap H (𝟙 L) f))
      (derivedInternalHomTensorIso H K L M₁).hom
      (derivedInternalHomTensorIso H K L M₂).hom
      (derivedInternalHomMap H (𝟙 (K ⊗[R]^L L)) f) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    (derivedInternalHomTensorNatIso H K L).hom.naturality f

end

end CategoryTheory
