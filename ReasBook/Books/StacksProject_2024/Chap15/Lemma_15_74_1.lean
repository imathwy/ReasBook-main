import Mathlib
import StacksProject_2024.Chap15.Lemma_15_59_15
import StacksProject_2024.Chap15.Lemma_15_74_4

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
  (Adjunction.rightAdjointUniq
      (H.derivedTensorAdj (K ⊗[R]^L L))
      (((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
        (derivedTensorProductTensorIso K L))).symm

/-- Lemma 15.74.1: for a chosen derived internal Hom on `D(R)` and objects `K`, `L`, `M`, there is
a canonical isomorphism
`R\mathrm{Hom}_R(K, R\mathrm{Hom}_R(L, M)) \cong
R\mathrm{Hom}_R(K \otimes_R^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. This is the component at `M` of the canonical right-adjoint
uniqueness isomorphism comparing `ihom L ⋙ ihom K` with `ihom (K ⊗[R]^L L)`. -/
noncomputable def derivedInternalHomTensorIso
    (H : RHomPkg) (K L M : DMod) :
    RHom[H](K, (RHom[H](L, M))) ≅ RHom[H]((K ⊗[R]^L L), M) :=
  (derivedInternalHomTensorNatIso H K L).app M

private theorem derivedInternalHomTensorNatIso_natural_left
    (H : RHomPkg) {K₁ K₂ L : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f) ≫
        (derivedInternalHomTensorNatIso H K₁ L).hom =
      (derivedInternalHomTensorNatIso H K₂ L).hom ≫
        MonoidalClosed.pre ((derivedTensorProduct L).map f) := by
  sorry

private theorem derivedInternalHomTensorNatIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    Functor.whiskerRight (MonoidalClosed.pre f) (ihom K) ≫
        (derivedInternalHomTensorNatIso H K L₁).hom =
      (derivedInternalHomTensorNatIso H K L₂).hom ≫
        MonoidalClosed.pre ((derivedTensorProductMap H f).app K) := by
  sorry

/-- Lemma 15.74.1 is contravariantly natural in the first variable `K`. -/
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
