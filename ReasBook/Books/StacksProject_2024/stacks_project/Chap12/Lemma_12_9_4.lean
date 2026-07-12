import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Opposite

/-
Domain-style sampling for Lemma 12.9.4:
- primary domain: object properties in an abelian category, with Artinian and Noetherian
  conditions organized via the owner API `ObjectProperty`;
- inspected owner declarations:
  `isArtinianObject`,
  `isNoetherianObject`,
  `ObjectProperty.IsSerreClass`,
  `ObjectProperty.prop_iff_of_shortExact`;
- best owner abstraction: the object property `isArtinianObject : ObjectProperty C` together with
  the Serre-class owner interface;
- primitive data: only the Artinian object property itself and the short exact sequence;
- derived API: the Serre-class instance and the short-exact characterization obtained from
  `ObjectProperty.prop_iff_of_shortExact`.

Source/core/bridge triage:
- `source-facing`: the textbook statements that Artinian objects are closed under short exact
  sequences;
- `core/canonical`: `isArtinianObject : ObjectProperty C` and the owner theorem
  `ObjectProperty.prop_iff_of_shortExact`;
- `bridge/view`: the Artinian/Noetherian-op duality theorem below, which is the minimal bridge
  needed because mathlib does not yet provide this owner result.
-/

private theorem wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedGT (Subobject A) ↔ WellFoundedLT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedGT (Subobject A) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedGT
    exact (wellFoundedGT_dual_iff (Subobject (op A))).1 inferInstance
  · intro hA
    letI : WellFoundedLT (Subobject (op A)) := hA
    letI : WellFoundedGT ((Subobject (op A))ᵒᵈ) := inferInstance
    exact (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedGT

private theorem wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op {C : Type u}
    [Category.{v} C] [Abelian C] (A : C) :
    WellFoundedLT (Subobject A) ↔ WellFoundedGT (Subobject (op A)) := by
  constructor
  · intro hA
    letI : WellFoundedLT (Subobject A) := hA
    letI : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (Abelian.subobjectIsoSubobjectOp A).symm.toOrderEmbedding.wellFoundedLT
    exact (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
  · intro hA
    letI : WellFoundedGT (Subobject (op A)) := hA
    have : WellFoundedLT ((Subobject (op A))ᵒᵈ) :=
      (wellFoundedGT_dual_iff ((Subobject (op A))ᵒᵈ)).1 inferInstance
    letI : WellFoundedLT (Subobject A) :=
      (Abelian.subobjectIsoSubobjectOp A).toOrderEmbedding.wellFoundedLT
    exact inferInstance

theorem isNoetherianObject_iff_isArtinianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsNoetherianObject A ↔ IsArtinianObject (op A) := by
  simpa [IsNoetherianObject, ObjectProperty.is_iff, IsArtinianObject] using
    wellFoundedGT_subobject_iff_wellFoundedLT_subobject_op A

theorem isArtinianObject_iff_isNoetherianObject_op {C : Type u} [Category.{v} C]
    [Abelian C] (A : C) :
    IsArtinianObject A ↔ IsNoetherianObject (op A) := by
  simpa [IsArtinianObject, ObjectProperty.is_iff, IsNoetherianObject] using
    wellFoundedLT_subobject_iff_wellFoundedGT_subobject_op A

/-- Helper for Lemma 12.9.4: the kernel subobject in a short exact sequence is Artinian as soon
as the left term is. -/
private lemma kernel_subobject_isArtinian {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} [Mono S.f] (h₁ : isArtinianObject S.X₁) :
    isArtinianObject (Subobject.mk S.f : C) := by
  -- Transport Artinianity across the canonical isomorphism identifying the kernel subobject with
  -- the source of the monomorphism.
  simpa [ObjectProperty.is_iff] using
    (isArtinianObject.prop_iff_of_iso (Subobject.underlyingIso S.f)).2 h₁

/-- Helper for Lemma 12.9.4: a descending chain of subobjects induces a descending chain inside
the kernel subobject by taking intersections. -/
private noncomputable def kernel_inf_chain {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} [Mono S.f] (F : ℕ →o (Subobject S.X₂)ᵒᵈ) :
    ℕ →o (Subobject (Subobject.mk S.f : C))ᵒᵈ where
  toFun n :=
    (Subobject.subobjectOrderIso (Subobject.mk S.f)).symm
      ⟨(show Subobject S.X₂ from F n) ⊓ Subobject.mk S.f, by simp⟩
  monotone' := by
    intro n m hnm
    exact (Subobject.subobjectOrderIso (Subobject.mk S.f)).symm.monotone <|
      Subtype.mk_le_mk.mpr (inf_le_inf_right _ (F.2 hnm))

/-- Helper for Lemma 12.9.4: intersections of a descending chain with the kernel subobject
eventually stabilize when the left term is Artinian. -/
private lemma antitone_inf_chain_stabilizes {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} [Mono S.f] (h₁ : isArtinianObject S.X₁)
    (F : ℕ →o (Subobject S.X₂)ᵒᵈ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      (show Subobject S.X₂ from F n) ⊓ Subobject.mk S.f =
        (show Subobject S.X₂ from F m) ⊓ Subobject.mk S.f := by
  letI : IsArtinianObject (Subobject.mk S.f : C) :=
    isArtinianObject.is_of_prop (kernel_subobject_isArtinian h₁)
  -- Apply the Artinian chain condition after transporting the chain to the kernel subobject.
  obtain ⟨n, hn⟩ :=
    antitone_chain_condition_of_isArtinianObject
      (X := (Subobject.mk S.f : C)) (kernel_inf_chain F)
  refine ⟨n, ?_⟩
  intro m hm
  simpa [kernel_inf_chain] using
    congrArg Subtype.val
      (congrArg (Subobject.subobjectOrderIso (Subobject.mk S.f)) (hn m hm))

/-- Helper for Lemma 12.9.4: a descending chain of subobjects induces a descending chain of image
subobjects in the right term by composing with the quotient map. -/
private noncomputable def quotient_image_chain {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (F : ℕ →o (Subobject S.X₂)ᵒᵈ) :
    ℕ →o (Subobject S.X₃)ᵒᵈ where
  toFun n := Limits.imageSubobject ((show Subobject S.X₂ from F n).arrow ≫ S.g)
  monotone' := by
    intro n m hnm
    -- The later term of the descending chain factors through the earlier term, so its image in
    -- the quotient object is smaller.
    simpa [Category.assoc, Subobject.ofLE_arrow] using
      (Limits.imageSubobject_comp_le
        (Subobject.ofLE (show Subobject S.X₂ from F m) (show Subobject S.X₂ from F n) (F.2 hnm))
        ((show Subobject S.X₂ from F n).arrow ≫ S.g))

/-- Helper for Lemma 12.9.4: the images of a descending chain in the quotient object eventually
stabilize when the right term is Artinian. -/
private lemma antitone_image_chain_stabilizes {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (h₃ : isArtinianObject S.X₃)
    (F : ℕ →o (Subobject S.X₂)ᵒᵈ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      Limits.imageSubobject ((show Subobject S.X₂ from F n).arrow ≫ S.g) =
        Limits.imageSubobject ((show Subobject S.X₂ from F m).arrow ≫ S.g) := by
  letI : IsArtinianObject S.X₃ := isArtinianObject.is_of_prop h₃
  -- Apply the Artinian chain condition directly to the chain of image subobjects in `S.X₃`.
  exact antitone_chain_condition_of_isArtinianObject (quotient_image_chain F)

/-- Helper for Lemma 12.9.4: the intersection `P ∩ A₁` is killed by the quotient map to `A₃`. -/
private lemma inf_arrow_comp_g_eq_zero {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} [Mono S.f] (P : Subobject S.X₂) :
    (P ⊓ Subobject.mk S.f).arrow ≫ S.g = 0 := by
  -- The intersection factors through the left term of the short exact sequence, so composing
  -- with the quotient map is zero.
  rw [← Subobject.inf_comp_right P (Subobject.mk S.f), Category.assoc,
    ← Subobject.underlyingIso_hom_comp_eq_mk S.f, Category.assoc, S.zero]
  simp

/-- Helper for Lemma 12.9.4: the induced row `P ∩ A₁ ⟶ P ⟶ image(P → A₃)` is a short complex. -/
private lemma subobject_inf_image_zero {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} [Mono S.f] (P : Subobject S.X₂) :
    Subobject.ofLE (P ⊓ Subobject.mk S.f) P inf_le_left ≫
      Limits.factorThruImageSubobject (P.arrow ≫ S.g) = 0 := by
  -- After composing with the image inclusion, this is exactly the map from `P ∩ A₁` to `A₃`.
  rw [← cancel_mono (Limits.imageSubobject (P.arrow ≫ S.g)).arrow, Category.assoc,
    Limits.imageSubobject_arrow_comp]
  simpa [Category.assoc, Subobject.inf_comp_left] using inf_arrow_comp_g_eq_zero (S := S) P

/-- Helper for Lemma 12.9.4: the ambient subobject cut out by the kernel of `P → image(P → A₃)`
is exactly `P ∩ A₁`. -/
private lemma inf_eq_mk_kernel_factorThruImageSubobject {C : Type u} [Category.{v} C]
    [Abelian C] {S : ShortComplex C} (hS : S.ShortExact) [Mono S.f] (P : Subobject S.X₂) :
    P ⊓ Subobject.mk S.f =
      Subobject.mk
        ((Limits.kernelSubobject (Limits.factorThruImageSubobject (P.arrow ≫ S.g))).arrow ≫
          P.arrow) := by
  let k := Limits.factorThruImageSubobject (P.arrow ≫ S.g)
  let j : (Limits.kernelSubobject k : C) ⟶ S.X₂ := (Limits.kernelSubobject k).arrow ≫ P.arrow
  haveI : Mono j := by
    dsimp [j]
    infer_instance
  have hPkZero :
      Subobject.ofLE (P ⊓ Subobject.mk S.f) P inf_le_left ≫ k = 0 := by
    -- This is the same vanishing used to define the induced short complex on `P`.
    simpa [k] using subobject_inf_image_zero (S := S) P
  have hkZero :
      ((Limits.kernelSubobject k).arrow ≫ P.arrow) ≫ S.g = 0 := by
    -- The kernel of `k` is killed by `S.g` because `k` factors the map `P.arrow ≫ S.g`.
    calc
      ((Limits.kernelSubobject k).arrow ≫ P.arrow) ≫ S.g
          = (Limits.kernelSubobject k).arrow ≫ (P.arrow ≫ S.g) := by simp [Category.assoc]
      _ = (Limits.kernelSubobject k).arrow ≫
            (k ≫ (Limits.imageSubobject (P.arrow ≫ S.g)).arrow) := by
          rw [Limits.imageSubobject_arrow_comp]
      _ = 0 := by simp
  apply le_antisymm
  · -- The intersection factors through the kernel of the induced quotient map.
    let ψ : ((P ⊓ Subobject.mk S.f : Subobject S.X₂) : C) ⟶ (Limits.kernelSubobject k : C) :=
      Limits.factorThruKernelSubobject k
        (Subobject.ofLE (P ⊓ Subobject.mk S.f) P inf_le_left) hPkZero
    simpa using
      (Subobject.mk_le_mk_of_comm ψ (by
        calc
          ψ ≫ j = ψ ≫ (Limits.kernelSubobject k).arrow ≫ P.arrow := by rfl
          _ = (ψ ≫ (Limits.kernelSubobject k).arrow) ≫ P.arrow := by simp [Category.assoc]
          _ = Subobject.ofLE (P ⊓ Subobject.mk S.f) P inf_le_left ≫ P.arrow := by
                rw [Limits.factorThruKernelSubobject_comp_arrow]
          _ = (P ⊓ Subobject.mk S.f).arrow := by rw [Subobject.inf_comp_left]) :
        Subobject.mk ((P ⊓ Subobject.mk S.f).arrow) ≤ Subobject.mk j)
  · -- Conversely, anything in that kernel lies both in `P` and in the left term `A₁`.
    refine le_inf ?_ ?_
    · simpa using
        (Subobject.mk_le_mk_of_comm (Limits.kernelSubobject k).arrow (by simp [j, k]) :
          Subobject.mk j ≤ Subobject.mk P.arrow)
    · refine Subobject.mk_le_of_comm
        (hS.exact.lift ((Limits.kernelSubobject k).arrow ≫ P.arrow) hkZero ≫
          (Subobject.underlyingIso S.f).inv) ?_
      calc
        (hS.exact.lift ((Limits.kernelSubobject k).arrow ≫ P.arrow) hkZero ≫
            (Subobject.underlyingIso S.f).inv) ≫ (Subobject.mk S.f).arrow
            = hS.exact.lift ((Limits.kernelSubobject k).arrow ≫ P.arrow) hkZero ≫ S.f := by
                simp [Category.assoc, Subobject.underlyingIso_arrow]
        _ = (Limits.kernelSubobject k).arrow ≫ P.arrow := by
              exact hS.exact.lift_f (((Limits.kernelSubobject k).arrow ≫ P.arrow)) hkZero

/-- Helper for Lemma 12.9.4: the source-faithful row attached to a subobject of the middle term. -/
private noncomputable def subobject_inf_image_shortComplex {C : Type u} [Category.{v} C]
    [Abelian C] {S : ShortComplex C} [Mono S.f] (P : Subobject S.X₂) :
    ShortComplex C :=
  ShortComplex.mk
    (Subobject.ofLE (P ⊓ Subobject.mk S.f) P inf_le_left)
    (Limits.factorThruImageSubobject (P.arrow ≫ S.g))
    (subobject_inf_image_zero (S := S) P)

/-- Helper for Lemma 12.9.4: each subobject of the middle term fits into the short exact row
`0 ⟶ P ∩ A₁ ⟶ P ⟶ image(P → A₃) ⟶ 0`. -/
private lemma subobject_shortExact_inf_image {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) [Mono S.f] (P : Subobject S.X₂) :
    (subobject_inf_image_shortComplex (S := S) P).ShortExact := by
  let k := Limits.factorThruImageSubobject (P.arrow ≫ S.g)
  let T' : ShortComplex C := ShortComplex.mk (Limits.kernelSubobject k).arrow k
    (Limits.kernelSubobject_arrow_comp (f := k))
  have hLeft : P ⊓ Subobject.mk S.f =
      Subobject.mk ((Limits.kernelSubobject k).arrow ≫ P.arrow) := by
    -- Route correction: the left term is identified by comparing kernels in the induced row,
    -- rather than by trying to push subobjects through `S.g`.
    simpa [k] using inf_eq_mk_kernel_factorThruImageSubobject (S := S) hS P
  let e :
      subobject_inf_image_shortComplex (S := S) P ≅ T' :=
    ShortComplex.isoMk
      (Subobject.isoOfEqMk (P ⊓ Subobject.mk S.f)
        ((Limits.kernelSubobject k).arrow ≫ P.arrow) hLeft)
      (Iso.refl _)
      (Iso.refl _)
      (by
        -- The left square commutes because both composites to `S.X₂` are the same inclusion.
        apply Subobject.eq_of_comp_arrow_eq
        simp [subobject_inf_image_shortComplex, T', k, Category.assoc])
      (by
        -- The right square is tautological: both rows use the same quotient map from `P`.
        simp [subobject_inf_image_shortComplex, T', k])
  have hT' : T'.ShortExact := by
    -- The kernel subobject row is exact because its left map already identifies the kernel of `k`.
    have hExact : T'.Exact := by
      refine ShortComplex.exact_of_f_is_kernel T' ?_
      dsimp [T']
      exact Limits.kernel.isoKernel (f := k) (Limits.kernelSubobject k).arrow
        (Limits.kernelSubobjectIso k) (Limits.kernelSubobject_arrow (f := k))
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact hExact
  exact ShortComplex.shortExact_of_iso e.symm hT'

private lemma subobject_eq_of_le_of_inf_eq_of_image_eq {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) [Mono S.f] {P Q : Subobject S.X₂} (hPQ : P ≤ Q)
    (hInf : P ⊓ Subobject.mk S.f = Q ⊓ Subobject.mk S.f)
    (hImage : Limits.imageSubobject (P.arrow ≫ S.g) =
      Limits.imageSubobject (Q.arrow ≫ S.g)) : P = Q := by
  let SP := subobject_inf_image_shortComplex (S := S) P
  let SQ := subobject_inf_image_shortComplex (S := S) Q
  let eInf :=
    Subobject.isoOfEq _ _ hInf
  let eImage :=
    Subobject.isoOfEq _ _ hImage
  let φ : SP ⟶ SQ :=
    ShortComplex.homMk eInf.hom (Subobject.ofLE P Q hPQ) eImage.hom
      (by
        -- The left square commutes because both paths are the inclusion of `P ∩ A₁` into `Q`.
        apply Subobject.eq_of_comp_arrow_eq
        simp [SP, SQ, eInf, subobject_inf_image_shortComplex])
      (by
        -- The right square commutes because both paths induce the same map `P ⟶ A₃`.
        apply Subobject.eq_of_comp_arrow_eq
        simp [SP, SQ, eImage, Category.assoc, subobject_inf_image_shortComplex])
  have hSP : SP.ShortExact := by
    simpa [SP] using subobject_shortExact_inf_image (S := S) hS P
  have hSQ : SQ.ShortExact := by
    simpa [SQ] using subobject_shortExact_inf_image (S := S) hS Q
  have hIso₂ : IsIso φ.τ₂ := by
    -- The comparison map is an isomorphism once the left and right vertical maps are.
    haveI : IsIso φ.τ₁ := by
      change IsIso eInf.hom
      infer_instance
    haveI : IsIso φ.τ₃ := by
      change IsIso eImage.hom
      infer_instance
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hSP hSQ
  haveI : IsIso (Subobject.ofLE P Q hPQ) := by
    simpa [φ] using hIso₂
  -- A comparable inclusion of subobjects that is an isomorphism must be an equality.
  exact Subobject.eq_of_comm (asIso (Subobject.ofLE P Q hPQ)) (by
    exact Subobject.ofLE_arrow (X := P) (Y := Q) hPQ)

/-- Helper for Lemma 12.9.4: Artinian objects are closed under extensions in a short exact
sequence. -/
private lemma isArtinianObject_middle_of_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) (h₁ : IsArtinianObject S.X₁)
    (h₃ : IsArtinianObject S.X₃) : IsArtinianObject S.X₂ := by
  haveI : Mono S.f := hS.mono_f
  -- Reduce the Artinian statement to eventual constancy of an arbitrary descending chain.
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro F
  obtain ⟨n₁, hn₁⟩ := antitone_inf_chain_stabilizes (S := S) (isArtinianObject.prop_of_is S.X₁) F
  obtain ⟨n₃, hn₃⟩ := antitone_image_chain_stabilizes (S := S) (isArtinianObject.prop_of_is S.X₃) F
  refine ⟨max n₁ n₃, ?_⟩
  intro m hm
  let N := max n₁ n₃
  have hNm : N ≤ m := hm
  have hPQ : (show Subobject S.X₂ from F m) ≤ (show Subobject S.X₂ from F N) := F.2 hNm
  have hInfN : (show Subobject S.X₂ from F n₁) ⊓ Subobject.mk S.f =
      (show Subobject S.X₂ from F N) ⊓ Subobject.mk S.f := hn₁ N (le_max_left _ _)
  have hInfM : (show Subobject S.X₂ from F n₁) ⊓ Subobject.mk S.f =
      (show Subobject S.X₂ from F m) ⊓ Subobject.mk S.f := hn₁ m (le_trans (le_max_left _ _) hm)
  have hInf : (show Subobject S.X₂ from F m) ⊓ Subobject.mk S.f =
      (show Subobject S.X₂ from F N) ⊓ Subobject.mk S.f := by
    rw [← hInfM, hInfN]
  have hImageN : Limits.imageSubobject ((show Subobject S.X₂ from F n₃).arrow ≫ S.g) =
      Limits.imageSubobject ((show Subobject S.X₂ from F N).arrow ≫ S.g) :=
    hn₃ N (le_max_right _ _)
  have hImageM : Limits.imageSubobject ((show Subobject S.X₂ from F n₃).arrow ≫ S.g) =
      Limits.imageSubobject ((show Subobject S.X₂ from F m).arrow ≫ S.g) :=
    hn₃ m (le_trans (le_max_right _ _) hm)
  have hImage : Limits.imageSubobject ((show Subobject S.X₂ from F m).arrow ≫ S.g) =
      Limits.imageSubobject ((show Subobject S.X₂ from F N).arrow ≫ S.g) := by
    rw [← hImageM, hImageN]
  -- The chain is constant once both the kernel intersections and quotient images have stabilized.
  change (show Subobject S.X₂ from F N) = (show Subobject S.X₂ from F m)
  symm
  exact subobject_eq_of_le_of_inf_eq_of_image_eq hS hPQ hInf hImage

/-- Lemma 12.9.4 owner abstraction: in an abelian category, Artinian objects form a Serre
class. -/
instance isArtinianObject_isSerreClass {C : Type u} [Category.{v} C] [Abelian C] :
    (isArtinianObject : ObjectProperty C).IsSerreClass where
  exists_zero := ObjectProperty.ContainsZero.exists_zero
  prop_of_mono f _ hX := isArtinianObject.prop_of_mono f hX
  prop_of_epi {X} {Y} f _ hX := by
    rw [← isArtinianObject.is_iff] at hX ⊢
    letI : IsNoetherianObject (op X) :=
      (isArtinianObject_iff_isNoetherianObject_op X).mp hX
    exact (isArtinianObject_iff_isNoetherianObject_op Y).mpr
      (isNoetherianObject_of_mono f.op)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [← isArtinianObject.is_iff] at h₁ h₃ ⊢
    -- Route correction: `Subobject.map S.g` is unavailable because `S.g` is epi, not mono, so the
    -- quotient-side control is expressed via image subobjects of the composites into `S.X₃`.
    exact isArtinianObject_middle_of_shortExact hS h₁ h₃

namespace ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/-- Lemma 12.9.4: in a short exact sequence in an abelian category, the middle object is
Artinian if and only if the left and right objects are Artinian. -/
-- Proof sketch: the owner abstraction is the object property `isArtinianObject`. Once this
-- property is known to form a Serre class, the statement is the canonical owner theorem
-- `ObjectProperty.prop_iff_of_shortExact`.
lemma isArtinianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔ IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := by
  simpa [IsArtinianObject, ObjectProperty.is_iff] using
    isArtinianObject.prop_iff_of_shortExact hS

end ShortComplex
end CategoryTheory
