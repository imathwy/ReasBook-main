import StacksProject_2024.Chap12.Lemma_12_10_3
import StacksProject_2024.Chap12.Lemma_12_10_6
import StacksProject_2024.Chap12.Lemma_12_11_2
import StacksProject_2024.Chap12.«12_11_2_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open ZeroObject

universe uA vA uB vB

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

noncomputable section

section

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/- Domain-style sampling for Lemma 12.11.3:
- primary domain: Serre localizations of abelian categories, the induced maps on `K₀`, and the
  canonical `ZMod 2` cyclic cochain complex detecting kernel classes;
- sampled owner declarations:
  `AbelianK0.mapExactFunctor`,
  `toSerreQuotient_kernel_eq`,
  `toSerreQuotient_essSurj`,
  `cyclicCochainComplex`;
- owner abstractions: the inclusion `P.ι`, the quotient functor `Q := P.isoModSerre.Q`, the
  induced `K₀` maps, and the canonical owner `cyclicCochainComplex` for the `ZMod 2` complex;
- primitive data: the Serre class `P`, the exact functors `P.ι` and `Q`, and the endomorphisms
  `φ, ψ` with square-zero relations;
- derived API: exactness and surjectivity on `K₀`, plus the kernel description via homology of the
  canonical cyclic complex after passage to the Serre quotient.

Source/core/bridge triage:
- `source-facing`: the exact sequence on `K₀` and the kernel characterization in the textbook
  cyclic-complex form;
- `core/canonical`: `AbelianK0.mapExactFunctor`, `ExactFunctor.of`, `Q`,
  `Q.mapHomologicalComplex`, and
  `cyclicCochainComplex`;
- `bridge/view`: quotient-acyclicity of the cyclic complex implies that its homology objects lie in
  the Serre class. -/

local notation "Q" => P.isoModSerre.Q
local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.1

local instance : PreservesFiniteColimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.2

local instance : PreservesFiniteLimits Q :=
  (exactFunctor_iff Q).1 (toSerreQuotient_exact P) |>.1

local instance : PreservesFiniteColimits Q :=
  (exactFunctor_iff Q).1 (toSerreQuotient_exact P) |>.2

local notation "K₀ι" => AbelianK0.mapExactFunctor (ExactFunctor.of P.ι)
local notation "K₀Q" => AbelianK0.mapExactFunctor (ExactFunctor.of Q)

/-- Helper for Lemma 12.11.3: the zero object has trivial class in `K₀`. -/
lemma k0_zero_eq :
    K₀[(0 : A)] = 0 := by
  let S : ShortComplex A := ShortComplex.mk (0 : (0 : A) ⟶ 0) (0 : (0 : A) ⟶ 0) (by simp)
  -- Compute the Grothendieck relation for the zero short exact sequence and cancel one copy.
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 : K₀[(0 : A)] = K₀[(0 : A)] + K₀[(0 : A)] := by
    simpa [S] using (AbelianK0.of_shortExact S hShort)
  have hSub := congrArg (fun z : AbelianK0 A ↦ z - K₀[(0 : A)]) hK0
  have hZero : (0 : AbelianK0 A) = K₀[(0 : A)] := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 12.11.3: isomorphic objects define the same class in `K₀`. -/
lemma k0_eq_of_iso {X Y : A} (e : X ≅ Y) :
    K₀[X] = K₀[Y] := by
  let S : ShortComplex A := ShortComplex.mk e.hom (0 : Y ⟶ 0) (by simp)
  -- Route the isomorphism through the short exact sequence `0 → X → Y → 0`.
  have hExact : S.Exact := by
    exact (S.exact_iff_epi (by simp [S])).2 inferInstance
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  have hK0 := (AbelianK0.of_shortExact S hShort).symm
  rw [k0_zero_eq] at hK0
  simpa [S] using hK0

/-- Helper for Lemma 12.11.3: for any morphism, the difference of its target and source classes
is the difference of the cokernel and kernel classes. -/
lemma k0_sub_eq_cokernel_sub_kernel {X Y : A} (f : X ⟶ Y) :
    K₀[Y] - K₀[X] = K₀[cokernel f] - K₀[kernel f] := by
  let S₁ : ShortComplex A := ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (by simp)
  let T₁ : ShortComplex A := ShortComplex.mk (kernel.ι f) f (by simp)
  -- First identify `[X]` with `[ker f] + [coimage f]`.
  have hExact₁ : S₁.Exact := by
    have hT₁ : T₁.Exact := ShortComplex.exact_kernel f
    simpa [S₁, T₁] using (T₁.exact_iff_exact_coimage_π).1 hT₁
  have hShort₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' hExact₁ inferInstance inferInstance
  have h₁ : K₀[X] = K₀[kernel f] + K₀[Abelian.coimage f] := by
    simpa [S₁] using (AbelianK0.of_shortExact S₁ hShort₁)
  let S₂ : ShortComplex A := ShortComplex.mk (Abelian.image.ι f) (cokernel.π f) (by simp)
  let T₂ : ShortComplex A := ShortComplex.mk f (cokernel.π f) (by simp)
  -- Then identify `[Y]` with `[image f] + [cokernel f]`.
  have hExact₂ : S₂.Exact := by
    have hT₂ : T₂.Exact := ShortComplex.exact_cokernel f
    simpa [S₂, T₂] using (T₂.exact_iff_exact_image_ι).1 hT₂
  have hShort₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' hExact₂ inferInstance inferInstance
  have h₂ : K₀[Y] = K₀[Abelian.image f] + K₀[cokernel f] := by
    simpa [S₂] using (AbelianK0.of_shortExact S₂ hShort₂)
  have himage : K₀[Abelian.coimage f] = K₀[Abelian.image f] := by
    exact k0_eq_of_iso  (Abelian.coimageIsoImage f)
  -- Cancel the common image/coimage class after transporting across the canonical isomorphism.
  calc
    K₀[Y] - K₀[X]
        = (K₀[Abelian.image f] + K₀[cokernel f]) -
            (K₀[kernel f] + K₀[Abelian.coimage f]) := by rw [h₂, h₁]
    _ = (K₀[Abelian.image f] + K₀[cokernel f]) -
          (K₀[kernel f] + K₀[Abelian.image f]) := by rw [himage]
    _ = K₀[cokernel f] - K₀[kernel f] := by
      abel

/-- Helper for Lemma 12.11.3: the difference of two classes coming from objects of the Serre
subcategory lies in the image of the inclusion map on `K₀`. -/
lemma sub_mem_range_of_inclusion
    {X Y : A} (hX : P X) (hY : P Y) :
    K₀[X] - K₀[Y] ∈ AddMonoidHom.range K₀ι := by
  -- Use the obvious preimage represented by the corresponding difference inside the full subcategory.
  refine ⟨K₀[⟨X, hX⟩] - K₀[⟨Y, hY⟩], ?_⟩
  rw [map_sub]
  rw [AbelianK0.mapExactFunctor_apply_of, AbelianK0.mapExactFunctor_apply_of]
  rfl

/-- Helper for Lemma 12.11.3: a morphism that becomes an isomorphism modulo the Serre class
contributes a `K₀`-difference in the image of the inclusion map. -/
lemma k0_sub_mem_range_of_isoModSerre {X Y : A} (f : X ⟶ Y)
    (hf : P.isoModSerre f) :
    K₀[Y] - K₀[X] ∈ AddMonoidHom.range K₀ι := by
  rcases (P.isoModSerre_iff f).1 hf with ⟨hmono, hepi⟩
  -- Rewrite the `K₀`-difference through kernel and cokernel, which both lie in `P`.
  rw [k0_sub_eq_cokernel_sub_kernel]
  exact sub_mem_range_of_inclusion (P := P) hepi hmono

/-- Helper for Lemma 12.11.3: objects that become isomorphic in the Serre quotient differ by a
class coming from the Serre subcategory. -/
lemma k0_sub_mem_range_of_quotient_iso {X Y : A}
    (e : (P.isoModSerre.Q).obj X ≅ (P.isoModSerre.Q).obj Y) :
    K₀[Y] - K₀[X] ∈ AddMonoidHom.range K₀ι := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q P.isoModSerre e.hom
  have hs : IsIso ((P.isoModSerre.Q).map φ.s) := Localization.inverts Q P.isoModSerre φ.s φ.hs
  have hmapf : e.hom ≫ (P.isoModSerre.Q).map φ.s = (P.isoModSerre.Q).map φ.f := by
    simpa [hφ] using MorphismProperty.LeftFraction.map_comp_map_s φ Q
      (Localization.inverts Q P.isoModSerre)
  have hfMap : IsIso ((P.isoModSerre.Q).map φ.f) := by
    rw [← hmapf]
    infer_instance
  have hf : P.isoModSerre φ.f := (isIso_map_iff Q P φ.f).1 hfMap
  have hY : K₀[φ.Y'] - K₀[Y] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_isoModSerre (P := P) φ.s φ.hs
  have hX : K₀[φ.Y'] - K₀[X] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_isoModSerre (P := P) φ.f hf
  have hdiff :
      (K₀[φ.Y'] - K₀[X]) - (K₀[φ.Y'] - K₀[Y]) ∈ AddMonoidHom.range K₀ι :=
    sub_mem hX hY
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff

/-- Helper for Lemma 12.11.3: the class of a binary biproduct is the sum of the two summand
classes in `K₀`. -/
lemma k0_biprod_eq_add (X Y : A) :
    K₀[X ⊞ Y] = K₀[X] + K₀[Y] := by
  let S : ShortComplex A :=
    ShortComplex.mk
      (biprod.inl : X ⟶ X ⊞ Y)
      (biprod.snd : X ⊞ Y ⟶ Y)
      (by simp)
  let s : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct X Y
  have hShort : S.ShortExact := s.shortExact
  simpa [S] using (AbelianK0.of_shortExact S hShort)

/-- Helper for Lemma 12.11.3: every `K₀`-class is a difference `[X] - [Y]` of two object classes.
-/
lemma exists_object_sub_eq_of_k0 (x : AbelianK0 A) :
    ∃ X Y : A, x = K₀[X] - K₀[Y] := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
      induction z using FreeAbelianGroup.induction_on with
      | zero =>
          -- Represent the zero class by `[0] - [0]`.
          refine ⟨0, 0, ?_⟩
          rw [k0_zero_eq]
          abel
      | of X =>
          -- A generator is `[X] - [0]`.
          refine ⟨X, 0, ?_⟩
          rw [k0_zero_eq]
          abel
      | neg X _ =>
          -- The negative of a generator is `[0] - [X]`.
          refine ⟨0, X, ?_⟩
          rw [k0_zero_eq]
          abel
      | add a b ha hb =>
          rcases ha with ⟨X₁, Y₁, h₁⟩
          rcases hb with ⟨X₂, Y₂, h₂⟩
          refine ⟨X₁ ⊞ X₂, Y₁ ⊞ Y₂, ?_⟩
          -- Combine the two difference representatives by the split biproduct exact sequences.
          have hmk :
              ((a + b : FreeAbelianGroup A) : AbelianK0 A) =
                (a : AbelianK0 A) + (b : AbelianK0 A) := by
            simpa using (QuotientAddGroup.mk' (AbelianK0.relations A)).map_add a b
          rw [hmk, h₁, h₂]
          calc
            (K₀[X₁] - K₀[Y₁]) + (K₀[X₂] - K₀[Y₂])
                = (K₀[X₁] + K₀[X₂]) - (K₀[Y₁] + K₀[Y₂]) := by
                    abel
            _ = K₀[X₁ ⊞ X₂] - K₀[Y₁ ⊞ Y₂] := by
                  rw [← k0_biprod_eq_add  X₁ X₂, ← k0_biprod_eq_add  Y₁ Y₂]

/-- Helper for Lemma 12.11.3: the composite `K₀(\mathcal C) → K₀(\mathcal A) → K₀(\mathcal A /
\mathcal C)` is zero. -/
lemma k0_quotient_comp_inclusion_eq_zero :
    AddMonoidHom.comp K₀Q K₀ι =
      (0 : AbelianK0 P.FullSubcategory →+ AbelianK0 P.isoModSerre.Localization) := by
  ext X
  have hzero : IsZero ((Q).obj X.1) := by
    exact (isZero_obj_iff Q P X.1).2 X.2
  -- Every object of `P` becomes zero in the Serre quotient.
  change K₀[(Q).obj X.1] = 0
  rw [k0_eq_of_iso (A := P.isoModSerre.Localization) hzero.isoZero, k0_zero_eq]

/-- Helper for Lemma 12.11.3: the raw preimage map to
`AbelianK0 A ⧸ AddMonoidHom.range K₀ι` kills the short-exact generators in the Serre quotient. -/
lemma preimage_generator_zero_mod_serre_range
    (π : AbelianK0 A →+ AbelianK0 A ⧸ AddMonoidHom.range K₀ι)
    (hπ_range : AddMonoidHom.range K₀ι ≤ π.ker)
    (preimageFG : FreeAbelianGroup P.isoModSerre.Localization →+
      (AbelianK0 A ⧸ AddMonoidHom.range K₀ι))
    (hpreimageFG :
      ∀ X : P.isoModSerre.Localization,
        preimageFG (FreeAbelianGroup.of X) = π K₀[(P.isoModSerre.Q).objPreimage X])
    (S : ShortComplex P.isoModSerre.Localization) (hS : S.ShortExact) :
    preimageFG
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0 := by
  letI : Functor.EssSurj ((P.isoModSerre.Q).mapArrow) := Localization.essSurj_mapArrow Q P.isoModSerre
  obtain ⟨f, ⟨e⟩⟩ := (Localization.essSurj_mapArrow Q P.isoModSerre).mem_essImage (Arrow.mk S.f)
  let e₁ : (Q).obj f.left ≅ S.X₁ := Arrow.leftFunc.mapIso e
  let e₂ : (Q).obj f.right ≅ S.X₂ := Arrow.rightFunc.mapIso e
  have hmapf : (P.isoModSerre.Q).map f.hom ≫ e₂.hom = e₁.hom ≫ S.f := by
    simpa [e₁, e₂] using (Arrow.w e.hom).symm
  have hmonoMap : Mono ((P.isoModSerre.Q).map f.hom) := by
    haveI : Mono S.f := hS.mono_f
    have hcomp : (P.isoModSerre.Q).map f.hom = e₁.hom ≫ S.f ≫ e₂.inv := by
      apply (cancel_mono e₂.hom).1
      simpa [Category.assoc] using hmapf
    have : Mono (e₁.hom ≫ S.f ≫ e₂.inv) := by infer_instance
    simpa [hcomp]
  have hkernel : P (kernel f.hom) := (mono_map_iff Q P f.hom).1 hmonoMap
  have hkernel_range : K₀[kernel f.hom] ∈ AddMonoidHom.range K₀ι := by
    have hkernel_sub :
        K₀[kernel f.hom] - K₀[(0 : A)] ∈ AddMonoidHom.range K₀ι :=
      sub_mem_range_of_inclusion (P := P) hkernel P.prop_zero
    simpa [k0_zero_eq (A := A)] using hkernel_sub
  have hkernel_pi : π K₀[kernel f.hom] = 0 := hπ_range hkernel_range
  let cofork : CokernelCofork ((P.isoModSerre.Q).map f.hom) :=
    CokernelCofork.ofπ (e₂.hom ≫ S.g) (by
      calc
        (P.isoModSerre.Q).map f.hom ≫ (e₂.hom ≫ S.g) =
            ((P.isoModSerre.Q).map f.hom ≫ e₂.hom) ≫ S.g := by
          rw [Category.assoc]
        _ = (e₁.hom ≫ S.f) ≫ S.g := by
          rw [hmapf]
        _ = 0 := by simpa [Category.assoc] using congrArg (e₁.hom ≫ ·) S.zero)
  have hcofork : IsColimit cofork := by
    exact IsCokernel.ofIso S.f hS.gIsCokernel cofork e₁.symm e₂.symm (Iso.refl _)
      (by simpa [e₁, e₂] using Arrow.w e.inv) (by simp [cofork])
  let e₃ : (Q).obj (cokernel f.hom) ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso
      ((CokernelCofork.isColimitMapCoconeEquiv
          (CokernelCofork.ofπ (cokernel.π f.hom) (cokernel.condition f.hom)) Q).1
        (isColimitOfPreserves Q (cokernelIsCokernel f.hom)))
      hcofork
  have hπ₂_range :
      K₀[f.right] - K₀[(Q).objPreimage S.X₂] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_quotient_iso (P := P)
      ((Q).objObjPreimageIso S.X₂ ≪≫ e₂.symm)
  have hπ₁_range :
      K₀[f.left] - K₀[(Q).objPreimage S.X₁] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_quotient_iso (P := P)
      ((Q).objObjPreimageIso S.X₁ ≪≫ e₁.symm)
  have hπ₃_range :
      K₀[cokernel f.hom] - K₀[(Q).objPreimage S.X₃] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_quotient_iso (P := P)
      ((Q).objObjPreimageIso S.X₃ ≪≫ e₃.symm)
  have hπ₂ :
      π K₀[f.right] = π K₀[(Q).objPreimage S.X₂] := by
    have hzero : π (K₀[f.right] - K₀[(Q).objPreimage S.X₂]) = 0 := hπ_range hπ₂_range
    exact sub_eq_zero.mp (by simpa [map_sub] using hzero)
  have hπ₁ :
      π K₀[f.left] = π K₀[(Q).objPreimage S.X₁] := by
    have hzero : π (K₀[f.left] - K₀[(Q).objPreimage S.X₁]) = 0 := hπ_range hπ₁_range
    exact sub_eq_zero.mp (by simpa [map_sub] using hzero)
  have hπ₃ :
      π K₀[cokernel f.hom] = π K₀[(Q).objPreimage S.X₃] := by
    have hzero : π (K₀[cokernel f.hom] - K₀[(Q).objPreimage S.X₃]) = 0 := hπ_range hπ₃_range
    exact sub_eq_zero.mp (by simpa [map_sub] using hzero)
  have hk0f :
      π K₀[cokernel f.hom] = π (K₀[f.right] - K₀[f.left]) := by
    have hrel := congrArg π (k0_sub_eq_cokernel_sub_kernel (A := A) f.hom)
    have hk0f' : π (K₀[f.right] - K₀[f.left]) = π K₀[cokernel f.hom] := by
      have hrel' : π (K₀[f.right] - K₀[f.left]) =
          π K₀[cokernel f.hom] - π K₀[kernel f.hom] := by
        simpa [map_sub] using hrel
      rw [hkernel_pi, sub_zero] at hrel'
      exact hrel'
    exact hk0f'.symm
  calc
    preimageFG
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃)
        = π K₀[(Q).objPreimage S.X₂] - π K₀[(Q).objPreimage S.X₁] -
            π K₀[(Q).objPreimage S.X₃] := by
              simp [hpreimageFG, map_sub]
    _ = π K₀[f.right] - π K₀[f.left] - π K₀[cokernel f.hom] := by
          rw [← hπ₂, ← hπ₁, ← hπ₃]
    _ = π (K₀[f.right] - K₀[f.left]) - π K₀[cokernel f.hom] := by
          rw [map_sub]
    _ = 0 := by
          rw [← hk0f]
          abel

-- Proof sketch: combine the exactness of the inclusion and quotient functors with the universal
-- property of `K₀` from `AbelianK0.mapExactFunctor`; exactness at `K₀(A)` comes from the quotient-kernel
-- description of the Serre localization, and surjectivity follows from essential surjectivity of
-- `toSerreQuotient_essSurj P`.
/-- First assertion of Lemma 12.11.3: the inclusion `\mathcal C \to \mathcal A` and the quotient functor
`\mathcal A \to \mathcal A / \mathcal C` induce an exact sequence
`K₀(\mathcal C) → K₀(\mathcal A) → K₀(\mathcal A / \mathcal C) → 0`. -/
@[stacks 02MX]
theorem serreClassK0_exactSequence :
    Function.Exact K₀ι K₀Q ∧ Function.Surjective K₀Q := by
  let π : AbelianK0 A →+ AbelianK0 A ⧸ AddMonoidHom.range K₀ι :=
    QuotientAddGroup.mk' (AddMonoidHom.range K₀ι)
  have hπ_range : AddMonoidHom.range K₀ι ≤ π.ker := by
    intro x hx
    exact (QuotientAddGroup.eq_zero_iff x).2 hx
  let preimageFG : FreeAbelianGroup P.isoModSerre.Localization →+
      (AbelianK0 A ⧸ AddMonoidHom.range K₀ι) :=
    FreeAbelianGroup.lift fun X ↦ π K₀[(Q).objPreimage X]
  have hpreimageFG :
      ∀ X : P.isoModSerre.Localization,
        preimageFG (FreeAbelianGroup.of X) = π K₀[(Q).objPreimage X] := by
    intro X
    simp [preimageFG]
  have hpreimage_rel :
      AbelianK0.relations P.isoModSerre.Localization ≤ preimageFG.ker := by
    rw [AbelianK0.relations, AddSubgroup.closure_le]
    rintro _ ⟨S, rfl⟩
    exact preimage_generator_zero_mod_serre_range (P := P) π hπ_range preimageFG hpreimageFG
      S.1 S.2
  let preimageK0 : AbelianK0 P.isoModSerre.Localization →+
      (AbelianK0 A ⧸ AddMonoidHom.range K₀ι) :=
    AbelianK0.lift (fun X ↦ π K₀[(Q).objPreimage X]) hpreimage_rel
  have hpreimage_obj (X : A) : preimageK0 K₀[(Q).obj X] = π K₀[X] := by
    change π K₀[(Q).objPreimage ((Q).obj X)] = π K₀[X]
    have hrange :
        K₀[X] - K₀[(Q).objPreimage ((Q).obj X)] ∈ AddMonoidHom.range K₀ι :=
      k0_sub_mem_range_of_quotient_iso (P := P) ((Q).objObjPreimageIso ((Q).obj X))
    have hzero : π K₀[X] - π K₀[(Q).objPreimage ((Q).obj X)] = 0 := by
      simpa [map_sub] using (hπ_range hrange : π (K₀[X] - K₀[(Q).objPreimage ((Q).obj X)]) = 0)
    exact (sub_eq_zero.mp hzero).symm
  have hpreimage_apply (x : AbelianK0 A) : preimageK0 (K₀Q x) = π x := by
    rcases exists_object_sub_eq_of_k0 (A := A) x with ⟨X, Y, rfl⟩
    change preimageK0 (K₀[(Q).obj X] - K₀[(Q).obj Y]) = π (K₀[X] - K₀[Y])
    rw [map_sub, hpreimage_obj, hpreimage_obj, map_sub]
  have hsurj : Function.Surjective K₀Q := by
    intro y
    rcases exists_object_sub_eq_of_k0 (A := P.isoModSerre.Localization) y with ⟨X, Y, rfl⟩
    refine ⟨K₀[(Q).objPreimage X] - K₀[(Q).objPreimage Y], ?_⟩
    rw [map_sub, AbelianK0.mapExactFunctor_apply_of, AbelianK0.mapExactFunctor_apply_of]
    simpa using congrArg₂ (fun a b ↦ a - b)
      (k0_eq_of_iso (A := P.isoModSerre.Localization) ((Q).objObjPreimageIso X))
      (k0_eq_of_iso (A := P.isoModSerre.Localization) ((Q).objObjPreimageIso Y))
  refine ⟨?_, hsurj⟩
  intro x
  constructor
  · intro hx
    have hzero : π x = 0 := by
      rw [← hpreimage_apply x, hx]
      simp [preimageK0]
    exact (QuotientAddGroup.eq_zero_iff x).1 hzero
  · rintro ⟨y, rfl⟩
    change (AddMonoidHom.comp K₀Q K₀ι) y = 0
    simpa using congrArg
      (fun f : AbelianK0 P.FullSubcategory →+ AbelianK0 P.isoModSerre.Localization ↦ f y)
      (k0_quotient_comp_inclusion_eq_zero (P := P))

-- Proof sketch: this is the owner `mapHomologyIso` specialized to the Serre quotient functor `Q`;
-- naming it keeps the later quotient-acyclicity proof on the source route instead of repeating the
-- transport calculation inline.
/-- Helper for Lemma 12.11.3: passing a complex to the Serre quotient commutes with taking
homology at a fixed degree. -/
abbrev quotient_homology_iso
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex A c) (i : ι) :
    ((((Q).mapHomologicalComplex c).obj K).homology i) ≅ (P.isoModSerre.Q).obj (K.homology i) :=
  -- Specialize the canonical homology comparison for the short complex at degree `i`.
  (K.sc i).mapHomologyIso Q

-- Proof sketch: apply the Serre-kernel criterion to the homology object of a complex `K`. If the
-- image of `K` in the Serre quotient is acyclic, then its `i`-th homology vanishes after
-- applying `Q`, so `K.homology i` lies in the kernel of `Q`, which is exactly `P`.
/-- If a homological complex becomes acyclic in the Serre quotient, then each of its homology
objects belongs to the Serre class. -/
theorem homology_mem_of_quotientAcyclic
    {ι : Type*} (c : ComplexShape ι) {K : HomologicalComplex A c}
    (hK : (((Q).mapHomologicalComplex c).obj K).Acyclic) (i : ι) :
    P (K.homology i) := by
  -- Rewrite acyclicity as exactness at degree `i`, so the mapped homology object is zero.
  rw [HomologicalComplex.acyclic_iff] at hK
  have hzero_mapped :
      IsZero ((((Q).mapHomologicalComplex c).obj K).homology i) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK i
  have hzero_obj : IsZero ((P.isoModSerre.Q).obj (K.homology i)) := by
    -- Compare the homology of the mapped complex with the image of the original homology object.
    exact hzero_mapped.of_iso (quotient_homology_iso P c K i).symm
  exact (isZero_obj_iff P.isoModSerre.Q P (K.homology i)).1 hzero_obj

/-- Helper for Lemma 12.11.3: composing a kernel map with the canonical lift into `kernel f`
realizes `kernel g` as a kernel of `kernel.lift f g h`, so the two kernels have the same `K₀`
class. -/
lemma k0_kernel_of_kernel_lift
    {X Y Z : A} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[kernel (kernel.lift f g h)] = K₀[kernel g] := by
  let e₁ :
      kernel g ≅ kernel ((kernel.lift f g h) ≫ kernel.ι f) :=
    kernel.congr g ((kernel.lift f g h) ≫ kernel.ι f) (by simp)
  let e₂ :
      kernel ((kernel.lift f g h) ≫ kernel.ι f) ≅ kernel (kernel.lift f g h) :=
    kernelCompMono (kernel.lift f g h) (kernel.ι f)
  -- The lift into `kernel f` has the same kernel as `g`, because `kernel.ι f` is mono.
  exact k0_eq_of_iso (A := A) (e₁ ≪≫ e₂).symm

/-- Helper for Lemma 12.11.3: the two homology objects of the canonical cyclic cochain complex
have the same image in `K₀(A)`. -/
lemma cyclic_homology_classes_cancel
    {M : A} (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    K₀[K.homology 0] - K₀[K.homology 1] = 0 := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  have hprev0 : (up (ZMod 2)).prev 0 = 1 :=
    ComplexShape.prev_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  have hnext0 : (up (ZMod 2)).next 0 = 1 :=
    ComplexShape.next_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  have hprev1 : (up (ZMod 2)).prev 1 = 0 :=
    ComplexShape.prev_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  have hnext1 : (up (ZMod 2)).next 1 = 0 :=
    ComplexShape.next_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  have hd0 : K.d 0 1 = φ := by
    simpa [K] using cyclicCochainComplex_d_zero (φ := φ) (ψ := ψ) hφψ hψφ
  have hd1 : K.d 1 0 = ψ := by
    simpa [K] using cyclicCochainComplex_d_one (φ := φ) (ψ := ψ) hφψ hψφ
  let α := kernel.lift (K.d 0 1) (K.d 1 0) (by
    simpa [hd0, hd1] using hψφ)
  let β := kernel.lift (K.d 1 0) (K.d 0 1) (by
    simpa [hd0, hd1] using hφψ)
  have hk₀raw :
      K₀[K.homology 0] = K₀[cokernel α] := by
    simpa using
      k0_eq_of_iso (A := A)
        (K.homologyIsoSc' 1 0 1 hprev0 hnext0 ≪≫
          (K.sc' 1 0 1).homologyIsoCokernelLift)
  have hk₁raw :
      K₀[K.homology 1] = K₀[cokernel β] := by
    simpa using
      k0_eq_of_iso (A := A)
        (K.homologyIsoSc' 0 1 0 hprev1 hnext1 ≪≫
          (K.sc' 0 1 0).homologyIsoCokernelLift)
  have hα :
      K₀[cokernel α] - K₀[kernel (K.d 1 0)] =
        K₀[kernel (K.d 0 1)] - K₀[M] := by
    have hα' :
        K₀[cokernel α] - K₀[kernel α] =
          K₀[kernel (K.d 0 1)] - K₀[K.X 1] := by
      simpa [α] using (k0_sub_eq_cokernel_sub_kernel (A := A) α).symm
    rw [k0_kernel_of_kernel_lift (A := A) (f := K.d 0 1) (g := K.d 1 0)
      (h := by simpa [hd0, hd1] using hψφ)] at hα'
    simpa [K] using hα'
  have hβ :
      K₀[cokernel β] - K₀[kernel (K.d 0 1)] =
        K₀[kernel (K.d 1 0)] - K₀[M] := by
    have hβ' :
        K₀[cokernel β] - K₀[kernel β] =
          K₀[kernel (K.d 1 0)] - K₀[K.X 0] := by
      simpa [β] using (k0_sub_eq_cokernel_sub_kernel (A := A) β).symm
    rw [k0_kernel_of_kernel_lift (A := A) (f := K.d 1 0) (g := K.d 0 1)
      (h := by simpa [hd0, hd1] using hφψ)] at hβ'
    simpa [K] using hβ'
  have hcoker :
      K₀[cokernel α] = K₀[cokernel β] := by
    calc
      K₀[cokernel α]
          = (K₀[cokernel α] - K₀[kernel (K.d 1 0)]) + K₀[kernel (K.d 1 0)] := by
              abel
      _ = (K₀[kernel (K.d 0 1)] - K₀[M]) + K₀[kernel (K.d 1 0)] := by
            rw [hα]
      _ = (K₀[cokernel β] - K₀[kernel (K.d 0 1)]) + K₀[kernel (K.d 0 1)] := by
            rw [hβ]
            abel
      _ = K₀[cokernel β] := by
            abel
  change K₀[K.homology 0] - K₀[K.homology 1] = 0
  rw [hk₀raw, hk₁raw, hcoker]
  abel

/-- Helper for Lemma 12.11.3: the formal sum of a list of objects in the free abelian group. -/
abbrev fg_list (l : List A) : FreeAbelianGroup A :=
  List.sum (l.map FreeAbelianGroup.of)

omit [Category.{vA} A] [Abelian A] in
/-- Helper for Lemma 12.11.3: the formal sum attached to an appended list is additive. -/
lemma fg_list_append (l₁ l₂ : List A) :
    fg_list (l₁ ++ l₂) = fg_list l₁ + fg_list l₂ := by
  -- Expand the appended list and collect the two partial sums.
  simp [fg_list, List.map_append, List.sum_append]

omit [Category.{vA} A] [Abelian A] in
/-- Helper for Lemma 12.11.3: the coefficient of an object in `fg_list l` is its multiplicity in
`l`. -/
lemma coeff_fg_list [DecidableEq A] (X : A) (l : List A) :
    FreeAbelianGroup.coeff X (fg_list l) = l.count X := by
  induction l with
  | nil =>
      -- The empty list has zero coefficient at every object.
      simp [fg_list, FreeAbelianGroup.coeff]
  | cons Y ys ih =>
      -- Split off the head and use the recursive count formula on the tail.
      by_cases h : X = Y
      · subst h
        have hsucc := congrArg (fun n : ℤ ↦ 1 + n) ih
        simpa [fg_list, FreeAbelianGroup.coeff, Int.add_comm] using hsucc
      · rw [List.count_cons]
        have h' : ¬Y = X := by
          intro hYX
          exact h hYX.symm
        simpa [fg_list, FreeAbelianGroup.coeff, h'] using ih

omit [Category.{vA} A] [Abelian A] in
/-- Helper for Lemma 12.11.3: equality of two positive formal sums gives a permutation of the
underlying lists. -/
lemma list_perm_of_fg_list_eq {l₁ l₂ : List A}
    (h : fg_list l₁ = fg_list l₂) :
    l₁.Perm l₂ := by
  classical
  -- Compare coefficients objectwise and invoke the standard count criterion for permutations.
  refine List.perm_iff_count.2 ?_
  intro X
  have hcoeff := congrArg (FreeAbelianGroup.coeff X) h
  simpa [coeff_fg_list] using hcoeff

/-- Helper for Lemma 12.11.3: the Grothendieck relation contributed by a short exact sequence. -/
abbrev short_exact_relation (S : { T : ShortComplex A // T.ShortExact }) :
    FreeAbelianGroup A :=
  FreeAbelianGroup.of S.1.X₂ - FreeAbelianGroup.of S.1.X₁ - FreeAbelianGroup.of S.1.X₃

/-- Helper for Lemma 12.11.3: the source proof's `T⁺` tail terms attached to signed short exact
data. -/
def signed_plus_terms
    (positiveSeqs negativeSeqs : List { T : ShortComplex A // T.ShortExact }) : List A :=
  (positiveSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
    (negativeSeqs.map fun S ↦ S.1.X₂)

/-- Helper for Lemma 12.11.3: the source proof's `T⁻` tail terms attached to signed short exact
data. -/
def signed_minus_terms
    (positiveSeqs negativeSeqs : List { T : ShortComplex A // T.ShortExact }) : List A :=
  (negativeSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
    (positiveSeqs.map fun S ↦ S.1.X₂)

/-- Helper for Lemma 12.11.3: concatenating two signed short exact blocks adds the formal sum of
their `T⁺` tails. -/
lemma fg_list_signed_plus_terms_append
    (positive₁ positive₂ negative₁ negative₂ : List { T : ShortComplex A // T.ShortExact }) :
    fg_list  (signed_plus_terms  (positive₁ ++ positive₂) (negative₁ ++ negative₂)) =
      fg_list  (signed_plus_terms  positive₁ negative₁) +
        fg_list  (signed_plus_terms  positive₂ negative₂) := by
  -- The two positive-endpoint blocks and two negative-middle blocks contribute additively.
  simp [fg_list, signed_plus_terms, List.flatMap_append, List.map_append, List.sum_append]
  abel

/-- Helper for Lemma 12.11.3: concatenating two signed short exact blocks adds the formal sum of
their `T⁻` tails. -/
lemma fg_list_signed_minus_terms_append
    (positive₁ positive₂ negative₁ negative₂ : List { T : ShortComplex A // T.ShortExact }) :
    fg_list  (signed_minus_terms  (positive₁ ++ positive₂) (negative₁ ++ negative₂)) =
      fg_list  (signed_minus_terms  positive₁ negative₁) +
        fg_list  (signed_minus_terms  positive₂ negative₂) := by
  -- The same additive decomposition holds for the negative tail.
  simp [fg_list, signed_minus_terms, List.flatMap_append, List.map_append, List.sum_append]
  abel

/-- Helper for Lemma 12.11.3: the closure-induction bookkeeping package for a formal relation in
the free abelian group. -/
structure SignedShortExactAccumulator (r : FreeAbelianGroup A) where
  positiveSeqs : List { T : ShortComplex A // T.ShortExact }
  negativeSeqs : List { T : ShortComplex A // T.ShortExact }
  difference_eq :
    fg_list  (signed_minus_terms  positiveSeqs negativeSeqs) -
      fg_list  (signed_plus_terms  positiveSeqs negativeSeqs) = r

/-- Helper for Lemma 12.11.3: the empty signed short exact accumulator represents the zero
relation. -/
lemma empty_signed_short_exact_accumulator_difference :
    fg_list (signed_minus_terms ([] : List { T : ShortComplex A // T.ShortExact }) []) -
      fg_list (signed_plus_terms ([] : List { T : ShortComplex A // T.ShortExact }) []) =
        (0 : FreeAbelianGroup A) := by
  -- With no short exact sequences, both source-proof tails are empty.
  simp [fg_list, signed_plus_terms, signed_minus_terms]

/-- Helper for Lemma 12.11.3: the zero relation has the empty signed short exact accumulator. -/
abbrev empty_signed_short_exact_accumulator :
    SignedShortExactAccumulator (0 : FreeAbelianGroup A) :=
  { positiveSeqs := ([] : List { T : ShortComplex A // T.ShortExact })
    negativeSeqs := ([] : List { T : ShortComplex A // T.ShortExact })
    difference_eq := empty_signed_short_exact_accumulator_difference  }

/-- Helper for Lemma 12.11.3: a single positive short exact sequence realizes its Grothendieck
relation in the accumulator formalism. -/
lemma singleton_positive_signed_short_exact_accumulator_difference
    (S : { T : ShortComplex A // T.ShortExact }) :
    fg_list  (signed_minus_terms  [S] []) -
      fg_list  (signed_plus_terms  [S] []) =
        short_exact_relation  S := by
  -- The positive generator contributes `X₂ - X₁ - X₃`.
  simp [fg_list, short_exact_relation, signed_plus_terms, signed_minus_terms]
  abel

/-- Helper for Lemma 12.11.3: a single positive short exact sequence realizes its Grothendieck
relation in the accumulator formalism. -/
abbrev singleton_positive_signed_short_exact_accumulator
    (S : { T : ShortComplex A // T.ShortExact }) :
    SignedShortExactAccumulator  (short_exact_relation  S) :=
  { positiveSeqs := [S]
    negativeSeqs := []
    difference_eq := singleton_positive_signed_short_exact_accumulator_difference  S }

/-- Helper for Lemma 12.11.3: swapping positive and negative data negates the represented
relation. -/
lemma swap_signed_short_exact_accumulator_difference
    {r : FreeAbelianGroup A} (w : SignedShortExactAccumulator r) :
    fg_list (signed_minus_terms w.negativeSeqs w.positiveSeqs) -
      fg_list (signed_plus_terms w.negativeSeqs w.positiveSeqs) = -r := by
  -- Swapping the two source-proof sides reverses the formal difference.
  calc
    fg_list  (signed_minus_terms  w.negativeSeqs w.positiveSeqs) -
        fg_list  (signed_plus_terms  w.negativeSeqs w.positiveSeqs)
        =
          fg_list  (signed_plus_terms  w.positiveSeqs w.negativeSeqs) -
            fg_list  (signed_minus_terms  w.positiveSeqs w.negativeSeqs) := by
              simp [signed_plus_terms, signed_minus_terms]
    _ = -(fg_list  (signed_minus_terms  w.positiveSeqs w.negativeSeqs) -
            fg_list  (signed_plus_terms  w.positiveSeqs w.negativeSeqs)) := by
              abel
    _ = -r := by rw [w.difference_eq]

/-- Helper for Lemma 12.11.3: swapping positive and negative data negates the represented
relation. -/
abbrev swap_signed_short_exact_accumulator
    {r : FreeAbelianGroup A} (w : SignedShortExactAccumulator r) :
    SignedShortExactAccumulator  (-r) :=
  { positiveSeqs := w.negativeSeqs
    negativeSeqs := w.positiveSeqs
    difference_eq := swap_signed_short_exact_accumulator_difference  w }

/-- Helper for Lemma 12.11.3: concatenating two accumulators adds their represented relations. -/
lemma append_signed_short_exact_accumulator_difference
    {r₁ r₂ : FreeAbelianGroup A}
    (w₁ : SignedShortExactAccumulator r₁)
    (w₂ : SignedShortExactAccumulator r₂) :
    fg_list 
        (signed_minus_terms 
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) -
      fg_list 
        (signed_plus_terms 
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) = r₁ + r₂ := by
  -- Concatenate the two source-proof blocks and then collect the two represented relations.
  calc
    fg_list 
        (signed_minus_terms 
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) -
        fg_list 
          (signed_plus_terms 
            (w₁.positiveSeqs ++ w₂.positiveSeqs)
            (w₁.negativeSeqs ++ w₂.negativeSeqs))
        =
          (fg_list  (signed_minus_terms  w₁.positiveSeqs w₁.negativeSeqs) +
              fg_list  (signed_minus_terms  w₂.positiveSeqs w₂.negativeSeqs)) -
            (fg_list  (signed_plus_terms  w₁.positiveSeqs w₁.negativeSeqs) +
              fg_list  (signed_plus_terms  w₂.positiveSeqs w₂.negativeSeqs)) := by
                rw [fg_list_signed_minus_terms_append, fg_list_signed_plus_terms_append]
    _ =
          (fg_list  (signed_minus_terms  w₁.positiveSeqs w₁.negativeSeqs) -
              fg_list  (signed_plus_terms  w₁.positiveSeqs w₁.negativeSeqs)) +
            (fg_list  (signed_minus_terms  w₂.positiveSeqs w₂.negativeSeqs) -
              fg_list  (signed_plus_terms  w₂.positiveSeqs w₂.negativeSeqs)) := by
                abel
    _ = r₁ + r₂ := by rw [w₁.difference_eq, w₂.difference_eq]

/-- Helper for Lemma 12.11.3: concatenating two accumulators adds their represented relations. -/
abbrev append_signed_short_exact_accumulator
    {r₁ r₂ : FreeAbelianGroup A}
    (w₁ : SignedShortExactAccumulator r₁)
    (w₂ : SignedShortExactAccumulator r₂) :
    SignedShortExactAccumulator (r₁ + r₂) :=
  { positiveSeqs := w₁.positiveSeqs ++ w₂.positiveSeqs
    negativeSeqs := w₁.negativeSeqs ++ w₂.negativeSeqs
    difference_eq := append_signed_short_exact_accumulator_difference  w₁ w₂ }

/-- Helper for Lemma 12.11.3: a kernel class `x = [P₀] - [Q₀]` yields the corresponding
free-abelian-group relation witness. -/
lemma relation_of_mem_ker_inclusion
    {x : AbelianK0 P.FullSubcategory} {P₀ Q₀ : P.FullSubcategory}
    (hx : x = K₀[P₀] - K₀[Q₀]) (hker : x ∈ (K₀ι).ker) :
    FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1 ∈ AbelianK0.relations A := by
  -- Rewrite the kernel condition as vanishing of the displayed difference in `AbelianK0 A`.
  rw [AddMonoidHom.mem_ker] at hker
  rw [hx, map_sub, AbelianK0.mapExactFunctor_apply_of, AbelianK0.mapExactFunctor_apply_of] at hker
  change
    QuotientAddGroup.mk' (AbelianK0.relations A)
      (FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1) = 0 at hker
  exact (QuotientAddGroup.eq_zero_iff _).1 hker

/-- Helper for Lemma 12.11.3: closure induction produces signed short exact bookkeeping for any
formal relation in `AbelianK0.relations A`. -/
theorem exists_signed_short_exact_accumulator_of_relation
    {r : FreeAbelianGroup A} (hr : r ∈ AbelianK0.relations A) :
    Nonempty (SignedShortExactAccumulator  r) := by
  -- Route correction: closure induction only needs the weak accumulator invariant, not the final
  -- balance isomorphism between the two ordered sums.
  rw [AbelianK0.relations] at hr
  induction hr using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨S, rfl⟩
      exact ⟨singleton_positive_signed_short_exact_accumulator  S⟩
  | zero =>
      exact ⟨empty_signed_short_exact_accumulator ⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨wx⟩
      rcases ihy with ⟨wy⟩
      exact ⟨append_signed_short_exact_accumulator  wx wy⟩
  | neg x hx ihx =>
      rcases ihx with ⟨wx⟩
      exact ⟨swap_signed_short_exact_accumulator  wx⟩

/-- Helper for Lemma 12.11.3: the ordered signed short-exact data used in the source proof. The
two lists are the source proof's `T⁺` and `T⁻`, and the displayed equations record exactly how the
positive and negative short exact generators expand into those ordered lists. -/
structure SignedShortExactPresentation (P₀ Q₀ : P.FullSubcategory) where
  positiveSeqs : List { S : ShortComplex A // S.ShortExact }
  negativeSeqs : List { S : ShortComplex A // S.ShortExact }
  plus_terms : List A
  minus_terms : List A
  plus_eq :
    plus_terms =
      P₀.1 ::
        (positiveSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
          (negativeSeqs.map fun S ↦ S.1.X₂)
  minus_eq :
    minus_terms =
      Q₀.1 ::
        (negativeSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
          (positiveSeqs.map fun S ↦ S.1.X₂)
  balance_eq : fg_list  plus_terms = fg_list  minus_terms

/-- Helper for Lemma 12.11.3: the left-associated biproduct attached to an ordered list of
objects. -/
def ordered_biprod : List A → A
  | [] => 0
  | X :: xs => X ⊞ ordered_biprod xs

/-- Helper for Lemma 12.11.3: permuting the ordered list only changes the ordered biproduct by the
canonical biproduct braidings and associators. -/
theorem ordered_biprod_iso_of_perm {l₁ l₂ : List A} (h : l₁.Perm l₂) :
    Nonempty (ordered_biprod l₁ ≅ ordered_biprod l₂) := by
  induction h with
  | nil =>
      -- The empty ordered biproduct is literally the zero object.
      exact ⟨Iso.refl _⟩
  | cons X h ih =>
      -- Keep the common head summand and recurse on the tail permutation.
      rcases ih with ⟨e⟩
      exact ⟨by
        simpa [ordered_biprod] using biprod.mapIso (Iso.refl X) e⟩
  | swap X Y l =>
      -- Swap adjacent summands by reassociating, braiding the first binary biproduct, and
      -- reassociating back.
      exact ⟨by
        simpa [ordered_biprod] using
          ((biprod.associator X Y (ordered_biprod l)).symm ≪≫
            biprod.mapIso (biprod.braiding X Y) (Iso.refl (ordered_biprod l)) ≪≫
            biprod.associator Y X (ordered_biprod l)).symm⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      -- Compose the two permutation isomorphisms.
      rcases ih₁ with ⟨e₁⟩
      rcases ih₂ with ⟨e₂⟩
      exact ⟨e₁ ≪≫ e₂⟩

/-- Helper for Lemma 12.11.3: the `K₀`-class of an ordered biproduct depends only on the
underlying multiset of summands. -/
lemma k0_eq_of_ordered_biprod_perm {l₁ l₂ : List A} (h : l₁.Perm l₂) :
    K₀[ordered_biprod l₁] = K₀[ordered_biprod l₂] := by
  -- Transport across the canonical permutation isomorphism.
  classical
  exact k0_eq_of_iso  (Classical.choice (ordered_biprod_iso_of_perm  h))

/-- Helper for Lemma 12.11.3: balanced positive formal sums give canonically isomorphic ordered
biproducts. -/
theorem ordered_biprod_iso_of_balance {l₁ l₂ : List A}
    (h : fg_list l₁ = fg_list l₂) :
    Nonempty (ordered_biprod l₁ ≅ ordered_biprod l₂) := by
  classical
  -- First recover the underlying list permutation from the equality in the free abelian group.
  exact ordered_biprod_iso_of_perm  (list_perm_of_fg_list_eq  h)

/-- Helper for Lemma 12.11.3: reattaching a common ordered prefix preserves an ordered-biproduct
isomorphism. -/
theorem ordered_biprod_iso_of_prefix (pre : List A) {l₁ l₂ : List A}
    (e : ordered_biprod l₁ ≅ ordered_biprod l₂) :
    Nonempty (ordered_biprod (pre ++ l₁) ≅ ordered_biprod (pre ++ l₂)) := by
  induction pre with
  | nil =>
      -- With no common prefix left, this is the original ordered-biproduct isomorphism.
      exact ⟨by simpa using e⟩
  | cons X xs ih =>
      -- Reattach the common head summand and recurse on the remaining prefix.
      rcases ih with ⟨e'⟩
      exact ⟨by simpa [ordered_biprod] using biprod.mapIso (Iso.refl X) e'⟩

/-- Helper for Lemma 12.11.3: flattening a list of binary biproduct blocks into the corresponding
ordered list of summands changes the ordered biproduct only by canonical associators. -/
theorem ordered_biprod_pairs_append_iso :
    ∀ pairs : List (A × A), ∀ tail : List A,
      Nonempty
        (ordered_biprod ((pairs.map fun p ↦ p.1 ⊞ p.2) ++ tail) ≅
          ordered_biprod ((pairs.flatMap fun p ↦ [p.1, p.2]) ++ tail))
  | [], tail =>
      -- No binary blocks remain, so both ordered biproducts are literally the same.
      ⟨Iso.refl _⟩
  | p :: pairs, tail => by
      -- Split off the first binary block, reassociate it, and recurse on the remaining blocks.
      rcases ordered_biprod_pairs_append_iso pairs tail with ⟨e⟩
      exact ⟨by
        simpa [ordered_biprod] using
          (biprod.associator p.1 p.2
              (ordered_biprod ((pairs.map fun q ↦ q.1 ⊞ q.2) ++ tail)) ≪≫
            biprod.mapIso (Iso.refl p.1)
              (biprod.mapIso (Iso.refl p.2) e))⟩

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: the distinguished heads `P₀` and `Q₀` balance the two signed tail
lists encoded by the accumulator relation. -/
lemma signedShortExactPresentationBalance
    {P₀ Q₀ : P.FullSubcategory}
    (w : SignedShortExactAccumulator (FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1)) :
    fg_list (P₀.1 :: signed_plus_terms w.positiveSeqs w.negativeSeqs) =
      fg_list (Q₀.1 :: signed_minus_terms w.positiveSeqs w.negativeSeqs) := by
  -- The accumulator relation is already the same equality after moving the two head terms.
  have hw :
      fg_list  (signed_minus_terms  w.positiveSeqs w.negativeSeqs) +
          FreeAbelianGroup.of Q₀.1 =
        FreeAbelianGroup.of P₀.1 +
          fg_list  (signed_plus_terms  w.positiveSeqs w.negativeSeqs) :=
    (sub_eq_sub_iff_add_eq_add).mp w.difference_eq
  simpa [fg_list, add_comm, add_left_comm, add_assoc] using hw.symm

/-- Helper for Lemma 12.11.3: a kernel class `x = [P₀] - [Q₀]` admits the source proof's ordered
signed short-exact presentation. -/
theorem exists_signed_short_exact_presentation_of_mem_ker_inclusion
    {x : AbelianK0 P.FullSubcategory} {P₀ Q₀ : P.FullSubcategory}
    (hx : x = K₀[P₀] - K₀[Q₀]) (hker : x ∈ (K₀ι).ker) :
    Nonempty (SignedShortExactPresentation P P₀ Q₀) := by
  have hrel :
      FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1 ∈ AbelianK0.relations A :=
    relation_of_mem_ker_inclusion (P := P) hx hker
  rcases exists_signed_short_exact_accumulator_of_relation (A := A) hrel with ⟨w⟩
  refine ⟨
    { positiveSeqs := w.positiveSeqs
      negativeSeqs := w.negativeSeqs
      plus_terms := P₀.1 :: signed_plus_terms w.positiveSeqs w.negativeSeqs
      minus_terms := Q₀.1 :: signed_minus_terms w.positiveSeqs w.negativeSeqs
      plus_eq := rfl
      minus_eq := rfl
      balance_eq := signedShortExactPresentationBalance (P := P) w }⟩

/-- Helper for Lemma 12.11.3: for one positive short exact block
`X₁ ⟶ X₂ ⟶ X₃`, the source-proof short complex
`X₂ ⟶ X₁ ⊞ X₃ ⟶ X₂` is exact. -/
lemma positivePresentationBlockDegreeZeroExact
    (S : { T : ShortComplex A // T.ShortExact }) :
    (ShortComplex.mk
      (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
      (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
      (by
        rw [biprod.lift_eq, biprod.desc_eq]
        simp [Category.assoc])).Exact := by
  haveI : Mono S.1.f := S.2.mono_f
  haveI : Epi S.1.g := S.2.epi_g
  let T : ShortComplex A :=
    ShortComplex.mk
      (biprod.inr : S.1.X₃ ⟶ S.1.X₁ ⊞ S.1.X₃)
      (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
      (by simpa using (biprod.inr_desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂)))
  have hT : T.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    have hInrZero :
        (biprod.inr : S.1.X₃ ⟶ S.1.X₁ ⊞ S.1.X₃) ≫
          biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂) = 0 := by
      simpa using (biprod.inr_desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
    refine KernelFork.IsLimit.ofι'
      (biprod.inr : S.1.X₃ ⟶ S.1.X₁ ⊞ S.1.X₃) hInrZero ?_
    intro W k hk
    have hkfst' : (k ≫ biprod.fst) ≫ S.1.f = 0 := by
      simpa [T, biprod.desc_eq, Category.assoc] using hk
    have hkfst : k ≫ biprod.fst = 0 := by
      apply (cancel_mono S.1.f).1
      simpa [Category.assoc] using hkfst'
    refine ⟨k ≫ biprod.snd, ?_⟩
    apply biprod.hom_ext
    · simp [Category.assoc, hkfst]
    · simp [Category.assoc]
  let φ :
      ShortComplex.mk
          (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
          (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
          (by
            rw [biprod.lift_eq, biprod.desc_eq]
            simp [Category.assoc]) ⟶ T :=
    { τ₁ := S.1.g
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        apply biprod.hom_ext
        · simpa [T, Category.assoc]
        · simpa [T, Category.assoc]
      comm₂₃ := by simp [T] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT

/-- Helper for Lemma 12.11.3: for one positive short exact block
`X₁ ⟶ X₂ ⟶ X₃`, the companion short complex
`X₁ ⊞ X₃ ⟶ X₂ ⟶ X₁ ⊞ X₃` is exact. -/
lemma positivePresentationBlockDegreeOneExact
    (S : { T : ShortComplex A // T.ShortExact }) :
    (ShortComplex.mk
      (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
      (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
      (by
        rw [biprod.desc_eq, biprod.lift_eq]
        simp [Category.assoc])).Exact := by
  haveI : Mono S.1.f := S.2.mono_f
  haveI : Epi S.1.g := S.2.epi_g
  let T : ShortComplex A :=
    ShortComplex.mk
      S.1.f
      (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
      (by
        rw [biprod.lift_eq]
        simp)
  have hT : T.Exact := by
    let χ : S.1 ⟶ T :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := biprod.inr
        comm₁₂ := by simp [T]
        comm₂₃ := by
          apply biprod.hom_ext
          · simpa [T]
          · simpa [T] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono χ).1 S.2.exact
  let ψ :
      ShortComplex.mk
          (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
          (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
          (by
            rw [biprod.desc_eq, biprod.lift_eq]
            simp [Category.assoc]) ⟶ T :=
    { τ₁ := biprod.fst
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        apply biprod.hom_ext'
        · simp [T]
        · simp [T]
      comm₂₃ := by simp [T] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT

/-- Helper for Lemma 12.11.3: the binary biproduct of two exact short complexes is exact. -/
lemma shortComplexBiprodExact {S T : ShortComplex A} (hS : S.Exact) (hT : T.Exact) :
    (S ⊞ T).Exact := by
  -- Route correction: compute exactness through homology, and make the binary-biproduct
  -- preservation path explicit instead of leaving it to brittle instance search.
  have hS0 : IsZero S.homology := by
    simpa [ShortComplex.exact_iff_isZero_homology] using hS
  have hT0 : IsZero T.homology := by
    simpa [ShortComplex.exact_iff_isZero_homology] using hT
  rw [ShortComplex.exact_iff_isZero_homology]
  letI : (ShortComplex.homologyFunctor A).Additive := inferInstance
  letI : PreservesFiniteBiproducts (ShortComplex.homologyFunctor A) := inferInstance
  letI : PreservesBiproductsOfShape WalkingPair (ShortComplex.homologyFunctor A) := inferInstance
  letI : PreservesBinaryBiproducts (ShortComplex.homologyFunctor A) :=
    Limits.preservesBinaryBiproducts_of_preservesBiproducts (ShortComplex.homologyFunctor A)
  let e :
      (ShortComplex.homologyFunctor A).obj (S ⊞ T) ≅
        (ShortComplex.homologyFunctor A).obj S ⊞ (ShortComplex.homologyFunctor A).obj T :=
    (ShortComplex.homologyFunctor A).mapBiprod S T
  -- The homology biproduct is zero because each summand homology is already zero.
  exact IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hS0, hT0⟩) e

/-- Helper for Lemma 12.11.3: the homology of a zero short complex is its middle object. -/
lemma zeroZeroShortComplexHomologyIsoMiddle (X Y Z : A) :
    Nonempty ((ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).homology ≅ Y) := by
  let S : ShortComplex A := ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp
  have hLiftZero : kernel.lift (0 : Y ⟶ Z) (0 : X ⟶ Y) zero_comp = 0 := by
    -- The cokernel presentation for homology reduces to the zero map into `kernel 0`.
    apply (cancel_mono (kernel.ι (0 : Y ⟶ Z))).1
    simp
  -- Rewrite the homology cokernel to the zero cokernel, then collapse `kernel 0` back to `Y`.
  refine ⟨S.homologyIsoCokernelLift ≪≫ ?_⟩
  rw [hLiftZero]
  exact cokernelZeroIsoTarget ≪≫ kernelZeroIsoSource

/-- Helper for Lemma 12.11.3: if the right summand short complex is exact, then adding it by
binary biproduct does not change homology. -/
lemma biprodHomologyIsoLeftOfExactRight {S T : ShortComplex A} (hT : T.Exact) :
    Nonempty ((S ⊞ T).homology ≅ S.homology) := by
  -- After applying homology, the exact right summand becomes zero and can be removed.
  have hT0 : IsZero T.homology := by
    simpa [ShortComplex.exact_iff_isZero_homology] using hT
  letI : (ShortComplex.homologyFunctor A).Additive := inferInstance
  letI : PreservesFiniteBiproducts (ShortComplex.homologyFunctor A) := inferInstance
  letI : PreservesBiproductsOfShape WalkingPair (ShortComplex.homologyFunctor A) := inferInstance
  letI : PreservesBinaryBiproducts (ShortComplex.homologyFunctor A) :=
    Limits.preservesBinaryBiproducts_of_preservesBiproducts (ShortComplex.homologyFunctor A)
  exact ⟨(ShortComplex.homologyFunctor A).mapBiprod S T ≪≫
    biprod.braiding S.homology T.homology ≪≫
      (isoZeroBiprod hT0).symm⟩

/-- Helper for Lemma 12.11.3: the ordered binary biproduct of a list of short complexes. -/
def orderedShortBiprod : List (ShortComplex A) → ShortComplex A
  | [] => ShortComplex.mk (0 : (0 : A) ⟶ 0) (0 : (0 : A) ⟶ 0) (zero_comp)
  | S :: l => S ⊞ orderedShortBiprod l

/-- Helper for Lemma 12.11.3: the first object of an ordered short biproduct is canonically
identified with the ordered biproduct of the first objects. -/
noncomputable def orderedShortBiprodX₁Iso :
    ∀ l : List (ShortComplex A),
      (orderedShortBiprod  l).X₁ ≅ ordered_biprod (l.map ShortComplex.X₁)
  | [] => Iso.refl _
  | S :: l => by
      letI : PreservesBinaryBiproducts (ShortComplex.π₁ : ShortComplex A ⥤ A) :=
        preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₁ : ShortComplex A ⥤ A)
      exact
        (ShortComplex.π₁.mapBiprod S (orderedShortBiprod  l)) ≪≫
          biprod.mapIso (Iso.refl _) (orderedShortBiprodX₁Iso l)

/-- Helper for Lemma 12.11.3: the middle object of an ordered short biproduct is canonically
identified with the ordered biproduct of the middle objects. -/
noncomputable def orderedShortBiprodX₂Iso :
    ∀ l : List (ShortComplex A),
      (orderedShortBiprod  l).X₂ ≅ ordered_biprod (l.map ShortComplex.X₂)
  | [] => Iso.refl _
  | S :: l => by
      letI : PreservesBinaryBiproducts (ShortComplex.π₂ : ShortComplex A ⥤ A) :=
        preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₂ : ShortComplex A ⥤ A)
      exact
        (ShortComplex.π₂.mapBiprod S (orderedShortBiprod  l)) ≪≫
          biprod.mapIso (Iso.refl _) (orderedShortBiprodX₂Iso l)

/-- Helper for Lemma 12.11.3: the third object of an ordered short biproduct is canonically
identified with the ordered biproduct of the third objects. -/
noncomputable def orderedShortBiprodX₃Iso :
    ∀ l : List (ShortComplex A),
      (orderedShortBiprod  l).X₃ ≅ ordered_biprod (l.map ShortComplex.X₃)
  | [] => Iso.refl _
  | S :: l => by
      letI : PreservesBinaryBiproducts (ShortComplex.π₃ : ShortComplex A ⥤ A) :=
        preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₃ : ShortComplex A ⥤ A)
      exact
        (ShortComplex.π₃.mapBiprod S (orderedShortBiprod  l)) ≪≫
          biprod.mapIso (Iso.refl _) (orderedShortBiprodX₃Iso l)

/-- Helper for Lemma 12.11.3: an ordered binary biproduct of exact short complexes is exact. -/
lemma orderedShortBiprodExact :
    ∀ l : List (ShortComplex A), (∀ S ∈ l, S.Exact) → (orderedShortBiprod  l).Exact
  | [], _ => by
      -- The empty ordered biproduct is the zero short complex.
      have hZeroX₂ : IsZero ((orderedShortBiprod ([] : List (ShortComplex A))).X₂) := by
        simpa [orderedShortBiprod] using (isZero_zero A)
      simpa [orderedShortBiprod] using
        (ShortComplex.exact_of_isZero_X₂ (orderedShortBiprod ([] : List (ShortComplex A))) hZeroX₂)
  | S :: l, hExact => by
      -- Peel off the head short complex and recurse on the tail.
      refine shortComplexBiprodExact  (hExact S (by simp)) ?_
      apply orderedShortBiprodExact
      intro T hT
      exact hExact T (by simp [hT])

/-- Helper for Lemma 12.11.3: applying the Serre quotient functor to an exact ordered short
biproduct preserves exactness. -/
lemma orderedShortBiprodMapExact
    (l : List (ShortComplex A))
    (hExact : ∀ S ∈ l, S.Exact) :
    ((orderedShortBiprod  l).map Q).Exact := by
  -- The quotient functor is exact, so it preserves exactness of the assembled short complex.
  exact (orderedShortBiprodExact  l hExact).map Q

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: the grouped `T⁺` and `T⁻` objects attached to a signed short-exact
presentation are canonically isomorphic. -/
lemma signedPresentationGroupedBalanceIso
    {P₀ Q₀ : P.FullSubcategory} (w : SignedShortExactPresentation P P₀ Q₀) :
    let posSeqs := w.positiveSeqs.unattach
    let negSeqs := w.negativeSeqs.unattach
    Nonempty
      (ordered_biprod
        (P₀.1 ::
          (posSeqs.map fun S ↦ S.X₁ ⊞ S.X₃) ++
            (negSeqs.map ShortComplex.X₂)) ≅
        ordered_biprod
        (Q₀.1 ::
          (posSeqs.map ShortComplex.X₂) ++
            (negSeqs.map fun S ↦ S.X₁ ⊞ S.X₃))) := by
  classical
  dsimp
  -- Route correction: normalize both grouped tails to the flattened source lists before using the
  -- stored balance relation `w.balance_eq`.
  have hPosGrouped :
      List.map (fun p : A × A ↦ p.1 ⊞ p.2)
          (w.positiveSeqs.unattach.map fun S ↦ (S.X₁, S.X₃)) =
        w.positiveSeqs.unattach.map (fun S ↦ S.X₁ ⊞ S.X₃) := by
    induction w.positiveSeqs.unattach with
    | nil =>
        rfl
    | cons S l ih =>
        simp [ih]
  have hPosFlat :
      List.flatMap (fun p : A × A ↦ [p.1, p.2])
          (w.positiveSeqs.unattach.map fun S ↦ (S.X₁, S.X₃)) =
        w.positiveSeqs.unattach.flatMap (fun S ↦ [S.X₁, S.X₃]) := by
    induction w.positiveSeqs.unattach with
    | nil =>
        rfl
    | cons S l ih =>
        simp [ih]
  have hNegGrouped :
      List.map (fun p : A × A ↦ p.1 ⊞ p.2)
          (w.negativeSeqs.unattach.map fun S ↦ (S.X₁, S.X₃)) =
        w.negativeSeqs.unattach.map (fun S ↦ S.X₁ ⊞ S.X₃) := by
    induction w.negativeSeqs.unattach with
    | nil =>
        rfl
    | cons S l ih =>
        simp [ih]
  have hNegFlat :
      List.flatMap (fun p : A × A ↦ [p.1, p.2])
          (w.negativeSeqs.unattach.map fun S ↦ (S.X₁, S.X₃)) =
        w.negativeSeqs.unattach.flatMap (fun S ↦ [S.X₁, S.X₃]) := by
    induction w.negativeSeqs.unattach with
    | nil =>
        rfl
    | cons S l ih =>
        simp [ih]
  have hPosFlatSubtype :
      w.positiveSeqs.flatMap (fun S ↦ [S.1.X₁, S.1.X₃]) =
        w.positiveSeqs.unattach.flatMap (fun S ↦ [S.X₁, S.X₃]) := by
    simpa using
      (List.flatMap_unattach
        (xs := w.positiveSeqs) (f := fun S : ShortComplex A ↦ [S.X₁, S.X₃])).symm
  have hNegFlatSubtype :
      w.negativeSeqs.flatMap (fun S ↦ [S.1.X₁, S.1.X₃]) =
        w.negativeSeqs.unattach.flatMap (fun S ↦ [S.X₁, S.X₃]) := by
    simpa using
      (List.flatMap_unattach
        (xs := w.negativeSeqs) (f := fun S : ShortComplex A ↦ [S.X₁, S.X₃])).symm
  have hPosMapSubtype :
      w.positiveSeqs.map (fun S ↦ S.1.X₂) =
        w.positiveSeqs.unattach.map ShortComplex.X₂ := by
    simpa using
      (List.map_unattach (xs := w.positiveSeqs) (f := ShortComplex.X₂)).symm
  have hNegMapSubtype :
      w.negativeSeqs.map (fun S ↦ S.1.X₂) =
        w.negativeSeqs.unattach.map ShortComplex.X₂ := by
    simpa using
      (List.map_unattach (xs := w.negativeSeqs) (f := ShortComplex.X₂)).symm
  rcases ordered_biprod_pairs_append_iso
      (pairs := w.positiveSeqs.unattach.map fun S ↦ (S.X₁, S.X₃))
      (tail := w.negativeSeqs.unattach.map ShortComplex.X₂) with ⟨ePlusTail⟩
  rcases ordered_biprod_iso_of_prefix [P₀.1] ePlusTail with ⟨ePlus⟩
  have ePlus' :
      ordered_biprod
          (P₀.1 ::
            (w.positiveSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂)) ≅
        ordered_biprod
          (P₀.1 ::
            (w.positiveSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂)) := by
    simpa [hPosGrouped, hPosFlat] using ePlus
  rcases ordered_biprod_pairs_append_iso
      (pairs := w.negativeSeqs.unattach.map fun S ↦ (S.X₁, S.X₃))
      (tail := []) with ⟨eMinusGrouped⟩
  rcases ordered_biprod_iso_of_prefix
      (Q₀.1 :: w.positiveSeqs.unattach.map ShortComplex.X₂) eMinusGrouped with ⟨eMinusGrouped⟩
  have eMinusGrouped' :
      ordered_biprod
          (Q₀.1 ::
            (w.positiveSeqs.unattach.map ShortComplex.X₂) ++
              (w.negativeSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃)) ≅
        ordered_biprod
          (Q₀.1 ::
            (w.positiveSeqs.unattach.map ShortComplex.X₂) ++
              (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃])) := by
    simpa [hNegGrouped, hNegFlat] using eMinusGrouped
  have hPlusTerms :
      fg_list w.plus_terms =
        fg_list
          (P₀.1 ::
            (w.positiveSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂)) := by
    simpa [hPosFlatSubtype, hNegMapSubtype] using congrArg fg_list w.plus_eq
  have hMinusTerms :
      fg_list w.minus_terms =
        fg_list
          (Q₀.1 ::
            (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
              (w.positiveSeqs.unattach.map ShortComplex.X₂)) := by
    simpa [hNegFlatSubtype, hPosMapSubtype] using congrArg fg_list w.minus_eq
  have hBalance :
      fg_list
          (P₀.1 ::
            (w.positiveSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂)) =
        fg_list
            (Q₀.1 ::
              (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
                (w.positiveSeqs.unattach.map ShortComplex.X₂)) := by
    -- The presentation fields already record exactly this flattened balance.
    calc
      fg_list
          (P₀.1 ::
            (w.positiveSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂))
          = fg_list w.plus_terms := hPlusTerms.symm
      _ = fg_list w.minus_terms := by simpa using w.balance_eq
      _ =
          fg_list
            (Q₀.1 ::
              (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
                (w.positiveSeqs.unattach.map ShortComplex.X₂)) := hMinusTerms
  rcases ordered_biprod_iso_of_balance hBalance with ⟨eBalance⟩
  have hMinusPerm :
      ((w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
          (w.positiveSeqs.unattach.map ShortComplex.X₂)).Perm
        ((w.positiveSeqs.unattach.map ShortComplex.X₂) ++
          (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃])) := by
    simpa using (List.perm_append_comm :
      ((w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃]) ++
          (w.positiveSeqs.unattach.map ShortComplex.X₂)).Perm
        ((w.positiveSeqs.unattach.map ShortComplex.X₂) ++
          (w.negativeSeqs.unattach.flatMap fun S ↦ [S.X₁, S.X₃])))
  rcases ordered_biprod_iso_of_perm (hMinusPerm.cons Q₀.1) with ⟨eMinusPerm⟩
  exact ⟨by
    simpa using ePlus' ≪≫ eBalance ≪≫ eMinusPerm ≪≫ eMinusGrouped'.symm⟩

/-- Helper for Lemma 12.11.3: the degree-`0` presentation block attached to a short exact
sequence is a short complex. -/
lemma degreeZeroPresentationBlock_zero
    (S : { T : ShortComplex A // T.ShortExact }) :
    biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g ≫
        biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂) = 0 := by
  rw [biprod.lift_eq, biprod.desc_eq]
  simp [Category.assoc]

/-- Helper for Lemma 12.11.3: the degree-`0` block used in the cyclic witness. -/
def degreeZeroPresentationBlock
    (S : { T : ShortComplex A // T.ShortExact }) : ShortComplex A :=
  ShortComplex.mk
    (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
    (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
    (degreeZeroPresentationBlock_zero  S)

/-- Helper for Lemma 12.11.3: the first object of the degree-`0` presentation block is `S.X₂`. -/
@[simp] lemma degreeZeroPresentationBlock_X₁
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeZeroPresentationBlock  S).X₁ = S.1.X₂ :=
  rfl

/-- Helper for Lemma 12.11.3: the middle object of the degree-`0` presentation block is
`S.X₁ ⊞ S.X₃`. -/
@[simp] lemma degreeZeroPresentationBlock_X₂
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeZeroPresentationBlock  S).X₂ = (S.1.X₁ ⊞ S.1.X₃) :=
  rfl

/-- Helper for Lemma 12.11.3: the third object of the degree-`0` presentation block is `S.X₂`. -/
@[simp] lemma degreeZeroPresentationBlock_X₃
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeZeroPresentationBlock  S).X₃ = S.1.X₂ :=
  rfl

/-- Helper for Lemma 12.11.3: the degree-`1` presentation block attached to a short exact
sequence is a short complex. -/
lemma degreeOnePresentationBlock_zero
    (S : { T : ShortComplex A // T.ShortExact }) :
    biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂) ≫
        biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g = 0 := by
  rw [biprod.desc_eq, biprod.lift_eq]
  simp [Category.assoc]

/-- Helper for Lemma 12.11.3: the degree-`1` block used in the cyclic witness. -/
def degreeOnePresentationBlock
    (S : { T : ShortComplex A // T.ShortExact }) : ShortComplex A :=
  ShortComplex.mk
    (biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂))
    (biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g)
    (degreeOnePresentationBlock_zero  S)

/-- Helper for Lemma 12.11.3: the first object of the degree-`1` presentation block is
`S.X₁ ⊞ S.X₃`. -/
@[simp] lemma degreeOnePresentationBlock_X₁
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeOnePresentationBlock  S).X₁ = (S.1.X₁ ⊞ S.1.X₃) :=
  rfl

/-- Helper for Lemma 12.11.3: the middle object of the degree-`1` presentation block is `S.X₂`. -/
@[simp] lemma degreeOnePresentationBlock_X₂
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeOnePresentationBlock  S).X₂ = S.1.X₂ :=
  rfl

/-- Helper for Lemma 12.11.3: the third object of the degree-`1` presentation block is
`S.X₁ ⊞ S.X₃`. -/
@[simp] lemma degreeOnePresentationBlock_X₃
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeOnePresentationBlock  S).X₃ = (S.1.X₁ ⊞ S.1.X₃) :=
  rfl

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₁` across the degree-`0` presentation
blocks records the middle terms of the underlying short exact sequences. -/
@[simp] lemma map_degreeZeroPresentationBlock_X₁
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeZeroPresentationBlock).map ShortComplex.X₁ = l.map (fun S ↦ S.1.X₂) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₂` across the degree-`0` presentation
blocks records the grouped outer terms `X₁ ⊞ X₃`. -/
@[simp] lemma map_degreeZeroPresentationBlock_X₂
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeZeroPresentationBlock).map ShortComplex.X₂ =
      l.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₃` across the degree-`0` presentation
blocks again records the middle terms. -/
@[simp] lemma map_degreeZeroPresentationBlock_X₃
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeZeroPresentationBlock).map ShortComplex.X₃ = l.map (fun S ↦ S.1.X₂) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₁` across the degree-`1` presentation
blocks records the grouped outer terms `X₁ ⊞ X₃`. -/
@[simp] lemma map_degreeOnePresentationBlock_X₁
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeOnePresentationBlock).map ShortComplex.X₁ =
      l.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₂` across the degree-`1` presentation
blocks records the middle terms of the underlying short exact sequences. -/
@[simp] lemma map_degreeOnePresentationBlock_X₂
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeOnePresentationBlock).map ShortComplex.X₂ = l.map (fun S ↦ S.1.X₂) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: mapping `ShortComplex.X₃` across the degree-`1` presentation
blocks again records the grouped outer terms `X₁ ⊞ X₃`. -/
@[simp] lemma map_degreeOnePresentationBlock_X₃
    (l : List { T : ShortComplex A // T.ShortExact }) :
    (l.map degreeOnePresentationBlock).map ShortComplex.X₃ =
      l.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) := by
  induction l with
  | nil =>
      rfl
  | cons S l ih =>
      simp [ih]

/-- Helper for Lemma 12.11.3: the first differential of a degree-`0` presentation block is the
expected `biprod.lift` map. -/
@[simp] lemma degreeZeroPresentationBlock_f
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeZeroPresentationBlock  S).f =
      biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g :=
  rfl

/-- Helper for Lemma 12.11.3: the second differential of a degree-`0` presentation block is the
expected `biprod.desc` map. -/
@[simp] lemma degreeZeroPresentationBlock_g
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeZeroPresentationBlock  S).g =
      biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂) :=
  rfl

/-- Helper for Lemma 12.11.3: the first differential of a degree-`1` presentation block is the
expected `biprod.desc` map. -/
@[simp] lemma degreeOnePresentationBlock_f
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeOnePresentationBlock  S).f =
      biprod.desc S.1.f (0 : S.1.X₃ ⟶ S.1.X₂) :=
  rfl

/-- Helper for Lemma 12.11.3: the second differential of a degree-`1` presentation block is the
expected `biprod.lift` map. -/
@[simp] lemma degreeOnePresentationBlock_g
    (S : { T : ShortComplex A // T.ShortExact }) :
    (degreeOnePresentationBlock  S).g =
      biprod.lift (0 : S.1.X₂ ⟶ S.1.X₁) S.1.g :=
  rfl

/-- Helper for Lemma 12.11.3: transporting a natural-transformation component across the
binary-biproduct comparison isomorphisms produces the componentwise `biprod.map`. -/
lemma natTransAppMapBiprod
    {F G : ShortComplex A ⥤ A} (α : F ⟶ G)
    (S T : ShortComplex A)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesBinaryBiproduct S T F] [PreservesBinaryBiproduct S T G] :
    (F.mapBiprod S T).inv ≫ α.app (S ⊞ T) ≫ (G.mapBiprod S T).hom =
      biprod.map (α.app S) (α.app T) := by
  -- Compare the two transported maps on the left and right biproduct summands.
  refine biprod.hom_ext' _ _ ?_ ?_
  · calc
      biprod.inl ≫ (F.mapBiprod S T).inv ≫ α.app (S ⊞ T) ≫ (G.mapBiprod S T).hom
          = F.map biprod.inl ≫ α.app (S ⊞ T) ≫ (G.mapBiprod S T).hom := by
              rw [Functor.mapBiprod_inv]
              simp
      _ = α.app S ≫ G.map biprod.inl ≫ (G.mapBiprod S T).hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ (G.mapBiprod S T).hom) (α.naturality biprod.inl)
      _ = α.app S ≫ biprod.inl := by
            apply biprod.hom_ext
            · rw [Functor.mapBiprod_hom]
              calc
                (α.app S ≫ G.map biprod.inl ≫ biprod.lift (G.map biprod.fst) (G.map biprod.snd)) ≫
                    biprod.fst
                    = α.app S ≫ (G.map biprod.inl ≫ G.map biprod.fst) := by
                        simp [Category.assoc, biprod.lift_fst]
                        rfl
                _ = α.app S ≫ G.map (biprod.inl ≫ biprod.fst) := by
                      rw [← G.map_comp]
                _ = α.app S := by
                      simp
                _ = (α.app S ≫ biprod.inl) ≫ biprod.fst := by
                      simp [Category.assoc]
            · rw [Functor.mapBiprod_hom]
              calc
                (α.app S ≫ G.map biprod.inl ≫ biprod.lift (G.map biprod.fst) (G.map biprod.snd)) ≫
                    biprod.snd
                    = α.app S ≫ (G.map biprod.inl ≫ G.map biprod.snd) := by
                        simp [Category.assoc, biprod.lift_snd]
                _ = α.app S ≫ G.map (biprod.inl ≫ biprod.snd) := by
                      rw [← G.map_comp]
                _ = 0 := by
                      simp
                _ = (α.app S ≫ biprod.inl) ≫ biprod.snd := by
                      simp [Category.assoc]
      _ = biprod.inl ≫ biprod.map (α.app S) (α.app T) := by
            symm
            simp
  · calc
      biprod.inr ≫ (F.mapBiprod S T).inv ≫ α.app (S ⊞ T) ≫ (G.mapBiprod S T).hom
          = F.map biprod.inr ≫ α.app (S ⊞ T) ≫ (G.mapBiprod S T).hom := by
              rw [Functor.mapBiprod_inv]
              simp
      _ = α.app T ≫ G.map biprod.inr ≫ (G.mapBiprod S T).hom := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ (G.mapBiprod S T).hom) (α.naturality biprod.inr)
      _ = α.app T ≫ biprod.inr := by
            apply biprod.hom_ext
            · rw [Functor.mapBiprod_hom]
              calc
                (α.app T ≫ G.map biprod.inr ≫ biprod.lift (G.map biprod.fst) (G.map biprod.snd)) ≫
                    biprod.fst
                    = α.app T ≫ (G.map biprod.inr ≫ G.map biprod.fst) := by
                        simp [Category.assoc, biprod.lift_fst]
                _ = α.app T ≫ G.map (biprod.inr ≫ biprod.fst) := by
                      rw [← G.map_comp]
                _ = 0 := by
                      simp
                _ = (α.app T ≫ biprod.inr) ≫ biprod.fst := by
                      simp [Category.assoc]
            · rw [Functor.mapBiprod_hom]
              calc
                (α.app T ≫ G.map biprod.inr ≫ biprod.lift (G.map biprod.fst) (G.map biprod.snd)) ≫
                    biprod.snd
                    = α.app T ≫ (G.map biprod.inr ≫ G.map biprod.snd) := by
                        simp [Category.assoc, biprod.lift_snd]
                        rfl
                _ = α.app T ≫ G.map (biprod.inr ≫ biprod.snd) := by
                      rw [← G.map_comp]
                _ = α.app T := by
                      simp
                _ = (α.app T ≫ biprod.inr) ≫ biprod.snd := by
                      simp [Category.assoc]
      _ = biprod.inr ≫ biprod.map (α.app S) (α.app T) := by
            symm
            simp

/-- Helper for Lemma 12.11.3: the first differential of a `ShortComplex` binary biproduct
becomes the componentwise `biprod.map` after transport across `π₁` and `π₂`. -/
lemma shortComplexBiprodFMap
    (S T : ShortComplex A)
    [PreservesBinaryBiproduct S T (ShortComplex.π₁ : ShortComplex A ⥤ A)]
    [PreservesBinaryBiproduct S T (ShortComplex.π₂ : ShortComplex A ⥤ A)] :
    (ShortComplex.π₁.mapBiprod S T).inv ≫ (S ⊞ T).f ≫ (ShortComplex.π₂.mapBiprod S T).hom =
      biprod.map S.f T.f := by
  -- This is the componentwise biproduct transport for the natural transformation `π₁ ⟶ π₂`.
  simpa using natTransAppMapBiprod
    (α := (ShortComplex.π₁Toπ₂ : (ShortComplex.π₁ : ShortComplex A ⥤ A) ⟶ ShortComplex.π₂))
    S T

/-- Helper for Lemma 12.11.3: the second differential of a `ShortComplex` binary biproduct
becomes the componentwise `biprod.map` after transport across `π₂` and `π₃`. -/
lemma shortComplexBiprodGMap
    (S T : ShortComplex A)
    [PreservesBinaryBiproduct S T (ShortComplex.π₂ : ShortComplex A ⥤ A)]
    [PreservesBinaryBiproduct S T (ShortComplex.π₃ : ShortComplex A ⥤ A)] :
    (ShortComplex.π₂.mapBiprod S T).inv ≫ (S ⊞ T).g ≫ (ShortComplex.π₃.mapBiprod S T).hom =
      biprod.map S.g T.g := by
  -- This is the same transport statement for the natural transformation `π₂ ⟶ π₃`.
  simpa using natTransAppMapBiprod
    (α := (ShortComplex.π₂Toπ₃ : (ShortComplex.π₂ : ShortComplex A ⥤ A) ⟶ ShortComplex.π₃))
    S T

/-- Helper for Lemma 12.11.3: conjugating a `biprod.map` by a right-hand `biprod.mapIso`
transport only changes the right component map. -/
lemma biprodMapIsoTransportRight
    {X Y U U' V V' : A}
    [HasBinaryBiproduct X U] [HasBinaryBiproduct Y V]
    [HasBinaryBiproduct X U'] [HasBinaryBiproduct Y V']
    (f : X ⟶ Y) (g : U ⟶ V) (eU : U ≅ U') (eV : V ≅ V') :
    (biprod.mapIso (Iso.refl X) eU).inv ≫ biprod.map f g ≫
        (biprod.mapIso (Iso.refl Y) eV).hom =
      biprod.map f (eU.inv ≫ g ≫ eV.hom) := by
  -- The left summand is fixed, so only the right branch changes under the two transports.
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp
  · simp

/-- Helper for Lemma 12.11.3: transporting the first differential of an ordered short biproduct
through the recursive `X₁/X₂` identifications yields the expected `biprod.map` normal form. -/
lemma orderedShortBiprodFCons
    (S : ShortComplex A) (l : List (ShortComplex A)) :
    (orderedShortBiprodX₁Iso  (S :: l)).inv ≫
        (orderedShortBiprod  (S :: l)).f ≫
        (orderedShortBiprodX₂Iso  (S :: l)).hom =
      biprod.map S.f
        ((orderedShortBiprodX₁Iso  l).inv ≫
          (orderedShortBiprod  l).f ≫
          (orderedShortBiprodX₂Iso  l).hom) := by
  letI : PreservesBinaryBiproducts (ShortComplex.π₁ : ShortComplex A ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₁ : ShortComplex A ⥤ A)
  letI : PreservesBinaryBiproducts (ShortComplex.π₂ : ShortComplex A ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₂ : ShortComplex A ⥤ A)
  -- Unfold one recursive layer of the ordered-biproduct identifications and normalize the middle
  -- map by the owner-level `ShortComplex` biproduct transport.
  calc
    (orderedShortBiprodX₁Iso  (S :: l)).inv ≫
          (orderedShortBiprod  (S :: l)).f ≫
          (orderedShortBiprodX₂Iso  (S :: l)).hom
        =
          (biprod.mapIso (Iso.refl S.X₁) (orderedShortBiprodX₁Iso l)).inv ≫
            ((ShortComplex.π₁.mapBiprod S (orderedShortBiprod l)).inv ≫
              (S ⊞ orderedShortBiprod l).f ≫
              (ShortComplex.π₂.mapBiprod S (orderedShortBiprod l)).hom) ≫
            (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).hom := by
              simp [orderedShortBiprodX₁Iso, orderedShortBiprodX₂Iso, orderedShortBiprod,
                Iso.trans_hom, Iso.trans_inv, Category.assoc]
              rfl
    _ =
          (biprod.mapIso (Iso.refl S.X₁) (orderedShortBiprodX₁Iso l)).inv ≫
            biprod.map S.f (orderedShortBiprod l).f ≫
            (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).hom := by
              exact congrArg
                (fun k ↦ (biprod.mapIso (Iso.refl S.X₁) (orderedShortBiprodX₁Iso l)).inv ≫
                  k ≫
                  (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).hom)
                (shortComplexBiprodFMap S (orderedShortBiprod l))
    _ =
          biprod.map S.f
            ((orderedShortBiprodX₁Iso  l).inv ≫
              (orderedShortBiprod  l).f ≫
              (orderedShortBiprodX₂Iso  l).hom) := by
                simpa [Category.assoc] using
                  biprodMapIsoTransportRight S.f (orderedShortBiprod l).f
                    (orderedShortBiprodX₁Iso l) (orderedShortBiprodX₂Iso l)

/-- Helper for Lemma 12.11.3: transporting the second differential of an ordered short biproduct
through the recursive `X₂/X₃` identifications yields the expected `biprod.map` normal form. -/
lemma orderedShortBiprodGCons
    (S : ShortComplex A) (l : List (ShortComplex A)) :
    (orderedShortBiprodX₂Iso  (S :: l)).inv ≫
        (orderedShortBiprod  (S :: l)).g ≫
        (orderedShortBiprodX₃Iso  (S :: l)).hom =
      biprod.map S.g
        ((orderedShortBiprodX₂Iso  l).inv ≫
          (orderedShortBiprod  l).g ≫
          (orderedShortBiprodX₃Iso  l).hom) := by
  letI : PreservesBinaryBiproducts (ShortComplex.π₂ : ShortComplex A ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₂ : ShortComplex A ⥤ A)
  letI : PreservesBinaryBiproducts (ShortComplex.π₃ : ShortComplex A ⥤ A) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (ShortComplex.π₃ : ShortComplex A ⥤ A)
  -- The backward differential is transported by the same one-layer normalization.
  calc
    (orderedShortBiprodX₂Iso  (S :: l)).inv ≫
          (orderedShortBiprod  (S :: l)).g ≫
          (orderedShortBiprodX₃Iso  (S :: l)).hom
        =
          (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).inv ≫
            ((ShortComplex.π₂.mapBiprod S (orderedShortBiprod l)).inv ≫
              (S ⊞ orderedShortBiprod l).g ≫
              (ShortComplex.π₃.mapBiprod S (orderedShortBiprod l)).hom) ≫
            (biprod.mapIso (Iso.refl S.X₃) (orderedShortBiprodX₃Iso l)).hom := by
              simp [orderedShortBiprodX₂Iso, orderedShortBiprodX₃Iso, orderedShortBiprod,
                Iso.trans_hom, Iso.trans_inv, Category.assoc]
              rfl
    _ =
          (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).inv ≫
            biprod.map S.g (orderedShortBiprod l).g ≫
            (biprod.mapIso (Iso.refl S.X₃) (orderedShortBiprodX₃Iso l)).hom := by
              exact congrArg
                (fun k ↦ (biprod.mapIso (Iso.refl S.X₂) (orderedShortBiprodX₂Iso l)).inv ≫
                  k ≫
                  (biprod.mapIso (Iso.refl S.X₃) (orderedShortBiprodX₃Iso l)).hom)
                (shortComplexBiprodGMap S (orderedShortBiprod l))
    _ =
          biprod.map S.g
            ((orderedShortBiprodX₂Iso  l).inv ≫
              (orderedShortBiprod  l).g ≫
              (orderedShortBiprodX₃Iso  l).hom) := by
                simpa [Category.assoc] using
                  biprodMapIsoTransportRight S.g (orderedShortBiprod l).g
                    (orderedShortBiprodX₂Iso l) (orderedShortBiprodX₃Iso l)

/-- Helper for Lemma 12.11.3: after choosing target identifications for the tail `X₁/X₂`
components, the first differential of a head-plus-tail ordered short biproduct becomes the
corresponding transported `biprod.map`. -/
lemma orderedShortBiprodFConsTransport
    (S : ShortComplex A) (l : List (ShortComplex A))
    {L₁ L₂ : A}
    (e₁ : ordered_biprod (l.map ShortComplex.X₁) ≅ L₁)
    (e₂ : ordered_biprod (l.map ShortComplex.X₂) ≅ L₂) :
    ((orderedShortBiprodX₁Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₁) e₁).inv ≫
        (orderedShortBiprod  (S :: l)).f ≫
        (orderedShortBiprodX₂Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₂) e₂).hom) =
      biprod.map S.f
        (e₁.inv ≫
          (orderedShortBiprodX₁Iso  l).inv ≫
          (orderedShortBiprod  l).f ≫
          (orderedShortBiprodX₂Iso  l).hom ≫
          e₂.hom) := by
  -- First split off the outer `biprod.mapIso` transports from the recursive ordered-biproduct
  -- identification, then rewrite the middle term by the owner-level `f` transport formula.
  calc
    ((orderedShortBiprodX₁Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₁) e₁).inv ≫
          (orderedShortBiprod  (S :: l)).f ≫
          (orderedShortBiprodX₂Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₂) e₂).hom)
        =
          (biprod.mapIso (Iso.refl S.X₁) e₁).inv ≫
            biprod.map S.f
              ((orderedShortBiprodX₁Iso  l).inv ≫
                (orderedShortBiprod  l).f ≫
                (orderedShortBiprodX₂Iso  l).hom) ≫
            (biprod.mapIso (Iso.refl S.X₂) e₂).hom := by
              simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv] using
                (calc
                  biprod.map (𝟙 S.X₁) e₁.inv ≫
                      (orderedShortBiprodX₁Iso  (S :: l)).inv ≫
                      (orderedShortBiprod  (S :: l)).f ≫
                      (orderedShortBiprodX₂Iso  (S :: l)).hom ≫
                      biprod.map (𝟙 S.X₂) e₂.hom
                      =
                    biprod.map (𝟙 S.X₁) e₁.inv ≫
                      ((orderedShortBiprodX₁Iso  (S :: l)).inv ≫
                        (orderedShortBiprod  (S :: l)).f ≫
                        (orderedShortBiprodX₂Iso  (S :: l)).hom) ≫
                      biprod.map (𝟙 S.X₂) e₂.hom := by
                        simp [Category.assoc]
                  _ =
                    biprod.map (𝟙 S.X₁) e₁.inv ≫
                      biprod.map S.f
                        ((orderedShortBiprodX₁Iso  l).inv ≫
                          (orderedShortBiprod  l).f ≫
                          (orderedShortBiprodX₂Iso  l).hom) ≫
                      biprod.map (𝟙 S.X₂) e₂.hom := by
                        exact congrArg
                          (fun k ↦ biprod.map (𝟙 S.X₁) e₁.inv ≫
                            k ≫
                            biprod.map (𝟙 S.X₂) e₂.hom)
                          (orderedShortBiprodFCons S l))
    _ =
          biprod.map S.f
            (e₁.inv ≫
              (orderedShortBiprodX₁Iso  l).inv ≫
              (orderedShortBiprod  l).f ≫
              (orderedShortBiprodX₂Iso  l).hom ≫
              e₂.hom) := by
                simpa [Category.assoc] using
                  biprodMapIsoTransportRight S.f
                    ((orderedShortBiprodX₁Iso  l).inv ≫
                      (orderedShortBiprod  l).f ≫
                      (orderedShortBiprodX₂Iso  l).hom)
                    e₁ e₂

/-- Helper for Lemma 12.11.3: after choosing target identifications for the tail `X₂/X₃`
components, the second differential of a head-plus-tail ordered short biproduct becomes the
corresponding transported `biprod.map`. -/
lemma orderedShortBiprodGConsTransport
    (S : ShortComplex A) (l : List (ShortComplex A))
    {L₂ L₃ : A}
    (e₂ : ordered_biprod (l.map ShortComplex.X₂) ≅ L₂)
    (e₃ : ordered_biprod (l.map ShortComplex.X₃) ≅ L₃) :
    ((orderedShortBiprodX₂Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₂) e₂).inv ≫
        (orderedShortBiprod  (S :: l)).g ≫
        (orderedShortBiprodX₃Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₃) e₃).hom) =
      biprod.map S.g
        (e₂.inv ≫
          (orderedShortBiprodX₂Iso  l).inv ≫
          (orderedShortBiprod  l).g ≫
          (orderedShortBiprodX₃Iso  l).hom ≫
          e₃.hom) := by
  -- The `g` side is the same transport calculation after replacing `X₁/X₂` by `X₂/X₃`.
  calc
    ((orderedShortBiprodX₂Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₂) e₂).inv ≫
          (orderedShortBiprod  (S :: l)).g ≫
          (orderedShortBiprodX₃Iso  (S :: l) ≪≫ biprod.mapIso (Iso.refl S.X₃) e₃).hom)
        =
          (biprod.mapIso (Iso.refl S.X₂) e₂).inv ≫
            biprod.map S.g
              ((orderedShortBiprodX₂Iso  l).inv ≫
                (orderedShortBiprod  l).g ≫
                (orderedShortBiprodX₃Iso  l).hom) ≫
            (biprod.mapIso (Iso.refl S.X₃) e₃).hom := by
              simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv] using
                (calc
                  biprod.map (𝟙 S.X₂) e₂.inv ≫
                      (orderedShortBiprodX₂Iso  (S :: l)).inv ≫
                      (orderedShortBiprod  (S :: l)).g ≫
                      (orderedShortBiprodX₃Iso  (S :: l)).hom ≫
                      biprod.map (𝟙 S.X₃) e₃.hom
                      =
                    biprod.map (𝟙 S.X₂) e₂.inv ≫
                      ((orderedShortBiprodX₂Iso  (S :: l)).inv ≫
                        (orderedShortBiprod  (S :: l)).g ≫
                        (orderedShortBiprodX₃Iso  (S :: l)).hom) ≫
                      biprod.map (𝟙 S.X₃) e₃.hom := by
                        simp [Category.assoc]
                  _ =
                    biprod.map (𝟙 S.X₂) e₂.inv ≫
                      biprod.map S.g
                        ((orderedShortBiprodX₂Iso  l).inv ≫
                          (orderedShortBiprod  l).g ≫
                          (orderedShortBiprodX₃Iso  l).hom) ≫
                      biprod.map (𝟙 S.X₃) e₃.hom := by
                        exact congrArg
                          (fun k ↦ biprod.map (𝟙 S.X₂) e₂.inv ≫
                            k ≫
                            biprod.map (𝟙 S.X₃) e₃.hom)
                          (orderedShortBiprodGCons S l))
    _ =
          biprod.map S.g
            (e₂.inv ≫
              (orderedShortBiprodX₂Iso  l).inv ≫
              (orderedShortBiprod  l).g ≫
              (orderedShortBiprodX₃Iso  l).hom ≫
              e₃.hom) := by
                simpa [Category.assoc] using
                  biprodMapIsoTransportRight S.g
                    ((orderedShortBiprodX₂Iso  l).inv ≫
                      (orderedShortBiprod  l).g ≫
                      (orderedShortBiprodX₃Iso  l).hom)
                    e₂ e₃

/-- Helper for Lemma 12.11.3: the empty ordered tail has zero forward transport. -/
lemma orderedShortBiprodNilForwardMap :
    (orderedShortBiprodX₁Iso ([] : List (ShortComplex A))).inv ≫
        (orderedShortBiprod ([] : List (ShortComplex A))).f ≫
        (orderedShortBiprodX₂Iso ([] : List (ShortComplex A))).hom =
      (0 : ordered_biprod (([] : List (ShortComplex A)).map ShortComplex.X₁) ⟶
        ordered_biprod (([] : List (ShortComplex A)).map ShortComplex.X₂)) := by
  -- The empty ordered short biproduct is the zero short complex.
  simp [orderedShortBiprod, orderedShortBiprodX₁Iso, orderedShortBiprodX₂Iso]
  rfl

/-- Helper for Lemma 12.11.3: the empty ordered tail has zero backward transport. -/
lemma orderedShortBiprodNilBackwardMap :
    (orderedShortBiprodX₂Iso ([] : List (ShortComplex A))).inv ≫
        (orderedShortBiprod ([] : List (ShortComplex A))).g ≫
        (orderedShortBiprodX₃Iso ([] : List (ShortComplex A))).hom =
      (0 : ordered_biprod (([] : List (ShortComplex A)).map ShortComplex.X₂) ⟶
        ordered_biprod (([] : List (ShortComplex A)).map ShortComplex.X₃)) := by
  -- The same zero-short-complex calculation handles the backward differential.
  simp [orderedShortBiprod, orderedShortBiprodX₂Iso, orderedShortBiprodX₃Iso]
  rfl

/-- Helper for Lemma 12.11.3: adding the same ordered-biproduct head to both sides of a list
equality turns the resulting `eqToIso` into the corresponding `biprod.mapIso`. -/
lemma orderedBiprodConsEqToIso {X : A} {l₁ l₂ : List A} (h : l₁ = l₂) :
    eqToIso (congrArg ordered_biprod (congrArg (List.cons X) h)) =
      biprod.mapIso (Iso.refl X) (eqToIso (congrArg ordered_biprod h)) := by
  subst h
  apply Iso.ext
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp [ordered_biprod, biprod.mapIso]
  · simp [ordered_biprod, biprod.mapIso]

/-- Helper for Lemma 12.11.3: the paired tail-map equality packaged as a reusable proposition for
the induction on the positive and negative short-exact blocks. -/
abbrev signedTailMapPairProp
    (pos neg : List { S : ShortComplex A // S.ShortExact }) : Prop :=
  let tail0 : List (ShortComplex A) :=
    (pos.map (degreeZeroPresentationBlock )) ++
      (neg.map (degreeOnePresentationBlock ))
  let tail1 : List (ShortComplex A) :=
    (pos.map (degreeOnePresentationBlock )) ++
      (neg.map (degreeZeroPresentationBlock ))
  let tail0X₁Iso :
      ordered_biprod (tail0.map ShortComplex.X₁) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₂) ++
            neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail0X₂Iso :
      ordered_biprod (tail0.map ShortComplex.X₂) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            neg.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail1X₁Iso :
      ordered_biprod (tail1.map ShortComplex.X₁) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            neg.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  let tail1X₂Iso :
      ordered_biprod (tail1.map ShortComplex.X₂) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₂) ++
            neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  let tail0X₃Iso :
      ordered_biprod (tail0.map ShortComplex.X₃) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₂) ++
            neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail1X₃Iso :
      ordered_biprod (tail1.map ShortComplex.X₃) ≅
        ordered_biprod
          (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            neg.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  ((tail0X₁Iso.inv ≫
        (orderedShortBiprodX₁Iso  tail0).inv ≫
        (orderedShortBiprod  tail0).f ≫
        (orderedShortBiprodX₂Iso  tail0).hom ≫
        tail0X₂Iso.hom) =
      (tail1X₂Iso.inv ≫
        (orderedShortBiprodX₂Iso  tail1).inv ≫
        (orderedShortBiprod  tail1).g ≫
        (orderedShortBiprodX₃Iso  tail1).hom ≫
        tail1X₃Iso.hom)) ∧
    ((tail0X₂Iso.inv ≫
        (orderedShortBiprodX₂Iso  tail0).inv ≫
        (orderedShortBiprod  tail0).g ≫
        (orderedShortBiprodX₃Iso  tail0).hom ≫
        tail0X₃Iso.hom) =
      (tail1X₁Iso.inv ≫
        (orderedShortBiprodX₁Iso  tail1).inv ≫
        (orderedShortBiprod  tail1).f ≫
        (orderedShortBiprodX₂Iso  tail1).hom ≫
        tail1X₂Iso.hom))

/-- Helper for Lemma 12.11.3: the empty positive and negative tails already satisfy the paired
forward/backward map equality. -/
lemma signedTailMapPairNil :
    signedTailMapPairProp (A := A) ([] : List { S : ShortComplex A // S.ShortExact }) [] := by
  -- The empty positive/negative tail is the zero short complex, so both transported maps vanish.
  constructor <;>
    simp [orderedShortBiprod, orderedShortBiprodX₁Iso, orderedShortBiprodX₂Iso,
      orderedShortBiprodX₃Iso]

/-- Helper for Lemma 12.11.3: nested induction on the positive and negative lists proves the
packaged paired tail-map identity without introducing extra prefix-transport scaffolding. -/
lemma signedTailMapPairCore :
    ∀ pos neg : List { S : ShortComplex A // S.ShortExact },
      signedTailMapPairProp (A := A) pos neg := by
  intro pos
  induction pos with
  | nil =>
      intro neg
      induction neg with
      | nil =>
          simpa using signedTailMapPairNil (A := A)
      | cons S neg ih =>
          have hNeg1X1 :
              (neg.map degreeOnePresentationBlock).map ShortComplex.X₁ =
                neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
            simpa using map_degreeOnePresentationBlock_X₁ (l := neg)
          have hNeg1X2 :
              (neg.map degreeOnePresentationBlock).map ShortComplex.X₂ =
                neg.map (fun T ↦ T.1.X₂) := by
            simpa using map_degreeOnePresentationBlock_X₂ (l := neg)
          have hNeg1X3 :
              (neg.map degreeOnePresentationBlock).map ShortComplex.X₃ =
                neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
            simpa using map_degreeOnePresentationBlock_X₃ (l := neg)
          have hNeg0X1 :
              (neg.map degreeZeroPresentationBlock).map ShortComplex.X₁ =
                neg.map (fun T ↦ T.1.X₂) := by
            simpa using map_degreeZeroPresentationBlock_X₁ (l := neg)
          have hNeg0X2 :
              (neg.map degreeZeroPresentationBlock).map ShortComplex.X₂ =
                neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
            simpa using map_degreeZeroPresentationBlock_X₂ (l := neg)
          have hNeg0X3 :
              (neg.map degreeZeroPresentationBlock).map ShortComplex.X₃ =
                neg.map (fun T ↦ T.1.X₂) := by
            simpa using map_degreeZeroPresentationBlock_X₃ (l := neg)
          have ihNeg1 :
              (eqToIso (congrArg ordered_biprod hNeg1X1)).inv ≫
                  (orderedShortBiprodX₁Iso (neg.map degreeOnePresentationBlock)).inv ≫
                  (orderedShortBiprod (neg.map degreeOnePresentationBlock)).f ≫
                  (orderedShortBiprodX₂Iso (neg.map degreeOnePresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hNeg1X2)).hom =
                (eqToIso (congrArg ordered_biprod hNeg0X2)).inv ≫
                  (orderedShortBiprodX₂Iso (neg.map degreeZeroPresentationBlock)).inv ≫
                  (orderedShortBiprod (neg.map degreeZeroPresentationBlock)).g ≫
                  (orderedShortBiprodX₃Iso (neg.map degreeZeroPresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hNeg0X3)).hom := by
            simpa [signedTailMapPairProp] using ih.1
          have ihNeg2 :
              (eqToIso (congrArg ordered_biprod hNeg1X2)).inv ≫
                  (orderedShortBiprodX₂Iso (neg.map degreeOnePresentationBlock)).inv ≫
                  (orderedShortBiprod (neg.map degreeOnePresentationBlock)).g ≫
                  (orderedShortBiprodX₃Iso (neg.map degreeOnePresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hNeg1X3)).hom =
                (eqToIso (congrArg ordered_biprod hNeg0X1)).inv ≫
                  (orderedShortBiprodX₁Iso (neg.map degreeZeroPresentationBlock)).inv ≫
                  (orderedShortBiprod (neg.map degreeZeroPresentationBlock)).f ≫
                  (orderedShortBiprodX₂Iso (neg.map degreeZeroPresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hNeg0X2)).hom := by
            simpa [signedTailMapPairProp] using ih.2
          -- With no positive blocks left, the next negative block sits at the head of both tails,
          -- so the recursive transport lemmas reduce both equalities to the induction hypothesis.
          constructor
          · suffices h : _ by
              simpa [orderedBiprodConsEqToIso] using h
            calc
              _ =
                  biprod.map (degreeOnePresentationBlock S).f
                    ((eqToIso (congrArg ordered_biprod hNeg1X1)).inv ≫
                      (orderedShortBiprodX₁Iso (neg.map degreeOnePresentationBlock)).inv ≫
                      (orderedShortBiprod (neg.map degreeOnePresentationBlock)).f ≫
                      (orderedShortBiprodX₂Iso (neg.map degreeOnePresentationBlock)).hom ≫
                      (eqToIso (congrArg ordered_biprod hNeg1X2)).hom) := by
                    simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                      (orderedShortBiprodFConsTransport
                        (S := degreeOnePresentationBlock S)
                        (l := neg.map degreeOnePresentationBlock)
                        (e₁ := eqToIso (congrArg ordered_biprod hNeg1X1))
                        (e₂ := eqToIso (congrArg ordered_biprod hNeg1X2)))
              _ =
                  biprod.map (degreeZeroPresentationBlock S).g
                    ((eqToIso (congrArg ordered_biprod hNeg0X2)).inv ≫
                      (orderedShortBiprodX₂Iso (neg.map degreeZeroPresentationBlock)).inv ≫
                      (orderedShortBiprod (neg.map degreeZeroPresentationBlock)).g ≫
                      (orderedShortBiprodX₃Iso (neg.map degreeZeroPresentationBlock)).hom ≫
                      (eqToIso (congrArg ordered_biprod hNeg0X3)).hom) := by
                    rw [ihNeg1]
                    simp
              _ = _ := by
                    symm
                    simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                      (orderedShortBiprodGConsTransport
                        (S := degreeZeroPresentationBlock S)
                        (l := neg.map degreeZeroPresentationBlock)
                        (e₂ := eqToIso (congrArg ordered_biprod hNeg0X2))
                        (e₃ := eqToIso (congrArg ordered_biprod hNeg0X3)))
          · suffices h : _ by
              simpa [orderedBiprodConsEqToIso] using h
            calc
              _ =
                  biprod.map (degreeOnePresentationBlock S).g
                    ((eqToIso (congrArg ordered_biprod hNeg1X2)).inv ≫
                      (orderedShortBiprodX₂Iso (neg.map degreeOnePresentationBlock)).inv ≫
                      (orderedShortBiprod (neg.map degreeOnePresentationBlock)).g ≫
                      (orderedShortBiprodX₃Iso (neg.map degreeOnePresentationBlock)).hom ≫
                      (eqToIso (congrArg ordered_biprod hNeg1X3)).hom) := by
                    simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                      (orderedShortBiprodGConsTransport
                        (S := degreeOnePresentationBlock S)
                        (l := neg.map degreeOnePresentationBlock)
                        (e₂ := eqToIso (congrArg ordered_biprod hNeg1X2))
                        (e₃ := eqToIso (congrArg ordered_biprod hNeg1X3)))
              _ =
                  biprod.map (degreeZeroPresentationBlock S).f
                    ((eqToIso (congrArg ordered_biprod hNeg0X1)).inv ≫
                      (orderedShortBiprodX₁Iso (neg.map degreeZeroPresentationBlock)).inv ≫
                      (orderedShortBiprod (neg.map degreeZeroPresentationBlock)).f ≫
                      (orderedShortBiprodX₂Iso (neg.map degreeZeroPresentationBlock)).hom ≫
                      (eqToIso (congrArg ordered_biprod hNeg0X2)).hom) := by
                    rw [ihNeg2]
                    simp
              _ = _ := by
                    symm
                    simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                      (orderedShortBiprodFConsTransport
                        (S := degreeZeroPresentationBlock S)
                        (l := neg.map degreeZeroPresentationBlock)
                        (e₁ := eqToIso (congrArg ordered_biprod hNeg0X1))
                        (e₂ := eqToIso (congrArg ordered_biprod hNeg0X2)))
  | cons S pos ih =>
      intro neg
      have hRest0X1 :
          ((pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock).map
            ShortComplex.X₁) =
            pos.map (fun T ↦ T.1.X₂) ++ neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeZeroPresentationBlock_X₁ (l := pos))
            (map_degreeOnePresentationBlock_X₁ (l := neg))
      have hRest0X2 :
          ((pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock).map
            ShortComplex.X₂) =
            pos.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) ++ neg.map (fun T ↦ T.1.X₂) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeZeroPresentationBlock_X₂ (l := pos))
            (map_degreeOnePresentationBlock_X₂ (l := neg))
      have hRest0X3 :
          ((pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock).map
            ShortComplex.X₃) =
            pos.map (fun T ↦ T.1.X₂) ++ neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeZeroPresentationBlock_X₃ (l := pos))
            (map_degreeOnePresentationBlock_X₃ (l := neg))
      have hRest1X1 :
          ((pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock).map
            ShortComplex.X₁) =
            pos.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) ++ neg.map (fun T ↦ T.1.X₂) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeOnePresentationBlock_X₁ (l := pos))
            (map_degreeZeroPresentationBlock_X₁ (l := neg))
      have hRest1X2 :
          ((pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock).map
            ShortComplex.X₂) =
            pos.map (fun T ↦ T.1.X₂) ++ neg.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeOnePresentationBlock_X₂ (l := pos))
            (map_degreeZeroPresentationBlock_X₂ (l := neg))
      have hRest1X3 :
          ((pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock).map
            ShortComplex.X₃) =
            pos.map (fun T ↦ T.1.X₁ ⊞ T.1.X₃) ++ neg.map (fun T ↦ T.1.X₂) := by
        simpa [List.map_append] using
          congrArg₂ List.append
            (map_degreeOnePresentationBlock_X₃ (l := pos))
            (map_degreeZeroPresentationBlock_X₃ (l := neg))
      -- A positive block contributes a degree-`0` head on the left tail and a degree-`1` head on
      -- the right tail; after transporting those heads, the two component maps agree by the
      -- recursive hypothesis on the remaining tails.
      constructor
      · suffices h : _ by
          simpa [orderedBiprodConsEqToIso] using h
        calc
          _ =
              biprod.map (degreeZeroPresentationBlock S).f
                ((eqToIso (congrArg ordered_biprod hRest0X1)).inv ≫
                  (orderedShortBiprodX₁Iso
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).inv ≫
                  (orderedShortBiprod
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).f ≫
                  (orderedShortBiprodX₂Iso
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hRest0X2)).hom) := by
                simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                  (orderedShortBiprodFConsTransport
                    (S := degreeZeroPresentationBlock S)
                    (l := pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)
                    (e₁ := eqToIso (congrArg ordered_biprod hRest0X1))
                    (e₂ := eqToIso (congrArg ordered_biprod hRest0X2)))
          _ =
              biprod.map (degreeOnePresentationBlock S).g
                ((eqToIso (congrArg ordered_biprod hRest1X2)).inv ≫
                  (orderedShortBiprodX₂Iso
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).inv ≫
                  (orderedShortBiprod
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).g ≫
                  (orderedShortBiprodX₃Iso
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hRest1X3)).hom) := by
                rw [(ih neg).1]
                simp
          _ = _ := by
                symm
                simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                  (orderedShortBiprodGConsTransport
                    (S := degreeOnePresentationBlock S)
                    (l := pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)
                    (e₂ := eqToIso (congrArg ordered_biprod hRest1X2))
                    (e₃ := eqToIso (congrArg ordered_biprod hRest1X3)))
      · suffices h : _ by
          simpa [orderedBiprodConsEqToIso] using h
        calc
          _ =
              biprod.map (degreeZeroPresentationBlock S).g
                ((eqToIso (congrArg ordered_biprod hRest0X2)).inv ≫
                  (orderedShortBiprodX₂Iso
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).inv ≫
                  (orderedShortBiprod
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).g ≫
                  (orderedShortBiprodX₃Iso
                    (pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hRest0X3)).hom) := by
                simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                  (orderedShortBiprodGConsTransport
                    (S := degreeZeroPresentationBlock S)
                    (l := pos.map degreeZeroPresentationBlock ++ neg.map degreeOnePresentationBlock)
                    (e₂ := eqToIso (congrArg ordered_biprod hRest0X2))
                    (e₃ := eqToIso (congrArg ordered_biprod hRest0X3)))
          _ =
              biprod.map (degreeOnePresentationBlock S).f
                ((eqToIso (congrArg ordered_biprod hRest1X1)).inv ≫
                  (orderedShortBiprodX₁Iso
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).inv ≫
                  (orderedShortBiprod
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).f ≫
                  (orderedShortBiprodX₂Iso
                    (pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)).hom ≫
                  (eqToIso (congrArg ordered_biprod hRest1X2)).hom) := by
                rw [(ih neg).2]
                simp
          _ = _ := by
                symm
                simpa [biprod.mapIso, Iso.trans_hom, Iso.trans_inv, Category.assoc] using
                  (orderedShortBiprodFConsTransport
                    (S := degreeOnePresentationBlock S)
                    (l := pos.map degreeOnePresentationBlock ++ neg.map degreeZeroPresentationBlock)
                    (e₁ := eqToIso (congrArg ordered_biprod hRest1X1))
                    (e₂ := eqToIso (congrArg ordered_biprod hRest1X2)))
/-- Helper for Lemma 12.11.3: the two signed tails have the same transported forward/backward
maps after grouping the positive and negative summands. -/
lemma signedTailMapPair :
    ∀ pos neg : List { S : ShortComplex A // S.ShortExact },
      let tail0 : List (ShortComplex A) :=
        (pos.map (degreeZeroPresentationBlock )) ++
          (neg.map (degreeOnePresentationBlock ))
      let tail1 : List (ShortComplex A) :=
        (pos.map (degreeOnePresentationBlock )) ++
          (neg.map (degreeZeroPresentationBlock ))
      let tail0X₁Iso :
          ordered_biprod (tail0.map ShortComplex.X₁) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₂) ++
                neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail0, Function.comp]
      let tail0X₂Iso :
          ordered_biprod (tail0.map ShortComplex.X₂) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
                neg.map (fun S ↦ S.1.X₂)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail0, Function.comp]
      let tail1X₁Iso :
          ordered_biprod (tail1.map ShortComplex.X₁) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
                neg.map (fun S ↦ S.1.X₂)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail1, Function.comp]
      let tail1X₂Iso :
          ordered_biprod (tail1.map ShortComplex.X₂) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₂) ++
                neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail1, Function.comp]
      let tail0X₃Iso :
          ordered_biprod (tail0.map ShortComplex.X₃) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₂) ++
                neg.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail0, Function.comp]
      let tail1X₃Iso :
          ordered_biprod (tail1.map ShortComplex.X₃) ≅
            ordered_biprod
              (pos.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
                neg.map (fun S ↦ S.1.X₂)) :=
        eqToIso <|
          congrArg ordered_biprod <|
            by
              simpa [tail1, Function.comp]
      ((tail0X₁Iso.inv ≫
            (orderedShortBiprodX₁Iso  tail0).inv ≫
            (orderedShortBiprod  tail0).f ≫
            (orderedShortBiprodX₂Iso  tail0).hom ≫
            tail0X₂Iso.hom) =
          (tail1X₂Iso.inv ≫
            (orderedShortBiprodX₂Iso  tail1).inv ≫
            (orderedShortBiprod  tail1).g ≫
            (orderedShortBiprodX₃Iso  tail1).hom ≫
            tail1X₃Iso.hom)) ∧
        ((tail0X₂Iso.inv ≫
            (orderedShortBiprodX₂Iso  tail0).inv ≫
            (orderedShortBiprod  tail0).g ≫
            (orderedShortBiprodX₃Iso  tail0).hom ≫
            tail0X₃Iso.hom) =
          (tail1X₁Iso.inv ≫
            (orderedShortBiprodX₁Iso  tail1).inv ≫
            (orderedShortBiprod  tail1).f ≫
            (orderedShortBiprodX₂Iso  tail1).hom ≫
            tail1X₂Iso.hom)) := by
  -- Route correction: the nested induction in `signedTailMapPairCore` eliminates the earlier
  -- prefix-transport mismatch by always stripping the next block from the actual head of each
  -- ordered short biproduct.
  intro pos neg
  simpa [signedTailMapPairProp] using signedTailMapPairCore (A := A) pos neg

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: the degree-`0` tail assembled from a signed short-exact
presentation is exact. -/
lemma signedPresentationTailDegreeZeroExact
    {P₀ Q₀ : P.FullSubcategory} (w : SignedShortExactPresentation P P₀ Q₀) :
    (orderedShortBiprod
      ((w.positiveSeqs.map (degreeZeroPresentationBlock )) ++
        (w.negativeSeqs.map (degreeOnePresentationBlock )))).Exact := by
  -- Each block in the ordered degree-`0` tail is exact on its own.
  apply orderedShortBiprodExact
  intro S hS
  rcases List.mem_append.mp hS with hS | hS
  · rcases List.mem_map.mp hS with ⟨T, -, rfl⟩
    exact positivePresentationBlockDegreeZeroExact T
  · rcases List.mem_map.mp hS with ⟨T, -, rfl⟩
    exact positivePresentationBlockDegreeOneExact T

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: the degree-`1` tail assembled from a signed short-exact
presentation is exact. -/
lemma signedPresentationTailDegreeOneExact
    {P₀ Q₀ : P.FullSubcategory} (w : SignedShortExactPresentation P P₀ Q₀) :
    (orderedShortBiprod
      ((w.positiveSeqs.map (degreeOnePresentationBlock )) ++
        (w.negativeSeqs.map (degreeZeroPresentationBlock )))).Exact := by
  -- The degree-`1` tail is the same blockwise exactness statement with the two block shapes
  -- swapped.
  apply orderedShortBiprodExact
  intro S hS
  rcases List.mem_append.mp hS with hS | hS
  · rcases List.mem_map.mp hS with ⟨T, -, rfl⟩
    exact positivePresentationBlockDegreeOneExact T
  · rcases List.mem_map.mp hS with ⟨T, -, rfl⟩
    exact positivePresentationBlockDegreeZeroExact T

/-- Helper for Lemma 12.11.3: if the two homology objects of the cyclic complex lie in the Serre
subcategory, then its image in the quotient is acyclic. -/
lemma cyclicComplexAcyclicOfHomologyIso
    {P₀ Q₀ : P.FullSubcategory}
    {M : A} {φ ψ : M ⟶ M} {hφψ : φ ≫ ψ = 0} {hψφ : ψ ≫ φ = 0}
    (e₀ : (cyclicCochainComplex φ ψ hφψ hψφ).homology 0 ≅ P₀.1)
    (e₁ : (cyclicCochainComplex φ ψ hφψ hψφ).homology 1 ≅ Q₀.1) :
    (((Q).mapHomologicalComplex (up (ZMod 2))).obj
      (cyclicCochainComplex φ ψ hφψ hψφ)).Acyclic := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  have hzeroP₀ : IsZero ((Q).obj P₀.1) :=
    (isZero_obj_iff P.isoModSerre.Q P P₀.1).2 P₀.2
  have hzeroQ₀ : IsZero ((Q).obj Q₀.1) :=
    (isZero_obj_iff P.isoModSerre.Q P Q₀.1).2 Q₀.2
  -- Each homology object becomes zero in the quotient because it is identified with an object of
  -- the Serre subcategory.
  have hzero0 :
      IsZero ((((Q).mapHomologicalComplex (up (ZMod 2))).obj K).homology 0) := by
    exact (hzeroP₀.of_iso ((Q).mapIso e₀)).of_iso
      (quotient_homology_iso P (up (ZMod 2)) K 0)
  have hzero1 :
      IsZero ((((Q).mapHomologicalComplex (up (ZMod 2))).obj K).homology 1) := by
    exact (hzeroQ₀.of_iso ((Q).mapIso e₁)).of_iso
      (quotient_homology_iso P (up (ZMod 2)) K 1)
  -- A `ZMod 2` complex is acyclic once exactness holds at its two degrees.
  rw [HomologicalComplex.acyclic_iff]
  intro i
  fin_cases i
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hzero0
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hzero1

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: a zero head block followed by an exact tail has homology `P₀` in
degree `0`. -/
theorem headPlusExactTailDegreeZeroHomologyIso
    {P₀ Q₀ : P.FullSubcategory} (tail : List (ShortComplex A))
    (hTail : (orderedShortBiprod tail).Exact) :
    Nonempty
      (((orderedShortBiprod 
        (ShortComplex.mk (0 : Q₀.1 ⟶ P₀.1) (0 : P₀.1 ⟶ Q₀.1) zero_comp :: tail)).homology ≅
          P₀.1)) := by
  let head : ShortComplex A :=
    ShortComplex.mk (0 : Q₀.1 ⟶ P₀.1) (0 : P₀.1 ⟶ Q₀.1) zero_comp
  rcases biprodHomologyIsoLeftOfExactRight (A := A) (S := head)
      (T := orderedShortBiprod tail) hTail with ⟨eTail⟩
  rcases zeroZeroShortComplexHomologyIsoMiddle (A := A)
      (X := Q₀.1) (Y := P₀.1) (Z := Q₀.1) with ⟨eHead⟩
  -- The zero head carries all the homology once the tail is exact.
  exact ⟨by
    simpa [head, orderedShortBiprod] using eTail ≪≫ eHead⟩

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: a zero head block followed by an exact tail has homology `Q₀` in
degree `1`. -/
theorem headPlusExactTailDegreeOneHomologyIso
    {P₀ Q₀ : P.FullSubcategory} (tail : List (ShortComplex A))
    (hTail : (orderedShortBiprod tail).Exact) :
    Nonempty
      (((orderedShortBiprod 
        (ShortComplex.mk (0 : P₀.1 ⟶ Q₀.1) (0 : Q₀.1 ⟶ P₀.1) zero_comp :: tail)).homology ≅
          Q₀.1)) := by
  let head : ShortComplex A :=
    ShortComplex.mk (0 : P₀.1 ⟶ Q₀.1) (0 : Q₀.1 ⟶ P₀.1) zero_comp
  rcases biprodHomologyIsoLeftOfExactRight (A := A) (S := head)
      (T := orderedShortBiprod tail) hTail with ⟨eTail⟩
  rcases zeroZeroShortComplexHomologyIsoMiddle (A := A)
      (X := P₀.1) (Y := Q₀.1) (Z := P₀.1) with ⟨eHead⟩
  -- The same reduction identifies the degree-`1` homology with the zero head block.
  exact ⟨by
    simpa [head, orderedShortBiprod] using eTail ≪≫ eHead⟩

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: a degree-`0` cyclic window isomorphism yields a homology
identification for the ambient cyclic complex. -/
theorem cyclicDegreeZeroHomologyIsoOfWindow
    {P₀ : P.FullSubcategory}
    {M : A} {φ ψ : M ⟶ M} {hφψ : φ ≫ ψ = 0} {hψφ : ψ ≫ φ = 0}
    {G0 : ShortComplex A}
    (hSc0 : (cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1 ≅ G0)
    (eG0 : G0.homology ≅ P₀.1) :
    Nonempty ((cyclicCochainComplex φ ψ hφψ hψφ).homology 0 ≅ P₀.1) := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  have hprev0 : (up (ZMod 2)).prev 0 = 1 :=
    ComplexShape.prev_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  have hnext0 : (up (ZMod 2)).next 0 = 1 :=
    ComplexShape.next_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  -- Route the degree-`0` homology computation through the corresponding short-complex window.
  exact ⟨K.homologyIsoSc' 1 0 1 hprev0 hnext0 ≪≫
    ShortComplex.homologyMapIso hSc0 ≪≫
      eG0⟩

omit [P.IsSerreClass] in
/-- Helper for Lemma 12.11.3: a degree-`1` cyclic window isomorphism yields a homology
identification for the ambient cyclic complex. -/
theorem cyclicDegreeOneHomologyIsoOfWindow
    {Q₀ : P.FullSubcategory}
    {M : A} {φ ψ : M ⟶ M} {hφψ : φ ≫ ψ = 0} {hψφ : ψ ≫ φ = 0}
    {G1 : ShortComplex A}
    (hSc1 : (cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0 ≅ G1)
    (eG1 : G1.homology ≅ Q₀.1) :
    Nonempty ((cyclicCochainComplex φ ψ hφψ hψφ).homology 1 ≅ Q₀.1) := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  have hprev1 : (up (ZMod 2)).prev 1 = 0 :=
    ComplexShape.prev_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  have hnext1 : (up (ZMod 2)).next 1 = 0 :=
    ComplexShape.next_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  -- Route the degree-`1` homology computation through the complementary cyclic window.
  exact ⟨K.homologyIsoSc' 0 1 0 hprev1 hnext1 ≪≫
    ShortComplex.homologyMapIso hSc1 ≪≫
      eG1⟩

/-- Helper for Lemma 12.11.3: once the two cyclic windows are identified with grouped short
complexes, their homology identifications package the exact quotient witness for the cyclic
complex. -/
lemma cyclicWitnessDataOfWindowIsos
    {P₀ Q₀ : P.FullSubcategory}
    {M : A} {φ ψ : M ⟶ M} {hφψ : φ ≫ ψ = 0} {hψφ : ψ ≫ φ = 0}
    {G0 G1 : ShortComplex A}
    (hSc0 : (cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1 ≅ G0)
    (hSc1 : (cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0 ≅ G1)
    (eG0 : G0.homology ≅ P₀.1)
    (eG1 : G1.homology ≅ Q₀.1) :
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    ∃ _ : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic,
      ∃ _ : K.homology 0 ≅ P₀.1, ∃ _ : K.homology 1 ≅ Q₀.1, True := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  -- First identify the two ambient homology objects via the chosen cyclic windows.
  rcases cyclicDegreeZeroHomologyIsoOfWindow (P := P)
      (φ := φ) (ψ := ψ) (hφψ := hφψ) (hψφ := hψφ) hSc0 eG0 with ⟨e₀⟩
  rcases cyclicDegreeOneHomologyIsoOfWindow (P := P)
      (φ := φ) (ψ := ψ) (hφψ := hφψ) (hψφ := hψφ) hSc1 eG1 with ⟨e₁⟩
  -- Those identifications place both homology objects in the Serre subcategory, so the quotient
  -- image of the cyclic complex is acyclic.
  refine ⟨cyclicComplexAcyclicOfHomologyIso (P := P) e₀ e₁, e₀, e₁, trivial⟩

/-- Helper for Lemma 12.11.3: the ordered signed short-exact presentation produces the cyclic
cochain complex from the source proof, with quotient-acyclic image and homology objects `P₀` and
`Q₀`. -/

lemma cyclic_witness_of_signed_short_exact_presentation
    {P₀ Q₀ : P.FullSubcategory} (w : SignedShortExactPresentation P P₀ Q₀) :
  ∃ (M : A) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0),
      let K := cyclicCochainComplex φ ψ hφψ hψφ
      ∃ _ : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic,
        ∃ _ : K.homology 0 ≅ P₀.1, ∃ _ : K.homology 1 ≅ Q₀.1, True := by
  classical
  -- Route correction: choose the grouped plus-side object once, define the cyclic differentials
  -- from the degree-`0` grouped window, and use the degree-`1` window only as a transported
  -- adapter for the opposite composition.
  let tail0 : List (ShortComplex A) :=
    (w.positiveSeqs.map degreeZeroPresentationBlock) ++
      (w.negativeSeqs.map degreeOnePresentationBlock)
  let tail1 : List (ShortComplex A) :=
    (w.positiveSeqs.map degreeOnePresentationBlock) ++
      (w.negativeSeqs.map degreeZeroPresentationBlock)
  let plusObj : A :=
    ordered_biprod
      (P₀.1 ::
        (w.positiveSeqs.map fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
          (w.negativeSeqs.map fun S ↦ S.1.X₂))
  let minusObj : A :=
    ordered_biprod
      (Q₀.1 ::
        (w.positiveSeqs.map fun S ↦ S.1.X₂) ++
          (w.negativeSeqs.map fun S ↦ S.1.X₁ ⊞ S.1.X₃))
  let head0 : ShortComplex A :=
    ShortComplex.mk (0 : Q₀.1 ⟶ P₀.1) (0 : P₀.1 ⟶ Q₀.1) zero_comp
  let head1 : ShortComplex A :=
    ShortComplex.mk (0 : P₀.1 ⟶ Q₀.1) (0 : Q₀.1 ⟶ P₀.1) zero_comp
  let G0 : ShortComplex A := orderedShortBiprod (head0 :: tail0)
  let G1 : ShortComplex A := orderedShortBiprod (head1 :: tail1)
  let tail0X1Iso :
      ordered_biprod (tail0.map ShortComplex.X₁) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₂) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail0X2Iso :
      ordered_biprod (tail0.map ShortComplex.X₂) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail0X3Iso :
      ordered_biprod (tail0.map ShortComplex.X₃) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₂) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail0, Function.comp]
  let tail1X1Iso :
      ordered_biprod (tail1.map ShortComplex.X₁) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  let tail1X2Iso :
      ordered_biprod (tail1.map ShortComplex.X₂) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₂) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  let tail1X3Iso :
      ordered_biprod (tail1.map ShortComplex.X₃) ≅
        ordered_biprod
          (w.positiveSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
            w.negativeSeqs.map (fun S ↦ S.1.X₂)) :=
    eqToIso <|
      congrArg ordered_biprod <|
        by
          simpa [tail1, Function.comp]
  let minusIso0X1 : G0.X₁ ≅ minusObj :=
    orderedShortBiprodX₁Iso (head0 :: tail0) ≪≫
      biprod.mapIso (Iso.refl Q₀.1) tail0X1Iso
  let plusIso0X2 : G0.X₂ ≅ plusObj :=
    orderedShortBiprodX₂Iso (head0 :: tail0) ≪≫
      biprod.mapIso (Iso.refl P₀.1) tail0X2Iso
  let minusIso0X3 : G0.X₃ ≅ minusObj :=
    orderedShortBiprodX₃Iso (head0 :: tail0) ≪≫
      biprod.mapIso (Iso.refl Q₀.1) tail0X3Iso
  let plusIso1X1 : G1.X₁ ≅ plusObj :=
    orderedShortBiprodX₁Iso (head1 :: tail1) ≪≫
      biprod.mapIso (Iso.refl P₀.1) tail1X1Iso
  let minusIso1X2 : G1.X₂ ≅ minusObj :=
    orderedShortBiprodX₂Iso (head1 :: tail1) ≪≫
      biprod.mapIso (Iso.refl Q₀.1) tail1X2Iso
  let plusIso1X3 : G1.X₃ ≅ plusObj :=
    orderedShortBiprodX₃Iso (head1 :: tail1) ≪≫
      biprod.mapIso (Iso.refl P₀.1) tail1X3Iso
  have hPosGrouped :
      w.positiveSeqs.unattach.map (fun S ↦ S.X₁ ⊞ S.X₃) =
        w.positiveSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) := by
    simpa using
      (List.map_unattach
        (xs := w.positiveSeqs) (f := fun S : ShortComplex A ↦ S.X₁ ⊞ S.X₃))
  have hNegGrouped :
      w.negativeSeqs.unattach.map (fun S ↦ S.X₁ ⊞ S.X₃) =
        w.negativeSeqs.map (fun S ↦ S.1.X₁ ⊞ S.1.X₃) := by
    simpa using
      (List.map_unattach
        (xs := w.negativeSeqs) (f := fun S : ShortComplex A ↦ S.X₁ ⊞ S.X₃))
  have hPosMiddle :
      w.positiveSeqs.unattach.map ShortComplex.X₂ =
        w.positiveSeqs.map (fun S ↦ S.1.X₂) := by
    simpa using (List.map_unattach (xs := w.positiveSeqs) (f := ShortComplex.X₂))
  have hNegMiddle :
      w.negativeSeqs.unattach.map ShortComplex.X₂ =
        w.negativeSeqs.map (fun S ↦ S.1.X₂) := by
    simpa using (List.map_unattach (xs := w.negativeSeqs) (f := ShortComplex.X₂))
  rcases signedPresentationGroupedBalanceIso (P := P) w with ⟨eRaw⟩
  have hPlusObj :
      ordered_biprod
          (P₀.1 ::
            (w.positiveSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂)) =
        plusObj := by
    calc
      ordered_biprod
          (P₀.1 ::
            (w.positiveSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃) ++
              (w.negativeSeqs.unattach.map ShortComplex.X₂))
        =
          ordered_biprod
            (P₀.1 ::
              (w.positiveSeqs.map fun S ↦ S.1.X₁ ⊞ S.1.X₃) ++
                (w.negativeSeqs.map fun S ↦ S.1.X₂)) := by
            rw [hPosGrouped, hNegMiddle]
      _ = plusObj := rfl
  have hMinusObj :
      ordered_biprod
          (Q₀.1 ::
            (w.positiveSeqs.unattach.map ShortComplex.X₂) ++
              (w.negativeSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃)) =
        minusObj := by
    calc
      ordered_biprod
          (Q₀.1 ::
            (w.positiveSeqs.unattach.map ShortComplex.X₂) ++
              (w.negativeSeqs.unattach.map fun S ↦ S.X₁ ⊞ S.X₃))
        =
          ordered_biprod
            (Q₀.1 ::
              (w.positiveSeqs.map fun S ↦ S.1.X₂) ++
                (w.negativeSeqs.map fun S ↦ S.1.X₁ ⊞ S.1.X₃)) := by
            rw [hPosMiddle, hNegGrouped]
      _ = minusObj := rfl
  let e : plusObj ≅ minusObj :=
    (eqToIso hPlusObj.symm) ≪≫ eRaw ≪≫ (eqToIso hMinusObj)
  have hTailPair :
      ((tail0X1Iso.inv ≫
            (orderedShortBiprodX₁Iso tail0).inv ≫
            (orderedShortBiprod tail0).f ≫
            (orderedShortBiprodX₂Iso tail0).hom ≫
            tail0X2Iso.hom) =
          (tail1X2Iso.inv ≫
            (orderedShortBiprodX₂Iso tail1).inv ≫
            (orderedShortBiprod tail1).g ≫
            (orderedShortBiprodX₃Iso tail1).hom ≫
            tail1X3Iso.hom)) ∧
        ((tail0X2Iso.inv ≫
            (orderedShortBiprodX₂Iso tail0).inv ≫
            (orderedShortBiprod tail0).g ≫
            (orderedShortBiprodX₃Iso tail0).hom ≫
            tail0X3Iso.hom) =
          (tail1X1Iso.inv ≫
            (orderedShortBiprodX₁Iso tail1).inv ≫
            (orderedShortBiprod tail1).f ≫
            (orderedShortBiprodX₂Iso tail1).hom ≫
            tail1X2Iso.hom)) := by
    simpa [tail0, tail1, tail0X1Iso, tail0X2Iso, tail0X3Iso, tail1X1Iso, tail1X2Iso,
      tail1X3Iso] using signedTailMapPair (A := A) w.positiveSeqs w.negativeSeqs
  have hG0f :
      minusIso0X1.inv ≫ G0.f ≫ plusIso0X2.hom =
        biprod.map (0 : Q₀.1 ⟶ P₀.1)
          (tail0X1Iso.inv ≫
            (orderedShortBiprodX₁Iso tail0).inv ≫
            (orderedShortBiprod tail0).f ≫
            (orderedShortBiprodX₂Iso tail0).hom ≫
            tail0X2Iso.hom) := by
    -- The degree-`0` head-plus-tail window transports to the grouped forward map on the minus
    -- side.
    simpa [G0, head0, minusIso0X1, plusIso0X2, Category.assoc] using
      orderedShortBiprodFConsTransport
        (S := head0) (l := tail0) tail0X1Iso tail0X2Iso
  have hG0g :
      plusIso0X2.inv ≫ G0.g ≫ minusIso0X3.hom =
        biprod.map (0 : P₀.1 ⟶ Q₀.1)
          (tail0X2Iso.inv ≫
            (orderedShortBiprodX₂Iso tail0).inv ≫
            (orderedShortBiprod tail0).g ≫
            (orderedShortBiprodX₃Iso tail0).hom ≫
            tail0X3Iso.hom) := by
    -- The second differential of the same window is the grouped backward map on the plus side.
    simpa [G0, head0, plusIso0X2, minusIso0X3, Category.assoc] using
      orderedShortBiprodGConsTransport
        (S := head0) (l := tail0) tail0X2Iso tail0X3Iso
  have hG1fRaw :
      plusIso1X1.inv ≫ G1.f ≫ minusIso1X2.hom =
        biprod.map (0 : P₀.1 ⟶ Q₀.1)
          (tail1X1Iso.inv ≫
            (orderedShortBiprodX₁Iso tail1).inv ≫
            (orderedShortBiprod tail1).f ≫
            (orderedShortBiprodX₂Iso tail1).hom ≫
            tail1X2Iso.hom) := by
    -- The degree-`1` head-plus-tail window has the same shape after swapping the two block
    -- families.
    simpa [G1, head1, plusIso1X1, minusIso1X2, Category.assoc] using
      orderedShortBiprodFConsTransport
        (S := head1) (l := tail1) tail1X1Iso tail1X2Iso
  have hG1gRaw :
      minusIso1X2.inv ≫ G1.g ≫ plusIso1X3.hom =
        biprod.map (0 : Q₀.1 ⟶ P₀.1)
          (tail1X2Iso.inv ≫
            (orderedShortBiprodX₂Iso tail1).inv ≫
            (orderedShortBiprod tail1).g ≫
            (orderedShortBiprodX₃Iso tail1).hom ≫
            tail1X3Iso.hom) := by
    -- The opposite degree-`1` differential is the transported grouped forward map.
    simpa [G1, head1, minusIso1X2, plusIso1X3, Category.assoc] using
      orderedShortBiprodGConsTransport
        (S := head1) (l := tail1) tail1X2Iso tail1X3Iso
  let ψBase : minusObj ⟶ plusObj :=
    biprod.map (0 : Q₀.1 ⟶ P₀.1)
      (tail0X1Iso.inv ≫
        (orderedShortBiprodX₁Iso tail0).inv ≫
        (orderedShortBiprod tail0).f ≫
        (orderedShortBiprodX₂Iso tail0).hom ≫
        tail0X2Iso.hom)
  let φBase : plusObj ⟶ minusObj :=
    biprod.map (0 : P₀.1 ⟶ Q₀.1)
      (tail0X2Iso.inv ≫
        (orderedShortBiprodX₂Iso tail0).inv ≫
        (orderedShortBiprod tail0).g ≫
        (orderedShortBiprodX₃Iso tail0).hom ≫
        tail0X3Iso.hom)
  have hG1f :
      plusIso1X1.inv ≫ G1.f ≫ minusIso1X2.hom = φBase := by
    -- The paired tail-transport lemma identifies the degree-`1` forward map with `φBase`.
    rw [hG1fRaw, ← hTailPair.2]
    rfl
  have hG1g :
      minusIso1X2.inv ≫ G1.g ≫ plusIso1X3.hom = ψBase := by
    -- The same lemma identifies the degree-`1` backward map with `ψBase`.
    rw [hG1gRaw, ← hTailPair.1]
    rfl
  have hψBaseφBase : ψBase ≫ φBase = 0 := by
    -- The degree-`0` short-complex relation gives the `ψ ≫ φ` square-zero identity before the
    -- final conjugation by `e`.
    calc
      ψBase ≫ φBase =
          (minusIso0X1.inv ≫ G0.f ≫ plusIso0X2.hom) ≫
            (plusIso0X2.inv ≫ G0.g ≫ minusIso0X3.hom) := by
              dsimp [ψBase, φBase]
              rw [hG0f.symm, hG0g.symm]
      _ = minusIso0X1.inv ≫ G0.f ≫ G0.g ≫ minusIso0X3.hom := by
            simp [Category.assoc]
      _ = 0 := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ minusIso0X1.inv ≫ k ≫ minusIso0X3.hom) G0.zero
  have hφBaseψBase : φBase ≫ ψBase = 0 := by
    -- The degree-`1` window gives the opposite square-zero identity.
    calc
      φBase ≫ ψBase =
          (plusIso1X1.inv ≫ G1.f ≫ minusIso1X2.hom) ≫
            (minusIso1X2.inv ≫ G1.g ≫ plusIso1X3.hom) := by
              rw [hG1f, hG1g]
      _ = plusIso1X1.inv ≫ G1.f ≫ G1.g ≫ plusIso1X3.hom := by
            simp [Category.assoc]
      _ = 0 := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ plusIso1X1.inv ≫ k ≫ plusIso1X3.hom) G1.zero
  let φ : plusObj ⟶ plusObj := φBase ≫ e.inv
  let ψ : plusObj ⟶ plusObj := e.hom ≫ ψBase
  have hφψ : φ ≫ ψ = 0 := by
    -- Transport the degree-`1` square-zero relation across the chosen balance isomorphism.
    simpa [φ, ψ, Category.assoc] using hφBaseψBase
  have hψφ : ψ ≫ φ = 0 := by
    -- The degree-`0` window provides the complementary square-zero relation.
    simpa [φ, ψ, Category.assoc] using
      congrArg (fun k ↦ e.hom ≫ k ≫ e.inv) hψBaseφBase
  have hG0f' :
      minusIso0X1.inv ≫ G0.f = ψBase ≫ plusIso0X2.inv := by
    -- Peel the codomain transport off the degree-`0` forward map to match `ShortComplex.isoMk`.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ plusIso0X2.inv) hG0f
  have hG0g' :
      plusIso0X2.inv ≫ G0.g = φBase ≫ minusIso0X3.inv := by
    -- The same normalization handles the second differential of the degree-`0` window.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ minusIso0X3.inv) hG0g
  have hG1f' :
      plusIso1X1.inv ≫ G1.f = φBase ≫ minusIso1X2.inv := by
    -- Normalize the degree-`1` forward map after rewriting its tail by `signedTailMapPair`.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ minusIso1X2.inv) hG1f
  have hG1g' :
      minusIso1X2.inv ≫ G1.g = ψBase ≫ plusIso1X3.inv := by
    -- Normalize the degree-`1` backward map in the same way.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ plusIso1X3.inv) hG1g
  let e0X1 : plusObj ≅ G0.X₁ := e ≪≫ minusIso0X1.symm
  let e0X2 : plusObj ≅ G0.X₂ := plusIso0X2.symm
  let e0X3 : plusObj ≅ G0.X₃ := e ≪≫ minusIso0X3.symm
  let e1X1 : plusObj ≅ G1.X₁ := plusIso1X1.symm
  let e1X2 : plusObj ≅ G1.X₂ := e ≪≫ minusIso1X2.symm
  let e1X3 : plusObj ≅ G1.X₃ := plusIso1X3.symm
  have hSc0f :
      e0X1.hom ≫ G0.f =
        ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1).f ≫ e0X2.hom := by
    -- The degree-`0` cyclic window is the degree-`0` head-plus-tail complex after one transport
    -- across the balance isomorphism.
    calc
      e0X1.hom ≫ G0.f =
          e.hom ≫ (minusIso0X1.inv ≫ G0.f) := by
            simp [e0X1, Category.assoc]
      _ = e.hom ≫ (ψBase ≫ plusIso0X2.inv) := by
            rw [hG0f']
      _ = ψ ≫ plusIso0X2.inv := by
            simp [ψ, Category.assoc]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1).f ≫ e0X2.hom := by
            simp [e0X2]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1).f ≫ e0X2.hom := by
            simp [HomologicalComplex.sc', cyclicCochainComplex_d_one]
  have hSc0g :
      e0X2.hom ≫ G0.g =
        ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1).g ≫
          e0X3.hom := by
    -- The second square uses the same chosen balance isomorphism on the right endpoint.
    calc
      e0X2.hom ≫ G0.g = φBase ≫ minusIso0X3.inv := by
            simpa [e0X2] using hG0g'
      _ = φBase ≫ e.inv ≫ e0X3.hom := by
            simp [e0X3]
      _ = φ ≫ e0X3.hom := by
            simp [φ, Category.assoc]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1).g ≫
            e0X3.hom := by
            simp [HomologicalComplex.sc', cyclicCochainComplex_d_zero]
  have hSc1f :
      e1X1.hom ≫ G1.f =
        ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0).f ≫
          e1X2.hom := by
    -- The opposite cyclic window is the concrete transported adapter furnished by the same
    -- `φBase`.
    calc
      e1X1.hom ≫ G1.f = φBase ≫ minusIso1X2.inv := by
            simpa [e1X1] using hG1f'
      _ = φBase ≫ e.inv ≫ e1X2.hom := by
            simp [e1X2]
      _ = φ ≫ e1X2.hom := by
            simp [φ, Category.assoc]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0).f ≫
            e1X2.hom := by
            simp [HomologicalComplex.sc', cyclicCochainComplex_d_zero]
  have hSc1g :
      e1X2.hom ≫ G1.g =
        ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0).g ≫ e1X3.hom := by
    -- The second square of the degree-`1` window uses the transported `ψBase`.
    calc
      e1X2.hom ≫ G1.g =
          e.hom ≫ (minusIso1X2.inv ≫ G1.g) := by
            simp [e1X2, Category.assoc]
      _ = e.hom ≫ (ψBase ≫ plusIso1X3.inv) := by
            rw [hG1g']
      _ = ψ ≫ plusIso1X3.inv := by
            simp [ψ, Category.assoc]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0).g ≫ e1X3.hom := by
            simp [e1X3]
      _ = ((cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0).g ≫ e1X3.hom := by
            simp [HomologicalComplex.sc', cyclicCochainComplex_d_one]
  let hSc0 :
      (cyclicCochainComplex φ ψ hφψ hψφ).sc' 1 0 1 ≅ G0 :=
    ShortComplex.isoMk e0X1 e0X2 e0X3 hSc0f hSc0g
  let hSc1 :
      (cyclicCochainComplex φ ψ hφψ hψφ).sc' 0 1 0 ≅ G1 :=
    ShortComplex.isoMk e1X1 e1X2 e1X3 hSc1f hSc1g
  rcases headPlusExactTailDegreeZeroHomologyIso (P := P) (P₀ := P₀) (Q₀ := Q₀)
      tail0 (signedPresentationTailDegreeZeroExact (P := P) w) with ⟨eG0⟩
  rcases headPlusExactTailDegreeOneHomologyIso (P := P) (P₀ := P₀) (Q₀ := Q₀)
      tail1 (signedPresentationTailDegreeOneExact (P := P) w) with ⟨eG1⟩
  refine ⟨plusObj, φ, ψ, hφψ, hψφ, ?_⟩
  -- With both cyclic windows identified with the grouped short complexes, the existing homology
  -- and quotient-acyclic packaging lemma completes the witness.
  exact cyclicWitnessDataOfWindowIsos (P := P) hSc0 hSc1 eG0 eG1

-- Proof sketch: a kernel element is represented by a formal difference of objects of the Serre
-- subcategory that becomes trivial in `K₀(A)`; organize the corresponding data as the canonical
-- `ZMod 2`-indexed cyclic cochain complex from `12.11.2.1`, require that its image in the Serre
-- quotient be exact, and read off the degree-`0` and degree-`1` homology objects in `P`.
-- Conversely, the usual Euler-characteristic computation for this cyclic complex shows that the
-- displayed difference maps to zero in `K₀(A)`.

/-- Lemma 12.11.3 (2): an element of the kernel of `K₀(\mathcal C) → K₀(\mathcal A)` is exactly
a difference `[H⁰(K)] - [H¹(K)]` coming from the canonical `ZMod 2`-indexed cyclic cochain
complex in `\mathcal A` built from the constant object `M` and alternating differentials
`\varphi, \psi`, whose image in the Serre quotient is exact and whose degree-`0` and degree-`1`
homology objects lie in the Serre subcategory `\mathcal C`. -/
@[stacks 02MX]
theorem mem_ker_serreClassInclusionK0Map_iff
    (x : AbelianK0 P.FullSubcategory) :
    x ∈ (K₀ι).ker ↔
      ∃ (M : A) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0),
      let K := cyclicCochainComplex φ ψ hφψ hψφ
      ∃ hExactQ : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic,
        x =
          K₀[⟨K.homology 0, homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 0⟩] -
            K₀[⟨K.homology 1, homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 1⟩] := by
  constructor
  · intro hx
    -- Rewrite the kernel class as a difference of two Serre-subcategory objects, then invoke the
    -- signed-presentation witness package from the source proof.
    rcases exists_object_sub_eq_of_k0 (A := P.FullSubcategory) x with ⟨P₀, Q₀, rfl⟩
    rcases exists_signed_short_exact_presentation_of_mem_ker_inclusion
        (P := P) (P₀ := P₀) (Q₀ := Q₀) rfl hx with ⟨w⟩
    rcases cyclic_witness_of_signed_short_exact_presentation (P := P) w with
        ⟨M, φ, ψ, hφψ, hψφ, hExactQ, e₀, e₁, _⟩
    refine ⟨M, φ, ψ, hφψ, hψφ, hExactQ, ?_⟩
    -- Transport the two identified homology objects back into the full subcategory `P`.
    have h0 :
        K₀[⟨(cyclicCochainComplex φ ψ hφψ hψφ).homology 0,
          homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 0⟩] = K₀[P₀] := by
      exact k0_eq_of_iso (A := P.FullSubcategory)
        (isoMk
          (P := P)
          (X := ⟨(cyclicCochainComplex φ ψ hφψ hψφ).homology 0,
            homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 0⟩)
          (Y := P₀)
          e₀)
    have h1 :
        K₀[⟨(cyclicCochainComplex φ ψ hφψ hψφ).homology 1,
          homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 1⟩] = K₀[Q₀] := by
      exact k0_eq_of_iso (A := P.FullSubcategory)
        (isoMk
          (P := P)
          (X := ⟨(cyclicCochainComplex φ ψ hφψ hψφ).homology 1,
            homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 1⟩)
          (Y := Q₀)
          e₁)
    rw [← h0, ← h1]
  · rintro ⟨M, φ, ψ, hφψ, hψφ, hExactQ, rfl⟩
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    -- The Euler characteristic of the cyclic complex cancels in `K₀(A)`, so the displayed class
    -- maps to zero under the inclusion.
    rw [AddMonoidHom.mem_ker]
    simpa [K, map_sub, AbelianK0.mapExactFunctor_apply_of] using
      cyclic_homology_classes_cancel (A := A) φ ψ hφψ hψφ

end

end

end _root_.CategoryTheory.ObjectProperty
