import StacksProject_2024.Chap12.Lemma_12_10_3
import StacksProject_2024.Chap12.Lemma_12_10_6
import StacksProject_2024.Chap12.Lemma_12_11_2
import StacksProject_2024.Chap12.«12_11_2_1»

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
  simpa [S, k0_zero_eq (A := A), add_comm] using (AbelianK0.of_shortExact S hShort).symm

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
    exact k0_eq_of_iso (A := A) (Abelian.coimageIsoImage f)
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
  -- Route the `K₀`-difference through kernel and cokernel, which both lie in the Serre class.
  have hf' := (P.isoModSerre_iff f).1 hf
  rcases sub_mem_range_of_inclusion (P := P) hf'.2 hf'.1 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [k0_sub_eq_cokernel_sub_kernel]
  exact hx

/-- Helper for Lemma 12.11.3: objects that become isomorphic in the Serre quotient differ by a
class coming from the Serre subcategory. -/
lemma k0_sub_mem_range_of_quotient_iso {X Y : A}
    (e : (P.isoModSerre.Q).obj X ≅ (P.isoModSerre.Q).obj Y) :
    K₀[Y] - K₀[X] ∈ AddMonoidHom.range K₀ι := by
  -- Express the quotient isomorphism by a left fraction `X ⟶ Y' ← Y` in the source category.
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q P.isoModSerre e.hom
  have hs : K₀[φ.Y'] - K₀[Y] ∈ AddMonoidHom.range K₀ι :=
    k0_sub_mem_range_of_isoModSerre (P := P) φ.s φ.hs
  have hmapf : e.hom ≫ (P.isoModSerre.Q).map φ.s = (P.isoModSerre.Q).map φ.f := by
    simpa [hφ] using
      MorphismProperty.LeftFraction.map_comp_map_s φ Q (Localization.inverts Q P.isoModSerre)
  haveI : IsIso ((P.isoModSerre.Q).map φ.f) := by
    letI : IsIso e.hom := by infer_instance
    letI : IsIso ((P.isoModSerre.Q).map φ.s) :=
      Localization.inverts Q P.isoModSerre φ.s φ.hs
    rw [← hmapf]
    infer_instance
  have hker : P (kernel φ.f) := by
    let eKernel : (P.isoModSerre.Q).obj (kernel φ.f) ≅ kernel ((P.isoModSerre.Q).map φ.f) :=
      CategoryTheory.Limits.PreservesKernel.iso Q φ.f
    have hzeroKernel : IsZero (kernel ((P.isoModSerre.Q).map φ.f)) := by
      exact IsZero.of_iso (isZero_zero _) (kernel.ofMono ((P.isoModSerre.Q).map φ.f))
    exact (isZero_obj_iff Q P (kernel φ.f)).1 (hzeroKernel.of_iso eKernel)
  have hcoker : P (cokernel φ.f) := by
    let eCokernel : (P.isoModSerre.Q).obj (cokernel φ.f) ≅ cokernel ((P.isoModSerre.Q).map φ.f) :=
      CategoryTheory.Limits.PreservesCokernel.iso Q φ.f
    have hzeroCokernel : IsZero (cokernel ((P.isoModSerre.Q).map φ.f)) := by
      exact IsZero.of_iso (isZero_zero _) (cokernel.ofEpi ((P.isoModSerre.Q).map φ.f))
    exact (isZero_obj_iff Q P (cokernel φ.f)).1 (hzeroCokernel.of_iso eCokernel)
  have hf : K₀[φ.Y'] - K₀[X] ∈ AddMonoidHom.range K₀ι := by
    -- The numerator of the fraction also becomes an isomorphism modulo the Serre class.
    rw [k0_sub_eq_cokernel_sub_kernel]
    exact sub_mem_range_of_inclusion (P := P) hcoker hker
  -- Add the two Serre-subcategory contributions along the fraction.
  have hs' : K₀[Y] - K₀[φ.Y'] ∈ AddMonoidHom.range K₀ι := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_mem hs
  have hsum : (K₀[φ.Y'] - K₀[X]) + (K₀[Y] - K₀[φ.Y']) ∈ AddMonoidHom.range K₀ι :=
    AddSubgroup.add_mem _ hf hs'
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Lemma 12.11.3: the class of a binary biproduct is the sum of the two summand
classes in `K₀`. -/
lemma k0_biprod_eq_add (X Y : A) :
    K₀[X ⊞ Y] = K₀[X] + K₀[Y] := by
  let S : ShortComplex A :=
    ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (by simp)
  -- Use the split short exact sequence `0 → X → X ⊞ Y → Y → 0`.
  have hS : S.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact
  simpa [S] using (AbelianK0.of_shortExact S hS)

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
          simp [k0_zero_eq (A := A)]
      | of X =>
          -- A generator is `[X] - [0]`.
          refine ⟨X, 0, ?_⟩
          simp [k0_zero_eq (A := A)]
      | neg X _ =>
          -- The negative of a generator is `[0] - [X]`.
          refine ⟨0, X, ?_⟩
          simp [k0_zero_eq (A := A)]
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
                  rw [← k0_biprod_eq_add (A := A) X₁ X₂, ← k0_biprod_eq_add (A := A) Y₁ Y₂]

/-- Helper for Lemma 12.11.3: the composite `K₀(\mathcal C) → K₀(\mathcal A) → K₀(\mathcal A /
\mathcal C)` is zero. -/
lemma k0_quotient_comp_inclusion_eq_zero :
    AddMonoidHom.comp K₀Q K₀ι =
      (0 : AbelianK0 P.FullSubcategory →+ AbelianK0 P.isoModSerre.Localization) := by
  apply DFunLike.ext
  intro x
  rcases exists_object_sub_eq_of_k0 (A := P.FullSubcategory) x with ⟨X, Y, rfl⟩
  have hXzero : IsZero (P.isoModSerre.Q.obj X.1) := (isZero_obj_iff Q P X.1).2 X.2
  have hYzero : IsZero (P.isoModSerre.Q.obj Y.1) := (isZero_obj_iff Q P Y.1).2 Y.2
  have hXk0 : K₀[P.isoModSerre.Q.obj X.1] = 0 := by
    calc
      K₀[P.isoModSerre.Q.obj X.1] = K₀[(0 : P.isoModSerre.Localization)] := by
        exact k0_eq_of_iso (A := P.isoModSerre.Localization) hXzero.isoZero
      _ = 0 := k0_zero_eq (A := P.isoModSerre.Localization)
  have hYk0 : K₀[P.isoModSerre.Q.obj Y.1] = 0 := by
    calc
      K₀[P.isoModSerre.Q.obj Y.1] = K₀[(0 : P.isoModSerre.Localization)] := by
        exact k0_eq_of_iso (A := P.isoModSerre.Localization) hYzero.isoZero
      _ = 0 := k0_zero_eq (A := P.isoModSerre.Localization)
  rw [AddMonoidHom.comp_apply, map_sub, map_sub, AbelianK0.mapExactFunctor_apply_of,
    AbelianK0.mapExactFunctor_apply_of, AbelianK0.mapExactFunctor_apply_of,
    AbelianK0.mapExactFunctor_apply_of]
  change K₀[P.isoModSerre.Q.obj X.1] - K₀[P.isoModSerre.Q.obj Y.1] = 0
  rw [hXk0, hYk0]
  simp

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
  obtain ⟨g, ⟨e⟩⟩ := (Localization.essSurj_mapArrow Q P.isoModSerre).mem_essImage (Arrow.mk S.f)
  let e₁ : (P.isoModSerre.Q).obj g.left ≅ S.X₁ := Arrow.leftFunc.mapIso e
  let e₂ : (P.isoModSerre.Q).obj g.right ≅ S.X₂ := Arrow.rightFunc.mapIso e
  letI : Mono S.f := hS.mono_f
  have hkernel_mem : P (kernel g.hom) := by
    -- Transport the zero kernel of `S.f` back across the arrow isomorphism.
    have hkernel_zero :
        (kernel.ι S.f ≫ e₁.inv) ≫ (P.isoModSerre.Q).map g.hom = 0 := by
      calc
        (kernel.ι S.f ≫ e₁.inv) ≫ (P.isoModSerre.Q).map g.hom
            = kernel.ι S.f ≫ (e₁.inv ≫ (P.isoModSerre.Q).map g.hom) := by simp [Category.assoc]
        _ = kernel.ι S.f ≫ (S.f ≫ e₂.inv) := by
              rw [show e₁.inv ≫ (P.isoModSerre.Q).map g.hom = S.f ≫ e₂.inv by
                simpa [e₁, e₂] using Arrow.w e.inv]
        _ = 0 := by simp
    let transportFork : KernelFork ((P.isoModSerre.Q).map g.hom) :=
      KernelFork.ofι (kernel.ι S.f ≫ e₁.inv) hkernel_zero
    have htransport_kernel :
        IsLimit transportFork := by
      have htransport_arrow : e₁.inv ≫ (P.isoModSerre.Q).map g.hom = S.f ≫ e₂.inv := by
        simpa [e₁, e₂] using Arrow.w e.inv
      have htransport_fork :
          (Iso.refl _).hom ≫ transportFork.ι = kernel.ι S.f ≫ e₁.inv := by
        simp [transportFork]
      exact IsKernel.ofIso S.f (kernelIsKernel S.f) transportFork
        e₁.symm e₂.symm (Iso.refl _) htransport_arrow htransport_fork
    let eKernel' : kernel ((P.isoModSerre.Q).map g.hom) ≅ kernel S.f :=
      IsLimit.conePointUniqueUpToIso (kernelIsKernel ((P.isoModSerre.Q).map g.hom)) htransport_kernel
    have hzeroKernel : IsZero (kernel ((P.isoModSerre.Q).map g.hom)) := by
      have hzeroSource : IsZero (kernel S.f) := by
        exact IsZero.of_iso (isZero_zero _) (kernel.ofMono S.f)
      exact hzeroSource.of_iso eKernel'
    let eKernel : (P.isoModSerre.Q).obj (kernel g.hom) ≅ kernel ((P.isoModSerre.Q).map g.hom) :=
      CategoryTheory.Limits.PreservesKernel.iso Q g.hom
    exact (isZero_obj_iff Q P (kernel g.hom)).1 (hzeroKernel.of_iso eKernel)
  have hS_cokernel : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    -- Short exactness identifies `S.g` as a cokernel of `S.f`.
    exact ((S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hS.exact, hS.epi_g⟩).some
  let e₃' : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS_cokernel
  have htransport_zero : (P.isoModSerre.Q).map g.hom ≫ (e₂.hom ≫ cokernel.π S.f) = 0 := by
    -- The arrow-square relation transports the canonical cokernel cofork of `S.f`.
    calc
      (P.isoModSerre.Q).map g.hom ≫ (e₂.hom ≫ cokernel.π S.f)
          = (((P.isoModSerre.Q).map g.hom) ≫ e₂.hom) ≫ cokernel.π S.f := by simp [Category.assoc]
      _ = (e₁.hom ≫ S.f) ≫ cokernel.π S.f := by
            rw [show (P.isoModSerre.Q).map g.hom ≫ e₂.hom = e₁.hom ≫ S.f by
              simpa [e₁, e₂] using (Arrow.w e.hom).symm]
      _ = 0 := by simp [Category.assoc]
  let transportCofork : CokernelCofork ((P.isoModSerre.Q).map g.hom) :=
    CokernelCofork.ofπ (e₂.hom ≫ cokernel.π S.f) htransport_zero
  have htransport_arrow : e₁.inv ≫ (P.isoModSerre.Q).map g.hom = S.f ≫ e₂.inv := by
    simpa [e₁, e₂] using Arrow.w e.inv
  have htransport_cofork : e₂.inv ≫ transportCofork.π = cokernel.π S.f := by
    simp [transportCofork]
  have htransport_colim : IsColimit transportCofork := by
    -- Transport the cokernel structure of `S.f` back across the arrow isomorphism.
    have htransport_cofork' :
        e₂.inv ≫ transportCofork.π =
          (CokernelCofork.ofπ (cokernel.π S.f) (cokernel.condition S.f)).π ≫ (Iso.refl _).hom := by
      simpa using htransport_cofork
    exact IsCokernel.ofIso S.f (cokernelIsCokernel S.f) transportCofork
      e₁.symm e₂.symm (Iso.refl _) htransport_arrow htransport_cofork'
  let e₃'' : cokernel ((P.isoModSerre.Q).map g.hom) ≅ cokernel S.f :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel ((P.isoModSerre.Q).map g.hom))
      htransport_colim
  let e₃ : (P.isoModSerre.Q).obj (cokernel g.hom) ≅ S.X₃ :=
    CategoryTheory.Limits.PreservesCokernel.iso Q g.hom ≪≫ e₃'' ≪≫ e₃'
  have hπ₁ : π K₀[(P.isoModSerre.Q).objPreimage S.X₁] = π K₀[g.left] := by
    -- Chosen preimages and the lifted source object differ by a quotient isomorphism.
    have hmem :
        K₀[g.left] - K₀[(P.isoModSerre.Q).objPreimage S.X₁] ∈ AddMonoidHom.range K₀ι :=
      k0_sub_mem_range_of_quotient_iso (P := P)
        (((P.isoModSerre.Q).objObjPreimageIso S.X₁) ≪≫ e₁.symm)
    have hzeroπ :
        π (K₀[g.left] - K₀[(P.isoModSerre.Q).objPreimage S.X₁]) = 0 := by
      exact hπ_range hmem
    rw [map_sub] at hzeroπ
    exact (sub_eq_zero.mp hzeroπ).symm
  have hπ₂ : π K₀[(P.isoModSerre.Q).objPreimage S.X₂] = π K₀[g.right] := by
    -- The same comparison on the middle term uses the right branch of the arrow isomorphism.
    have hmem :
        K₀[g.right] - K₀[(P.isoModSerre.Q).objPreimage S.X₂] ∈ AddMonoidHom.range K₀ι :=
      k0_sub_mem_range_of_quotient_iso (P := P)
        (((P.isoModSerre.Q).objObjPreimageIso S.X₂) ≪≫ e₂.symm)
    have hzeroπ :
        π (K₀[g.right] - K₀[(P.isoModSerre.Q).objPreimage S.X₂]) = 0 := by
      exact hπ_range hmem
    rw [map_sub] at hzeroπ
    exact (sub_eq_zero.mp hzeroπ).symm
  have hπ₃ : π K₀[(P.isoModSerre.Q).objPreimage S.X₃] = π K₀[cokernel g.hom] := by
    -- The cokernel comparison supplies the third generator rewrite.
    have hmem :
        K₀[cokernel g.hom] - K₀[(P.isoModSerre.Q).objPreimage S.X₃] ∈
          AddMonoidHom.range K₀ι :=
      k0_sub_mem_range_of_quotient_iso (P := P)
        (((P.isoModSerre.Q).objObjPreimageIso S.X₃) ≪≫ e₃.symm)
    have hzeroπ :
        π (K₀[cokernel g.hom] - K₀[(P.isoModSerre.Q).objPreimage S.X₃]) = 0 := by
      exact hπ_range hmem
    rw [map_sub] at hzeroπ
    exact (sub_eq_zero.mp hzeroπ).symm
  have hπkernel : π K₀[kernel g.hom] = 0 := by
    -- The transported kernel lives in the Serre class, so its class dies in the quotient.
    have hmem : K₀[kernel g.hom] ∈ AddMonoidHom.range K₀ι := by
      refine ⟨K₀[⟨kernel g.hom, hkernel_mem⟩], ?_⟩
      rw [AbelianK0.mapExactFunctor_apply_of]
      rfl
    exact hπ_range hmem
  -- Rewrite the quotient generator to the source arrow model and then apply the standard `K₀`
  -- relation for a single morphism.
  calc
    preimageFG
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃)
        = π K₀[(P.isoModSerre.Q).objPreimage S.X₂] -
            π K₀[(P.isoModSerre.Q).objPreimage S.X₁] -
            π K₀[(P.isoModSerre.Q).objPreimage S.X₃] := by
              rw [map_sub, map_sub, hpreimageFG, hpreimageFG, hpreimageFG]
    _ = π K₀[g.right] - π K₀[g.left] - π K₀[cokernel g.hom] := by
          rw [hπ₂, hπ₁, hπ₃]
    _ = π (K₀[g.right] - K₀[g.left] - K₀[cokernel g.hom]) := by
          rw [map_sub, map_sub]
    _ = π (K₀[cokernel g.hom] - K₀[kernel g.hom] - K₀[cokernel g.hom]) := by
          rw [k0_sub_eq_cokernel_sub_kernel]
    _ = -π K₀[kernel g.hom] := by
          rw [map_sub, map_sub]
          abel
    _ = 0 := by
          rw [hπkernel, neg_zero]

-- Proof sketch: combine the exactness of the inclusion and quotient functors with the universal
-- property of `K₀` from `AbelianK0.mapExactFunctor`; exactness at `K₀(A)` comes from the quotient-kernel
-- description of the Serre localization, and surjectivity follows from essential surjectivity of
-- `toSerreQuotient_essSurj P`.
/-- Lemma 12.11.3 (1): the inclusion `\mathcal C \to \mathcal A` and the quotient functor
`\mathcal A \to \mathcal A / \mathcal C` induce an exact sequence
`K₀(\mathcal C) → K₀(\mathcal A) → K₀(\mathcal A / \mathcal C) → 0`. -/
theorem serreClassK0_exactSequence :
    Function.Exact K₀ι K₀Q ∧ Function.Surjective K₀Q := by
  constructor
  · -- Route correction: descend the raw preimage map through `AbelianK0.lift`, then compare it to
    -- the quotient map `π` on generators of `K₀(A)`.
    let π : AbelianK0 A →+ AbelianK0 A ⧸ AddMonoidHom.range K₀ι :=
      QuotientAddGroup.mk' (AddMonoidHom.range K₀ι)
    let preimageFG : FreeAbelianGroup P.isoModSerre.Localization →+
        (AbelianK0 A ⧸ AddMonoidHom.range K₀ι) :=
      FreeAbelianGroup.lift (fun X : P.isoModSerre.Localization ↦ π K₀[(P.isoModSerre.Q).objPreimage X])
    have hrelations :
        AbelianK0.relations P.isoModSerre.Localization ≤ preimageFG.ker := by
      -- The only relations are the short-exact generators, handled by the lifted-arrow calculation.
      rw [AbelianK0.relations, AddSubgroup.closure_le]
      rintro _ ⟨S, rfl⟩
      rcases S with ⟨S, hS⟩
      exact preimage_generator_zero_mod_serre_range (P := P) π
        (by
          intro z hz
          simpa [π] using (QuotientAddGroup.eq_zero_iff z).2 hz)
        preimageFG
        (by
          intro X
          rfl)
        S hS
    let δ : AbelianK0 P.isoModSerre.Localization →+
        (AbelianK0 A ⧸ AddMonoidHom.range K₀ι) :=
      AbelianK0.lift (fun X : P.isoModSerre.Localization ↦ π K₀[(P.isoModSerre.Q).objPreimage X])
        hrelations
    have hδ_of (X : P.isoModSerre.Localization) :
        δ K₀[X] = π K₀[(P.isoModSerre.Q).objPreimage X] := by
      -- Evaluate the descended map on the class of a single quotient object.
      simpa [δ] using
        (AbelianK0.lift_of
          (fun X : P.isoModSerre.Localization ↦ π K₀[(P.isoModSerre.Q).objPreimage X])
          hrelations X)
    have hδ_comp_of (X : A) : δ (K₀Q K₀[X]) = π K₀[X] := by
      -- The chosen preimage of `Q.obj X` is only quotient-isomorphic to `X`, so compare modulo
      -- `range K₀ι`.
      rw [AbelianK0.mapExactFunctor_apply_of, hδ_of]
      have hmem :
          K₀[X] - K₀[(P.isoModSerre.Q).objPreimage ((P.isoModSerre.Q).obj X)] ∈
            AddMonoidHom.range K₀ι :=
        k0_sub_mem_range_of_quotient_iso (P := P)
          ((P.isoModSerre.Q).objObjPreimageIso ((P.isoModSerre.Q).obj X))
      have hzero :
          π (K₀[X] - K₀[(P.isoModSerre.Q).objPreimage ((P.isoModSerre.Q).obj X)]) = 0 := by
        exact (QuotientAddGroup.eq_zero_iff
          (K₀[X] - K₀[(P.isoModSerre.Q).objPreimage ((P.isoModSerre.Q).obj X)])).2 hmem
      rw [map_sub] at hzero
      exact (sub_eq_zero.mp hzero).symm
    have hδ_comp (x : AbelianK0 A) : δ (K₀Q x) = π x := by
      -- Reduce a general `K₀` class to a difference of two object classes.
      rcases exists_object_sub_eq_of_k0 (A := A) x with ⟨X, Y, rfl⟩
      calc
        δ (K₀Q (K₀[X] - K₀[Y])) = δ (K₀Q K₀[X]) - δ (K₀Q K₀[Y]) := by
          rw [map_sub, map_sub]
        _ = π K₀[X] - π K₀[Y] := by
          rw [hδ_comp_of, hδ_comp_of]
        _ = π (K₀[X] - K₀[Y]) := by
          rw [map_sub]
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext x
      simpa [Function.comp, AddMonoidHom.comp_apply] using
        DFunLike.congr_fun (k0_quotient_comp_inclusion_eq_zero (P := P)) x
    · intro x hx
      have hπzero : π x = 0 := by
        calc
          π x = δ (K₀Q x) := by symm; exact hδ_comp x
          _ = 0 := by rw [hx, map_zero]
      have hxmem : x ∈ AddMonoidHom.range K₀ι := by
        change QuotientAddGroup.mk' (AddMonoidHom.range K₀ι) x = 0 at hπzero
        exact (QuotientAddGroup.eq_zero_iff x).1 hπzero
      rcases hxmem with ⟨y, hy⟩
      exact ⟨y, hy⟩
  · letI : Functor.EssSurj (P.isoModSerre.Q) :=
        Localization.essSurj (P.isoModSerre.Q) P.isoModSerre
    intro x
    rcases exists_object_sub_eq_of_k0 (A := P.isoModSerre.Localization) x with ⟨X, Y, hxy⟩
    refine
      ⟨K₀[(P.isoModSerre.Q).objPreimage X] - K₀[(P.isoModSerre.Q).objPreimage Y], ?_⟩
    -- Lift representatives of the quotient classes and transport along the canonical preimage isos.
    calc
      K₀Q (K₀[(P.isoModSerre.Q).objPreimage X] - K₀[(P.isoModSerre.Q).objPreimage Y])
          =
            K₀[(ExactFunctor.of (P.isoModSerre.Q)).obj.obj ((P.isoModSerre.Q).objPreimage X)] -
              K₀[(ExactFunctor.of (P.isoModSerre.Q)).obj.obj ((P.isoModSerre.Q).objPreimage Y)] := by
                rw [map_sub, AbelianK0.mapExactFunctor_apply_of,
                  AbelianK0.mapExactFunctor_apply_of]
      _ =
            K₀[(P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage X)] -
              K₀[(P.isoModSerre.Q).obj ((P.isoModSerre.Q).objPreimage Y)] := by
                rfl
      _ = K₀[X] - K₀[Y] := by
            rw [k0_eq_of_iso (A := P.isoModSerre.Localization)
                  ((P.isoModSerre.Q).objObjPreimageIso X),
              k0_eq_of_iso (A := P.isoModSerre.Localization)
                ((P.isoModSerre.Q).objObjPreimageIso Y)]
      _ = x := hxy.symm

-- Proof sketch: this is the owner `mapHomologyIso` specialized to the Serre quotient functor `Q`;
-- naming it keeps the later quotient-acyclicity proof on the source route instead of repeating the
-- transport calculation inline.
/-- Helper for Lemma 12.11.3: passing a complex to the Serre quotient commutes with taking
homology at a fixed degree. -/
abbrev quotient_homology_iso
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex A c) (i : ι) :
    ((((Q).mapHomologicalComplex c).obj K).homology i) ≅ P.isoModSerre.Q.obj (K.homology i) :=
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
  have hzero_obj : IsZero (P.isoModSerre.Q.obj (K.homology i)) := by
    -- Compare the homology of the mapped complex with the image of the original homology object.
    exact hzero_mapped.of_iso (quotient_homology_iso P c K i).symm
  exact (isZero_obj_iff P.isoModSerre.Q P (K.homology i)).1 hzero_obj

/-- Helper for Lemma 12.11.3: composing a kernel map with the canonical lift into `kernel f`
realizes `kernel g` as a kernel of `kernel.lift f g h`, so the two kernels have the same `K₀`
class. -/
lemma k0_kernel_of_kernel_lift
    {X Y Z : A} (f : Y ⟶ Z) (g : X ⟶ Y) (h : g ≫ f = 0) :
    K₀[kernel (kernel.lift f g h)] = K₀[kernel g] := by
  -- The old route tried to unfold both kernels directly; instead, transfer the source kernel
  -- across the mono `kernel.ι f` and then compare the kernel objects by uniqueness.
  have hcomp : kernel.ι g ≫ kernel.lift f g h = 0 := by
    refine (cancel_mono (kernel.ι f)).1 ?_
    simp [Category.assoc, kernel.lift_ι, kernel.condition]
  let hKernel :
      IsLimit
        (KernelFork.ofι (kernel.ι g) hcomp) :=
    isKernelOfComp (f := kernel.lift f g h) (g := kernel.ι f) (h := g)
      (kernelIsKernel g)
      hcomp
      (by simpa using (kernel.lift_ι f g h))
  let e : kernel g ≅ kernel (kernel.lift f g h) :=
    IsLimit.conePointUniqueUpToIso hKernel (limit.isLimit _)
  exact k0_eq_of_iso (A := A) e.symm

/-- Helper for Lemma 12.11.3: the two homology objects of the canonical cyclic cochain complex
have the same image in `K₀(A)`. -/
lemma cyclic_homology_classes_cancel
    {M : A} (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0) :
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    K₀[K.homology 0] - K₀[K.homology 1] = 0 := by
  let K := cyclicCochainComplex φ ψ hφψ hψφ
  change K₀[K.homology 0] - K₀[K.homology 1] = 0
  have hprev0 : (up (ZMod 2)).prev 0 = 1 :=
    ComplexShape.prev_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  have hnext0 : (up (ZMod 2)).next 0 = 1 :=
    ComplexShape.next_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  have hprev1 : (up (ZMod 2)).prev 1 = 0 :=
    ComplexShape.prev_eq' _ (by decide : (0 : ZMod 2) + 1 = 1)
  have hnext1 : (up (ZMod 2)).next 1 = 0 :=
    ComplexShape.next_eq' _ (by decide : (1 : ZMod 2) + 1 = 0)
  let v₀ := kernel.lift (K.sc' 1 0 1).g (K.sc' 1 0 1).f (K.sc' 1 0 1).zero
  let v₁ := kernel.lift (K.sc' 0 1 0).g (K.sc' 0 1 0).f (K.sc' 0 1 0).zero
  have hIso0 : K.homology 0 ≅ cokernel v₀ := by
    -- Degree `0` homology is the quotient `ker φ / im ψ`, presented as a cokernel.
    refine K.homologyIsoSc' 1 0 1 hprev0 hnext0 ≪≫ ?_
    exact (K.sc' 1 0 1).homologyIsoCokernelLift
  have hIso1 : K.homology 1 ≅ cokernel v₁ := by
    -- Degree `1` homology is the quotient `ker ψ / im φ`, presented as a cokernel.
    refine K.homologyIsoSc' 0 1 0 hprev1 hnext1 ≪≫ ?_
    exact (K.sc' 0 1 0).homologyIsoCokernelLift
  have hH0 : K₀[K.homology 0] = K₀[cokernel v₀] :=
    k0_eq_of_iso (A := A) hIso0
  have hH1 : K₀[K.homology 1] = K₀[cokernel v₁] :=
    k0_eq_of_iso (A := A) hIso1
  have hku0 : K₀[kernel v₀] = K₀[kernel ψ] :=
    by
      simpa [K, v₀] using
        (k0_kernel_of_kernel_lift (A := A) (K.sc' 1 0 1).g (K.sc' 1 0 1).f
          (K.sc' 1 0 1).zero)
  have hku1 : K₀[kernel v₁] = K₀[kernel φ] :=
    by
      simpa [K, v₁] using
        (k0_kernel_of_kernel_lift (A := A) (K.sc' 0 1 0).g (K.sc' 0 1 0).f
          (K.sc' 0 1 0).zero)
  have hu0 : K₀[kernel φ] - K₀[M] = K₀[cokernel v₀] - K₀[kernel ψ] := by
    -- Rewrite the kernel term of `v₀` back to `kernel ψ`.
    have hk0 := k0_sub_eq_cokernel_sub_kernel (A := A) (f := v₀)
    rw [hku0] at hk0
    simpa [K, v₀] using hk0
  have hu1 : K₀[kernel ψ] - K₀[M] = K₀[cokernel v₁] - K₀[kernel φ] := by
    -- Rewrite the kernel term of `v₁` back to `kernel φ`.
    have hk1 := k0_sub_eq_cokernel_sub_kernel (A := A) (f := v₁)
    rw [hku1] at hk1
    simpa [K, v₁] using hk1
  have hc0 : K₀[cokernel v₀] = K₀[kernel φ] - K₀[M] + K₀[kernel ψ] := by
    calc
      K₀[cokernel v₀] = (K₀[cokernel v₀] - K₀[kernel ψ]) + K₀[kernel ψ] := by
        abel
      _ = (K₀[kernel φ] - K₀[M]) + K₀[kernel ψ] := by
        rw [← hu0]
      _ = K₀[kernel φ] - K₀[M] + K₀[kernel ψ] := by
        abel
  have hc1 : K₀[cokernel v₁] = K₀[kernel ψ] - K₀[M] + K₀[kernel φ] := by
    calc
      K₀[cokernel v₁] = (K₀[cokernel v₁] - K₀[kernel φ]) + K₀[kernel φ] := by
        abel
      _ = (K₀[kernel ψ] - K₀[M]) + K₀[kernel φ] := by
        rw [← hu1]
      _ = K₀[kernel ψ] - K₀[M] + K₀[kernel φ] := by
        abel
  -- The two cokernel presentations differ only by commuting the two kernel summands.
  calc
    K₀[K.homology 0] - K₀[K.homology 1]
        = K₀[cokernel v₀] - K₀[cokernel v₁] := by rw [hH0, hH1]
    _ = (K₀[kernel φ] - K₀[M] + K₀[kernel ψ]) -
          (K₀[kernel ψ] - K₀[M] + K₀[kernel φ]) := by rw [hc0, hc1]
    _ = 0 := by
          abel

/-- Helper for Lemma 12.11.3: the formal sum of a list of objects in the free abelian group. -/
abbrev fg_list (l : List A) : FreeAbelianGroup A :=
  List.sum (l.map FreeAbelianGroup.of)

/-- Helper for Lemma 12.11.3: the formal sum attached to an appended list is additive. -/
lemma fg_list_append (l₁ l₂ : List A) :
    fg_list (A := A) (l₁ ++ l₂) = fg_list (A := A) l₁ + fg_list (A := A) l₂ := by
  -- Expand the appended list and collect the two partial sums.
  simp [fg_list, List.map_append, List.sum_append]

/-- Helper for Lemma 12.11.3: the coefficient of an object in `fg_list l` is its multiplicity in
`l`. -/
lemma coeff_fg_list [DecidableEq A] (X : A) (l : List A) :
    FreeAbelianGroup.coeff X (fg_list (A := A) l) = l.count X := by
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

/-- Helper for Lemma 12.11.3: equality of two positive formal sums gives a permutation of the
underlying lists. -/
lemma list_perm_of_fg_list_eq [DecidableEq A] {l₁ l₂ : List A}
    (h : fg_list (A := A) l₁ = fg_list (A := A) l₂) :
    l₁.Perm l₂ := by
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
    fg_list (A := A) (signed_plus_terms (A := A) (positive₁ ++ positive₂) (negative₁ ++ negative₂)) =
      fg_list (A := A) (signed_plus_terms (A := A) positive₁ negative₁) +
        fg_list (A := A) (signed_plus_terms (A := A) positive₂ negative₂) := by
  -- The two positive-endpoint blocks and two negative-middle blocks contribute additively.
  simp [fg_list, signed_plus_terms, List.flatMap_append, List.map_append, List.sum_append]
  abel

/-- Helper for Lemma 12.11.3: concatenating two signed short exact blocks adds the formal sum of
their `T⁻` tails. -/
lemma fg_list_signed_minus_terms_append
    (positive₁ positive₂ negative₁ negative₂ : List { T : ShortComplex A // T.ShortExact }) :
    fg_list (A := A) (signed_minus_terms (A := A) (positive₁ ++ positive₂) (negative₁ ++ negative₂)) =
      fg_list (A := A) (signed_minus_terms (A := A) positive₁ negative₁) +
        fg_list (A := A) (signed_minus_terms (A := A) positive₂ negative₂) := by
  -- The same additive decomposition holds for the negative tail.
  simp [fg_list, signed_minus_terms, List.flatMap_append, List.map_append, List.sum_append]
  abel

/-- Helper for Lemma 12.11.3: the closure-induction bookkeeping package for a formal relation in
the free abelian group. -/
structure SignedShortExactAccumulator (r : FreeAbelianGroup A) where
  positiveSeqs : List { T : ShortComplex A // T.ShortExact }
  negativeSeqs : List { T : ShortComplex A // T.ShortExact }
  difference_eq :
    fg_list (A := A) (signed_minus_terms (A := A) positiveSeqs negativeSeqs) -
      fg_list (A := A) (signed_plus_terms (A := A) positiveSeqs negativeSeqs) = r

/-- Helper for Lemma 12.11.3: the empty signed short exact accumulator represents the zero
relation. -/
lemma empty_signed_short_exact_accumulator_difference :
    fg_list (A := A) (signed_minus_terms (A := A) [] []) -
      fg_list (A := A) (signed_plus_terms (A := A) [] []) = 0 := by
  -- With no short exact sequences, both source-proof tails are empty.
  simp [fg_list, signed_plus_terms, signed_minus_terms]

/-- Helper for Lemma 12.11.3: the zero relation has the empty signed short exact accumulator. -/
abbrev empty_signed_short_exact_accumulator :
    SignedShortExactAccumulator (A := A) 0 :=
  { positiveSeqs := []
    negativeSeqs := []
    difference_eq := empty_signed_short_exact_accumulator_difference (A := A) }

/-- Helper for Lemma 12.11.3: a single positive short exact sequence realizes its Grothendieck
relation in the accumulator formalism. -/
lemma singleton_positive_signed_short_exact_accumulator_difference
    (S : { T : ShortComplex A // T.ShortExact }) :
    fg_list (A := A) (signed_minus_terms (A := A) [S] []) -
      fg_list (A := A) (signed_plus_terms (A := A) [S] []) =
        short_exact_relation (A := A) S := by
  -- The positive generator contributes `X₂ - X₁ - X₃`.
  simp [fg_list, short_exact_relation, signed_plus_terms, signed_minus_terms]
  abel

/-- Helper for Lemma 12.11.3: a single positive short exact sequence realizes its Grothendieck
relation in the accumulator formalism. -/
abbrev singleton_positive_signed_short_exact_accumulator
    (S : { T : ShortComplex A // T.ShortExact }) :
    SignedShortExactAccumulator (A := A) (short_exact_relation (A := A) S) :=
  { positiveSeqs := [S]
    negativeSeqs := []
    difference_eq := singleton_positive_signed_short_exact_accumulator_difference (A := A) S }

/-- Helper for Lemma 12.11.3: swapping positive and negative data negates the represented
relation. -/
lemma swap_signed_short_exact_accumulator_difference
    {r : FreeAbelianGroup A} (w : SignedShortExactAccumulator (A := A) r) :
    fg_list (A := A) (signed_minus_terms (A := A) w.negativeSeqs w.positiveSeqs) -
      fg_list (A := A) (signed_plus_terms (A := A) w.negativeSeqs w.positiveSeqs) = -r := by
  -- Swapping the two source-proof sides reverses the formal difference.
  calc
    fg_list (A := A) (signed_minus_terms (A := A) w.negativeSeqs w.positiveSeqs) -
        fg_list (A := A) (signed_plus_terms (A := A) w.negativeSeqs w.positiveSeqs)
        =
          fg_list (A := A) (signed_plus_terms (A := A) w.positiveSeqs w.negativeSeqs) -
            fg_list (A := A) (signed_minus_terms (A := A) w.positiveSeqs w.negativeSeqs) := by
              simp [signed_plus_terms, signed_minus_terms]
    _ = -(fg_list (A := A) (signed_minus_terms (A := A) w.positiveSeqs w.negativeSeqs) -
            fg_list (A := A) (signed_plus_terms (A := A) w.positiveSeqs w.negativeSeqs)) := by
              abel
    _ = -r := by rw [w.difference_eq]

/-- Helper for Lemma 12.11.3: swapping positive and negative data negates the represented
relation. -/
abbrev swap_signed_short_exact_accumulator
    {r : FreeAbelianGroup A} (w : SignedShortExactAccumulator (A := A) r) :
    SignedShortExactAccumulator (A := A) (-r) :=
  { positiveSeqs := w.negativeSeqs
    negativeSeqs := w.positiveSeqs
    difference_eq := swap_signed_short_exact_accumulator_difference (A := A) w }

/-- Helper for Lemma 12.11.3: concatenating two accumulators adds their represented relations. -/
lemma append_signed_short_exact_accumulator_difference
    {r₁ r₂ : FreeAbelianGroup A}
    (w₁ : SignedShortExactAccumulator (A := A) r₁)
    (w₂ : SignedShortExactAccumulator (A := A) r₂) :
    fg_list (A := A)
        (signed_minus_terms (A := A)
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) -
      fg_list (A := A)
        (signed_plus_terms (A := A)
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) = r₁ + r₂ := by
  -- Concatenate the two source-proof blocks and then collect the two represented relations.
  calc
    fg_list (A := A)
        (signed_minus_terms (A := A)
          (w₁.positiveSeqs ++ w₂.positiveSeqs)
          (w₁.negativeSeqs ++ w₂.negativeSeqs)) -
        fg_list (A := A)
          (signed_plus_terms (A := A)
            (w₁.positiveSeqs ++ w₂.positiveSeqs)
            (w₁.negativeSeqs ++ w₂.negativeSeqs))
        =
          (fg_list (A := A) (signed_minus_terms (A := A) w₁.positiveSeqs w₁.negativeSeqs) +
              fg_list (A := A) (signed_minus_terms (A := A) w₂.positiveSeqs w₂.negativeSeqs)) -
            (fg_list (A := A) (signed_plus_terms (A := A) w₁.positiveSeqs w₁.negativeSeqs) +
              fg_list (A := A) (signed_plus_terms (A := A) w₂.positiveSeqs w₂.negativeSeqs)) := by
                rw [fg_list_signed_minus_terms_append, fg_list_signed_plus_terms_append]
    _ =
          (fg_list (A := A) (signed_minus_terms (A := A) w₁.positiveSeqs w₁.negativeSeqs) -
              fg_list (A := A) (signed_plus_terms (A := A) w₁.positiveSeqs w₁.negativeSeqs)) +
            (fg_list (A := A) (signed_minus_terms (A := A) w₂.positiveSeqs w₂.negativeSeqs) -
              fg_list (A := A) (signed_plus_terms (A := A) w₂.positiveSeqs w₂.negativeSeqs)) := by
                abel
    _ = r₁ + r₂ := by rw [w₁.difference_eq, w₂.difference_eq]

/-- Helper for Lemma 12.11.3: concatenating two accumulators adds their represented relations. -/
abbrev append_signed_short_exact_accumulator
    {r₁ r₂ : FreeAbelianGroup A}
    (w₁ : SignedShortExactAccumulator (A := A) r₁)
    (w₂ : SignedShortExactAccumulator (A := A) r₂) :
    SignedShortExactAccumulator (A := A) (r₁ + r₂) :=
  { positiveSeqs := w₁.positiveSeqs ++ w₂.positiveSeqs
    negativeSeqs := w₁.negativeSeqs ++ w₂.negativeSeqs
    difference_eq := append_signed_short_exact_accumulator_difference (A := A) w₁ w₂ }

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
    Nonempty (SignedShortExactAccumulator (A := A) r) := by
  -- Route correction: closure induction only needs the weak accumulator invariant, not the final
  -- balance isomorphism between the two ordered sums.
  rw [AbelianK0.relations] at hr
  induction hr using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨S, rfl⟩
      exact ⟨singleton_positive_signed_short_exact_accumulator (A := A) S⟩
  | zero =>
      exact ⟨empty_signed_short_exact_accumulator (A := A)⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨wx⟩
      rcases ihy with ⟨wy⟩
      exact ⟨append_signed_short_exact_accumulator (A := A) wx wy⟩
  | neg x hx ihx =>
      rcases ihx with ⟨wx⟩
      exact ⟨swap_signed_short_exact_accumulator (A := A) wx⟩

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
  balance_eq : fg_list (A := A) plus_terms = fg_list (A := A) minus_terms

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
  exact k0_eq_of_iso (A := A) (Classical.choice (ordered_biprod_iso_of_perm (A := A) h))

/-- Helper for Lemma 12.11.3: balanced positive formal sums give canonically isomorphic ordered
biproducts. -/
theorem ordered_biprod_iso_of_balance {l₁ l₂ : List A}
    (h : fg_list (A := A) l₁ = fg_list (A := A) l₂) :
    Nonempty (ordered_biprod l₁ ≅ ordered_biprod l₂) := by
  classical
  -- First recover the underlying list permutation from the equality in the free abelian group.
  exact ordered_biprod_iso_of_perm (A := A) (list_perm_of_fg_list_eq (A := A) h)

/-- Helper for Lemma 12.11.3: a kernel class `x = [P₀] - [Q₀]` admits the source proof's ordered
signed short-exact presentation. -/
theorem exists_signed_short_exact_presentation_of_mem_ker_inclusion
    {x : AbelianK0 P.FullSubcategory} {P₀ Q₀ : P.FullSubcategory}
    (hx : x = K₀[P₀] - K₀[Q₀]) (hker : x ∈ (K₀ι).ker) :
    Nonempty (SignedShortExactPresentation (P := P) P₀ Q₀) := by
  -- Rewrite the kernel condition as a relation witness and package the resulting accumulator into
  -- the source proof's final balanced `T⁺/T⁻` lists.
  have hrelation :
      FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1 ∈ AbelianK0.relations A :=
    relation_of_mem_ker_inclusion (A := A) (P := P) hx hker
  rcases exists_signed_short_exact_accumulator_of_relation (A := A) hrelation with ⟨w⟩
  let plus_terms : List A :=
    P₀.1 :: signed_plus_terms (A := A) w.positiveSeqs w.negativeSeqs
  let minus_terms : List A :=
    Q₀.1 :: signed_minus_terms (A := A) w.positiveSeqs w.negativeSeqs
  have hplus_eq :
      plus_terms =
        P₀.1 ::
          (w.positiveSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
            (w.negativeSeqs.map fun S ↦ S.1.X₂) := by
    -- The positive presentation list is just the chosen accumulator tail with the distinguished
    -- head `P₀`.
    rfl
  have hminus_eq :
      minus_terms =
        Q₀.1 ::
          (w.negativeSeqs.flatMap fun S ↦ [S.1.X₁, S.1.X₃]) ++
            (w.positiveSeqs.map fun S ↦ S.1.X₂) := by
    -- The negative presentation list is the corresponding accumulator tail with head `Q₀`.
    rfl
  have hbalance : fg_list (A := A) plus_terms = fg_list (A := A) minus_terms := by
    -- The accumulator equality is exactly the balance relation after reattaching the heads.
    have hzero :
        fg_list (A := A) plus_terms - fg_list (A := A) minus_terms = 0 := by
      calc
        fg_list (A := A) plus_terms - fg_list (A := A) minus_terms
            =
              (FreeAbelianGroup.of P₀.1 - FreeAbelianGroup.of Q₀.1) -
                (fg_list (A := A) (signed_minus_terms (A := A) w.positiveSeqs w.negativeSeqs) -
                  fg_list (A := A) (signed_plus_terms (A := A) w.positiveSeqs w.negativeSeqs)) := by
                    simp [plus_terms, minus_terms, fg_list]
                    abel
        _ = 0 := by
              rw [w.difference_eq]
              abel
    exact sub_eq_zero.mp hzero
  exact
    ⟨{ positiveSeqs := w.positiveSeqs
       negativeSeqs := w.negativeSeqs
       plus_terms := plus_terms
       minus_terms := minus_terms
       plus_eq := hplus_eq
       minus_eq := hminus_eq
       balance_eq := hbalance }⟩

/-- Helper for Lemma 12.11.3: the ordered signed short-exact presentation produces the cyclic
cochain complex from the source proof, with quotient-acyclic image and homology objects `P₀` and
`Q₀`. -/
lemma cyclic_witness_of_signed_short_exact_presentation
    {P₀ Q₀ : P.FullSubcategory} (w : SignedShortExactPresentation (P := P) P₀ Q₀) :
    ∃ (M : A) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0),
      let K := cyclicCochainComplex φ ψ hφψ hψφ
      ∃ hExactQ : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic,
        ∃ e₀ : K.homology 0 ≅ P₀.1, ∃ e₁ : K.homology 1 ≅ Q₀.1, True := by
  -- TODO: use `ordered_biprod_iso_of_balance w.balance_eq` to identify the two ordered biproducts,
  -- then transport the recursive source-proof differentials across that iso and read off the two
  -- homology objects as the distinguished heads `P₀` and `Q₀`.
  sorry

-- Proof sketch: a kernel element is represented by a formal difference of objects of the Serre
-- subcategory that becomes trivial in `K₀(A)`; organize the corresponding data as the canonical
-- `ZMod 2`-indexed cyclic cochain complex from `12.11.2.1`, require that its image in the Serre
-- quotient be exact, and read off the degree-`0` and degree-`1` homology objects in `P`.
-- Conversely, the usual Euler-characteristic computation for this cyclic complex shows that the
-- displayed difference maps to zero in `K₀(A)`.

/-- Lemma 12.11.3 (2): an element of the kernel of `K₀(\mathcal C) → K₀(\mathcal A)` is exactly a
difference `[H⁰(K)] - [H¹(K)]` coming from the canonical `ZMod 2`-indexed cyclic cochain complex
in `\mathcal A` built from the constant object `M` and alternating differentials
`\varphi, \psi`, whose image in the Serre quotient is exact and whose degree-`0` and degree-`1`
homology objects lie in the Serre subcategory `\mathcal C`. -/
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
  · -- Route correction: stabilize the source proof first as an ordered signed short-exact
    -- presentation, then consume that package to build the cyclic witness and identify its two
    -- homology objects with the chosen representatives of `x`.
    intro hker
    classical
    rcases exists_object_sub_eq_of_k0 (A := P.FullSubcategory) x with ⟨P₀, Q₀, hx⟩
    rcases exists_signed_short_exact_presentation_of_mem_ker_inclusion (P := P) hx hker with ⟨w⟩
    rcases cyclic_witness_of_signed_short_exact_presentation (P := P) w with
      ⟨M, φ, ψ, hφψ, hψφ, hcyclic⟩
    dsimp at hcyclic
    rcases hcyclic with ⟨hExactQ, e₀, e₁, -⟩
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    have hExactQ' : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic := by
      -- Rename the witness so the remaining argument can use the canonical `K`.
      simpa [K] using hExactQ
    have e₀' : K.homology 0 ≅ P₀.1 := by
      -- The closing helper returns the source proof's degree-`0` homology identification.
      simpa [K] using e₀
    have e₁' : K.homology 1 ≅ Q₀.1 := by
      -- The closing helper returns the source proof's degree-`1` homology identification.
      simpa [K] using e₁
    have hmem₀ : P (K.homology 0) :=
      homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ' 0
    have hmem₁ : P (K.homology 1) :=
      homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ' 1
    have hIso₀ : ⟨K.homology 0, hmem₀⟩ ≅ P₀ := by
      -- Lift the ambient homology identification into the full subcategory `P`.
      exact P.isoMk e₀'
    have hIso₁ : ⟨K.homology 1, hmem₁⟩ ≅ Q₀ := by
      -- The same transport works for the degree-`1` homology object.
      exact P.isoMk e₁'
    have hx' :
        x =
          K₀[⟨K.homology 0, hmem₀⟩] - K₀[⟨K.homology 1, hmem₁⟩] := by
      -- Replace the chosen representatives of `x` by the two homology objects identified above.
      calc
        x = K₀[P₀] - K₀[Q₀] := hx
        _ = K₀[⟨K.homology 0, hmem₀⟩] - K₀[⟨K.homology 1, hmem₁⟩] := by
              rw [← k0_eq_of_iso (A := P.FullSubcategory) hIso₀,
                ← k0_eq_of_iso (A := P.FullSubcategory) hIso₁]
    refine ⟨M, φ, ψ, hφψ, hψφ, ?_⟩
    -- Package the cyclic witness back into the theorem's exact statement.
    dsimp
    refine ⟨hExactQ', ?_⟩
    simpa [K] using hx'
  · rintro ⟨M, φ, ψ, hφψ, hψφ, hExactQ, rfl⟩
    let K := cyclicCochainComplex φ ψ hφψ hψφ
    -- Forget the Serre witnesses and compute in the ambient `K₀(A)` using Euler characteristic.
    rw [AddMonoidHom.mem_ker, map_sub, AbelianK0.mapExactFunctor_apply_of,
      AbelianK0.mapExactFunctor_apply_of]
    simpa [K] using
      (cyclic_homology_classes_cancel (A := A) (φ := φ) (ψ := ψ) hφψ hψφ)

end

end

end _root_.CategoryTheory.ObjectProperty
