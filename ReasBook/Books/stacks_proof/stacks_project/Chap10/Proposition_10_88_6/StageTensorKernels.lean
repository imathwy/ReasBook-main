import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Definition_10_88_2
import StacksProject_2024.Chap10.Lemma_10_11_1
import StacksProject_2024.Chap10.Lemma_10_11_4
import StacksProject_2024.Chap10.Lemma_10_79_4
import StacksProject_2024.Chap10.Lemma_10_82_14
import StacksProject_2024.Chap10.Lemma_10_88_3
import StacksProject_2024.Chap10.Lemma_10_88_5
import StacksProject_2024.Chap10.Proposition_10_88_6.ModuleCatFactorization

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: pushing a chosen stage factorization forward to a later stage
gives the corresponding explicit factorization on underlying linear maps. -/
lemma pushed_forward_stage_factorization_hom
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    ∃ h : F.obj j →ₗ[R] M, f = h.comp (g₀ ≫ F.map (homOfLE hij)).hom := by
  refine ⟨(colimit.ι F j ≫ c.hom).hom, ?_⟩
  have hpush :
      g₀ ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom) = ModuleCat.ofHom f :=
    push_forward_stage_factorization (R := R) (F := F) (c := c) (g := g₀) (f := f) hg₀ hij
  -- Proof comment: forgetting the pushed-forward categorical factorization gives the explicit
  -- equality of underlying linear maps needed in clause `(2) → (1)`.
  ext x
  have hpush_apply :=
    congrArg (fun t : P ⟶ ModuleCat.of R M ↦ t.hom x) hpush
  simpa [Category.assoc] using hpush_apply.symm

/-- Helper for Proposition 10.88.6: the pushed-forward stage factorization can be read directly on
the frozen carrier linear maps used by the domination lemmas. -/
lemma pushed_forward_stage_factorization_hom_typed
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {P : ModuleCat.{max v w} R}
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    ∃ h : ((F.obj j : Type (max v w)) →ₗ[R] M),
      (f : (P : Type (max v w)) →ₗ[R] M) =
        h.comp
          ((((g₀ ≫ F.map (homOfLE hij)).hom) :
            (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)))) := by
  -- Proof comment: this is the same pushed-forward factorization, with the carrier types spelled
  -- out explicitly so later domination arguments do not depend on coercion search.
  simpa using
    pushed_forward_stage_factorization_hom
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀

/-- Helper for Proposition 10.88.6: the colimit object of `F` is equal to the bundled module on
its underlying carrier. -/
lemma colimit_eq_moduleCat_of_carrier
    (F : I ⥤ ModuleCat.{max v w} R) :
    colimit F =
      ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w)) := by
  -- Proof comment: `ModuleCat.of` is reducible on an already bundled module carrier.
  rfl

/-- Helper for Proposition 10.88.6: package the lifted-index cocone as a colimit presentation in
the common universe of the module stages. -/
noncomputable def lifted_index_colimitPresentation
    (F : I ⥤ ModuleCat.{max v w} R) :
    ColimitPresentation (ULift.{max v w} I)
      (ModuleCat.of R ((colimit F : ModuleCat.{max v w} R) : Type (max v w))) :=
  { diag := lifted_index_diagram (R := R) F
    ι :=
      (lifted_index_cocone (R := R)
        (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
        F (eqToIso (colimit_eq_moduleCat_of_carrier (R := R) F))).ι
    isColimit :=
      common_universe_lifted_index_isColimit (R := R)
        (M := ((colimit F : ModuleCat.{max v w} R) : Type (max v w)))
        F (eqToIso (colimit_eq_moduleCat_of_carrier (R := R) F)) }

/-- Helper for Proposition 10.88.6: the lifted-index colimit presentation uses the original
colimit leg at `ULift.up i`, viewed in the definitional `ModuleCat.of` codomain. -/
lemma lifted_index_colimitPresentation_leg_hom
    (F : I ⥤ ModuleCat.{max v w} R) (i : I) :
    (((lifted_index_colimitPresentation (R := R) F).ι.app (ULift.up i)).hom :
      (F.obj i : Type (max v w)) →ₗ[R]
        ((colimit F : ModuleCat.{max v w} R) : Type (max v w))) =
      (colimit.ι F i).hom := by
  -- Proof comment: after unfolding the packaged lifted-index presentation, the leg at `ULift.up i`
  -- is definitionally the original colimit cocone map.
  rfl

/-- Helper for Proposition 10.88.6: evaluating the left tensor of the lifted-index colimit leg at
`ULift.up i` is the same as evaluating the left tensor of the original colimit leg. -/
lemma lifted_index_colimitPresentation_leg_lTensor_apply
    (F : I ⥤ ModuleCat.{max v w} R) (i : I)
    (N : Type (max u v w)) [AddCommGroup N] [Module R N]
    (x : N ⊗[R] (F.obj i : Type (max v w))) :
    ((((lifted_index_colimitPresentation (R := R) F).ι.app (ULift.up i)).hom).lTensor N) x =
      (((colimit.ι F i).hom).lTensor N) x := by
  -- Proof comment: after unfolding the packaged lifted-index leg, both sides are definitionally
  -- the same application of `1 ⊗ f_i`.
  rfl

/-- Helper for Proposition 10.88.6: a transition map in the lifted-index diagram becomes the
corresponding original transition map after tensoring on the left by a fixed module. -/
lemma lifted_index_diagram_map_lTensor_eq
    (F : I ⥤ ModuleCat.{max v w} R)
    {i : I} {j : ULift.{max v w} I}
    (w : ULift.up i ⟶ j)
    (N : Type (max u v w)) [AddCommGroup N] [Module R N] :
    (((lifted_index_diagram (R := R) F).map w).hom.lTensor N) =
      (((F.map (homOfLE (show i ≤ j.down from w.down.down))).hom).lTensor N) := by
  -- Proof comment: the lifted-index diagram was defined by forgetting `ULift.down` on the index,
  -- so its tensorized transition map is definitionally the original one.
  rfl

/-- Helper for Proposition 10.88.6: `TensorProduct.comm` rewrites right-tensor vanishing into the
left-tensor form used by the stabilization lemmas from Lemma `10.88.3`. -/
lemma lTensor_zero_of_rTensor_zero_via_comm
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] B)
    {x : A ⊗[R] N}
    (hx : (f.rTensor N) x = 0) :
    (f.lTensor N) (TensorProduct.comm R A N x) = 0 := by
  -- Proof comment: after applying `TensorProduct.comm` on the target, the left-tensor map becomes
  -- the original right-tensor map.
  have hcomm :
      TensorProduct.comm R N B ((f.lTensor N) (TensorProduct.comm R A N x)) = 0 := by
    calc
    TensorProduct.comm R N B ((f.lTensor N) (TensorProduct.comm R A N x))
        = (f.rTensor N) x := by
            simpa using
              (LinearMap.rTensor_comm (N := N) f (TensorProduct.comm R A N x)).symm
    _ = 0 := hx
  exact (TensorProduct.comm R N B).injective hcomm

/-- Helper for Proposition 10.88.6: `TensorProduct.comm` also converts left-tensor vanishing back
to right-tensor vanishing. -/
lemma rTensor_zero_of_lTensor_zero_via_comm
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] B)
    {y : N ⊗[R] A}
    (hy : (f.lTensor N) y = 0) :
    (f.rTensor N) (TensorProduct.comm R N A y) = 0 := by
  -- Proof comment: the commutativity isomorphism intertwines `f ⊗ 1` and `1 ⊗ f`, so the
  -- right-tensor map kills the commuted tensor as soon as the left-tensor map kills the original.
  calc
    (f.rTensor N) (TensorProduct.comm R N A y)
        = TensorProduct.comm R N B ((f.lTensor N) y) := by
            simpa using (LinearMap.rTensor_comm (N := N) f y)
    _ = 0 := by simp [hy]
/-- Helper for Proposition 10.88.6: a chosen stage factorization of `f` identifies tensor-kernel
membership for `f` with tensor-kernel membership for the corresponding precomposed colimit map. -/
lemma tensor_mem_ker_of_stage_factorization
    {P : ModuleCat.{max v w} R}
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    {Q : Type (max u v w)} [AddCommMonoid Q] [Module R Q]
    {x : P ⊗[R] Q}
    (hx : x ∈ LinearMap.ker (f.rTensor Q)) :
    (g₀.hom.rTensor Q) x ∈ LinearMap.ker (((colimit.ι F i ≫ c.hom).hom).rTensor Q) := by
  have hg₀_hom :
      (g₀ ≫ (colimit.ι F i ≫ c.hom)).hom = f :=
    stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀
  have hx_zero : (f.rTensor Q) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_comp : ((((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom).rTensor Q) x) = 0 := by
    -- Proof comment: after rewriting by the chosen stage factorization, the tensor equation is the
    -- same as the original vanishing of `f ⊗ 1`.
    simpa [hg₀_hom] using hx_zero
  -- Proof comment: tensoring a composite is the composite of the tensor maps, so the displayed
  -- equality is exactly kernel membership for the precomposed colimit map.
  simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx_comp

/-- Helper for Proposition 10.88.6: membership in the tensor kernel is the same as vanishing after
applying the tensor map. -/
lemma mem_rTensor_ker_iff
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {Q : Type (max u v w)} [AddCommMonoid Q] [Module R Q]
    (f : A →ₗ[R] B) (x : A ⊗[R] Q) :
    x ∈ LinearMap.ker (f.rTensor Q) ↔ (f.rTensor Q) x = 0 := by
  -- Proof comment: this is exactly the defining characterization of kernel membership.
  simp [LinearMap.mem_ker]

/-- Helper for Proposition 10.88.6: if two right-tensor maps agree, then their kernels are equal.
-/
lemma LinearMap.ker_eq_of_rTensor_eq
    {A B : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    {Q : Type (max u v w)} [AddCommMonoid Q] [Module R Q]
    {f g : A →ₗ[R] B}
    (hfg : f.rTensor Q = g.rTensor Q) :
    LinearMap.ker (f.rTensor Q) = LinearMap.ker (g.rTensor Q) := by
  -- Proof comment: after rewriting the tensor maps to be literally the same linear map, their
  -- kernels coincide definitionally.
  simpa [hfg]

/-- Helper for Proposition 10.88.6: a domination hypothesis specializes directly to any bundled
test object in `ModuleCat`. -/
lemma LinearMap.kernel_le_of_dominates_moduleCat_testObject
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hdom : g.Dominates f)
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N) := by
  let eA : A ⊗[R] N ≃ₗ[R] A ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R A) ULift.moduleEquiv.symm
  let eB : B ⊗[R] N ≃ₗ[R] B ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R B) ULift.moduleEquiv.symm
  let eC : C ⊗[R] N ≃ₗ[R] C ⊗[R] ULift.{u} N :=
    TensorProduct.congr (LinearEquiv.refl R C) ULift.moduleEquiv.symm
  have hf_apply (x : A ⊗[R] N) :
      (f.rTensor (ULift.{u} N)) (eA x) = eB ((f.rTensor N) x) := by
    -- Proof comment: changing the tensor factor from `N` to `ULift N` commutes with `f ⊗ 1`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eB]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  have hg_apply (x : A ⊗[R] N) :
      (g.rTensor (ULift.{u} N)) (eA x) = eC ((g.rTensor N) x) := by
    -- Proof comment: the same transport square holds for `g ⊗ 1`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [eA, eC]
    · intro a n
      rfl
    · intro x₁ x₂ hx₁ hx₂
      simp [hx₁, hx₂]
  intro x hx
  have hx_zero : (f.rTensor N) x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hx_lift :
      (f.rTensor (ULift.{u} N)) (eA x) = 0 := by
    calc
      (f.rTensor (ULift.{u} N)) (eA x)
          = eB ((f.rTensor N) x) := hf_apply x
      _ = 0 := by simp [hx_zero]
  have hx_lift_mem :
      eA x ∈ LinearMap.ker (f.rTensor (ULift.{u} N)) := by
    simpa [LinearMap.mem_ker] using hx_lift
  have hy_lift_mem :
      eA x ∈ LinearMap.ker (g.rTensor (ULift.{u} N)) := hdom (ULift.{u} N) hx_lift_mem
  have hy_lift : (g.rTensor (ULift.{u} N)) (eA x) = 0 := by
    simpa [LinearMap.mem_ker] using hy_lift_mem
  have hy_zero : (g.rTensor N) x = 0 := by
    apply eC.injective
    calc
      eC ((g.rTensor N) x)
          = (g.rTensor (ULift.{u} N)) (eA x) := by
              symm
              exact hg_apply x
      _ = 0 := hy_lift
      _ = eC 0 := by simp [eC]
  simpa [LinearMap.mem_ker] using hy_zero

/-- Helper for Proposition 10.88.6: kernel membership for the tensor of a composite is exactly
kernel membership for the second tensor map after applying the first tensor map. -/
lemma mem_ker_rTensor_comp_iff
    {P A B : Type (max v w)}
    [AddCommGroup P] [Module R P]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (u : P →ₗ[R] A) (f : A →ₗ[R] B)
    (N : ModuleCat.{max v w} R)
    (x : P ⊗[R] N) :
    x ∈ LinearMap.ker ((f.comp u).rTensor N) ↔
      (u.rTensor N) x ∈ LinearMap.ker (f.rTensor N) := by
  -- Proof comment: tensoring a composite is the composite of the tensor maps, so both kernel
  -- conditions are literally the same equation after rewriting by `LinearMap.rTensor_comp`.
  simp [LinearMap.mem_ker, LinearMap.rTensor_comp]

/-- Helper for Proposition 10.88.6: kernel membership for the tensor of a bundled composite is
the same as kernel membership for the second tensor map after applying the first tensor map. -/
lemma mem_ker_rTensor_moduleCat_comp_iff
    {P A B : ModuleCat.{max v w} R}
    (u : P ⟶ A) (v : A ⟶ B)
    (N : ModuleCat.{max v w} R)
    (x : (P : Type (max v w)) ⊗[R] N) :
    x ∈ LinearMap.ker
      (((((u ≫ v).hom) : (P : Type (max v w)) →ₗ[R] (B : Type (max v w))).rTensor N) :
        (P : Type (max v w)) ⊗[R] N →ₗ[R] (B : Type (max v w)) ⊗[R] N) ↔
      ((((u.hom) : (P : Type (max v w)) →ₗ[R] (A : Type (max v w))).rTensor N) x) ∈
        LinearMap.ker
          (((v.hom : (A : Type (max v w)) →ₗ[R] (B : Type (max v w))).rTensor N) :
            (A : Type (max v w)) ⊗[R] N →ₗ[R] (B : Type (max v w)) ⊗[R] N) := by
  -- Proof comment: forget to the carrier linear maps and invoke the already proved tensor-kernel
  -- statement for the corresponding unbundled composite.
  simp [LinearMap.mem_ker, LinearMap.rTensor_comp]

/-- Helper for Proposition 10.88.6: tensoring a bundled morphism into `ModuleCat.of R M` agrees
with tensoring the same underlying linear map viewed as landing in the carrier `M`. -/
lemma moduleCat_ofHom_codomain_rTensor_eq_typed
    {A : ModuleCat.{max v w} R}
    (u : A ⟶ ModuleCat.of R M)
    (N : ModuleCat.{max v w} R) :
    (((u.hom).rTensor N) :
      (A : Type (max v w)) ⊗[R] N →ₗ[R]
        ((ModuleCat.of R M : ModuleCat.{max v w} R) ⊗[R] N)) =
      ((((show (A : Type (max v w)) →ₗ[R] M from u.hom)).rTensor N) :
        (A : Type (max v w)) ⊗[R] N →ₗ[R] (M ⊗[R] N)) := by
  -- Proof comment: both tensor maps are definitionally the same on pure tensors; the only work
  -- is to normalize the codomain from bundled `ModuleCat.of R M` to the carrier `M`.
  refine LinearMap.ext fun x : (A : Type (max v w)) ⊗[R] N => ?_
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a n
    rfl
  · intro x₁ x₂ hx₁ hx₂
    simpa [hx₁, hx₂]

/-- Helper for Proposition 10.88.6: pointwise equality between a bundled morphism into
`ModuleCat.of R M` and an unbundled linear map yields equality after tensoring with a fixed
bundled test object. -/
lemma LinearMap.rTensor_eq_of_pointwise_eq_moduleCat_codomain
    {P : ModuleCat.{max v w} R}
    (u : P ⟶ ModuleCat.of R M)
    (f : P →ₗ[R] M)
    (N : ModuleCat.{max v w} R)
    (huf : ∀ p : P, u.hom p = f p) :
    ((((u.hom).rTensor N) :
      (P : Type (max v w)) ⊗[R] N →ₗ[R] (M ⊗[R] N)) =
        f.rTensor N) := by
  let u' : (P : Type (max v w)) →ₗ[R] M := u.hom
  have hu'_eq : u' = f := by
    -- Proof comment: extensionality turns the pointwise hypothesis into equality of linear maps.
    ext p
    exact huf p
  -- Proof comment: normalize the codomain of the bundled tensor map once, then rewrite by the
  -- underlying linear-map equality.
  calc
    ((((u.hom).rTensor N) :
      (P : Type (max v w)) ⊗[R] N →ₗ[R] (M ⊗[R] N)))
        = u'.rTensor N := by
            simpa [u'] using moduleCat_ofHom_codomain_rTensor_eq_typed (R := R) (M := M) u N
    _ = f.rTensor N := by rw [hu'_eq]

/-- Helper for Proposition 10.88.6: a chosen stage factorization identifies the tensor map of the
bundled composite with the tensor map of the underlying linear map `f`. -/
lemma stage_factorization_rTensor_eq
    {P : ModuleCat.{max v w} R}
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (N : ModuleCat.{max v w} R) :
    ((((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom).rTensor N) :
      (P : Type (max v w)) ⊗[R] N →ₗ[R] (M ⊗[R] N)) =
      f.rTensor N := by
  have hhom :
      (g₀ ≫ (colimit.ι F i ≫ c.hom)).hom = f :=
    stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀
  have hpointwise : ∀ p : P, ((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom) p = f p := by
    -- Proof comment: forget the bundled factorization to a pointwise identity on the source
    -- module `P`.
    intro p
    exact LinearMap.congr_fun hhom p
  let u' : (P : Type (max v w)) →ₗ[R] M := (g₀ ≫ (colimit.ι F i ≫ c.hom)).hom
  have hu'_eq : u' = f := by
    -- Proof comment: package the pointwise stage-factorization equality as equality of linear
    -- maps before tensoring.
    ext p
    exact hpointwise p
  -- Proof comment: normalize the bundled codomain once, then rewrite by the identified linear map.
  calc
    ((((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom).rTensor N) :
      (P : Type (max v w)) ⊗[R] N →ₗ[R] (M ⊗[R] N))
        = u'.rTensor N := by
            simpa [u'] using
              moduleCat_ofHom_codomain_rTensor_eq_typed (R := R) (M := M)
                (u := g₀ ≫ (colimit.ι F i ≫ c.hom)) N
    _ = f.rTensor N := by rw [hu'_eq]

/-- Helper for Proposition 10.88.6: after pushing a chosen stage factorization forward to stage
`j`, the resulting bundled composite is exactly `ModuleCat.ofHom f`. -/
lemma pushed_forward_stage_factorization_eq_ofHom
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    g₀ ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom) = ModuleCat.ofHom f := by
  -- Proof comment: this is exactly the categorical push-forward of the chosen stage
  -- factorization along the transition map `f_{ij}`.
  exact push_forward_stage_factorization (R := R) (F := F) (c := c) (g := g₀) (f := f) hg₀ hij

/-- Helper for Proposition 10.88.6: precomposing the chosen dominating stage map with the fixed
factorization `g₀` yields domination of the pushed-forward stage map over the pushed-forward
colimit map. -/
lemma pushed_forward_stage_map_dominates_stage_factorization_map
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom)) :
    (((g₀ ≫ F.map (homOfLE hij)).hom) :
      (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).Dominates
        (((g₀ ≫ (colimit.ι F i ≫ c.hom)).hom) : (P : Type (max v w)) →ₗ[R] M) := by
    -- Proof comment: precompose the stage domination hypothesis by the chosen factorization map
    -- `g₀`, while keeping the codomain frozen to the carrier `M`.
    intro Q
    intro _ _
    intro x hx
    have hx' :
        (g₀.hom.rTensor Q) x ∈
          LinearMap.ker ((((colimit.ι F i ≫ c.hom).hom) : (F.obj i : Type (max v w)) →ₗ[R] M).rTensor Q) := by
      simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hx
    have hy' :
        (g₀.hom.rTensor Q) x ∈
          LinearMap.ker
            ((((F.map (homOfLE hij)).hom) :
              (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).rTensor Q) :=
      hdom Q hx'
    have hy_zero :
        ((((F.map (homOfLE hij)).hom) :
            (F.obj i : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).rTensor Q)
          ((g₀.hom.rTensor Q) x) = 0 := by
      simpa [LinearMap.mem_ker] using hy'
    simpa [LinearMap.mem_ker, LinearMap.rTensor_comp] using hy_zero

/-- Helper for Proposition 10.88.6: pushing the chosen stage factorization forward to stage `j`
identifies the resulting frozen carrier map with `f`. -/
lemma pushed_forward_stage_factorization_hom_eq_frozen
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    ((((g₀ ≫ F.map (homOfLE hij)) ≫ (colimit.ι F j ≫ c.hom)).hom) :
      (P : Type (max v w)) →ₗ[R] M) = f := by
  have hpush :
      g₀ ≫ F.map (homOfLE hij) ≫ (colimit.ι F j ≫ c.hom) = ModuleCat.ofHom f :=
    pushed_forward_stage_factorization_eq_ofHom
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀
  -- Proof comment: forgetting the bundled equality of composites gives the desired equality of the
  -- carrier linear maps.
  simpa using congrArg ModuleCat.Hom.hom hpush

/-- Helper for Proposition 10.88.6: evaluating the frozen pushed-forward stage factorization at a
source element gives the explicit composite formula through stage `j`. -/
lemma pushed_forward_stage_factorization_frozen_apply
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (x : P) :
    f x = (colimit.ι F j ≫ c.hom).hom (((g₀ ≫ F.map (homOfLE hij)).hom) x) := by
  -- Proof comment: specialize the frozen carrier equality to the chosen source element `x`.
  calc
    f x
        = ((((g₀ ≫ F.map (homOfLE hij)) ≫ (colimit.ι F j ≫ c.hom)).hom) :
            (P : Type (max v w)) →ₗ[R] M) x := by
              exact
                (LinearMap.congr_fun
                  (pushed_forward_stage_factorization_hom_eq_frozen
                    (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀)
                  x).symm
    _ = (colimit.ι F j ≫ c.hom).hom (((g₀ ≫ F.map (homOfLE hij)).hom) x) := by
          rfl

/-- Helper for Proposition 10.88.6: the pushed-forward stage factorization gives the reverse
domination needed for the mutual-domination kernel comparison in clause `(2) → (1)`. -/
lemma pushed_forward_stage_factorization_reverse_domination_frozen
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f) :
    (f : (P : Type (max v w)) →ₗ[R] M).Dominates
      ((((g₀ ≫ F.map (homOfLE hij)).hom) :
        (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)))) := by
  let gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)) :=
    (g₀ ≫ F.map (homOfLE hij)).hom
  rcases
      pushed_forward_stage_factorization_hom
        (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀ with
    ⟨h, hh⟩
  intro N
  intro _ _
  intro x hx
  have hx_zero : (gij.rTensor N) x = 0 := by
    simpa [gij, LinearMap.mem_ker] using hx
  have hh_tensor :
      f.rTensor N = (h.rTensor N).comp (gij.rTensor N) := by
    simpa [gij, LinearMap.rTensor_comp] using
      congrArg (fun t : (P : Type (max v w)) →ₗ[R] M ↦ t.rTensor N) hh
  have hy_zero : (f.rTensor N) x = 0 := by
    calc
      (f.rTensor N) x = ((h.rTensor N).comp (gij.rTensor N)) x := by rw [hh_tensor]
      _ = (h.rTensor N) ((gij.rTensor N) x) := rfl
      _ = 0 := by rw [hx_zero, LinearMap.map_zero]
  simpa [LinearMap.mem_ker] using hy_zero

/-- Helper for Proposition 10.88.6: after pushing a chosen factorization of `f` forward to stage
`j`, the resulting stage map and `f` dominate each other. -/
lemma stage_domination_and_pushed_factorization_mutual_domination
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom)) :
    (((((F.map (homOfLE hij)).hom).comp g₀.hom) :
        (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).Dominates
          (f : (P : Type (max v w)) →ₗ[R] M)) ∧
      ((f : (P : Type (max v w)) →ₗ[R] M).Dominates
        ((((F.map (homOfLE hij)).hom).comp g₀.hom) :
          (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)))) := by
  constructor
  · -- Proof comment: rewrite the forward domination target using the chosen stage factorization
    -- of `f`.
    rw [← stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀]
    simpa [moduleCat_comp_hom_typed] using
      pushed_forward_stage_map_dominates_stage_factorization_map
        (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀ hdom
  · -- Proof comment: the reverse domination is exactly the pushed-forward factorization lemma.
    simpa [moduleCat_comp_hom_typed] using
      pushed_forward_stage_factorization_reverse_domination_frozen
        (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀

/-- Helper for Proposition 10.88.6: the mutual-domination package above can be restated directly
for the bundled composite `g₀ ≫ f_{ij}` on carrier linear maps, without exposing the internal
`LinearMap.comp` normal form. -/
lemma stage_domination_and_pushed_factorization_mutual_domination_composite
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom)) :
    let gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)) :=
      (g₀ ≫ F.map (homOfLE hij)).hom
    gij.Dominates (f : (P : Type (max v w)) →ₗ[R] M) ∧
      (f : (P : Type (max v w)) →ₗ[R] M).Dominates gij := by
  let gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)) :=
    (g₀ ≫ F.map (homOfLE hij)).hom
  -- Proof comment: this is just the already-proved mutual-domination statement, rewritten so the
  -- composite stage map appears in the same normal form used by the pending bundled kernel step.
  simpa [gij, moduleCat_comp_hom_typed] using
    stage_domination_and_pushed_factorization_mutual_domination
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀ hdom

/-- Helper for Proposition 10.88.6: fixing the carrier types explicitly prevents Lean from
reopening universes when specializing mutual domination to a bundled test module. -/
lemma kernel_eq_of_mutual_domination_moduleCat_frozen
    {A B C : Type (max v w)}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : A →ₗ[R] C}
    (hgf : g.Dominates f) (hfg : f.Dominates g)
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Proof comment: this is exactly the bundled kernel-equality owner proved earlier, but with all
  -- carrier universes fixed by the statement so later call sites do not create fresh metavariables.
  exact
    tensor_kernel_eq_of_mutual_domination_moduleCat.{u, v, w}
      (A := A) (B := B) (C := C) (f := f) (g := g) hgf hfg N

/-- Helper for Proposition 10.88.6: precomposing a dominating stage map with a chosen
factorization of `f` through stage `i` yields the kernel equality needed for clause `(1)`. -/
lemma kernel_eq_of_stage_domination_and_pushed_factorization_unbundled
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom))
    (Q : Type (max u v w)) [AddCommMonoid Q] [Module R Q] :
    LinearMap.ker (f.rTensor Q) =
      LinearMap.ker (((g₀ ≫ F.map (homOfLE hij)).hom).rTensor Q) := by
  let gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)) :=
    (g₀ ≫ F.map (homOfLE hij)).hom
  have hforward₀ :=
    pushed_forward_stage_map_dominates_stage_factorization_map
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀ hdom
  have hforward :
      (gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).Dominates
        (f : (P : Type (max v w)) →ₗ[R] M) := by
    -- Proof comment: rewrite the pushed-forward domination target using the chosen stage
    -- factorization of `f`.
    simpa [gij, stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀]
      using hforward₀
  have hreverse :
      (f : (P : Type (max v w)) →ₗ[R] M).Dominates
        (gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))) :=
    pushed_forward_stage_factorization_reverse_domination_frozen
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀
  -- Proof comment: the forward and reverse domination inclusions give equality of the tensor
  -- kernels by antisymmetry.
  exact le_antisymm (hforward Q) (hreverse Q)

/-- Helper for Proposition 10.88.6: precomposing a dominating stage map with a chosen
factorization of `f` through stage `i` yields the kernel equality needed for clause `(1)`. -/
lemma kernel_eq_of_stage_domination_and_pushed_factorization
    {P : ModuleCat.{max v w} R}
    [Module.FinitePresentation R P]
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i j : I} (hij : i ≤ j)
    (g₀ : P ⟶ F.obj i)
    (f : P →ₗ[R] M)
    (hg₀ : g₀ ≫ (colimit.ι F i ≫ c.hom) = ModuleCat.ofHom f)
    (hdom : ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ c.hom).hom))
    (N : ModuleCat.{max v w} R) :
    LinearMap.ker (f.rTensor N) =
      LinearMap.ker (((g₀ ≫ F.map (homOfLE hij)).hom).rTensor N) := by
  -- Route correction: this wrapper should reuse the finished unbundled owner directly rather than
  -- reopening the bundled mutual-domination transport layer.
  let gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w)) :=
    (g₀ ≫ F.map (homOfLE hij)).hom
  have hforward₀ :=
    pushed_forward_stage_map_dominates_stage_factorization_map
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀ hdom
  have hforward :
      (gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))).Dominates
        (f : (P : Type (max v w)) →ₗ[R] M) := by
    -- Proof comment: rewrite the pushed-forward domination target using the chosen factorization
    -- of `f` through stage `i`.
    simpa [gij, stage_factorization_hom_eq (R := R) (F := F) (c := c) (g₀ := g₀) (f := f) hg₀]
      using hforward₀
  have hreverse :
      (f : (P : Type (max v w)) →ₗ[R] M).Dominates
        (gij : (P : Type (max v w)) →ₗ[R] (F.obj j : Type (max v w))) :=
    pushed_forward_stage_factorization_reverse_domination_frozen
      (R := R) (F := F) (c := c) (hij := hij) (g₀ := g₀) (f := f) hg₀
  -- Proof comment: specialize both domination directions to the bundled test object `N` and apply
  -- antisymmetry of submodule inclusion.
  exact le_antisymm
    (LinearMap.kernel_le_of_dominates_moduleCat_testObject.{u, v, w}
      (A := (P : Type (max v w))) (B := M) (C := (F.obj j : Type (max v w)))
      (f := f) (g := gij) hforward N)
    (LinearMap.kernel_le_of_dominates_moduleCat_testObject.{u, v, w}
      (A := (P : Type (max v w))) (B := (F.obj j : Type (max v w))) (C := M)
      (f := gij) (g := f) hreverse N)

/-- Helper for Proposition 10.88.6: tensor vanishing after the identified colimit map already
vanishes before postcomposing with the colimit isomorphism. -/
lemma tensor_zero_of_iso_comp_colimit_zero
    (F : I ⥤ ModuleCat.{max v w} R)
    (c : colimit F ≅ ModuleCat.of R M)
    {i : I}
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    {x : F.obj i ⊗[R] N}
    (hx : (((colimit.ι F i ≫ c.hom).hom).rTensor N) x = 0) :
    (((colimit.ι F i).hom).rTensor N) x = 0 := by
  have hcolim_iso : colimit.ι F i = colimit.ι F i ≫ c.hom ≫ c.inv := by
    -- Compose `colimit.ι F i` with the identity `c.hom ≫ c.inv = 𝟙` on the colimit object.
    calc
      colimit.ι F i = colimit.ι F i ≫ 𝟙 (colimit F) := by simp
      _ = colimit.ι F i ≫ (c.hom ≫ c.inv) := by rw [c.hom_inv_id]
      _ = colimit.ι F i ≫ c.hom ≫ c.inv := by simp
  have hcolim_tensor :
      (((colimit.ι F i).hom).rTensor N) x =
        (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := by
    -- Evaluate the morphism identity above after tensoring with `N`.
    simpa using congrArg
      (fun t : F.obj i ⟶ colimit F ↦ (t.hom.rTensor N) x) hcolim_iso
  have hcolim_apply :
      (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x =
        (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := by
    -- Tensoring a composite is the composite of the tensor maps.
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (colimit.ι F i ≫ c.hom).hom)
        (g := c.inv.hom) (x := x))
  calc
    (((colimit.ι F i).hom).rTensor N) x
        = (((colimit.ι F i ≫ c.hom ≫ c.inv).hom).rTensor N) x := hcolim_tensor
    _ = (LinearMap.rTensor N (c.inv.hom.comp ((colimit.ι F i ≫ c.hom).hom))) x := by
          rfl
    _ = (c.inv.hom.rTensor N) ((((colimit.ι F i ≫ c.hom).hom).rTensor N) x) := hcolim_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

/-- Helper for Proposition 10.88.6: if a later transition map kills a tensor element, then any
transition map factoring through it kills the same tensor element. -/
lemma tensor_zero_of_transition_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    {i j k : I} {hij : i ≤ j} {hik : i ≤ k}
    {N : Type (max u v w)} [AddCommGroup N] [Module R N]
    {x : F.obj i ⊗[R] N}
    {h : F.obj k ⟶ F.obj j}
    (hh : F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h)
    (hx : (((F.map (homOfLE hik)).hom).rTensor N) x = 0) :
    (((F.map (homOfLE hij)).hom).rTensor N) x = 0 := by
  have hh_tensor :
      (((F.map (homOfLE hij)).hom).rTensor N) x =
        ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := by
    -- Evaluate the factorization identity after tensoring with `N`.
    simpa using congrArg (fun t : F.obj i ⟶ F.obj j ↦ (t.hom.rTensor N) x) hh
  have hh_apply :
      ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) =
        (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := by
    -- Tensoring the factored map converts the target to a postcomposition of the later-stage map.
    change (LinearMap.rTensor N (h.hom.comp (F.map (homOfLE hik)).hom)) x =
      (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x)
    simpa only [LinearMap.rTensor_comp] using
      (LinearMap.rTensor_comp_apply (M := N) (f := (F.map (homOfLE hik)).hom)
        (g := h.hom) (x := x))
  calc
    (((F.map (homOfLE hij)).hom).rTensor N) x
        = ((((F.map (homOfLE hik) ≫ h).hom).rTensor N) x) := hh_tensor
    _ = (h.hom.rTensor N) ((((F.map (homOfLE hik)).hom).rTensor N) x) := hh_apply
    _ = 0 := by rw [hx]; simp only [LinearMap.map_zero]

end
