import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap10.Lemma_10_51_3
import stacks_proof.stacks_project.Chap15.Lemma_15_102_Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] CategoryTheory.HasExt.standard

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open scoped IdealPowerSubmodule

universe u v

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M N : (ModuleCat.{u} A)) [Module.Finite A M]

local notation "Mod" => ModuleCat A

/- Domain-style sampling:
- primary domain: Ext-groups of finite modules over a Noetherian ring, with restriction maps
  induced by the inclusions `I^[n] M ↪ M` and `I^[n - c] N ↪ N`;
- sampled owner declarations:
  `idealPowerSubtype`,
  `idealPowerSubtypeExtPrecomp`,
  `idealPowerSubtypeExtPostcomp`;
- best owner abstraction: the chapter owner surface for these restriction maps is
  `idealPowerSubtypeExtPrecomp` in the source variable and `idealPowerSubtypeExtPostcomp` in the
  target variable, both derived canonically from `idealPowerSubtype`;
- primitive data: the ideal `I`, the finite source module `M`, the target module `N`, the degree
  `p`, and the ideal-power inclusions on `M` and `N`;
- derived API: the eventual factorization of the restriction map through
  `Ext^p_A(I^[n] M, I^[n - c] N)`.

Layer triage:
- `source-facing`: the eventual factorization statement from the Stacks lemma;
- `core/canonical`: `idealPowerSubtype`, `Ext.precompOfLinear`, and `Ext.postcompOfLinear`;
- `bridge/view`: the witness map `φ` giving the factorization through the ideal-power target. -/

/-- Helper for Lemma 15.102.2: restricting an `A`-linear map along `I^[n] M ↪ M` lands in the
shifted ideal-power stage `I^[n - c] N`. -/
abbrev idealPowerStageRestrictedHom
    (n c : ℕ) (f : M ⟶ N) :
    idealPowerStage I n M ⟶ idealPowerStage I (n - c) N :=
  ModuleCat.ofHom <|
    (Submodule.inclusion (idealPowerSubmodule_mono I (Nat.sub_le n c))).comp
      (idealPowerSubmoduleMap I f.hom n)

/-- Helper for Lemma 15.102.2: after composing with the ambient inclusion
`I^[n - c] N ↪ N`, the restricted map agrees with the original map restricted to `I^[n] M`. -/
theorem idealPowerStageRestrictedHom_comp_subtype
    (f : M ⟶ N) (n c : ℕ) (x : idealPowerStage I n M) :
    idealPowerSubtype I (n - c) N
        ((idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f).hom x) =
      f.hom ((idealPowerSubtype I n M) x) := by
  -- Both sides evaluate the same linear map on the element `x`.
  rfl

/-- Helper for Lemma 15.102.2: as module morphisms, stagewise restriction followed by the ambient
inclusion of the shifted target stage equals restriction along the source-stage inclusion. -/
theorem idealPowerStageRestrictedHom_comp_subtype_hom
    (f : M ⟶ N) (n c : ℕ) :
    (idealPowerSubtype I (n - c) N).comp
        (idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f).hom =
      f.hom.comp (idealPowerSubtype I n M) := by
  -- Compare the two underlying linear maps on the elements of `I^[n] M`.
  ext x
  exact idealPowerStageRestrictedHom_comp_subtype (I := I) (M := M) (N := N) f n c x

/-- Helper for Lemma 15.102.2: the stagewise restriction construction is additive in the ambient
map. -/
theorem idealPowerStageRestrictedHom_add
    (f g : M ⟶ N) (n c : ℕ) :
    idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c (f + g) =
      idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f +
        idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c g := by
  -- Restriction and the stage inclusions are pointwise linear.
  ext x
  rfl

/-- Helper for Lemma 15.102.2: the stagewise restriction construction commutes with scalar
multiplication. -/
theorem idealPowerStageRestrictedHom_smul
    (a : A) (f : M ⟶ N) (n c : ℕ) :
    idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c (a • f) =
      a • idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f := by
  -- The shifted-stage restriction operator is defined by composing `A`-linear maps.
  ext x
  rfl

/-- Helper for Lemma 15.102.2: restricting morphisms stagewise defines an `A`-linear map on Hom
groups. -/
abbrev idealPowerStageRestrictionLinear
    (n c : ℕ) :
    (M ⟶ N) →ₗ[A] (idealPowerStage I n M ⟶ idealPowerStage I (n - c) N) where
  toFun f := idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f
  map_add' f g := idealPowerStageRestrictedHom_add (I := I) (M := M) (N := N) f g n c
  map_smul' a f := idealPowerStageRestrictedHom_smul (I := I) (M := M) (N := N) a f n c

/-- Helper for Lemma 15.102.2: the degree-zero restriction map on `Ext` factors through the
shifted ideal-power target via the stagewise restriction operator on `Hom`. -/
noncomputable def idealPowerStageRestrictionExtZero
    (n c : ℕ) :
    Ext M N 0 →ₗ[A] Ext (idealPowerStage I n M) (idealPowerStage I (n - c) N) 0 :=
  (((Ext.linearEquiv₀ :
      Ext (idealPowerStage I n M) (idealPowerStage I (n - c) N) 0 ≃ₗ[A]
        (idealPowerStage I n M ⟶ idealPowerStage I (n - c) N)).symm.toLinearMap) ∘ₗ
      ((idealPowerStageRestrictionLinear (I := I) (M := M) (N := N) n c).comp
        ((Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)).toLinearMap)))

/-- Helper for Lemma 15.102.2: after rewriting `Ext⁰` as `Hom`, the degree-zero factorization
through the shifted ideal-power stage recovers the canonical restriction map. -/
theorem idealPowerStageRestrictionExtZero_mk₀
    (n c : ℕ) (f : M ⟶ N) :
    idealPowerStageRestrictionExtZero (I := I) (M := M) (N := N) n c (Ext.mk₀ f) =
      Ext.mk₀ (idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f) := by
  -- The factorization map was defined by transporting the stagewise restriction operator across
  -- the canonical identification `Ext⁰ ≃ Hom`.
  change
      Ext.mk₀
        ((idealPowerStageRestrictionLinear (I := I) (M := M) (N := N) n c ∘ₗ
            (Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)).toLinearMap) (Ext.mk₀ f)) =
        Ext.mk₀ (idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f)
  have hmk :
      ((Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)) (Ext.mk₀ f)) = f := by
    apply ((Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)).symm.injective)
    simpa [Ext.homEquiv₀_symm_apply]
  apply congrArg Ext.mk₀
  exact congrArg (idealPowerStageRestrictionLinear (I := I) (M := M) (N := N) n c) hmk

namespace CategoryTheory.Abelian.Ext

/-- Helper for Lemma 15.102.2: postcomposition by a degree-zero `Ext` class computes by ordinary
composition on the underlying module morphisms. -/
theorem postcompOfLinear_mk₀
    {X Y Z : Mod} (f : X ⟶ Y) (v : Y ⟶ Z) :
    ((Ext.mk₀ v).postcompOfLinear A X (add_zero 0)) (Ext.mk₀ f) = Ext.mk₀ (f ≫ v) := by
  -- In degree `0`, the Yoneda product with `mk₀ v` is just composition with `v`.
  change (Ext.mk₀ f).comp (Ext.mk₀ v) (add_zero 0) = Ext.mk₀ (f ≫ v)
  simpa [Ext.mk₀_comp_mk₀]

/-- Helper for Lemma 15.102.2: precomposition by a degree-zero `Ext` class computes by ordinary
composition on the underlying module morphisms. -/
theorem precompOfLinear_mk₀
    {X X' Y : Mod} (u : X' ⟶ X) (f : X ⟶ Y) :
    ((Ext.mk₀ u).precompOfLinear A Y (zero_add 0)) (Ext.mk₀ f) = Ext.mk₀ (u ≫ f) := by
  -- In degree `0`, the Yoneda product with `mk₀ u` is just composition with `u`.
  change (Ext.mk₀ u).comp (Ext.mk₀ f) (zero_add 0) = Ext.mk₀ (u ≫ f)
  simpa [Ext.mk₀_comp_mk₀]

end CategoryTheory.Abelian.Ext

/-- Helper for Lemma 15.102.2: after rewriting `Ext⁰` as `Hom`, the degree-zero factorization
through the shifted ideal-power stage recovers the canonical restriction map. -/
theorem idealPowerStageRestrictionExtZero_spec
    (n c : ℕ) (x : Ext M N 0) :
    idealPowerSubtypeExtPostcomp I (n - c) (idealPowerStage I n M) N 0
        (idealPowerStageRestrictionExtZero (I := I) (M := M) (N := N) n c x) =
      idealPowerSubtypeExtPrecomp I n M N 0 x := by
  -- Route correction: the owner wrappers do not reduce on their own, so first replace `x` by a
  -- degree-zero class `mk₀ f` and then compute both sides by the new `mk₀` interface lemmas.
  obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective x
  change
    idealPowerSubtypeExtPostcomp I (n - c) (idealPowerStage I n M) N 0
        (idealPowerStageRestrictionExtZero (I := I) (M := M) (N := N) n c (Ext.mk₀ f)) =
      idealPowerSubtypeExtPrecomp I n M N 0 (Ext.mk₀ f)
  rw [idealPowerStageRestrictionExtZero_mk₀]
  rw [idealPowerSubtypeExtPostcomp, idealPowerSubtypeExtPrecomp]
  change
    (Ext.mk₀ (idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f)).comp
        (Ext.mk₀ (ModuleCat.ofHom (idealPowerSubtype I (n - c) N))) (add_zero 0) =
      (Ext.mk₀ (ModuleCat.ofHom (idealPowerSubtype I n M))).comp (Ext.mk₀ f) (zero_add 0)
  -- The two Yoneda products are equal because the underlying composites of module morphisms agree.
  let leftRes : idealPowerStage I n M ⟶ idealPowerStage I (n - c) N :=
    idealPowerStageRestrictedHom (I := I) (M := M) (N := N) n c f
  let leftMor : idealPowerStage I n M ⟶ N :=
    ModuleCat.ofHom ((idealPowerSubtype I (n - c) N).comp leftRes.hom)
  let rightMor : idealPowerStage I n M ⟶ N :=
    ModuleCat.ofHom (f.hom.comp (idealPowerSubtype I n M))
  have hMor : leftMor = rightMor := by
    apply ModuleCat.hom_ext_iff.mpr
    simpa [leftRes, leftMor, rightMor] using
      idealPowerStageRestrictedHom_comp_subtype_hom (I := I) (M := M) (N := N) f n c
  simpa [leftRes, leftMor, rightMor, Ext.mk₀_comp_mk₀] using congrArg Ext.mk₀ hMor

/-- Helper for Lemma 15.102.2: in degree `0`, the restriction map always factors through the
shifted ideal-power target. This is the base case input for the positive-degree argument. -/
theorem exists_ext_zero_factorization_through_ideal_power_target (c n : ℕ) :
    let Mn := idealPowerStage I n M
    let Nn := idealPowerStage I (n - c) N
    ∃ φ : Ext M N 0 →ₗ[A] Ext Mn Nn 0,
      ∀ x : Ext M N 0,
        idealPowerSubtypeExtPostcomp I (n - c) Mn N 0 (φ x) =
          idealPowerSubtypeExtPrecomp I n M N 0 x := by
  -- The explicit degree-zero factorization is the `Hom`-level stagewise restriction operator.
  refine ⟨idealPowerStageRestrictionExtZero (I := I) (M := M) (N := N) n c, ?_⟩
  intro x
  exact idealPowerStageRestrictionExtZero_spec (I := I) (M := M) (N := N) n c x

/-- Helper for Lemma 15.102.2: surjectivity of `f` descends to the restricted map
`I^[n] X → I^[n] Y`. -/
theorem idealPowerSubmoduleMap_surjective_of_surjective
    {X Y : Type v} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    {f : X →ₗ[A] Y} (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (idealPowerSubmoduleMap I f n) := by
  rintro ⟨y, hy⟩
  rw [idealPowerSubmodule] at hy
  -- Follow the generators of `I ^ n • ⊤`: each scalar multiple lifts along the surjection `f`,
  -- and sums of lifted generators stay inside the same ideal-power stage.
  have hx :
      ∃ x : X, f x = y ∧ x ∈ I ^ n • (⊤ : Submodule A X) := by
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr x hx
      rcases hf x with ⟨x', rfl⟩
      refine ⟨r • x', by simp, ?_⟩
      exact Submodule.smul_mem_smul hr (by simpa using hx)
    · intro y₁ y₂ hy₁ hy₂
      rcases hy₁ with ⟨x₁, rfl, hx₁⟩
      rcases hy₂ with ⟨x₂, rfl, hx₂⟩
      refine ⟨x₁ + x₂, by simp, Submodule.add_mem _ hx₁ hx₂⟩
  rcases hx with ⟨x, rfl, hxmem⟩
  refine ⟨⟨x, ?_⟩, rfl⟩
  simpa [idealPowerSubmodule] using hxmem

/-- Helper for Lemma 15.102.2: the canonical short exact row attached to the restricted stage map
is available as soon as the original map is surjective. -/
theorem idealPowerSubmoduleMap_shortExact_of_surjective
    {X Y : Type v} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    {f : X →ₗ[A] Y} (hf : Function.Surjective f) (n : ℕ) :
    (LinearMap.shortComplexKer (idealPowerSubmoduleMap I f n)).ShortExact := by
  -- Stage exactness is now separated from Artin-Rees: it is the kernel row of a surjective map.
  simpa using
    (LinearMap.shortExact_shortComplexKer
      (f := idealPowerSubmoduleMap I f n)
      (idealPowerSubmoduleMap_surjective_of_surjective (I := I) (f := f) hf n))

/-- Helper for Lemma 15.102.2: a finite module admits a finite free cover whose kernel row is the
canonical short exact sequence `0 → ker(π) → F → M → 0`. -/
theorem exists_finite_free_cover_shortExact :
    ∃ (F : Mod) (π : F ⟶ M),
      Module.Free A F ∧ Module.Finite A F ∧ Function.Surjective π.hom ∧
        Module.Finite A (LinearMap.ker π.hom) ∧
        (LinearMap.shortComplexKer π.hom).ShortExact := by
  -- The positive-degree route starts by freezing one finite free cover of `M`.
  obtain ⟨n, f, hf⟩ :=
    (Module.Finite.iff_exists_surjective_free (R := A) (M := M)).mp inferInstance
  refine ⟨ModuleCat.of A (Fin n → A), ModuleCat.ofHom f, ?_, ?_, hf, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · infer_instance
  · simpa using LinearMap.shortExact_shortComplexKer hf

/-- Helper for Lemma 15.102.2: Artin-Rees applied to the kernel inclusion `ker(π) ↪ F` gives a
uniform shift whose stage-`c + n` intersection lands in `I^[n] ker(π)`. -/
theorem exists_kernel_subtype_artin_rees_shift
    {F : Mod} [Module.Finite A F] (π : F ⟶ M) :
    ∃ c : ℕ, ∀ n : ℕ,
      Submodule.comap (LinearMap.ker π.hom).subtype (I^[c + n] F) ≤
        I^[n] (LinearMap.ker π.hom) := by
  let _ : Module.Finite A (LinearMap.ker π.hom) := by
    infer_instance
  obtain ⟨c, hpow, _⟩ :=
    Ideal.exists_artin_rees_constant_of_exact I
      (LinearMap.exact_subtype_ker_map (LinearMap.ker π.hom).subtype)
  refine ⟨c, ?_⟩
  intro n
  have hker : LinearMap.ker (LinearMap.ker π.hom).subtype = ⊥ := by
    ext x
    simp
  -- With zero kernel, the owner Artin-Rees equality collapses to the shifted containment we need.
  calc
    Submodule.comap (LinearMap.ker π.hom).subtype (I^[c + n] F) =
        I ^ n • Submodule.comap (LinearMap.ker π.hom).subtype (I ^ c • (⊤ : Submodule A F)) := by
      simpa [idealPowerSubmodule, hker, show c + n - c = n by omega] using
        hpow (c + n) (Nat.le_add_right c n)
    _ ≤ I ^ n • (⊤ : Submodule A (LinearMap.ker π.hom)) := by
      exact smul_mono_right _ le_top
    _ = I^[n] (LinearMap.ker π.hom) := rfl

/-- Helper for Lemma 15.102.2: forgetting the stage condition sends the kernel of the restricted
map `I^[n] F → I^[n] M` into the ambient kernel `ker(π)`. -/
abbrev stageKernelToKernel
    {F : Mod} (π : F ⟶ M) (n : ℕ) :
    ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom n)) ⟶
      ModuleCat.of A (LinearMap.ker π.hom) :=
  ModuleCat.ofHom
    { toFun := fun x ↦
        ⟨x.1.1, by
          -- The restricted kernel equation already says that the underlying element is killed by
          -- `π.hom`; forget the target-stage subtype.
          exact congrArg Subtype.val x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }

/-- Helper for Lemma 15.102.2: after the Artin-Rees shift, the actual kernel of the restricted
map `I^[c + m] F → I^[c + m] M` maps canonically into `I^[m] ker(π)`. -/
theorem exists_shifted_stage_kernel_comparison_of_cover
    {F : Mod} [Module.Finite A F] (π : F ⟶ M) (hπsurj : Function.Surjective π.hom) :
    ∃ c : ℕ, ∀ m : ℕ,
      ∃ κ :
        ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c + m))) ⟶
          idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)),
        (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
          (stageKernelToKernel (I := I) (π := π) (n := c + m)).hom ∧
        (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c + m))).ShortExact := by
  rcases exists_kernel_subtype_artin_rees_shift (I := I) (π := π) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro m
  let κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)) :=
    ModuleCat.ofHom
      { toFun := fun x ↦
          ⟨((stageKernelToKernel (I := I) (π := π) (n := c + m)).hom x),
            hc m <| by
              -- The stage kernel element lies in `I^[c + m] F` by construction, so Artin-Rees
              -- places its ambient-kernel image inside `I^[m] ker(π)`.
              exact x.1.2⟩
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro a x
          rfl }
  refine ⟨κ, ?_, ?_⟩
  · -- Both composites forget to the same ambient kernel element.
    ext x
    rfl
  · -- The restricted row is the canonical kernel row of a surjective stage map.
    exact idealPowerSubmoduleMap_shortExact_of_surjective
      (I := I) (f := π.hom) hπsurj (c + m)

/-- Helper for Lemma 15.102.2: the shifted restricted kernel row maps to the original cover row
by forgetting stage conditions on all three terms. -/
abbrev restricted_cover_row_hom
    {F : Mod} (π : F ⟶ M) (c m : ℕ) :
    LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c + m)) ⟶
      LinearMap.shortComplexKer π.hom :=
  CategoryTheory.ShortComplex.Hom.mk
    (stageKernelToKernel (I := I) (π := π) (n := c + m))
    (ModuleCat.ofHom (idealPowerSubtype I (c + m) F))
    (ModuleCat.ofHom (idealPowerSubtype I (c + m) M))
    (by
      -- On the left square, both composites are the canonical inclusion of the restricted kernel
      -- into `F`.
      apply ModuleCat.hom_ext_iff.mpr
      ext x
      rfl)
    (by
      -- On the right square, both composites evaluate to `π.hom` on the underlying stage element.
      apply ModuleCat.hom_ext_iff.mpr
      ext x
      rfl)

/-- Helper for Lemma 15.102.2: the concrete row morphism above rewrites the extension class of the
restricted cover row into the restriction of the original cover extension class. -/
theorem restricted_cover_extClass_naturality
    {F : Mod} (π : F ⟶ M) (c m : ℕ)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact) :
    hstage.extClass.comp
        (Ext.mk₀ (stageKernelToKernel (I := I) (π := π) (n := c + m))) (zero_add 1) =
      (Ext.mk₀ (ModuleCat.ofHom (idealPowerSubtype I (c + m) M))).comp hπ.extClass (add_zero 1) := by
  -- The owner theorem `extClass_naturality` applies directly once the restricted row morphism is
  -- written in the canonical `ShortComplex.Hom` form.
  simpa [restricted_cover_row_hom] using
    (CategoryTheory.ShortComplex.ShortExact.extClass_naturality
      (h₁ := hstage) (h₂ := hπ)
      (f := restricted_cover_row_hom (I := I) (M := M) (π := π) c m))

/-- Helper for Lemma 15.102.2: for the fixed free cover row `0 → ker(π) → F → M → 0`, the
degree-`1` contravariant boundary map `Ext⁰_A(ker(π), N) → Ext¹_A(M, N)` is surjective. -/
theorem cover_boundary_surjective_ext_one
    {F : Mod} (π : F ⟶ M) (hFproj : CategoryTheory.Projective F)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact) :
    Function.Surjective
      (hπ.extClass.precompOfLinear A N (Nat.add_zero 1) :
        Ext (ModuleCat.of A (LinearMap.ker π.hom)) N 0 →ₗ[A] Ext M N 1) := by
  intro e
  let S := LinearMap.shortComplexKer π.hom
  letI : CategoryTheory.Projective F := hFproj
  have hkill : (Ext.mk₀ S.g).comp e (zero_add 1) = 0 := by
    -- The middle term of the original cover row is projective, so the image in `Ext¹(F, N)`
    -- vanishes and exactness can lift `e` across the boundary map.
    have hkill' : (Ext.mk₀ π).comp e (zero_add 1) = 0 := by
      exact ((Ext.mk₀ π).comp e (zero_add 1)).eq_zero_of_projective
    simpa [S] using hkill'
  obtain ⟨x, hx⟩ := contravariant_sequence_exact₃ hπ N e hkill (Nat.add_zero 1)
  refine ⟨x, ?_⟩
  -- The exactness witness is exactly the boundary-map formula defining the linear map above.
  simpa [S] using hx

/-- Helper for Lemma 15.102.2: for the fixed projective cover row `0 → ker(π) → F → M → 0`,
the contravariant boundary map is a linear equivalence in every positive degree. -/
noncomputable def cover_boundary_linearEquiv_ext_succ
    {F : Mod} (π : F ⟶ M) (hFproj : CategoryTheory.Projective F)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact) (q : ℕ) :
    Ext (ModuleCat.of A (LinearMap.ker π.hom)) N (q + 1) ≃ₗ[A] Ext M N (q + 2) := by
  let δ :
      Ext (ModuleCat.of A (LinearMap.ker π.hom)) N (q + 1) →ₗ[A] Ext M N (q + 2) :=
    hπ.extClass.precompOfLinear A N (Nat.add_comm 1 (q + 1))
  have hsurj : Function.Surjective δ := by
    letI : CategoryTheory.Projective F := hFproj
    intro e
    exact Ext.contravariant_sequence_exact₃ hπ N e (Ext.eq_zero_of_projective _)
      (Nat.add_comm 1 (q + 1))
  have hinj : Function.Injective δ := by
    letI : CategoryTheory.Projective F := hFproj
    intro x y hxy
    have hsub : δ (x - y) = 0 := by
      rw [LinearMap.map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hπ N (x - y)
      (Nat.add_comm 1 (q + 1)) hsub
    have hzzero : z = 0 := by
      exact z.eq_zero_of_projective
    have hxy' : x - y = 0 := by
      simpa [δ, hzzero] using hz.symm
    exact sub_eq_zero.mp hxy'
  -- The long exact sequence is exact on both sides of the boundary map because `F` is projective.
  exact LinearEquiv.ofBijective δ ⟨hinj, hsurj⟩

/-- Helper for Lemma 15.102.2: after the Artin-Rees shift and the kernel comparison map `κ`,
the stage boundary row yields the kernel-side boundary map used in the degree-`1` descent. -/
noncomputable abbrev restricted_cover_boundary_lift
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact) :
    Ext (ModuleCat.of A (LinearMap.ker π.hom)) N 0 →ₗ[A]
      Ext (idealPowerStage I (c0 + m) M)
        (idealPowerStage I m N) 1 :=
  (hstage.extClass.precompOfLinear A (idealPowerStage I m N) (Nat.add_zero 1)) ∘ₗ
    ((Ext.mk₀ κ).precompOfLinear A (idealPowerStage I m N) (zero_add 0)) ∘ₗ
      idealPowerStageRestrictionExtZero
        (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) m 0

/-- Helper for Lemma 15.102.2: after forgetting the stage condition on the target, the
kernel-side input used in the degree-`1` boundary calculation agrees with the stage-middle
restriction of the ambient map. -/
theorem restricted_cover_kernel_input_eq_stage_middle_restriction
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (f : F ⟶ N) :
    ((idealPowerSubtype I m N).comp
      (idealPowerStageRestrictedHom
        (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) m 0
        (ModuleCat.ofHom (f.hom.comp ((LinearMap.ker π.hom).subtype)))).hom).comp κ.hom =
      ((idealPowerSubtype I ((c0 + m) - c0) N).comp
        (idealPowerStageRestrictedHom (I := I) (M := F) (N := N) (c0 + m) c0 f).hom).comp
          (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).f.hom := by
  -- Compare the two composites on a stage-kernel element after forgetting the stage condition.
  ext x
  have hκx :=
    LinearMap.congr_fun
      ((show
          (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
            (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom
        from hκ)) x
  have hκx_val :
      (((idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))) (κ.hom x) :
          ModuleCat.of A (LinearMap.ker π.hom)).1 : F) =
        ((LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).f.hom x : F) := by
    simpa [stageKernelToKernel] using congrArg Subtype.val hκx
  -- After forgetting the stage conditions, both composites apply `f` to the same element of `F`.
  simpa using congrArg f.hom hκx_val

/-- Helper for Lemma 15.102.2: after postcomposing with `I^[m] N ↪ N`, the restricted kernel-side
input attached to `g : ker(π) ⟶ N` is exactly the ambient kernel comparison map followed by `g`. -/
theorem restricted_cover_kernel_target_eq
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (g : ModuleCat.of A (LinearMap.ker π.hom) ⟶ N) :
    ((idealPowerSubtype I m N).comp
        (idealPowerStageRestrictedHom
          (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) m 0 g).hom).comp κ.hom =
      g.hom.comp (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom := by
  -- First rewrite the stage-restricted map after postcomposing with the ambient inclusion.
  have hcomp :
      (((idealPowerSubtype I m N).comp
          (idealPowerStageRestrictedHom
            (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) m 0 g).hom).comp
          κ.hom) =
        g.hom.comp (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom := by
    calc
      (((idealPowerSubtype I m N).comp
          (idealPowerStageRestrictedHom
            (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) m 0 g).hom).comp
            κ.hom)
        =
          (g.hom.comp
            (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom)))).comp κ.hom := by
            simpa [LinearMap.comp_assoc] using
              congrArg (fun φ ↦ φ.comp κ.hom)
                (idealPowerStageRestrictedHom_comp_subtype_hom
                  (I := I) (M := ModuleCat.of A (LinearMap.ker π.hom)) (N := N) g m 0)
      _ = g.hom.comp (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom := by
            simpa [LinearMap.comp_assoc] using congrArg (g.hom.comp) hκ
  exact hcomp

/-- Helper for Lemma 15.102.2: the stage-boundary factorization is reduced to a computation on a
degree-zero representative `Ext.mk₀ g`. -/
theorem restricted_cover_boundary_factorization_mk₀
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact)
    (g : ModuleCat.of A (LinearMap.ker π.hom) ⟶ N) :
    idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1
        (restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage
          (Ext.mk₀ g)) =
      idealPowerSubtypeExtPrecomp I (c0 + m) M N 1
        ((hπ.extClass.precompOfLinear A N (Nat.add_zero 1)) (Ext.mk₀ g)) := by
  -- TODO: the remaining comparison square must be normalized at the level of Yoneda products:
  -- first compute the left-hand side as
  -- `hstage.extClass.comp (((Ext.mk₀ κ).comp (Ext.mk₀ g_restricted)).comp (Ext.mk₀ subtypeN))`,
  -- then rewrite the triple `mk₀` composite using `restricted_cover_kernel_target_eq`, and
  -- finally apply `restricted_cover_extClass_naturality` plus one associativity step.
  sorry

/-- Helper for Lemma 15.102.2: in the restricted stage row, the boundary map kills every
degree-zero class coming from the middle term. -/
theorem restricted_stage_boundary_kills_middle_image_mk₀
    {F : Mod} (π : F ⟶ M) (c0 m : ℕ)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (u :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).X₂ ⟶
        idealPowerStage I m N) :
    let S := LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))
    (hstage.extClass.precompOfLinear A (idealPowerStage I m N) (Nat.add_zero 1))
        (((Ext.mk₀ S.f).precompOfLinear A (idealPowerStage I m N) (zero_add 0))
          (Ext.mk₀ u)) = 0 := by
  let S := LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))
  -- Consecutive maps in the contravariant long exact Ext sequence compose to zero.
  have hseq :=
    (Ext.contravariantSequence_exact hstage (idealPowerStage I m N) 0 1 (by decide)).zero 1
      (by decide)
  rw [show (Ext.contravariantSequence hstage (idealPowerStage I m N) 0 1 (by decide)).map' 1 2
      (by decide) (by decide) =
        AddCommGrpCat.ofHom ((Ext.mk₀ S.f).precomp (idealPowerStage I m N) (zero_add 0)) by
      rfl,
    show (Ext.contravariantSequence hstage (idealPowerStage I m N) 0 1 (by decide)).map' 2 3
      (by decide) (by decide) =
        AddCommGrpCat.ofHom
          (hstage.extClass.precomp (idealPowerStage I m N) (Nat.add_zero 1)) by
      rfl] at hseq
  have hval := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom' hseq) (Ext.mk₀ u)
  change
    (hstage.extClass.precomp (idealPowerStage I m N) (Nat.add_zero 1))
      (((Ext.mk₀ S.f).precomp (idealPowerStage I m N) (zero_add 0))
        (Ext.mk₀ u)) = 0 at hval
  simpa using hval

/-- Helper for Lemma 15.102.2: the stage boundary kills the image of the ambient cover map after
reducing to a degree-zero representative `Ext.mk₀ f`. -/
theorem restricted_cover_boundary_kills_cover_image_mk₀
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (f : F ⟶ N) :
    let βm := restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage;
    βm ((Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker π.hom).subtype)).comp (Ext.mk₀ f)
      (zero_add 0)) = 0 := by
  -- TODO: identify the input with the image of the restricted middle-term map
  -- `Ext⁰(I^[c₀+m]F, I^[m]N) → Ext⁰(ker(I^[c₀+m]F → I^[c₀+m]M), I^[m]N)` using
  -- `restricted_cover_kernel_input_eq_stage_middle_restriction`, then apply
  -- `restricted_stage_boundary_kills_middle_image_mk₀`.
  sorry

/-- Helper for Lemma 15.102.2: after postcomposing the lifted stage boundary with the ambient
inclusion `I^[m] N ↪ N`, one recovers the original cover boundary restricted along
`I^[c₀ + m] M ↪ M`. -/
theorem restricted_cover_boundary_factorization
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact)
    (x : Ext (ModuleCat.of A (LinearMap.ker π.hom)) N 0) :
    idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1
        (restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage x) =
      idealPowerSubtypeExtPrecomp I (c0 + m) M N 1
        ((hπ.extClass.precompOfLinear A N (Nat.add_zero 1)) x) := by
  -- Route correction: reduce the public `Ext⁰` statement to the concrete `mk₀` computation.
  obtain ⟨g, rfl⟩ := Ext.homEquiv₀.symm.surjective x
  simpa using
    restricted_cover_boundary_factorization_mk₀
      (I := I) (M := M) (N := N) (π := π) (c0 := c0) (m := m)
      κ hκ hstage hπ g

/-- Helper for Lemma 15.102.2: the lifted stage boundary vanishes on the image of the ambient
cover map `Ext⁰(F, N) → Ext⁰(ker(π), N)`. -/
theorem restricted_cover_boundary_kills_cover_image
    {F : Mod} (π : F ⟶ M) [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (y : Ext F N 0) :
    let βm := restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage;
    βm ((Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker π.hom).subtype)).comp y (zero_add 0)) = 0 := by
  -- Route correction: reduce the public `Ext⁰` statement to the concrete `mk₀` computation.
  obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective y
  simpa using
    restricted_cover_boundary_kills_cover_image_mk₀
      (I := I) (M := M) (N := N) (π := π) (c0 := c0) (m := m)
      κ hκ hstage f

/-- Helper for Lemma 15.102.2: every class in the kernel of the original cover boundary also lies
in the kernel of the lifted stage boundary. -/
theorem restricted_cover_boundary_ker_le
    {F : Mod} (π : F ⟶ M)
    [Module.Finite A (LinearMap.ker π.hom)] (c0 m : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact) :
    LinearMap.ker (hπ.extClass.precompOfLinear A N (Nat.add_zero 1)) ≤
      LinearMap.ker
        (restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage) := by
  let βm :=
    restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage
  intro z hz
  have hz' : (hπ.extClass.precompOfLinear A N (Nat.add_zero 1)) z = 0 := by
    simpa using hz
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hπ N z (Nat.add_zero 1) hz'
  -- Exactness identifies `z` with a cover-image class, and the previous lemma kills that image.
  calc
    βm z = βm ((Ext.mk₀ (ModuleCat.ofHom (LinearMap.ker π.hom).subtype)).comp y (zero_add 0)) := by
      rw [← hy]
    _ = 0 := by
      exact restricted_cover_boundary_kills_cover_image
        (I := I) (M := M) (N := N) (π := π) (c0 := c0) (m := m)
        κ hκ hstage y

/-- Helper for Lemma 15.102.2: a fixed finite free cover and its Artin-Rees shift give the
degree-`1` factorization through `Ext¹_A(I^[c₀ + m] M, I^[m] N)`. -/
theorem exists_ext_one_factorization_from_cover
    {F : Mod} (π : F ⟶ M) (hFproj : CategoryTheory.Projective F)
    [Module.Finite A (LinearMap.ker π.hom)] (c0 : ℕ)
    (hc0 :
      ∀ m : ℕ,
        ∃ κ :
          ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
            idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)),
          (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
            (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom ∧
          (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact) :
    ∀ m : ℕ,
      ∃ φ : Ext M N 1 →ₗ[A] Ext (idealPowerStage I (c0 + m) M) (idealPowerStage I m N) 1,
        ∀ x : Ext M N 1,
          idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1 (φ x) =
            idealPowerSubtypeExtPrecomp I (c0 + m) M N 1 x := by
  let K : Mod := ModuleCat.of A (LinearMap.ker π.hom)
  intro m
  rcases hc0 m with ⟨κ, hκ, hstage⟩
  let δ :
      Ext K N 0 →ₗ[A] Ext M N 1 :=
    hπ.extClass.precompOfLinear A N (Nat.add_zero 1)
  let βm :
      Ext K N 0 →ₗ[A] Ext (idealPowerStage I (c0 + m) M) (idealPowerStage I m N) 1 :=
    restricted_cover_boundary_lift (I := I) (M := M) (N := N) π c0 m κ hstage
  have hsurj :
      Function.Surjective δ := by
    -- The fixed free cover identifies `Ext¹(M, N)` with the quotient of `Ext⁰(K, N)`.
    exact cover_boundary_surjective_ext_one (A := A) (M := M) (N := N) π hFproj hπ
  have hker :
      LinearMap.ker δ ≤ LinearMap.ker βm := by
    -- Descend the stage boundary through the quotient by the kernel of `δ`.
    exact restricted_cover_boundary_ker_le
      (I := I) (M := M) (N := N) (π := π) c0 m κ hκ hstage hπ
  let βbar :
      Ext K N 0 ⧸ LinearMap.ker δ →ₗ[A]
        Ext (idealPowerStage I (c0 + m) M) (idealPowerStage I m N) 1 :=
    (LinearMap.ker δ).liftQ βm hker
  let eδ : (Ext K N 0 ⧸ LinearMap.ker δ) ≃ₗ[A] Ext M N 1 :=
    δ.quotKerEquivOfSurjective hsurj
  refine ⟨βbar ∘ₗ eδ.symm.toLinearMap, ?_⟩
  intro x
  rcases hsurj x with ⟨z, rfl⟩
  have heδ :
      eδ.symm (δ z) = Submodule.Quotient.mk z := by
    -- The quotient equivalence sends the class of `z` back to the chosen representative.
    simpa [eδ] using (LinearMap.quotKerEquivOfSurjective_symm_apply (f := δ) hsurj z)
  -- Evaluate the descended map on the quotient representative `z`.
  calc
    idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1
        ((βbar ∘ₗ eδ.symm.toLinearMap) (δ z))
      =
        idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1
          (βbar (eδ.symm (δ z))) := by
            rfl
    _ =
        idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1
          (βbar (Submodule.Quotient.mk z)) := by
            rw [heδ]
    _ =
        idealPowerSubtypeExtPostcomp I m (idealPowerStage I (c0 + m) M) N 1 (βm z) := by
          rw [Submodule.liftQ_apply]
    _ = idealPowerSubtypeExtPrecomp I (c0 + m) M N 1 (δ z) := by
          exact restricted_cover_boundary_factorization
            (I := I) (M := M) (N := N) (π := π) (c0 := c0) (m := m)
            κ hκ hstage hπ z

/-- Helper for Lemma 15.102.2: the stage index `c + (n - c)` rewrites back to `n` whenever
`c ≤ n`. -/
theorem idealPowerStage_add_sub_eq
    (c n : ℕ) (h : c ≤ n) :
    idealPowerStage I (c + (n - c)) M = idealPowerStage I n M := by
  simp [Nat.add_sub_of_le h]

/-- Helper for Lemma 15.102.2: a degree-`1` factorization can be reindexed along an equality of
target-stage indices. -/
theorem exists_ext_one_factorization_target_reindex
    (u s t : ℕ) (hst : s = t) :
    (∃ φ : Ext M N 1 →ₗ[A] Ext (idealPowerStage I u M) (idealPowerStage I s N) 1,
      ∀ x : Ext M N 1,
        idealPowerSubtypeExtPostcomp I s (idealPowerStage I u M) N 1 (φ x) =
          idealPowerSubtypeExtPrecomp I u M N 1 x) →
    (∃ φ : Ext M N 1 →ₗ[A] Ext (idealPowerStage I u M) (idealPowerStage I t N) 1,
      ∀ x : Ext M N 1,
        idealPowerSubtypeExtPostcomp I t (idealPowerStage I u M) N 1 (φ x) =
          idealPowerSubtypeExtPrecomp I u M N 1 x) := by
  -- After replacing the target-stage index by an equal one, the factorization statement is
  -- literally unchanged.
  subst hst
  intro hφ
  simpa using hφ

/-- Helper for Lemma 15.102.2: once the Artin-Rees shift `c₀` is fixed for a free cover,
the degree-`1` factorization can be repackaged for any stage `n ≥ c₀` by writing
`n = c₀ + (n - c₀)`. -/
theorem exists_ext_one_factorization_at_ge_shift
    {F : Mod} (π : F ⟶ M) (hFproj : CategoryTheory.Projective F)
    [Module.Finite A (LinearMap.ker π.hom)] (c0 : ℕ)
    (hc0 :
      ∀ m : ℕ,
        ∃ κ :
          ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
            idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)),
          (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
            (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom ∧
          (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact)
    (n : ℕ) (hn : c0 ≤ n) :
    let Mn := idealPowerStage I n M
    let Nn := idealPowerStage I (n - c0) N
    ∃ φ : Ext M N 1 →ₗ[A] Ext Mn Nn 1,
      ∀ x : Ext M N 1,
        idealPowerSubtypeExtPostcomp I (n - c0) Mn N 1 (φ x) =
          idealPowerSubtypeExtPrecomp I n M N 1 x := by
  let m := n - c0
  have hn' : n = c0 + m := by
    -- Rewrite the target stage index into the cover theorem's `c₀ + m` form.
    subst m
    exact (Nat.add_sub_of_le hn).symm
  have hm : m = (c0 + m) - c0 := by
    simp
  rw [hn']
  -- First reuse the stage-`m` factorization, then transport the target-stage index by `hm`.
  exact
    exists_ext_one_factorization_target_reindex
      (I := I) (M := M) (N := N) (u := c0 + m) (s := m) (t := (c0 + m) - c0) hm
      (exists_ext_one_factorization_from_cover
        (I := I) (M := M) (N := N) (π := π) hFproj c0 hc0 hπ m)

/-- Helper for Lemma 15.102.2: a factorization in degree `q + 1` for the kernel of a free cover
pushes forward to a factorization in degree `q + 2` for the quotient module by composing with the
restricted stage boundary and the usual dimension-shift equivalence. -/
theorem exists_ext_succ_factorization_from_cover
    {F : Mod} (π : F ⟶ M) (hFproj : CategoryTheory.Projective F)
    [Module.Finite A (LinearMap.ker π.hom)] (c0 c1 m q : ℕ)
    (κ :
      ModuleCat.of A (LinearMap.ker (idealPowerSubmoduleMap I π.hom (c0 + m))) ⟶
        idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
    (hκ :
      (idealPowerSubtype I m (ModuleCat.of A (LinearMap.ker π.hom))).comp κ.hom =
        (stageKernelToKernel (I := I) (π := π) (n := c0 + m)).hom)
    (hstage :
      (LinearMap.shortComplexKer (idealPowerSubmoduleMap I π.hom (c0 + m))).ShortExact)
    (hπ : (LinearMap.shortComplexKer π.hom).ShortExact)
    (φK :
      Ext (ModuleCat.of A (LinearMap.ker π.hom)) N (q + 1) →ₗ[A]
        Ext (idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom)))
          (idealPowerStage I (m - c1) N) (q + 1))
    (hφK :
      ∀ y : Ext (ModuleCat.of A (LinearMap.ker π.hom)) N (q + 1),
        idealPowerSubtypeExtPostcomp I (m - c1)
            (idealPowerStage I m (ModuleCat.of A (LinearMap.ker π.hom))) N (q + 1) (φK y) =
          idealPowerSubtypeExtPrecomp I m (ModuleCat.of A (LinearMap.ker π.hom)) N (q + 1) y) :
    ∃ φ : Ext M N (q + 2) →ₗ[A]
        Ext (idealPowerStage I (c0 + m) M) (idealPowerStage I (m - c1) N) (q + 2),
      ∀ x : Ext M N (q + 2),
        idealPowerSubtypeExtPostcomp I (m - c1)
            (idealPowerStage I (c0 + m) M) N (q + 2) (φ x) =
          idealPowerSubtypeExtPrecomp I (c0 + m) M N (q + 2) x := by
  -- TODO: combine the kernel-side factorization `φK` with the restricted boundary map and then
  -- use `restricted_cover_extClass_naturality` together with `cover_boundary_linearEquiv_ext_succ`.
  sorry

/-- Helper for Lemma 15.102.2: every finite source module satisfies the positive-degree stage
factorization statement, proved by induction on the Ext degree. -/
theorem exists_ext_factorization_positive_degree_of_finite_source
    (X : Mod) [Module.Finite A X] :
    ∀ p : ℕ, 0 < p →
      ∃ c : ℕ, ∀ n ≥ c,
        let Xn := idealPowerStage I n X
        let Nn := idealPowerStage I (n - c) N
        ∃ φ : Ext X N p →ₗ[A] Ext Xn Nn p,
          ∀ x : Ext X N p,
            idealPowerSubtypeExtPostcomp I (n - c) Xn N p (φ x) =
              idealPowerSubtypeExtPrecomp I n X N p x := by
  -- TODO: run the source-faithful induction on the Ext degree: degree `1` via
  -- `exists_ext_one_factorization_at_ge_shift`, and the successor step via
  -- `exists_ext_succ_factorization_from_cover`.
  sorry

-- Route correction: the positive-degree factorization is not a formal consequence of Ext
-- functoriality. The stagewise restriction operator above is the chain-level input, and the
-- remaining work is to transport it through a finite free/projective resolution and the
-- Artin-Rees comparison from Lemma `15.102.1`.

-- Proof sketch: the source lemma is the positive-degree statement. In degree `0`, the
-- restriction map already factors with `c = 0` by viewing a morphism `M ⟶ N` as a morphism
-- `I^n M ⟶ I^n N`. For `p > 0`, apply Artin-Rees to a finite presentation of `M` to obtain a
-- uniform constant `c`; for each `n ≥ c`, the induced map on a free resolution of `I^n M` lands
-- in `I^(n - c) N`, which yields the required factorization on `Ext^p` by induction on `p`.
/-- Lemma 15.102.2: for every degree `p > 0`, the canonical `A`-linear restriction map
`Ext^p_A(M, N) → Ext^p_A(I^n M, N)` factors for large `n` through some `A`-linear map
`Ext^p_A(M, N) → Ext^p_A(I^n M, I^(n - c) N)`, whose postcomposition with the canonical map
`Ext^p_A(I^n M, I^(n - c) N) → Ext^p_A(I^n M, N)` induced by `I^(n - c) N ↪ N` recovers the
restriction map. -/
@[stacks 0G3L]
theorem exists_ext_factorization_through_ideal_power_target (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      let Mn := idealPowerStage I n M
      let Nn := idealPowerStage I (n - c) N
      ∃ φ :
        Ext M N p →ₗ[A] Ext Mn Nn p,
        ∀ x : Ext M N p,
          idealPowerSubtypeExtPostcomp I (n - c) Mn N p (φ x) =
            idealPowerSubtypeExtPrecomp I n M N p x :=
  by
    -- Route correction: the final theorem now delegates to the degree induction over arbitrary
    -- finite source modules, whose base step is the degree-`1` cover descent and whose successor
    -- step is the boundary transport through the same fixed cover.
    exact exists_ext_factorization_positive_degree_of_finite_source
      (I := I) (N := N) M p hp

end
