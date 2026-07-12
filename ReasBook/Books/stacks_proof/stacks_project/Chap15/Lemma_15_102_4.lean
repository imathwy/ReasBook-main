import Mathlib
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_65_3
import StacksProject_2024.Chap15.Lemma_15_66_1
import StacksProject_2024.Chap15.Lemma_15_102_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

open scoped IdealPowerSubmodule

local notation "Cpx" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "singleCpx₀" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "Q" => DerivedCategory.Q

/-- Helper for Lemma 15.102.4: a pseudo-coherent derived object admits a bounded-above
termwise finite free `ProjectiveMinus` representative with an actual isomorphism to the target
derived object. -/
private theorem exists_projectiveMinus_finiteFree_iso_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.ProjectiveMinus (ModuleCat A),
      (∀ i : ℤ, Module.Free A ((P : Cpx).X i)) ∧
      (∀ i : ℤ, Module.Finite A ((P : Cpx).X i)) ∧
      Nonempty (DerivedCategory.Q.obj (P : Cpx) ≅ K) := by
  rcases hK with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat A) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat A) E).2 ⟨b, hEb⟩⟩,
      fun i ↦ by
        letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
        exact inferInstance⟩
  refine ⟨P, ?_, ?_, ⟨asIso α⟩⟩
  · intro i
    -- Proof comment: the packaged `ProjectiveMinus` complex uses the original finite free
    -- representative termwise, so freeness is inherited degreewise.
    simpa [P] using
      (show Module.Free A (E.X i) by
        letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
        infer_instance)
  · intro i
    -- Proof comment: the same packaging preserves the finite generation needed later for the
    -- Artin-Rees argument on the three-term Hom row.
    simpa [P] using
      (show Module.Finite A (E.X i) by
        letI : CochainComplex.IsTermwiseFiniteFree E := hEfree
        infer_instance)

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

open scoped IdealPowerSubmodule

local notation "Cpx" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
variable (K : DMod) (p : ℤ)
local notation "Extp" => derivedExtModuleFunctor K p

/-- Helper for Lemma 15.102.4: precomposition with a morphism acts linearly on represented Hom
modules. -/
private noncomputable def represented_hom_precompose
    {X Y N : ModuleCat A} (u : X ⟶ Y) :
    ModuleCat.of A (Y →ₗ[A] N) ⟶ ModuleCat.of A (X →ₗ[A] N) :=
  ModuleCat.ofHom (LinearMap.lcomp A N u.hom)

/-- Helper for Lemma 15.102.4: postcomposition with a module morphism acts linearly on
represented Hom modules. -/
private noncomputable def represented_hom_postcompose
    {X M N : ModuleCat A} (f : M ⟶ N) :
    ModuleCat.of A (X →ₗ[A] M) ⟶ ModuleCat.of A (X →ₗ[A] N) :=
  ModuleCat.ofHom (LinearMap.compRight A f.hom)

/-- Helper for Lemma 15.102.4: the explicit represented-Hom row attached to the chosen
projective-minus complex still has zero composite. -/
private theorem represented_hom_row_zero
    (P : CochainComplex.ProjectiveMinus (ModuleCat A))
    (N : ModuleCat A) (p : ℤ) :
    represented_hom_precompose
        (A := A) (N := N) ((P : Cpx).d (-p) (-p + 1)) ≫
      represented_hom_precompose
        (A := A) (N := N) ((P : Cpx).d (-p - 1) (-p)) =
        0 := by
  -- Proof comment: composing the two represented-Hom differentials is precomposition by
  -- `d ≫ d`, which vanishes by the cochain-complex identity.
  ext g x
  change g ((((P : Cpx).d (-p - 1) (-p) ≫ (P : Cpx).d (-p) (-p + 1)).hom) x) = 0
  rw [(P : Cpx).d_comp_d (-p - 1) (-p) (-p + 1)]
  simp

/-- Helper for Lemma 15.102.4: the source proof uses the represented-Hom row obtained from the
three terms around degree `p` of the chosen projective-minus complex. -/
private abbrev represented_hom_row
    (P : CochainComplex.ProjectiveMinus (ModuleCat A))
    (N : ModuleCat A) (p : ℤ) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (represented_hom_precompose (A := A) ((P : Cpx).d (-p) (-p + 1)))
    (represented_hom_precompose (A := A) ((P : Cpx).d (-p - 1) (-p)))
    (represented_hom_row_zero (A := A) P N p)

/-- Helper for Lemma 15.102.4: precomposition in the source variable commutes with
postcomposition in the module variable on represented Hom modules. -/
private theorem represented_hom_precompose_comp_postcompose
    {X Y M N : ModuleCat A} (u : X ⟶ Y) (f : M ⟶ N) :
    represented_hom_precompose (A := A) (N := M) u ≫
        represented_hom_postcompose (A := A) (X := X) f =
      represented_hom_postcompose (A := A) (X := Y) f ≫
        represented_hom_precompose (A := A) (N := N) u := by
  -- Proof comment: both composites send `g : Y ⟶ M` to the same map `x ↦ f (g (u x))`.
  apply ModuleCat.hom_ext
  ext g x
  rfl

/-- Helper for Lemma 15.102.4: a module morphism `N ⟶ N'` induces the expected morphism between
the represented-Hom rows by postcomposition on each term. -/
private noncomputable def represented_hom_row_map
    (P : CochainComplex.ProjectiveMinus (ModuleCat A))
    {N N' : ModuleCat A} (f : N ⟶ N') (p : ℤ) :
    represented_hom_row (A := A) P N p ⟶ represented_hom_row (A := A) P N' p :=
  -- Proof comment: the three termwise postcomposition maps form a short-complex morphism because
  -- precomposition by each differential commutes with postcomposition by `f`.
  ShortComplex.homMk
    (represented_hom_postcompose (A := A) (X := (P : Cpx).X (-p + 1)) f)
    (represented_hom_postcompose (A := A) (X := (P : Cpx).X (-p)) f)
    (represented_hom_postcompose (A := A) (X := (P : Cpx).X (-p - 1)) f)
    (represented_hom_precompose_comp_postcompose
      (A := A) ((P : Cpx).d (-p) (-p + 1)) f)
    (represented_hom_precompose_comp_postcompose
      (A := A) ((P : Cpx).d (-p - 1) (-p)) f)

/-- Helper for Lemma 15.102.4: forgetting the ideal-power stage after restricting a linear map is
the same as first forgetting the source stage and then applying the ambient map. -/
private theorem idealPowerSubmoduleMap_comp_subtype
    {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (I : Ideal A) (f : X →ₗ[A] Y) (n : ℕ) :
    (idealPowerSubtype I n Y).comp (idealPowerSubmoduleMap I f n) =
      f.comp (idealPowerSubtype I n X) := by
  -- Proof comment: `idealPowerSubmoduleMap` is literally `f` restricted to the stage submodule,
  -- so forgetting the stage on either side leaves the same ambient value.
  rfl

/-- Helper for Lemma 15.102.4: the previous linear identity remains valid after packaging the
linear maps as morphisms in `ModuleCat`. -/
private theorem idealPowerSubmoduleMap_comp_subtype_hom
    {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (I : Ideal A) (f : X →ₗ[A] Y) (n : ℕ) :
    ModuleCat.ofHom (idealPowerSubmoduleMap I f n) ≫
        ModuleCat.ofHom (idealPowerSubtype I n Y) =
      ModuleCat.ofHom (idealPowerSubtype I n X) ≫
        ModuleCat.ofHom f := by
  -- Proof comment: `ModuleCat.ofHom` preserves composition literally, so the linear statement
  -- upgrades by a direct rewrite.
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Helper for Lemma 15.102.4: for a finite family, pointwise membership in `I^[n] M` implies
membership in the ideal-power submodule of the whole product module. -/
private theorem pi_mem_idealPower_of_forall
    (I : Ideal A) (n : ℕ) {ι : Type u} [Finite ι] [DecidableEq ι]
    {M : Type u} [AddCommGroup M] [Module A M]
    (x : ι → M) (hx : ∀ i, x i ∈ I^[n] M) :
    x ∈ I^[n] (ι → M) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hsingle : ∀ i, Pi.single i (x i) ∈ I^[n] (ι → M) := by
    intro i
    let xi : I^[n] M := ⟨x i, hx i⟩
    -- Proof comment: each supported coordinate vector comes from the canonical linear map
    -- `M → ι → M`, hence lies in the ideal-power stage after applying `idealPowerSubmoduleMap`.
    simpa using
      (idealPowerSubmoduleMap I (LinearMap.single A (fun _ : ι ↦ M) i) n xi).2
  have hsum :
      ∑ i, Pi.single i (x i) ∈ I^[n] (ι → M) := by
    -- Proof comment: the ideal-power stage is a submodule, so it is closed under the finite sum
    -- of the supported coordinate vectors.
    exact Submodule.sum_mem _ fun i _ ↦ hsingle i
  have hxsum : (∑ i, Pi.single i (x i)) = x := by
    -- Proof comment: a finite tuple is the sum of its supported coordinate vectors.
    ext i
    simp
  simpa [hxsum] using hsum

/-- Helper for Lemma 15.102.4: a finite family of elements of `I^[n] M` defines an element of the
ambient ideal-power stage `I^[n] (ι → M)` by forgetting the pointwise stage proofs. -/
private noncomputable def pi_to_idealPowerStageLinear
    (I : Ideal A) (n : ℕ) (ι : Type u) [Finite ι] [DecidableEq ι]
    (M : ModuleCat A) :
    (ι → idealPowerStage I n M) →ₗ[A] I^[n] (ModuleCat.of A (ι → M)) :=
  { toFun := fun v ↦
      ⟨fun i ↦ (idealPowerSubtype I n M) (v i),
        pi_mem_idealPower_of_forall (A := A) I n
          (fun i ↦ (idealPowerSubtype I n M) (v i)) fun i ↦ (v i).2⟩
    map_add' := by
      -- Proof comment: addition is coordinatewise on the finite family.
      intro v w
      ext i
      rfl
    map_smul' := by
      -- Proof comment: scalar multiplication is likewise coordinatewise.
      intro a v
      ext i
      rfl }

/-- Helper for Lemma 15.102.4: for a finite free source `F`, the source-proof inclusion
`Hom_A(F, I^[n] M) ⟶ I^[n] Hom_A(F, M)` is obtained by choosing a basis of `F`, moving to
coordinates, and then transporting the pointwise ideal-power inclusion back. -/
private noncomputable def finite_free_hom_to_idealPower_stage
    (I : Ideal A) (n : ℕ) (F M : ModuleCat A)
    [Module.Free A F] [Module.Finite A F] :
    ModuleCat.of A (F →ₗ[A] idealPowerStage I n M) ⟶
      idealPowerStage I n (ModuleCat.of A (F →ₗ[A] M)) :=
  let ι := Module.Free.ChooseBasisIndex A F
  let b : Module.Basis ι A F := Module.Free.chooseBasis A F
  let _ : Finite ι := inferInstance
  let _ : DecidableEq ι := Classical.decEq ι
  ModuleCat.ofHom <|
    (idealPowerSubmoduleMap I
        ((b.constr A : (ι → M) ≃ₗ[A] (F →ₗ[A] M)).toLinearMap) n).comp <|
      (pi_to_idealPowerStageLinear (A := A) I n ι M).comp <|
        ((b.constr A : (ι → idealPowerStage I n M) ≃ₗ[A]
            (F →ₗ[A] idealPowerStage I n M)).symm.toLinearMap)

/-- Helper for Lemma 15.102.4: evaluating the finite-free comparison map on a chosen basis vector
recovers ordinary postcomposition by the stage inclusion. -/
private theorem finite_free_hom_to_idealPower_stage_apply_basis
    (I : Ideal A) (n : ℕ) (F M : ModuleCat A)
    [Module.Free A F] [Module.Finite A F] :
    let ι := Module.Free.ChooseBasisIndex A F
    let b : Module.Basis ι A F := Module.Free.chooseBasis A F
    let _ : Finite ι := inferInstance
    let _ : DecidableEq ι := Classical.decEq ι
    ∀ (g : F →ₗ[A] idealPowerStage I n M) (i : ι),
      ((finite_free_hom_to_idealPower_stage (A := A) I n F M ≫
          ModuleCat.ofHom (idealPowerSubtype I n (ModuleCat.of A (F →ₗ[A] M)))).hom g)
        (b i) =
        (idealPowerSubtype I n M) (g (b i)) := by
  classical
  intro ι b _ _
  intro g i
  have hcoords :
      (((b.constr A : (ι → idealPowerStage I n M) ≃ₗ[A] (F →ₗ[A] idealPowerStage I n M)).symm)
          g) i =
        g (b i) := by
    -- Proof comment: the inverse coordinate map records the values of `g` on the chosen basis.
    simpa using
      (Module.Basis.constr_basis
        (b := b) (S := A)
        (((b.constr A : (ι → idealPowerStage I n M) ≃ₗ[A]
            (F →ₗ[A] idealPowerStage I n M)).symm g)) i).symm
  -- Proof comment: after evaluating on `b i`, the outer basis transport collapses and only the
  -- stage inclusion applied to `g (b i)` remains.
  dsimp [finite_free_hom_to_idealPower_stage]
  change
    ((b.constr A : (ι → M) ≃ₗ[A] (F →ₗ[A] M))
        (fun j ↦
          (idealPowerSubtype I n M)
            (((b.constr A : (ι → idealPowerStage I n M) ≃ₗ[A]
                (F →ₗ[A] idealPowerStage I n M)).symm g) j)))
      (b i) =
      (idealPowerSubtype I n M) (g (b i))
  rw [Module.Basis.constr_basis]
  simpa [hcoords]

/-- Helper for Lemma 15.102.4: after forgetting the target stage, the finite-free comparison map
is exactly the obvious postcomposition by `I^[n] M ↪ M`. -/
private theorem finite_free_hom_to_idealPower_stage_comp_subtype
    (I : Ideal A) (n : ℕ) (F M : ModuleCat A)
    [Module.Free A F] [Module.Finite A F] :
    finite_free_hom_to_idealPower_stage (A := A) I n F M ≫
        ModuleCat.ofHom (idealPowerSubtype I n (ModuleCat.of A (F →ₗ[A] M))) =
      represented_hom_postcompose (A := A) (X := F) ((idealPowerSubtypeNatTrans I n).app M) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A F
  let b : Module.Basis ι A F := Module.Free.chooseBasis A F
  let _ : Finite ι := inferInstance
  let _ : DecidableEq ι := Classical.decEq ι
  apply ModuleCat.hom_ext
  ext g x
  -- Proof comment: expand `x` in the chosen basis and compare the two resulting finite sums
  -- termwise using the basis-vector computation proved just above.
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using congrArg (fun y : M ↦ (b.repr x) i • y)
    (finite_free_hom_to_idealPower_stage_apply_basis (A := A) I n F M g i)

/-- Helper for Lemma 15.102.4: the finite-free comparison maps commute with precomposition in the
source variable, which is the compatibility needed to package the three termwise maps into the
represented-Hom row morphism. -/
private theorem finite_free_hom_to_idealPower_stage_precompose
    (I : Ideal A) (n : ℕ) {F₁ F₂ M : ModuleCat A}
    [Module.Free A F₁] [Module.Finite A F₁]
    [Module.Free A F₂] [Module.Finite A F₂]
    (u : F₁ ⟶ F₂) :
    represented_hom_precompose (A := A) (N := idealPowerStage I n M) u ≫
        finite_free_hom_to_idealPower_stage (A := A) I n F₁ M =
      finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
        ModuleCat.ofHom
          (idealPowerSubmoduleMap I
            (represented_hom_precompose (A := A) (N := M) u).hom n) := by
  let j :=
    ModuleCat.ofHom (idealPowerSubtype I n (ModuleCat.of A (F₁ →ₗ[A] M)))
  let j₂ :=
    ModuleCat.ofHom (idealPowerSubtype I n (ModuleCat.of A (F₂ →ₗ[A] M)))
  letI : Mono j :=
    (ModuleCat.mono_iff_injective _).2 fun x y hxy ↦ Subtype.ext hxy
  -- Proof comment: both candidate maps become the same after forgetting the target ideal-power
  -- stage inside `Hom_A(F₁, M)`.
  have hcomp :
      (represented_hom_precompose (A := A) (N := idealPowerStage I n M) u ≫
          finite_free_hom_to_idealPower_stage (A := A) I n F₁ M) ≫ j =
        (finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
            ModuleCat.ofHom
              (idealPowerSubmoduleMap I
                (represented_hom_precompose (A := A) (N := M) u).hom n)) ≫
          j := by
    -- Proof comment: after postcomposing with the subtype, the left side is ordinary
    -- postcomposition by `I^[n] M ↪ M`, while the right side is the same map rewritten through
    -- the restricted target stage map.
    have hleft :
        (represented_hom_precompose (A := A) (N := idealPowerStage I n M) u ≫
              finite_free_hom_to_idealPower_stage (A := A) I n F₁ M) ≫
            j =
          represented_hom_precompose (A := A) (N := idealPowerStage I n M) u ≫
            represented_hom_postcompose (A := A) (X := F₁)
              ((idealPowerSubtypeNatTrans I n).app M) := by
      rw [Category.assoc]
      rw [finite_free_hom_to_idealPower_stage_comp_subtype]
      rfl
    have hmiddle :
        represented_hom_precompose (A := A) (N := idealPowerStage I n M) u ≫
            represented_hom_postcompose (A := A) (X := F₁)
              ((idealPowerSubtypeNatTrans I n).app M) =
          represented_hom_postcompose (A := A) (X := F₂)
            ((idealPowerSubtypeNatTrans I n).app M) ≫
              represented_hom_precompose (A := A) (N := M) u := by
      apply ModuleCat.hom_ext
      ext g x
      rfl
    have hright :
        represented_hom_postcompose (A := A) (X := F₂)
            ((idealPowerSubtypeNatTrans I n).app M) ≫
              represented_hom_precompose (A := A) (N := M) u =
          (finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
              ModuleCat.ofHom
                (idealPowerSubmoduleMap I
                  (represented_hom_precompose (A := A) (N := M) u).hom n)) ≫
            j := by
      calc
        represented_hom_postcompose (A := A) (X := F₂)
            ((idealPowerSubtypeNatTrans I n).app M) ≫
              represented_hom_precompose (A := A) (N := M) u =
            (finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫ j₂) ≫
              represented_hom_precompose (A := A) (N := M) u := by
          rw [finite_free_hom_to_idealPower_stage_comp_subtype]
          rfl
        _ =
            finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
              (j₂ ≫ represented_hom_precompose (A := A) (N := M) u) := by
          simp [Category.assoc]
        _ =
            finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
              (ModuleCat.ofHom
                (idealPowerSubmoduleMap I
                  (represented_hom_precompose (A := A) (N := M) u).hom n) ≫
                j) := by
          simpa using
            congrArg
              (fun k ↦ finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫ k)
              ((idealPowerSubmoduleMap_comp_subtype_hom
                (A := A) I
                (represented_hom_precompose (A := A) (N := M) u).hom n).symm)
        _ =
            (finite_free_hom_to_idealPower_stage (A := A) I n F₂ M ≫
                ModuleCat.ofHom
                  (idealPowerSubmoduleMap I
                    (represented_hom_precompose (A := A) (N := M) u).hom n)) ≫
              j := by
          simp [Category.assoc]
    exact hleft.trans (hmiddle.trans hright)
  -- Proof comment: the subtype inclusion is monic, so equality after composing with it suffices.
  exact (cancel_mono j).1 hcomp

-- Proof sketch: choose a bounded-above complex of finite free `A`-modules representing `K`,
-- compute `Ext^p_A(K, -)` by the corresponding three-term `Hom` row, and apply
-- Lemma `15.102.1` to that finite row.
/-- Lemma 15.102.4: if `A` is Noetherian, `K ∈ D(A)` is pseudo-coherent, and `M` is a finite
`A`-module, then for every integer `p` there is a constant `c` such that for `n ≥ c` the image of
`Ext^p_A(K, I^[n] M) → Ext^p_A(K, M)` is contained in `I^[n - c] Ext^p_A(K, M)`. -/
@[stacks 0DYI]
theorem exists_derivedExt_image_le_idealPower_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (M : ModuleCat A) [Module.Finite A M]
    (p : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      LinearMap.range
          (((Extp).map ((idealPowerSubtypeNatTrans I n).app M)).hom) ≤
        I^[n - c] ((Extp).obj M) := by
  obtain ⟨P, hPfree, hPfinite, ⟨e⟩⟩ :=
    exists_projectiveMinus_finiteFree_iso_of_isPseudoCoherent (A := A) K hK
  -- Route correction: fix one finite-free `ProjectiveMinus` representative first and keep the
  -- proof on the source row `Hom_A(P^{-p+1}, -) → Hom_A(P^{-p}, -) → Hom_A(P^{-p-1}, -)`.
  let S := represented_hom_row (A := A) P M p
  -- The remaining source-faithful steps use this fixed represented-Hom row.
  -- TODO: package the now-proved termwise finite-free maps
  -- `Hom_A(P^{-q}, I^[n] M) → I^[n] Hom_A(P^{-q}, M)` and the compatibility theorem
  -- `finite_free_hom_to_idealPower_stage_precompose` into a short-complex morphism
  -- `represented_hom_row P (idealPowerStage I n M) p ⟶ S.idealPowerSubmoduleStageComplex I n`.
  -- Then apply Lemma `15.102.1` to obtain the row-level image containment in
  -- `I^[n - c] S.leftHomology`.
  -- TODO: after the row-level containment is isolated, build the explicit
  -- `HomComplex`/`toSingleEquiv` comparison that identifies `S.leftHomology` with
  -- `((derivedExtModuleFunctor K p).obj M)` and transports naturality of the restriction map.
  let _ := S
  let _ := hPfree
  let _ := hPfinite
  let _ := e
  sorry

end

end CategoryTheory
