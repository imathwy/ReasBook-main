import Mathlib
import StacksProject_2024.Chap15.Lemma_15_101_4
import StacksProject_2024.Chap15.Lemma_15_101_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open IadicFiniteModuleSystem

noncomputable section

universe u

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A

/- Domain-style sampling for Lemma 15.101.8:
- primary domain: `Ext` towers in the quotient category of `I`-adic finite module systems from
  Remark `15.101.6`;
- sampled owner declarations:
  `IadicFiniteModuleSystem`,
  `IadicFiniteModuleSystem.Category`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.isIso_iff_hasEventuallyBoundedKernelAndCokernel`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: the two `IadicFiniteModuleSystem` objects
    `extQuotientSystem I M N i` and `extReductionSystem I M N i`;
  `core/canonical`: the quotient-category owner from Remark `15.101.6`, together with the
    object-level proposition `CategoryTheory.IsIsomorphic`;
  `bridge/view`: the stagewise reduction `M / I^n M`, which is only implementation data for the
    reduction-side system and should not remain a second public owner;
- primitive data: the two source-facing Ext systems;
- derived API: the theorem that these systems are isomorphic in the category `\mathcal C`.

This item should therefore keep the systems themselves public, but record the comparison at the
canonical object-isomorphism layer rather than as a chosen concrete isomorphism. -/

/-- The reduction `M_n = M / I^n M`, viewed as a module over `A_n = A / I^n`. This is a private
bridge for the reduction-side system, not a second public owner. -/
private abbrev stagewiseReduction (I : Ideal A) (M : ModuleCat A) (n : ℕ+) :
    ModuleCat (stageRing A I n) :=
  ModuleCat.of (stageRing A I n) (M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A M)))

/-- Helper for Lemma 15.101.8: the `ℕ+`-indexed reduction stage is exactly the predecessor-indexed
ideal-power quotient used in Lemma `15.101.4`. -/
theorem stagewiseReduction_underlying_eq_idealPowerModuleQuotient
    (I : Ideal A) (M : ModuleCat A) (n : ℕ+) :
    (stagewiseReduction I M n : Type u) = idealPowerModuleQuotient I M n.natPred := by
  -- Both sides are the quotient by `I^n M`; the only difference is the `ℕ+` versus `ℕ` index.
  change M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A M)) =
      M ⧸ (I ^ (n.natPred + 1) • (⊤ : Submodule A M))
  rw [n.natPred_add_one]

/-- The inverse system whose `n`th stage is
`Ext^i_A(M, N) / I^n Ext^i_A(M, N)`, indexed by positive integers `n`. -/
abbrev extQuotientSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext M N i ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N i))))

/-- The inverse system whose `n`th stage is
`Ext^i_{A / I^n}(M / I^n M, N / I^n N)`, indexed by positive integers `n`. -/
abbrev extReductionSystem (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    [Module.Finite A N] (i : ℕ) : IadicFiniteModuleSystem A I :=
  fun n ↦ FGModuleCat.of (stageRing A I n)
    (Ext (stagewiseReduction I M n) (stagewiseReduction I N n) i)

/-- Helper for Lemma 15.101.8: under the canonical degree-zero identification
`Ext^0_A(M, N) ≃ Hom_A(M, N)`, the class `Ext.mk₀ f` corresponds to the original morphism `f`. -/
theorem ext_zero_linearEquiv_apply_mk₀
    (M N : ModuleCat A) (f : M ⟶ N) :
    (Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N)) (Ext.mk₀ f) = f := by
  -- The degree-zero `Ext` owner is literally `Hom`, and `Ext.mk₀` is the forward embedding.
  apply (Ext.linearEquiv₀.symm.injective)
  simpa [Ext.homEquiv₀_symm_apply]

/-- Helper for Lemma 15.101.8: at each reduced stage `A / I^n`, the class of a concrete reduced
map `f : M_n ⟶ N_n` in degree zero is identified with `f` itself. -/
theorem ext_zero_linearEquiv_apply_mk₀_stagewiseReduction
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+)
    (f : stagewiseReduction I M n ⟶ stagewiseReduction I N n) :
    (Ext.linearEquiv₀ :
        Ext (stagewiseReduction I M n) (stagewiseReduction I N n) 0 ≃ₗ[stageRing A I n]
          (stagewiseReduction I M n ⟶ stagewiseReduction I N n))
      (Ext.mk₀ f) = f := by
  -- This is the same degree-zero `Ext = Hom` computation after changing the ambient ring to
  -- `A / I^n`.
  apply (Ext.linearEquiv₀.symm.injective)
  simpa [Ext.homEquiv₀_symm_apply]

/-- Helper for Lemma 15.101.8: an `A`-linear equivalence between quotient-ring modules is
automatically linear over the quotient ring itself. -/
private theorem linearEquivOverQuotientOfRestrictScalars_map_smul
    (J : Ideal A) {M N : Type u}
    [AddCommGroup M] [Module (A ⧸ J) M] [Module A M] [IsScalarTower A (A ⧸ J) M]
    [AddCommGroup N] [Module (A ⧸ J) N] [Module A N] [IsScalarTower A (A ⧸ J) N]
    (e : M ≃ₗ[A] N) (a : A ⧸ J) (x : M) :
    e (a • x) = a • e x := by
  -- Reduce the quotient scalar to a representative in `A` and reuse `A`-linearity of `e`.
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hr : ((Ideal.Quotient.mk J) r : A ⧸ J) = r • (1 : A ⧸ J) := by
    change ((Ideal.Quotient.mk J) r : A ⧸ J) = ((Ideal.Quotient.mk J) r : A ⧸ J) * 1
    simpa using (mul_one ((Ideal.Quotient.mk J) r)).symm
  have hx : ((Ideal.Quotient.mk J) r : A ⧸ J) • x = r • x := by
    rw [hr]
    simpa [smul_assoc]
  have hy : ((Ideal.Quotient.mk J) r : A ⧸ J) • e x = r • e x := by
    rw [hr]
    simpa [smul_assoc]
  rw [hx, hy]
  simpa using e.map_smul r x

/-- Helper for Lemma 15.101.8: an `A`-linear equivalence between quotient-ring modules upgrades to
an equivalence over the quotient ring. -/
private noncomputable def linearEquivOverQuotientOfRestrictScalars
    (J : Ideal A) {M N : Type u}
    [AddCommGroup M] [Module (A ⧸ J) M] [Module A M] [IsScalarTower A (A ⧸ J) M]
    [AddCommGroup N] [Module (A ⧸ J) N] [Module A N] [IsScalarTower A (A ⧸ J) N]
    (e : M ≃ₗ[A] N) :
    M ≃ₗ[A ⧸ J] N :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquivOverQuotientOfRestrictScalars_map_smul (J := J) e }

/-- Helper for Lemma 15.101.8: quotienting by `J • ⊤` is functorial for an ambient linear
equivalence. -/
private noncomputable def quotientByIdealSmulTopLinearEquiv
    (J : Ideal A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) :
    (M ⧸ J • (⊤ : Submodule A M)) ≃ₗ[A] (N ⧸ J • (⊤ : Submodule A N)) :=
  let hForward :
      J • (⊤ : Submodule A M) ≤
        Submodule.comap e.toLinearMap (J • (⊤ : Submodule A N)) := by
    -- Transport visible `J`-multiples across `e`; linearity preserves the ideal-action shape.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e y ∈ (⊤ : Submodule A N) by simp))
  let hBackward :
      J • (⊤ : Submodule A N) ≤
        Submodule.comap e.symm.toLinearMap (J • (⊤ : Submodule A M)) := by
    -- The inverse equivalence gives the same quotient-transport statement in the reverse
    -- direction.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e.symm y ∈ (⊤ : Submodule A M) by simp))
  let f :
      (M ⧸ J • (⊤ : Submodule A M)) →ₗ[A] (N ⧸ J • (⊤ : Submodule A N)) :=
    Submodule.mapQ
      (J • (⊤ : Submodule A M))
      (J • (⊤ : Submodule A N))
      e.toLinearMap
      hForward
  let g :
      (N ⧸ J • (⊤ : Submodule A N)) →ₗ[A] (M ⧸ J • (⊤ : Submodule A M)) :=
    Submodule.mapQ
      (J • (⊤ : Submodule A N))
      (J • (⊤ : Submodule A M))
      e.symm.toLinearMap
      hBackward
  -- Compare both composites on quotient generators, where they reduce to the ambient inverse
  -- equalities for `e` and `e.symm`.
  LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      simpa [f, g] using
        congrArg (Submodule.Quotient.mk (p := J • (⊤ : Submodule A N)))
          (e.apply_symm_apply x))
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      simpa [f, g] using
        congrArg (Submodule.Quotient.mk (p := J • (⊤ : Submodule A M)))
          (e.symm_apply_apply x))

/-- Helper for Lemma 15.101.8: quotient transport along a linear equivalence sends a class to the
class of its image. -/
private theorem quotientByIdealSmulTopLinearEquiv_apply_mk
    (J : Ideal A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (x : M) :
    quotientByIdealSmulTopLinearEquiv (A := A) (J := J) e (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (e x) : N ⧸ J • (⊤ : Submodule A N)) := by
  -- The forward map is the quotient map induced by `e`, so it preserves visible representatives.
  rfl

/-- Helper for Lemma 15.101.8: the predecessor-indexed quotient `M / I^(n.pred+1) M` is exactly
the `ℕ+`-indexed quotient `M / I^n M`. -/
private theorem idealPowerModuleQuotient_natPred_eq_stage
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ+) :
    idealPowerModuleQuotient I M n.natPred = M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A M)) := by
  -- The two quotients only differ by rewriting `n.pred + 1` back to `n`.
  change M ⧸ (I ^ (n.natPred + 1) • (⊤ : Submodule A M)) = _
  rw [n.natPred_add_one]

/-- Helper for Lemma 15.101.8: the predecessor-indexed quotient stage from
Lemma `15.101.4` is canonically the same `A`-module as the `ℕ+`-indexed reduction stage. -/
private noncomputable abbrev stagewiseReduction_underlying_linearEquiv
    (I : Ideal A) (M : ModuleCat A) (n : ℕ+) :
    idealPowerModuleQuotient I M n.natPred ≃ₗ[A] stagewiseReduction I M n :=
  LinearEquiv.ofEq
    (stagewiseReduction_underlying_eq_idealPowerModuleQuotient (I := I) (M := M) (n := n)).symm

/-- Helper for Lemma 15.101.8: the actual degree-zero source stage `Ext^0_A(M,N) / I^n` is the
same quotient-Hom stage used by Lemma `15.101.4`. -/
private noncomputable abbrev ext_zero_quotient_stage_linearEquiv
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    extQuotientSystem I M N 0 n ≃ₗ[stageRing A I n] idealPowerModuleQuotient I (M ⟶ N) n.natPred :=
  let eA :
      (Ext M N 0 ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N 0)))) ≃ₗ[A]
        ((M ⟶ N) ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (M ⟶ N)))) :=
    quotientByIdealSmulTopLinearEquiv (A := A) (J := I ^ (n : ℕ))
      (Ext.linearEquiv₀ : Ext M N 0 ≃ₗ[A] (M ⟶ N))
  let eQ :
      (Ext M N 0 ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N 0)))) ≃ₗ[stageRing A I n]
        ((M ⟶ N) ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (M ⟶ N)))) :=
    linearEquivOverQuotientOfRestrictScalars (A := A) (J := I ^ (n : ℕ)) eA
  (LinearEquiv.ofEq
      (show (extQuotientSystem I M N 0 n : Type u) =
          Ext M N 0 ⧸ (I ^ (n : ℕ) • (⊤ : Submodule A (Ext M N 0))) from rfl)).trans
    (eQ.trans
      (LinearEquiv.ofEq
        (idealPowerModuleQuotient_natPred_eq_stage (I := I) (M := (M ⟶ N)) (n := n)).symm))

/-- Helper for Lemma 15.101.8: the source-side degree-zero adapter sends the class of `Ext.mk₀ f`
to the quotient class of `f`. -/
private theorem ext_zero_quotient_stage_linearEquiv_apply_mk₀
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N]
    (n : ℕ+) (f : M ⟶ N) :
    ext_zero_quotient_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
        (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n) =
      (Submodule.Quotient.mk f : idealPowerModuleQuotient I (M ⟶ N) n.natPred) := by
  -- Unfold the degree-zero source transport: it is just quotienting the `Ext^0 = Hom`
  -- equivalence.
  simpa [ext_zero_quotient_stage_linearEquiv, quotientByIdealSmulTopLinearEquiv_apply_mk,
    ext_zero_linearEquiv_apply_mk₀, idealPowerModuleQuotient_natPred_eq_stage]

/-- Helper for Lemma 15.101.8: the actual degree-zero reduction stage is already the concrete
reduced Hom group. -/
private noncomputable abbrev ext_zero_reduction_stage_linearEquiv
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    extReductionSystem I M N 0 n ≃ₗ[stageRing A I n]
      (stagewiseReduction I M n ⟶ stagewiseReduction I N n) :=
  (LinearEquiv.ofEq
      (show (extReductionSystem I M N 0 n : Type u) =
          Ext (stagewiseReduction I M n) (stagewiseReduction I N n) 0 from rfl)).trans
    (Ext.linearEquiv₀ :
      Ext (stagewiseReduction I M n) (stagewiseReduction I N n) 0 ≃ₗ[stageRing A I n]
        (stagewiseReduction I M n ⟶ stagewiseReduction I N n))

/-- Helper for Lemma 15.101.8: on the target side, the degree-zero adapter evaluates `Ext.mk₀`
to the underlying concrete reduced morphism. -/
private theorem ext_zero_reduction_stage_linearEquiv_apply_mk₀
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N]
    (n : ℕ+) (f : stagewiseReduction I M n ⟶ stagewiseReduction I N n) :
    ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
        (Ext.mk₀ f : extReductionSystem I M N 0 n) =
      f := by
  -- The target degree-zero stage is literally `Hom` over `A / I^n`.
  simpa [ext_zero_reduction_stage_linearEquiv] using
    ext_zero_linearEquiv_apply_mk₀_stagewiseReduction (A := A) (I := I) (M := M) (N := N) n f

/-- Helper for Lemma 15.101.8: any `A`-linear map into the quotient stage `N / I^n N` kills
`I^n M`, so it factors through the source quotient `M / I^n M`. -/
private theorem stagewise_reduction_hom_le_ker
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+)
    (f : M →ₗ[A] stagewiseReduction I N n) :
    I ^ (n : ℕ) • (⊤ : Submodule A M) ≤ LinearMap.ker f := by
  -- Every `I^n`-multiple maps to zero because the quotient codomain is annihilated by `I^n`.
  refine Submodule.smul_le.mpr ?_
  intro r hr m _hm
  change (r : A) • f m = 0
  refine Quotient.inductionOn' (f m) ?_
  intro y
  change (Submodule.Quotient.mk ((r : A) • y) : stagewiseReduction I N n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr (by simp)

/-- Helper for Lemma 15.101.8: an `A`-linear map `M → N / I^n N` descends uniquely to an
`A`-linear map `M / I^n M → N / I^n N`. -/
private noncomputable abbrev stagewise_reduction_hom_descend
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+)
    (f : M →ₗ[A] stagewiseReduction I N n) :
    stagewiseReduction I M n →ₗ[A] stagewiseReduction I N n :=
  (I ^ (n : ℕ) • (⊤ : Submodule A M)).liftQ f
    (stagewise_reduction_hom_le_ker (I := I) (M := M) (N := N) (n := n) f)

/-- Helper for Lemma 15.101.8: the descended quotient map is linear over the quotient ring
`A / I^n`, not just over `A`. -/
private theorem stagewise_reduction_hom_descend_map_smul
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+)
    (f : M →ₗ[A] stagewiseReduction I N n) :
    ∀ (c : stageRing A I n) (q : stagewiseReduction I M n),
      stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n) f (c • q) =
        c • stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n) f q := by
  intro c q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine Quotient.inductionOn' q ?_
  intro m
  have hmk :
      Ideal.Quotient.mk (I ^ (n : ℕ)) r • (Submodule.Quotient.mk m : stagewiseReduction I M n) =
        (Submodule.Quotient.mk (r • m) : stagewiseReduction I M n) := by
    simpa using
      (Module.Quotient.mk_smul_mk M (I ^ (n : ℕ) • (⊤ : Submodule A M)) r m :
        Ideal.Quotient.mk (I ^ (n : ℕ)) r •
            (Submodule.Quotient.mk m : M ⧸ I ^ (n : ℕ) • (⊤ : Submodule A M)) =
          (Submodule.Quotient.mk (r • m) :
            M ⧸ I ^ (n : ℕ) • (⊤ : Submodule A M)))
  -- Rewrite the quotient scalar action on a numerator representative and then use the original
  -- `A`-linearity of `f`.
  rw [hmk]
  calc
    stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n) f
        (Submodule.Quotient.mk (r • m) : stagewiseReduction I M n) =
      f (r • m) := by
          rfl
    _ = Ideal.Quotient.mk (I ^ (n : ℕ)) r • f m := by
          simpa [Algebra.smul_def] using (f.map_smul r m)
    _ = Ideal.Quotient.mk (I ^ (n : ℕ)) r •
        stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n) f
          (Submodule.Quotient.mk m : stagewiseReduction I M n) := by
          rfl

/-- Helper for Lemma 15.101.8: the model Hom stage `Hom_A(M, N / I^n N)` from
Lemma `15.101.4` canonically factors through the actual reduced-stage Hom group
`Hom_{A / I^n}(M / I^n M, N / I^n N)`. -/
private noncomputable def stagewise_reduction_hom_factorization_restrictScalars
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+) :
    homIdealPowerStage I M N n.natPred ≃ₗ[A]
      (stagewiseReduction I M n ⟶ stagewiseReduction I N n) := by
  let eN :
      idealPowerModuleQuotient I N n.natPred ≃ₗ[A] stagewiseReduction I N n :=
    stagewiseReduction_underlying_linearEquiv (I := I) (M := N) (n := n)
  let forward :
      homIdealPowerStage I M N n.natPred →ₗ[A]
        (stagewiseReduction I M n ⟶ stagewiseReduction I N n) :=
    { toFun := fun f ↦
        { toFun :=
            stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n)
              (eN.toLinearMap.comp f)
          map_add' :=
            (stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n)
              (eN.toLinearMap.comp f)).map_add
          map_smul' := stagewise_reduction_hom_descend_map_smul
            (I := I) (M := M) (N := N) (n := n) (eN.toLinearMap.comp f) }
      map_add' := by
        intro f g
        ext q
        refine Quotient.inductionOn' q ?_
        intro m
        rfl
      map_smul' := by
        intro a f
        ext q
        refine Quotient.inductionOn' q ?_
        intro m
        rfl }
  let backward :
      (stagewiseReduction I M n ⟶ stagewiseReduction I N n) →ₗ[A]
        homIdealPowerStage I M N n.natPred :=
    { toFun := fun g ↦
        eN.symm.toLinearMap.comp
          ((LinearMap.restrictScalars A g).comp
            (Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule A M))))
      map_add' := by
        intro g h
        ext m
        rfl
      map_smul' := by
        intro a g
        ext m
        rfl }
  -- The two constructions are inverse by evaluation on quotient numerators.
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · ext f m
    simp [forward, backward, stagewise_reduction_hom_descend, eN]
  · ext g q
    refine Quotient.inductionOn' q ?_
    intro m
    simp [forward, backward, stagewise_reduction_hom_descend, eN]

/-- Helper for Lemma 15.101.8: after restricting scalars from `A / I^n` to `A`, the model Hom
stage from Lemma `15.101.4` is canonically the actual reduced-stage Hom group. -/
theorem stagewise_reduction_hom_factorization
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+) :
    homIdealPowerStage I M N n.natPred ≃ₗ[stageRing A I n]
      (stagewiseReduction I M n ⟶ stagewiseReduction I N n) := by
  -- Promote the `A`-linear equivalence to quotient-linear form using the standard scalar bridge.
  exact linearEquivOverQuotientOfRestrictScalars (J := I ^ (n : ℕ))
    (stagewise_reduction_hom_factorization_restrictScalars
      (I := I) (M := M) (N := N) (n := n))

/-- Helper for Lemma 15.101.8: a concrete morphism `f : M ⟶ N` induces the expected map on the
reduced stages `M / I^n M ⟶ N / I^n N`. -/
private noncomputable abbrev stagewise_reduction_hom_descend_of_hom
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+) (f : M ⟶ N) :
    stagewiseReduction I M n ⟶ stagewiseReduction I N n :=
  { toFun :=
      stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n)
        ((Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule A N))).comp f)
    map_add' :=
      (stagewise_reduction_hom_descend (I := I) (M := M) (N := N) (n := n)
        ((Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule A N))).comp f)).map_add
    map_smul' :=
      stagewise_reduction_hom_descend_map_smul (I := I) (M := M) (N := N) (n := n)
        ((Submodule.mkQ (I ^ (n : ℕ) • (⊤ : Submodule A N))).comp f) }

/-- Helper for Lemma 15.101.8: the raw Hom comparison from Lemma `15.101.4` becomes the concrete
descended morphism on `M / I^n M ⟶ N / I^n N` before any degree-zero `Ext` transport. -/
private theorem stagewise_reduction_hom_factorization_homReductionLinearMap
    (I : Ideal A) (M N : ModuleCat A) (n : ℕ+) (f : M ⟶ N) :
    (stagewise_reduction_hom_factorization (I := I) (M := M) (N := N) (n := n))
        ((homReductionLinearMap I M N n.natPred) f) =
      stagewise_reduction_hom_descend_of_hom (I := I) (M := M) (N := N) (n := n) f := by
  -- Both sides are the same quotient-descended map; the left side first rewrites the target
  -- quotient stage through the predecessor-indexed model of Lemma `15.101.4`.
  ext q
  refine Quotient.inductionOn' q ?_
  intro m
  rfl

/-- Helper for Lemma 15.101.8: after transporting the degree-zero comparison to the actual Ext
systems, the stage map is the concrete reduced Hom comparison. -/
private noncomputable abbrev ext_zero_reduction_comparison_stageLinearMap
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    extQuotientSystem I M N 0 n →ₗ[stageRing A I n] extReductionSystem I M N 0 n :=
  (ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) (n := n)).symm.toLinearMap.comp
    (((stagewise_reduction_hom_factorization (A := A) (I := I) (M := M) (N := N) (n := n)).toLinearMap).comp
      ((homReductionComparison I M N n.natPred).comp
        (ext_zero_quotient_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) (n := n)).toLinearMap))

/-- Helper for Lemma 15.101.8: on `Ext.mk₀` generators, the transported degree-zero stage map
agrees with the concrete descended map `M / I^n M ⟶ N / I^n N`. -/
private theorem ext_zero_reduction_comparison_transport_apply_mk₀
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N]
    (n : ℕ+) (f : M ⟶ N) :
    ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
        (ext_zero_reduction_comparison_stageLinearMap
          (A := A) (I := I) (M := M) (N := N) n
          (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n)) =
      stagewise_reduction_hom_descend_of_hom (I := I) (M := M) (N := N) (n := n) f := by
  -- Route correction: once the source and target degree-zero stages are normalized explicitly,
  -- the comparison is a direct computation on `mk₀` generators.
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [LinearEquiv.apply_symm_apply]
  rw [ext_zero_quotient_stage_linearEquiv_apply_mk₀]
  exact stagewise_reduction_hom_factorization_homReductionLinearMap
    (A := A) (I := I) (M := M) (N := N) (n := n) f

/-- Helper for Lemma 15.101.8: at cutoff `0`, the source power submodule is the whole stage. -/
private theorem powerSubmodule_zero_eq_top
    (I : Ideal A) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    powerSubmodule 0 X n = ⊤ := by
  -- The zeroth power of the stage ideal is the unit ideal, so `I^0 E_n = E_n`.
  simp [powerSubmodule]

/-- Helper for Lemma 15.101.8: at cutoff `0`, the torsion submodule is trivial because `1` kills
only zero. -/
private theorem torsionSubmodule_zero_eq_bot
    (I : Ideal A) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    torsionSubmodule 0 X n = ⊥ := by
  -- Membership in the `I^0`-torsion submodule means being killed by every element of the whole
  -- ring, hence in particular by `1`.
  ext x
  constructor
  · intro hx
    rw [torsionSubmodule, Submodule.mem_torsionBySet_iff] at hx
    have h1 : (1 : stageRing A I n) ∈ stageIdeal A I n ^ 0 := by
      simp
    have hx1 := hx ⟨1, h1⟩
    simpa using hx1
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst hx
    rw [torsionSubmodule, Submodule.mem_torsionBySet_iff]
    intro a
    simp

/-- Helper for Lemma 15.101.8: cutoff `0` identifies the source power submodule with the ambient
stage module. -/
private noncomputable abbrev powerSubmodule_zero_linearEquiv
    (I : Ideal A) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    powerSubmodule 0 X n ≃ₗ[stageRing A I n] X n :=
  (LinearEquiv.ofEq _ _ (powerSubmodule_zero_eq_top (A := A) (I := I) (X := X) (n := n))).trans
    Submodule.topEquiv

/-- Helper for Lemma 15.101.8: quotienting by the cutoff-`0` torsion submodule does nothing. -/
private noncomputable abbrev torsionQuotient_zero_linearEquiv
    (I : Ideal A) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    torsionQuotient 0 X n ≃ₗ[stageRing A I n] X n :=
  Submodule.quotEquivOfEqBot (torsionSubmodule 0 X n)
    (torsionSubmodule_zero_eq_bot (A := A) (I := I) (X := X) (n := n))

/-- Helper for Lemma 15.101.8: a family of honest stage maps packages into a cutoff-`0`
representative. -/
private noncomputable def cutoff_zero_representative_of_stageLinearMap
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n) :
    HomRepresentative X Y :=
  { cutoff := 0
    map := fun n _ ↦
      (torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n).symm.toLinearMap.comp
        ((φ n).comp
          (powerSubmodule_zero_linearEquiv (A := A) (I := I) (X := X) n).toLinearMap) }

/-- Helper for Lemma 15.101.8: after the cutoff-`0` source and target identifications, the generic
representative evaluates to the original stage map. -/
private theorem cutoff_zero_representative_of_stageLinearMap_apply_symm
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n) (n : ℕ+) (x : X n) :
    torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n
      ((cutoff_zero_representative_of_stageLinearMap (A := A) (I := I) (X := X) (Y := Y) φ)
        n (Nat.zero_le _)
        ((powerSubmodule_zero_linearEquiv (A := A) (I := I) (X := X) n).symm x)) =
      φ n x := by
  -- Unfold the cutoff-`0` packaging once; the remaining simplification is cancellation of the
  -- source and target linear equivalences.
  simp [cutoff_zero_representative_of_stageLinearMap, LinearMap.comp_apply]

/-- Helper for Lemma 15.101.8: the cutoff-`0` source packaging does not change the stagewise
kernel. -/
private noncomputable def cutoff_zero_representative_kernel_linearEquiv
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n) (n : ℕ+) :
    LinearMap.ker
        (((cutoff_zero_representative_of_stageLinearMap
          (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _))) ≃ₗ[stageRing A I n]
      LinearMap.ker (φ n) := by
  let eX := powerSubmodule_zero_linearEquiv (A := A) (I := I) (X := X) n
  let eY := torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n
  let rep :=
    ((cutoff_zero_representative_of_stageLinearMap
      (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _))
  let forward :
      LinearMap.ker rep →ₗ[stageRing A I n] LinearMap.ker (φ n) := by
    refine
      { toFun := fun x ↦ ⟨eX x, ?_⟩
        map_add' := ?_
        map_smul' := ?_ }
    · -- Apply the target cutoff-`0` identification to the kernel equation and cancel the
      -- packaging equivalences.
      have hx := congrArg eY x.2
      simpa [rep, eX, eY, cutoff_zero_representative_of_stageLinearMap, LinearMap.comp_apply]
        using hx
    · intro x y
      ext
      rfl
    · intro a x
      ext
      rfl
  let backward :
      LinearMap.ker (φ n) →ₗ[stageRing A I n]
        LinearMap.ker rep := by
    refine
      { toFun := fun x ↦ ⟨eX.symm x, ?_⟩
        map_add' := ?_
        map_smul' := ?_ }
    · -- Push the packaged map forward through the target cutoff-`0` equivalence and use the
      -- given raw kernel condition.
      apply eY.symm.injective
      simpa [rep, eX, eY, cutoff_zero_representative_of_stageLinearMap, LinearMap.comp_apply]
        using x.2
    · intro x y
      ext
      rfl
    · intro a x
      ext
      rfl
  -- Both transports are inverse because the source cutoff-`0` equivalence is itself inverse to
  -- its symmetry.
  exact LinearEquiv.ofLinear forward backward
    (by
      intro x
      ext
      simp [forward, backward, eX])
    (by
      intro x
      ext
      simp [forward, backward, eX])

/-- Helper for Lemma 15.101.8: after removing the cutoff-`0` target packaging, the range is the
raw range of the original stage map. -/
private theorem cutoff_zero_representative_range_map_eq
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n) (n : ℕ+) :
    (LinearMap.range
        (((cutoff_zero_representative_of_stageLinearMap
          (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _)))).map
      (torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n).toLinearMap =
      LinearMap.range (φ n) := by
  let eX := powerSubmodule_zero_linearEquiv (A := A) (I := I) (X := X) n
  let eY := torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n
  let rep :=
    ((cutoff_zero_representative_of_stageLinearMap
      (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _))
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    refine ⟨eX x, ?_⟩
    simp [rep, eX, eY, cutoff_zero_representative_of_stageLinearMap, LinearMap.comp_apply]
  · rintro y ⟨x, rfl⟩
    refine ⟨rep (eX.symm x), ?_, ?_⟩
    · exact ⟨eX.symm x, rfl⟩
    · simpa [eY, rep] using
        cutoff_zero_representative_of_stageLinearMap_apply_symm
          (A := A) (I := I) (X := X) (Y := Y) φ n x

/-- Helper for Lemma 15.101.8: the cutoff-`0` target packaging does not change the stagewise
cokernel. -/
private noncomputable def cutoff_zero_representative_cokernel_linearEquiv
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n) (n : ℕ+) :
    (torsionQuotient 0 Y n ⧸
        LinearMap.range
          (((cutoff_zero_representative_of_stageLinearMap
            (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _)))) ≃ₗ[stageRing A I n]
      (Y n ⧸ LinearMap.range (φ n)) := by
  let rep :=
    ((cutoff_zero_representative_of_stageLinearMap
      (A := A) (I := I) (X := X) (Y := Y) φ) n (Nat.zero_le _))
  let eQuot :
      (torsionQuotient 0 Y n ⧸ LinearMap.range rep) ≃ₗ[stageRing A I n]
        (Y n ⧸
          (LinearMap.range rep).map
            (torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n).toLinearMap) :=
    quotientBySubmoduleLinearEquiv
      (torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n)
      (LinearMap.range rep)
  let eRange :
      (Y n ⧸
          (LinearMap.range rep).map
            (torsionQuotient_zero_linearEquiv (A := A) (I := I) (X := Y) n).toLinearMap) ≃ₗ[
              stageRing A I n] (Y n ⧸ LinearMap.range (φ n)) :=
    Submodule.quotEquivOfEq _ _
      (cutoff_zero_representative_range_map_eq
        (A := A) (I := I) (X := X) (Y := Y) φ n)
  -- First transport the quotient by range along the target cutoff-`0` equivalence, then rewrite
  -- the transported range to the raw one.
  exact eQuot.trans eRange

/-- Helper for Lemma 15.101.8: the normalized degree-zero comparison stage maps define an actual
cutoff-`0` representative between the Ext systems. -/
private noncomputable def ext_zero_reduction_comparison_representative
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] :
    HomRepresentative (extQuotientSystem I M N 0) (extReductionSystem I M N 0) :=
  cutoff_zero_representative_of_stageLinearMap (A := A) (I := I)
    (X := extQuotientSystem I M N 0) (Y := extReductionSystem I M N 0)
    (fun n ↦ ext_zero_reduction_comparison_stageLinearMap
      (A := A) (I := I) (M := M) (N := N) n)

/-- Helper for Lemma 15.101.8: on `Ext.mk₀` generators, the cutoff-`0` representative computes the
same reduced map as the normalized degree-zero stage comparison. -/
private theorem ext_zero_reduction_comparison_representative_apply_mk₀
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N]
    (n : ℕ+) (f : M ⟶ N) :
    ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
      (torsionQuotient_zero_linearEquiv (A := A) (I := I)
        (X := extReductionSystem I M N 0) n
        ((ext_zero_reduction_comparison_representative (A := A) (I := I) (M := M) (N := N))
          n (Nat.zero_le _)
          ((powerSubmodule_zero_linearEquiv (A := A) (I := I)
            (X := extQuotientSystem I M N 0) n).symm
            (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n)))) =
      stagewise_reduction_hom_descend_of_hom (I := I) (M := M) (N := N) (n := n) f := by
  -- First remove the cutoff-`0` wrapper, then reuse the already normalized degree-zero transport.
  have hstage :
      torsionQuotient_zero_linearEquiv (A := A) (I := I)
          (X := extReductionSystem I M N 0) n
          ((ext_zero_reduction_comparison_representative (A := A) (I := I) (M := M) (N := N))
            n (Nat.zero_le _)
            ((powerSubmodule_zero_linearEquiv (A := A) (I := I)
              (X := extQuotientSystem I M N 0) n).symm
              (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n))) =
        ext_zero_reduction_comparison_stageLinearMap
          (A := A) (I := I) (M := M) (N := N) n
          (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n) := by
    simpa [ext_zero_reduction_comparison_representative] using
      cutoff_zero_representative_of_stageLinearMap_apply_symm
        (A := A) (I := I)
        (X := extQuotientSystem I M N 0) (Y := extReductionSystem I M N 0)
        (fun m ↦ ext_zero_reduction_comparison_stageLinearMap
          (A := A) (I := I) (M := M) (N := N) m)
        n
        (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n)
  calc
    ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
        (torsionQuotient_zero_linearEquiv (A := A) (I := I)
          (X := extReductionSystem I M N 0) n
          ((ext_zero_reduction_comparison_representative (A := A) (I := I) (M := M) (N := N))
            n (Nat.zero_le _)
            ((powerSubmodule_zero_linearEquiv (A := A) (I := I)
              (X := extQuotientSystem I M N 0) n).symm
              (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n)))) =
      ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n
        (ext_zero_reduction_comparison_stageLinearMap
          (A := A) (I := I) (M := M) (N := N) n
          (Submodule.Quotient.mk (Ext.mk₀ f) : extQuotientSystem I M N 0 n)) := by
            rw [hstage]
    _ = stagewise_reduction_hom_descend_of_hom (I := I) (M := M) (N := N) (n := n) f := by
          exact ext_zero_reduction_comparison_transport_apply_mk₀
            (A := A) (I := I) (M := M) (N := N) n f

/-- Helper for Lemma 15.101.8: a linear equivalence transports quotient-by-submodule modules to
the quotient by the mapped submodule. -/
private noncomputable def quotientBySubmoduleLinearEquiv
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (P : Submodule R M) :
    (M ⧸ P) ≃ₗ[R] (N ⧸ P.map e.toLinearMap) :=
  let f :
      (M ⧸ P) →ₗ[R] (N ⧸ P.map e.toLinearMap) :=
    P.mapQ
      (P.map e.toLinearMap)
      e.toLinearMap
      (by
        intro x hx
        exact Submodule.mem_map_of_mem hx)
  let g :
      (N ⧸ P.map e.toLinearMap) →ₗ[R] (M ⧸ P) :=
    (P.map e.toLinearMap).mapQ
      P
      e.symm.toLinearMap
      (by
        intro y hy
        rcases Submodule.mem_map.1 hy with ⟨x, hx, rfl⟩
        simpa using hx)
  -- Evaluate both composites on quotient generators, where they reduce to the ambient inverse
  -- equalities for `e`.
  LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      simpa [f, g] using
        congrArg (Submodule.Quotient.mk (p := P.map e.toLinearMap))
          (e.apply_symm_apply x))
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      simpa [f, g] using
        congrArg (Submodule.Quotient.mk (p := P))
          (e.symm_apply_apply x))

/-- Helper for Lemma 15.101.8: if a power of an ideal annihilates one module, then the same power
annihilates any linearly equivalent module. -/
private theorem ideal_smul_top_eq_bot_of_linearEquiv
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N)
    (hM : J • (⊤ : Submodule R M) = ⊥) :
    J • (⊤ : Submodule R N) = ⊥ := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr y hy
    have hsource_mem : r • e.symm y ∈ J • (⊤ : Submodule R M) := by
      exact Submodule.smul_mem_smul hr (by simp)
    have hsource_zero : r • e.symm y = 0 := by
      rw [hM, Submodule.mem_bot] at hsource_mem
      simpa using hsource_mem
    simpa using congrArg e hsource_zero
  · exact bot_le

/-- Helper for Lemma 15.101.8: torsion by a fixed set is preserved when transporting a module
backward along a linear equivalence. -/
private theorem module_isTorsionBySet_of_linearEquiv
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {S : Set R}
    (hN : Module.IsTorsionBySet R N S) :
    Module.IsTorsionBySet R M S := by
  intro x
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  have hx : a • e x = 0 := by
    rw [Submodule.mem_torsionBySet_iff] at hN
    exact hN (e x) a
  apply e.injective
  simpa using hx

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the target degree-zero stage is
canonically the raw Hom stage from Lemma `15.101.4`. -/
private noncomputable abbrev ext_zero_reduction_target_linearEquiv_restrictScalars
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    extReductionSystem I M N 0 n ≃ₗ[A] homIdealPowerStage I M N n.natPred :=
  ((ext_zero_reduction_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n).trans
    (stagewise_reduction_hom_factorization (A := A) (I := I) (M := M) (N := N) n).symm).restrictScalars A

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the normalized degree-zero stage
map is the conjugate of the raw Hom comparison by the source and target adapters. -/
private theorem ext_zero_reduction_comparison_stageLinearMap_restrictScalars_eq
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    LinearMap.restrictScalars A
        (ext_zero_reduction_comparison_stageLinearMap
          (A := A) (I := I) (M := M) (N := N) n) =
      (ext_zero_reduction_target_linearEquiv_restrictScalars
          (A := A) (I := I) (M := M) (N := N) n).symm.toLinearMap.comp
        ((homReductionComparison I M N n.natPred).comp
          ((ext_zero_quotient_stage_linearEquiv
            (A := A) (I := I) (M := M) (N := N) n).restrictScalars A).toLinearMap) := by
  -- This is just the literal definition of the normalized degree-zero stage map after all
  -- structure maps are viewed over `A`.
  rfl

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the source degree-zero adapter
identifies the raw kernel from Lemma `15.101.4` with the kernel of the normalized reduced stage
map. -/
private noncomputable def ext_zero_reduction_comparison_stageLinearMap_restrictScalars_kernel_equiv
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    LinearMap.ker (homReductionComparison I M N n.natPred) ≃ₗ[A]
      LinearMap.ker
        (LinearMap.restrictScalars A
          (ext_zero_reduction_comparison_stageLinearMap
            (A := A) (I := I) (M := M) (N := N) n)) := by
  let eSource :
      extQuotientSystem I M N 0 n ≃ₗ[A] idealPowerModuleQuotient I (M ⟶ N) n.natPred :=
    (ext_zero_quotient_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n).restrictScalars A
  let eTarget :
      extReductionSystem I M N 0 n ≃ₗ[A] homIdealPowerStage I M N n.natPred :=
    ext_zero_reduction_target_linearEquiv_restrictScalars
      (A := A) (I := I) (M := M) (N := N) n
  let forward :
      LinearMap.ker (homReductionComparison I M N n.natPred) →ₗ[A]
        LinearMap.ker
          (LinearMap.restrictScalars A
            (ext_zero_reduction_comparison_stageLinearMap
              (A := A) (I := I) (M := M) (N := N) n)) :=
    { toFun := fun x ↦
        ⟨eSource.symm x, by
          -- Apply the target adapter to reduce to the raw kernel condition on `x`.
          apply eTarget.injective
          simp [eSource, eTarget,
            ext_zero_reduction_comparison_stageLinearMap_restrictScalars_eq,
            LinearMap.comp_apply, x.2]⟩
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  let backward :
      LinearMap.ker
          (LinearMap.restrictScalars A
            (ext_zero_reduction_comparison_stageLinearMap
              (A := A) (I := I) (M := M) (N := N) n)) →ₗ[A]
        LinearMap.ker (homReductionComparison I M N n.natPred) :=
    { toFun := fun x ↦
        ⟨eSource x, by
          -- Apply the target adapter to the kernel condition on the normalized stage map.
          have hx :
              LinearMap.restrictScalars A
                  (ext_zero_reduction_comparison_stageLinearMap
                    (A := A) (I := I) (M := M) (N := N) n) x = 0 := x.2
          have hx' := congrArg eTarget hx
          simpa [eSource, eTarget,
            ext_zero_reduction_comparison_stageLinearMap_restrictScalars_eq,
            LinearMap.comp_apply] using hx'⟩
      map_add' := by
        intro x y
        ext
        rfl
      map_smul' := by
        intro a x
        ext
        rfl }
  -- The two kernel transports are inverse because the source adapter is itself an equivalence.
  refine LinearEquiv.ofLinear forward backward ?_ ?_
  · intro x
    ext
    simp [forward, backward, eSource]
  · intro x
    ext
    simp [forward, backward, eSource]

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the range of the normalized
degree-zero stage map is the image of the raw Hom-comparison range under the target adapter. -/
private theorem ext_zero_reduction_comparison_stageLinearMap_restrictScalars_range_eq
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    LinearMap.range
        (LinearMap.restrictScalars A
          (ext_zero_reduction_comparison_stageLinearMap
            (A := A) (I := I) (M := M) (N := N) n)) =
      (LinearMap.range (homReductionComparison I M N n.natPred)).map
        (ext_zero_reduction_target_linearEquiv_restrictScalars
          (A := A) (I := I) (M := M) (N := N) n).symm.toLinearMap := by
  let eSource :
      extQuotientSystem I M N 0 n ≃ₗ[A] idealPowerModuleQuotient I (M ⟶ N) n.natPred :=
    (ext_zero_quotient_stage_linearEquiv (A := A) (I := I) (M := M) (N := N) n).restrictScalars A
  let eTarget :
      extReductionSystem I M N 0 n ≃ₗ[A] homIdealPowerStage I M N n.natPred :=
    ext_zero_reduction_target_linearEquiv_restrictScalars
      (A := A) (I := I) (M := M) (N := N) n
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨(homReductionComparison I M N n.natPred) (eSource x), ?_, ?_⟩
    · exact ⟨eSource x, rfl⟩
    · simp [eSource, eTarget,
        ext_zero_reduction_comparison_stageLinearMap_restrictScalars_eq,
        LinearMap.comp_apply]
  · rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    refine ⟨eSource.symm x, ?_⟩
    simp [eSource, eTarget,
      ext_zero_reduction_comparison_stageLinearMap_restrictScalars_eq,
      LinearMap.comp_apply]

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the cokernel of the normalized
degree-zero stage map is linearly equivalent to the cokernel of the raw Hom comparison from
Lemma `15.101.4`. -/
private noncomputable def ext_zero_reduction_comparison_stageLinearMap_restrictScalars_cokernel_equiv
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (n : ℕ+) :
    (homIdealPowerStage I M N n.natPred ⧸
        LinearMap.range (homReductionComparison I M N n.natPred)) ≃ₗ[A]
      (extReductionSystem I M N 0 n ⧸
        LinearMap.range
          (LinearMap.restrictScalars A
            (ext_zero_reduction_comparison_stageLinearMap
              (A := A) (I := I) (M := M) (N := N) n))) := by
  let eTarget :
      extReductionSystem I M N 0 n ≃ₗ[A] homIdealPowerStage I M N n.natPred :=
    ext_zero_reduction_target_linearEquiv_restrictScalars
      (A := A) (I := I) (M := M) (N := N) n
  let eQuot :
      (homIdealPowerStage I M N n.natPred ⧸
          LinearMap.range (homReductionComparison I M N n.natPred)) ≃ₗ[A]
        (extReductionSystem I M N 0 n ⧸
          (LinearMap.range (homReductionComparison I M N n.natPred)).map
            eTarget.symm.toLinearMap) :=
    quotientBySubmoduleLinearEquiv eTarget.symm
      (LinearMap.range (homReductionComparison I M N n.natPred))
  let eRange :
      (extReductionSystem I M N 0 n ⧸
          (LinearMap.range (homReductionComparison I M N n.natPred)).map
            eTarget.symm.toLinearMap) ≃ₗ[A]
        (extReductionSystem I M N 0 n ⧸
          LinearMap.range
            (LinearMap.restrictScalars A
              (ext_zero_reduction_comparison_stageLinearMap
                (A := A) (I := I) (M := M) (N := N) n))) :=
    Submodule.quotEquivOfEq _ _
      (ext_zero_reduction_comparison_stageLinearMap_restrictScalars_range_eq
        (A := A) (I := I) (M := M) (N := N) n).symm
  -- First transport the quotient by range along the target equivalence, then rewrite the range.
  exact eQuot.trans eRange

/-- Helper for Lemma 15.101.8: if `I^c` annihilates an `A`-module that already comes from the
quotient ring `A / I^n`, then the module is torsion by the stage ideal to the same power. -/
private theorem module_isTorsionBySet_stageIdeal_of_ideal_smul_top_eq_bot
    (I : Ideal A) (n : ℕ+) {X : Type u}
    [AddCommGroup X] [Module (stageRing A I n) X] [Module A X]
    [IsScalarTower A (stageRing A I n) X]
    (c : ℕ) (hX : I ^ c • (⊤ : Submodule A X) = ⊥) :
    Module.IsTorsionBySet
      (stageRing A I n)
      X
      (↑((stageIdeal A I n) ^ c) : Set (stageRing A I n)) := by
  intro x
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  have ha' : (a : stageRing A I n) ∈ Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) (I ^ c) := by
    simpa [IadicFiniteModuleSystem.stageIdeal, Ideal.map_pow] using a.2
  rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (I ^ (n : ℕ)))
      (Ideal.Quotient.mk_surjective (I ^ (n : ℕ)))] at ha'
  rcases ha' with ⟨r, hr, rfl⟩
  have hrx_mem : r • x ∈ I ^ c • (⊤ : Submodule A X) := by
    exact Submodule.smul_mem_smul hr (by simp)
  have hrx_zero : r • x = 0 := by
    rw [hX, Submodule.mem_bot] at hrx_mem
    simpa using hrx_mem
  simpa using hrx_zero

/-- Helper for Lemma 15.101.8: after restricting scalars to `A`, the normalized degree-zero stage
comparison inherits the same uniform annihilation bound on kernels and cokernels as the raw Hom
comparison from Lemma `15.101.4`. -/
private theorem exists_ext_zero_reduction_comparison_stageLinearMap_annihilated_kernel_cokernel
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ+,
        I ^ c •
            (⊤ :
              Submodule A
                (LinearMap.ker
                  (LinearMap.restrictScalars A
                    (ext_zero_reduction_comparison_stageLinearMap
                      (A := A) (I := I) (M := M) (N := N) n)))) =
          ⊥) ∧
      ∀ n : ℕ+,
        I ^ c •
            (⊤ :
              Submodule A
                (extReductionSystem I M N 0 n ⧸
                  LinearMap.range
                    (LinearMap.restrictScalars A
                      (ext_zero_reduction_comparison_stageLinearMap
                        (A := A) (I := I) (M := M) (N := N) n)))) =
          ⊥ := by
  obtain ⟨c, hc_pos, hker, hcoker⟩ :=
    exists_homReductionComparison_annihilated_kernel_cokernel (A := A) (I := I) (M := M) (N := N)
  refine ⟨c, hc_pos, ?_, ?_⟩
  · intro n
    -- Transport the raw kernel annihilation bound along the explicit source-side kernel
    -- equivalence.
    exact ideal_smul_top_eq_bot_of_linearEquiv
      (J := I ^ c)
      (ext_zero_reduction_comparison_stageLinearMap_restrictScalars_kernel_equiv
        (A := A) (I := I) (M := M) (N := N) n)
      (hker n.natPred)
  · intro n
    -- Transport the raw quotient-by-range annihilation bound along the explicit cokernel
    -- equivalence.
    exact ideal_smul_top_eq_bot_of_linearEquiv
      (J := I ^ c)
      (ext_zero_reduction_comparison_stageLinearMap_restrictScalars_cokernel_equiv
        (A := A) (I := I) (M := M) (N := N) n)
      (hcoker n.natPred)

/-- Helper for Lemma 15.101.8: a cutoff-`0` representative has eventually bounded kernel and
cokernel once one stagewise ideal power kills every kernel and cokernel uniformly. -/
private theorem cutoff_zero_representative_hasEventuallyBoundedKernelAndCokernel_of_uniform_torsion
    {X Y : IadicFiniteModuleSystem A I}
    (φ : ∀ n : ℕ+, X n →ₗ[stageRing A I n] Y n)
    (c : ℕ)
    (hker :
      ∀ n : ℕ+,
        Module.IsTorsionBySet
          (stageRing A I n)
          (LinearMap.ker (φ n))
          (↑((stageIdeal A I n) ^ c) : Set (stageRing A I n)))
    (hcoker :
      ∀ n : ℕ+,
        Module.IsTorsionBySet
          (stageRing A I n)
          (Y n ⧸ LinearMap.range (φ n))
          (↑((stageIdeal A I n) ^ c) : Set (stageRing A I n))) :
    HasEventuallyBoundedKernelAndCokernel
      ((Q I).map
        (cutoff_zero_representative_of_stageLinearMap (A := A) (I := I) (X := X) (Y := Y) φ)) := by
  -- Use the cutoff-`0` representative itself as the witness, with no need to discard any initial
  -- stages.
  refine ⟨cutoff_zero_representative_of_stageLinearMap (A := A) (I := I) (X := X) (Y := Y) φ,
    rfl, ?_⟩
  refine ⟨c, 0, Nat.zero_le _, ?_⟩
  intro n hn
  constructor
  · -- The level kernel is the raw stagewise kernel after the explicit cutoff-`0` source
    -- identification.
    exact module_isTorsionBySet_of_linearEquiv
      (cutoff_zero_representative_kernel_linearEquiv
        (A := A) (I := I) (X := X) (Y := Y) φ n)
      (hker n)
  · -- The level cokernel is the raw stagewise quotient by range after the target cutoff-`0`
    -- normalization.
    exact module_isTorsionBySet_of_linearEquiv
      (cutoff_zero_representative_cokernel_linearEquiv
        (A := A) (I := I) (X := X) (Y := Y) φ n)
      (hcoker n)

/-- Helper for Lemma 15.101.8: the normalized degree-zero comparison already gives an isomorphism
in the quotient category of Remark `15.101.6`. -/
private theorem ext_zero_reduction_comparison_isomorphic
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] :
    IsIsomorphic ((Q I).obj (extQuotientSystem I M N 0)) ((Q I).obj (extReductionSystem I M N 0)) := by
  let f :
      ((Q I).obj (extQuotientSystem I M N 0)) ⟶
        ((Q I).obj (extReductionSystem I M N 0)) :=
    (Q I).map
      (ext_zero_reduction_comparison_representative
        (A := A) (I := I) (M := M) (N := N))
  obtain ⟨c, _hc_pos, hker, hcoker⟩ :=
    exists_ext_zero_reduction_comparison_stageLinearMap_annihilated_kernel_cokernel
      (A := A) (I := I) (M := M) (N := N)
  have hfBounded : HasEventuallyBoundedKernelAndCokernel f := by
    -- Convert the uniform annihilation bounds over `A` into stage-ideal torsion bounds, then
    -- feed them to the general cutoff-`0` representative criterion.
    refine cutoff_zero_representative_hasEventuallyBoundedKernelAndCokernel_of_uniform_torsion
      (A := A) (I := I)
      (X := extQuotientSystem I M N 0)
      (Y := extReductionSystem I M N 0)
      (fun n ↦ ext_zero_reduction_comparison_stageLinearMap
        (A := A) (I := I) (M := M) (N := N) n)
      c
      ?_
      ?_
    · intro n
      exact module_isTorsionBySet_stageIdeal_of_ideal_smul_top_eq_bot
        (A := A) (I := I) (n := n) c (hker n)
    · intro n
      exact module_isTorsionBySet_stageIdeal_of_ideal_smul_top_eq_bot
        (A := A) (I := I) (n := n) c (hcoker n)
  have hfIso : IsIso f :=
    (IadicFiniteModuleSystem.isIso_iff_hasEventuallyBoundedKernelAndCokernel
      (A := A) (I := I) f).2 hfBounded
  -- An isomorphism witness for the comparison morphism gives the desired object-level
  -- isomorphism.
  exact ⟨asIso f⟩

/-- Helper for Lemma 15.101.8: for a short exact row with projective middle term, the
contravariant boundary map is a linear equivalence in every positive degree. -/
private noncomputable def shortExact_boundary_linearEquiv_ext_succ
    {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (N : ModuleCat R) [CategoryTheory.Projective S.X₂] (q : ℕ) :
    Ext S.X₁ N (q + 1) ≃ₗ[R] Ext S.X₃ N (q + 2) := by
  let δ : Ext S.X₁ N (q + 1) →ₗ[R] Ext S.X₃ N (q + 2) :=
    hS.extClass.precompOfLinear R N (Nat.add_comm 1 (q + 1))
  have hsurj : Function.Surjective δ := by
    intro e
    -- Exactness at the right-hand `Ext` term lifts every class across the boundary map.
    exact Ext.contravariant_sequence_exact₃ hS N e (Ext.eq_zero_of_projective _)
      (Nat.add_comm 1 (q + 1))
  have hinj : Function.Injective δ := by
    intro x y hxy
    have hsub : δ (x - y) = 0 := by
      rw [LinearMap.map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS N (x - y)
      (Nat.add_comm 1 (q + 1)) hsub
    have hzero : z = 0 := by
      exact z.eq_zero_of_projective
    have hxy' : x - y = 0 := by
      simpa [δ, hzero] using hz.symm
    exact sub_eq_zero.mp hxy'
  -- The long exact sequence is exact on both sides because the middle term is projective.
  exact LinearEquiv.ofBijective δ ⟨hinj, hsurj⟩

/-- Helper for Lemma 15.101.8: a finite module over a Noetherian ring admits one exact finite
free presentation. -/
private theorem exists_exact_finite_free_presentation
    (X : ModuleCat A) [Module.Finite A X] :
    ∃ n m : ℕ, ∃ f : (Fin m → A) →ₗ[A] (Fin n → A), ∃ g : (Fin n → A) →ₗ[A] X,
      Function.Exact f g ∧ Function.Surjective g := by
  letI : Module.FinitePresentation A X := Module.finitePresentation_of_finite A X
  -- Over a Noetherian ring, finite modules are finitely presented, so the canonical owner theorem
  -- produces the required exact sequence between finite free modules.
  simpa using
    (Module.FinitePresentation.iff_exists_exact_free_sequence A X).mp inferInstance

-- Proof sketch: choose a finite presentation `0 → K → A^r → M → 0`, compare the systems
-- `(K / I^n K)_n` and `(Ker(A_n^r → M_n))_n` via Lemma `15.101.1`, and then compare the induced
-- Hom systems using Lemmas `15.101.4` and `15.101.7`. Dimension shifting reduces the higher Ext
-- cases to `i = 0, 1`, where the long exact sequence and a diagram chase produce the required
-- representative with uniformly bounded kernel and cokernel.
/-- Lemma 15.101.8: for every `i ≥ 0`, the system
`(\operatorname{Ext}^i_A(M, N) / I^n \operatorname{Ext}^i_A(M, N))_{n \ge 1}` admits a
representative with eventually bounded kernel and cokernel to the system
`(\operatorname{Ext}^i_{A / I^n}(M / I^n M, N / I^n N))_{n \ge 1}`; equivalently, and here taken
as the canonical public statement, these two objects are isomorphic in the category
`\mathcal C` of Remark `15.101.6`. -/
theorem extQuotientSystem_isomorphic_extReductionSystem
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M] [Module.Finite A N] (i : ℕ) :
    IsIsomorphic ((Q I).obj (extQuotientSystem I M N i)) ((Q I).obj (extReductionSystem I M N i)) := by
  induction i generalizing M N with
  | zero =>
      -- The base case is now fully normalized: Lemma `15.101.4` gives the raw Hom comparison,
      -- and Lemma `15.101.7` upgrades the packaged cutoff-`0` representative to an isomorphism.
      simpa using ext_zero_reduction_comparison_isomorphic
        (A := A) (I := I) (M := M) (N := N)
  | succ j ih =>
      -- Route correction: the degree-zero transport is finished above, so the only remaining work
      -- is the source-faithful positive-degree argument via one fixed finite free presentation.
      rcases exists_exact_finite_free_presentation (A := A) M with
        ⟨n, m, f, g, hfg, hg⟩
      let K : ModuleCat A := ModuleCat.of A (LinearMap.ker g)
      let S : ShortComplex (ModuleCat A) := LinearMap.shortComplexKer g
      have hS : S.ShortExact := by
        -- The canonical kernel row `0 → ker(g) → A^n → M → 0` is short exact because `g` is
        -- surjective.
        simpa [S] using LinearMap.shortExact_shortComplexKer hg
      have ihK :
          IsIsomorphic
            ((Q I).obj (extQuotientSystem I K N j))
            ((Q I).obj (extReductionSystem I K N j)) := by
        -- The inductive input is now available on the fixed first syzygy `K`.
        exact ih (M := K) (N := N)
      -- TODO: compare the quotient-system stages for `K` with the actual reduced kernels
      -- `K(n) = ker(F_n → M_n)` using Lemma `15.101.1`, upgrade that comparison to the stagewise
      -- `Ext^j` systems via Lemma `15.101.7`, and then conjugate `ihK` through the unreduced and
      -- reduced boundary equivalences coming from `hS` and the projective middle term `A^n`.
      sorry

end
