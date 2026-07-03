import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_98_3 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped DirectSum
open HomogeneousIdeal

universe u w

noncomputable section

section

/- Domain triage:
* `source-facing`: Lemma `10.98.3` asks for one finite graded `A`-module whose quotients
  `N / I^n N` recover the given inverse system.
* `core/canonical` owners: the sequential inverse system is a functor
  `OrderDual ℕ+ ⥤ ModuleCat A`; the ambient graded module is carried by
  `DirectSum.Decomposition ℳ` and `SetLike.GradedSMul 𝒜 ℳ`; the quotient-transition maps are the
  canonical maps `AdicCompletion.transitionMap`.
* `bridge/view`: the stagewise graded equivalences from those quotients to the prescribed stages of
  the inverse system, expressed by linear equivalences together with degreewise compatibility and
  commuting quotient squares.

Primitive data are the finite graded stages, the transition maps, and the single realizing graded
module. The quotient identifications and their compatibility are derived API from that owner data,
so this file states the source-facing existential theorem directly rather than introducing a second
public wrapper structure.

Relevant owner declarations sampled for this refinement:
* `OrderDual ℕ+ ⥤ ModuleCat A`
* `AdicCompletion.transitionMap`
* `DirectSum.Decomposition`
* `SetLike.GradedSMul`
* `HomogeneousIdeal.irrelevant`
* `surjective_of_irrelevant_reduceModIdeal_surjective`
-/

local instance : AddAction ℕ ℤ where
  vadd n d := n + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (𝒜 : ℕ → Submodule A A) [GradedRing 𝒜]

local notation "SmallModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat A

/-- Helper for Lemma 10.98.3: the successor comparison in `ℕ+` viewed in the opposite indexing
category. -/
private theorem pnat_le_succ (n : ℕ+) : n ≤ n + 1 := by
  exact_mod_cast Nat.le_succ (n : ℕ)

/-- Helper for Lemma 10.98.3: the `k`th positive stage, numbered so that `0` corresponds to
stage `1`. -/
private abbrev natStage (k : ℕ) : ℕ+ :=
  ⟨k + 1, Nat.succ_pos k⟩

/-- Helper for Lemma 10.98.3: every positive stage is `natStage` applied to its predecessor
index. -/
private theorem natStage_pred_eq (n : ℕ+) : natStage ((n : ℕ) - 1) = n := by
  apply Subtype.ext
  change ((n : ℕ) - 1) + 1 = n
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.2)

/-- Helper for Lemma 10.98.3: the transition map from stage `j` down to stage `i` for a
comparison `i ≤ j`. -/
private abbrev transitionMap
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) {i j : ℕ+} (hij : i ≤ j) :
    G_.obj (OrderDual.toDual j) →ₗ[A] G_.obj (OrderDual.toDual i) :=
  (G_.map (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom

/-- Helper for Lemma 10.98.3: the immediate successor transition `G_{n + 1} → G_n`. -/
private abbrev stageMap (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) (n : ℕ+) :
    G_.obj (OrderDual.toDual (n + 1)) →ₗ[A] G_.obj (OrderDual.toDual n) :=
  transitionMap G_ (pnat_le_succ n)

/-- Helper for Lemma 10.98.3: the canonical projection from the inverse limit to stage `n`. -/
private abbrev limitProjection (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) (n : ℕ+) :
    (limit G_ : ModuleCat.{w} A) →ₗ[A] G_.obj (OrderDual.toDual n) :=
  (limit.π G_ (OrderDual.toDual n)).hom

/-- Helper for Lemma 10.98.3: every long transition factors through the immediate successor map at
the top stage. -/
private theorem transitionMap_step_eq_comp
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) {i j : ℕ+} (hij : i ≤ j) :
    transitionMap G_ (Nat.le.step hij) = (transitionMap G_ hij).comp (stageMap G_ j) := by
  -- In the preorder category `OrderDual ℕ+`, all morphisms are unique, so the long transition is
  -- the composite of the shorter transition with the last successor step.
  ext x
  change
    (G_.map (homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual i from Nat.le.step hij))).hom x =
      (G_.map (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom
        ((G_.map
            (homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual j from pnat_le_succ j))).hom
          x)
  have hcomp :
      homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual i from Nat.le.step hij) =
        homOfLE (show OrderDual.toDual (j + 1) ≤ OrderDual.toDual j from pnat_le_succ j) ≫
          homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij) := by
    exact Subsingleton.elim _ _
  rw [hcomp, Functor.map_comp]
  rfl

/-- Helper for Lemma 10.98.3: the `n`th limit projection is the successor transition after the
projection to stage `n + 1`. -/
private theorem stageMap_comp_limitProjection_eq
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) (n : ℕ+) :
    (stageMap G_ n).comp (limitProjection G_ (n + 1)) = limitProjection G_ n := by
  -- This is exactly the compatibility relation of the limit cone.
  ext x
  change
    ((limit.π G_ (OrderDual.toDual (n + 1))) ≫
        G_.map
          (homOfLE
            (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))).hom x =
      (limit.π G_ (OrderDual.toDual n)).hom x
  simpa using
    congrArg (fun g ↦ g.hom x)
      (limit.w G_
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n)))

/-- Helper for Lemma 10.98.3: every long transition composed with the corresponding limit
projection is the earlier limit projection. -/
private theorem transitionMap_comp_limitProjection_eq
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) {i j : ℕ+} (hij : i ≤ j) :
    (transitionMap G_ hij).comp (limitProjection G_ j) = limitProjection G_ i := by
  -- This is the general limit-cone compatibility relation for the unique morphism `j ⟶ i`.
  ext x
  change
    ((limit.π G_ (OrderDual.toDual j)) ≫
        G_.map
          (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij))).hom x =
      (limit.π G_ (OrderDual.toDual i)).hom x
  simpa using
    congrArg (fun g ↦ g.hom x)
      (limit.w G_
        (homOfLE (show OrderDual.toDual j ≤ OrderDual.toDual i from hij)))

/-- Helper for Lemma 10.98.3: the canonical grading on the inverse limit consists of elements
whose stagewise coordinates all lie in the same degree. -/
private def limit_grading
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    (d : ℤ) :
    Submodule ℤ (limit G_ : ModuleCat.{w} A) :=
  { carrier := {x | ∀ n : ℕ+, limitProjection G_ n x ∈ 𝒢 n d}
    zero_mem' := by
      intro n
      simpa using (𝒢 n d).zero_mem
    add_mem' := by
      intro x y hx hy n
      simpa [map_add] using (𝒢 n d).add_mem (hx n) (hy n)
    smul_mem' := by
      intro a x hx n
      simpa [map_zsmul] using (𝒢 n d).smul_mem a (hx n) }

/-- Helper for Lemma 10.98.3: homogeneous scalars act on the inverse-limit grading
coordinatewise. -/
private theorem limit_grading_smul_mem
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    {i : ℕ} {d : ℤ} {a : A} (ha : a ∈ 𝒜 i)
    {x : (limit G_ : ModuleCat.{w} A)} (hx : x ∈ limit_grading G_ 𝒢 d) :
    a • x ∈ limit_grading G_ 𝒢 (i + d) := by
  intro n
  have hx_n : limitProjection G_ n x ∈ 𝒢 n d := hx n
  -- Project to stage `n` and use the stagewise graded action.
  change (limitProjection G_ n) (a • x) ∈ 𝒢 n (i + d)
  simpa [LinearMap.map_smul] using
    (SetLike.GradedSMul.smul_mem ha hx_n : a • limitProjection G_ n x ∈ 𝒢 n (i +ᵥ d))

/-- Helper for Lemma 10.98.3: the stagewise grading gives a graded action on the inverse limit. -/
@[reducible] private def limit_grading_gradedSmul
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)] :
    SetLike.GradedSMul 𝒜 (limit_grading G_ 𝒢) where
  smul_mem := by
    intro i d a x ha hx
    exact limit_grading_smul_mem
      (𝒜 := 𝒜) (G_ := G_) (𝒢 := 𝒢) (i := i) (d := d) (a := a) ha (x := x) hx

/-- Helper for Lemma 10.98.3: the homogeneous ideal is finitely generated because the ambient ring
is Noetherian. -/
private theorem homogeneousIdeal_toIdeal_fg (I : HomogeneousIdeal 𝒜) : I.toIdeal.FG := by
  -- This is the exact finite-generation input needed by Lemma `10.98.2`'s quotient comparison.
  simpa using I.toIdeal.fg_of_isNoetherianRing

/-- Helper for Lemma 10.98.3: each stage `G_n` is annihilated by `I ^ n` once the successor map
has kernel `I ^ n G_{n + 1}` and is surjective. -/
private theorem stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) :
    ∀ n : ℕ+,
      I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥ := by
  intro n
  have hmapker :
      Submodule.map (stageMap G_ n) (LinearMap.ker (stageMap G_ n)) = ⊥ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.mp hx
    · intro hy
      rw [Submodule.mem_bot] at hy
      subst hy
      refine ⟨0, ?_, map_zero _⟩
      exact LinearMap.mem_ker.mpr (map_zero (stageMap G_ n))
  -- Follow the source proof: map the kernel description through the surjective successor map.
  calc
    I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n)))
        = I.toIdeal ^ (n : ℕ) • LinearMap.range (stageMap G_ n) := by
            rw [LinearMap.range_eq_top.2 (by simpa [stageMap] using hG_surj n)]
    _ = Submodule.map (stageMap G_ n)
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) := by
            rw [Submodule.map_smul'', Submodule.map_top]
    _ = Submodule.map (stageMap G_ n) (LinearMap.ker (stageMap G_ n)) := by
            rw [show LinearMap.ker (stageMap G_ n) =
                I.toIdeal ^ (n : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) by
                  simpa [stageMap] using hG_ker n]
    _ = ⊥ := hmapker

/-- Helper for Lemma 10.98.3: the `n`th limit projection kills `I ^ n` on the inverse limit once
the `n`th stage is annihilated by `I ^ n`. -/
private theorem limit_projection_pow_smul_top_le_ker_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)) ≤
      LinearMap.ker (limitProjection G_ n) := by
  have hmaple :
      Submodule.map (limitProjection G_ n)
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) ≤
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ <| by
      rw [Submodule.map_top]
      exact le_top
  have hmapbot :
      Submodule.map (limitProjection G_ n)
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) ≤
        ⊥ := by
    simpa [hStage n] using le_trans hmaple (le_of_eq (hStage n))
  -- Passing to the kernel is the universal-property step needed for `liftQ`.
  simpa [Submodule.comap_bot] using
    (Submodule.map_le_iff_le_comap.mp hmapbot)

/-- Helper for Lemma 10.98.3: the `n`th limit projection descends to the quotient
`(lim G_) / I ^ n (lim G_)` in the current module universe. -/
private def limit_projection_quotient_desc_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    ((limit G_ : ModuleCat.{w} A) ⧸
        (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) →ₗ[A]
      G_.obj (OrderDual.toDual n) :=
  (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))).liftQ
    (limitProjection G_ n)
    (limit_projection_pow_smul_top_le_ker_univ (𝒜 := 𝒜) I G_ hStage n)

/-- Helper for Lemma 10.98.3: the descended quotient-stage map recovers the original limit
projection on representatives. -/
private theorem limit_projection_quotient_desc_univ_comp_mkQ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage n).comp
        (Submodule.mkQ
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) =
      limitProjection G_ n := by
  -- The descended map is defined by `liftQ`, so composing with `mkQ` returns the projection.
  simpa [limit_projection_quotient_desc_univ, limitProjection] using
    (Submodule.liftQ_mkQ
      (p := I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))
      (limitProjection G_ n)
      (limit_projection_pow_smul_top_le_ker_univ (𝒜 := 𝒜) I G_ hStage n))

/-- Helper for Lemma 10.98.3: an arbitrary quotient transition on the inverse-limit quotients is
the usual adic transition map between the `I^n`-power quotients. -/
private abbrev limit_projection_positive_stage_map_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A) {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((limit G_ : ModuleCat.{w} A) ⧸
        I.toIdeal ^ ((OrderDual.ofDual i : ℕ+) : ℕ) •
          (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) →ₗ[A]
      ((limit G_ : ModuleCat.{w} A) ⧸
        I.toIdeal ^ ((OrderDual.ofDual j : ℕ+) : ℕ) •
          (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) :=
  AdicCompletion.transitionMap I.toIdeal (limit G_ : ModuleCat.{w} A)
    (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤ ((OrderDual.ofDual i : ℕ+) : ℕ) from
      (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f))

/-- Helper for Lemma 10.98.3: the kernel of the descended quotient-stage map is exactly the image
of the original stage-projection kernel in the quotient. -/
private theorem limit_projection_quotient_desc_ker_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    LinearMap.ker (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage n) =
      Submodule.map
        (Submodule.mkQ
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))))
        (LinearMap.ker (limitProjection G_ n)) := by
  -- This is the first source-proof kernel identification for the descended stage map.
  simpa [limit_projection_quotient_desc_univ, limitProjection] using
    (Submodule.ker_liftQ
      (p := I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))
      (f := (limit.π G_ (OrderDual.toDual n)).hom)
      (h := limit_projection_pow_smul_top_le_ker_univ (𝒜 := 𝒜) I G_ hStage n))

/-- Helper for Lemma 10.98.3: the descended quotient-stage maps commute with every quotient
transition on the inverse limit. -/
private theorem limit_projection_positive_stage_map_comm_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (G_.map f).hom ∘ₗ
        limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual i) =
      limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual j) ∘ₗ
        limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_ f := by
  -- Evaluate both sides on a quotient representative and use the limit cone relation.
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  change ((limit.π G_ i) ≫ G_.map f).hom y = (limit.π G_ j).hom y
  exact congrArg (fun g ↦ g.hom y) (limit.w G_ f)

/-- Helper for Lemma 10.98.3: quotient transitions send higher-stage kernels into lower-stage
kernels. -/
private theorem limit_projection_positive_stage_map_mem_kernel_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    {i j : OrderDual ℕ+} (f : i ⟶ j)
    {x :
      ((limit G_ : ModuleCat.{w} A) ⧸
        I.toIdeal ^ ((OrderDual.ofDual i : ℕ+) : ℕ) •
          (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))}
    (hx :
      x ∈
        LinearMap.ker
          (limit_projection_quotient_desc_univ
            (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual i))) :
    limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_ f x ∈
      LinearMap.ker
        (limit_projection_quotient_desc_univ
          (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual j)) := by
  change
    limit_projection_quotient_desc_univ
        (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual i) x = 0 at hx
  change
    limit_projection_quotient_desc_univ
        (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual j)
        (limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_ f x) = 0
  calc
    limit_projection_quotient_desc_univ
        (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual j)
        (limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_ f x) =
      (G_.map f).hom
        (limit_projection_quotient_desc_univ
          (𝒜 := 𝒜) I G_ hStage (OrderDual.ofDual i) x) := by
            simpa using
              congrArg (fun g ↦ g x)
                (limit_projection_positive_stage_map_comm_univ
                  (𝒜 := 𝒜) I G_ hStage f).symm
    _ = 0 := by
          rw [hx]
          exact map_zero ((G_.map f).hom)

/-- Helper for Lemma 10.98.3: the successor map on quotient kernels is obtained by restricting
the quotient transition `(n + 1) ⟶ n`. -/
private abbrev quotient_desc_kernel_transition_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+) :
    LinearMap.ker
        (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage (n + 1)) →ₗ[A]
      LinearMap.ker
        (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage n) :=
  ((limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))).domRestrict
      (LinearMap.ker
        (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage (n + 1)))).codRestrict
    (LinearMap.ker
      (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage n))
    (fun x ↦
      limit_projection_positive_stage_map_mem_kernel_univ
        (𝒜 := 𝒜) I G_ hStage
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n)) x.2)

/-- Helper for Lemma 10.98.3: every quotient transition on the inverse limit keeps the chosen
representative unchanged. -/
private theorem limit_projection_positive_stage_map_univ_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    {i j : OrderDual ℕ+} (f : i ⟶ j)
    (x : (limit G_ : ModuleCat.{w} A)) :
    limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_ f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- The adic transition map between quotient stages is defined on representatives by the identity.
  rfl

/-- Helper for Lemma 10.98.3: the successor transition on quotient kernels also keeps the chosen
representative of a kernel element unchanged. -/
private theorem quotient_desc_kernel_transition_univ_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥)
    (n : ℕ+)
    (x : (limit G_ : ModuleCat.{w} A))
    (hx :
      Submodule.Quotient.mk x ∈
        LinearMap.ker
          (limit_projection_quotient_desc_univ
            (𝒜 := 𝒜) I G_ hStage (n + 1))) :
    (quotient_desc_kernel_transition_univ (𝒜 := 𝒜) I G_ hStage n
        ⟨Submodule.Quotient.mk x, hx⟩).1 =
      Submodule.Quotient.mk x := by
  -- The restricted successor transition is still the identity on the underlying quotient class.
  exact
    limit_projection_positive_stage_map_univ_apply_mk
      (𝒜 := 𝒜) I G_
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
      x

/-- Helper for Lemma 10.98.3: every power of a homogeneous ideal remains homogeneous. -/
private theorem ideal_pow_isHomogeneous
    (I : HomogeneousIdeal 𝒜) (n : ℕ) :
    (I.toIdeal ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
      simpa using (Ideal.IsHomogeneous.top (𝒜 := 𝒜))
  | succ n ih =>
      -- The source route only needs homogeneity of `I ^ n` to read off its graded components.
      simpa [pow_succ] using Ideal.IsHomogeneous.mul (𝒜 := 𝒜) ih I.isHomogeneous

/-- Helper for Lemma 10.98.3: the exact cutoff `Int.toNat (d - m) + 1` forces every shifted
degree to lie strictly above `d` once the original module degree is at least `m`. -/
private theorem target_degree_lt_of_cutoff_le
    {m d e : ℤ} {i : ℕ}
    (hm : m ≤ e)
    (hi : Int.toNat (d - m) + 1 ≤ i) :
    d < (i : ℤ) + e := by
  have hi' : (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) ≤ i := by
    exact_mod_cast hi
  by_cases hdm : 0 ≤ d - m
  · have hi'' : (d - m : ℤ) + 1 ≤ i := by
      calc
        (d - m : ℤ) + 1 = (((Int.toNat (d - m) : ℕ) : ℤ) + 1) := by
          rw [Int.toNat_of_nonneg hdm]
        _ = (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) := by norm_num
        _ ≤ i := hi'
    linarith
  · have hdm' : d < m := by linarith
    have hpos : (0 : ℤ) < (((Int.toNat (d - m) + 1 : ℕ) : ℤ)) := by
      norm_num
    linarith

/-- Helper for Lemma 10.98.3: because `I ≤ 𝒜₊`, an element of `I ^ n` has no homogeneous
components in degrees `< n`. -/
private theorem decompose_pow_mem_eq_zero_of_lt
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    {n j : ℕ} {r : A}
    (hr : r ∈ I.toIdeal ^ n)
    (hj : j < n) :
    ((DirectSum.decompose 𝒜 r j : 𝒜 j) : A) = 0 := by
  classical
  have hvanish :
      ∀ {k : ℕ} {x : A}, x ∈ I.toIdeal ^ k →
        ∀ t < k, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : A) = 0 := by
    intro k x hx
    refine Submodule.pow_induction_on_left'
        (M := I.toIdeal)
        (C := fun k x _ =>
          ∀ t < k, ((DirectSum.decompose 𝒜 x t : 𝒜 t) : A) = 0) ?_ ?_ ?_ hx
    · intro a t ht
      exact (Nat.not_lt_zero _ ht).elim
    · intro x y k hx hy hx_zero hy_zero t ht
      simpa [DirectSum.decompose_add, hx_zero t ht, hy_zero t ht]
    · intro m hm k x hx hx_zero t ht
      have hm0 : ((DirectSum.decompose 𝒜 m 0 : 𝒜 0) : A) = 0 := by
        have hm_irrelevant : m ∈ 𝒜₊ := hI hm
        have hproj0 : GradedRing.proj 𝒜 0 m = 0 := by
          simpa [HomogeneousIdeal.mem_irrelevant_iff] using hm_irrelevant
        simpa [GradedRing.proj_apply] using hproj0
      -- Expand the left factor into homogeneous pieces and use the induction hypothesis on the
      -- shifted degree of the right factor.
      rw [← DirectSum.sum_support_decompose 𝒜 m, Finset.sum_mul, DirectSum.decompose_sum]
      have hsum_zero :
          (∑ i ∈ (DirectSum.decompose 𝒜 m).support,
              (DirectSum.decompose 𝒜 ((((DirectSum.decompose 𝒜 m) i : 𝒜 i) : A) * x) t :
                𝒜 t)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          apply Subtype.ext
          simpa [hm0]
        · by_cases hit : i ≤ t
          · have hlt : t - i < k := by
              omega
            apply Subtype.ext
            rw [DirectSum.coe_decompose_mul_of_left_mem_of_le (𝒜 := 𝒜)
              (a := (((DirectSum.decompose 𝒜 m i : 𝒜 i) : A))) (b := x)
              (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit]
            simp [hx_zero (t - i) hlt]
          · apply Subtype.ext
            simpa using
              (DirectSum.coe_decompose_mul_of_left_mem_of_not_le (𝒜 := 𝒜)
                (a := (((DirectSum.decompose 𝒜 m i : 𝒜 i) : A))) (b := x)
                (i := i) (n := t) (a_mem := SetLike.coe_mem _) hit)
      simpa using congrArg (fun z : 𝒜 t ↦ (z : A)) hsum_zero
  exact hvanish hr j hj

/-- Helper for Lemma 10.98.3: an `I ^ (d - m + 1)` coefficient cannot contribute to degree `d`
when it acts on a homogeneous vector whose degree is at least `m`. -/
private theorem decompose_pow_smul_homogeneous_eq_zero_of_degree_lower_bound
    {M : Type*} [AddCommGroup M] [Module A M]
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {m d : ℤ}
    {y : M} (hy : SetLike.IsHomogeneousElem ℳ y)
    (hm : m ≤ homogeneousDegree ℳ y hy)
    {r : A}
    (hr : r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1)) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0 := by
  classical
  let e : ℤ := homogeneousDegree ℳ y hy
  have hy_mem : y ∈ ℳ e := homogeneousDegree_mem ℳ y hy
  have hr_decomp :
      ∀ i, (DirectSum.decompose 𝒜 r i : A) ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) :=
    (Ideal.IsHomogeneous.mem_iff (𝒜 := 𝒜)
      (I := I.toIdeal ^ (Int.toNat (d - m) + 1))
      (ideal_pow_isHomogeneous (𝒜 := 𝒜) I (Int.toNat (d - m) + 1))).1 hr
  have hsum_smul :
      r • y =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) := by
    calc
      r • y =
          (∑ i ∈ (DirectSum.decompose 𝒜 r).support,
            (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A))) • y := by
              simpa using congrArg (fun a : A ↦ a • y) (DirectSum.sum_support_decompose 𝒜 r).symm
      _ =
          ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
            (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) := by
              rw [Finset.sum_smul]
  -- Expand the coefficient into homogeneous pieces; low-degree coefficients vanish in `I^k`,
  -- while high-degree coefficients shift the module degree strictly above `d`.
  rw [hsum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y)) d : ℳ d)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 r).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y))
        d)
  rw [happly]
  have hsum_zero :
      (∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hii : i < Int.toNat (d - m) + 1
    · have hzero :
          ((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) = 0 := by
        simpa using
          (decompose_pow_mem_eq_zero_of_lt (𝒜 := 𝒜) (I := I) hI
            (r := (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A))) (hr_decomp i) hii)
      apply Subtype.ext
      simpa [hzero]
    · have hige : Int.toNat (d - m) + 1 ≤ i := Nat.le_of_not_gt hii
      have hlt : d < (i : ℤ) + e :=
        target_degree_lt_of_cutoff_le (m := m) (d := d) (e := e) hm hige
      have hsmul : (((DirectSum.decompose 𝒜 r i : 𝒜 i) : A) • y) ∈ ℳ (i +ᵥ e) :=
        SetLike.GradedSMul.smul_mem (SetLike.coe_mem _) hy_mem
      apply Subtype.ext
      simpa using
        (DirectSum.decompose_of_mem_ne ℳ hsmul (by
          change ((i : ℤ) + e) ≠ d
          exact ne_of_gt hlt))
  exact congrArg (fun z : ℳ d ↦ (z : M)) hsum_zero

/-- Helper for Lemma 10.98.3: after fixing a lower bound on generator degrees, any coefficient in
`I ^ (d - m + 1)` kills the degree-`d` component of every vector in the span. -/
private theorem decompose_pow_smul_span_eq_zero_of_degree_lower_bound
    {M : Type*} [AddCommGroup M] [Module A M]
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {y : M}
    (hy : y ∈ Submodule.span A (s : Set M))
    {r : A}
    (hr : r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1)) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0 := by
  have hspan :
      ∀ {y : M}, y ∈ Submodule.span A (s : Set M) →
        ∀ {r : A}, r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) →
          ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0 := by
    refine Submodule.span_induction
      (p := fun y _ =>
        ∀ {r : A}, r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) →
          ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0) ?_ ?_ ?_ ?_
    · intro x hx r hr'
      exact decompose_pow_smul_homogeneous_eq_zero_of_degree_lower_bound
        (𝒜 := 𝒜) (I := I) (hI := hI) (ℳ := ℳ)
        (y := x) (hy := hs_homogeneous x hx) (m := m) (d := d)
        (hm := hs_lower x hx) hr'
    · intro r hr'
      simp
    · intro y z hy' hz' hy_zero hz_zero r hr'
      simpa [smul_add, DirectSum.decompose_add, hy_zero hr', hz_zero hr']
    · intro a y hy' hy_zero r hr'
      have har : a * r ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) := Ideal.mul_mem_left _ _ hr'
      simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using hy_zero har
  exact hspan hy hr

/-- Helper for Lemma 10.98.3: the degree-`d` component of any element of
`I ^ (d - m + 1) • span(s)` vanishes once all generators have degree at least `m`. -/
private theorem decompose_pow_smul_span_mem_eq_zero_of_degree_lower_bound
    {M : Type*} [AddCommGroup M] [Module A M]
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {z : M}
    (hz :
      z ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) • Submodule.span A (s : Set M)) :
    ((DirectSum.decompose ℳ z d : ℳ d) : M) = 0 := by
  -- Route correction: once the coefficient-side cutoff lemma is in place, the source proof's
  -- span step is the direct `smul_induction_on` reduction.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr y hy
    exact decompose_pow_smul_span_eq_zero_of_degree_lower_bound
      (𝒜 := 𝒜) (I := I) (hI := hI) (ℳ := ℳ)
      (s := s) hs_homogeneous m d hs_lower hy hr
  · intro y z hy_zero hz_zero
    simpa [DirectSum.decompose_add, hy_zero, hz_zero]

/-- Helper for Lemma 10.98.3: a homogeneous degree-`d` element in
`I ^ (d - m + 1) • span(s)` must vanish once the generators all have degree at least `m`. -/
private theorem eq_zero_of_homogeneous_mem_pow_smul_span_of_degree_lower_bound
    {M : Type*} [AddCommGroup M] [Module A M]
    (I : HomogeneousIdeal 𝒜)
    (hI : I ≤ 𝒜₊)
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (m d : ℤ)
    (hs_lower :
      ∀ x, ∀ hx : x ∈ s, m ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {z : M} (hz_hom : z ∈ ℳ d)
    (hz :
      z ∈ I.toIdeal ^ (Int.toNat (d - m) + 1) • Submodule.span A (s : Set M)) :
    z = 0 := by
  -- A homogeneous degree-`d` vector is equal to its own degree-`d` component.
  have hcomponent :
      ((DirectSum.decompose ℳ z d : ℳ d) : M) = 0 :=
    decompose_pow_smul_span_mem_eq_zero_of_degree_lower_bound
      (𝒜 := 𝒜) (I := I) (hI := hI) (ℳ := ℳ)
      (s := s) hs_homogeneous m d hs_lower hz
  simpa [DirectSum.decompose_of_mem_same ℳ hz_hom] using hcomponent

/-- Helper for Lemma 10.98.3: a degree-preserving map between `ℤ`-graded modules commutes with
the chosen homogeneous projections. -/
private theorem decompose_map_eq_of_mapsTo_zgraded
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (ℳ : ℤ → Submodule ℤ M)
    (ℕₘ : ℤ → Submodule ℤ N)
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℕₘ]
    (f : N →ₗ[A] M)
    (hf : ∀ i, Set.MapsTo f (ℕₘ i) (ℳ i))
    (y : N) (i : ℤ) :
    ((DirectSum.decompose ℳ (f y) i : ℳ i) : M) =
      f (((DirectSum.decompose ℕₘ y i : ℕₘ i) : N)) := by
  classical
  let s : Finset ℤ := (DirectSum.decompose ℕₘ y).support
  let g : ℤ → N := fun j ↦ ((DirectSum.decompose ℕₘ y j : ℕₘ j) : N)
  have hdecomp :
      DirectSum.decompose ℳ (f y) =
        ∑ j ∈ s, DirectSum.decompose ℳ (f (g j)) := by
    -- Expand `y` into its homogeneous pieces and apply `f` termwise before projecting.
    rw [show y = ∑ j ∈ s, g j by
      simp [s, g, DirectSum.sum_support_decompose]]
    rw [map_sum, DirectSum.decompose_sum]
  have hcoord :
      ((DirectSum.decompose ℳ (f y) i : ℳ i) : M) =
        ∑ j ∈ s, ((DirectSum.decompose ℳ (f (g j)) i : ℳ i) : M) := by
    simpa [DirectSum.sum_apply] using
      congrArg (fun z : ⨁ j, ℳ j ↦ (z i : M)) hdecomp
  have hterm :
      ∀ j ∈ s,
        ((DirectSum.decompose ℳ (f (g j)) i : ℳ i) : M) =
          if h : j = i then f (((DirectSum.decompose ℕₘ y i : ℕₘ i) : N)) else 0 := by
    intro j hj
    by_cases hji : j = i
    · subst j
      have hmem : f (g i) ∈ ℳ i := hf i (DirectSum.decompose ℕₘ y i).2
      simpa [g] using (DirectSum.decompose_of_mem_same ℳ hmem)
    · have hmem : f (g j) ∈ ℳ j := hf j (DirectSum.decompose ℕₘ y j).2
      simpa [g, hji] using (DirectSum.decompose_of_mem_ne ℳ hmem hji)
  rw [Finset.sum_congr rfl hterm] at hcoord
  by_cases hi : i ∈ s
  · rw [Finset.sum_eq_single_of_mem i hi] at hcoord
    · simpa using hcoord
    · intro j hj hji
      simp [hji]
  · have hi_zero : (((DirectSum.decompose ℕₘ y i : ℕₘ i) : N)) = 0 := by
      have hi_zero' : (DirectSum.decompose ℕₘ y i : ℕₘ i) = 0 := by
        by_contra hzero
        exact hi (by simpa [s, DFinsupp.mem_support_iff, hzero])
      exact congrArg (fun z : ℕₘ i ↦ (z : N)) hi_zero'
    rw [Finset.sum_eq_zero] at hcoord
    · simpa [hi_zero] using hcoord
    · intro j hj
      have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      simp [hji]

/-- Helper for Lemma 10.98.3: every homogeneous element at stage `n` has a homogeneous lift of
the same degree at stage `n + 1`. -/
private theorem stageMap_surjective_on_homogeneous_piece
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    (h𝒢 :
      ∀ (n : ℕ+) (d : ℤ) {x : G_.obj (OrderDual.toDual (n + 1))},
        x ∈ 𝒢 (n + 1) d →
          ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) x ∈ 𝒢 n d)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) (d : ℤ) {y : G_.obj (OrderDual.toDual n)} (hy : y ∈ 𝒢 n d) :
    ∃ x : G_.obj (OrderDual.toDual (n + 1)),
      x ∈ 𝒢 (n + 1) d ∧ stageMap G_ n x = y := by
  obtain ⟨x₀, hx₀⟩ := hG_surj n y
  have hx₀' : stageMap G_ n x₀ = y := by
    simpa [stageMap] using hx₀
  have hmaps :
      ∀ i, Set.MapsTo (stageMap G_ n) (𝒢 (n + 1) i) (𝒢 n i) := by
    intro i x hx
    simpa [stageMap] using h𝒢 n i hx
  refine ⟨((DirectSum.decompose (𝒢 (n + 1)) x₀ d : 𝒢 (n + 1) d) : _), ?_, ?_⟩
  · -- The chosen lift is homogeneous by construction.
    exact (DirectSum.decompose (𝒢 (n + 1)) x₀ d).2
  · -- Route correction: instead of projecting after an arbitrary lift later, project the lift
    -- now and use the `decompose`/map compatibility to recover `y` in degree `d`.
    calc
      stageMap G_ n (((DirectSum.decompose (𝒢 (n + 1)) x₀ d : 𝒢 (n + 1) d) : _)) =
          ((DirectSum.decompose (𝒢 n) (stageMap G_ n x₀) d : 𝒢 n d) : _) := by
            symm
            exact decompose_map_eq_of_mapsTo_zgraded
              (ℳ := 𝒢 n) (ℕₘ := 𝒢 (n + 1)) (f := stageMap G_ n) hmaps x₀ d
      _ = y := by
            have hy_component :
                (((DirectSum.decompose (𝒢 n) y d : 𝒢 n d) :
                  G_.obj (OrderDual.toDual n))) = y := by
              simpa using (DirectSum.decompose_of_mem_same (𝒢 n) hy)
            calc
              ((DirectSum.decompose (𝒢 n) (stageMap G_ n x₀) d : 𝒢 n d) :
                  G_.obj (OrderDual.toDual n)) =
                (((DirectSum.decompose (𝒢 n) y d : 𝒢 n d) :
                  G_.obj (OrderDual.toDual n))) := by
                    rw [hx₀']
              _ = y := hy_component

/-- Helper for Lemma 10.98.3: quotienting a spanning family still gives a spanning family in the
quotient module. -/
private theorem quotient_span_eq_top_of_span_eq_top
    {M : Type*} [AddCommGroup M] [Module A M]
    (p : Submodule A M)
    {ι : Type*} (x : ι → M)
    (hx : Submodule.span A (Set.range x) = ⊤) :
    Submodule.span A (p.mkQ '' Set.range x) = ⊤ := by
  -- Push the spanning statement through the quotient map and use that `mkQ` is surjective.
  calc
    Submodule.span A (p.mkQ '' Set.range x) =
        Submodule.map p.mkQ (Submodule.span A (Set.range x)) := by
          rw [Submodule.map_span]
    _ = Submodule.map p.mkQ ⊤ := by rw [hx]
    _ = ⊤ := by
          simpa [Submodule.range_mkQ] using (Submodule.map_top (f := p.mkQ))

/-- Helper for Lemma 10.98.3: the `A`-span of homogeneous elements is a homogeneous submodule for
the ambient `Submodule ℤ` grading. -/
private theorem decompose_smul_mem_span_of_homogeneous_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {t : Set M} {y : M} (hy : y ∈ t)
    (hy_hom : SetLike.IsHomogeneousElem ℳ y)
    (a : A) (i : ℤ) :
    ((DirectSum.decompose ℳ (a • y) i : ℳ i) : M) ∈ Submodule.span A t := by
  classical
  let e : ℤ := homogeneousDegree ℳ y hy_hom
  have hy_mem : y ∈ ℳ e := homogeneousDegree_mem ℳ y hy_hom
  have hsum_smul :
      a • y =
        ∑ j ∈ (DirectSum.decompose 𝒜 a).support,
          (((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y) := by
    -- Expand the scalar into its homogeneous pieces before projecting to degree `i`.
    calc
      a • y =
          (∑ j ∈ (DirectSum.decompose 𝒜 a).support,
            (((DirectSum.decompose 𝒜 a j : 𝒜 j) : A))) • y := by
              simpa using congrArg (fun b : A ↦ b • y) (DirectSum.sum_support_decompose 𝒜 a).symm
      _ =
          ∑ j ∈ (DirectSum.decompose 𝒜 a).support,
            (((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y) := by
              rw [Finset.sum_smul]
  rw [hsum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ j ∈ (DirectSum.decompose 𝒜 a).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) j : 𝒜 j) : A) • y)) i : ℳ i)) =
        ∑ j ∈ (DirectSum.decompose 𝒜 a).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) j : 𝒜 j) : A) • y) i : ℳ i) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 a).support)
        (fun j ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) j : 𝒜 j) : A) • y))
        i)
  rw [happly]
  have hsum_mem :
      (∑ j ∈ (DirectSum.decompose 𝒜 a).support,
          (((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a) j : 𝒜 j) : A) • y) i : ℳ i) :
            M))) ∈
        Submodule.span A t := by
    refine Submodule.sum_mem _ ?_
    intro j hj
    have hsmul :
        ((((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y) : M) ∈ ℳ (j +ᵥ e) :=
      SetLike.GradedSMul.smul_mem (SetLike.coe_mem _) hy_mem
    by_cases hji : (j : ℤ) + e = i
    · -- The single summand landing in degree `i` is an `A`-multiple of the generator `y`.
      have hcomponent :
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y)) i : ℳ i) :
            M) =
            (((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y) := by
        rw [← hji]
        exact DirectSum.decompose_of_mem_same ℳ hsmul
      rw [hcomponent]
      exact Submodule.smul_mem (Submodule.span A t) _ (Submodule.subset_span hy)
    · -- Every other homogeneous scalar shifts `y` to a different degree, so its projection
      -- vanishes.
      have hcomponent :
          ((DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 a j : 𝒜 j) : A) • y)) i : ℳ i) :
            M) =
            0 := by
        simpa using
          (DirectSum.decompose_of_mem_ne ℳ hsmul (by
            change ((j : ℤ) + e) ≠ i
            exact hji))
      rw [hcomponent]
      exact Submodule.zero_mem (Submodule.span A t)
  simpa using hsum_mem

/-- Helper for Lemma 10.98.3: every homogeneous component of an element in the span of a finite
homogeneous family remains in the same span for the ambient `Submodule ℤ` grading. -/
private theorem decompose_mem_span_finset_of_homogeneous_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    {y : M}
    (hy : y ∈ Submodule.span A (s : Set M))
    (i : ℤ) :
    ((DirectSum.decompose ℳ y i : ℳ i) : M) ∈ Submodule.span A (s : Set M) := by
  classical
  obtain ⟨f, hf_support, hsum⟩ :=
    (Submodule.mem_span_finset (R := A) (s := s)).1 (by simpa using hy)
  -- Replace `y` by a finite coefficient expansion and keep each projected summand in the same
  -- span using the single-generator homogeneous projection lemma.
  rw [← hsum, DirectSum.decompose_sum]
  have happly :
      (((∑ z ∈ s, DirectSum.decompose ℳ (f z • z)) i : ℳ i)) =
        ∑ z ∈ s, (DirectSum.decompose ℳ (f z • z) i : ℳ i) := by
    simpa using
      (DFinsupp.finset_sum_apply s
        (fun z ↦ DirectSum.decompose ℳ (f z • z))
        i)
  rw [happly]
  have hsum_mem :
      (∑ z ∈ s, (((DirectSum.decompose ℳ (f z • z) i : ℳ i) : M))) ∈
        Submodule.span A (s : Set M) := by
    refine Submodule.sum_mem _ ?_
    intro z hz
    by_cases hfz : f z = 0
    · simpa [hfz] using (Submodule.zero_mem (Submodule.span A (s : Set M)))
    · have hz_support : z ∈ Function.support f := by
        simp [Function.mem_support, hfz]
      have hz_s : z ∈ s := hf_support hz_support
      exact decompose_smul_mem_span_of_homogeneous_zgraded
        (𝒜 := 𝒜) (ℳ := ℳ) (t := (s : Set M))
        (y := z) hz_s (hs_homogeneous z hz_s) (f z) i
  simpa using hsum_mem

/-- Helper for Lemma 10.98.3: the `A`-span of homogeneous elements is a homogeneous submodule for
the ambient `Submodule ℤ` grading. -/
private theorem span_isHomogeneous_of_isHomogeneousElem_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {t : Set M}
    (ht : ∀ x ∈ t, SetLike.IsHomogeneousElem ℳ x) :
    (Submodule.span A t).IsHomogeneous ℳ := by
  intro i x hx
  obtain ⟨s, hs_subset, hx_s⟩ := Submodule.mem_span_finite_of_mem_span hx
  have hs_homogeneous : ∀ y ∈ s, SetLike.IsHomogeneousElem ℳ y := by
    intro y hy
    exact ht y (hs_subset hy)
  -- Shrink the span membership to a finite homogeneous family, then project termwise inside that
  -- finite span before enlarging back to `t`.
  exact
    (Submodule.span_mono hs_subset)
      (decompose_mem_span_finset_of_homogeneous_zgraded
        (𝒜 := 𝒜) (ℳ := ℳ) s hs_homogeneous hx_s i)

/-- Helper for Lemma 10.98.3: a finite `A`-module with a `Submodule ℤ` grading admits a finite
homogeneous generating set. -/
private theorem exists_finset_homogeneous_span_eq_top_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [Module.Finite A M] :
    ∃ s : Finset M,
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
        Submodule.span A (s : Set M) = ⊤ := by
  classical
  obtain ⟨t, ht_top⟩ := Module.Finite.fg_top (R := A) (M := M)
  let s : Finset M :=
    t.biUnion fun x =>
      (DirectSum.decompose ℳ x).support.image fun i => (DirectSum.decompose ℳ x i : M)
  have hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨y, hy, hx⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, (DirectSum.decompose ℳ y i).2⟩
  have hspan_le :
      Submodule.span A (t : Set M) ≤ Submodule.span A (s : Set M) := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    -- Replace each original generator by the sum of its homogeneous components.
    rw [← DirectSum.sum_support_decompose ℳ y]
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.subset_span <| by
      exact Finset.mem_biUnion.mpr ⟨y, hy, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  refine ⟨s, hs_homogeneous, top_unique ?_⟩
  simpa [ht_top] using hspan_le

/-- Helper for Lemma 10.98.3: an irrelevant coefficient kills every component at or below the
degree of a homogeneous vector for the current `Submodule ℤ` grading. -/
private theorem decompose_single_homogeneous_smul_component_eq_zero_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {a : A} {i : ℕ} (ha : a ∈ 𝒜 i)
    {y : M} {e d : ℤ} (hy : y ∈ ℳ e)
    (hi : 0 < i) (hd : d ≤ e) :
    ((DirectSum.decompose ℳ ((a : A) • y) d : ℳ d) : M) = 0 := by
  have hsmul : (a • y) ∈ ℳ (i +ᵥ e) := SetLike.GradedSMul.smul_mem ha hy
  simpa using
    (DirectSum.decompose_of_mem_ne ℳ hsmul (positive_vadd_ne_of_le hi hd))

/-- Helper for Lemma 10.98.3: an irrelevant coefficient kills every component at or below the
degree of a homogeneous vector for the current `Submodule ℤ` grading. -/
private theorem decompose_irrelevant_smul_homogeneous_eq_zero_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {y : M} (hy : SetLike.IsHomogeneousElem ℳ y)
    {d : ℤ} (hd : d ≤ homogeneousDegree ℳ y hy)
    {r : A} (hr : r ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) = 0 := by
  classical
  let e : ℤ := homogeneousDegree ℳ y hy
  have hy_mem : y ∈ ℳ e := homogeneousDegree_mem ℳ y hy
  have hr0 : ((DirectSum.decompose 𝒜 r 0 : 𝒜 0) : A) = 0 := by
    -- Membership in the irrelevant ideal is exactly vanishing of the degree-zero coefficient.
    have hproj0 : GradedRing.proj 𝒜 0 r = 0 := by
      simpa [HomogeneousIdeal.mem_irrelevant_iff] using hr
    simpa [GradedRing.proj_apply] using hproj0
  have hsum :
      ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
        (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      apply Subtype.ext
      simpa [hr0]
    · have hi_pos : 0 < i := Nat.pos_iff_ne_zero.mpr hi0
      -- Positive-degree coefficients move `y` strictly above degree `d`.
      apply Subtype.ext
      simpa using
        (decompose_single_homogeneous_smul_component_eq_zero_zgraded (𝒜 := 𝒜) (ℳ := ℳ)
          (a := (((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A))
          (ha := SetLike.coe_mem _)
          (hy := hy_mem) hi_pos hd)
  -- Expand the irrelevant coefficient into homogeneous pieces before projecting.
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, DirectSum.decompose_sum]
  have happly :
      (((∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y)) d : ℳ d)) =
        ∑ i ∈ (DirectSum.decompose 𝒜 r).support,
          (DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y) d : ℳ d) := by
    simpa using
      (DFinsupp.finset_sum_apply
        ((DirectSum.decompose 𝒜 r).support)
        (fun i ↦ DirectSum.decompose ℳ ((((DirectSum.decompose 𝒜 r) i : 𝒜 i) : A) • y))
        d)
  rw [happly]
  simpa using congrArg (fun z : ℳ d ↦ (z : M)) hsum

/-- Helper for Lemma 10.98.3: the degree-`d` component of an irrelevant multiple of the span lies
in a homogeneous submodule once all generators outside it have degree at least `d`. -/
private theorem decompose_irrelevant_smul_span_mem_of_min_degree_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (d : ℤ)
    (hs_min :
      ∀ x, ∀ hx : x ∈ s, x ∉ P → d ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {y : M}
    (hy : y ∈ Submodule.span A (s : Set M))
    {r : A} (hr : r ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) :
    ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P := by
  have hspan :
      ∀ {y : M}, y ∈ Submodule.span A (s : Set M) →
        ∀ {r : A}, r ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal →
          ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P := by
    refine Submodule.span_induction
      (p := fun y _ ↦ ∀ {r : A}, r ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal →
        ((DirectSum.decompose ℳ (r • y) d : ℳ d) : M) ∈ P) ?_ ?_ ?_ ?_
    · intro x hx r hr
      by_cases hxP : x ∈ P
      · -- If the generator is already inside `P`, homogeneity of `P` keeps every component there.
        have hrx : r • x ∈ P := Submodule.smul_mem P r hxP
        exact (Submodule.IsHomogeneous.mem_iff ℳ hP).1 hrx d
      · -- Otherwise the minimal-degree hypothesis forces the projected component to vanish.
        have hzero :
            ((DirectSum.decompose ℳ (r • x) d : ℳ d) : M) = 0 :=
          decompose_irrelevant_smul_homogeneous_eq_zero_zgraded
            (𝒜 := 𝒜) (ℳ := ℳ)
            (y := x) (hy := hs_homogeneous x hx)
            (d := d) (hd := hs_min x hx hxP) (r := r) hr
        exact hzero ▸ P.zero_mem
    · intro r hr
      simpa using (P.zero_mem : (0 : M) ∈ P)
    · intro y z hy' hz' hyP hzP r hr
      -- Additivity of `DirectSum.decompose` keeps the component inside `P`.
      simpa [smul_add, DirectSum.decompose_add] using Submodule.add_mem P (hyP hr) (hzP hr)
    · intro a y hy' hyP r hr
      -- Move the outer scalar into the irrelevant coefficient and stay inside the ideal.
      have har : a * r ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal := Ideal.mul_mem_left _ _ hr
      simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using hyP har
  exact hspan hy hr

/-- Helper for Lemma 10.98.3: the degree-`d` component of an element of
`𝒜₊ • span(s)` lies in the chosen homogeneous submodule under the same minimal-degree hypothesis. -/
private theorem decompose_mem_of_irrelevant_smul_span_of_min_degree_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (d : ℤ)
    (hs_min :
      ∀ x, ∀ hx : x ∈ s, x ∉ P → d ≤ homogeneousDegree ℳ x (hs_homogeneous x hx))
    {z : M}
    (hz :
      z ∈ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • Submodule.span A (s : Set M)) :
    ((DirectSum.decompose ℳ z d : ℳ d) : M) ∈ P := by
  -- Route correction: with the span lemma in place, the outer irrelevant multiple is a direct
  -- `Submodule.smul_induction_on` reduction.
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr y hy
    exact decompose_irrelevant_smul_span_mem_of_min_degree_zgraded
      (𝒜 := 𝒜) (ℳ := ℳ) (P := P) hP s hs_homogeneous d hs_min hy hr
  · intro y z hyP hzP
    simpa [DirectSum.decompose_add] using Submodule.add_mem P hyP hzP

/-- Helper for Lemma 10.98.3: a minimal-degree generator outside a homogeneous submodule already
lies in that submodule once it is congruent modulo `𝒜₊ • span(s)` to an element of the
submodule. -/
private theorem mem_of_mem_sup_irrelevant_smul_span_of_min_degree_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    {x : M} (hx : x ∈ s)
    (hx_min :
      ∀ y, ∀ hy : y ∈ s, y ∉ P →
        homogeneousDegree ℳ x (hs_homogeneous x hx) ≤
          homogeneousDegree ℳ y (hs_homogeneous y hy))
    (hx_sup : x ∈ P ⊔ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • Submodule.span A (s : Set M)) :
    x ∈ P := by
  let d : ℤ := homogeneousDegree ℳ x (hs_homogeneous x hx)
  have hs_min :
      ∀ y, ∀ hy : y ∈ s, y ∉ P → d ≤ homogeneousDegree ℳ y (hs_homogeneous y hy) := by
    intro y hy hyP
    simpa [d] using hx_min y hy hyP
  rcases Submodule.mem_sup.mp hx_sup with ⟨p, hp, z, hz, hx_eq⟩
  have hp_component : ((DirectSum.decompose ℳ p d : ℳ d) : M) ∈ P :=
    (Submodule.IsHomogeneous.mem_iff ℳ hP).1 hp d
  have hz_component : ((DirectSum.decompose ℳ z d : ℳ d) : M) ∈ P :=
    decompose_mem_of_irrelevant_smul_span_of_min_degree_zgraded
      (𝒜 := 𝒜) (ℳ := ℳ) (P := P) hP s hs_homogeneous d hs_min hz
  have hx_component :
      ((DirectSum.decompose ℳ x d : ℳ d) : M) =
        ((DirectSum.decompose ℳ p d : ℳ d) : M) +
          ((DirectSum.decompose ℳ z d : ℳ d) : M) := by
    rw [← hx_eq, DirectSum.decompose_add]
    rfl
  have hx_self : ((DirectSum.decompose ℳ x d : ℳ d) : M) = x := by
    simpa [d] using decompose_homogeneousDegree_eq ℳ x (hs_homogeneous x hx)
  -- Project to the minimal degree; both projected pieces already lie in `P`.
  rw [← hx_self, hx_component]
  exact Submodule.add_mem P hp_component hz_component

/-- Helper for Lemma 10.98.3: if a homogeneous submodule together with the irrelevant multiple of
a finite homogeneous span generates the whole module, then that finite span already lies in the
submodule. -/
private theorem le_of_homogeneous_span_sup_irrelevant_eq_top_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {P : Submodule A M} (hP : P.IsHomogeneous ℳ)
    (s : Finset M)
    (hs_homogeneous : ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x)
    (hspan :
      P ⊔ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • Submodule.span A (s : Set M) = ⊤) :
    Submodule.span A (s : Set M) ≤ P := by
  classical
  refine Submodule.span_le.mpr ?_
  intro x hx
  by_cases hxP : x ∈ P
  · exact hxP
  · let t : Finset M := s.filter fun y ↦ y ∉ P
    have ht_nonempty : t.Nonempty := by
      refine Finset.nonempty_iff_ne_empty.mpr ?_
      intro ht_empty
      have hx_t : x ∈ t := Finset.mem_filter.mpr ⟨hx, hxP⟩
      simpa [t, ht_empty] using hx_t
    obtain ⟨y, hy, hy_min⟩ :=
      Finset.exists_min_image t.attach
        (fun z : {z // z ∈ t} =>
          homogeneousDegree ℳ z.1 (hs_homogeneous z.1 (Finset.mem_filter.mp z.2).1))
        ht_nonempty.attach
    have hy_mem : y.1 ∈ s := (Finset.mem_filter.mp y.2).1
    have hy_not_mem : y.1 ∉ P := (Finset.mem_filter.mp y.2).2
    have hy_min' :
        ∀ z, ∀ hz : z ∈ s, z ∉ P →
          homogeneousDegree ℳ y.1 (hs_homogeneous y.1 hy_mem) ≤
            homogeneousDegree ℳ z (hs_homogeneous z hz) := by
      intro z hz hzP
      exact hy_min ⟨z, Finset.mem_filter.mpr ⟨hz, hzP⟩⟩ (by simp)
    have hy_sup : y.1 ∈ P ⊔ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • Submodule.span A (s : Set M) := by
      rw [hspan]
      exact Submodule.mem_top
    have hy_memP :
        y.1 ∈ P :=
      mem_of_mem_sup_irrelevant_smul_span_of_min_degree_zgraded
        (𝒜 := 𝒜) (ℳ := ℳ) (P := P) hP s hs_homogeneous hy_mem hy_min' hy_sup
    exact False.elim <| hy_not_mem hy_memP

/-- Helper for Lemma 10.98.3: if the quotient classes of a finite homogeneous family span modulo
`𝒜₊ • ⊤`, then the family already spans the whole module. -/
private theorem span_eq_top_of_quotient_span_eq_top_of_homogeneous_zgraded
    {M : Type*} [AddCommGroup M] [Module A M]
    (ℳ : ℤ → Submodule ℤ M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → M) (δ : ι → ℤ)
    (hx : ∀ i, x i ∈ ℳ (δ i))
    (hspan :
      Submodule.span A
        ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • (⊤ : Submodule A M)).mkQ) '' Set.range x) = ⊤) :
    Submodule.span A (Set.range x) = ⊤ := by
  classical
  let P : Submodule A M := Submodule.span A (Set.range x)
  have hP : P.IsHomogeneous ℳ := by
    -- The chosen generators are already homogeneous in their prescribed degrees.
    refine span_isHomogeneous_of_isHomogeneousElem_zgraded (𝒜 := 𝒜) (ℳ := ℳ) ?_
    intro y hy
    rcases hy with ⟨j, rfl⟩
    exact ⟨δ j, hx j⟩
  have hsup : P ⊔ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • (⊤ : Submodule A M) = ⊤ := by
    have hmap :
        Submodule.map
            (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • (⊤ : Submodule A M)).mkQ)
            P = ⊤ := by
      -- Push the chosen span through the quotient map first.
      rw [show P = Submodule.span A (Set.range x) by rfl, Submodule.map_span]
      exact hspan
    rwa [Submodule.map_mkQ_eq_top, sup_comm] at hmap
  obtain ⟨s, hs_homogeneous, hs_span⟩ :=
    exists_finset_homogeneous_span_eq_top_zgraded (A := A) (ℳ := ℳ)
  have hs_le : Submodule.span A (s : Set M) ≤ P := by
    have hspan' :
        P ⊔ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal • Submodule.span A (s : Set M) = ⊤ := by
      simpa [hs_span] using hsup
    exact le_of_homogeneous_span_sup_irrelevant_eq_top_zgraded
      (𝒜 := 𝒜) (ℳ := ℳ) (P := P) hP s hs_homogeneous hspan'
  apply top_unique
  simpa [P, hs_span] using hs_le

/-- Helper for Lemma 10.98.3: the successor map sends the irrelevant-ideal submodule of stage
`n + 1` onto the corresponding irrelevant-ideal submodule of stage `n`. -/
private theorem stageMap_irrelevant_smul_top_map_eq
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    Submodule.map (stageMap G_ n)
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) =
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual n)))) := by
  -- The source proof only uses that successor maps are surjective, so the irrelevant ideal acts
  -- on the target stage exactly as the image of the corresponding source-stage submodule.
  calc
    Submodule.map (stageMap G_ n)
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) =
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) • LinearMap.range (stageMap G_ n)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
    _ =
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual n)))) := by
        rw [LinearMap.range_eq_top.2 (by simpa [stageMap] using hG_surj n)]

/-- Helper for Lemma 10.98.3: the irrelevant-ideal submodule of stage `n + 1` lies in the
preimage of the irrelevant-ideal submodule of stage `n` under the successor map. -/
private theorem stageMap_irrelevant_smul_top_le_comap
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) ≤
      Submodule.comap (stageMap G_ n)
        ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual n))))) := by
  -- Repackage the image computation above as the map/comap relation needed by `mapQ`.
  exact
    (Submodule.map_le_iff_le_comap.mp <|
      le_of_eq (stageMap_irrelevant_smul_top_map_eq (𝒜 := 𝒜) G_ hG_surj n))

/-- Helper for Lemma 10.98.3: because `ker(stageMap)` is contained in the irrelevant ideal, the
preimage of the irrelevant-ideal submodule is exactly the irrelevant-ideal submodule itself. -/
private theorem stageMap_irrelevant_smul_top_comap_eq
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    Submodule.comap (stageMap G_ n)
        ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual n))))) =
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) := by
  have hpow_le_irrelevant :
      I.toIdeal ^ (n : ℕ) ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal := by
    exact le_trans
      (Ideal.pow_right_mono hI (n : ℕ))
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal).pow_le_self (Nat.ne_of_gt n.2))
  refine le_antisymm ?_ (stageMap_irrelevant_smul_top_le_comap (𝒜 := 𝒜) G_ hG_surj n)
  intro x hx
  have hx_map :
      stageMap G_ n x ∈
        Submodule.map (stageMap G_ n)
          ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))) := by
    rw [stageMap_irrelevant_smul_top_map_eq (𝒜 := 𝒜) G_ hG_surj n]
    exact hx
  rcases hx_map with ⟨z, hz, hz_eq⟩
  have hdiff_ker : x - z ∈ LinearMap.ker (stageMap G_ n) := by
    rw [LinearMap.mem_ker]
    calc
      stageMap G_ n (x - z) = stageMap G_ n x - stageMap G_ n z := by
        simpa using (stageMap G_ n).map_sub x z
      _ = 0 := by rw [hz_eq, sub_self]
  have hdiff_pow :
      x - z ∈ I.toIdeal ^ (n : ℕ) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
    have hker_eq :
        LinearMap.ker (stageMap G_ n) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
      simpa [stageMap] using hG_ker n
    exact hker_eq ▸ hdiff_ker
  have hpow_mem :
      x - z ∈
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) :=
    Submodule.smul_mono_left hpow_le_irrelevant hdiff_pow
  have hsum :
      (x - z) + z ∈
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) :=
    Submodule.add_mem _ hpow_mem hz
  have hx_mem :
      x ∈
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) := by
    convert hsum using 1
    exact (sub_add_cancel x z).symm
  exact hx_mem

/-- Helper for Lemma 10.98.3: the successor map descends to a quotient map modulo the irrelevant
ideal. -/
private abbrev stageMap_irrelevant_quotientMap
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    (G_.obj (OrderDual.toDual (n + 1)) ⧸
        ((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))) →ₗ[A]
      (G_.obj (OrderDual.toDual n) ⧸
        ((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual n))))) :=
  ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
      (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))).mapQ
    ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
      (⊤ : Submodule A (G_.obj (OrderDual.toDual n)))))
    (stageMap G_ n)
    (stageMap_irrelevant_smul_top_le_comap (𝒜 := 𝒜) G_ hG_surj n)

/-- Helper for Lemma 10.98.3: the descended successor map modulo the irrelevant ideal is
surjective. -/
private theorem stageMap_irrelevant_quotientMap_surjective
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    Function.Surjective (stageMap_irrelevant_quotientMap (𝒜 := 𝒜) G_ hG_surj n) := by
  intro y
  obtain ⟨y₀, rfl⟩ :=
    Submodule.mkQ_surjective
      ((((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual n))))) y
  obtain ⟨x, rfl⟩ := hG_surj n y₀
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rfl

/-- Helper for Lemma 10.98.3: the descended successor map modulo the irrelevant ideal has trivial
kernel. -/
private theorem stageMap_irrelevant_quotientMap_ker_eq_bot
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    LinearMap.ker (stageMap_irrelevant_quotientMap (𝒜 := 𝒜) G_ hG_surj n) = ⊥ := by
  -- The kernel computation for `mapQ` reduces injectivity to the already-identified comap.
  rw [Submodule.ker_mapQ]
  rw [stageMap_irrelevant_smul_top_comap_eq (𝒜 := 𝒜) I hI G_ hG_surj hG_ker n]
  simpa using
    (Submodule.mkQ_map_self
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))))

/-- Helper for Lemma 10.98.3: the descended successor map modulo the irrelevant ideal is
injective. -/
private theorem stageMap_irrelevant_quotientMap_injective
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    Function.Injective (stageMap_irrelevant_quotientMap (𝒜 := 𝒜) G_ hG_surj n) :=
  LinearMap.ker_eq_bot.mp
    (stageMap_irrelevant_quotientMap_ker_eq_bot (𝒜 := 𝒜) I hI G_ hG_surj hG_ker n)

private noncomputable def stageMap_irrelevant_quotient_equiv
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    (G_.obj (OrderDual.toDual (n + 1)) ⧸
        ((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))) ≃ₗ[A]
      (G_.obj (OrderDual.toDual n) ⧸
        ((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual n))))) :=
  LinearEquiv.ofBijective
    (stageMap_irrelevant_quotientMap (𝒜 := 𝒜) G_ hG_surj n)
    ⟨stageMap_irrelevant_quotientMap_injective (𝒜 := 𝒜) I hI G_ hG_surj hG_ker n,
      stageMap_irrelevant_quotientMap_surjective (𝒜 := 𝒜) G_ hG_surj n⟩

/-- Helper for Lemma 10.98.3: the irrelevant-quotient successor isomorphism sends a class to the
class of its image under the original successor map. -/
private theorem stageMap_irrelevant_quotient_equiv_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) (x : G_.obj (OrderDual.toDual (n + 1))) :
    stageMap_irrelevant_quotient_equiv
        (𝒜 := 𝒜) I hI G_ hG_surj hG_ker n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (stageMap G_ n x) := by
  -- The quotient equivalence is defined from the descended `mapQ`, so it acts on representatives
  -- exactly by applying the original successor map.
  rfl

/-- Helper for Lemma 10.98.3: a finite homogeneous generating family in stage `1` lifts to a
spanning family in every later stage. -/
private theorem stageMap_irrelevant_quotient_equiv_image_generator_classes
    {ι : Type*}
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (k : ℕ)
    (xk : ι → G_.obj (OrderDual.toDual (natStage k)))
    (xk_succ : ι → G_.obj (OrderDual.toDual (natStage (k + 1))))
    (hx_step : ∀ i, stageMap G_ (natStage k) (xk_succ i) = xk i) :
    let pSucc :
        Submodule A (G_.obj (OrderDual.toDual (natStage (k + 1)))) :=
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (natStage (k + 1))))))
    let pCurr :
        Submodule A (G_.obj (OrderDual.toDual (natStage k))) :=
      (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
        (⊤ : Submodule A (G_.obj (OrderDual.toDual (natStage k)))))
    let e :
        (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) ≃ₗ[A]
          (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr) :=
      stageMap_irrelevant_quotient_equiv
        (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k)
    (e : (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) →ₗ[A]
        (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr)) ''
          ((Submodule.mkQ pSucc) '' Set.range xk_succ) =
      (Submodule.mkQ pCurr) '' Set.range xk := by
  intro pSucc pCurr e
  ext y
  constructor
  · rintro ⟨q, ⟨z, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨xk i, ⟨i, rfl⟩, ?_⟩
    symm
    change
      stageMap_irrelevant_quotient_equiv
          (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k)
          (Submodule.Quotient.mk (xk_succ i)) =
        Submodule.Quotient.mk (xk i)
    rw [stageMap_irrelevant_quotient_equiv_apply_mk
      (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k) (xk_succ i)]
    exact congrArg Submodule.Quotient.mk (hx_step i)
  · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
    refine ⟨Submodule.Quotient.mk (xk_succ i), ?_, ?_⟩
    · exact ⟨xk_succ i, ⟨i, rfl⟩, rfl⟩
    · change
        stageMap_irrelevant_quotient_equiv
            (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k)
            (Submodule.Quotient.mk (xk_succ i)) =
          Submodule.Quotient.mk (xk i)
      rw [stageMap_irrelevant_quotient_equiv_apply_mk
        (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k) (xk_succ i)]
      exact congrArg Submodule.Quotient.mk (hx_step i)

/-- Helper for Lemma 10.98.3: a finite homogeneous generating family in stage `1` lifts to a
spanning family in every later stage. -/
private theorem stage_span_eq_top_of_stage_one_generator_lifts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (g : ι → G_.obj (OrderDual.toDual (natStage 0)))
    (δ : ι → ℤ)
    (hg : ∀ i, g i ∈ 𝒢 (natStage 0) (δ i))
    (hg_span : Submodule.span A (Set.range g) = ⊤)
    (x : ∀ k : ℕ, ι → G_.obj (OrderDual.toDual (natStage k)))
    (hx_zero : ∀ i, x 0 i = g i)
    (hx_deg : ∀ k i, x k i ∈ 𝒢 (natStage k) (δ i))
    (hx_step : ∀ k i, stageMap G_ (natStage k) (x (k + 1) i) = x k i) :
    ∀ k : ℕ, Submodule.span A (Set.range (x k)) = ⊤ := by
  intro k
  induction k with
  | zero =>
      have hrange : Set.range (x 0) = Set.range g := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨i, ?_⟩
          simpa [hx_zero i]
        · rintro ⟨i, rfl⟩
          refine ⟨i, ?_⟩
          simpa [hx_zero i]
      simpa [hrange] using hg_span
  | succ k ih =>
      let pCurr :
          Submodule A (G_.obj (OrderDual.toDual (natStage k))) :=
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (natStage k)))))
      let pSucc :
          Submodule A (G_.obj (OrderDual.toDual (natStage (k + 1)))) :=
        (((𝒜₊ : HomogeneousIdeal 𝒜).toIdeal) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (natStage (k + 1))))))
      let e :
          (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) ≃ₗ[A]
            (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr) :=
        stageMap_irrelevant_quotient_equiv
          (𝒜 := 𝒜) I hI G_ hG_surj hG_ker (natStage k)
      have hk_quot :
          Submodule.span A ((Submodule.mkQ pCurr) '' Set.range (x k)) = ⊤ :=
        quotient_span_eq_top_of_span_eq_top (A := A) pCurr (x k) ih
      have himage :
          (e : (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) →ₗ[A]
              (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr)) ''
            ((Submodule.mkQ pSucc) '' Set.range (x (k + 1))) =
            (Submodule.mkQ pCurr) '' Set.range (x k) := by
        simpa [e, pCurr, pSucc] using
          stageMap_irrelevant_quotient_equiv_image_generator_classes
            (𝒜 := 𝒜) (I := I) hI G_ hG_surj hG_ker k (x k) (x (k + 1)) (hx_step k)
      have hmap_top :
          Submodule.map
              (e : (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) →ₗ[A]
                  (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr))
              (Submodule.span A ((Submodule.mkQ pSucc) '' Set.range (x (k + 1)))) = ⊤ := by
        -- Transport the quotient generators across the irrelevant-quotient isomorphism.
        rw [Submodule.map_span, himage]
        exact hk_quot
      have hquot_top :
          Submodule.span A ((Submodule.mkQ pSucc) '' Set.range (x (k + 1))) = ⊤ := by
        apply top_unique
        intro q hq
        have he_mem :
            (e : (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) →ₗ[A]
                (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr)) q ∈
              Submodule.map
                (e : (G_.obj (OrderDual.toDual (natStage (k + 1))) ⧸ pSucc) →ₗ[A]
                    (G_.obj (OrderDual.toDual (natStage k)) ⧸ pCurr))
                (Submodule.span A ((Submodule.mkQ pSucc) '' Set.range (x (k + 1)))) := by
          rw [hmap_top]
          exact Submodule.mem_top
        rcases he_mem with ⟨q', hq', hqq'⟩
        have : q' = q := e.injective hqq'
        simpa [this] using hq'
      exact span_eq_top_of_quotient_span_eq_top_of_homogeneous_zgraded
        (𝒜 := 𝒜) (ℳ := 𝒢 (natStage (k + 1))) (x := x (k + 1)) (δ := δ)
        (fun i ↦ hx_deg (k + 1) i) hquot_top

/-- Helper for Lemma 10.98.3: successor compatibility already determines every long transition of
the family. -/
private theorem transitionMap_apply_of_successor_compatible
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (v : ∀ n : ℕ+, G_.obj (OrderDual.toDual n))
    (hv : ∀ n : ℕ+, stageMap G_ n (v (n + 1)) = v n)
    {i j : ℕ+} (hij : i ≤ j) :
    transitionMap G_ hij (v j) = v i := by
  let offsetStage : ℕ → ℕ+ := fun k ↦
    ⟨(i : ℕ) + k, Nat.add_pos_left i.2 k⟩
  have hoffset :
      ∀ k : ℕ,
        transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k) (v (offsetStage k)) =
          v i := by
    intro k
    induction k with
    | zero =>
        have hId :
            transitionMap G_ (show i ≤ offsetStage 0 from Nat.le_add_right i 0) =
              (LinearMap.id : G_.obj (OrderDual.toDual i) →ₗ[A] G_.obj (OrderDual.toDual i)) := by
          ext x
          change
            (G_.map (homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl))).hom x = x
          have hhom :
              homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl) =
                𝟙 (OrderDual.toDual i) := by
            exact Subsingleton.elim _ _
          simpa [hhom]
        rw [hId]
        change v (offsetStage 0) = v i
        cases i with
        | mk i hi =>
            simp [offsetStage]
    | succ k ih =>
        have hstep : offsetStage (k + 1) = offsetStage k + 1 := by
          apply Subtype.ext
          rfl
        have hcomp :
            transitionMap G_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1)) =
              (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)).comp
                (stageMap G_ (offsetStage k)) := by
          simpa [hstep] using
            (transitionMap_step_eq_comp G_
              (show i ≤ offsetStage k from Nat.le_add_right i k))
        have hvk :
            stageMap G_ (offsetStage k) (v (offsetStage (k + 1))) = v (offsetStage k) := by
          simpa [hstep] using hv (offsetStage k)
        calc
          transitionMap G_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1))
              (v (offsetStage (k + 1))) =
            transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)
              (stageMap G_ (offsetStage k) (v (offsetStage (k + 1)))) := by
                rw [hcomp]
                rfl
          _ =
            transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)
              (v (offsetStage k)) := by
                rw [hvk]
          _ = v i := ih
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = offsetStage k := by
    apply Subtype.ext
    simpa [offsetStage] using hk
  subst hj
  simpa using hoffset k

/-- Helper for Lemma 10.98.3: a successor-compatible family of stage elements determines an
element of the inverse limit. -/
private theorem exists_limit_element_of_successor_compatible
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (v : ∀ n : ℕ+, G_.obj (OrderDual.toDual n))
    (hv : ∀ n : ℕ+, stageMap G_ n (v (n + 1)) = v n) :
    ∃ x : (limit G_ : ModuleCat.{w} A), ∀ n : ℕ+, limitProjection G_ n x = v n := by
  let F := G_ ⋙ forget (ModuleCat.{w} A)
  let sec : F.sections :=
    ⟨fun i ↦ v (OrderDual.ofDual i), by
      intro i j f
      -- Reinterpret the diagram morphism as a long transition and use compatibility of `v`.
      simpa [F, transitionMap] using
        transitionMap_apply_of_successor_compatible
          (G_ := G_) v hv
          (i := OrderDual.ofDual j)
          (j := OrderDual.ofDual i)
          (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)⟩
  let y : limit F := (Types.limitEquivSections F).symm sec
  refine ⟨(preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y, ?_⟩
  intro n
  have hπ :=
    congrArg
      (fun g ↦ g ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y))
      (preservesLimitIso_hom_π
        (G := forget (ModuleCat.{w} A)) (F := G_) (j := OrderDual.toDual n))
  have hsec_eval :
      limit.π F (OrderDual.toDual n) y = (sec : ∀ j, F.obj j) (OrderDual.toDual n) := by
    simpa [y] using
      (Types.limitEquivSections_symm_apply (F := F) (x := sec) (j := OrderDual.toDual n))
  have hy :
      limit.π F (OrderDual.toDual n) y = v n := by
    simpa [sec] using hsec_eval
  have hproj0 :
      limitProjection G_ n ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        ((forget (ModuleCat.{w} A)).map (limit.π G_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) := by
    rfl
  have hproj1 :
      ((forget (ModuleCat.{w} A)).map (limit.π G_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) := by
    exact hπ.symm
  have hproj2 :
      ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        limit.π F (OrderDual.toDual n) y := by
    simp
  exact hproj0.trans (hproj1.trans (hproj2.trans hy))

/-- Helper for Lemma 10.98.3: every long transition map is surjective once the successor maps are
surjective. -/
private theorem transitionMap_surjective_of_successive_ideal_power_quotients_univ
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    {i j : ℕ+} (hij : i ≤ j) :
    Function.Surjective (transitionMap G_ hij) := by
  let offsetStage : ℕ → ℕ+ := fun k ↦
    ⟨(i : ℕ) + k, Nat.add_pos_left i.2 k⟩
  have hoffset :
      ∀ k : ℕ,
        Function.Surjective
          (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)) := by
    intro k
    induction k with
    | zero =>
        -- Offset `0` is the identity transition from stage `i` to itself.
        have hId :
            transitionMap G_ (show i ≤ offsetStage 0 from Nat.le_add_right i 0) =
              (LinearMap.id : G_.obj (OrderDual.toDual i) →ₗ[A] G_.obj (OrderDual.toDual i)) := by
          ext x
          change
            (G_.map (homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl))).hom x = x
          have hhom :
              homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl) =
                𝟙 (OrderDual.toDual i) := by
            exact Subsingleton.elim _ _
          simpa [hhom]
        rw [hId]
        exact fun x ↦ ⟨x, rfl⟩
    | succ k ih =>
        -- A long transition factors through the last successor map.
        have hstep : offsetStage (k + 1) = offsetStage k + 1 := by
          apply Subtype.ext
          rfl
        have hcomp :
            transitionMap G_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1)) =
              (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)).comp
                (stageMap G_ (offsetStage k)) := by
          simpa [hstep] using
            (transitionMap_step_eq_comp G_
              (show i ≤ offsetStage k from Nat.le_add_right i k))
        rw [hcomp]
        exact ih.comp (by simpa [stageMap] using hG_surj (offsetStage k))
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = offsetStage k := by
    apply Subtype.ext
    simpa [offsetStage] using hk
  subst hj
  simpa using hoffset k

/-- Helper for Lemma 10.98.3: every long transition map preserves the fixed grading degree. -/
private theorem transitionMap_mapsTo_zgraded
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    (h𝒢 :
      ∀ (n : ℕ+) (d : ℤ) {x : G_.obj (OrderDual.toDual (n + 1))},
        x ∈ 𝒢 (n + 1) d →
          ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) x ∈ 𝒢 n d)
    {i j : ℕ+} (hij : i ≤ j) (d : ℤ) :
    Set.MapsTo (transitionMap G_ hij) (𝒢 j d) (𝒢 i d) := by
  let offsetStage : ℕ → ℕ+ := fun k ↦
    ⟨(i : ℕ) + k, Nat.add_pos_left i.2 k⟩
  have hoffset :
      ∀ k : ℕ,
        Set.MapsTo
          (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k))
          (𝒢 (offsetStage k) d) (𝒢 i d) := by
    intro k
    induction k with
    | zero =>
        intro x hx
        have hId :
            transitionMap G_ (show i ≤ offsetStage 0 from Nat.le_add_right i 0) =
              (LinearMap.id : G_.obj (OrderDual.toDual i) →ₗ[A] G_.obj (OrderDual.toDual i)) := by
          ext z
          change
            (G_.map (homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl))).hom z = z
          have hhom :
              homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl) =
                𝟙 (OrderDual.toDual i) := by
            exact Subsingleton.elim _ _
          simpa [hhom]
        simpa [hId] using hx
    | succ k ih =>
        intro x hx
        have hstepEq : offsetStage (k + 1) = offsetStage k + 1 := by
          apply Subtype.ext
          rfl
        have hstep :
            stageMap G_ (offsetStage k) x ∈ 𝒢 (offsetStage k) d := by
          simpa [stageMap, hstepEq] using h𝒢 (offsetStage k) d hx
        have hcomp :
            transitionMap G_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1)) =
              (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)).comp
                (stageMap G_ (offsetStage k)) := by
          simpa [hstepEq] using
            (transitionMap_step_eq_comp G_
              (show i ≤ offsetStage k from Nat.le_add_right i k))
        -- Proof comment: factor the long transition through the last successor step and apply the
        -- induction hypothesis to the intermediate stage.
        rw [hcomp]
        simpa [LinearMap.comp_apply] using ih hstep
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = offsetStage k := by
    apply Subtype.ext
    simpa [offsetStage] using hk
  subst hj
  simpa using hoffset k

/-- Helper for Lemma 10.98.3: every homogeneous element in an earlier stage has a homogeneous
preimage of the same degree in any later stage. -/
private theorem transitionMap_surjective_on_homogeneous_piece
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    (h𝒢 :
      ∀ (n : ℕ+) (d : ℤ) {x : G_.obj (OrderDual.toDual (n + 1))},
        x ∈ 𝒢 (n + 1) d →
          ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) x ∈ 𝒢 n d)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    {i j : ℕ+} (hij : i ≤ j) (d : ℤ)
    {y : G_.obj (OrderDual.toDual i)} (hy : y ∈ 𝒢 i d) :
    ∃ x : G_.obj (OrderDual.toDual j),
      x ∈ 𝒢 j d ∧ transitionMap G_ hij x = y := by
  obtain ⟨x₀, hx₀⟩ :=
    transitionMap_surjective_of_successive_ideal_power_quotients_univ G_ hG_surj hij y
  have hmaps :
      Set.MapsTo (transitionMap G_ hij) (𝒢 j d) (𝒢 i d) :=
    transitionMap_mapsTo_zgraded G_ 𝒢 h𝒢 hij d
  refine ⟨((DirectSum.decompose (𝒢 j) x₀ d : 𝒢 j d) : _), ?_, ?_⟩
  · exact (DirectSum.decompose (𝒢 j) x₀ d).2
  · -- Proof comment: decompose the arbitrary preimage into its degree-`d` part and use that the
    -- long transition commutes with degree projections.
    calc
      transitionMap G_ hij (((DirectSum.decompose (𝒢 j) x₀ d : 𝒢 j d) : _)) =
          ((DirectSum.decompose (𝒢 i) (transitionMap G_ hij x₀) d : 𝒢 i d) : _) := by
            symm
            exact decompose_map_eq_of_mapsTo_zgraded
              (ℳ := 𝒢 i) (ℕₘ := 𝒢 j) (f := transitionMap G_ hij)
              (fun e ↦ transitionMap_mapsTo_zgraded G_ 𝒢 h𝒢 hij e) x₀ d
      _ = y := by
            rw [hx₀]
            simpa using (DirectSum.decompose_of_mem_same (𝒢 i) hy)

/-- Helper for Lemma 10.98.3: each canonical projection from the inverse limit onto stage `n` is
surjective in the ambient module universe. -/
private theorem limit_projection_surjective_of_successive_ideal_power_quotients_univ
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    Function.Surjective (limitProjection G_ n) := by
  classical
  let F := G_ ⋙ forget (ModuleCat.{w} A)
  have hAllSurj :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j), Function.Surjective (F.map f) := by
    intro i j f
    simpa [F, transitionMap] using
      transitionMap_surjective_of_successive_ideal_power_quotients_univ G_ hG_surj (leOfHom f)
  have hML : F.IsMittagLeffler := by
    -- The underlying set-valued system is Mittag-Leffler because every transition is surjective.
    exact Functor.isMittagLeffler_of_surjective (F := F) hAllSurj
  intro x
  let s : Set (F.obj (OrderDual.toDual n)) := Set.singleton x
  haveI :
      ∀ j : OrderDual ℕ+,
        Nonempty ((F.toPreimages s).obj j) := by
    intro j
    exact F.toPreimages_nonempty_of_surjective s hAllSurj (Set.singleton_nonempty x) j
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_countable_mittagLeffler_inverse_system (A := F.toPreimages s)
      (Functor.IsMittagLeffler.toPreimages (F := F) (s := s) hML)
  let secF : F.sections :=
    ⟨fun j ↦ (sec j).1, fun f ↦ by
      exact congrArg Subtype.val (hsec f)⟩
  let y : limit F := (Types.limitEquivSections F).symm secF
  refine ⟨(preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y, ?_⟩
  have hπ :=
    congrArg
      (fun g ↦ g ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y))
      (preservesLimitIso_hom_π
        (G := forget (ModuleCat.{w} A)) (F := G_) (j := OrderDual.toDual n))
  have hmem : (sec (OrderDual.toDual n)).1 = x := by
    -- Unpack the defining `toPreimages` condition at the identity morphism.
    have hsecMem :
        (sec (OrderDual.toDual n)).1 ∈
          ⋂ f : OrderDual.toDual n ⟶ OrderDual.toDual n, F.map f ⁻¹' s := by
      simpa [Functor.toPreimages_obj] using (sec (OrderDual.toDual n)).2
    rw [Set.mem_iInter] at hsecMem
    have hid := hsecMem (𝟙 (OrderDual.toDual n))
    simpa [s] using hid
  have hsec_eval :
      limit.π F (OrderDual.toDual n) y = (secF : ∀ j, F.obj j) (OrderDual.toDual n) := by
    simpa [y] using
      (Types.limitEquivSections_symm_apply (F := F) (x := secF) (j := OrderDual.toDual n))
  have hy :
      limit.π F (OrderDual.toDual n) y = x := by
    -- Evaluate the chosen section at stage `n` and use the defining singleton condition.
    simpa [secF, hmem] using hsec_eval
  have hproj0 :
      limitProjection G_ n ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        ((forget (ModuleCat.{w} A)).map (limit.π G_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) := by
    rfl
  have hproj1 :
      ((forget (ModuleCat.{w} A)).map (limit.π G_ (OrderDual.toDual n)))
          ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) := by
    exact hπ.symm
  have hproj2 :
      ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).hom ≫
          limit.π F (OrderDual.toDual n))
            ((preservesLimitIso (forget (ModuleCat.{w} A)) G_).inv y) =
        limit.π F (OrderDual.toDual n) y := by
    simp
  exact hproj0.trans (hproj1.trans (hproj2.trans hy))

/-- Helper for Lemma 10.98.3: the descended quotient-stage map is surjective in the ambient
module universe. -/
private theorem limit_projection_quotient_desc_surjective_of_successive_ideal_power_quotients_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    Function.Surjective
      (limit_projection_quotient_desc_univ
        (𝒜 := 𝒜) I G_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) I G_ hG_surj hG_ker)
        n) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
      (𝒜 := 𝒜) I G_ hG_surj hG_ker
  intro x
  rcases
      limit_projection_surjective_of_successive_ideal_power_quotients_univ
        (A := A) (G_ := G_) hG_surj n x with
    ⟨y, rfl⟩
  refine ⟨Submodule.Quotient.mk y, ?_⟩
  simpa [hStage] using
    congrArg (fun g ↦ g y)
      (limit_projection_quotient_desc_univ_comp_mkQ (𝒜 := 𝒜) I G_ hStage n)

/-- Helper for Lemma 10.98.3: the source identity
`N_{n + 1} + I ^ n (\varprojlim G_i) = N_n` for the kernels of the limit projections in the
ambient module universe. -/
private theorem limit_projection_ker_succ_sup_pow_smul_top_of_successive_ideal_power_quotients_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    LinearMap.ker (limitProjection G_ (n + 1)) ⊔
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)) =
      LinearMap.ker (limitProjection G_ n) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
      (𝒜 := 𝒜) I G_ hG_surj hG_ker
  apply le_antisymm
  · -- Proof comment: each summand on the left already maps to zero in stage `n`.
    rw [sup_le_iff]
    constructor
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      calc
        limitProjection G_ n x =
            stageMap G_ n (limitProjection G_ (n + 1) x) := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun g ↦ g x) (stageMap_comp_limitProjection_eq G_ n).symm
        _ = stageMap G_ n 0 := by rw [hx]
        _ = 0 := by exact map_zero (stageMap G_ n)
    · exact limit_projection_pow_smul_top_le_ker_univ (𝒜 := 𝒜) I G_ hStage n
  · intro x hx
    -- Proof comment: split `x` by lifting its stage-`n + 1` coordinate from the ideal-power
    -- summand, mirroring the source proof of Lemma `10.98.2`.
    have hxstage :
        limitProjection G_ (n + 1) x ∈
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
      have hxker :
          limitProjection G_ (n + 1) x ∈ LinearMap.ker (stageMap G_ n) := by
        rw [LinearMap.mem_ker]
        rw [LinearMap.mem_ker] at hx
        calc
          stageMap G_ n (limitProjection G_ (n + 1) x) =
              limitProjection G_ n x := by
                simpa [LinearMap.comp_apply] using
                  congrArg (fun g ↦ g x) (stageMap_comp_limitProjection_eq G_ n)
          _ = 0 := hx
      rw [show LinearMap.ker (stageMap G_ n) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) by
            simpa [stageMap] using hG_ker n] at hxker
      exact hxker
    have hmap :
        limitProjection G_ (n + 1) x ∈
          Submodule.map (limitProjection G_ (n + 1))
            (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) := by
      have hmap_smul :
          Submodule.map (limitProjection G_ (n + 1))
              (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) =
            I.toIdeal ^ (n : ℕ) •
              (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
        calc
          Submodule.map (limitProjection G_ (n + 1))
              (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))) =
            I.toIdeal ^ (n : ℕ) •
              Submodule.map (limitProjection G_ (n + 1))
                (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)) := by
                  rw [Submodule.map_smul'']
          _ = I.toIdeal ^ (n : ℕ) • LinearMap.range (limitProjection G_ (n + 1)) := by
                rw [Submodule.map_top]
          _ = I.toIdeal ^ (n : ℕ) •
                (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
                  rw [LinearMap.range_eq_top.2
                    (limit_projection_surjective_of_successive_ideal_power_quotients_univ
                      (A := A) (G_ := G_) hG_surj (n + 1))]
      rw [hmap_smul]
      exact hxstage
    rcases hmap with ⟨y, hyI, hyproj⟩
    refine Submodule.mem_sup.2 ⟨x - y, ?_, y, hyI, by simp⟩
    rw [LinearMap.mem_ker]
    calc
      limitProjection G_ (n + 1) (x - y) =
          limitProjection G_ (n + 1) x - limitProjection G_ (n + 1) y := by
            simpa using (limitProjection G_ (n + 1)).map_sub x y
      _ = 0 := by
            rw [hyproj]
            exact sub_self _

/-- Helper for Lemma 10.98.3: the source identity
`N_{n + 1} + I ^ n M = N_n` makes the successor transition on the quotient kernels surjective in
the ambient module universe. -/
private theorem quotient_desc_kernel_transition_surjective_of_successive_ideal_power_quotients_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    Function.Surjective
      (quotient_desc_kernel_transition_univ
        (𝒜 := 𝒜) I G_
        (stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) I G_ hG_surj hG_ker)
        n) := by
  let hStage :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
      (𝒜 := 𝒜) I G_ hG_surj hG_ker
  intro y
  -- Proof comment: rewrite the lower kernel via `limit_projection_quotient_desc_ker_univ`,
  -- split a representative with the predecessor-kernel decomposition, and descend the higher
  -- kernel element to the required quotient class.
  have hy_map :
      (y :
        ((limit G_ : ModuleCat.{w} A) ⧸
          I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ∈
        Submodule.map
          (Submodule.mkQ
            (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A))))
          (LinearMap.ker (limitProjection G_ n)) := by
    rw [← limit_projection_quotient_desc_ker_univ (𝒜 := 𝒜) I G_ hStage n]
    exact y.2
  rcases hy_map with ⟨x, hxker, hy_eq⟩
  have hxsplit :
      x ∈ LinearMap.ker (limitProjection G_ (n + 1)) ⊔
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)) := by
    rw [limit_projection_ker_succ_sup_pow_smul_top_of_successive_ideal_power_quotients_univ
      (𝒜 := 𝒜) I G_ hG_surj hG_ker n]
    exact hxker
  rcases Submodule.mem_sup.1 hxsplit with ⟨z, hz, w, hw, rfl⟩
  have hz_left :
      Submodule.Quotient.mk z ∈
        LinearMap.ker
          (limit_projection_quotient_desc_univ (𝒜 := 𝒜) I G_ hStage (n + 1)) := by
    rw [limit_projection_quotient_desc_ker_univ (𝒜 := 𝒜) I G_ hStage (n + 1)]
    exact ⟨z, hz, rfl⟩
  refine ⟨⟨Submodule.Quotient.mk z, hz_left⟩, ?_⟩
  apply Subtype.ext
  change
    limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_
      (homOfLE
        (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
      (Submodule.Quotient.mk z) = y.1
  calc
    limit_projection_positive_stage_map_univ (𝒜 := 𝒜) I G_
        (homOfLE
          (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
        (Submodule.Quotient.mk z)
      = Submodule.Quotient.mk z := by
          simpa using
            limit_projection_positive_stage_map_univ_apply_mk
              (𝒜 := 𝒜) I G_
              (homOfLE
                (show OrderDual.toDual (n + 1) ≤ OrderDual.toDual n from pnat_le_succ n))
              z
    _ = Submodule.Quotient.mk (z + w) := by
          exact
            (Submodule.Quotient.eq
              (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))).2 <| by
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_mem hw
    _ = y.1 := hy_eq

/-- Helper for Lemma 10.98.3: a vector killed by a long transition map already lies in the
expected ideal-power submodule at the source stage. -/
private theorem transitionMap_ker_le_pow_smul_top
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    {i j : ℕ+} (hij : i ≤ j)
    {x : G_.obj (OrderDual.toDual j)} (hx : transitionMap G_ hij x = 0) :
    x ∈ I.toIdeal ^ (i : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual j))) := by
  let offsetStage : ℕ → ℕ+ := fun k ↦
    ⟨(i : ℕ) + k, Nat.add_pos_left i.2 k⟩
  have hoffset :
      ∀ k : ℕ, ∀ {y : G_.obj (OrderDual.toDual (offsetStage k))},
        transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k) y = 0 →
          y ∈ I.toIdeal ^ (i : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k)))) := by
    intro k
    induction k with
    | zero =>
        intro y hy
        have hId :
            transitionMap G_ (show i ≤ offsetStage 0 from Nat.le_add_right i 0) =
              (LinearMap.id : G_.obj (OrderDual.toDual i) →ₗ[A] G_.obj (OrderDual.toDual i)) := by
          ext z
          change
            (G_.map (homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl))).hom z = z
          have hhom :
              homOfLE (show OrderDual.toDual i ≤ OrderDual.toDual i from le_rfl) =
                𝟙 (OrderDual.toDual i) := by
            exact Subsingleton.elim _ _
          simpa [hhom]
        have hy_zero : y = 0 := by
          simpa [hId] using hy
        simpa [hy_zero]
    | succ k ih =>
        intro y hy
        have hstep : offsetStage (k + 1) = offsetStage k + 1 := by
          apply Subtype.ext
          rfl
        have hcomp :
            transitionMap G_ (show i ≤ offsetStage (k + 1) from Nat.le_add_right i (k + 1)) =
              (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k)).comp
                (stageMap G_ (offsetStage k)) := by
          simpa [hstep] using
            (transitionMap_step_eq_comp G_
              (show i ≤ offsetStage k from Nat.le_add_right i k))
        rw [hcomp] at hy
        let y' : G_.obj (OrderDual.toDual (offsetStage k + 1)) :=
          Eq.mp (by simp [hstep]) y
        have hy' :
            (transitionMap G_ (show i ≤ offsetStage k from Nat.le_add_right i k))
                (stageMap G_ (offsetStage k) y') = 0 := by
          simpa [y', hstep] using hy
        have hy_stage :
            stageMap G_ (offsetStage k) y' ∈
              I.toIdeal ^ (i : ℕ) •
                (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k)))) :=
          ih hy'
        have hmap :
            Submodule.map (stageMap G_ (offsetStage k))
                (I.toIdeal ^ (i : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1))))) =
              I.toIdeal ^ (i : ℕ) •
                (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k)))) := by
          calc
            Submodule.map (stageMap G_ (offsetStage k))
                (I.toIdeal ^ (i : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1))))) =
                I.toIdeal ^ (i : ℕ) • LinearMap.range (stageMap G_ (offsetStage k)) := by
                  rw [Submodule.map_smul'', Submodule.map_top]
            _ = I.toIdeal ^ (i : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k)))) := by
                  rw [LinearMap.range_eq_top.2 (by simpa [stageMap] using hG_surj (offsetStage k))]
        have hy_lift :
            stageMap G_ (offsetStage k) y' ∈
              Submodule.map (stageMap G_ (offsetStage k))
                (I.toIdeal ^ (i : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1))))) := by
          rw [hmap]
          exact hy_stage
        rcases hy_lift with ⟨z, hz, hz_eq⟩
        have hdiff_ker : y' - z ∈ LinearMap.ker (stageMap G_ (offsetStage k)) := by
          rw [LinearMap.mem_ker]
          calc
            stageMap G_ (offsetStage k) (y' - z) =
                stageMap G_ (offsetStage k) y' - stageMap G_ (offsetStage k) z := by
                  simpa using (stageMap G_ (offsetStage k)).map_sub y' z
            _ = 0 := by rw [hz_eq, sub_self]
        have hdiff_pow_top :
            y' - z ∈ I.toIdeal ^ ((offsetStage k : ℕ) : ℕ) •
              (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) := by
          have hker_eq :
              LinearMap.ker (stageMap G_ (offsetStage k)) =
                I.toIdeal ^ ((offsetStage k : ℕ) : ℕ) •
                  (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) := by
            simpa [stageMap] using hG_ker (offsetStage k)
          exact hker_eq ▸ hdiff_ker
        have hpow_le :
            I.toIdeal ^ ((offsetStage k : ℕ) : ℕ) •
                (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) ≤
              I.toIdeal ^ (i : ℕ) •
                (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) :=
          Submodule.smul_mono_left
            (Ideal.pow_le_pow_right (show (i : ℕ) ≤ ((offsetStage k : ℕ+) : ℕ) from
              Nat.le_add_right i k))
        have hdiff_mem :
            y' - z ∈ I.toIdeal ^ (i : ℕ) •
              (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) :=
          hpow_le hdiff_pow_top
        have hsum :
            (y' - z) + z ∈ I.toIdeal ^ (i : ℕ) •
              (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) :=
          Submodule.add_mem _ hdiff_mem hz
        have hy'_mem :
            y' ∈ I.toIdeal ^ (i : ℕ) •
              (⊤ : Submodule A (G_.obj (OrderDual.toDual (offsetStage k + 1)))) := by
          convert hsum using 1
          exact (sub_add_cancel y' z).symm
        simpa [y', hstep] using hy'_mem
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  have hj : j = offsetStage k := by
    apply Subtype.ext
    simpa [offsetStage] using hk
  subst hj
  simpa using hoffset k hx

/-- Helper for Lemma 10.98.3: every finite stage is small in the ring universe, so the inverse
system can be shrunk into the same universe expected by Lemma `10.98.2`. -/
private theorem stage_small_of_finite
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (i : OrderDual ℕ+) :
    Small.{u} (G_.obj i) := by
  let n : ℕ+ := OrderDual.ofDual i
  -- Reindex the `OrderDual` stage back to `ℕ+` and use finite generation of that stage.
  have hfin : Module.Finite A (G_.obj (OrderDual.toDual n)) := inferInstance
  simpa [n] using (Module.Finite.small A (G_.obj (OrderDual.toDual n)))

/-- Helper for Lemma 10.98.3: conjugating a linear map by `Shrink.linearEquiv` moves it to the
small universe while preserving its algebraic behavior. -/
private abbrev shrinkLinearMap
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Small.{u} M] [Small.{u} N] (f : M →ₗ[A] N) :
    Shrink.{u} M →ₗ[A] Shrink.{u} N :=
  (Shrink.linearEquiv A N).symm.toLinearMap.comp
    (f.comp (Shrink.linearEquiv A M).toLinearMap)

/-- Helper for Lemma 10.98.3: surjectivity is invariant under shrinking the source and target
modules. -/
private theorem shrinkLinearMap_surjective
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Small.{u} M] [Small.{u} N] {f : M →ₗ[A] N} (hf : Function.Surjective f) :
    Function.Surjective (shrinkLinearMap (A := A) f) := by
  intro y
  -- Lift the target element back to the original stage, solve surjectively there, and shrink
  -- the chosen preimage back down.
  obtain ⟨x, hx⟩ := hf ((Shrink.linearEquiv A N) y)
  refine ⟨(Shrink.linearEquiv A M).symm x, ?_⟩
  apply (Shrink.linearEquiv A N).injective
  simpa [shrinkLinearMap] using hx

/-- Helper for Lemma 10.98.3: mapping the kernel of a shrunken map back to the original module
recovers the original kernel. -/
private theorem shrinkLinearMap_ker_map
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Small.{u} M] [Small.{u} N] (f : M →ₗ[A] N) :
    Submodule.map (Shrink.linearEquiv A M).toLinearMap
      (LinearMap.ker (shrinkLinearMap (A := A) f)) =
        LinearMap.ker f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- Apply the inverse shrink equivalence to turn the shrunken kernel equation into the
    -- original one.
    have hx' := congrArg (Shrink.linearEquiv A N) hx
    simpa [shrinkLinearMap] using hx'
  · intro hy
    refine ⟨(Shrink.linearEquiv A M).symm y, ?_, ?_⟩
    · -- The chosen preimage lies in the shrunken kernel because its image in the original module
      -- is already zero.
      apply (Shrink.linearEquiv A N).injective
      simpa [shrinkLinearMap] using hy
    · simp

/-- Helper for Lemma 10.98.3: the shrink equivalence preserves ideal-power submodules of `⊤`. -/
private theorem shrink_pow_smul_top_map_eq
    (J : Ideal A) {M : Type*} [AddCommGroup M] [Module A M] [Small.{u} M] (n : ℕ) :
    Submodule.map (Shrink.linearEquiv A M).toLinearMap
      (J ^ n • (⊤ : Submodule A (Shrink.{u} M))) =
        J ^ n • (⊤ : Submodule A M) := by
  -- The shrink equivalence preserves both `⊤` and ideal scalar multiplication.
  simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 (Shrink.linearEquiv A M).surjective] using
    (Submodule.map_smul'' (I := J ^ n) (N := (⊤ : Submodule A (Shrink.{u} M)))
      (f := (Shrink.linearEquiv A M : Shrink.{u} M →ₗ[A] M)))

/-- Helper for Lemma 10.98.3: the finite inverse system can be shrunk stagewise into
`OrderDual ℕ+ ⥤ ModuleCat A`, which is the exact universe of Lemma `10.98.2`. -/
private def shrinkInverseSystem
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    SmallModuleInverseSystem where
  obj i := by
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    exact ModuleCat.of A (Shrink.{u} (G_.obj i))
  map {i j} f := by
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    letI : Small.{u} (G_.obj j) := stage_small_of_finite (A := A) G_ j
    exact ModuleCat.ofHom (shrinkLinearMap (A := A) (G_.map f).hom)
  map_id := by
    intro i
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    ext x
    simp [shrinkLinearMap]
  map_comp := by
    intro i j k f g
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    letI : Small.{u} (G_.obj j) := stage_small_of_finite (A := A) G_ j
    letI : Small.{u} (G_.obj k) := stage_small_of_finite (A := A) G_ k
    ext x
    simp [shrinkLinearMap]

/-- Helper for Lemma 10.98.3: each shrunken stage is linearly equivalent to the original stage. -/
private abbrev shrinkInverseSystem_stageEquiv
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (i : OrderDual ℕ+) :
    (shrinkInverseSystem (A := A) G_).obj i ≃ₗ[A] G_.obj i := by
  letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
  exact Shrink.linearEquiv A (G_.obj i)

/-- Helper for Lemma 10.98.3: the successor maps in the shrunken system remain surjective. -/
private theorem shrinkInverseSystem_stageMap_surjective
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (n : ℕ+) :
    Function.Surjective
      (((shrinkInverseSystem (A := A) G_).map
          (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) := by
  letI : Small.{u} (G_.obj (OrderDual.toDual (n + 1))) :=
    stage_small_of_finite (A := A) G_ (OrderDual.toDual (n + 1))
  letI : Small.{u} (G_.obj (OrderDual.toDual n)) :=
    stage_small_of_finite (A := A) G_ (OrderDual.toDual n)
  -- The shadow-system successor map is exactly the shrunken original successor map.
  simpa [shrinkInverseSystem, shrinkLinearMap] using
    (shrinkLinearMap_surjective
      (A := A)
      (M := ↑(G_.obj (OrderDual.toDual (n + 1))))
      (N := ↑(G_.obj (OrderDual.toDual n)))
      (f := (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom)
      (by simpa using hG_surj n))

/-- Helper for Lemma 10.98.3: the kernel description for the successor maps transports to the
shrunken inverse system. -/
private theorem shrinkInverseSystem_stageMap_ker
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    LinearMap.ker
        (((shrinkInverseSystem (A := A) G_).map
            (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
      I.toIdeal ^ (n : ℕ) •
        (⊤ : Submodule A ((shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual (n + 1)))) := by
  letI : Small.{u} (G_.obj (OrderDual.toDual (n + 1))) :=
    stage_small_of_finite (A := A) G_ (OrderDual.toDual (n + 1))
  letI : Small.{u} (G_.obj (OrderDual.toDual n)) :=
    stage_small_of_finite (A := A) G_ (OrderDual.toDual n)
  let e :
      ((shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual (n + 1))) ≃ₗ[A]
        G_.obj (OrderDual.toDual (n + 1)) :=
    shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual (n + 1))
  let f :
      G_.obj (OrderDual.toDual (n + 1)) →ₗ[A] G_.obj (OrderDual.toDual n) :=
    (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom
  let fsh :
      ((shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual (n + 1))) →ₗ[A]
        ((shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual n)) :=
    ((shrinkInverseSystem (A := A) G_).map
      (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom
  have hker_map :
      Submodule.map e.toLinearMap (LinearMap.ker fsh) = LinearMap.ker f := by
    -- The shrunken successor map is `shrinkLinearMap f`, so its kernel maps back to `ker f`.
    simpa [e, f, fsh, shrinkInverseSystem_stageEquiv, shrinkInverseSystem, shrinkLinearMap] using
      (shrinkLinearMap_ker_map
        (A := A)
        (M := G_.obj (OrderDual.toDual (n + 1)))
        (N := G_.obj (OrderDual.toDual n))
        f)
  have hpow_map :
      Submodule.map e.toLinearMap
          (I.toIdeal ^ (n : ℕ) •
            (⊤ :
              Submodule A ((shrinkInverseSystem (A := A) G_).obj
                (OrderDual.toDual (n + 1))))) =
        I.toIdeal ^ (n : ℕ) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
    -- The same equivalence also preserves the ideal-power submodule of `⊤`.
    simpa [e, shrinkInverseSystem_stageEquiv, shrinkInverseSystem] using
      (shrink_pow_smul_top_map_eq
        (A := A)
        (J := I.toIdeal)
        (M := G_.obj (OrderDual.toDual (n + 1)))
        (n := (n : ℕ)))
  ext x
  constructor
  · intro hx
    -- Push the kernel membership to the original stage and rewrite it with `hG_ker`.
    have hx_orig : e x ∈ LinearMap.ker f := by
      rw [← hker_map]
      exact ⟨x, hx, rfl⟩
    have hx_pow :
        e x ∈ I.toIdeal ^ (n : ℕ) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
      have hx_orig' :
          e x ∈
            LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) := by
        simpa [f] using hx_orig
      rw [hG_ker n] at hx_orig'
      exact hx_orig'
    rw [← hpow_map] at hx_pow
    rcases hx_pow with ⟨y, hy, hy_eq⟩
    have hyx : y = x := e.injective hy_eq
    simpa [hyx] using hy
  · intro hx
    -- Conversely, push the ideal-power membership forward, use the original kernel formula,
    -- and pull the result back through the shrink equivalence.
    have hx_orig :
        e x ∈ I.toIdeal ^ (n : ℕ) •
          (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))) := by
      rw [← hpow_map]
      exact ⟨x, hx, rfl⟩
    have hx_ker : e x ∈ LinearMap.ker f := by
      have hx_ker' :
          e x ∈
            LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) := by
        rw [hG_ker n]
        exact hx_orig
      simpa [f] using hx_ker'
    rw [← hker_map] at hx_ker
    rcases hx_ker with ⟨y, hy, hy_eq⟩
    have hyx : y = x := e.injective hy_eq
    simpa [hyx] using hy

/-- Helper for Lemma 10.98.3: the stagewise shrink equivalences intertwine the shrunken structure
maps with the original ones. -/
private theorem shrinkInverseSystem_stageEquiv_naturality
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((shrinkInverseSystem_stageEquiv (A := A) G_ j).toLinearMap).comp
        (((shrinkInverseSystem (A := A) G_).map f).hom) =
      ((G_.map f).hom).comp ((shrinkInverseSystem_stageEquiv (A := A) G_ i).toLinearMap) := by
  letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
  letI : Small.{u} (G_.obj j) := stage_small_of_finite (A := A) G_ j
  -- Evaluate the shrunken map on a representative and unfold the conjugation.
  ext x
  change
    (Shrink.linearEquiv A (G_.obj j))
        ((Shrink.linearEquiv A (G_.obj j)).symm
          ((G_.map f).hom ((Shrink.linearEquiv A (G_.obj i)) x))) =
      (G_.map f).hom ((Shrink.linearEquiv A (G_.obj i)) x)
  simpa using
    (Shrink.linearEquiv A (G_.obj j)).apply_symm_apply
      ((G_.map f).hom ((Shrink.linearEquiv A (G_.obj i)) x))

/-- Helper for Lemma 10.98.3: the cone from the shrunken inverse limit to the original system is
pointwise natural after transporting stage projections through the stage shrink equivalences. -/
private theorem shrink_limit_cone_naturality_pointwise
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    {i j : OrderDual ℕ+} (f : i ⟶ j)
    (x : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)) :
    (G_.map f).hom
        (shrinkInverseSystem_stageEquiv (A := A) G_ i
          ((limit.π (shrinkInverseSystem (A := A) G_) i).hom x)) =
      shrinkInverseSystem_stageEquiv (A := A) G_ j
        ((limit.π (shrinkInverseSystem (A := A) G_) j).hom x) := by
  -- First transport the shrunken structure map to the original stage, then use the limit cone
  -- relation in the shrunken system.
  calc
    (G_.map f).hom
        (shrinkInverseSystem_stageEquiv (A := A) G_ i
          ((limit.π (shrinkInverseSystem (A := A) G_) i).hom x)) =
      shrinkInverseSystem_stageEquiv (A := A) G_ j
        (((shrinkInverseSystem (A := A) G_).map f).hom
          ((limit.π (shrinkInverseSystem (A := A) G_) i).hom x)) := by
            simpa [LinearMap.comp_apply] using
              (congrArg
                (fun g ↦ g ((limit.π (shrinkInverseSystem (A := A) G_) i).hom x))
                (shrinkInverseSystem_stageEquiv_naturality (A := A) (G_ := G_) f)).symm
    _ = shrinkInverseSystem_stageEquiv (A := A) G_ j
          ((limit.π (shrinkInverseSystem (A := A) G_) j).hom x) := by
            simpa using
              congrArg (fun g ↦ g.hom x)
                (limit.w (shrinkInverseSystem (A := A) G_) f)

/-- Helper for Lemma 10.98.3: the cone from the original inverse limit to the shrunken system is
pointwise natural after shrinking each stage projection. -/
private theorem unshrink_limit_cone_naturality_pointwise
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    {i j : OrderDual ℕ+} (f : i ⟶ j)
    (x : (limit G_ : ModuleCat.{w} A)) :
    ((shrinkInverseSystem (A := A) G_).map f).hom
        ((shrinkInverseSystem_stageEquiv (A := A) G_ i).symm
          ((limit.π G_ i).hom x)) =
      (shrinkInverseSystem_stageEquiv (A := A) G_ j).symm
        ((limit.π G_ j).hom x) := by
  -- Apply the stage equivalence on the target stage so that the transported naturality equation
  -- reduces to the original limit-cone relation.
  apply (shrinkInverseSystem_stageEquiv (A := A) G_ j).injective
  calc
    shrinkInverseSystem_stageEquiv (A := A) G_ j
        (((shrinkInverseSystem (A := A) G_).map f).hom
          ((shrinkInverseSystem_stageEquiv (A := A) G_ i).symm
            ((limit.π G_ i).hom x))) =
      (G_.map f).hom ((limit.π G_ i).hom x) := by
        simpa [LinearMap.comp_apply] using
          congrArg
            (fun g ↦
              g ((shrinkInverseSystem_stageEquiv (A := A) G_ i).symm
                ((limit.π G_ i).hom x)))
            (shrinkInverseSystem_stageEquiv_naturality (A := A) (G_ := G_) f)
    _ = (limit.π G_ j).hom x := by
          simpa using congrArg (fun g ↦ g.hom x) (limit.w G_ f)
    _ = shrinkInverseSystem_stageEquiv (A := A) G_ j
          ((shrinkInverseSystem_stageEquiv (A := A) G_ j).symm
            ((limit.π G_ j).hom x)) := by
              simp

/-- Helper for Lemma 10.98.3: the inverse limit of the finite stages is still small in the ring
universe, because its stage projections inject it into the product of the shrunken stages. -/
private theorem limit_small_of_finite
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    Small.{u} ↥(limit G_ : ModuleCat.{w} A) := by
  let S : OrderDual ℕ+ → Type u := fun i ↦
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    Shrink.{u} (G_.obj i)
  let f : ↥(limit G_ : ModuleCat.{w} A) → ∀ i : OrderDual ℕ+, S i :=
    fun x i ↦
      letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
      equivShrink (G_.obj i) ((limit.π G_ i).hom x)
  exact small_of_injective (f := f) <| by
    intro x y hxy
    apply CategoryTheory.Limits.Concrete.limit_ext G_ x y
    intro i
    letI : Small.{u} (G_.obj i) := stage_small_of_finite (A := A) G_ i
    exact (equivShrink (G_.obj i)).injective (congrFun hxy i)

/-- Helper for Lemma 10.98.3: the inverse limit of the shrunken system is still small in the
ambient stage universe, because the stage projections embed it into the product of the original
stage carriers. -/
private theorem shrinkInverseSystem_limit_small_of_finite
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    Small.{w} ↥(limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) := by
  let Gsh : OrderDual ℕ+ ⥤ ModuleCat A := shrinkInverseSystem (A := A) G_
  let S : OrderDual ℕ+ → Type w := fun i ↦ G_.obj i
  let f : ↥(limit Gsh : ModuleCat A) → ∀ i : OrderDual ℕ+, S i := fun x i ↦
    (shrinkInverseSystem_stageEquiv (A := A) G_ i) ((limit.π Gsh i).hom x)
  -- Compare two limit points by all stage projections after identifying each shrunken stage with
  -- the original one.
  exact small_of_injective (f := f) <| by
    intro x y hxy
    apply CategoryTheory.Limits.Concrete.limit_ext Gsh x y
    intro i
    exact (shrinkInverseSystem_stageEquiv (A := A) G_ i).injective (congrFun hxy i)

/-- Helper for Lemma 10.98.3: shrinking the two whole inverse limits produces comparison linear
maps with explicit formulas on every stage projection. -/
private theorem shrink_limit_lift_projection_formulas
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    ∃ f : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) →ₗ[A]
        (limit G_ : ModuleCat.{w} A),
      ∃ g : (limit G_ : ModuleCat.{w} A) →ₗ[A]
          (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A),
        (∀ n : ℕ+,
            ∀ x : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A),
              limitProjection G_ n (f x) =
                shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
                  (limitProjection (shrinkInverseSystem (A := A) G_) n x)) ∧
          ∀ n : ℕ+,
            ∀ x : (limit G_ : ModuleCat.{w} A),
              limitProjection (shrinkInverseSystem (A := A) G_) n (g x) =
                (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
                  (limitProjection G_ n x) := by
  let Gsh : OrderDual ℕ+ ⥤ ModuleCat A := shrinkInverseSystem (A := A) G_
  let D : ModuleCat A := limit Gsh
  let L : ModuleCat.{w} A := limit G_
  letI : Small.{w} ↥D := shrinkInverseSystem_limit_small_of_finite (A := A) G_
  letI : Small.{u} ↥L := limit_small_of_finite (A := A) G_
  let shrinkD : ModuleCat.{w} A := ModuleCat.of A (Shrink.{w} D)
  let shrinkL : ModuleCat A := ModuleCat.of A (Shrink.{u} L)
  let φ : ∀ i : OrderDual ℕ+, shrinkD ⟶ G_.obj i := fun i ↦
    ModuleCat.ofHom
      (((shrinkInverseSystem_stageEquiv (A := A) G_ i).toLinearMap).comp
        (((limit.π Gsh i).hom).comp (Shrink.linearEquiv A D).toLinearMap))
  let ψ : ∀ i : OrderDual ℕ+, shrinkL ⟶ Gsh.obj i := fun i ↦
    ModuleCat.ofHom
      (((shrinkInverseSystem_stageEquiv (A := A) G_ i).symm.toLinearMap).comp
        (((limit.π G_ i).hom).comp (Shrink.linearEquiv A L).toLinearMap))
  have hφ :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        φ i ≫ G_.map f = φ j := by
    intro i j f
    ext x
    change
      (G_.map f).hom
          (shrinkInverseSystem_stageEquiv (A := A) G_ i
            ((limit.π Gsh i).hom ((Shrink.linearEquiv A D) x))) =
        shrinkInverseSystem_stageEquiv (A := A) G_ j
          ((limit.π Gsh j).hom ((Shrink.linearEquiv A D) x))
    simpa using
      shrink_limit_cone_naturality_pointwise (A := A) (G_ := G_) f ((Shrink.linearEquiv A D) x)
  have hψ :
      ∀ ⦃i j : OrderDual ℕ+⦄ (f : i ⟶ j),
        ψ i ≫ Gsh.map f = ψ j := by
    intro i j f
    ext x
    change
      (Gsh.map f).hom
          ((shrinkInverseSystem_stageEquiv (A := A) G_ i).symm
            ((limit.π G_ i).hom ((Shrink.linearEquiv A L) x))) =
        (shrinkInverseSystem_stageEquiv (A := A) G_ j).symm
          ((limit.π G_ j).hom ((Shrink.linearEquiv A L) x))
    simpa [Gsh] using
      unshrink_limit_cone_naturality_pointwise
        (A := A) (G_ := G_) f ((Shrink.linearEquiv A L) x)
  let originalCone : Cone G_ :=
    { pt := shrinkD
      π := { app := φ
             naturality := by
               intro i j f
               simpa using (hφ f).symm } }
  let shrunkCone : Cone Gsh :=
    { pt := shrinkL
      π := { app := ψ
             naturality := by
               intro i j f
               simpa using (hψ f).symm } }
  let f₀ : shrinkD ⟶ L := limit.lift G_ originalCone
  let g₀ : shrinkL ⟶ D := limit.lift Gsh shrunkCone
  let f :
      (limit Gsh : ModuleCat A) →ₗ[A] (limit G_ : ModuleCat.{w} A) :=
    f₀.hom.comp (Shrink.linearEquiv A D).symm.toLinearMap
  let g :
      (limit G_ : ModuleCat.{w} A) →ₗ[A] (limit Gsh : ModuleCat A) :=
    g₀.hom.comp (Shrink.linearEquiv A L).symm.toLinearMap
  have hf :
      ∀ n : ℕ+,
        ∀ x : (limit Gsh : ModuleCat A),
          limitProjection G_ n (f x) =
            shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
              (limitProjection Gsh n x) := by
    intro n x
    change
      (limit.π G_ (OrderDual.toDual n)).hom
          (f₀.hom ((Shrink.linearEquiv A D).symm x)) =
        shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
          ((limit.π Gsh (OrderDual.toDual n)).hom x)
    rw [show (limit.π G_ (OrderDual.toDual n)).hom (f₀.hom ((Shrink.linearEquiv A D).symm x)) =
        ((f₀ ≫ limit.π G_ (OrderDual.toDual n)).hom) ((Shrink.linearEquiv A D).symm x) by
          rfl]
    rw [show (f₀ ≫ limit.π G_ (OrderDual.toDual n)) = φ (OrderDual.toDual n) by
          simpa [f₀, originalCone] using limit.lift_π originalCone (OrderDual.toDual n)]
    change
      shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
          ((limit.π Gsh (OrderDual.toDual n)).hom
            ((Shrink.linearEquiv A D) ((Shrink.linearEquiv A D).symm x))) =
        shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
          ((limit.π Gsh (OrderDual.toDual n)).hom x)
    rw [(Shrink.linearEquiv A D).apply_symm_apply x]
  have hg :
      ∀ n : ℕ+,
        ∀ x : (limit G_ : ModuleCat.{w} A),
          limitProjection Gsh n (g x) =
            (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
              (limitProjection G_ n x) := by
    intro n x
    change
      (limit.π Gsh (OrderDual.toDual n)).hom
          (g₀.hom ((Shrink.linearEquiv A L).symm x)) =
        (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
          ((limit.π G_ (OrderDual.toDual n)).hom x)
    rw [show (limit.π Gsh (OrderDual.toDual n)).hom (g₀.hom ((Shrink.linearEquiv A L).symm x)) =
        ((g₀ ≫ limit.π Gsh (OrderDual.toDual n)).hom) ((Shrink.linearEquiv A L).symm x) by
          rfl]
    rw [show (g₀ ≫ limit.π Gsh (OrderDual.toDual n)) = ψ (OrderDual.toDual n) by
          simpa [g₀, shrunkCone] using limit.lift_π shrunkCone (OrderDual.toDual n)]
    change
      (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
          ((limit.π G_ (OrderDual.toDual n)).hom
            ((Shrink.linearEquiv A L) ((Shrink.linearEquiv A L).symm x))) =
        (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
          ((limit.π G_ (OrderDual.toDual n)).hom x)
    rw [(Shrink.linearEquiv A L).apply_symm_apply x]
  exact ⟨f, g, hf, hg⟩

/-- Helper for Lemma 10.98.3: shrinking the inverse system stagewise induces a linear equivalence
of inverse limits, with explicit formulas on every stage projection. -/
private theorem shrinkInverseSystem_limitLinearEquiv_spec
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    ∃ e : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ≃ₗ[A]
        (limit G_ : ModuleCat.{w} A),
      (∀ n : ℕ+,
          ∀ x : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A),
            limitProjection G_ n (e x) =
              shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
                (limitProjection (shrinkInverseSystem (A := A) G_) n x)) ∧
        ∀ n : ℕ+,
          ∀ x : (limit G_ : ModuleCat.{w} A),
            limitProjection (shrinkInverseSystem (A := A) G_) n (e.symm x) =
              (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
                (limitProjection G_ n x) := by
  rcases shrink_limit_lift_projection_formulas (A := A) (G_ := G_) with ⟨f, g, hf, hg⟩
  have hgf : g.comp f = LinearMap.id := by
    ext x
    apply CategoryTheory.Limits.Concrete.limit_ext (shrinkInverseSystem (A := A) G_) (g (f x)) x
    intro i
    let n : ℕ+ := OrderDual.ofDual i
    have hg_i := hg n (f x)
    have hf_i := hf n x
    change
      limitProjection (shrinkInverseSystem (A := A) G_) n (g (f x)) =
        limitProjection (shrinkInverseSystem (A := A) G_) n x
    rw [hg_i, hf_i]
    simp
  have hfg : f.comp g = LinearMap.id := by
    ext x
    apply CategoryTheory.Limits.Concrete.limit_ext G_ (f (g x)) x
    intro i
    let n : ℕ+ := OrderDual.ofDual i
    have hf_i := hf n (g x)
    have hg_i := hg n x
    change limitProjection G_ n (f (g x)) = limitProjection G_ n x
    rw [hf_i, hg_i]
    simp
  let e :
      (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ≃ₗ[A]
        (limit G_ : ModuleCat.{w} A) :=
    LinearEquiv.ofLinear f g hfg hgf
  refine ⟨e, ?_, ?_⟩
  · intro n x
    exact hf n x
  · intro n x
    exact hg n x

/-- Helper for Lemma 10.98.3: the inverse limits of the original and shrunken systems are
identified by transporting each stage projection through `shrinkInverseSystem_stageEquiv`. -/
private noncomputable def shrinkInverseSystem_limitLinearEquiv
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))] :
    (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ≃ₗ[A]
      (limit G_ : ModuleCat.{w} A) :=
  Classical.choose (shrinkInverseSystem_limitLinearEquiv_spec (A := A) G_)

/-- Helper for Lemma 10.98.3: the chosen inverse-limit comparison reads off the original stage
projection by first projecting in the shrunken system and then unshrinking that stage. -/
private theorem shrinkInverseSystem_limitLinearEquiv_apply_projection
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+) (x : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)) :
    limitProjection G_ n (shrinkInverseSystem_limitLinearEquiv (A := A) G_ x) =
      shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)
        (limitProjection (shrinkInverseSystem (A := A) G_) n x) := by
  exact (Classical.choose_spec (shrinkInverseSystem_limitLinearEquiv_spec (A := A) G_)).1 n x

/-- Helper for Lemma 10.98.3: the inverse of the chosen limit comparison recovers the shrunken
stage projection by first projecting in the original system and then shrinking that stage. -/
private theorem shrinkInverseSystem_limitLinearEquiv_symm_apply_projection
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+) (x : (limit G_ : ModuleCat.{w} A)) :
    limitProjection (shrinkInverseSystem (A := A) G_) n
        ((shrinkInverseSystem_limitLinearEquiv (A := A) G_).symm x) =
      (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)).symm
        (limitProjection G_ n x) := by
  exact (Classical.choose_spec (shrinkInverseSystem_limitLinearEquiv_spec (A := A) G_)).2 n x

/-- Helper for Lemma 10.98.3: the inverse-limit shrink equivalence preserves the ideal-power
denominator used in the quotient comparison. -/
private theorem shrinkInverseSystem_limitLinearEquiv_map_pow_smul_top
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+) :
    Submodule.map
        (shrinkInverseSystem_limitLinearEquiv (A := A) G_).toLinearMap
        (I.toIdeal ^ (n : ℕ) •
          (⊤ :
            Submodule A (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A))) =
      I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)) := by
  -- Proof comment: a linear equivalence preserves `⊤`, so it also preserves its ideal-power
  -- scalar multiples by `Submodule.map_smul''`.
  rw [Submodule.map_smul'', Submodule.map_top]
  rw [LinearMap.range_eq_top.2 (shrinkInverseSystem_limitLinearEquiv (A := A) G_).surjective]

/-- Helper for Lemma 10.98.3: shrinking the inverse limit induces the corresponding quotient
equivalence on the `I^n`-power quotients. -/
private noncomputable def shrinkInverseSystem_limitQuotientEquiv
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+) :
    ((limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ⧸
        (I.toIdeal ^ (n : ℕ) •
          (⊤ : Submodule A (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)))) ≃ₗ[A]
      ((limit G_ : ModuleCat.{w} A) ⧸
        (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) :=
  Submodule.Quotient.equiv
    _ _
    (shrinkInverseSystem_limitLinearEquiv (A := A) G_)
    (shrinkInverseSystem_limitLinearEquiv_map_pow_smul_top (𝒜 := 𝒜) (A := A) I G_ n)

/-- Helper for Lemma 10.98.3: the quotient transport through the inverse-limit shrink equivalence
sends a representative to the class of its image. -/
private theorem shrinkInverseSystem_limitQuotientEquiv_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+)
    (x : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)) :
    shrinkInverseSystem_limitQuotientEquiv (𝒜 := 𝒜) (A := A) I G_ n
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (shrinkInverseSystem_limitLinearEquiv (A := A) G_ x) := by
  -- Proof comment: `Submodule.Quotient.equiv` is induced by the underlying linear equivalence.
  simp [shrinkInverseSystem_limitQuotientEquiv]

/-- Helper for Lemma 10.98.3: the inverse quotient transport sends a representative in the
original limit back to the class of its preimage in the shrunken limit. -/
private theorem shrinkInverseSystem_limitQuotientEquiv_symm_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+) (x : (limit G_ : ModuleCat.{w} A)) :
    (shrinkInverseSystem_limitQuotientEquiv (𝒜 := 𝒜) (A := A) I G_ n).symm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((shrinkInverseSystem_limitLinearEquiv (A := A) G_).symm x) := by
  -- Proof comment: after rewriting the inverse quotient equivalence, the computation rule is the
  -- same representative formula for the inverse linear equivalence.
  simp [shrinkInverseSystem_limitQuotientEquiv]

/-- Helper for Lemma 10.98.3: once the shrunken inverse system has the quotient realization with
the expected representative formula, the quotient and stage shrink equivalences transport it back
to the original universe without changing that formula. -/
private theorem unshrink_quotient_stage_equiv_spec
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (n : ℕ+)
    (e_sh :
      ((limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ⧸
          (I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)))) ≃ₗ[A]
        (shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual n))
    (happly :
      ∀ y : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A),
        e_sh (Submodule.Quotient.mk y) =
          limitProjection (shrinkInverseSystem (A := A) G_) n y) :
    ∃ e :
      ((limit G_ : ModuleCat.{w} A) ⧸
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ≃ₗ[A]
        G_.obj (OrderDual.toDual n),
      ∀ x : (limit G_ : ModuleCat.{w} A),
        e (Submodule.Quotient.mk x) = limitProjection G_ n x := by
  let e :
      ((limit G_ : ModuleCat.{w} A) ⧸
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ≃ₗ[A]
        G_.obj (OrderDual.toDual n) :=
    (shrinkInverseSystem_limitQuotientEquiv (𝒜 := 𝒜) (A := A) I G_ n).symm.trans
      (e_sh.trans (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n)))
  refine ⟨e, ?_⟩
  intro x
  -- Proof comment: first rewrite the original quotient class as the class of its shrunken
  -- preimage, then use the shrunken representative formula and finally unshrink the stage
  -- projection.
  change
    (shrinkInverseSystem_stageEquiv (A := A) G_ (OrderDual.toDual n))
        (e_sh
          ((shrinkInverseSystem_limitQuotientEquiv (𝒜 := 𝒜) (A := A) I G_ n).symm
            (Submodule.Quotient.mk x))) =
      limitProjection G_ n x
  rw [shrinkInverseSystem_limitQuotientEquiv_symm_apply_mk (𝒜 := 𝒜) (A := A) I G_ n x]
  rw [happly ((shrinkInverseSystem_limitLinearEquiv (A := A) G_).symm x)]
  rw [shrinkInverseSystem_limitLinearEquiv_symm_apply_projection (A := A) (G_ := G_) n x]
  simp

/-- Helper for Lemma 10.98.3: the quotient-realization equivalence from Lemma `10.98.2`
packaged on the closed small-universe shrunken inverse system, so the imported theorem can be
applied without reopening the ambient functor-universe mismatch. -/
private theorem shrink_inverse_system_small_quotient_stage_equiv_spec
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ∃ e_sh :
      ((limit (shrinkInverseSystem (A := A) G_) : ModuleCat A) ⧸
          (I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A)))) ≃ₗ[A]
        (shrinkInverseSystem (A := A) G_).obj (OrderDual.toDual n),
      ∀ y : (limit (shrinkInverseSystem (A := A) G_) : ModuleCat A),
        e_sh (Submodule.Quotient.mk y) =
          limitProjection (shrinkInverseSystem (A := A) G_) n y := by
  -- TODO: the remaining blocker is purely functor-universe packaging. A closed theorem needs a
  -- genuine `Functor.{0,0,0,max u 1}` clone of `shrinkInverseSystem`, because using
  -- `let Gsh := shrinkInverseSystem ...` still elaborates as `Functor.{0,u,0,u+1}` and is
  -- rejected before Lemma `10.98.2` can be applied.
  sorry

/-- Helper for Lemma 10.98.3: the quotient-realization equivalence from Lemma `10.98.2`
specialized to this file's `ModuleCat.{w}` inverse system, together with its representative
formula. -/
private theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_spec
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ∃ e :
      ((limit G_ : ModuleCat.{w} A) ⧸
          (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ≃ₗ[A]
        G_.obj (OrderDual.toDual n),
      ∀ x : (limit G_ : ModuleCat.{w} A),
        e (Submodule.Quotient.mk x) = limitProjection G_ n x := by
  rcases
      shrink_inverse_system_small_quotient_stage_equiv_spec
        (𝒜 := 𝒜) (A := A) (I := I) (G_ := G_) hG_surj hG_ker n with
    ⟨e_sh, happly⟩
  -- Route correction: apply Lemma `10.98.2` only to the closed small-universe system `Gsh`, then
  -- transport the resulting stage equivalence back through the existing shrink/unshrink API.
  exact
    unshrink_quotient_stage_equiv_spec
      (𝒜 := 𝒜) (A := A) (I := I) (G_ := G_) n e_sh happly

/-- Helper for Lemma 10.98.3: the quotient-realization equivalence from Lemma `10.98.2`
specialized to this file's `ModuleCat.{w}` inverse system. -/
private noncomputable def inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    ((limit G_ : ModuleCat.{w} A) ⧸
        (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ≃ₗ[A]
      G_.obj (OrderDual.toDual n) :=
  Classical.choose <|
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_spec
      (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n

/-- Helper for Lemma 10.98.3: the transported quotient equivalence still sends the class of an
inverse-limit element to its `n`th stage projection. -/
private theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) (x : (limit G_ : ModuleCat.{w} A)) :
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n (Submodule.Quotient.mk x) =
      limitProjection G_ n x := by
  exact
    (Classical.choose_spec <|
      inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_spec
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n) x

/-- Helper for Lemma 10.98.3: any quotient class represented by a degree-`d` inverse-limit
element is sent by the descended quotient equivalence to degree `d` in stage `n`. -/
private theorem quotient_mem_stage_of_limit_grading_mem
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) (d : ℤ)
    {x :
      (limit G_ : ModuleCat.{w} A) ⧸
        (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))}
    (hx :
      x ∈
        (limit_grading G_ 𝒢 d).map
          ((Submodule.mkQ
              (I.toIdeal ^ (n : ℕ) •
                (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))).restrictScalars ℤ)) :
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n x ∈
      𝒢 n d := by
  rcases hx with ⟨y, hy, rfl⟩
  -- Read the quotient class on the chosen representative and then unpack the definition of the
  -- inverse-limit grading at stage `n`.
  change
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n (Submodule.Quotient.mk y) ∈
      𝒢 n d
  rw [inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
    (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n y]
  exact hy n

/-- Helper for Lemma 10.98.3: the descended quotient equivalences commute with the canonical
quotient transition maps and the successor map of the inverse system. -/
private theorem inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_commSq
    (I : HomogeneousIdeal 𝒜)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1)))))
    (n : ℕ+) :
    CommSq
      (ModuleCat.ofHom
        (AdicCompletion.transitionMap I.toIdeal (limit G_ : ModuleCat.{w} A) (Nat.le_succ (n : ℕ))))
      (ModuleCat.ofHom
        (inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker (n + 1)).toLinearMap)
      (ModuleCat.ofHom
        (inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n).toLinearMap)
      (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))) := by
  refine ⟨?_⟩
  apply ModuleCat.hom_ext_iff.mpr
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    Submodule.mkQ_surjective
      (I.toIdeal ^ ((n + 1 : ℕ+) : ℕ) •
        (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))
      x
  -- Read both sides on a representative and compare them through the limit cone relation.
  change
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n
        (AdicCompletion.transitionMap I.toIdeal (limit G_ : ModuleCat.{w} A)
          (Nat.le_succ (n : ℕ)) (Submodule.Quotient.mk y)) =
      (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom
        (inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker (n + 1)
          (Submodule.Quotient.mk y))
  change
    inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n (Submodule.Quotient.mk y) =
      (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom
        (inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
          (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker (n + 1)
          (Submodule.Quotient.mk y))
  rw [inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
    (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n]
  rw [inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
    (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker (n + 1)]
  simpa [AdicCompletion.transitionMap, stageMap, LinearMap.comp_apply] using
    congrArg (fun g ↦ g y) (stageMap_comp_limitProjection_eq G_ n).symm

/-- Lemma 10.98.3 (1): a surjective inverse system of finite graded `A`-modules whose successive
transition kernels are the graded submodules `I^n N_{n + 1}` is realized by one finite graded
`A`-module. -/
-- Proof sketch: choose compatible homogeneous generators in degree `1`, use graded Nakayama to
-- show that each stage is generated in the same degrees, define the `d`th graded piece of the
-- limit module by the stabilized degree-`d` parts, and identify each stage with the quotient by
-- the corresponding power of `I`.
theorem exists_finite_graded_module_realizing_inverse_system_of_graded_ideal_power_quotients
    (I : HomogeneousIdeal 𝒜)
    (hI : I.toIdeal ≤ (𝒜₊ : HomogeneousIdeal 𝒜).toIdeal)
    (G_ : OrderDual ℕ+ ⥤ ModuleCat.{w} A)
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (G_.obj (OrderDual.toDual n)))
    [∀ n : ℕ+, DirectSum.Decomposition (𝒢 n)]
    [∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    [∀ n : ℕ+, Module.Finite A (G_.obj (OrderDual.toDual n))]
    (h𝒢 :
      ∀ (n : ℕ+) (d : ℤ) {x : G_.obj (OrderDual.toDual (n + 1))},
        x ∈ 𝒢 (n + 1) d →
          ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) x ∈ 𝒢 n d)
    (hG_surj :
      ∀ n : ℕ+, Function.Surjective ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom))
    (hG_ker :
      ∀ n : ℕ+,
        LinearMap.ker ((G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))).hom) =
          I.toIdeal ^ (n : ℕ) •
            (⊤ : Submodule A (G_.obj (OrderDual.toDual (n + 1))))) :
    ∃ (N : ModuleCat.{w} A) (ℳ : ℤ → Submodule ℤ N)
      (_ : DirectSum.Decomposition ℳ) (_ : SetLike.GradedSMul 𝒜 ℳ) (_ : Module.Finite A N)
      (e :
        ∀ n : ℕ+,
          (N ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))) ≃ₗ[A] G_.obj (OrderDual.toDual n)),
        (∀ (n : ℕ+) (d : ℤ) (x : N ⧸ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))),
            e n x ∈ 𝒢 n d ↔
              x ∈
                (ℳ d).map
                  ((Submodule.mkQ (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A N))).restrictScalars
                    ℤ)) ∧
          ∀ n : ℕ+,
            CommSq
              (ModuleCat.ofHom
                (AdicCompletion.transitionMap I.toIdeal N (Nat.le_succ (n : ℕ))))
              (ModuleCat.ofHom (e (n + 1)).toLinearMap)
              (ModuleCat.ofHom (e n).toLinearMap)
              (G_.map (homOfLE (show n ≤ n + 1 from Nat.le_succ n))) := by
  -- Route correction: abandon the shadow-system bridge. The source proof works directly with the
  -- descended maps from `limitProjection`, and the remaining open work is the graded
  -- stabilization argument that upgrades those descended maps to graded isomorphisms.
  let hStage :
      ∀ n : ℕ+,
        I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (G_.obj (OrderDual.toDual n))) = ⊥ :=
    stage_pow_smul_top_eq_bot_of_successive_ideal_power_quotients_univ
      (𝒜 := 𝒜) I G_ hG_surj hG_ker
  let e :
      ∀ n : ℕ+,
        ((limit G_ : ModuleCat.{w} A) ⧸
            (I.toIdeal ^ (n : ℕ) • (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))) ≃ₗ[A]
          G_.obj (OrderDual.toDual n) :=
    fun n ↦
      inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ
        (𝒜 := 𝒜) I G_ hG_surj hG_ker n
  let hDecomp : DirectSum.Decomposition (limit_grading G_ 𝒢) := sorry
  letI : DirectSum.Decomposition (limit_grading G_ 𝒢) := hDecomp
  refine
    ⟨limit G_, limit_grading G_ 𝒢, hDecomp, limit_grading_gradedSmul (𝒜 := 𝒜) G_ 𝒢, ?_,
      e, ?_⟩
  · -- TODO: prove `Module.Finite A (limit G_)` by choosing a finite homogeneous generating set in
    -- stage `1`, lifting it compatibly through the surjective inverse system, and checking in a
    -- cutoff stage that those limit lifts generate every homogeneous element.
    classical
    sorry
  · -- TODO: combine the grading decomposition with
    -- `limit_projection_quotient_desc_univ_comp_mkQ` and the limit-cone relation
    -- `stageMap_comp_limitProjection_eq` to prove the degreewise compatibility and commuting
    -- quotient squares for the descended equivalences `e n`.
    have hgraded :
        ∀ (n : ℕ+) (d : ℤ)
          (x :
            (limit G_ : ModuleCat.{w} A) ⧸
              (I.toIdeal ^ (n : ℕ) •
                (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))),
          e n x ∈ 𝒢 n d ↔
            x ∈
              (limit_grading G_ 𝒢 d).map
                ((Submodule.mkQ
                    (I.toIdeal ^ (n : ℕ) •
                      (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))).restrictScalars ℤ) := by
      classical
      intro n d x
      constructor
      · intro hx
        let q :=
          Submodule.mkQ
            (I.toIdeal ^ (n : ℕ) •
              (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))
        obtain ⟨y, rfl⟩ :=
          Submodule.mkQ_surjective
            (I.toIdeal ^ (n : ℕ) •
              (⊤ : Submodule A (limit G_ : ModuleCat.{w} A)))
            x
        let y_d : limit_grading G_ 𝒢 d := DirectSum.decompose (limit_grading G_ 𝒢) y d
        refine ⟨(y_d : (limit G_ : ModuleCat.{w} A)), y_d.2, ?_⟩
        change q (y_d : (limit G_ : ModuleCat.{w} A)) = q y
        have hy_stage : limitProjection G_ n y ∈ 𝒢 n d := by
          simpa [e, inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
            (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n y] using hx
        let s : Finset ℤ := (DirectSum.decompose (limit_grading G_ 𝒢) y).support
        let comp : ℤ → (limit G_ : ModuleCat.{w} A) := fun i ↦
          ((DirectSum.decompose (limit_grading G_ 𝒢) y i : limit_grading G_ 𝒢 i) :
            (limit G_ : ModuleCat.{w} A))
        have hterm_zero :
            ∀ i ∈ s, i ≠ d → q (comp i) = 0 := by
          intro i hi hid
          have hproj_zero : limitProjection G_ n (comp i) = 0 := by
            calc
              limitProjection G_ n (comp i) =
              ((DirectSum.decompose (𝒢 n) (limitProjection G_ n y) i : 𝒢 n i) : _) := by
                  symm
                  exact decompose_map_eq_of_mapsTo_zgraded
                    (ℳ := 𝒢 n) (ℕₘ := limit_grading G_ 𝒢)
                    (f := limitProjection G_ n)
                    (hf := fun j z hz ↦ hz n)
                    y i
              _ = 0 := by
                    simpa using (DirectSum.decompose_of_mem_ne (𝒢 n) hy_stage hid.symm)
          apply (e n).injective
          simpa [q, e, inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_apply_mk
            (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n (comp i)] using hproj_zero
        have hsumq :
            q y = ∑ i ∈ s, q (comp i) := by
          simpa [s] using
            congrArg q (DirectSum.sum_support_decompose (limit_grading G_ 𝒢) y).symm
        by_cases hd : d ∈ s
        · have hsum_single :
            ∑ i ∈ s, q (comp i) = q (y_d : (limit G_ : ModuleCat.{w} A)) := by
            refine Finset.sum_eq_single_of_mem d hd ?_
            intro i hi hid
            simpa [comp, y_d] using hterm_zero i hi hid
          calc
            q (y_d : (limit G_ : ModuleCat.{w} A)) =
                ∑ i ∈ s, q (comp i) := by
                        symm
                        exact hsum_single
            _ = q y := hsumq.symm
        · have hy_d_zero :
              (y_d : limit_grading G_ 𝒢 d) = 0 := by
            by_contra hy_d_zero
            exact hd (by simpa [s, DFinsupp.mem_support_iff, hy_d_zero])
          have hsum_zero :
            ∑ i ∈ s, q (comp i) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            exact hterm_zero i hi (by
              intro hid
              exact hd (hid ▸ hi))
          calc
            q (y_d : (limit G_ : ModuleCat.{w} A)) = 0 := by
              simpa [hy_d_zero]
            _ = ∑ i ∈ s, q (comp i) := hsum_zero.symm
            _ = q y := hsumq.symm
      · intro hx
        exact quotient_mem_stage_of_limit_grading_mem
          (𝒜 := 𝒜) (A := A) (I := I) (G_ := G_) (𝒢 := 𝒢) hG_surj hG_ker n d hx
    refine ⟨hgraded, ?_⟩
    intro n
    simpa [e] using
      inverseLimitQuotientPowLinearEquiv_of_successive_ideal_power_quotients_univ_commSq
        (𝒜 := 𝒜) (A := A) I G_ hG_surj hG_ker n

end
