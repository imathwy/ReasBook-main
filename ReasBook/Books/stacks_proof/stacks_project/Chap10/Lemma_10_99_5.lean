import StacksProject_2024.Chap10.Lemma_10_82_13
import StacksProject_2024.Chap10.Lemma_10_99_1

open IsLocalRing
open CategoryTheory
open Fin

section CriteriaForFlatness

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable {n : ℕ}
variable {F : Fin (n + 2) → Type v}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
variable [∀ i, IsScalarTower R S (F i)]

/- Domain-style sampling:
* primary domain: finite exact sequences of modules over a local ring map, together with reduction
  modulo the maximal ideal.
* semantic recall (`lean_leansearch`): no stronger existing owner displaced the local
  `ComposableArrows.Exact` packaging, so the repair stays within the same-file head/tail bridges.
* inspected owner declarations:
  `CategoryTheory.ComposableArrows.Exact`,
  `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc`,
  `CategoryTheory.HomologicalComplex.ExactAt`,
  `LinearMap.quotientMapByIdeal`.
* best owner abstraction: the finite family of differentials should be organized by the canonical
  finite-sequence owner `ComposableArrows`, with exactness carried by `ComposableArrows.Exact`;
  the leftmost injectivity clause remains separate source-facing edge data for the augmented
  sequence `0 → F_{n+1} → ⋯ → F₀`.
* primitive data: the maps `d i : F_{i+1} → F_i`, the finite/flat hypotheses on the modules, and
  the reduction modulo `maximalIdeal R`.
* derived API: the finite sequence `finiteSequence d` and the reduced sequence
  `reducedFiniteSequence R d`, together with their owner predicate `.Exact`.
* source/core/bridge triage:
  `source-facing`: the two lemmas about exactness and flat cokernels for a finite sequence of
    `S`-modules;
  `core/canonical`: `ComposableArrows.Exact`;
  `bridge/view`: `finiteSequence` and `reducedFiniteSequence`, which package the displayed maps into
    the canonical owner object.
-/

namespace CriteriaForFlatness

/-- The finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`
attached to the displayed differentials, organized by the canonical owner
`ComposableArrows (ModuleCat S) (n + 1)`. -/
noncomputable abbrev finiteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (F i.rev))
    (fun i ↦ by
      change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom (d i.rev))

variable (R) in
/-- The reduction modulo `maximalIdeal R` of the finite sequence
`F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`,
organized by the same canonical owner `ComposableArrows`. -/
noncomputable abbrev reducedFiniteSequence
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R
        (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev)))))
    (fun i ↦ by
      change
        ModuleCat.of R
            (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
          ModuleCat.of R
            (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom
        (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))

/-- Helper for Lemma 10.99.5: the canonical shortened family
`C, F_n, …, F_0` obtained from
`F_{n+2} ⟶ F_{n+1} ⟶ F_n ⟶ ⋯ ⟶ F_0`
by replacing the leftmost pair with its cokernel `C`. -/
noncomputable abbrev shortenedFamily
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) :
    Fin (n + 2) → Type v :=
  Fin.snoc (fun i : Fin (n + 1) ↦ F i.castSucc.castSucc) C

/-- Helper for Lemma 10.99.5: the last object of the shortened family is the head cokernel `C`. -/
lemma shortenedFamily_last
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)) = C := by
  simp [CriteriaForFlatness.shortenedFamily]

/-- Helper for Lemma 10.99.5: every non-last object of the shortened family is the corresponding
double tail object of the original family. -/
lemma shortenedFamily_castSucc
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) (i : Fin (n + 1)) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc = F i.castSucc.castSucc := by
  -- A `castSucc` coordinate is strictly before the new last coordinate, so it stays in the
  -- original double tail.
  simp [CriteriaForFlatness.shortenedFamily]

/-- Helper for Lemma 10.99.5: the target of the new head map in the shortened family is the
original module immediately to its right. -/
lemma shortenedFamily_head_target
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc =
      F ((Fin.last n).castSucc.castSucc) := by
  -- Specialize the generic cast-successor description to the head position.
  simpa using @CriteriaForFlatness.shortenedFamily_castSucc _ F C (Fin.last n)

/-- Helper for Lemma 10.99.5: the source of the new head map in the shortened family is
the head cokernel `C`. -/
lemma shortenedFamily_head_source
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ = C := by
  -- Move the successor of the last non-head index to the last index of the shortened family.
  rw [Fin.succ_last]
  exact @CriteriaForFlatness.shortenedFamily_last _ F C

/-- Helper for Lemma 10.99.5: the source of each tail map in the shortened family is the
corresponding shifted original source module. -/
lemma shortenedFamily_tail_source
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) (i : Fin n) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ =
      F (succ (castSucc (castSucc i))) := by
  -- Rewrite the shifted source index as a `castSucc` coordinate of the `Fin.snoc` family.
  simp [CriteriaForFlatness.shortenedFamily, ← Fin.castSucc_succ]

/-- Helper for Lemma 10.99.5: the target of each shifted tail map in the shortened family
is the corresponding double-tail object of the original family. -/
lemma shortenedFamily_tail_target
    {n : ℕ} {F : Fin (n + 3) → Type v} (C : Type v) (i : Fin n) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc =
      F (castSucc (castSucc (castSucc i))) := by
  -- Specialize the generic non-last coordinate identity to the shifted target index.
  simpa using @CriteriaForFlatness.shortenedFamily_castSucc _ F C i.castSucc

/-- Helper for Lemma 10.99.5: the shortened family inherits additive commutative group structure
from the original tail objects and the head cokernel. -/
@[reducible]
noncomputable instance shortenedFamilyAddCommGroup
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] {C : Type v} [AddCommGroup C]
    (i : Fin (n + 2)) :
    AddCommGroup (@CriteriaForFlatness.shortenedFamily _ F C i) :=
  @Fin.snoc (n + 1)
    (fun i ↦ AddCommGroup (@CriteriaForFlatness.shortenedFamily _ F C i))
    (fun i ↦
      Equiv.addCommGroup
        (Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i)))
    (Equiv.addCommGroup
      (Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C)))
    i

/-- Helper for Lemma 10.99.5: the cast from the last shortened coordinate to `C`
preserves the already chosen shortened-family addition. -/
lemma shortenedFamilyCastLast_map_add
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] {C : Type v} [AddCommGroup C]
    (x y : @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1))) :
    Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C) (x + y) =
      Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C) x +
        Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C) y := by
  -- Expose the endpoint branch of the transported additive structure, then use the
  -- addition-preserving equivalence attached to the same cast.
  have hAdd :
      (CriteriaForFlatness.shortenedFamilyAddCommGroup  
          (Fin.last (n + 1))).add =
        ((Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C)).add).add := by
    unfold CriteriaForFlatness.shortenedFamilyAddCommGroup
    rw [Fin.snoc_last]
  change Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C)
      ((CriteriaForFlatness.shortenedFamilyAddCommGroup  
        (Fin.last (n + 1))).add x y) = _
  rw [hAdd]
  letI : Add (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1))) :=
    (Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C)).add
  exact AddEquiv.map_add
    (Equiv.addEquiv (Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C))) x y

/-- Helper for Lemma 10.99.5: the cast from a non-last shortened coordinate to the
corresponding original tail coordinate preserves the chosen shortened-family addition. -/
lemma shortenedFamilyCastCastSucc_map_add
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] {C : Type v} [AddCommGroup C]
    (i : Fin (n + 1))
    (x y : @CriteriaForFlatness.shortenedFamily _ F C i.castSucc) :
    Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i) (x + y) =
      Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i) x +
        Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i) y := by
  -- Expose the `castSucc` branch of the transported additive structure before applying the
  -- endpoint cast's additive equivalence.
  have hAdd :
      (CriteriaForFlatness.shortenedFamilyAddCommGroup   i.castSucc).add =
        ((Equiv.cast
          (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i)).add).add := by
    unfold CriteriaForFlatness.shortenedFamilyAddCommGroup
    rw [Fin.snoc_castSucc]
  change Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i)
      ((CriteriaForFlatness.shortenedFamilyAddCommGroup   i.castSucc).add
        x y) = _
  rw [hAdd]
  letI : Add (@CriteriaForFlatness.shortenedFamily _ F C i.castSucc) :=
    (Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i)).add
  exact AddEquiv.map_add
    (Equiv.addEquiv (Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i))) x y

/-- Helper for Lemma 10.99.5: the last shortened coordinate is additively equivalent to
the head cokernel coordinate. -/
noncomputable abbrev shortenedFamilyAddEquiv_last
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] {C : Type v} [AddCommGroup C] :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)) ≃+ C :=
  AddEquiv.mk'
    (Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C))
    (CriteriaForFlatness.shortenedFamilyCastLast_map_add  )

/-- Helper for Lemma 10.99.5: each non-last shortened coordinate is additively equivalent
to the corresponding original double-tail coordinate. -/
noncomputable abbrev shortenedFamilyAddEquiv_castSucc
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] {C : Type v} [AddCommGroup C] (i : Fin (n + 1)) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc ≃+ F i.castSucc.castSucc :=
  AddEquiv.mk'
    (Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i))
    (CriteriaForFlatness.shortenedFamilyCastCastSucc_map_add   i)

/-- Helper for Lemma 10.99.5: scalar towers transport across an additive equivalence
when both scalar actions on the source are the explicit actions transported by the equivalence. -/
lemma addEquiv_isScalarTower_equiv_smul
    {A B : Type v}
    [AddCommMonoid A] [AddCommMonoid B]
    [Module R B] [Module S B] [IsScalarTower R S B]
    (e : A ≃+ B) :
    @IsScalarTower R S A _ (Equiv.smul S e.toEquiv) (Equiv.smul R e.toEquiv) := by
  -- Push the scalar-tower law across the equivalence, where it is exactly the target law.
  refine @IsScalarTower.mk R S A _ (Equiv.smul S e.toEquiv) (Equiv.smul R e.toEquiv) ?_
  intro r s x
  change @SMul.smul S A (Equiv.smul S e.toEquiv) (r • s) x =
    @SMul.smul R A (Equiv.smul R e.toEquiv) r
      (@SMul.smul S A (Equiv.smul S e.toEquiv) s x)
  unfold Equiv.smul
  simp [smul_assoc]

/-- Helper for Lemma 10.99.5: if both module structures on the source are transported
across the same additive equivalence, then the scalar-tower law is transported too. -/
lemma addEquiv_isScalarTower_module
    {A B : Type v}
    [AddCommMonoid A] [AddCommMonoid B]
    [Module R B] [Module S B] [IsScalarTower R S B]
    (e : A ≃+ B) :
    letI : Module S A := e.module S
    letI : Module R A := e.module R
    IsScalarTower R S A := by
  -- Repackage the explicit `Equiv.smul` transfer in the public `AddEquiv.module` spelling.
  exact CriteriaForFlatness.addEquiv_isScalarTower_equiv_smul   e

/-- Helper for Lemma 10.99.5: the shortened family inherits module structure over any base ring
by transporting the endpoint module structures along the same additive equivalences as its
additive structure. -/
@[reducible]
noncomputable instance shortenedFamilyModuleOfRing
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C]
    (i : Fin (n + 2)) :
    Module A (@CriteriaForFlatness.shortenedFamily _ F C i) :=
  @Fin.snoc (n + 1)
    (fun i ↦ Module A (@CriteriaForFlatness.shortenedFamily _ F C i))
    (fun i ↦
      (CriteriaForFlatness.shortenedFamilyAddEquiv_castSucc   i).module A)
    ((CriteriaForFlatness.shortenedFamilyAddEquiv_last  ).module A)
    i

/-- Helper for Lemma 10.99.5: the shortened family inherits its `S`-module structure from the
original tail objects and the head cokernel. -/
noncomputable abbrev shortenedFamilyModule
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (i : Fin (n + 2)) :
    Module S (@CriteriaForFlatness.shortenedFamily _ F C i) :=
  CriteriaForFlatness.shortenedFamilyModuleOfRing    i

/-- Helper for Lemma 10.99.5: the shortened family inherits its `R`-module structure from the
original tail objects and the head cokernel. -/
noncomputable abbrev shortenedFamilyModuleRestrictScalars
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    {C : Type v} [AddCommGroup C] [Module R C]
    (i : Fin (n + 2)) :
    Module R (@CriteriaForFlatness.shortenedFamily _ F C i) :=
  CriteriaForFlatness.shortenedFamilyModuleOfRing    i

/-- Helper for Lemma 10.99.5: scalar towers on the original family and the head cokernel induce
the corresponding scalar tower on the shortened family. -/
noncomputable instance shortenedFamilyIsScalarTower
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (i : Fin (n + 2)) :
    IsScalarTower R S (@CriteriaForFlatness.shortenedFamily _ F C i) := by
  -- Route correction: use the single generic module instance, so the transported `R`- and
  -- `S`-module structures are produced by the same additive equivalence.
  induction i using Fin.lastCases with
  | last =>
      unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
      rw [Fin.snoc_last, Fin.snoc_last]
      exact CriteriaForFlatness.addEquiv_isScalarTower_module  
        (CriteriaForFlatness.shortenedFamilyAddEquiv_last  )
  | cast i =>
      unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact CriteriaForFlatness.addEquiv_isScalarTower_module  
        (CriteriaForFlatness.shortenedFamilyAddEquiv_castSucc   i)

/-- Helper for Lemma 10.99.5: the generic transported `S`-module on the last shortened
endpoint is the module transported by the last endpoint additive equivalence. -/
lemma shortenedFamilyModuleOfRing_last_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] :
    (CriteriaForFlatness.shortenedFamilyModuleOfRing (Fin.last (n + 1)) :
        Module S (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)))) =
      (CriteriaForFlatness.shortenedFamilyAddEquiv_last :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)) ≃+ C).module S := by
  -- Expose the last branch of the generic transported-module instance.
  unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
  rw [Fin.snoc_last]

/-- Helper for Lemma 10.99.5: the generic transported `S`-module on a non-last shortened
endpoint is the module transported by the corresponding endpoint additive equivalence. -/
lemma shortenedFamilyModuleOfRing_castSucc_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] (i : Fin (n + 1)) :
    (CriteriaForFlatness.shortenedFamilyModuleOfRing i.castSucc :
        Module S (@CriteriaForFlatness.shortenedFamily _ F C i.castSucc)) =
      (CriteriaForFlatness.shortenedFamilyAddEquiv_castSucc i :
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc ≃+ F i.castSucc.castSucc).module S := by
  -- Expose the non-last branch of the generic transported-module instance.
  unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
  rw [Fin.snoc_castSucc]

/-- Helper for Lemma 10.99.5: the last shortened-coordinate cast is linear over the
chosen transported module structure. -/
lemma shortenedFamilyCastLast_map_smul
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C]
    (a : A) (x : @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1))) :
    Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C) (a • x) =
      a • Equiv.cast (@CriteriaForFlatness.shortenedFamily_last _ F C) x := by
  -- Expose the last branch of the shortened module instance; its scalar action was transported
  -- by exactly this endpoint cast.
  unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
  rw [Fin.snoc_last]
  simp [Equiv.smul_def, CriteriaForFlatness.shortenedFamilyAddEquiv_last, AddEquiv.mk']

/-- Helper for Lemma 10.99.5: each non-last shortened-coordinate cast is linear over the
chosen transported module structure. -/
lemma shortenedFamilyCastCastSucc_map_smul
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C]
    (i : Fin (n + 1)) (a : A)
    (x : @CriteriaForFlatness.shortenedFamily _ F C i.castSucc) :
    Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i) (a • x) =
      a • Equiv.cast (@CriteriaForFlatness.shortenedFamily_castSucc _ F C i) x := by
  -- Expose the `castSucc` branch of the shortened module instance; its scalar action was
  -- transported by exactly this endpoint cast.
  unfold CriteriaForFlatness.shortenedFamilyModuleOfRing
  rw [Fin.snoc_castSucc]
  simp [Equiv.smul_def, CriteriaForFlatness.shortenedFamilyAddEquiv_castSucc, AddEquiv.mk']

/-- Helper for Lemma 10.99.5: the last shortened coordinate is linearly equivalent to the
head cokernel coordinate. -/
noncomputable abbrev shortenedCastLastLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)) ≃ₗ[A] C :=
  (CriteriaForFlatness.shortenedFamilyAddEquiv_last  ).toLinearEquiv
    (CriteriaForFlatness.shortenedFamilyCastLast_map_smul  )

/-- Helper for Lemma 10.99.5: each non-last shortened coordinate is linearly equivalent
to the corresponding original double-tail coordinate. -/
noncomputable abbrev shortenedCastCastSuccLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] (i : Fin (n + 1)) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc ≃ₗ[A] F i.castSucc.castSucc :=
  (CriteriaForFlatness.shortenedFamilyAddEquiv_castSucc   i).toLinearEquiv
    (CriteriaForFlatness.shortenedFamilyCastCastSucc_map_smul   i)

/-- Helper for Lemma 10.99.5: the source of the shortened head map is linearly equivalent
to the head cokernel coordinate. -/
noncomputable abbrev shortenedHeadSourceLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[A] C :=
  (show
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[A]
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)) from
      LinearEquiv.cast (Fin.succ_last n)).trans
    (CriteriaForFlatness.shortenedCastLastLinearEquiv   )

/-- Helper for Lemma 10.99.5: the target of the shortened head map is linearly equivalent
to the corresponding original double-tail coordinate. -/
noncomputable abbrev shortenedHeadTargetLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[A]
      F ((Fin.last n).castSucc.castSucc) :=
  CriteriaForFlatness.shortenedCastCastSuccLinearEquiv   
    (Fin.last n)

/-- Helper for Lemma 10.99.5: the source of a shortened tail map is linearly equivalent
to the corresponding shifted original source. -/
noncomputable abbrev shortenedTailSourceLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] (i : Fin n) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[A]
      F (succ (castSucc (castSucc i))) :=
  (show
      @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[A]
        @CriteriaForFlatness.shortenedFamily _ F C i.succ.castSucc from
      LinearEquiv.cast (Fin.succ_castSucc i)).trans
    (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv    i.succ)

/-- Helper for Lemma 10.99.5: the target of a shortened tail map is linearly equivalent
to the corresponding shifted original target. -/
noncomputable abbrev shortenedTailTargetLinearEquiv
    {A : Type*} [CommRing A]
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module A (F i)]
    {C : Type v} [AddCommGroup C] [Module A C] (i : Fin n) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[A]
      F (castSucc (castSucc (castSucc i))) :=
  CriteriaForFlatness.shortenedCastCastSuccLinearEquiv    i.castSucc

/-- Helper for Lemma 10.99.5: transport the descended head map to the canonical source and target
objects of the shortened family. -/
noncomputable abbrev shortened_head_map_cast
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc)) :
    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ →ₗ[S]
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc :=
  (CriteriaForFlatness.shortenedHeadTargetLinearEquiv   ).symm.toLinearMap.comp
    (w.comp (CriteriaForFlatness.shortenedHeadSourceLinearEquiv   ).toLinearMap)

/-- Helper for Lemma 10.99.5: transport each original tail differential to the canonical source
and target objects of the shortened family. -/
noncomputable abbrev shortened_tail_map_cast
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
      @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc :=
  (CriteriaForFlatness.shortenedTailTargetLinearEquiv    i).symm.toLinearMap.comp
    ((d i.castSucc.castSucc).comp
      (CriteriaForFlatness.shortenedTailSourceLinearEquiv    i).toLinearMap)

/-- Helper for Lemma 10.99.5: the shortened head map agrees with the original descended
head map after applying the endpoint linear equivalences. -/
lemma shortened_head_map_cast_comm
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (x : @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ) :
    (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
          F ((Fin.last n).castSucc.castSucc))
        ((CriteriaForFlatness.shortened_head_map_cast w :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ →ₗ[S]
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc) x) =
      w ((CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[S] C) x) := by
  -- The head map was defined by conjugating `w` with the endpoint linear equivalences.
  let e :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
        F ((Fin.last n).castSucc.castSucc) :=
    CriteriaForFlatness.shortenedHeadTargetLinearEquiv
  change e (e.symm
      (w ((CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[S] C) x))) =
    w ((CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[S] C) x)
  exact LinearEquiv.apply_symm_apply e _

/-- Helper for Lemma 10.99.5: each shortened tail map agrees with the corresponding
original differential after applying the endpoint linear equivalences. -/
lemma shortened_tail_map_cast_comm
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n)
    (x : @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ) :
    (CriteriaForFlatness.shortenedTailTargetLinearEquiv i :
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[S]
          F (castSucc (castSucc (castSucc i))))
        ((CriteriaForFlatness.shortened_tail_map_cast d i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
              @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc) x) =
      d i.castSucc.castSucc
        ((CriteriaForFlatness.shortenedTailSourceLinearEquiv i :
          @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[S]
            F (succ (castSucc (castSucc i)))) x) := by
  -- The tail map was defined by conjugating the shifted original differential with endpoint
  -- linear equivalences.
  simp [CriteriaForFlatness.shortened_tail_map_cast]

/-- Helper for Lemma 10.99.5: each shortened tail map forms a ladder square with the
corresponding original double-tail differential. -/
lemma shortenedTailMap_ladder
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    (d i.castSucc.castSucc).comp
        (CriteriaForFlatness.shortenedTailSourceLinearEquiv i :
          @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[S]
            F (succ (castSucc (castSucc i)))).toLinearMap =
      (CriteriaForFlatness.shortenedTailTargetLinearEquiv i :
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[S]
          F (castSucc (castSucc (castSucc i)))).toLinearMap.comp
        (CriteriaForFlatness.shortened_tail_map_cast d i :
          @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc) := by
  -- Read the pointwise commutation lemma as an equality of linear maps.
  ext x
  exact (CriteriaForFlatness.shortened_tail_map_cast_comm   d i x).symm

/-- Helper for Lemma 10.99.5: the shortened tail ladder, expressed as a commutative
square in `ModuleCat S`. -/
lemma shortenedTailMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d i :
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
          @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc) ≫
        (CriteriaForFlatness.shortenedTailTargetLinearEquiv i :
          @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[S]
            F (castSucc (castSucc (castSucc i)))).toModuleIso.hom =
      (CriteriaForFlatness.shortenedTailSourceLinearEquiv i :
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[S]
          F (succ (castSucc (castSucc i)))).toModuleIso.hom ≫
        ModuleCat.ofHom (d i.castSucc.castSucc) := by
  -- Promote the linear-map ladder to the categorical square needed by the `δ₀` comparison.
  apply ModuleCat.hom_ext
  exact (CriteriaForFlatness.shortenedTailMap_ladder   d i).symm

/-- Helper for Lemma 10.99.5: the shortened head ladder, expressed as a commutative
square in `ModuleCat S`. -/
lemma shortenedHeadMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc)) :
    ModuleCat.ofHom (CriteriaForFlatness.shortened_head_map_cast   w) ≫
        (CriteriaForFlatness.shortenedHeadTargetLinearEquiv
            ).toModuleIso.hom =
      (CriteriaForFlatness.shortenedHeadSourceLinearEquiv
            ).toModuleIso.hom ≫
        ModuleCat.ofHom w := by
  -- Promote the representative-level commutation of the shortened head map to `ModuleCat`.
  apply ModuleCat.hom_ext
  ext x
  exact CriteriaForFlatness.shortened_head_map_cast_comm   w x

/-- Helper for Chap10 Lemma 10 99 5: the shortened head ladder can be read directly as a
linear-map square between the normalized shortened head map and the raw descended head map. -/
lemma shortenedHeadMap_ladder
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc)) :
    w.comp
        (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[S] C).toLinearMap =
      (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
            F ((Fin.last n).castSucc.castSucc)).toLinearMap.comp
        (CriteriaForFlatness.shortened_head_map_cast   w) := by
  -- Repackage the pointwise endpoint comparison as an equality of linear maps.
  ext x
  exact (CriteriaForFlatness.shortened_head_map_cast_comm   w x).symm

/-- Helper for Chap10 Lemma 10 99 5: the first shortened tail square matches the raw next
differential after rewriting the common middle equivalence at the left endpoint. -/
lemma shortenedFirstTailMap_ladder
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (d ((2 : Fin (n + 3)).rev)).comp
        (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[S]
            F ((Fin.last (n + 1)).castSucc.castSucc)).toLinearMap =
      (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
            F (castSucc (castSucc (castSucc (Fin.last n))))).toLinearMap.comp
        (CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)) := by
  -- Read the endpoint specialization of the generic shortened-tail ladder directly in the
  -- linear-map world, so this lemma does not depend on the later categorical wrapper.
  exact congrArg ModuleCat.Hom.hom <|
    (by
      simpa [Fin.succ_last, Fin.rev_succ,
        CriteriaForFlatness.shortenedTailSourceLinearEquiv,
        CriteriaForFlatness.shortenedHeadTargetLinearEquiv] using
        (show
          ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc) ≫
              (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
                  F (castSucc (castSucc (castSucc (Fin.last n))))).toModuleIso.hom =
            (CriteriaForFlatness.shortenedTailSourceLinearEquiv (Fin.last n) :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ ≃ₗ[S]
                F (succ (castSucc (castSucc (Fin.last n))))).toModuleIso.hom ≫
              ModuleCat.ofHom (d (Fin.last n).castSucc.castSucc) from
          CriteriaForFlatness.shortenedTailMap_ladder_moduleCat d (Fin.last n)).symm)

/-- Helper for Lemma 10.99.5: the first shortened tail square can be written using the
same middle equivalence as the shortened head square. -/
lemma shortenedFirstTailMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[S]
          F ((Fin.last (n + 1)).castSucc.castSucc)).toModuleIso.hom ≫
        ModuleCat.ofHom
          (d ((2 : Fin (n + 3)).rev)) =
      ModuleCat.ofHom
          (CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)) ≫
        (CriteriaForFlatness.shortenedTailTargetLinearEquiv
            (Fin.last n) :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
            F (castSucc (castSucc (castSucc (Fin.last n))))).toModuleIso.hom := by
  -- Route correction: specialize the generic shortened-tail ladder at the endpoint and normalize
  -- the source equivalence so it matches the shortened head-target equivalence.
  simpa [Fin.succ_last, Fin.rev_succ,
    CriteriaForFlatness.shortenedTailSourceLinearEquiv,
    CriteriaForFlatness.shortenedHeadTargetLinearEquiv] using
    (show
      ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc) ≫
          (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
              F (castSucc (castSucc (castSucc (Fin.last n))))).toModuleIso.hom =
        (CriteriaForFlatness.shortenedTailSourceLinearEquiv (Fin.last n) :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ ≃ₗ[S]
            F (succ (castSucc (castSucc (Fin.last n))))).toModuleIso.hom ≫
          ModuleCat.ofHom (d (Fin.last n).castSucc.castSucc) from
      CriteriaForFlatness.shortenedTailMap_ladder_moduleCat d (Fin.last n)).symm

/-- Helper for Lemma 10.99.5: the shortened cokernel row has a canonical differential family,
with the descended head map at the left end and the shifted original tail maps elsewhere. -/
noncomputable abbrev shortenedDifferential
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ∀ i : Fin (n + 1),
      @CriteriaForFlatness.shortenedFamily _ F C i.succ →ₗ[S]
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc :=
  fun i ↦
    show @CriteriaForFlatness.shortenedFamily _ F C i.succ →ₗ[S]
        @CriteriaForFlatness.shortenedFamily _ F C i.castSucc from
      Fin.lastCases
        (CriteriaForFlatness.shortened_head_map_cast   w)
        (fun j ↦ CriteriaForFlatness.shortened_tail_map_cast   d j)
        i

/-- Helper for Lemma 10.99.5: at the left endpoint, the shortened differential is exactly the
cast-normalized descended head map. -/
lemma shortenedDifferential_last
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    CriteriaForFlatness.shortenedDifferential   w d (Fin.last n) =
      CriteriaForFlatness.shortened_head_map_cast   w := by
  -- Evaluate the explicit `Fin.lastCases` description at the left endpoint.
  simp only [CriteriaForFlatness.shortenedDifferential, Fin.lastCases_last]

/-- Helper for Lemma 10.99.5: away from the left endpoint, the shortened differential is the
corresponding cast-normalized original tail map. -/
lemma shortenedDifferential_castSucc
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    CriteriaForFlatness.shortenedDifferential   w d i.castSucc =
      CriteriaForFlatness.shortened_tail_map_cast   d i := by
  -- Read off the `Fin.castSucc` coordinates of the shortened differential.
  simp [CriteriaForFlatness.shortenedDifferential]

/-- Helper for Chap10 Lemma 10 99 5: at the stable reversed tail index, the shortened
differential is exactly the corresponding casted tail map. -/
lemma shortenedDifferential_revCastSucc
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    CriteriaForFlatness.shortenedDifferential w d i.rev.castSucc =
      CriteriaForFlatness.shortened_tail_map_cast d i.rev := by
  -- Move to the off-head branch of `shortenedDifferential` and read off the tail map directly.
  simpa using (CriteriaForFlatness.shortenedDifferential_castSucc w d i.rev)

variable (R) in
/-- Helper for Chap10 Lemma 10 99 5: after reduction modulo `maximalIdeal R`, the shortened
differential at the stable reversed tail index is the reduced casted tail map. -/
lemma reducedShortenedDifferential_revCastSucc
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    (((CriteriaForFlatness.shortenedDifferential w d i.rev.castSucc).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R)) =
      (((CriteriaForFlatness.shortened_tail_map_cast d i.rev).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R)) := by
  -- Reduce the unreduced bridge first; the quotient map respects literal equality of maps.
  rw [CriteriaForFlatness.shortenedDifferential_revCastSucc w d i]

/-- Helper for Chap10 Lemma 10 99 5: the shifted reverse index of the original row matches the
stable `castSucc.castSucc` spelling used by the double-tail owner maps. -/
lemma doubleTail_revCastSuccCastSucc
    {n : ℕ} (i : Fin n) :
    i.succ.succ.rev = i.rev.castSucc.castSucc := by
  -- Normalize the shifted reverse index once; this is the stable spelling used downstream.
  simpa [Fin.rev_succ] using (Fin.rev_succ i.succ)

/-- Helper for Lemma 10.99.5: an `A`-linear equivalence carries `I • ⊤` onto
`I • ⊤`. -/
lemma linearEquiv_map_smul_top
    {A M N : Type*} [CommRing A]
    [AddCommMonoid M] [Module A M]
    [AddCommMonoid N] [Module A N]
    (I : Ideal A) (e : M ≃ₗ[A] N) :
    Submodule.map (e : M →ₗ[A] N) (I • (⊤ : Submodule A M)) =
      I • (⊤ : Submodule A N) := by
  -- Push ideal multiples through the equivalence and use surjectivity for the image of `⊤`.
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

/-- Helper for Lemma 10.99.5: an `A`-linear equivalence induces an equivalence on
quotients by `I • ⊤`. -/
noncomputable abbrev quotientSmulTopLinearEquivOfLinearEquiv
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : M ≃ₗ[A] N) :
    (M ⧸ (I • (⊤ : Submodule A M))) ≃ₗ[A]
      (N ⧸ (I • (⊤ : Submodule A N))) :=
  Submodule.Quotient.equiv _ _ e
    (CriteriaForFlatness.linearEquiv_map_smul_top I e)

/-- Helper for Lemma 10.99.5: the quotient equivalence induced by an `A`-linear
equivalence sends a representative to the corresponding representative. -/
lemma quotientSmulTopLinearEquivOfLinearEquiv_mk
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : M ≃ₗ[A] N) (x : M) :
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv I e
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := by
  -- This is the defining representative computation for `Submodule.Quotient.equiv`.
  simp [CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv]

/-- Helper for Lemma 10.99.5: the quotient equivalence induced by a linear equivalence
sends the quotient map of a representative to the quotient map of its image. -/
lemma quotientSmulTopLinearEquivOfLinearEquiv_mkQ
    {A M N : Type*} [CommRing A]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (I : Ideal A) (e : M ≃ₗ[A] N) (x : M) :
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv I e
        ((I • (⊤ : Submodule A M)).mkQ x) =
      (I • (⊤ : Submodule A N)).mkQ (e x) := by
  -- Rephrase the existing `Submodule.Quotient.mk` computation in `mkQ` notation.
  simpa [Submodule.mkQ_apply] using
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv_mk I e x

/-- Helper for Lemma 10.99.5: after quotienting by `maximalIdeal R • ⊤`, each shortened
tail map still forms the same ladder square with the corresponding reduced original
double-tail differential. -/
lemma reducedShortenedTailMap_ladder
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    (((d i.castSucc.castSucc).restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailSourceLinearEquiv i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[R]
              F (succ (castSucc (castSucc i))))).toLinearMap =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailTargetLinearEquiv i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[R]
              F (castSucc (castSucc (castSucc i))))).toLinearMap.comp
        ((((CriteriaForFlatness.shortened_tail_map_cast d i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
              @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) := by
  -- Compare the two quotient maps on representatives; the endpoint quotient equivalences send
  -- representatives to representatives, so the unreduced tail ladder gives the equality.
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply,
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv_mkQ]
  exact congrArg
    ((maximalIdeal R •
      (⊤ : Submodule R (F (castSucc (castSucc (castSucc i)))))).mkQ)
    (CriteriaForFlatness.shortened_tail_map_cast_comm   d i x).symm

/-- Helper for Lemma 10.99.5: the reduced shortened tail ladder, expressed as a
commutative square in `ModuleCat R`. -/
lemma reducedShortenedTailMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d i :
              @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R))) ≫
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailTargetLinearEquiv i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.castSucc ≃ₗ[R]
              F (castSucc (castSucc (castSucc i))))).toModuleIso.hom =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailSourceLinearEquiv i :
            @CriteriaForFlatness.shortenedFamily _ F C i.castSucc.succ ≃ₗ[R]
              F (succ (castSucc (castSucc i))))).toModuleIso.hom ≫
        ModuleCat.ofHom
          (((d i.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R)) := by
  -- Promote the reduced linear-map ladder to the categorical square used by the reduced `δ₀`
  -- component naturality proof.
  apply ModuleCat.hom_ext
  exact (CriteriaForFlatness.reducedShortenedTailMap_ladder  
      d i).symm

/-- Helper for Lemma 10.99.5: the reduced shortened head ladder, expressed as a
commutative square in `ModuleCat R`. -/
lemma reducedShortenedHeadMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc)) :
    ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_head_map_cast
              w).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R))) ≫
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv
              )).toModuleIso.hom =
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadSourceLinearEquiv
              )).toModuleIso.hom ≫
    ModuleCat.ofHom
          (((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) := by
  -- Compare both quotient maps on representatives; the reduced head square is the representative
  -- level commutation of the shortened head map with the endpoint quotient equivalences.
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply,
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv_mkQ]
  exact congrArg
    ((maximalIdeal R •
      (⊤ : Submodule R (F ((Fin.last n).castSucc.castSucc)))).mkQ)
    (CriteriaForFlatness.shortened_head_map_cast_comm   w x)

/-- Helper for Lemma 10.99.5: the first reduced shortened tail square can be written
using the same middle equivalence as the reduced shortened head square. -/
lemma reducedShortenedFirstTailMap_ladder_moduleCat
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[R]
              F ((Fin.last (n + 1)).castSucc.castSucc))).toModuleIso.hom ≫
        ModuleCat.ofHom
          (((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R)) =
      ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R))) ≫
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[R]
              F (castSucc (castSucc (castSucc (Fin.last n)))))).toModuleIso.hom := by
  -- Route correction: this is the reduced endpoint specialization of the generic reduced tail
  -- ladder, after normalizing the third differential index and the endpoint equivalence.
  simpa [Fin.succ_last, Fin.rev_succ,
    CriteriaForFlatness.shortenedTailSourceLinearEquiv,
    CriteriaForFlatness.shortenedHeadTargetLinearEquiv] using
    (CriteriaForFlatness.reducedShortenedTailMap_ladder_moduleCat
      d (Fin.last n)).symm

/-- Helper for Lemma 10.99.5: after quotienting by `maximalIdeal R • ⊤`, the shortened
head map forms the ladder square with the reduced descended head map. -/
lemma reducedShortenedHeadMap_ladder
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc)) :
    (((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)).toLinearMap) =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
              F ((Fin.last n).castSucc.castSucc))).toLinearMap.comp
        ((((CriteriaForFlatness.shortened_head_map_cast
            w).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) := by
  -- Compare both quotient maps on representatives; the reduced linear-map square is the
  -- representative computation behind the already established `ModuleCat` ladder.
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply,
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv_mkQ]
  exact congrArg
    ((maximalIdeal R •
      (⊤ : Submodule R (F ((Fin.last n).castSucc.castSucc)))).mkQ)
    (CriteriaForFlatness.shortened_head_map_cast_comm   w x).symm

/-- Helper for Chap10 Lemma 10 99 5: after reduction, the first shortened tail square matches
the raw reduced next differential through the same endpoint quotient equivalence as the head map. -/
lemma reducedShortenedFirstTailMap_ladder
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    ((((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R))).comp
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[R]
              F ((Fin.last (n + 1)).castSucc.castSucc))).toLinearMap =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[R]
              F (castSucc (castSucc (castSucc (Fin.last n)))))).toLinearMap.comp
        ((((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) := by
  -- Read the reduced endpoint categorical ladder in the linear-map world once and reuse it
  -- downstream in the exactness transport lemmas.
  exact congrArg ModuleCat.Hom.hom
    (CriteriaForFlatness.reducedShortenedFirstTailMap_ladder_moduleCat d)

/-- Helper for Lemma 10.99.5: an adjacent map in a `δ₀` tail is the corresponding
shifted adjacent map in the original `ComposableArrows` object. -/
lemma composableArrows_delta0_map_succ
    {Cat : Type*} [Category Cat] {m : ℕ} (T : ComposableArrows Cat (m + 1))
    (i : ℕ) (hi : i < m) :
    T.δ₀.map' i (i + 1) = T.map' (i + 1) (i + 2) := by
  -- Both sides are the same functor map after precomposing by the successor functor.
  rfl

/-- Helper for Lemma 10.99.5: the underlying type of each unreduced shortened-tail object
is the corresponding underlying type in the original double tail. -/
lemma shortened_finiteSequence_delta0_obj_type_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    (((CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).obj i :
        Type v) =
      (((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).obj i : Type v) := by
  -- Strip away `ModuleCat` structure and compare only the underlying family indices.
  unfold CriteriaForFlatness.finiteSequence
  change @CriteriaForFlatness.shortenedFamily _ F C i.succ.rev = F (rev (i.succ.succ))
  rw [Fin.rev_succ i, Fin.rev_succ i.succ, Fin.rev_succ i]
  exact @CriteriaForFlatness.shortenedFamily_castSucc _ F C i.rev

/-- Helper for Lemma 10.99.5: after forgetting the descended head, a shortened
unreduced tail object is the cast-successor endpoint of the shortened family. -/
lemma shortenedFiniteSequenceDelta0_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).obj i =
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc) := by
  -- Normalize the two owner projections, leaving only the index identity `succ.rev = rev.castSucc`.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.mkOfObjOfMapSucc_obj,
    Fin.rev_succ]

/-- Helper for Lemma 10.99.5: after forgetting the first two original arrows, the
unreduced tail object is the corresponding double-tail endpoint. -/
lemma shortenedFiniteSequenceDelta0_target_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ModuleCat.of S (F (castSucc (castSucc i.rev))) =
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).obj i := by
  -- Normalize the two successive `δ₀` projections, leaving the same reversed endpoint.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.δ₀Functor_obj_obj,
    ComposableArrows.mkOfObjOfMapSucc_obj, Fin.rev_succ, Fin.rev_succ]

/-- Helper for Lemma 10.99.5: objectwise, the shortened unreduced tail is canonically
isomorphic to the double tail of the original unreduced row. -/
noncomputable abbrev shortenedFiniteSequenceDelta0ComponentIso
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).obj i ≅
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).obj i :=
  eqToIso (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i) ≪≫
    (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv   
      i.rev).toModuleIso ≪≫
    eqToIso (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i)

/-- Helper for Lemma 10.99.5: the unreduced component isomorphism hom is the explicit
`eqToHom ≫ linearEquiv ≫ eqToHom` composite used by the tail ladder square. -/
lemma shortenedFiniteSequenceDelta0ComponentIso_hom_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso
          w d i).hom =
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
          w d i) ≫
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
             i.rev).toModuleIso.hom ≫
        eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
            w d i) := by
  -- Unfold the component isomorphism once so later naturality proofs can rewrite to the owner
  -- level ladder square without simplifying `eqToIso` transports in place.
  rfl

/-- Helper for Lemma 10.99.5: after normalizing the source and target objects, the shortened
component isomorphism hom is the underlying `castSucc.castSucc` linear equivalence. -/
lemma shortenedFiniteSequenceDelta0ComponentIso_hom_eq_normalized
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
          w d i).symm ≫
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso
          w d i).hom ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
          w d i).symm =
      (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
           i.rev).toModuleIso.hom := by
  -- Rewrite the component isomorphism to its explicit owner-level composite before collapsing the
  -- two transport equalities to identities.
  rw [CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso_hom_eq]
  simp [Category.assoc]

/-- Helper for Lemma 10.99.5: after reduction, a shortened tail object is the quotient
of the corresponding cast-successor endpoint of the shortened family. -/
lemma reducedShortenedFiniteSequenceDelta0_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.reducedFiniteSequence R
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).obj i =
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc)))) := by
  -- Normalize the reduced `δ₀` owner object and then rewrite the reversed successor coordinate.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.mkOfObjOfMapSucc_obj]
  have h : i.succ.rev = i.rev.castSucc := by
    simpa using (Fin.rev_succ i)
  exact congrArg
    (fun j : Fin (n + 2) ↦
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C j ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j)))))
    h

/-- Helper for Lemma 10.99.5: after reduction, the original double-tail object is the
quotient of the corresponding double-tail endpoint of the original family. -/
lemma reducedShortenedFiniteSequenceDelta0_target_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ModuleCat.of R
        (F (castSucc (castSucc i.rev)) ⧸
          (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc i.rev)))))) =
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).obj i := by
  -- Normalize the two successive reduced owner projections, leaving the same reversed endpoint.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.δ₀Functor_obj_obj,
    ComposableArrows.mkOfObjOfMapSucc_obj]
  have h : castSucc (castSucc i.rev) = rev (i.succ.succ) := by
    simpa [Fin.rev_succ] using (Fin.rev_succ i.succ).symm
  exact congrArg
    (fun j : Fin (n + 3) ↦
      ModuleCat.of R
        (F j ⧸ (maximalIdeal R • (⊤ : Submodule R (F j)))))
    h

/-- Helper for Lemma 10.99.5: the original unreduced double tail can be written as an
explicit `mkOfObjOfMapSucc` owner in stable reversed indexing form. -/
noncomputable abbrev finiteSequenceDelta0Delta0ExplicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (F (castSucc (castSucc i.rev))))
    (fun i ↦ by
      change ModuleCat.of S (F (castSucc (castSucc i.castSucc.rev))) ⟶
          ModuleCat.of S (F (castSucc (castSucc i.succ.rev)))
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom (d (castSucc (castSucc i.rev))))

/-- Helper for Lemma 10.99.5: each object of the original unreduced double tail is the
corresponding explicit reversed-index double-tail endpoint. -/
lemma finiteSequenceDelta0Delta0_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).obj i =
      ModuleCat.of S (F (castSucc (castSucc i.rev))) := by
  -- Normalize the two successive `δ₀` object projections to the explicit double tail.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.δ₀Functor_obj_obj,
    ComposableArrows.mkOfObjOfMapSucc_obj, Fin.rev_succ, Fin.rev_succ]

/-- Helper for Lemma 10.99.5: the source index of a shortened unreduced `δ₀` tail map has the
stable reversed-index spelling expected by the tail ladder. -/
lemma shortenedFiniteSequenceDelta0_sourceIndex_eq
    {n : ℕ} (i : Fin n) :
    castSucc (rev (castSucc i)) = castSucc (succ (rev i)) := by
  -- Rewrite the `castSucc` reverse index once to the stable `i.rev.succ` form.
  simpa [Fin.rev_castSucc]

/-- Helper for Lemma 10.99.5: the target index of a shortened unreduced `δ₀` tail map has the
stable reversed-index spelling expected by the tail ladder. -/
lemma shortenedFiniteSequenceDelta0_targetIndex_eq
    {n : ℕ} (i : Fin n) :
    castSucc (rev (succ i)) = castSucc (castSucc (rev i)) := by
  -- Rewrite the `succ` reverse index once to the stable `i.rev.castSucc` form.
  simpa [Fin.rev_succ]

/-- Helper for Lemma 10.99.5: the explicit shortened unreduced tail owner has the expected
source object for the stable reversed-index tail map at `i`. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (rev (castSucc i)))) =
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C (succ (castSucc (rev i)))) := by
  -- Normalize the explicit owner source to the `shortened_tail_map_cast` source index.
  exact congrArg
    (fun j : Fin (n + 2) ↦ ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j))
    (by
      simpa [← Fin.castSucc_succ] using
        (CriteriaForFlatness.shortenedFiniteSequenceDelta0_sourceIndex_eq i))

/-- Helper for Lemma 10.99.5: the explicit shortened unreduced tail owner has the expected
target object for the stable reversed-index tail map at `i`. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (castSucc (rev i)))) =
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (rev (succ i)))) := by
  -- Normalize the explicit owner target to the `shortened_tail_map_cast` target index.
  exact congrArg
    (fun j : Fin (n + 2) ↦ ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j))
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0_targetIndex_eq i).symm

/-- Helper for Chap10 Lemma 10 99 5: the explicit shortened-tail source normalization at the
reversed index `i` can be written directly in the `i.castSucc.rev` spelling used by the forgotten
head owner map. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.castSucc.rev.castSucc) =
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.succ) := by
  -- Re-express the explicit owner source equality in the spelling used by the shifted `δ₀` map.
  simpa [Fin.rev_castSucc, Fin.rev_rev, ← Fin.castSucc_succ] using
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq d i)

/-- Helper for Chap10 Lemma 10 99 5: the explicit shortened-tail target normalization at the
reversed index `i` can be written directly in the `i.succ.rev` spelling used by the forgotten
head owner map. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.castSucc) =
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.succ.rev.castSucc) := by
  -- Re-express the explicit owner target equality in the spelling used by the shifted `δ₀` map.
  simpa [Fin.rev_succ] using
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq d i)

/-- Helper for Lemma 10.99.5: the shortened unreduced `δ₀` tail also has an explicit owner
presentation in stable reversed indexing form. -/
noncomputable abbrev shortenedFiniteSequenceDelta0ExplicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat S) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc))
    (fun i ↦
      eqToHom
          (show
            ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (rev (castSucc i)))) =
              ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                (succ (castSucc (rev i)))) from
            CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq d i) ≫
        ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d i.rev) ≫
      eqToHom
          (show
            ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (castSucc (rev i)))) =
              ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                (castSucc (rev (succ i)))) from
            CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq d i))

/-- Helper for Chap10 Lemma 10 99 5: if both displayed maps have already been normalized to the
explicit-tail owner world and the normalized square commutes there, then the original
`ComposableArrows.isoMk` naturality square follows by reassembling the same object transports. -/
lemma componentIsoNaturality_of_normalizedTailSquare
    {Cat : Type*} [Category Cat]
    {X₀ X₁ A₀ A₁ B₀ B₁ Y₀ Y₁ : Cat}
    {f : X₀ ⟶ X₁} {g : Y₀ ⟶ Y₁}
    {f' : A₀ ⟶ A₁} {g' : B₀ ⟶ B₁}
    {e₀ : A₀ ⟶ B₀} {e₁ : A₁ ⟶ B₁}
    (sx₀ : X₀ = A₀) (sx₁ : X₁ = A₁) (ty₀ : B₀ = Y₀) (ty₁ : B₁ = Y₁)
    (hf : eqToHom sx₀.symm ≫ f ≫ eqToHom sx₁ = f')
    (hg : eqToHom ty₀ ≫ g ≫ eqToHom ty₁.symm = g')
    (hcomm : f' ≫ e₁ = e₀ ≫ g') :
    f ≫ (eqToHom sx₁ ≫ e₁ ≫ eqToHom ty₁) =
      (eqToHom sx₀ ≫ e₀ ≫ eqToHom ty₀) ≫ g := by
  -- Collapse the object equalities first; then the target statement is exactly the normalized
  -- square after replacing the two displayed maps by their explicit-tail forms.
  subst sx₀ sx₁ ty₀ ty₁
  have hf' : f = f' := by
    simpa using hf
  have hg' : g = g' := by
    simpa using hg
  simpa [hf', hg', Category.assoc] using hcomm

/-- Helper for Chap10 Lemma 10 99 5: after shifting once into the owner of the shortened
sequence, the forgotten-head map is exactly the explicit reversed-index shortened tail map. -/
lemma shortenedFiniteSequenceShiftedMap_eq_explicitTailOwner
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
      ((CriteriaForFlatness.finiteSequence
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) =
        eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
            d i) ≫
          ModuleCat.ofHom
            (CriteriaForFlatness.shortened_tail_map_cast d i.rev :
              @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.castSucc) ≫
        eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
          d i) := by
  -- Route correction: normalize the shifted forgotten-head map first, so the public `δ₀`
  -- comparison only has to assemble this owner-level formula with the explicit owner read-off.
  rw [CriteriaForFlatness.composableArrows_delta0_map_succ
    (CriteriaForFlatness.finiteSequence (CriteriaForFlatness.shortenedDifferential w d)) i.1 i.2]
  let obj : Fin (n + 2) → ModuleCat S := fun j ↦
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j.rev)
  let mapSucc : ∀ j : Fin (n + 1), obj j.castSucc ⟶ obj j.succ := fun j ↦ by
    change ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j.castSucc.rev) ⟶
      ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j.succ.rev)
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (CriteriaForFlatness.shortenedDifferential w d j.rev)
  change eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
      w d i.castSucc).symm ≫
        (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' (i.1 + 1) (i.1 + 2) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) = _
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc (i.1 + 1)
    (Nat.succ_lt_succ i.2)]
  change eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
      w d i.castSucc).symm ≫
        mapSucc i.succ ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) = _
  simpa [obj, mapSucc, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_succ, Category.assoc,
    CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq,
    CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq,
    CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq_rev,
    CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq_rev] using
    (CriteriaForFlatness.shortenedTailMap_ladder_moduleCat (d := d) (i := i.rev))

/-- Helper for Chap10 Lemma 10 99 5: after shifting twice into the original owner, the double-tail
map is exactly the explicit reversed-index original tail map. -/
lemma doubleTailShiftedMap_eq_explicitTailOwner
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.castSucc) ≫
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).map' i.1 (i.1 + 1) ≫
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- Route correction: normalize the original double-tail owner map before comparing it with the
  -- explicit owner, so later naturality proofs stay in one stable reversed-index spelling.
  rw [CriteriaForFlatness.composableArrows_delta0_map_succ
      ((CriteriaForFlatness.finiteSequence d).δ₀) i.1 i.2,
    CriteriaForFlatness.composableArrows_delta0_map_succ
      (CriteriaForFlatness.finiteSequence d) (i.1 + 1) (Nat.succ_lt_succ i.2)]
  let obj₁ : Fin (n + 3) → ModuleCat S := fun j ↦ ModuleCat.of S (F j.rev)
  let mapSucc₁ : ∀ j : Fin (n + 2), obj₁ j.castSucc ⟶ obj₁ j.succ := fun j ↦ by
    change ModuleCat.of S (F j.castSucc.rev) ⟶ ModuleCat.of S (F j.succ.rev)
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d j.rev)
  let obj₂ : Fin (n + 1) → ModuleCat S := fun j ↦
    ModuleCat.of S (F (castSucc (castSucc j.rev)))
  let mapSucc₂ : ∀ j : Fin n, obj₂ j.castSucc ⟶ obj₂ j.succ := fun j ↦ by
    change ModuleCat.of S (F (castSucc (castSucc j.castSucc.rev))) ⟶
      ModuleCat.of S (F (castSucc (castSucc j.succ.rev)))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d j.rev.castSucc.castSucc)
  change eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
      w d i.castSucc) ≫
        (ComposableArrows.mkOfObjOfMapSucc obj₁ mapSucc₁).map' (i.1 + 2) (i.1 + 3) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      (ComposableArrows.mkOfObjOfMapSucc obj₂ mapSucc₂).map' i.1 (i.1 + 1)
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj₁ mapSucc₁ (i.1 + 2)
      (Nat.succ_lt_succ (Nat.succ_lt_succ i.2)),
    ComposableArrows.mkOfObjOfMapSucc_map_succ obj₂ mapSucc₂ i.1 i.2]
  change eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
      w d i.castSucc) ≫
        mapSucc₁ i.succ.succ ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      mapSucc₂ i
  apply ModuleCat.hom_ext
  ext x
  simpa [obj₁, mapSucc₁, obj₂, mapSucc₂, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_succ,
    Category.assoc, CriteriaForFlatness.doubleTail_revCastSuccCastSucc]

/-- Helper for Chap10 Lemma 10 99 5: after forgetting the descended head, the shortened `δ₀`
map is the explicit reversed-index tail map once both endpoints are rewritten to the stable
explicit-tail owner objects. -/
lemma shortenedFiniteSequenceDelta0_map_eq_explicitTail_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
      ((CriteriaForFlatness.finiteSequence
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) =
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- First rewrite the shifted owner map to the stable explicit-tail formula, then read the
  -- explicit owner map off directly at the same reversed index.
  calc
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
        ((CriteriaForFlatness.finiteSequence
            (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
        eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
          w d i.succ) =
        eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
            d i) ≫
          ModuleCat.ofHom
            (CriteriaForFlatness.shortened_tail_map_cast d i.rev :
              @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.castSucc) ≫
          eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
            d i) := CriteriaForFlatness.shortenedFiniteSequenceShiftedMap_eq_explicitTailOwner
              w d i
    _ = (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i.1 (i.1 + 1) := by
      let obj : Fin (n + 1) → ModuleCat S := fun j ↦
        ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j.rev.castSucc)
      let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦
          eqToHom
              (show
                ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (rev (castSucc j)))) =
                  ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                    (succ (castSucc (rev j)))) from
                CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq d j) ≫
            ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d j.rev) ≫
          eqToHom
              (show
                ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (castSucc (rev j)))) =
                  ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                    (castSucc (rev (succ j)))) from
                CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq d j)
      change eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
          d i) ≫
            ModuleCat.ofHom
              (CriteriaForFlatness.shortened_tail_map_cast d i.rev :
                @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.succ →ₗ[S]
                  @CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc.castSucc) ≫
            eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
              d i) =
          (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.1 (i.1 + 1)
      simpa [obj, mapSucc] using
        (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.1 i.2).symm

lemma shortenedFiniteSequenceDelta0_map_eq_explicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩).symm ≫
      ((CriteriaForFlatness.finiteSequence
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i (i + 1) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩) =
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable `Fin` bridge proved just above.
  simpa using
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0_map_eq_explicitTail_fin
      w d ⟨i, hi⟩)

/-- Helper for Chap10 Lemma 10 99 5: after rewriting the original double-tail endpoints to the
stable reversed-index owner objects, the double-tail map is exactly the explicit-tail owner map. -/
lemma finiteSequenceDelta0Delta0_map_eq_explicitTail_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.castSucc) ≫
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).map' i.1 (i.1 + 1) ≫
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- This is exactly the shifted double-tail comparison proved just above.
  exact CriteriaForFlatness.doubleTailShiftedMap_eq_explicitTailOwner w d i

lemma finiteSequenceDelta0Delta0_map_eq_explicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩) ≫
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).map' i (i + 1) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩).symm =
      (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable `Fin` bridge proved just above.
  simpa using
    (CriteriaForFlatness.finiteSequenceDelta0Delta0_map_eq_explicitTail_fin
      w d ⟨i, hi⟩)

/-- Helper for Chap10 Lemma 10 99 5: in the explicit-tail owner world, the shortened tail map and
the original double-tail map are related by the canonical `castSucc.castSucc` endpoint
equivalences. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_map_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i.rev.1 (i.rev.1 + 1) =
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
          d i.rev) ≫
        ModuleCat.ofHom
          (CriteriaForFlatness.shortened_tail_map_cast d i.rev.rev :
            @CriteriaForFlatness.shortenedFamily _ F C i.rev.rev.castSucc.succ →ₗ[S]
              @CriteriaForFlatness.shortenedFamily _ F C i.rev.rev.castSucc.castSucc) ≫
      eqToHom (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
          d i.rev) := by
  -- Read the explicit-tail owner map directly from `mkOfObjOfMapSucc` at the stable reversed
  -- index, so the right-hand side is literally the stored `mapSucc` formula.
  let obj : Fin (n + 1) → ModuleCat S := fun j ↦
    ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C j.rev.castSucc)
  let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦
      eqToHom
          (show
            ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (rev (castSucc j)))) =
              ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                (succ (castSucc (rev j)))) from
            CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq d j) ≫
        ModuleCat.ofHom (CriteriaForFlatness.shortened_tail_map_cast d j.rev) ≫
      eqToHom
          (show
            ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (castSucc (rev j)))) =
              ModuleCat.of S (@CriteriaForFlatness.shortenedFamily _ F C
                (castSucc (rev (succ j)))) from
            CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq d j)
  -- After unfolding the owner once, `mkOfObjOfMapSucc_map_succ` returns exactly this stored
  -- `mapSucc`, and `Fin.rev_rev` rewrites the remaining index.
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.rev.1 (i.rev.1 + 1) = _
  simpa [obj, mapSucc, Fin.rev_rev] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.rev.1 i.rev.2)

/-- Helper for Chap10 Lemma 10 99 5: the explicit double-tail owner map can also be read directly
at the stable reversed index, so its middle differential is literally `d i.castSucc.castSucc`. -/
lemma finiteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (i : Fin n) :
    ModuleCat.of S (F i.rev.castSucc.rev.castSucc.castSucc) =
      ModuleCat.of S (F i.castSucc.castSucc.succ) := by
  -- Normalize the reversed source object to the direct `castSucc.castSucc` source index.
  exact congrArg (fun j : Fin (n + 3) ↦ ModuleCat.of S (F j))
    (by simp [Fin.rev_castSucc, Fin.rev_rev, ← Fin.castSucc_succ])

/-- Helper for Chap10 Lemma 10 99 5: the explicit double-tail owner target at the reversed index
matches the direct `castSucc.castSucc` target index. -/
lemma finiteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (i : Fin n) :
    ModuleCat.of S (F i.castSucc.castSucc.castSucc) =
      ModuleCat.of S (F i.rev.succ.rev.castSucc.castSucc) := by
  -- Normalize the reversed target object to the direct `castSucc.castSucc` target index.
  exact congrArg (fun j : Fin (n + 3) ↦ ModuleCat.of S (F j))
    (by simp [Fin.rev_succ, Fin.rev_rev, ← Fin.castSucc_succ])

/-- Helper for Chap10 Lemma 10 99 5: the explicit double-tail owner map can also be read directly
at the stable reversed index, with both endpoints rewritten to the direct `castSucc.castSucc`
spelling. -/
lemma finiteSequenceDelta0Delta0ExplicitTail_map_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.rev.1 (i.rev.1 + 1) =
      eqToHom (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev i) ≫
        ModuleCat.ofHom (d i.castSucc.castSucc) ≫
      eqToHom (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev i) := by
  -- Read the explicit double-tail owner map directly from `mkOfObjOfMapSucc`, so the right-hand
  -- side is the stored `castSucc.castSucc` differential at the stable reversed index.
  let obj : Fin (n + 1) → ModuleCat S := fun j ↦
    ModuleCat.of S (F (castSucc (castSucc j.rev)))
  let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦ by
    change ModuleCat.of S (F (castSucc (castSucc j.castSucc.rev))) ⟶
      ModuleCat.of S (F (castSucc (castSucc j.succ.rev)))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d j.rev.castSucc.castSucc)
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.rev.1 (i.rev.1 + 1) = _
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.rev.1 i.rev.2]
  apply ModuleCat.hom_ext
  ext x
  simpa [obj, mapSucc, Fin.rev_rev, Fin.rev_castSucc, Fin.rev_succ, Category.assoc,
    CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev,
    CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev]

/-- Helper for Chap10 Lemma 10 99 5: in the explicit-tail owner world, the normalized ladder
square is proved by splitting on whether the reversed tail index is the endpoint or an interior
index. -/
lemma shortenedFiniteSequenceDelta0ExplicitTail_naturality_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (@CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail
        S _ _ _ n F _ _ C _ _ d).map' i.1 (i.1 + 1) ≫
      (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        i.succ.rev).toModuleIso.hom =
    (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        i.castSucc.rev).toModuleIso.hom ≫
        (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- Rewrite both explicit owner maps to the same reversed-index core formulas, then the target is
  -- exactly the normalized shortened-tail ladder square at `i.rev`.
  have hshort :=
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_map_rev d i.rev)
  have hdouble :=
    (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail_map_rev d i.rev)
  rw [show
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i.1 (i.1 + 1) =
        (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail d).map' i.rev.rev.1
          (i.rev.rev.1 + 1) by simpa [Fin.rev_rev]]
  rw [show
      (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) =
        (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i.rev.rev.1
          (i.rev.rev.1 + 1) by simpa [Fin.rev_rev]]
  rw [hshort, hdouble]
  simpa [Fin.rev_rev, Fin.rev_castSucc, Fin.rev_succ,
    CriteriaForFlatness.shortenedTailSourceLinearEquiv,
    CriteriaForFlatness.shortenedTailTargetLinearEquiv,
    Category.assoc] using
    (CriteriaForFlatness.shortenedTailMap_ladder_moduleCat d i.rev)

lemma shortenedFiniteSequenceDelta0ExplicitTail_naturality
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    (@CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail
        S _ _ _ n F _ _ C _ _ d).map' i (i + 1) ≫
      (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        ((⟨i + 1, Nat.succ_lt_succ hi⟩ : Fin (n + 1)).rev)).toModuleIso.hom =
      (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        ((⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩ : Fin (n + 1)).rev)).toModuleIso.hom ≫
        (CriteriaForFlatness.finiteSequenceDelta0Delta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable `Fin`-indexed normalized ladder square.
  simpa using
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_naturality_fin
      d ⟨i, hi⟩)

/-- Helper for Lemma 10.99.5: the objectwise comparison between the shortened unreduced
`δ₀` tail and the original unreduced double tail satisfies the adjacent commuting squares required
by `ComposableArrows.isoMk`. -/
lemma shortenedFiniteSequenceDelta0ComponentIso_hom_naturality
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    ((CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i (i + 1) ≫
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso
          w d ⟨i + 1, Nat.succ_lt_succ hi⟩).hom =
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso
          w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩).hom ≫
    ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).map' i (i + 1) := by
  -- Reassemble the raw naturality square from the normalized explicit-tail square.
  simpa [CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso_hom_eq, Category.assoc] using
    (CriteriaForFlatness.componentIsoNaturality_of_normalizedTailSquare
      (sx₀ := CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩)
      (sx₁ := CriteriaForFlatness.shortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩)
      (ty₀ := CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩)
      (ty₁ := CriteriaForFlatness.shortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩)
      (e₀ := (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        ((⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩ : Fin (n + 1)).rev)).toModuleIso.hom)
      (e₁ := (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
        ((⟨i + 1, Nat.succ_lt_succ hi⟩ : Fin (n + 1)).rev)).toModuleIso.hom)
      (hf := CriteriaForFlatness.shortenedFiniteSequenceDelta0_map_eq_explicitTail
        w d i hi)
      (hg := CriteriaForFlatness.finiteSequenceDelta0Delta0_map_eq_explicitTail
        w d i hi)
      (hcomm := CriteriaForFlatness.shortenedFiniteSequenceDelta0ExplicitTail_naturality
        w d i hi))

/-- Helper for Lemma 10.99.5: the shortened unreduced tail is canonically isomorphic to
the double tail of the original unreduced finite sequence. -/
noncomputable def shortenedFiniteSequenceDelta0Iso
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.finiteSequence
      (CriteriaForFlatness.shortenedDifferential   w d)).δ₀ ≅
      (CriteriaForFlatness.finiteSequence d).δ₀.δ₀ :=
  -- Package the objectwise comparison by `ComposableArrows.isoMk`; the previous lemma supplies
  -- exactly the adjacent commuting squares.
  ComposableArrows.isoMk
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso
        w d)
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0ComponentIso_hom_naturality
        w d)

/-- Helper for Lemma 10.99.5: after reduction modulo `maximalIdeal R`, each shortened
tail object is canonically isomorphic to the corresponding original double-tail object. -/
noncomputable def reducedShortenedFiniteSequenceDelta0ComponentIso
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.reducedFiniteSequence R
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).obj i ≅
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).obj i :=
  eqToIso (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
          w d i) ≪≫
    (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv   
        i.rev)).toModuleIso ≪≫
    eqToIso (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
          w d i)

/-- Helper for Lemma 10.99.5: the reduced component isomorphism hom is the explicit
`eqToHom ≫ quotientEquiv ≫ eqToHom` composite used by the reduced tail ladder square. -/
lemma reducedShortenedFiniteSequenceDelta0ComponentIso_hom_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso
           w d i).hom =
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
            w d i) ≫
        (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
               i.rev)).toModuleIso.hom ≫
        eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
              w d i) := by
  -- Unfold the reduced component isomorphism once so the reduced naturality proof can reuse the
  -- owner-level reduced tail ladder square directly.
  rfl

/-- Helper for Lemma 10.99.5: after normalizing the source and target objects, the reduced
component isomorphism hom is the quotient linear equivalence induced by the normalized
`castSucc.castSucc` comparison. -/
lemma reducedShortenedFiniteSequenceDelta0ComponentIso_hom_eq_normalized
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
            w d i).symm ≫
      (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso
           w d i).hom ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
            w d i).symm =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
             i.rev)).toModuleIso.hom := by
  -- Rewrite the reduced component isomorphism to the explicit `eqToHom ≫ quotientEquiv ≫ eqToHom`
  -- composite, then simplify the normalized transports away.
  rw [CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso_hom_eq]
  simp [Category.assoc]

/-- Helper for Lemma 10.99.5: the reduced original double tail also has an explicit owner
presentation in the same reversed indexing convention. -/
noncomputable abbrev reducedFiniteSequenceDelta0Delta0ExplicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R
        (F (castSucc (castSucc i.rev)) ⧸
          (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc i.rev)))))))
    (fun i ↦ by
      change
        ModuleCat.of R
            (F (castSucc (castSucc i.castSucc.rev)) ⧸
              (maximalIdeal R •
                (⊤ : Submodule R (F (castSucc (castSucc i.castSucc.rev)))))) ⟶
          ModuleCat.of R
            (F (castSucc (castSucc i.succ.rev)) ⧸
              (maximalIdeal R •
                (⊤ : Submodule R (F (castSucc (castSucc i.succ.rev))))))
      rw [Fin.rev_castSucc, Fin.rev_succ]
      exact ModuleCat.ofHom
        (((d (castSucc (castSucc i.rev))).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))

/-- Helper for Lemma 10.99.5: each object of the original reduced double tail is the
corresponding explicit reduced reversed-index double-tail endpoint. -/
lemma reducedFiniteSequenceDelta0Delta0_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin (n + 1)) :
    ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).obj i =
      ModuleCat.of R
        (F (castSucc (castSucc i.rev)) ⧸
          (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc i.rev)))))) := by
  -- Normalize the two successive reduced `δ₀` object projections to the explicit double tail.
  rw [ComposableArrows.δ₀Functor_obj_obj, ComposableArrows.δ₀Functor_obj_obj,
    ComposableArrows.mkOfObjOfMapSucc_obj]
  have h : rev (i.succ.succ) = castSucc (castSucc i.rev) := by
    simpa [Fin.rev_succ] using (Fin.rev_succ i.succ).symm
  exact congrArg
    (fun j : Fin (n + 3) ↦
      ModuleCat.of R
        (F j ⧸ (maximalIdeal R • (⊤ : Submodule R (F j)))))
    h

/-- Helper for Lemma 10.99.5: the explicit reduced shortened tail owner has the expected
source object for the stable reversed-index reduced tail map at `i`. -/
lemma reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (rev (castSucc i))) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (rev (castSucc i))))))) =
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C (succ (castSucc (rev i))) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
              (succ (castSucc (rev i))))))) := by
  -- Normalize the explicit reduced owner source to the reduced `shortened_tail_map_cast` source.
  exact congrArg
    (fun j : Fin (n + 2) ↦
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C j ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j)))))
    (by
      simpa [← Fin.castSucc_succ] using
        (CriteriaForFlatness.shortenedFiniteSequenceDelta0_sourceIndex_eq i))

/-- Helper for Lemma 10.99.5: the explicit reduced shortened tail owner has the expected
target object for the stable reversed-index reduced tail map at `i`. -/
lemma reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) (i : Fin n) :
    ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (castSucc (rev i))) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (castSucc (rev i))))))) =
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C (castSucc (rev (succ i))) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
              (castSucc (rev (succ i))))))) := by
  -- Normalize the explicit reduced owner target to the reduced `shortened_tail_map_cast` target.
  exact congrArg
    (fun j : Fin (n + 2) ↦
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C j ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j)))))
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0_targetIndex_eq i).symm

/-- Helper for Lemma 10.99.5: the shortened reduced `δ₀` tail also has an explicit owner
presentation in stable reversed indexing form. -/
noncomputable abbrev reducedShortenedFiniteSequenceDelta0ExplicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ComposableArrows (ModuleCat R) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C i.rev.castSucc)))))
    (fun i ↦
      eqToHom
          (show
            ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (rev (castSucc i))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (rev (castSucc i))))))) =
              ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (succ (castSucc (rev i))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (succ (castSucc (rev i))))))) from
            CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
              d i) ≫
        ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d i.rev).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) ≫
      eqToHom
          (show
            ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (castSucc (rev i))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (castSucc (rev i))))))) =
              ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (rev (succ i))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (rev (succ i))))))) from
            CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
              d i))

/-- Helper for Chap10 Lemma 10 99 5: the explicit reduced shortened-tail owner map can be read
directly at the stable reversed index, so its middle map is literally the stored quotient tail
map. -/
lemma reducedShortenedFiniteSequenceDelta0ExplicitTail_map_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map' i.rev.1
        (i.rev.1 + 1) =
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
          d i.rev) ≫
        ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d i.rev).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
          d i.rev) := by
  -- Read the explicit reduced owner map directly from `mkOfObjOfMapSucc` at the stable reversed
  -- index, so the right-hand side is the stored quotient tail map formula.
  let obj : Fin (n + 1) → ModuleCat R := fun j ↦
    ModuleCat.of R
      (@CriteriaForFlatness.shortenedFamily _ F C j.rev.castSucc ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j.rev.castSucc))))
  let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦
      eqToHom
          (show
            ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (rev (castSucc j))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (rev (castSucc j))))))) =
              ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (succ (castSucc (rev j))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (succ (castSucc (rev j))))))) from
            CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
              d j) ≫
        ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d j.rev).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) ≫
      eqToHom
          (show
            ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (castSucc (rev j))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (castSucc (rev j))))))) =
              ModuleCat.of R
                (@CriteriaForFlatness.shortenedFamily _ F C
                  (castSucc (rev (succ j))) ⧸
                  (maximalIdeal R •
                    (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C
                      (castSucc (rev (succ j))))))) from
            CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
              d j)
  -- After unfolding the owner once, the map is exactly the stored `mapSucc` formula.
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.rev.1 (i.rev.1 + 1) = _
  simpa [obj, mapSucc, Fin.rev_rev] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.rev.1 i.rev.2)

/-- Helper for Chap10 Lemma 10 99 5: the explicit reduced double-tail owner map can also be read
directly at the stable reversed index, so its middle differential is literally the reduced
`castSucc.castSucc` differential. -/
lemma reducedFiniteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (i : Fin n) :
    ModuleCat.of R
        (F i.rev.castSucc.rev.castSucc.castSucc ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F i.rev.castSucc.rev.castSucc.castSucc)))) =
      ModuleCat.of R
        (F i.castSucc.castSucc.succ ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F i.castSucc.castSucc.succ)))) := by
  -- Normalize the reversed reduced source object to the direct `castSucc.castSucc` source index.
  exact congrArg
    (fun j : Fin (n + 3) ↦
      ModuleCat.of R
        (F j ⧸ (maximalIdeal R • (⊤ : Submodule R (F j)))))
    (by simp [Fin.rev_castSucc, Fin.rev_rev, ← Fin.castSucc_succ])

/-- Helper for Chap10 Lemma 10 99 5: the explicit reduced double-tail owner target at the reversed
index matches the direct `castSucc.castSucc` target index. -/
lemma reducedFiniteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (i : Fin n) :
    ModuleCat.of R
        (F i.castSucc.castSucc.castSucc ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F i.castSucc.castSucc.castSucc)))) =
      ModuleCat.of R
        (F i.rev.succ.rev.castSucc.castSucc ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F i.rev.succ.rev.castSucc.castSucc)))) := by
  -- Normalize the reversed reduced target object to the direct `castSucc.castSucc` target index.
  exact congrArg
    (fun j : Fin (n + 3) ↦
      ModuleCat.of R
        (F j ⧸ (maximalIdeal R • (⊤ : Submodule R (F j)))))
    (by simp [Fin.rev_succ, Fin.rev_rev, ← Fin.castSucc_succ])

/-- Helper for Chap10 Lemma 10 99 5: the explicit reduced double-tail owner map can also be read
directly at the stable reversed index, with both endpoints rewritten to the direct
`castSucc.castSucc` spelling. -/
lemma reducedFiniteSequenceDelta0Delta0ExplicitTail_map_rev
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.rev.1
        (i.rev.1 + 1) =
      eqToHom (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev
          (R := R) i) ≫
        ModuleCat.ofHom
          (((d i.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R)) ≫
      eqToHom (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev
          (R := R) i) := by
  -- Read the explicit reduced double-tail owner map directly from `mkOfObjOfMapSucc`.
  let obj : Fin (n + 1) → ModuleCat R := fun j ↦
    ModuleCat.of R
      (F (castSucc (castSucc j.rev)) ⧸
        (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.rev))))))
  let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦ by
    change ModuleCat.of R
        (F (castSucc (castSucc j.castSucc.rev)) ⧸
          (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.castSucc.rev)))))) ⟶
      ModuleCat.of R
        (F (castSucc (castSucc j.succ.rev)) ⧸
          (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.succ.rev))))))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom
      (((d j.rev.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R))
  -- After unfolding the owner once, the map is exactly the stored reduced differential.
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.rev.1 (i.rev.1 + 1) = _
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.rev.1 i.rev.2]
  apply ModuleCat.hom_ext
  ext x
  simpa [obj, mapSucc, Fin.rev_rev, Fin.rev_castSucc, Fin.rev_succ, Category.assoc,
    CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail_source_obj_eq_rev,
    CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail_target_obj_eq_rev]

/-- Helper for Chap10 Lemma 10 99 5: after shifting once into the reduced owner of the shortened
sequence, the forgotten-head map is exactly the explicit reduced reversed-index tail map. -/
lemma reducedShortenedFiniteSequenceShiftedMap_eq_explicitTailOwner
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
      ((CriteriaForFlatness.reducedFiniteSequence R
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) =
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
          d i) ≫
        ModuleCat.ofHom
          ((((CriteriaForFlatness.shortened_tail_map_cast d i.rev).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))) ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
        d i) := by
  -- Route correction: normalize the shifted reduced forgotten-head map first, so the public
  -- reduced `δ₀` comparison only needs to match one stable explicit owner formula.
  rw [CriteriaForFlatness.composableArrows_delta0_map_succ
    (CriteriaForFlatness.reducedFiniteSequence R
      (CriteriaForFlatness.shortenedDifferential w d)) i.1 i.2]
  let obj : Fin (n + 2) → ModuleCat R := fun j ↦
    ModuleCat.of R
      (@CriteriaForFlatness.shortenedFamily _ F C j.rev ⧸
        (maximalIdeal R •
          (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j.rev))))
  let mapSucc : ∀ j : Fin (n + 1), obj j.castSucc ⟶ obj j.succ := fun j ↦ by
    change ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C j.castSucc.rev ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j.castSucc.rev)))) ⟶
      ModuleCat.of R
        (@CriteriaForFlatness.shortenedFamily _ F C j.succ.rev ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (@CriteriaForFlatness.shortenedFamily _ F C j.succ.rev))))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom
      ((((CriteriaForFlatness.shortenedDifferential w d j.rev).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R)))
  change eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
      w d i.castSucc).symm ≫
        (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' (i.1 + 1) (i.1 + 2) ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) = _
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc (i.1 + 1)
    (Nat.succ_lt_succ i.2)]
  change eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
      w d i.castSucc).symm ≫
        mapSucc i.succ ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) = _
  simpa [obj, mapSucc, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_succ, Category.assoc,
    CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq,
    CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq,
    CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq_rev,
    CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq_rev] using
    (CriteriaForFlatness.reducedShortenedTailMap_ladder_moduleCat (R := R) (d := d) (i := i.rev))

/-- Helper for Chap10 Lemma 10 99 5: after shifting twice into the reduced original owner, the
double-tail map is exactly the explicit reduced reversed-index original tail map. -/
lemma reducedDoubleTailShiftedMap_eq_explicitTailOwner
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d i.castSucc) ≫
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).map' i.1 (i.1 + 1) ≫
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- Route correction: normalize the reduced original double-tail owner map before comparing it
  -- with the explicit reduced owner, so later naturality proofs stay in one stable spelling.
  calc
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d i.castSucc) ≫
        ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).map' i.1 (i.1 + 1) ≫
        eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
          w d i.succ).symm =
        ModuleCat.ofHom
          ((((d i.succ.succ.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R))) := by
      rw [CriteriaForFlatness.composableArrows_delta0_map_succ
          ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀) i.1 i.2,
        CriteriaForFlatness.composableArrows_delta0_map_succ
          (CriteriaForFlatness.reducedFiniteSequence R d) (i.1 + 1) (Nat.succ_lt_succ i.2)]
      let obj : Fin (n + 3) → ModuleCat R := fun j ↦
        ModuleCat.of R
          (F j.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F j.rev))))
      let mapSucc : ∀ j : Fin (n + 2), obj j.castSucc ⟶ obj j.succ := fun j ↦ by
        change ModuleCat.of R
            (F j.castSucc.rev ⧸
              (maximalIdeal R • (⊤ : Submodule R (F j.castSucc.rev)))) ⟶
          ModuleCat.of R
            (F j.succ.rev ⧸
              (maximalIdeal R • (⊤ : Submodule R (F j.succ.rev))))
        rw [Fin.rev_castSucc, Fin.rev_succ]
        exact ModuleCat.ofHom
          ((((d j.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))
      change eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
          w d i.castSucc) ≫
            (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' (i.1 + 2) (i.1 + 3) ≫
          eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
            w d i.succ).symm =
          ModuleCat.ofHom
            ((((d i.succ.succ.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc (i.1 + 2)
        (Nat.succ_lt_succ (Nat.succ_lt_succ i.2))]
      have hrev :
          ((⟨i.1 + 2, Nat.succ_lt_succ (Nat.succ_lt_succ i.2)⟩ : Fin (n + 2)).rev) =
            i.succ.succ.rev := by
        simpa using (rfl : (i.succ.succ).rev = i.succ.succ.rev)
      rw [hrev]
      simpa [obj, mapSucc, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_succ, Category.assoc]
    _ = (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
      let obj : Fin (n + 1) → ModuleCat R := fun j ↦
        ModuleCat.of R
          (F (castSucc (castSucc j.rev)) ⧸
            (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.rev))))))
      let mapSucc : ∀ j : Fin n, obj j.castSucc ⟶ obj j.succ := fun j ↦ by
        change ModuleCat.of R
            (F (castSucc (castSucc j.castSucc.rev)) ⧸
              (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.castSucc.rev)))))) ⟶
          ModuleCat.of R
            (F (castSucc (castSucc j.succ.rev)) ⧸
              (maximalIdeal R • (⊤ : Submodule R (F (castSucc (castSucc j.succ.rev))))))
        rw [Fin.rev_castSucc, Fin.rev_succ]
        exact ModuleCat.ofHom
          (((d j.rev.castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))
      change ModuleCat.ofHom
          ((((d i.succ.succ.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R))) =
          (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' i.1 (i.1 + 1)
      simpa [obj, mapSucc, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_succ] using
        (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc i.1 i.2).symm

/-- Helper for Chap10 Lemma 10 99 5: the reduced shortened `δ₀` map agrees with the explicit
reduced shortened-tail owner map at the stable `Fin` index. -/
lemma reducedShortenedFiniteSequenceDelta0_map_eq_explicitTail_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
      ((CriteriaForFlatness.reducedFiniteSequence R
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
      eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.succ) =
      (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map' i.1
        (i.1 + 1) := by
  -- First rewrite the shifted reduced owner map to the stable explicit-tail formula, then read
  -- the explicit reduced owner map off directly at that same index.
  calc
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d i.castSucc).symm ≫
        ((CriteriaForFlatness.reducedFiniteSequence R
            (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i.1 (i.1 + 1) ≫
        eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
          w d i.succ) =
        eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_source_obj_eq
            d i) ≫
          ModuleCat.ofHom
            ((((CriteriaForFlatness.shortened_tail_map_cast d i.rev).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R))) ≫
          eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_target_obj_eq
            d i) := CriteriaForFlatness.reducedShortenedFiniteSequenceShiftedMap_eq_explicitTailOwner
              (R := R) w d i
    _ = (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map' i.1
          (i.1 + 1) := by
      -- Read the same reduced owner map directly from the explicit-tail construction.
      simpa [Fin.rev_rev] using
        (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_map_rev
          (R := R) d i.rev).symm

/-- Helper for Chap10 Lemma 10 99 5: the reduced original double-tail map agrees with the
explicit reduced double-tail owner map at the stable `Fin` index. -/
lemma reducedFiniteSequenceDelta0Delta0_map_eq_explicitTail_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d i.castSucc) ≫
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).map' i.1 (i.1 + 1) ≫
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d i.succ).symm =
      (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.1 (i.1 + 1) := by
  -- This is exactly the shifted reduced double-tail comparison proved just above.
  exact CriteriaForFlatness.reducedDoubleTailShiftedMap_eq_explicitTailOwner (R := R) w d i

/-- Helper for Chap10 Lemma 10 99 5: after reduction, the shortened `δ₀` map becomes the explicit
reduced reversed-index tail map once the endpoints are rewritten to the stable explicit owners. -/
lemma reducedShortenedFiniteSequenceDelta0_map_eq_explicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩).symm ≫
      ((CriteriaForFlatness.reducedFiniteSequence R
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i (i + 1) ≫
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩) =
      (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable reduced `Fin` bridge proved just above.
  simpa using
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_map_eq_explicitTail_fin
      (R := R) w d ⟨i, hi⟩)

/-- Helper for Chap10 Lemma 10 99 5: after reduction, the original double-tail map is the
explicit reduced reversed-index owner map once both endpoints are normalized. -/
lemma reducedFiniteSequenceDelta0Delta0_map_eq_explicitTail
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩) ≫
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).map' i (i + 1) ≫
    eqToHom (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩).symm =
      (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable reduced `Fin` bridge proved just above.
  simpa using
    (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0_map_eq_explicitTail_fin
      (R := R) w d ⟨i, hi⟩)

/-- Helper for Chap10 Lemma 10 99 5: in the explicit reduced owner world, the normalized ladder
square is exactly the reduced shortened-tail ladder at the reversed index. -/
lemma reducedShortenedFiniteSequenceDelta0ExplicitTail_naturality_fin
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : Fin n) :
    (@CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail
        R S _ _ _ _ _ _ _ n F _ _ _ _ C _ _ _ _ d).map' i.1 (i.1 + 1) ≫
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          i.succ.rev)).toModuleIso.hom =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          i.castSucc.rev)).toModuleIso.hom ≫
        (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.1
          (i.1 + 1) := by
  -- Rewrite both reduced explicit owner maps to the same reversed-index core formulas, then the
  -- target is exactly the normalized reduced shortened-tail ladder square at `i.rev`.
  have hshort :=
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_map_rev
      (R := R) d i.rev)
  have hdouble :=
    (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail_map_rev
      (R := R) d i.rev)
  rw [show
      (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map' i.1
          (i.1 + 1) =
        (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail d).map'
          i.rev.rev.1 (i.rev.rev.1 + 1) by simpa [Fin.rev_rev]]
  rw [show
      (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i.1
          (i.1 + 1) =
        (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map'
          i.rev.rev.1 (i.rev.rev.1 + 1) by simpa [Fin.rev_rev]]
  rw [hshort, hdouble]
  simpa [Fin.rev_rev, Fin.rev_castSucc, Fin.rev_succ,
    CriteriaForFlatness.shortenedTailSourceLinearEquiv,
    CriteriaForFlatness.shortenedTailTargetLinearEquiv,
    Category.assoc] using
    (CriteriaForFlatness.reducedShortenedTailMap_ladder_moduleCat (R := R) d i.rev)

/-- Helper for Chap10 Lemma 10 99 5: in the explicit reduced owner world, the reduced shortened
tail map and the reduced original double-tail map are related by the canonical quotient endpoint
equivalences. -/
lemma reducedShortenedFiniteSequenceDelta0ExplicitTail_naturality
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    (@CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail
        R S _ _ _ _ _ _ _ n F _ _ _ _ C _ _ _ _ d).map' i (i + 1) ≫
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          ((⟨i + 1, Nat.succ_lt_succ hi⟩ : Fin (n + 1)).rev))).toModuleIso.hom =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          ((⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩ : Fin (n + 1)).rev))).toModuleIso.hom ≫
        (CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0ExplicitTail d).map' i (i + 1) := by
  -- Replace the nat-index statement by the stable reduced `Fin`-indexed normalized ladder square.
  simpa using
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_naturality_fin
      (R := R) d ⟨i, hi⟩)

/-- Helper for Lemma 10.99.5: the reduced component comparison between the shortened `δ₀`
tail and the original reduced double tail satisfies the adjacent commuting squares required by
`ComposableArrows.isoMk`. -/
-- TODO: rewrite both reduced owner maps through the new explicit reduced owner normalizers, then
-- split on the reversed index and apply either `reducedShortenedFirstTailMap_ladder_moduleCat` or
-- `reducedShortenedTailMap_ladder_moduleCat`.
lemma reducedShortenedFiniteSequenceDelta0ComponentIso_hom_naturality
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (i : ℕ) (hi : i < n) :
    ((CriteriaForFlatness.reducedFiniteSequence R
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).map' i (i + 1) ≫
      (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso
           w d ⟨i + 1, Nat.succ_lt_succ hi⟩).hom =
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso
           w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩).hom ≫
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).map' i (i + 1) := by
  -- Reassemble the raw reduced naturality square from the normalized explicit reduced owner
  -- square, exactly as in the unreduced component comparison.
  simpa [CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso_hom_eq,
    Category.assoc] using
    (CriteriaForFlatness.componentIsoNaturality_of_normalizedTailSquare
      (sx₀ := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩)
      (sx₁ := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_source_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩)
      (ty₀ := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩)
      (ty₁ := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_target_obj_eq
        w d ⟨i + 1, Nat.succ_lt_succ hi⟩)
      (e₀ := (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          ((⟨i, Nat.lt_trans hi (Nat.lt_succ_self n)⟩ : Fin (n + 1)).rev))).toModuleIso.hom)
      (e₁ := (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
        (maximalIdeal R)
        (CriteriaForFlatness.shortenedCastCastSuccLinearEquiv
          ((⟨i + 1, Nat.succ_lt_succ hi⟩ : Fin (n + 1)).rev))).toModuleIso.hom)
      (hf := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_map_eq_explicitTail
        (R := R) w d i hi)
      (hg := CriteriaForFlatness.reducedFiniteSequenceDelta0Delta0_map_eq_explicitTail
        (R := R) w d i hi)
      (hcomm := CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ExplicitTail_naturality
        (R := R) w d i hi))

/-- Helper for Lemma 10.99.5: the reduced shortened tail is canonically isomorphic to the
double tail of the original reduced finite sequence. -/
noncomputable def reducedShortenedFiniteSequenceDelta0Iso
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R
      (CriteriaForFlatness.shortenedDifferential   w d)).δ₀ ≅
      (CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀ :=
  -- Package the reduced objectwise comparison by `ComposableArrows.isoMk`; the previous lemma
  -- supplies the localized reduced commuting squares.
  ComposableArrows.isoMk
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso
         w d)
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0ComponentIso_hom_naturality
         w d)

/-- Helper for Lemma 10.99.5: exactness of the shortened unreduced `δ₀` tail is
equivalent to exactness of the original unreduced double tail. -/
lemma shortenedFiniteSequenceDelta0_exact_iff
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    ((CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).Exact ↔
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).Exact := by
  -- The owner-level `δ₀` comparison is already an isomorphism, so exactness transports directly.
  exact ComposableArrows.exact_iff_of_iso
    (CriteriaForFlatness.shortenedFiniteSequenceDelta0Iso   w d)

/-- Helper for Lemma 10.99.5: exactness of the shortened reduced `δ₀` tail is equivalent
to exactness of the original reduced double tail. -/
lemma reducedShortenedFiniteSequenceDelta0_exact_iff
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R
        (CriteriaForFlatness.shortenedDifferential   w d)).δ₀.Exact ↔
      ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).Exact := by
  -- This is the reduced analogue of the previous transport lemma.
  exact ComposableArrows.exact_iff_of_iso
    (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0Iso
         w d)

/-- Helper for Lemma 10.99.5: the leftmost owner map of `finiteSequence d` is the displayed head
differential. -/
lemma finiteSequence_leftmost_map_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.finiteSequence d).map' 0 1 = ModuleCat.ofHom (d (Fin.last (n + 1))) := by
  -- Unfold the owner once and read off its leftmost displayed map.
  let obj : Fin (n + 3) → ModuleCat S := fun i ↦ ModuleCat.of S (F i.rev)
  let mapSucc : ∀ i : Fin (n + 2), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d i.rev)
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 0 1 =
    ModuleCat.ofHom (d (Fin.last (n + 1)))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 0 (Nat.succ_pos (n + 1)))

/-- Helper for Lemma 10.99.5: the second owner map of `finiteSequence d` is the next displayed
differential. -/
lemma finiteSequence_next_map_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.finiteSequence d).map' 1 2 =
      ModuleCat.ofHom (d (Fin.castSucc (Fin.last n))) := by
  -- Unfold the owner once and normalize the reversed successor index to the next displayed map.
  let obj : Fin (n + 3) → ModuleCat S := fun i ↦ ModuleCat.of S (F i.rev)
  let mapSucc : ∀ i : Fin (n + 2), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d i.rev)
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 1 2 =
    ModuleCat.ofHom (d (Fin.castSucc (Fin.last n)))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 1
      (Nat.succ_lt_succ (Nat.succ_pos n)))

/-- Helper for Lemma 10.99.5: the third owner map of `finiteSequence d` is the third
displayed differential, written in the stable `Fin.rev` form that still works in the smallest
three-map case. -/
lemma finiteSequence_third_map_eq
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.finiteSequence d).map' 2 3 =
      ModuleCat.ofHom (d ((2 : Fin (n + 3)).rev)) := by
  -- Unfold the owner once and read off the third displayed differential in stable `Fin.rev` form.
  let obj : Fin (n + 4) → ModuleCat S := fun i ↦ ModuleCat.of S (F i.rev)
  let mapSucc : ∀ i : Fin (n + 3), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change ModuleCat.of S (F i.castSucc.rev) ⟶ ModuleCat.of S (F i.succ.rev)
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (d i.rev)
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 2 3 =
    ModuleCat.ofHom (d ((2 : Fin (n + 3)).rev))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 2
      (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos n))))

/-- Helper for Lemma 10.99.5: the `Fin.rev` index used for the third differential is the
same as the double `castSucc` of `Fin.last n`. -/
lemma thirdDifferentialIndex_eq (n : ℕ) :
    ((2 : Fin (n + 3)).rev) = (Fin.last n).castSucc.castSucc := by
  -- Compare the two indices by their values: both are the unique element of `Fin (n + 3)` with
  -- value `n`.
  apply Fin.ext
  change n + 3 - (2 + 1) = n
  simpa using (Nat.add_sub_cancel n 3)

/-- Helper for Lemma 10.99.5: the third owner map of `finiteSequence d` can also be read
as the differential indexed by `(Fin.last n).castSucc.castSucc`. -/
lemma finiteSequence_third_map_eq_castSuccCastSucc
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.finiteSequence d).map' 2 3 =
      ModuleCat.ofHom (d ((Fin.last n).castSucc.castSucc)) := by
  simpa [CriteriaForFlatness.thirdDifferentialIndex_eq n] using
    (CriteriaForFlatness.finiteSequence_third_map_eq  d)

/-- Helper for Lemma 10.99.5: the leftmost owner map of the reduced finite sequence is the
reduction of the displayed head differential. -/
lemma reducedFiniteSequence_leftmost_map_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R d).map' 0 1 =
      ModuleCat.ofHom
        (((d (Fin.last (n + 1))).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  -- Unfold the reduced owner once and read off its leftmost reduced differential.
  let obj : Fin (n + 3) → ModuleCat R := fun i ↦
    ModuleCat.of R (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev))))
  let mapSucc : ∀ i : Fin (n + 2), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change
      ModuleCat.of R
          (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
        ModuleCat.of R
          (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 0 1 =
    ModuleCat.ofHom
      (((d (Fin.last (n + 1))).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 0 (Nat.succ_pos (n + 1)))

/-- Helper for Lemma 10.99.5: the second owner map of the reduced finite sequence is the
reduction of the next displayed differential. -/
lemma reducedFiniteSequence_next_map_eq
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R d).map' 1 2 =
      ModuleCat.ofHom
        (((d (Fin.castSucc (Fin.last n))).restrictScalars R).quotientMapByIdeal
          (maximalIdeal R)) := by
  -- Unfold the reduced owner once and normalize the reversed successor index.
  let obj : Fin (n + 3) → ModuleCat R := fun i ↦
    ModuleCat.of R (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev))))
  let mapSucc : ∀ i : Fin (n + 2), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change
      ModuleCat.of R
          (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
        ModuleCat.of R
          (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 1 2 =
    ModuleCat.ofHom
      (((d (Fin.castSucc (Fin.last n))).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 1
      (Nat.succ_lt_succ (Nat.succ_pos n)))

/-- Helper for Lemma 10.99.5: the third owner map of the reduced finite sequence is the
reduction of the third displayed differential, written in the stable `Fin.rev` form. -/
lemma reducedFiniteSequence_third_map_eq
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R d).map' 2 3 =
      ModuleCat.ofHom
        (((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
          (maximalIdeal R)) := by
  -- Unfold the reduced owner once and read off the third reduced differential in stable form.
  let obj : Fin (n + 4) → ModuleCat R := fun i ↦
    ModuleCat.of R (F i.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.rev))))
  let mapSucc : ∀ i : Fin (n + 3), obj i.castSucc ⟶ obj i.succ := fun i ↦ by
    change
      ModuleCat.of R
          (F i.castSucc.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.castSucc.rev)))) ⟶
        ModuleCat.of R
          (F i.succ.rev ⧸ (maximalIdeal R • (⊤ : Submodule R (F i.succ.rev))))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact ModuleCat.ofHom (((d i.rev).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
  change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 2 3 =
    ModuleCat.ofHom
      (((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
        (maximalIdeal R))
  simpa [obj, mapSucc] using
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc 2
      (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos n))))

/-- Helper for Lemma 10.99.5: the third owner map of the reduced finite sequence can also
be read as the reduction of the differential indexed by `(Fin.last n).castSucc.castSucc`. -/
lemma reducedFiniteSequence_third_map_eq_castSuccCastSucc
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    (CriteriaForFlatness.reducedFiniteSequence R d).map' 2 3 =
      ModuleCat.ofHom
        (((d ((Fin.last n).castSucc.castSucc)).restrictScalars R).quotientMapByIdeal
          (maximalIdeal R)) := by
  simpa [CriteriaForFlatness.thirdDifferentialIndex_eq n] using
    (CriteriaForFlatness.reducedFiniteSequence_third_map_eq   d)

/-- Helper for Lemma 10.99.5: the first two displayed differentials compose to zero whenever the
packaged finite sequence is a complex. -/
lemma head_zero_comp_of_isComplex
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex) :
    (d (Fin.castSucc (Fin.last n))).comp (d (Fin.last (n + 1))) = 0 := by
  -- Translate the owner statement `hcomplex.zero 0` into an identity of linear maps.
  have hzero := congrArg ModuleCat.Hom.hom (hcomplex.zero 0)
  simpa only [ModuleCat.hom_comp, finiteSequence_leftmost_map_eq,
    finiteSequence_next_map_eq] using hzero

/-- Helper for Lemma 10.99.5: the first composition in a finite complex is zero, so the range of
the leftmost differential is contained in the kernel of the next differential. -/
lemma head_range_le_ker_of_isComplex
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex) :
    LinearMap.range (d (Fin.last (n + 1))) ≤
      LinearMap.ker (d (Fin.castSucc (Fin.last n))) := by
  -- Normalize the owner-level zero-composition statement to the concrete head pair.
  exact LinearMap.range_le_ker_iff.mpr (head_zero_comp_of_isComplex  d hcomplex)

/-- Helper for Lemma 10.99.5: the second and third displayed differentials of a finite
complex also compose to zero, so the range of the second differential is contained in the kernel
of the third. -/
lemma next_range_le_ker_of_isComplex
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc)
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex) :
    LinearMap.range (d (Fin.castSucc (Fin.last (n + 1)))) ≤
      LinearMap.ker (d ((2 : Fin (n + 3)).rev)) := by
  -- Translate the owner-level relation `hcomplex.zero 1` into the concrete second and third maps.
  have hzero := congrArg ModuleCat.Hom.hom (hcomplex.zero 1)
  have hcomp :
      (d ((2 : Fin (n + 3)).rev)).comp (d (Fin.castSucc (Fin.last (n + 1)))) = 0 := by
    simpa only [ModuleCat.hom_comp, CriteriaForFlatness.finiteSequence_next_map_eq,
      CriteriaForFlatness.finiteSequence_third_map_eq] using hzero
  exact LinearMap.range_le_ker_iff.mpr hcomp

end CriteriaForFlatness

/-- Helper for Lemma 10.99.5: once a pair `g, h` is exact, quotienting the source of `g` by any
submodule contained in `ker g` preserves exactness against `h`. -/
lemma exact_range_liftQ_of_range_le_ker
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D}
    (hfg0 : LinearMap.range f ≤ LinearMap.ker g)
    (hgh : Function.Exact g h) :
    Function.Exact ((LinearMap.range f).liftQ g hfg0) h := by
  -- The descended map has the same range as `g`, so exactness against `h` is unchanged.
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · -- Check the new pair still composes to zero on quotient representatives.
    ext x
    change (h ∘ₗ g) x = 0
    simpa using LinearMap.congr_fun hgh.linearMap_comp_eq_zero x
  · -- The kernel of `h` is still the range of the descended map.
    rw [LinearMap.exact_iff] at hgh
    simpa [Submodule.range_liftQ] using hgh.le

/-- Helper for Lemma 10.99.5: injectivity of the descended quotient map recovers exactness of the
original pair. -/
lemma exact_of_injective_range_liftQ
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hfg0 : LinearMap.range f ≤ LinearMap.ker g)
    (hg : Function.Injective ((LinearMap.range f).liftQ g hfg0)) :
    Function.Exact f g := by
  -- Injectivity forces the quotient kernel to vanish, which is equivalent to `ker g = range f`.
  have hker : LinearMap.ker ((LinearMap.range f).liftQ g hfg0) = ⊥ := by
    simpa [LinearMap.ker_eq_bot] using hg
  rw [LinearMap.exact_iff]
  exact (LinearMap.ker_eq_bot_range_liftQ_iff hfg0).mp hker

/-- Helper for Lemma 10.99.5: exactness of a quotient-descended head against the next map
recovers exactness of the original tail pair. -/
lemma exact_of_exact_range_liftQ
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D}
    (hfg0 : LinearMap.range f ≤ LinearMap.ker g)
    (hgh : Function.Exact ((LinearMap.range f).liftQ g hfg0) h) :
    Function.Exact g h := by
  -- The quotient lift has the same image as `g`, so exactness against `h` pulls back unchanged.
  rw [LinearMap.exact_iff] at hgh ⊢
  simpa [Submodule.range_liftQ] using hgh

/-- Helper for Lemma 10.99.5: exactness of two linear maps is exactness of the corresponding
two-arrow `ComposableArrows` object in `ModuleCat`. -/
lemma composableArrowsExact₂_of_functionExact
    {T : Type*} [CommRing T]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module T A] [Module T B] [Module T C]
    {f : A →ₗ[T] B} {g : B →ₗ[T] C}
    (hfg : Function.Exact f g) :
    (ComposableArrows.mk₂
      (show ModuleCat.of T A ⟶ ModuleCat.of T B from ModuleCat.ofHom f)
      (show ModuleCat.of T B ⟶ ModuleCat.of T C from ModuleCat.ofHom g)).Exact := by
  let S : ShortComplex (ModuleCat T) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
      simpa [ModuleCat.hom_comp] using congrArg ModuleCat.ofHom hfg.linearMap_comp_eq_zero)
  have hS : S.Exact := by
    rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact hfg
  simpa [S] using hS.exact_toComposableArrows

/-- Helper for Lemma 10.99.5: if `t ∘ v = 0`, then the descended map
`(LinearMap.range u).liftQ v huv` still composes trivially with `t`. -/
lemma comp_liftQ_eq_zero_of_range_le_ker
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module S A] [Module S B] [Module S C] [Module S D]
    {u : A →ₗ[S] B} {v : B →ₗ[S] C} {t : C →ₗ[S] D}
    (huv : LinearMap.range u ≤ LinearMap.ker v)
    (hvt : LinearMap.range v ≤ LinearMap.ker t) :
    t.comp ((LinearMap.range u).liftQ v huv) = 0 := by
  -- Compare both quotient maps on representatives and reduce to the original
  -- composition `t ∘ v = 0`.
  apply Submodule.linearMap_qext
  ext x
  change t (((LinearMap.range u).liftQ v huv) (Submodule.Quotient.mk x)) = 0
  rw [show ((LinearMap.range u).liftQ v huv) (Submodule.Quotient.mk x) = v x by
    simpa using LinearMap.congr_fun ((LinearMap.range u).liftQ_mkQ v huv) x]
  exact LinearMap.congr_fun (LinearMap.range_le_ker_iff.mp hvt) x

/-- Helper for Lemma 10.99.5: quotients of finite `S`-modules are finite. -/
lemma finite_quotient_range
    {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [Module S A] [Module S B]
    [Module.Finite S B]
    (u : A →ₗ[S] B) :
    Module.Finite S (B ⧸ LinearMap.range u) := by
  -- The cokernel is a quotient of the finite target module, so finiteness descends.
  infer_instance

/-- Helper for Lemma 10.99.5: reducing a linear map modulo an ideal sends its range to the image
of the original range in the quotient. -/
lemma quotientMapByIdeal_range_eq_map
    {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (I : Ideal R) (u : A →ₗ[R] B) :
    LinearMap.range (u.quotientMapByIdeal I) =
      Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R B))) (LinearMap.range u) := by
  -- Both sides consist of classes represented by elements of the form `u x`.
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine Quotient.inductionOn x ?_
    intro x
    refine ⟨u x, ?_, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, hy⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    simpa using hy

/-- Helper for Lemma 10.99.5: the closed fiber of the head cokernel is identified with the
cokernel of the reduced head map by passing both quotients through the same ambient quotient. -/
noncomputable def head_cokernel_closed_fiber_linearEquiv
    {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (I : Ideal R) (u : A →ₗ[R] B) :
    ((B ⧸ LinearMap.range u) ⧸ (I • (⊤ : Submodule R (B ⧸ LinearMap.range u)))) ≃ₗ[R]
      ((B ⧸ (I • (⊤ : Submodule R B))) ⧸ (LinearMap.range (u.quotientMapByIdeal I))) := by
  -- First rewrite the closed fiber of the cokernel as a quotient by the image of `I • B`.
  let eLeft :=
    Submodule.quotEquivOfEq
      (I • (⊤ : Submodule R (B ⧸ LinearMap.range u)))
      (Submodule.map (Submodule.mkQ (LinearMap.range u)) (I • (⊤ : Submodule R B)))
      (by simp [Submodule.map_smul'', Submodule.range_mkQ])
  -- Then identify both iterated quotients with the same quotient of `B`.
  let eMiddle :=
    Submodule.quotientQuotientEquivQuotientSup (LinearMap.range u) (I • (⊤ : Submodule R B))
  let eSwap :=
    Submodule.quotEquivOfEq
      (((LinearMap.range u) ⊔ (I • (⊤ : Submodule R B))))
      (((I • (⊤ : Submodule R B)) ⊔ LinearMap.range u))
      (sup_comm _ _)
  let eRight :=
    (Submodule.quotEquivOfEq
      (LinearMap.range (u.quotientMapByIdeal I))
      (Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R B))) (LinearMap.range u))
      (quotientMapByIdeal_range_eq_map  I u)).trans
      (Submodule.quotientQuotientEquivQuotientSup (I • (⊤ : Submodule R B)) (LinearMap.range u))
  exact eLeft.trans (eMiddle.trans (eSwap.trans eRight.symm))

/-- Helper for Lemma 10.99.5: the closed-fiber comparison for the head cokernel sends the double
class of `b` to the obvious double class of `b`. -/
lemma head_cokernel_closed_fiber_linearEquiv_apply_mk_mk
    {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (I : Ideal R) (u : A →ₗ[R] B) (b : B) :
    head_cokernel_closed_fiber_linearEquiv  I u
      (Submodule.Quotient.mk (Submodule.Quotient.mk b)) =
        Submodule.Quotient.mk (Submodule.Quotient.mk b) := by
  -- Unfold the comparison: each quotient equivalence is definitionally the identity on
  -- representatives of the form `Submodule.Quotient.mk (Submodule.Quotient.mk b)`.
  dsimp [head_cokernel_closed_fiber_linearEquiv]
  rfl

namespace CriteriaForFlatness

/-- Helper for Lemma 10.99.5: exactness of the reduced head pair gives the quotient-lift
compatibility hypothesis `range ≤ ker` needed to descend the next map to the reduced head
cokernel. -/
lemma reduced_head_range_le_ker
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C]
    [Module R A] [Module R B] [Module R C]
    [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]
    (I : Ideal R)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C)
    (hExact :
      Function.Exact ((u.restrictScalars R).quotientMapByIdeal I)
        ((v.restrictScalars R).quotientMapByIdeal I)) :
    LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I) ≤
      LinearMap.ker ((v.restrictScalars R).quotientMapByIdeal I) := by
  -- Rewrite exactness as the owner equality `ker = range`, then take the forward inclusion.
  rw [LinearMap.exact_iff] at hExact
  exact hExact.symm.le

/-- Helper for Lemma 10.99.5: after identifying the closed fiber of the head cokernel with the
cokernel of the reduced head map, the descended reduced head is the quotient lift of the reduced
next differential. -/
lemma reduced_descended_head_ladder
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C]
    [Module R A] [Module R B] [Module R C]
    [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]
    (I : Ideal R)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C)
    (huv : LinearMap.range u ≤ LinearMap.ker v)
    (huv_mod :
      LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I) ≤
        LinearMap.ker ((v.restrictScalars R).quotientMapByIdeal I)) :
    ((LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I)).liftQ
        ((v.restrictScalars R).quotientMapByIdeal I) huv_mod).comp
        (head_cokernel_closed_fiber_linearEquiv  I (u.restrictScalars R)).toLinearMap =
      ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) := by
  -- Evaluate both sides on a double quotient representative; each map then reduces to the same
  -- quotient class of `v b`.
  apply DFunLike.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    (I • (⊤ : Submodule R (B ⧸ LinearMap.range u))) x
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u) y
  have hmk :
      head_cokernel_closed_fiber_linearEquiv  I (u.restrictScalars R)
          ((I • (⊤ : Submodule R (B ⧸ LinearMap.range u))).mkQ
            ((LinearMap.range u).mkQ b)) =
        Submodule.Quotient.mk (Submodule.Quotient.mk b) := by
    simpa [Submodule.mkQ_apply] using
      (head_cokernel_closed_fiber_linearEquiv_apply_mk_mk
         I (u.restrictScalars R) b)
  rw [LinearMap.comp_apply]
  change (((LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I)).liftQ
      ((v.restrictScalars R).quotientMapByIdeal I) huv_mod)
      ((head_cokernel_closed_fiber_linearEquiv  I (u.restrictScalars R))
        ((I • (⊤ : Submodule R (B ⧸ LinearMap.range u))).mkQ
          ((LinearMap.range u).mkQ b))) =
    ((u.range.liftQ v huv).restrictScalars R).quotientMapByIdeal I
      ((I • (⊤ : Submodule R (B ⧸ LinearMap.range u))).mkQ
        ((LinearMap.range u).mkQ b)))
  have hleft :=
    congrArg
      (((LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I)).liftQ
        ((v.restrictScalars R).quotientMapByIdeal I) huv_mod))
      hmk
  rw [hleft]
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.99.5: the reduced descended head commutes with the closed-fiber comparison
when the comparison is read in the source-faithful direction needed for transport along the
shortened cokernel complex. -/
lemma reduced_descended_head_ladder_symm
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C]
    [Module R A] [Module R B] [Module R C]
    [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]
    (I : Ideal R)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C)
    (huv : LinearMap.range u ≤ LinearMap.ker v)
    (huv_mod :
      LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I) ≤
        LinearMap.ker ((v.restrictScalars R).quotientMapByIdeal I)) :
    ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I).comp
        (head_cokernel_closed_fiber_linearEquiv  I (u.restrictScalars R)).symm.toLinearMap =
      (LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I)).liftQ
        ((v.restrictScalars R).quotientMapByIdeal I) huv_mod := by
  -- Postcompose the forward ladder with the inverse comparison; the middle comparison cancels.
  let e := head_cokernel_closed_fiber_linearEquiv  I (u.restrictScalars R)
  have hforward :
      ((LinearMap.range ((u.restrictScalars R).quotientMapByIdeal I)).liftQ
          ((v.restrictScalars R).quotientMapByIdeal I) huv_mod).comp e.toLinearMap =
        ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) :=
    reduced_descended_head_ladder   I u v huv huv_mod
  have hpost :=
    congrArg (fun f ↦ f.comp e.symm.toLinearMap) hforward
  simpa [e, LinearMap.comp_assoc] using hpost.symm

/-- Helper for Lemma 10.99.5: exactness of the first reduced pair makes the reduced descended
head injective on the closed fiber of the head cokernel. -/
lemma reduced_descended_head_injective
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C]
    [Module R A] [Module R B] [Module R C]
    [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C]
    (I : Ideal R)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C)
    (huv : LinearMap.range u ≤ LinearMap.ker v)
    (hExact :
      Function.Exact ((u.restrictScalars R).quotientMapByIdeal I)
        ((v.restrictScalars R).quotientMapByIdeal I)) :
    Function.Injective ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) := by
  let uMod := ((u.restrictScalars R).quotientMapByIdeal I)
  let vMod := ((v.restrictScalars R).quotientMapByIdeal I)
  let e := head_cokernel_closed_fiber_linearEquiv I (u.restrictScalars R)
  have huv_mod : LinearMap.range uMod ≤ LinearMap.ker vMod :=
    CriteriaForFlatness.reduced_head_range_le_ker I u v hExact
  have hLiftInj : Function.Injective ((LinearMap.range uMod).liftQ vMod huv_mod) := by
    exact LinearMap.ker_eq_bot.mp <|
      (LinearMap.ker_eq_bot_range_liftQ_iff huv_mod).2 hExact
  have hlift :
      ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I).comp
          e.symm.toLinearMap =
        (LinearMap.range uMod).liftQ vMod huv_mod :=
    CriteriaForFlatness.reduced_descended_head_ladder_symm I u v huv huv_mod
  intro x y hxy
  apply e.injective
  apply hLiftInj
  have hx :
      ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) x =
        (LinearMap.range uMod).liftQ vMod huv_mod (e x) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hlift (e x)
  have hy :
      ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) y =
        (LinearMap.range uMod).liftQ vMod huv_mod (e y) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hlift (e y)
  calc
    (LinearMap.range uMod).liftQ vMod huv_mod (e x)
        = ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) x := hx.symm
    _ = ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I) y := hxy
    _ = (LinearMap.range uMod).liftQ vMod huv_mod (e y) := hy
/-- Helper for Lemma 10.99.5: exactness of the reduced tail descends across the head cokernel to
the reduced head of the shortened complex. -/
lemma reduced_descended_head_exact
    {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module S A] [Module S B] [Module S C] [Module S D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    [IsScalarTower R S A] [IsScalarTower R S B] [IsScalarTower R S C] [IsScalarTower R S D]
    (I : Ideal R)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C) (t : C →ₗ[S] D)
    (huv : LinearMap.range u ≤ LinearMap.ker v)
    (hExact_uv :
      Function.Exact ((u.restrictScalars R).quotientMapByIdeal I)
        ((v.restrictScalars R).quotientMapByIdeal I))
    (hExact_vt :
      Function.Exact ((v.restrictScalars R).quotientMapByIdeal I)
        ((t.restrictScalars R).quotientMapByIdeal I)) :
    Function.Exact ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I)
      ((t.restrictScalars R).quotientMapByIdeal I) := by
  let uMod := ((u.restrictScalars R).quotientMapByIdeal I)
  let vMod := ((v.restrictScalars R).quotientMapByIdeal I)
  let tMod := ((t.restrictScalars R).quotientMapByIdeal I)
  let e := head_cokernel_closed_fiber_linearEquiv I (u.restrictScalars R)
  have huv_mod : LinearMap.range uMod ≤ LinearMap.ker vMod :=
    CriteriaForFlatness.reduced_head_range_le_ker I u v hExact_uv
  have hraw :
      Function.Exact ((LinearMap.range uMod).liftQ vMod huv_mod) tMod :=
    exact_range_liftQ_of_range_le_ker huv_mod hExact_vt
  have hcomp :
      Function.Exact
        ((((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I).comp
          e.symm.toLinearMap))
        tMod := by
    rw [CriteriaForFlatness.reduced_descended_head_ladder_symm I u v huv huv_mod]
    exact hraw
  exact (LinearEquiv.precomp_exact_iff_exact
    (f := ((((LinearMap.range u).liftQ v huv).restrictScalars R).quotientMapByIdeal I))
    (g := tMod) (e := e.symm)).1 hcomp
/-- Helper for Lemma 10.99.5: exactness of the first shortened unreduced pair is
equivalent to exactness of the raw descended head pair. -/
lemma shortenedHeadPairExact_iff_raw
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last (n + 1)).castSucc.castSucc))
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    Function.Exact
        (CriteriaForFlatness.shortened_head_map_cast   w)
        (CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)) ↔
      Function.Exact w (d ((2 : Fin (n + 3)).rev)) := by
  let e₁ :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ ≃ₗ[S] C :=
    CriteriaForFlatness.shortenedHeadSourceLinearEquiv
  let e₂ :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[S]
        F ((Fin.last (n + 1)).castSucc.castSucc) :=
    CriteriaForFlatness.shortenedHeadTargetLinearEquiv
  let e₃ :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
        F (castSucc (castSucc (castSucc (Fin.last n)))) :=
    CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n)
  have htail :
      (CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n)).comp e₂.symm.toLinearMap =
        e₃.symm.toLinearMap.comp (d ((2 : Fin (n + 3)).rev)) := by
    ext x
    have h :=
      LinearMap.congr_fun (CriteriaForFlatness.shortenedFirstTailMap_ladder (C := C) d)
        (e₂.symm x)
    simpa [LinearMap.comp_apply] using congrArg e₃.symm h
  calc
    Function.Exact (CriteriaForFlatness.shortened_head_map_cast   w)
        (CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n))
      ↔ Function.Exact
          (e₂.toLinearMap.comp (CriteriaForFlatness.shortened_head_map_cast   w))
          ((CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)).comp
            e₂.symm.toLinearMap) := by
              simpa [LinearMap.comp_assoc, e₂] using
                (LinearEquiv.conj_exact_iff_exact
                  (f := CriteriaForFlatness.shortened_head_map_cast   w)
                  (g := CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)) e₂).symm
    _ ↔ Function.Exact (w.comp e₁.toLinearMap)
          (e₃.symm.toLinearMap.comp (d ((2 : Fin (n + 3)).rev))) := by
            rw [CriteriaForFlatness.shortenedHeadMap_ladder, htail]
    _ ↔ Function.Exact w (e₃.symm.toLinearMap.comp (d ((2 : Fin (n + 3)).rev))) := by
          simpa [LinearMap.comp_assoc, e₁] using
            (LinearEquiv.precomp_exact_iff_exact
              (f := w)
              (g := e₃.symm.toLinearMap.comp (d ((2 : Fin (n + 3)).rev)))
              (e := e₁))
    _ ↔ Function.Exact w (d ((2 : Fin (n + 3)).rev)) := by
          simpa [LinearMap.comp_assoc, e₃] using
            (LinearEquiv.postcomp_exact_iff_exact
              (f := w) (g := d ((2 : Fin (n + 3)).rev)) (e := e₃.symm))
/-- Helper for Lemma 10.99.5: exactness of the first shortened reduced pair is equivalent
to exactness of the raw reduced descended head pair. -/
lemma reducedShortenedHeadPairExact_iff_raw
    {n : ℕ} {F : Fin (n + 4) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last (n + 1)).castSucc.castSucc))
    (d : ∀ i : Fin (n + 3), F i.succ →ₗ[S] F i.castSucc) :
    Function.Exact
        (LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
          (maximalIdeal R))
        (LinearMap.quotientMapByIdeal
          (((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                  @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R))
          (maximalIdeal R)) ↔
    Function.Exact
        (LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R))
        (LinearMap.quotientMapByIdeal ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
          (maximalIdeal R)) := by
  let e₁ :
      (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ ⧸
        (maximalIdeal R •
          (⊤ : Submodule R
            (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ)))) ≃ₗ[R]
        (C ⧸ (maximalIdeal R • (⊤ : Submodule R C))) :=
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ ≃ₗ[R] C)
  let e₂ :
      (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ⧸
        (maximalIdeal R •
          (⊤ : Submodule R
            (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc)))) ≃ₗ[R]
        (F ((Fin.last (n + 1)).castSucc.castSucc) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F ((Fin.last (n + 1)).castSucc.castSucc))))) :=
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[R]
          F ((Fin.last (n + 1)).castSucc.castSucc))
  let e₃ :
      (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ⧸
        (maximalIdeal R •
          (⊤ : Submodule R
            (@CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc)))) ≃ₗ[R]
        (F (castSucc (castSucc (castSucc (Fin.last n)))) ⧸
          (maximalIdeal R •
            (⊤ : Submodule R (F (castSucc (castSucc (castSucc (Fin.last n)))))))) :=
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n) :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[R]
          F (castSucc (castSucc (castSucc (Fin.last n)))))
  have htail :
      (((((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R).quotientMapByIdeal
            (maximalIdeal R))).comp e₂.symm.toLinearMap) =
        e₃.symm.toLinearMap.comp
          (LinearMap.quotientMapByIdeal
            ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
            (maximalIdeal R)) := by
    ext x
    have h :=
      LinearMap.congr_fun
        (CriteriaForFlatness.reducedShortenedFirstTailMap_ladder (R := R) (C := C) d)
        (e₂.symm x)
    simpa [LinearMap.comp_apply] using congrArg e₃.symm h
  calc
    Function.Exact
        (LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
          (maximalIdeal R))
        (LinearMap.quotientMapByIdeal
          (((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                  @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R))
          (maximalIdeal R))
      ↔ Function.Exact
          (e₂.toLinearMap.comp
            (LinearMap.quotientMapByIdeal
              ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
              (maximalIdeal R)))
          ((((LinearMap.quotientMapByIdeal
              (((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
                    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R))
              (maximalIdeal R))).comp e₂.symm.toLinearMap)) := by
              simpa [LinearMap.comp_assoc, e₂] using
                (LinearEquiv.conj_exact_iff_exact
                  (f := LinearMap.quotientMapByIdeal
                    ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
                    (maximalIdeal R))
                  (g := LinearMap.quotientMapByIdeal
                    (((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
                          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc).restrictScalars R))
                    (maximalIdeal R))
                  e₂).symm
    _ ↔ Function.Exact
          ((LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R)).comp
            e₁.toLinearMap)
          (e₃.symm.toLinearMap.comp
            (LinearMap.quotientMapByIdeal
              ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
              (maximalIdeal R))) := by
            rw [CriteriaForFlatness.reducedShortenedHeadMap_ladder (R := R), htail]
    _ ↔ Function.Exact
          (LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R))
          (e₃.symm.toLinearMap.comp
            (LinearMap.quotientMapByIdeal
              ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
              (maximalIdeal R))) := by
            simpa [LinearMap.comp_assoc, e₁] using
              (LinearEquiv.precomp_exact_iff_exact
                (f := LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R))
                (g := e₃.symm.toLinearMap.comp
                  (LinearMap.quotientMapByIdeal
                    ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
                    (maximalIdeal R)))
                (e := e₁))
    _ ↔ Function.Exact
          (LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R))
          (LinearMap.quotientMapByIdeal
            ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
            (maximalIdeal R)) := by
            simpa [LinearMap.comp_assoc, e₃] using
              (LinearEquiv.postcomp_exact_iff_exact
                (f := LinearMap.quotientMapByIdeal (w.restrictScalars R) (maximalIdeal R))
                (g := LinearMap.quotientMapByIdeal
                  ((d ((2 : Fin (n + 3)).rev)).restrictScalars R)
                  (maximalIdeal R))
                (e := e₃.symm))
/-- Helper for Lemma 10.99.5: injectivity of the reduced descended head map transports
across the reduced head endpoint equivalences to injectivity of the reduced shortened head map. -/
lemma reducedShortenedHeadInjective_of_raw
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (hrawHeadInjective :
      Function.Injective (((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R)))) :
    Function.Injective
      (LinearMap.quotientMapByIdeal
        ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
        (maximalIdeal R)) := by
  let e₁ :=
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)
  let e₂ :=
    CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
      (maximalIdeal R)
      (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
          F ((Fin.last n).castSucc.castSucc))
  have hladder := CriteriaForFlatness.reducedShortenedHeadMap_ladder (R := R) w
  intro x y hxy
  apply e₁.injective
  apply hrawHeadInjective
  have hx :
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
              F ((Fin.last n).castSucc.castSucc))) (((LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast w).restrictScalars R)
          (maximalIdeal R)) x)) =
        ((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))
          ((CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
            (maximalIdeal R)
            (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)) x) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hladder x
  have hy :
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
              F ((Fin.last n).castSucc.castSucc))) (((LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast w).restrictScalars R)
          (maximalIdeal R)) y)) =
        ((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))
          ((CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
            (maximalIdeal R)
            (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
              @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)) y) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hladder y
  calc
    ((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))
        ((CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)) x)
        =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
              F ((Fin.last n).castSucc.castSucc)))
        (((LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast w).restrictScalars R)
          (maximalIdeal R)) x)) := hx.symm
    _ =
      (CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[R]
              F ((Fin.last n).castSucc.castSucc)))
        (((LinearMap.quotientMapByIdeal
          ((CriteriaForFlatness.shortened_head_map_cast w).restrictScalars R)
          (maximalIdeal R)) y)) := by simpa [hxy]
    _ =
      ((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))
        ((CriteriaForFlatness.quotientSmulTopLinearEquivOfLinearEquiv
          (maximalIdeal R)
          (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[R] C)) y) := hy
/-- Helper for Lemma 10.99.5: injectivity of the shortened head map transports across the
endpoint linear equivalences to injectivity of the raw descended map `w`. -/
lemma shortenedDescendedMap_injective_of_castInjective
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc))
    (hcastInjective :
      Function.Injective (CriteriaForFlatness.shortened_head_map_cast   w)) :
    Function.Injective w := by
  let e₁ :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).succ ≃ₗ[S] C :=
    CriteriaForFlatness.shortenedHeadSourceLinearEquiv
  let e₂ :
      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
        F ((Fin.last n).castSucc.castSucc) :=
    CriteriaForFlatness.shortenedHeadTargetLinearEquiv
  have hladder := CriteriaForFlatness.shortenedHeadMap_ladder w
  intro x y hxy
  have hpre :
      e₁.symm x = e₁.symm y := by
    apply hcastInjective
    apply e₂.injective
    have hx :
        w x =
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
              F ((Fin.last n).castSucc.castSucc))
            ((CriteriaForFlatness.shortened_head_map_cast w) (e₁.symm x)) := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun hladder (e₁.symm x)).symm
    have hy :
        w y =
          (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
            @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
              F ((Fin.last n).castSucc.castSucc))
            ((CriteriaForFlatness.shortened_head_map_cast w) (e₁.symm y)) := by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun hladder (e₁.symm y)).symm
    calc
      (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
            F ((Fin.last n).castSucc.castSucc))
          ((CriteriaForFlatness.shortened_head_map_cast w) (e₁.symm x))
          = w x := hx.symm
      _ = w y := hxy
      _ =
        (CriteriaForFlatness.shortenedHeadTargetLinearEquiv :
          @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc ≃ₗ[S]
            F ((Fin.last n).castSucc.castSucc))
          ((CriteriaForFlatness.shortened_head_map_cast w) (e₁.symm y)) := hy
  exact e₁.symm.injective hpre
/-- Helper for Lemma 10.99.5: if the head cokernel `C` and the original tail modules are
finite over `S`, then every term of the shortened family is finite over `S`. -/
lemma shortenedFamily_finite
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C]
    (hfiniteC : Module.Finite S C)
    (hfinite : ∀ i, Module.Finite S (F i)) :
    ∀ i, Module.Finite S (@CriteriaForFlatness.shortenedFamily _ F C i) := by
  intro i
  refine Fin.lastCases
      (motive := fun j ↦ Module.Finite S (@CriteriaForFlatness.shortenedFamily _ F C j))
      ?_ ?_ i
  · simpa [CriteriaForFlatness.shortenedFamily] using hfiniteC
  · intro j
    simpa [CriteriaForFlatness.shortenedFamily] using hfinite j.castSucc.castSucc
/-- Helper for Lemma 10.99.5: if the head cokernel `C` and the original tail modules are
flat over `R`, then every term of the shortened family is flat over `R`. -/
lemma shortenedFamily_flat
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module R (F i)]
    [∀ i, IsScalarTower R S (F i)]
    {C : Type v} [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (hflatC : Module.Flat R C)
    (hflat : ∀ i, Module.Flat R (F i)) :
    ∀ i, Module.Flat R (@CriteriaForFlatness.shortenedFamily _ F C i) := by
  intro i
  refine Fin.lastCases
      (motive := fun j ↦ Module.Flat R (@CriteriaForFlatness.shortenedFamily _ F C j))
      ?_ ?_ i
  · simpa [CriteriaForFlatness.shortenedFamily] using hflatC
  · intro j
    simpa [CriteriaForFlatness.shortenedFamily] using hflat j.castSucc.castSucc
/-- Helper for Lemma 10.99.5: the shortened row remains a complex whenever the original
finite sequence is a complex. -/
lemma shortenedDifferentialIsComplex_of_isComplex
    {n : ℕ} {F : Fin (n + 3) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    (d : ∀ i : Fin (n + 2), F i.succ →ₗ[S] F i.castSucc)
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (huv :
      LinearMap.range (d (Fin.last (n + 1))) ≤
        LinearMap.ker (d (Fin.castSucc (Fin.last n)))) :
    let C := F (Fin.last (n + 1)).castSucc ⧸ LinearMap.range (d (Fin.last (n + 1)))
    let w :=
      (LinearMap.range (d (Fin.last (n + 1)))).liftQ
        (d (Fin.castSucc (Fin.last n))) huv
    (CriteriaForFlatness.finiteSequence
        (CriteriaForFlatness.shortenedDifferential   w d)).IsComplex := by
  let C := F (Fin.last (n + 1)).castSucc ⧸ LinearMap.range (d (Fin.last (n + 1)))
  let w :=
    (LinearMap.range (d (Fin.last (n + 1)))).liftQ
      (d (Fin.castSucc (Fin.last n))) huv
  have hrawZero :
      (d ((2 : Fin (n + 2)).rev)).comp w = 0 := by
    exact comp_liftQ_eq_zero_of_range_le_ker huv
      (CriteriaForFlatness.next_range_le_ker_of_isComplex d hcomplex)
  have hheadZero :
      (CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n)).comp
        (CriteriaForFlatness.shortened_head_map_cast w) = 0 := by
    let e₂ :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).castSucc ≃ₗ[S]
          F ((Fin.last (n + 1)).castSucc.castSucc) :=
      CriteriaForFlatness.shortenedHeadTargetLinearEquiv
    let e₃ :
        @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc ≃ₗ[S]
          F (castSucc (castSucc (castSucc (Fin.last n)))) :=
      CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n)
    have hcomp :
        e₃.toLinearMap.comp
          ((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n)).comp
            (CriteriaForFlatness.shortened_head_map_cast w)) = 0 := by
      calc
        e₃.toLinearMap.comp
            ((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n)).comp
              (CriteriaForFlatness.shortened_head_map_cast w))
            = (d ((2 : Fin (n + 2)).rev)).comp
                (e₂.toLinearMap.comp
                  (CriteriaForFlatness.shortened_head_map_cast w)) := by
                    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc,
                      CriteriaForFlatness.shortenedFirstTailMap_ladder (C := C) d]
        _ = (d ((2 : Fin (n + 2)).rev)).comp
              (w.comp
                (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
                  @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ ≃ₗ[S]
                    C).toLinearMap) := by
                      rw [CriteriaForFlatness.shortenedHeadMap_ladder]
        _ = ((d ((2 : Fin (n + 2)).rev)).comp w).comp
              (CriteriaForFlatness.shortenedHeadSourceLinearEquiv :
                @CriteriaForFlatness.shortenedFamily _ F C (Fin.last (n + 1)).succ ≃ₗ[S]
                  C).toLinearMap := by
                    rw [LinearMap.comp_assoc]
        _ = 0 := by simp [hrawZero]
    ext x
    apply (CriteriaForFlatness.shortenedTailTargetLinearEquiv (Fin.last n)).injective
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomp x
  have hdoubleTailComplex :
      ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).IsComplex := by
    refine ComposableArrows.IsComplex.mk ?_
    intro i hi
    simpa using hcomplex.zero (i + 2) (by omega)
  have hshortTailComplex :
      ((CriteriaForFlatness.finiteSequence
          (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).IsComplex :=
    ComposableArrows.isComplex_of_iso
      (CriteriaForFlatness.shortenedFiniteSequenceDelta0Iso   w d).symm
      hdoubleTailComplex
  refine ComposableArrows.IsComplex.mk ?_
  intro i hi
  obtain rfl | i := i
  · simpa [CriteriaForFlatness.finiteSequence_leftmost_map_eq,
      CriteriaForFlatness.finiteSequence_next_map_eq,
      CriteriaForFlatness.shortenedDifferential_last,
      CriteriaForFlatness.shortenedDifferential_castSucc] using
        (congrArg ModuleCat.ofHom hheadZero)
  · simpa using hshortTailComplex.zero i (by omega)
end CriteriaForFlatness
/-- Helper for Lemma 10.99.5: the augmented finite sequence is exact when its leftmost map is
injective and the packaged tail is exact. -/
class FiniteComplexExact
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc) : Prop where
  left_injective : Function.Injective (d (Fin.last n))
  tail_exact : (CriteriaForFlatness.finiteSequence d).Exact

/-- Chap10 Lemma 10 99 5: for a local homomorphism `R → S` of local Noetherian rings, if
`0 → F_{n+1}/𝔪F_{n+1} → F_n/𝔪F_n → ⋯ → F_0/𝔪F_0` is exact and every `F_i` is a finite `S`-module
flat over `R`, then `0 → F_{n+1} → F_n → ⋯ → F_0` is exact, and moreover the cokernel of
`F₁ → F₀` is flat over `R`. The middle exactness is organized by the canonical finite-sequence
owner `ComposableArrows.Exact`, while injectivity of the leftmost map remains the separate
source-facing edge condition. The source hypothesis that the displayed maps form a finite complex
is recorded by `hcomplex`. -/
@[stacks 00MI]
theorem exact_and_flat_cokernel_of_reducedFiniteComplexExact
    [IsNoetherianRing R]
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (hinjective_mod :
      Function.Injective
        (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))
    (hexact_mod : (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    FiniteComplexExact d ∧
      Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) := by
  induction n with
  | zero =>
      constructor
      · refine ⟨?_, ComposableArrows.exact₁ _⟩
        have h0 :
            Function.Injective ((d 0).restrictScalars R) := by
          exact injective_of_mod_maximalIdeal_injective
            (R := R) (S := S) (M := F 0) (N := F 1)
            ((d 0).restrictScalars R) hinjective_mod
        simpa using h0
      · simpa [LinearMap.range_restrictScalars] using
          flat_quotient_of_mod_maximalIdeal_injective
            (R := R) (S := S) (M := F 0) (N := F 1)
            ((d 0).restrictScalars R) hinjective_mod
  | succ n ih =>
      let u := d (Fin.last (n + 1))
      let v := d (Fin.castSucc (Fin.last n))
      let C := F (Fin.last (n + 1)).castSucc ⧸ LinearMap.range u
      let w : C →ₗ[S] F ((Fin.last n).castSucc.castSucc) :=
        (LinearMap.range u).liftQ v
          (CriteriaForFlatness.head_range_le_ker_of_isComplex d hcomplex)
      have huv : LinearMap.range u ≤ LinearMap.ker v :=
        CriteriaForFlatness.head_range_le_ker_of_isComplex d hcomplex
      have hu : Function.Injective u := by
        have huR : Function.Injective (u.restrictScalars R) := by
          exact injective_of_mod_maximalIdeal_injective
            (R := R) (S := S) (M := F (Fin.last (n + 1)).castSucc)
            (N := F (Fin.last (n + 2))) (u.restrictScalars R) hinjective_mod
        simpa [u] using huR
      have hfiniteC : Module.Finite S C :=
        finite_quotient_range u
      have hflatC : Module.Flat R C := by
        simpa [u, C, LinearMap.range_restrictScalars] using
          flat_quotient_of_mod_maximalIdeal_injective
            (R := R) (S := S) (M := F (Fin.last (n + 1)).castSucc)
            (N := F (Fin.last (n + 2))) (u.restrictScalars R) hinjective_mod
      have hfiniteShort :
          ∀ i, Module.Finite S (@CriteriaForFlatness.shortenedFamily _ F C i) :=
        CriteriaForFlatness.shortenedFamily_finite hfiniteC hfinite
      have hflatShort :
          ∀ i, Module.Flat R (@CriteriaForFlatness.shortenedFamily _ F C i) :=
        CriteriaForFlatness.shortenedFamily_flat hflatC hflat
      have hcomplexShort :
          (CriteriaForFlatness.finiteSequence
            (CriteriaForFlatness.shortenedDifferential   w d)).IsComplex := by
        simpa [w, C] using
          (CriteriaForFlatness.shortenedDifferentialIsComplex_of_isComplex
            d hcomplex huv : let C := F (Fin.last (n + 1)).castSucc ⧸ LinearMap.range u
              let w := (LinearMap.range u).liftQ v huv
              (CriteriaForFlatness.finiteSequence
                (CriteriaForFlatness.shortenedDifferential   w d)).IsComplex)
      have hpairRedCat :=
        ((ComposableArrows.exact_iff_δ₀ (CriteriaForFlatness.reducedFiniteSequence R d)).1
          hexact_mod).1
      have hpairRedShort := hpairRedCat.exact 0 (by omega)
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hpairRedShort
      have hpairRed :
          Function.Exact
            (((d (Fin.last (n + 1))).restrictScalars R).quotientMapByIdeal (maximalIdeal R))
            (((d (Fin.castSucc (Fin.last n))).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R)) := by
        simpa [u, v, CriteriaForFlatness.reducedFiniteSequence_leftmost_map_eq,
          CriteriaForFlatness.reducedFiniteSequence_next_map_eq] using hpairRedShort
      have htailRed : ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀).Exact :=
        ((ComposableArrows.exact_iff_δ₀ (CriteriaForFlatness.reducedFiniteSequence R d)).1
          hexact_mod).2
      have hnextRedCat := ((ComposableArrows.exact_iff_δ₀
        ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀)).1 htailRed).1
      have hnextRedShort := hnextRedCat.exact 0 (by omega)
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hnextRedShort
      have hnextRed :
          Function.Exact
            (((d (Fin.castSucc (Fin.last n))).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R))
            (((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R)) := by
        simpa [v, CriteriaForFlatness.reducedFiniteSequence_next_map_eq,
          CriteriaForFlatness.reducedFiniteSequence_third_map_eq] using hnextRedShort
      have hrawHeadInjective :
          Function.Injective (((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R))) := by
        simpa [w] using
          (CriteriaForFlatness.reduced_descended_head_injective
            (R := R) (S := S) (I := maximalIdeal R) u v huv hpairRed)
      have hinjectiveShort_mod :
          Function.Injective
            ((((CriteriaForFlatness.shortenedDifferential   w d) (Fin.last n)).restrictScalars R)
              .quotientMapByIdeal (maximalIdeal R)) := by
        simpa [CriteriaForFlatness.shortenedDifferential_last, w] using
          (CriteriaForFlatness.reducedShortenedHeadInjective_of_raw
            (R := R) (w := w) hrawHeadInjective)
      have hrawHeadRedExact :
          Function.Exact
            (((w.restrictScalars R).quotientMapByIdeal (maximalIdeal R)))
            (((d ((2 : Fin (n + 3)).rev)).restrictScalars R).quotientMapByIdeal
              (maximalIdeal R)) := by
        simpa [w] using
          (CriteriaForFlatness.reduced_descended_head_exact
            (R := R) (S := S) (I := maximalIdeal R) u v
            (d ((2 : Fin (n + 3)).rev)) huv hpairRed hnextRed)
      have hshortHeadRedExact :
          Function.Exact
            (LinearMap.quotientMapByIdeal
              ((CriteriaForFlatness.shortened_head_map_cast   w).restrictScalars R)
              (maximalIdeal R))
            (LinearMap.quotientMapByIdeal
              (((CriteriaForFlatness.shortened_tail_map_cast d (Fin.last n) :
                    @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.succ →ₗ[S]
                      @CriteriaForFlatness.shortenedFamily _ F C (Fin.last n).castSucc.castSucc)
                  .restrictScalars R))
              (maximalIdeal R)) :=
        (CriteriaForFlatness.reducedShortenedHeadPairExact_iff_raw
          (R := R) (w := w) (d := d)).2 hrawHeadRedExact
      have hdoubleTailRed :
          ((CriteriaForFlatness.reducedFiniteSequence R d).δ₀.δ₀).Exact :=
        htailRed.δ₀
      have hshortTailRed :
          (CriteriaForFlatness.reducedFiniteSequence R
            (CriteriaForFlatness.shortenedDifferential   w d)).δ₀.Exact :=
        (CriteriaForFlatness.reducedShortenedFiniteSequenceDelta0_exact_iff
          (R := R) (w := w) (d := d)).2 hdoubleTailRed
      have hshortHeadRedCat :
          (ComposableArrows.mk₂
            ((CriteriaForFlatness.reducedFiniteSequence R
                (CriteriaForFlatness.shortenedDifferential   w d)).map' 0 1)
            ((CriteriaForFlatness.reducedFiniteSequence R
                (CriteriaForFlatness.shortenedDifferential   w d)).map' 1 2)).Exact := by
        simpa [CriteriaForFlatness.reducedFiniteSequence_leftmost_map_eq,
          CriteriaForFlatness.reducedFiniteSequence_next_map_eq,
          CriteriaForFlatness.shortenedDifferential_last,
          CriteriaForFlatness.shortenedDifferential_castSucc] using
            (composableArrowsExact₂_of_functionExact (T := R) hshortHeadRedExact)
      have hexactShort_mod :
          (CriteriaForFlatness.reducedFiniteSequence R
            (CriteriaForFlatness.shortenedDifferential   w d)).Exact :=
        ComposableArrows.exact_of_δ₀ hshortHeadRedCat hshortTailRed
      have hshort :=
        ih (F := CriteriaForFlatness.shortenedFamily C)
          (d := CriteriaForFlatness.shortenedDifferential   w d)
          hfiniteShort hflatShort hcomplexShort hinjectiveShort_mod hexactShort_mod
      have hwCastInjective :
          Function.Injective (CriteriaForFlatness.shortened_head_map_cast   w) := by
        simpa [CriteriaForFlatness.shortenedDifferential_last, w] using
          hshort.1.left_injective
      have hw : Function.Injective w :=
        CriteriaForFlatness.shortenedDescendedMap_injective_of_castInjective
          (w := w) hwCastInjective
      have hshortHeadCat :=
        ((ComposableArrows.exact_iff_δ₀
            (CriteriaForFlatness.finiteSequence
              (CriteriaForFlatness.shortenedDifferential   w d))).1
          hshort.1.tail_exact).1
      have hshortHeadShort := hshortHeadCat.exact 0 (by omega)
      rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hshortHeadShort
      have hshortHead :
          Function.Exact
            (CriteriaForFlatness.shortened_head_map_cast   w)
            (CriteriaForFlatness.shortened_tail_map_cast   d (Fin.last n)) := by
        simpa [CriteriaForFlatness.finiteSequence_leftmost_map_eq,
          CriteriaForFlatness.finiteSequence_next_map_eq,
          CriteriaForFlatness.shortenedDifferential_last,
          CriteriaForFlatness.shortenedDifferential_castSucc] using hshortHeadShort
      have hrawHead :
          Function.Exact w (d ((2 : Fin (n + 3)).rev)) :=
        (CriteriaForFlatness.shortenedHeadPairExact_iff_raw (w := w) (d := d)).1 hshortHead
      have hnext :
          Function.Exact (d (Fin.castSucc (Fin.last n))) (d ((2 : Fin (n + 3)).rev)) := by
        exact exact_of_exact_range_liftQ huv hrawHead
      have hshortTail :
          ((CriteriaForFlatness.finiteSequence
              (CriteriaForFlatness.shortenedDifferential   w d)).δ₀).Exact :=
        ((ComposableArrows.exact_iff_δ₀
            (CriteriaForFlatness.finiteSequence
              (CriteriaForFlatness.shortenedDifferential   w d))).1
          hshort.1.tail_exact).2
      have hdoubleTail :
          ((CriteriaForFlatness.finiteSequence d).δ₀.δ₀).Exact :=
        (CriteriaForFlatness.shortenedFiniteSequenceDelta0_exact_iff
          w d).1 hshortTail
      have hnextCat :
          (ComposableArrows.mk₂
            (((CriteriaForFlatness.finiteSequence d).δ₀).map' 0 1)
            (((CriteriaForFlatness.finiteSequence d).δ₀).map' 1 2)).Exact := by
        simpa [CriteriaForFlatness.finiteSequence_next_map_eq,
          CriteriaForFlatness.finiteSequence_third_map_eq] using
            (composableArrowsExact₂_of_functionExact (T := S) hnext)
      have htail :
          ((CriteriaForFlatness.finiteSequence d).δ₀).Exact :=
        ComposableArrows.exact_of_δ₀ hnextCat hdoubleTail
      have hhead : Function.Exact u v :=
        exact_of_injective_range_liftQ huv hw
      have hheadCat :
          (ComposableArrows.mk₂
            ((CriteriaForFlatness.finiteSequence d).map' 0 1)
            ((CriteriaForFlatness.finiteSequence d).map' 1 2)).Exact := by
        simpa [u, v, CriteriaForFlatness.finiteSequence_leftmost_map_eq,
          CriteriaForFlatness.finiteSequence_next_map_eq] using
            (composableArrowsExact₂_of_functionExact (T := S) hhead)
      have hexact : (CriteriaForFlatness.finiteSequence d).Exact :=
        ComposableArrows.exact_of_δ₀ hheadCat htail
      have hflat0 : Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) := by
        simpa [CriteriaForFlatness.shortenedFamily, CriteriaForFlatness.shortenedDifferential,
          CriteriaForFlatness.shortened_tail_map_cast, w, C] using hshort.2
      exact ⟨⟨hu, hexact⟩, hflat0⟩

/-- Projection helper: exactness part of
`exact_and_flat_cokernel_of_reducedFiniteComplexExact`. -/
theorem finiteComplexExact_of_reducedFiniteComplexExact
    [IsNoetherianRing R]
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (hexact_mod :
      Function.Injective
          (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) ∧
        (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    FiniteComplexExact d :=
  (exact_and_flat_cokernel_of_reducedFiniteComplexExact
    d hfinite hflat hcomplex hexact_mod.1 hexact_mod.2).1
/-- Projection helper: flat-cokernel part of
`exact_and_flat_cokernel_of_reducedFiniteComplexExact`. -/
theorem flat_cokernel_of_reducedFiniteComplexExact
    [IsNoetherianRing R]
    (d : ∀ i : Fin (n + 1), F i.succ →ₗ[S] F i.castSucc)
    (hfinite : ∀ i, Module.Finite S (F i))
    (hflat : ∀ i, Module.Flat R (F i))
    (hcomplex : (CriteriaForFlatness.finiteSequence d).IsComplex)
    (hinjective_mod :
      Function.Injective
        (((d (Fin.last n)).restrictScalars R).quotientMapByIdeal (maximalIdeal R)))
    (hexact_mod : (CriteriaForFlatness.reducedFiniteSequence R d).Exact) :
    Module.Flat R (F 0 ⧸ LinearMap.range (d 0)) :=
  (exact_and_flat_cokernel_of_reducedFiniteComplexExact
    d hfinite hflat hcomplex hinjective_mod hexact_mod).2
end CriteriaForFlatness
