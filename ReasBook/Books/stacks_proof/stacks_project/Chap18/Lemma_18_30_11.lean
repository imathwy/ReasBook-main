import Mathlib
import StacksProject_2024.Chap12.Definition_12_10_1
import StacksProject_2024.Chap18.Lemma_18_30_7
import StacksProject_2024.Chap18.Situation_18_30_5
import StacksProject_2024.Chap18.Lemma_18_30_9
import StacksProject_2024.Chap18.Lemma_18_30_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "P" => HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B

variable {J 𝒪 B}

section Helpers

/-- Helper for Lemma 18.30.11: the zero module already has a finite basis cokernel presentation,
using the empty finite coproduct of basis summands. -/
private lemma hasFiniteBasisConstructibleModuleCokernelPresentation_zero :
    P (J := J) (𝒪 := 𝒪) (B := B) (0 : Mod) := by
  let A : Mod := ∐ fun i : Fin 0 ↦ localizedStructureModuleExtensionByZero 𝒪 (Fin.elim0 i)
  have hA : P (J := J) (𝒪 := 𝒪) (B := B) A :=
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_basisCoproduct
      (J := J) (𝒪 := 𝒪) (B := B) (U := Fin.elim0) (hU := Fin.elim0)
  have hZeroA : IsZero A := by
    infer_instance
  -- Proof comment: the empty finite coproduct is a zero object, so its finite presentation
  -- transports directly to the ambient zero module.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) hZeroA.isoZero hA

/-- Helper for Lemma 18.30.11: after refining a presentation by Lemma `18.30.9`, the induced
map on cokernels is exactly the descended map coming from the lifted morphism on refined
generators. -/
private lemma refinedCokernelMap_eq_desc
    {n m : ℕ} {K : Fin n → Type*}
    {U : Fin n → C} {V : Fin m → C}
    (Ucover : ∀ i : Fin n, K i → C)
    (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (w :
      FiniteBasisRefinementInducingCokernelIsoWitness
        (J := J) (𝒪 := 𝒪) (B := B) U V Ucover f)
    {X : Mod}
    (α :
      (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ X)
    (hα : f ≫ α = 0)
    (u : _ ⟶ X)
    (hu : w.right ≫ α = u) :
    cokernel.map w.top f w.left w.right w.comm ≫ cokernel.desc f α hα =
      cokernel.desc w.top u (by
        -- Proof comment: the lifted morphism on the refined generators kills `w.top` because the
        -- refinement square commutes and `α` already kills the original relation map `f`.
        calc
          w.top ≫ u = w.top ≫ w.right ≫ α := by rw [hu]; simp [Category.assoc]
          _ = w.left ≫ f ≫ α := by rw [w.comm]; simp [Category.assoc]
          _ = 0 := by simp [hα, Category.assoc]) := by
  apply (cancel_epi (cokernel.π w.top)).1
  -- Proof comment: both morphisms out of `cokernel w.top` agree after precomposing with the
  -- cokernel projection, so the universal property of `cokernel w.top` identifies them.
  rw [Category.assoc, Category.assoc, cokernel.π_desc_assoc, cokernel.π_desc]
  simpa [hu, w.comm, Category.assoc] using
    (CokernelCofork.π_mapOfIsColimit_assoc
      (cokernelIsCokernel w.top)
      (CokernelCofork.ofπ (cokernel.π f) (by simpa using cokernel.condition f))
      (Arrow.homMk w.left w.right w.comm)
      (cokernel.desc f α hα))

/-- Helper for Lemma 18.30.11: once a refined source presentation lifts the morphism `φ`,
transporting the kernel result back to the original presentation is formal. -/
private lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_refinedKernel
    {n₁ m₁ n₂ m₂ : ℕ} {K : Fin n₁ → Type*}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (Ucover : ∀ i : Fin n₁, K i → C)
    (f₁ :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (f₂ :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f₁ ⟶ cokernel f₂)
    (w :
      FiniteBasisRefinementInducingCokernelIsoWitness
        (J := J) (𝒪 := 𝒪) (B := B) U₁ V₁ Ucover f₁)
    (u : _ ⟶ (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (hu : w.right ≫ (cokernel.π f₁ ≫ φ) = u ≫ cokernel.π f₂)
    (hKernel :
      P (J := J) (𝒪 := 𝒪) (B := B)
        (kernel
          (cokernel.desc w.top (u ≫ cokernel.π f₂) (by
            -- Proof comment: the refined lift to the target generators kills `w.top`.
            calc
              w.top ≫ (u ≫ cokernel.π f₂) = (w.top ≫ w.right) ≫ (cokernel.π f₁ ≫ φ) := by
                rw [hu]
                simp [Category.assoc]
              _ = (w.left ≫ f₁) ≫ (cokernel.π f₁ ≫ φ) := by rw [w.comm]
              _ = 0 := by simp [Category.assoc]))) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel φ) := by
  let e₁ : cokernel w.top ≅ cokernel f₁ :=
    asIso (cokernel.map w.top f₁ w.left w.right w.comm)
  have hdesc :
      e₁.hom ≫ φ =
        cokernel.desc w.top (u ≫ cokernel.π f₂) (by
          -- Proof comment: this is exactly the refined presentation identity recorded above.
          calc
            w.top ≫ (u ≫ cokernel.π f₂) = (w.top ≫ w.right) ≫ (cokernel.π f₁ ≫ φ) := by
              rw [hu]
              simp [Category.assoc]
            _ = (w.left ≫ f₁) ≫ (cokernel.π f₁ ≫ φ) := by rw [w.comm]
            _ = 0 := by simp [Category.assoc]) := by
    simpa [e₁] using
      refinedCokernelMap_eq_desc
        (J := J) (𝒪 := 𝒪) (B := B)
        Ucover f₁ w (cokernel.π f₁ ≫ φ)
        (by simp [Category.assoc]) (u ≫ cokernel.π f₂) hu
  let eKernel :
      kernel (cokernel.desc w.top (u ≫ cokernel.π f₂) (by
        calc
          w.top ≫ (u ≫ cokernel.π f₂) = (w.top ≫ w.right) ≫ (cokernel.π f₁ ≫ φ) := by
            rw [hu]
            simp [Category.assoc]
          _ = (w.left ≫ f₁) ≫ (cokernel.π f₁ ≫ φ) := by rw [w.comm]
          _ = 0 := by simp [Category.assoc])) ≅ kernel φ :=
    kernel.mapIso
      (cokernel.desc w.top (u ≫ cokernel.π f₂) (by
        calc
          w.top ≫ (u ≫ cokernel.π f₂) = (w.top ≫ w.right) ≫ (cokernel.π f₁ ≫ φ) := by
            rw [hu]
            simp [Category.assoc]
          _ = (w.left ≫ f₁) ≫ (cokernel.π f₁ ≫ φ) := by rw [w.comm]
          _ = 0 := by simp [Category.assoc]))
      φ e₁.symm (Iso.refl _) (by
        -- Proof comment: `φ` is the conjugate of the refined descended morphism through `e₁`.
        simpa [Category.assoc] using hdesc.symm)
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eKernel hKernel

/-- Helper for Lemma 18.30.11: for a quotient map `cokernel.π t` and a descended morphism out of
its cokernel, the kernel of the descended morphism is the cokernel of the induced map from the
relation object into the kernel of the lifted map. -/
private lemma kernelDescIso_cokernelKernelLift
    {W A X : Mod}
    (t : W ⟶ A)
    (g : A ⟶ X)
    (h : t ≫ g = 0) :
    kernel (cokernel.desc t g h) ≅ cokernel (kernel.lift g t h) := by
  let q : A ⟶ cokernel t := cokernel.π t
  let δ : cokernel t ⟶ X := cokernel.desc t g h
  let κ : W ⟶ kernel g := kernel.lift g t h
  let L₁ : ShortComplex Mod :=
    ShortComplex.mk t q (by simpa using cokernel.condition t)
  let L₂ : ShortComplex Mod :=
    ShortComplex.mk (kernel.ι g) g (by simpa using kernel.condition g)
  let φ : L₁ ⟶ L₂ :=
    ShortComplex.Hom.mk κ (𝟙 A) δ
      (by
        -- Proof comment: the left square is exactly the defining equation of `kernel.lift`.
        simpa [κ] using kernel.lift_ι g t h)
      (by
        -- Proof comment: the right square is exactly the defining equation of `cokernel.desc`.
        simpa [q, δ, Category.assoc] using cokernel.π_desc t g h)
  let S : ShortComplex.SnakeInput Mod where
    L₀ := kernel φ
    L₁ := L₁
    L₂ := L₂
    L₃ := cokernel φ
    v₀₁ := kernel.ι φ
    v₁₂ := φ
    v₂₃ := cokernel.π φ
    h₀ := kernelIsKernel φ
    h₃ := cokernelIsCokernel φ
    L₁_exact := by
      -- Proof comment: the upper row is the canonical cokernel sequence of `t`.
      simpa [L₁] using ShortComplex.exact_of_g_is_cokernel L₁ (cokernelIsCokernel t)
    epi_L₁_g := by
      dsimp [L₁, q]
      infer_instance
    L₂_exact := by
      -- Proof comment: the lower row is the canonical kernel sequence of `g`.
      simpa [L₂] using ShortComplex.exact_of_f_is_kernel L₂ (kernelIsKernel g)
    mono_L₂_f := by
      dsimp [L₂]
      infer_instance
  have hZeroL₀X₂ : IsZero S.L₀.X₂ := by
    let e :
        S.L₀.X₂ ≅ kernel (𝟙 A) :=
      IsLimit.conePointUniqueUpToIso S.h₀τ₂ (kernelIsKernel (𝟙 A))
    have hId : IsZero (kernel (𝟙 A)) := by
      exact Limits.IsZero.of_iso (Limits.isZero_zero _) (kernel.ofMono (𝟙 A))
    -- Proof comment: the middle kernel row term is a kernel of the identity, hence zero.
    exact Limits.IsZero.of_iso hId e
  have hZeroL₃X₂ : IsZero S.L₃.X₂ := by
    let e :
        S.L₃.X₂ ≅ cokernel (𝟙 A) :=
      IsColimit.coconePointUniqueUpToIso S.h₃τ₂ (cokernelIsCokernel (𝟙 A))
    have hId : IsZero (cokernel (𝟙 A)) := by
      exact Limits.IsZero.of_iso (Limits.isZero_zero _) (cokernel.ofEpi (𝟙 A))
    -- Proof comment: the middle cokernel row term is a cokernel of the identity, hence zero.
    exact Limits.IsZero.of_iso hId e
  let eKernel :
      kernel δ ≅ S.L₀.X₃ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel δ) S.h₀τ₃
  let eCokernel :
      S.L₃.X₁ ≅ cokernel κ :=
    IsColimit.coconePointUniqueUpToIso S.h₃τ₁ (cokernelIsCokernel κ)
  -- Proof comment: the snake lemma for the comparison between the cokernel sequence of `t` and
  -- the kernel sequence of `g` has zero middle terms, so its connecting morphism is an
  -- isomorphism from `kernel δ` to `cokernel κ`.
  exact eKernel ≪≫ S.δIso hZeroL₀X₂ hZeroL₃X₂ ≪≫ eCokernel

/-- Helper for Lemma 18.30.11: the kernel of a morphism between explicit finite cokernel
presentations again admits a finite basis cokernel presentation. -/
private lemma presentationQuotientKernel_hasFiniteBasisConstructibleModuleCokernelPresentation
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f))
    {n m : ℕ}
    (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B)
    (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel (cokernel.π f)) := by
  have hφZero : f ≫ cokernel.π f = 0 := by
    simpa using cokernel.condition f
  let φ :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        kernel (cokernel.π f) :=
    kernel.lift (cokernel.π f) f hφZero
  have hφι : φ ≫ kernel.ι (cokernel.π f) = f := by
    simpa [φ] using kernel.lift_ι (cokernel.π f) f hφZero
  have hKernelCompZero : kernel.ι f ≫ φ = 0 := by
    apply (cancel_mono (kernel.ι (cokernel.π f))).1
    simpa [Category.assoc, hφι] using kernel.condition f
  let hKernelφ :
      IsLimit (KernelFork.ofι (kernel.ι f) hKernelCompZero) :=
    isKernelOfComp
      (f := φ)
      (g := kernel.ι (cokernel.π f))
      (h := f)
      (kernelIsKernel f)
      hKernelCompZero
      hφι
  let eKernel : kernel f ≅ kernel φ :=
    IsLimit.conePointUniqueUpToIso hKernelφ (limit.isLimit _)
  have hKernelφPresentation :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel φ) := by
    -- Proof comment: composing `φ` with the mono `kernel.ι (cokernel.π f)` recovers `f`, so
    -- the kernel of `φ` is the already-controlled kernel of `f`.
    exact
      CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
        (J := J) (𝒪 := 𝒪) (B := B) eKernel
        (hkernel U V hU hV f)
  -- Proof comment: `presentationKernelCoverEpi` supplies an epimorphism from the relation
  -- coproduct onto `kernel (cokernel.π f)`, and the preceding paragraph identifies its kernel
  -- with the already-controlled kernel of `f`.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_epi_from_basisCoproduct
      (J := J) (𝒪 := 𝒪) (B := B)
      V hV φ (𝟙 (kernel φ)) hKernelφPresentation

/-- Helper for Lemma 18.30.11: the kernel hypothesis can be applied after reindexing finite
coproducts by `Fin`. -/
private lemma kernel_of_finiteTypes_hasFiniteBasisConstructibleModuleCokernelPresentation
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f))
    {A K : Type*} [Fintype A] [Fintype K]
    (U : A → C) (V : K → C)
    (hU : ∀ a, U a ∈ B) (hV : ∀ k, V k ∈ B)
    (f :
      (∐ fun k : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V k)) ⟶
        (∐ fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a))) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel f) := by
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eK : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let sourceIso :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ≅
        (∐ fun k : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V k)) :=
    Limits.Sigma.reindex eK (fun k : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V k))
  let targetIso :
      (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) ≅
        (∐ fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a)) :=
    Limits.Sigma.reindex eA (fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a))
  let f' :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) :=
    sourceIso.hom ≫ f ≫ targetIso.inv
  have hKernel' :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel f') :=
    hkernel
      (fun i ↦ U (eA i))
      (fun j ↦ V (eK j))
      (by
        intro i
        exact hU (eA i))
      (by
        intro j
        exact hV (eK j))
      f'
  let eKernel : kernel f' ≅ kernel f :=
    kernel.mapIso f' f sourceIso targetIso (by simp [f', Category.assoc])
  -- Proof comment: after reindexing the finite source and target families to `Fin`, the kernel
  -- hypothesis applies directly and the result transports back along the induced kernel isomorphism.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eKernel hKernel'

/-- Helper for Lemma 18.30.11: postcomposing by an epimorphism does not change the kernel object.
-/
private lemma kernelIsoOfCompRightEpi
    {A B X : Mod} (u : A ⟶ B) (v : B ⟶ X) [Epi v] :
    kernel u ≅ kernel (u ≫ v) := by
  let hom : kernel u ⟶ kernel (u ≫ v) :=
    kernel.map u (u ≫ v) (𝟙 A) v (by simp)
  let inv : kernel (u ≫ v) ⟶ kernel u :=
    kernel.lift u (kernel.ι (u ≫ v)) (by
      apply (cancel_epi v).1
      simpa [Category.assoc] using kernel.condition (u ≫ v))
  refine
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Proof comment: compare both endomorphisms after the kernel inclusion of `u`.
    apply (cancel_mono (kernel.ι u)).1
    simp [hom, inv, Category.assoc, kernel.map]
  · -- Proof comment: compare both endomorphisms after the kernel inclusion of `u ≫ v`.
    apply (cancel_mono (kernel.ι (u ≫ v))).1
    simp [hom, inv, Category.assoc, kernel.map]

/-- Helper for Lemma 18.30.11: the kernel of a morphism between explicit finite cokernel
presentations again admits a finite basis cokernel presentation. -/
private lemma basisToPresentedKernel_hasFiniteBasisConstructibleModuleCokernelPresentation
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f))
    {n₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f₂ :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (α :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⟶
        cokernel f₂) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel α) := by
  obtain ⟨r, W, _, hW, _, left, u, hleft, _, hu⟩ :=
    SheafOfModules.RingedSite.existsFiniteBasisLiftCoverOfEpi
      (J := J) (𝒪 := 𝒪) (B := B) U₁ hU₁ α (cokernel.π f₂)
  letI : Epi left := hleft
  have hKernelLeft :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel left) :=
    kernel_of_finiteTypes_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) hkernel U₁ (fun a : Σ i : Fin n₁, Fin (r i) ↦ W a.1 a.2)
      hU₁
      (by
        intro a
        exact hW a.1 a.2)
      left
  have hKernelU :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel u) :=
    kernel_of_finiteTypes_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) hkernel U₂ (fun a : Σ i : Fin n₁, Fin (r i) ↦ W a.1 a.2)
      hU₂
      (by
        intro a
        exact hW a.1 a.2)
      u
  let eKernelU : kernel u ≅ kernel (u ≫ cokernel.π f₂) :=
    kernelIsoOfCompRightEpi (u := u) (v := cokernel.π f₂)
  have hKernelLifted :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel (u ≫ cokernel.π f₂)) :=
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eKernelU hKernelU
  have hKernelComp :
      kernel.ι left ≫ (u ≫ cokernel.π f₂) = 0 := by
    -- Proof comment: the refined lift equation `u ≫ cokernel.π f₂ = left ≫ α` turns the kernel
    -- relation of `left` into the vanishing needed to descend along `kernel.ι left`.
    rw [hu]
    simp [Category.assoc]
  let λ : kernel left ⟶ kernel (u ≫ cokernel.π f₂) :=
    kernel.lift (u ≫ cokernel.π f₂) (kernel.ι left) hKernelComp
  have hCokernelLambda :
      P (J := J) (𝒪 := 𝒪) (B := B) (cokernel λ) := by
    rcases hKernelLeft with ⟨nLeft, mLeft, ULeft, VLeft, fLeft, eLeft, hULeft, hVLeft⟩
    rcases hKernelLifted with
      ⟨nLifted, mLifted, ULifted, VLifted, fLifted, eLifted, hULifted, hVLifted⟩
    let λ' : cokernel fLeft ⟶ cokernel fLifted :=
      eLeft.inv ≫ λ ≫ eLifted.hom
    have hLambda' :
        P (J := J) (𝒪 := 𝒪) (B := B) (cokernel λ') :=
      ringedSite_constructibleModule_cokernel_of_morphism
        (J := J) (𝒪 := 𝒪) (B := B)
        ULeft VLeft ULifted VLifted
        hULeft hVLeft hULifted hVLifted
        fLeft fLifted λ'
    let eCokernel : cokernel λ' ≅ cokernel λ :=
      cokernel.mapIso λ' λ eLeft.symm eLifted.symm (by
        -- Proof comment: `λ'` is exactly `λ` written through the chosen kernel presentations.
        simp [λ', Category.assoc])
    exact
      CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
        (J := J) (𝒪 := 𝒪) (B := B) eCokernel hLambda'
  let coforkLeft : CokernelCofork (kernel.ι left) :=
    CokernelCofork.ofπ left (by simpa using kernel.condition left)
  have hcoforkLeft : IsColimit coforkLeft := by
    let S : ShortComplex Mod :=
      ShortComplex.mk (kernel.ι left) left (by simpa using kernel.condition left)
    have hSExact : S.Exact := by
      -- Proof comment: the kernel row of the epimorphism `left` is exact.
      simpa [S] using ShortComplex.exact_of_f_is_kernel S (kernelIsKernel left)
    obtain ⟨hcolim⟩ := (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hSExact, inferInstance⟩
    simpa [coforkLeft] using hcolim
  let eLeft :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ≅
        cokernel (kernel.ι left) :=
    IsColimit.coconePointUniqueUpToIso hcoforkLeft (cokernelIsCokernel (kernel.ι left))
  have hleft_eLeft :
      left ≫ eLeft.hom = cokernel.π (kernel.ι left) := by
    -- Proof comment: the chosen cokernel isomorphism identifies the presentation quotient map
    -- `left` with the canonical cokernel projection.
    simp [eLeft, coforkLeft]
  let δ : cokernel (kernel.ι left) ⟶ cokernel f₂ :=
    cokernel.desc (kernel.ι left) (u ≫ cokernel.π f₂) hKernelComp
  have hdesc :
      eLeft.hom ≫ δ = α := by
    apply (cancel_epi left).1
    -- Proof comment: both maps out of the quotient `A₁ ≅ cokernel (kernel.ι left)` are determined
    -- by their composite with the epimorphic cover map `left`.
    rw [Category.assoc, hleft_eLeft, cokernel.π_desc]
    simpa [Category.assoc] using hu
  have hKernelDelta :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel δ) := by
    let eDesc :
        kernel δ ≅ cokernel λ :=
      kernelDescIso_cokernelKernelLift
        (J := J) (𝒪 := 𝒪) (B := B)
        (kernel.ι left) (u ≫ cokernel.π f₂) hKernelComp
    -- Proof comment: the descended kernel is the cokernel of the induced map from the refined
    -- source relation object into the lifted target kernel.
    exact
      CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
        (J := J) (𝒪 := 𝒪) (B := B) eDesc hCokernelLambda
  let eKernel : kernel α ≅ kernel δ :=
    kernel.mapIso α δ eLeft (Iso.refl _) (by
      -- Proof comment: after identifying the source with `cokernel (kernel.ι left)`, the
      -- original map `α` is exactly the descended morphism `δ`.
      simpa [Category.assoc] using hdesc)
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eKernel hKernelDelta

/-- Helper for Lemma 18.30.11: the kernel of a morphism between explicit finite cokernel
presentations again admits a finite basis cokernel presentation. -/
private lemma presentedKernel_hasFiniteBasisConstructibleModuleCokernelPresentation
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f))
    {n₁ m₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B) (hV₁ : ∀ j, V₁ j ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f₁ :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (f₂ :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f₁ ⟶ cokernel f₂) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel φ) := by
  let α : (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⟶ cokernel f₂ :=
    cokernel.π f₁ ≫ φ
  have hKernelAlpha :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel α) :=
    basisToPresentedKernel_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) hkernel U₁ U₂ V₂ hU₁ hU₂ hV₂ f₂ α
  let κ :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        kernel α :=
    kernel.lift α f₁ (by simp [α, Category.assoc])
  have hCokernelκ :
      P (J := J) (𝒪 := 𝒪) (B := B) (cokernel κ) :=
    by
      rcases hKernelAlpha with ⟨nα, mα, Uα, Vα, fα, eα, hUα, hVα⟩
      let f₀ :
          (∐ fun j : Fin 0 ↦ localizedStructureModuleExtensionByZero 𝒪 (Fin.elim0 j)) ⟶
            (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) :=
        0
      let e₀ :
          cokernel f₀ ≅
            (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) :=
        CategoryTheory.Limits.cokernelZeroIsoTarget
      let κ' : cokernel f₀ ⟶ cokernel fα :=
        e₀.hom ≫ κ ≫ eα.hom
      have hκ' :
          P (J := J) (𝒪 := 𝒪) (B := B) (cokernel κ') :=
        ringedSite_constructibleModule_cokernel_of_morphism
          (J := J) (𝒪 := 𝒪) (B := B)
          V₁ (fun j : Fin 0 ↦ Fin.elim0 j) Uα Vα
          hV₁ Fin.elim0 hUα hVα f₀ fα κ'
      let eCokernel : cokernel κ' ≅ cokernel κ :=
        cokernel.mapIso κ' κ e₀ eα.symm (by
          -- Proof comment: `κ'` is exactly `κ` expressed through the chosen source and target
          -- presentations.
          simp [κ', Category.assoc])
      exact
        CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
          (J := J) (𝒪 := 𝒪) (B := B) eCokernel hκ'
  have hKernelDesc :
      P (J := J) (𝒪 := 𝒪) (B := B)
        (kernel
          (cokernel.desc f₁ α (by
            -- Proof comment: `α` is the presentation-level representative of `φ`, so it
            -- annihilates `f₁` by the cokernel relation.
            simp [α, Category.assoc]))) := by
    let e :
        cokernel κ ≅
          kernel
            (cokernel.desc f₁ α (by
              simp [α, Category.assoc])) :=
      (kernelDescIso_cokernelKernelLift
        (J := J) (𝒪 := 𝒪) (B := B)
        f₁ α (by simp [α, Category.assoc])).symm
    -- Proof comment: the generic kernel-of-descended-map comparison turns the kernel problem into
    -- a cokernel problem for the map into `kernel α`.
    exact
      CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
        (J := J) (𝒪 := 𝒪) (B := B) e hCokernelκ
  have hdesc :
      cokernel.desc f₁ α (by simp [α, Category.assoc]) = φ := by
    apply (cancel_epi (cokernel.π f₁)).1
    -- Proof comment: both descended maps are determined by their composite with
    -- `cokernel.π f₁`.
    simp [α, Category.assoc]
  simpa [hdesc] using hKernelDesc

/-- Helper for Lemma 18.30.11: adjoining a finite lifted cover to a presentation map produces a
presentation of the cokernel of the descended morphism. -/
private lemma cokernelIso_of_appendedFiniteLift
    {R S T C' : Mod}
    (g : R ⟶ T) (α : S ⟶ cokernel g) (δ : C' ⟶ S) (β : C' ⟶ T)
    [Epi δ]
    (hcomm : δ ≫ α = β ≫ cokernel.π g) :
    cokernel (coprod.desc β g) ≅ cokernel α := by
  let l : cokernel g ⟶ cokernel (coprod.desc β g) :=
    cokernel.desc g (cokernel.π (coprod.desc β g)) (by simp)
  have hl : α ≫ l = 0 := by
    -- Proof comment: the added relation kills `α` after cancellation through the epimorphic
    -- cover `δ`.
    apply (cancel_epi δ).1
    rw [Category.assoc, hcomm, Category.assoc]
    simp [l, Category.assoc]
  let cofork : CokernelCofork α := CokernelCofork.ofπ l hl
  have hcofork : IsColimit cofork := by
    refine CokernelCofork.IsColimit.ofπ' l hl ?_
    intro Z k hk
    refine ⟨cokernel.desc (coprod.desc β g) (cokernel.π g ≫ k) ?_, by
      simp [l, Category.assoc]⟩
    -- Proof comment: the universal morphism out of the appended presentation is determined on the
    -- two coproduct summands.
    apply coprod.hom_ext
    · rw [Category.assoc, hcomm, Category.assoc, cokernel.π_desc, hk]
    · simp [Category.assoc]
  -- Proof comment: compare the explicit cokernel above with the canonical chosen cokernel of `α`.
  exact (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel α) hcofork).symm

/-- Helper for Lemma 18.30.11: a finite-index presentation over arbitrary finite index types can
be reindexed into the `Fin n` form used by the predicate `P`. -/
private lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    {X : Mod}
    {A K : Type*} [Fintype A] [Fintype K]
    (U : A → C) (V : K → C)
    (f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (e : X ≅ cokernel f)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B) :
    P (J := J) (𝒪 := 𝒪) (B := B) X := by
  let _ : HasColimitsOfShape (Discrete A) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) A
  let _ : HasColimitsOfShape (Discrete K) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) K
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card A))) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) (Fin (Fintype.card A))
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card K))) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) (Fin (Fintype.card K))
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eK : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let sourceIso :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ≅
        (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) :=
    Limits.Sigma.reindex eK (fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j))
  let targetIso :
      (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) ≅
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    Limits.Sigma.reindex eA (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
  let f' :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) :=
    sourceIso.hom ≫ f ≫ targetIso.inv
  let ecoker : cokernel f ≅ cokernel f' :=
    cokernel.mapIso f f' sourceIso.symm targetIso.symm (by simp [f'])
  -- Proof comment: reindex both finite coproducts to `Fin` and transport the resulting cokernel
  -- presentation across the conjugation isomorphism.
  refine
    ⟨Fintype.card A, Fintype.card K,
      fun i ↦ U (eA i), fun j ↦ V (eK j), f', e ≪≫ ecoker, ?_, ?_⟩
  · intro i
    exact hU (eA i)
  · intro j
    exact hV (eK j)

/-- Helper for Lemma 18.30.11: the cokernel of a map from a finite basis coproduct into a module
with a finite basis presentation again has a finite basis presentation. -/
private lemma basisToPresentedCokernel_hasFiniteBasisConstructibleModuleCokernelPresentation
    {n₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (α :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⟶
        cokernel g) :
    P (J := J) (𝒪 := 𝒪) (B := B) (cokernel α) := by
  obtain ⟨r, W, _, hW, _, left, lift, _, _, hcomm⟩ :=
    SheafOfModules.RingedSite.existsFiniteBasisLiftCoverOfEpi
      (J := J) (𝒪 := 𝒪) (B := B) U₁ hU₁ α (cokernel.π g)
  let leftIndex : Type u := Σ i : Fin n₁, Fin (r i)
  let leftFamily : leftIndex → C := fun a ↦ W a.1 a.2
  let flatIndex : Type u := Σ t : WalkingPair, WalkingPair.casesOn t leftIndex (Fin m₂)
  let flatFamily : flatIndex → C := fun a ↦
    WalkingPair.casesOn a.1 leftFamily V₂ a.2
  let binarySourceIso :
      ((∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a)) ⨿
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun t : WalkingPair ↦
          WalkingPair.casesOn t
            (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
            (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) := by
    -- Proof comment: rewrite the binary coproduct as the coproduct of the walking-pair diagram.
    simpa using
      (Sigma.isoColimit
        (pair
          (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)))).symm
  let flattenIso :
      (∐ fun t : WalkingPair ↦
        WalkingPair.casesOn t
          (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) := by
    -- Proof comment: flatten the two-stage coproduct into one coproduct over the sigma index.
    simpa [leftIndex, leftFamily, flatIndex, flatFamily] using
      (sigmaSigmaIso
        (fun t : WalkingPair ↦ WalkingPair.casesOn t leftIndex (Fin m₂))
        (fun t ↦ WalkingPair.casesOn t
          (fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))))
  let sourceIso :
      ((∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a)) ⨿
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) :=
    binarySourceIso ≪≫ flattenIso
  let f :
      (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)) :=
    sourceIso.inv ≫ coprod.desc lift g
  let ecoker :
      cokernel (coprod.desc lift g) ≅ cokernel f :=
    cokernel.mapIso (coprod.desc lift g) f sourceIso (Iso.refl _) (by simp [f])
  let e :
      cokernel α ≅ cokernel f :=
    (cokernelIso_of_appendedFiniteLift
      (J := J) (𝒪 := 𝒪) g α left lift hcomm.symm).symm ≪≫ ecoker
  have hFlat : ∀ a : flatIndex, flatFamily a ∈ B := by
    intro a
    cases a with
    | mk t x =>
        cases t with
        | left =>
            exact hW x.1 x.2
        | right =>
            exact hV₂ x
  -- Proof comment: the flattened finite source map gives the required finite basis cokernel
  -- presentation of `cokernel α`.
  exact hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    (J := J) (𝒪 := 𝒪) (B := B)
    U₂ flatFamily f e hU₂ hFlat

/-- Helper for Lemma 18.30.11: cokernels of morphisms between explicit finite cokernel
presentations again admit finite basis cokernel presentations. -/
private lemma presentedCokernel_hasFiniteBasisConstructibleModuleCokernelPresentation
    {n₁ m₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B) (hV₁ : ∀ j, V₁ j ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f ⟶ cokernel g) :
    P (J := J) (𝒪 := 𝒪) (B := B) (cokernel φ) := by
  let α := cokernel.π f ≫ φ
  have hα :
      P (J := J) (𝒪 := 𝒪) (B := B) (cokernel α) :=
    basisToPresentedCokernel_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) U₁ U₂ V₂ hU₁ hU₂ hV₂ g α
  let e : cokernel α ≅ cokernel φ :=
    CategoryTheory.ShortComplex.cokernelIso_of_cokernelProjectionComp
      (J := J) (𝒪 := 𝒪) (B := B) f φ
  -- Proof comment: the source relation contributes only through the canonical cokernel comparison
  -- isomorphism from the presentation-level map `α`.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) e hα

/-- Helper for Lemma 18.30.11: cokernels of morphisms between finitely presented basis-cokernel
modules again admit finite basis cokernel presentations. -/
private lemma cokernel_of_morphism_hasFiniteBasisConstructibleModuleCokernelPresentation
    {X Y : Mod} (u : X ⟶ Y)
    (hX : P (J := J) (𝒪 := 𝒪) (B := B) X)
    (hY : P (J := J) (𝒪 := 𝒪) (B := B) Y) :
    P (J := J) (𝒪 := 𝒪) (B := B) (cokernel u) := by
  rcases hX with ⟨n₁, m₁, U₁, V₁, f₁, e₁, hU₁, hV₁⟩
  rcases hY with ⟨n₂, m₂, U₂, V₂, f₂, e₂, hU₂, hV₂⟩
  let u' : cokernel f₁ ⟶ cokernel f₂ := e₁.inv ≫ u ≫ e₂.hom
  have hu' :
      P (J := J) (𝒪 := 𝒪) (B := B) (cokernel u') :=
    presentedCokernel_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) U₁ V₁ U₂ V₂ hU₁ hV₁ hU₂ hV₂ f₁ f₂ u'
  let eCokernel : cokernel u' ≅ cokernel u :=
    cokernel.mapIso u' u e₁.symm e₂.symm (by
      -- Proof comment: `u'` is just `u` conjugated by the chosen presentation isomorphisms.
      simp [u', Category.assoc])
  -- Proof comment: once the normalized cokernel is handled by Lemma `18.30.8`, transport back to
  -- the original morphism `u`.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eCokernel hu'

/-- Helper for Lemma 18.30.11: kernels of morphisms between finitely presented basis-cokernel
modules reduce to the corresponding kernel problem for explicit presentation cokernels. -/
private lemma kernel_of_morphism_hasFiniteBasisConstructibleModuleCokernelPresentation
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f))
    {X Y : Mod} (u : X ⟶ Y)
    (hX : P (J := J) (𝒪 := 𝒪) (B := B) X)
    (hY : P (J := J) (𝒪 := 𝒪) (B := B) Y) :
    P (J := J) (𝒪 := 𝒪) (B := B) (kernel u) := by
  rcases hX with ⟨n₁, m₁, U₁, V₁, f₁, e₁, hU₁, hV₁⟩
  rcases hY with ⟨n₂, m₂, U₂, V₂, f₂, e₂, hU₂, hV₂⟩
  let u' : cokernel f₁ ⟶ cokernel f₂ := e₁.inv ≫ u ≫ e₂.hom
  have hu' :
      P (J := J) (𝒪 := 𝒪) (B := B) (kernel u') :=
    presentedKernel_hasFiniteBasisConstructibleModuleCokernelPresentation
      (J := J) (𝒪 := 𝒪) (B := B) hkernel
      U₁ V₁ U₂ V₂ hU₁ hV₁ hU₂ hV₂ f₁ f₂ u'
  let eKernel : kernel u' ≅ kernel u :=
    kernel.mapIso u' u e₁.symm e₂.symm (by
      -- Proof comment: `u'` is the presentation-level conjugate of `u`, so the kernel objects are
      -- canonically isomorphic.
      simp [u', Category.assoc])
  -- Proof comment: the unresolved kernel step is now isolated entirely in the explicit
  -- presentation-level helper above.
  exact
    CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) eKernel hu'

end Helpers

-- Proof sketch: apply the weak-Serre criterion to the object property of modules admitting a
-- finite basis cokernel presentation as in `18.30.7.2`. The basis assumptions are the setup from
-- Situation `18.30.5`, the displayed hypothesis gives the kernel step for maps between the
-- standard finite presentation objects, and the remaining closure properties are exactly the ones
-- established earlier in this subsection.
/-- Lemma 18.30.11: in Situation `18.30.5`, let `\mathcal A \subset \operatorname{Mod}(\mathcal
O)` be the full subcategory of modules isomorphic to a cokernel as in `18.30.7.2`. If the kernel
of every map
`\bigoplus_{j = 1, \ldots, m} j_{V_j!}\mathcal O_{V_j} \to
\bigoplus_{i = 1, \ldots, n} j_{U_i!}\mathcal O_{U_i}`
with `U_i` and `V_j` in `B` again lies in `\mathcal A`, then `\mathcal A` is a weak Serre
subcategory of `\operatorname{Mod}(\mathcal O)`. -/
@[stacks 093H]
theorem ringedSite_finiteBasisConstructibleModuleCokernelPresentation_isWeakSerreSubcategory_of_kernel_condition
    (hkernel :
      ∀ {n m : ℕ} (U : Fin n → C) (V : Fin m → C),
        (∀ i, U i ∈ B) →
        (∀ j, V j ∈ B) →
        (f :
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
            (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) →
          HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (kernel f)) :
    IsWeakSerreClass (HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B) := by
  -- Proof comment: use the closure-package criterion from Definition `12.10.1`. Zero objects,
  -- cokernels, and extensions are already handled by earlier Chapter 18 lemmas; the only new
  -- structural ingredient is kernel closure.
  letI : P.ContainsZero := by
    refine ⟨(0 : Mod), isZero_zero _, ?_⟩
    simpa using
      hasFiniteBasisConstructibleModuleCokernelPresentation_zero
        (J := J) (𝒪 := 𝒪) (B := B)
  letI : P.IsClosedUnderKernels where
    kernels_le := by
      intro Z hZ
      rcases hZ with ⟨f, k, hk, hXY⟩
      have hKernel :
          P (J := J) (𝒪 := 𝒪) (B := B) (kernel f) :=
        kernel_of_morphism_hasFiniteBasisConstructibleModuleCokernelPresentation
          (J := J) (𝒪 := 𝒪) (B := B) hkernel f hXY.1 hXY.2
      let eKernel : kernel f ≅ k.pt :=
        IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk
      -- Proof comment: convert the normalized kernel object back to the chosen fork point.
      exact
        CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
          (J := J) (𝒪 := 𝒪) (B := B) eKernel hKernel
  letI : P.IsClosedUnderCokernels where
    cokernels_le := by
      intro Z hZ
      rcases hZ with ⟨f, k, hk, hXY⟩
      have hCokernel :
          P (J := J) (𝒪 := 𝒪) (B := B) (cokernel f) :=
        cokernel_of_morphism_hasFiniteBasisConstructibleModuleCokernelPresentation
          (J := J) (𝒪 := 𝒪) (B := B) f hXY.1 hXY.2
      let eCokernel : cokernel f ≅ k.pt :=
        IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk
      -- Proof comment: the chosen cokernel cocone point differs from the canonical one only by a
      -- unique isomorphism.
      exact
        CategoryTheory.ShortComplex.hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
          (J := J) (𝒪 := 𝒪) (B := B) eCokernel hCokernel
  letI : P.IsClosedUnderExtensions where
    prop_X₂_of_shortExact {S} hS h₁ h₃ := by
      -- Proof comment: Lemma `18.30.10` is exactly the extension-closure statement needed here.
      exact
        CategoryTheory.ShortComplex.ringedSite_hasFiniteBasisConstructibleModuleCokernelPresentation_X2_of_shortExact
          (J := J) (𝒪 := 𝒪) (B := B) (S := S) hS h₁ h₃
  exact isWeakSerreClass_of_closure P

end
