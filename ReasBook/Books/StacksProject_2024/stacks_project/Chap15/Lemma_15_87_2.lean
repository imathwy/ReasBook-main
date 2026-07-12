import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComposableArrows
open Opposite
open SequentialInverseSystem

noncomputable section

universe u

/-- Helper for Lemma 15.87.2: the ambient inverse-system category of abelian groups in universe
`u`. -/
private abbrev AbSeq := SequentialInverseSystem (AddCommGrpCat.{u})

/- Domain-style sampling for Lemma 15.87.2:
- primary domain: the Milnor `lim` / `lim¹` exact sequence for a short exact sequence of
  sequential inverse systems of abelian groups;
- sampled owner declarations:
  `SequentialInverseSystem.firstDerivedLimit`,
  `SequentialInverseSystem.inverseLimit_exact_and_mono_of_shortExact`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `ShortComplex.SnakeInput.δ`,
  `ShortComplex.SnakeInput.snake_lemma`;
- best owner abstraction on this theorem surface: the degree-zero term is the canonical inverse
  limit object `limit A`, while the degree-one obstruction is the chapter owner
  `A.firstDerivedLimit`; the connecting morphism should therefore be the snake-lemma boundary map
  on the canonical Milnor difference-map diagram whose kernel row is `S.map lim` and whose
  cokernel row is expressed by `firstDerivedLimit`;
- primitive data: only the short exact sequence `S : ShortComplex AbSeq`;
- derived API: the canonical map on `firstDerivedLimit`, the named connecting morphism
  `lim C ⟶ lim¹ A`, the five-term exact segment for `lim`, and the endpoint mono/epi
  consequences.

Source/core/bridge triage:
  `source-facing`: the exact five-term segment and six-term endpoint consequences for
  `lim` / `lim¹`;
  `core/canonical`: `limit`, `firstDerivedLimit`, `derivedLimitDifferenceMap`, and the snake-lemma
  owner `ShortComplex.SnakeInput`;
  `bridge/view`: the Milnor ambient-product diagram attached to `S`, whose top kernel row is
  `S.map lim` and whose bottom cokernel row is the induced short complex on `firstDerivedLimit`.
  -/

namespace SequentialInverseSystem

/-- Helper for Lemma 15.87.2: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence of abelian groups. -/
theorem shortExact_eval {S : ShortComplex AbSeq.{u}} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat.{u}).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ AddCommGrpCat.{u}).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    -- Evaluation preserves kernels, so left exactness descends to the stagewise row.
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  -- Epimorphy of the right map is checked componentwise.
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

private abbrev productMap {A B : AbSeq.{u}} (φ : A ⟶ B) :
    ∏ᶜ inverseSystemFamily A ⟶ ∏ᶜ inverseSystemFamily B :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) n ≫ φ.app (op n)

private theorem productMap_π {A B : AbSeq.{u}} (φ : A ⟶ B) (n : ℕ) :
    productMap φ ≫ Pi.π (inverseSystemFamily B) n =
      Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) := by
  rw [productMap, Pi.lift_π]

/-- Helper for Lemma 15.87.2: postcomposing a map into the Milnor product with `productMap`
normalizes directly to the stagewise component map. -/
private theorem productMap_π_assoc {A B : AbSeq.{u}} {T : AddCommGrpCat.{u}}
    (k : T ⟶ ∏ᶜ inverseSystemFamily A) (φ : A ⟶ B) (n : ℕ) :
    k ≫ productMap φ ≫ Pi.π (inverseSystemFamily B) n =
      k ≫ Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) := by
  simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t) (productMap_π φ n)

private theorem productMap_zero
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    productMap S.f ≫ productMap S.g = 0 := by
  -- Route correction: compare the composite after each product projection so the short-complex
  -- relation becomes the stagewise equality `(S.f.app (op n)) ≫ (S.g.app (op n)) = 0`.
  apply Pi.hom_ext
  intro n
  calc
    (productMap S.f ≫ productMap S.g) ≫ Pi.π (inverseSystemFamily S.X₃) n =
        productMap S.f ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) := by
          simp [Category.assoc, productMap_π]
    _ =
        Pi.π (inverseSystemFamily S.X₁) n ≫ S.f.app (op n) ≫ S.g.app (op n) := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ t ≫ S.g.app (op n))
            (productMap_π S.f n)
    _ = Pi.π (inverseSystemFamily S.X₁) n ≫ 0 := by
          have hzero_n := NatTrans.congr_app S.zero (op n)
          change S.f.app (op n) ≫ S.g.app (op n) = 0 at hzero_n
          rw [hzero_n]
    _ = 0 := by simp
    _ = 0 ≫ Pi.π (inverseSystemFamily S.X₃) n := by simp

private theorem productMap_comm {A B : AbSeq.{u}} (φ : A ⟶ B) :
    derivedLimitDifferenceMap A ≫ productMap φ =
      productMap φ ≫ derivedLimitDifferenceMap B := by
  -- Compare both Milnor endomorphisms after projection to a fixed stage.
  apply Pi.hom_ext
  intro n
  calc
    (derivedLimitDifferenceMap A ≫ productMap φ) ≫ Pi.π (inverseSystemFamily B) n =
        derivedLimitDifferenceMap A ≫
          (Pi.π (inverseSystemFamily A) n ≫ φ.app (op n)) := by
          rw [Category.assoc, productMap_π]
    _ =
        (derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n) ≫ φ.app (op n) := by
          simp [Category.assoc]
    _ =
        (Pi.π (inverseSystemFamily A) n -
            Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n)) ≫
          φ.app (op n) := by
          rw [derivedLimitDifferenceMap_comp_π]
    _ =
        Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) -
          (Pi.π (inverseSystemFamily A) (n + 1) ≫
            A.transitionMap (Nat.le_succ n) ≫ φ.app (op n)) := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
        Pi.π (inverseSystemFamily A) n ≫ φ.app (op n) -
          (Pi.π (inverseSystemFamily A) (n + 1) ≫
            φ.app (op (n + 1)) ≫ B.transitionMap (Nat.le_succ n)) := by
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily A) (n + 1) ≫ t)
              (φ.naturality ((homOfLE (Nat.le_succ n)).op))
    _ =
        (Pi.π (inverseSystemFamily A) n ≫ φ.app (op n)) -
          ((Pi.π (inverseSystemFamily A) (n + 1) ≫ φ.app (op (n + 1))) ≫
            B.transitionMap (Nat.le_succ n)) := by
          simp [Category.assoc]
    _ =
        (productMap φ ≫ Pi.π (inverseSystemFamily B) n) -
          (productMap φ ≫ Pi.π (inverseSystemFamily B) (n + 1)) ≫
            B.transitionMap (Nat.le_succ n) := by
          rw [productMap_π, productMap_π]
    _ =
        productMap φ ≫
          (Pi.π (inverseSystemFamily B) n -
            Pi.π (inverseSystemFamily B) (n + 1) ≫ B.transitionMap (Nat.le_succ n)) := by
          simp [Preadditive.comp_sub, Category.assoc]
    _ =
        productMap φ ≫ derivedLimitDifferenceMap B ≫ Pi.π (inverseSystemFamily B) n := by
          rw [derivedLimitDifferenceMap_comp_π]
    _ =
        (productMap φ ≫ derivedLimitDifferenceMap B) ≫ Pi.π (inverseSystemFamily B) n := by
          simp [Category.assoc]

private abbrev productShortComplex
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    ShortComplex (AddCommGrpCat.{u}) :=
  ShortComplex.mk (productMap S.f) (productMap S.g) (productMap_zero S)

private abbrev limitToProduct (A : AbSeq.{u}) :
    limit A ⟶ ∏ᶜ inverseSystemFamily A :=
  Pi.lift fun n ↦ limit.π A (op n)

private theorem limitToProduct_π (A : AbSeq.{u}) (n : ℕ) :
    limitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      limit.π A (op n) := by
  rw [limitToProduct, Pi.lift_π]

/-- Helper for Lemma 15.87.2: postcomposing a map into the inverse limit with the canonical map to
the Milnor product identifies the resulting stage projection. -/
private theorem limitToProduct_π_assoc {A : AbSeq.{u}} {T : AddCommGrpCat.{u}}
    (k : T ⟶ limit A) (n : ℕ) :
    k ≫ limitToProduct A ≫ Pi.π (inverseSystemFamily A) n =
      k ≫ limit.π A (op n) := by
  simpa [Category.assoc] using congrArg (fun t ↦ k ≫ t) (limitToProduct_π A n)

/-- Helper for Lemma 15.87.2: precomposing the Milnor difference map with a morphism into the
product yields the expected projected difference formula. -/
private theorem differenceMap_π_preassoc {A : AbSeq.{u}} {T : AddCommGrpCat.{u}}
    (k : T ⟶ ∏ᶜ inverseSystemFamily A) (n : ℕ) :
    k ≫ derivedLimitDifferenceMap A ≫ Pi.π (inverseSystemFamily A) n =
      k ≫ Pi.π (inverseSystemFamily A) n -
        k ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
  simpa [Category.assoc, Preadditive.comp_sub] using
    congrArg (fun t ↦ k ≫ t) (derivedLimitDifferenceMap_comp_π A n)

private theorem limitToProduct_comp_difference (A : AbSeq.{u}) :
    limitToProduct A ≫ derivedLimitDifferenceMap A = 0 := by
  -- Compare the Milnor relation after each projection of the product.
  apply Pi.hom_ext
  intro n
  calc
    (limitToProduct A ≫ derivedLimitDifferenceMap A) ≫ Pi.π (inverseSystemFamily A) n =
        limitToProduct A ≫ Pi.π (inverseSystemFamily A) n -
          limitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
            A.transitionMap (Nat.le_succ n) := by
          simp [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
        limit.π A (op n) -
          limitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
            A.transitionMap (Nat.le_succ n) := by
          rw [limitToProduct_π]
    _ =
        limit.π A (op n) -
          limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
          have hπsucc :
              limitToProduct A ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫
                A.transitionMap (Nat.le_succ n) =
                  limit.π A (op (n + 1)) ≫ A.transitionMap (Nat.le_succ n) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ A.transitionMap (Nat.le_succ n))
                (limitToProduct_π A (n + 1))
          rw [hπsucc]
    _ = 0 := by
          rw [limit.w A ((homOfLE (Nat.le_succ n)).op)]
          simp
    _ = 0 ≫ Pi.π (inverseSystemFamily A) n := by simp

/-- Helper for Lemma 15.87.2: the map on inverse limits commutes with the first Milnor product
row. -/
private theorem limitToProductHom_comm_f
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    limitToProduct S.X₁ ≫ productMap S.f =
      lim.map S.f ≫ limitToProduct S.X₂ := by
  -- Compare both morphisms after projection to each stage of the product.
  apply Pi.hom_ext
  intro n
  calc
    (limitToProduct S.X₁ ≫ productMap S.f) ≫ Pi.π (inverseSystemFamily S.X₂) n =
        (limitToProduct S.X₁ ≫ Pi.π (inverseSystemFamily S.X₁) n) ≫ S.f.app (op n) := by
          simp [Category.assoc, productMap_π]
    _ = limit.π S.X₁ (op n) ≫ S.f.app (op n) := by
          rw [limitToProduct_π]
    _ = (lim.map S.f ≫ limitToProduct S.X₂) ≫ Pi.π (inverseSystemFamily S.X₂) n := by
          simpa [Category.assoc, limitToProduct_π] using
            (limMap_π (α := S.f) (j := op n)).symm

/-- Helper for Lemma 15.87.2: the map on inverse limits commutes with the second Milnor product
row. -/
private theorem limitToProductHom_comm_g
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    limitToProduct S.X₂ ≫ productMap S.g =
      lim.map S.g ≫ limitToProduct S.X₃ := by
  -- Compare both morphisms after projection to each stage of the product.
  apply Pi.hom_ext
  intro n
  calc
    (limitToProduct S.X₂ ≫ productMap S.g) ≫ Pi.π (inverseSystemFamily S.X₃) n =
        (limitToProduct S.X₂ ≫ Pi.π (inverseSystemFamily S.X₂) n) ≫ S.g.app (op n) := by
          simp [Category.assoc, productMap_π]
    _ = limit.π S.X₂ (op n) ≫ S.g.app (op n) := by
          rw [limitToProduct_π]
    _ = (lim.map S.g ≫ limitToProduct S.X₃) ≫ Pi.π (inverseSystemFamily S.X₃) n := by
          simpa [Category.assoc, limitToProduct_π] using
            (limMap_π (α := S.g) (j := op n)).symm

private abbrev limitToProductHom
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    S.map lim ⟶ productShortComplex S where
  τ₁ := limitToProduct S.X₁
  τ₂ := limitToProduct S.X₂
  τ₃ := limitToProduct S.X₃
  comm₁₂ := limitToProductHom_comm_f S
  comm₂₃ := limitToProductHom_comm_g S

private abbrev milnorDifferenceHom
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    productShortComplex S ⟶ productShortComplex S where
  τ₁ := derivedLimitDifferenceMap S.X₁
  τ₂ := derivedLimitDifferenceMap S.X₂
  τ₃ := derivedLimitDifferenceMap S.X₃
  comm₁₂ := productMap_comm S.f
  comm₂₃ := productMap_comm S.g

private theorem productToFirstDerivedLimit_comm_f
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    cokernel.π (derivedLimitDifferenceMap S.X₁) ≫ firstDerivedLimitMap S.f =
      productMap S.f ≫ cokernel.π (derivedLimitDifferenceMap S.X₂) := by
  -- This is the defining cokernel-desc compatibility for `cokernel.map`.
  simp [firstDerivedLimitMap]

private theorem productToFirstDerivedLimit_comm_g
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    cokernel.π (derivedLimitDifferenceMap S.X₂) ≫ firstDerivedLimitMap S.g =
      productMap S.g ≫ cokernel.π (derivedLimitDifferenceMap S.X₃) := by
  -- This is the defining cokernel-desc compatibility for `cokernel.map`.
  simp [firstDerivedLimitMap]

/-- Helper for Lemma 15.87.2: the induced short complex on `R^1 \!\varprojlim` has zero
composite. -/
private theorem firstDerivedLimitShortComplex_zero
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    firstDerivedLimitMap S.f ≫ firstDerivedLimitMap S.g = 0 := by
  -- Cancel the source cokernel projection and compute through the two defining maps.
  apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap S.X₁))).1
  calc
    cokernel.π (derivedLimitDifferenceMap S.X₁) ≫
        (firstDerivedLimitMap S.f ≫ firstDerivedLimitMap S.g) =
        (cokernel.π (derivedLimitDifferenceMap S.X₁) ≫ firstDerivedLimitMap S.f) ≫
          firstDerivedLimitMap S.g := by simp [Category.assoc]
    _ =
        (productMap S.f ≫ cokernel.π (derivedLimitDifferenceMap S.X₂)) ≫
          firstDerivedLimitMap S.g := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ t ≫ firstDerivedLimitMap S.g)
            (productToFirstDerivedLimit_comm_f S)
    _ =
        productMap S.f ≫
          (cokernel.π (derivedLimitDifferenceMap S.X₂) ≫ firstDerivedLimitMap S.g) := by
          simp [Category.assoc]
    _ =
        productMap S.f ≫
          (productMap S.g ≫ cokernel.π (derivedLimitDifferenceMap S.X₃)) := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ productMap S.f ≫ t)
            (productToFirstDerivedLimit_comm_g S)
    _ =
        (productMap S.f ≫ productMap S.g) ≫ cokernel.π (derivedLimitDifferenceMap S.X₃) := by
          simp [Category.assoc]
    _ = 0 := by
          simpa [Category.assoc] using congrArg
            (fun t ↦ t ≫ cokernel.π (derivedLimitDifferenceMap S.X₃))
            (productMap_zero S)
    _ = cokernel.π (derivedLimitDifferenceMap S.X₁) ≫ 0 := by simp

private abbrev firstDerivedLimitShortComplex
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    ShortComplex (AddCommGrpCat.{u}) :=
  ShortComplex.mk (firstDerivedLimitMap S.f) (firstDerivedLimitMap S.g)
    (firstDerivedLimitShortComplex_zero S)

private abbrev productToFirstDerivedLimitHom
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    productShortComplex S ⟶ firstDerivedLimitShortComplex S where
  τ₁ := cokernel.π (derivedLimitDifferenceMap S.X₁)
  τ₂ := cokernel.π (derivedLimitDifferenceMap S.X₂)
  τ₃ := cokernel.π (derivedLimitDifferenceMap S.X₃)
  comm₁₂ := productToFirstDerivedLimit_comm_f S
  comm₂₃ := productToFirstDerivedLimit_comm_g S

/-- Helper for Lemma 15.87.2: the product row is exact because products of abelian groups preserve
short exact sequences. -/
private noncomputable def productMap_f_is_kernel
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι (productMap S.f) (productMap_zero S)) := by
  -- Evaluate at each stage, use the stagewise kernel witness, and reassemble the lifts into the
  -- product object.
  let stageKernel :
      ∀ n : ℕ,
        IsLimit
          (KernelFork.ofι
            (S.f.app (op n))
            (by
              have hzero_n := NatTrans.congr_app S.zero (op n)
              change S.f.app (op n) ≫ S.g.app (op n) = 0 at hzero_n
              exact hzero_n)) :=
    fun n ↦ (SequentialInverseSystem.shortExact_eval (S := S) (n := n) hS).fIsKernel
  refine KernelFork.IsLimit.ofι (productMap S.f) (productMap_zero S)
    (fun {W} s hs ↦
      let stageLift : ∀ n : ℕ, W ⟶ S.X₁.obj (op n) :=
        fun n ↦
          let hsₙ : s ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) = 0 := by
            have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₃) n) hs
            simpa [Category.assoc, productMap_π] using hproj
          (stageKernel n).lift (KernelFork.ofι (s ≫ Pi.π (inverseSystemFamily S.X₂) n) hsₙ)
      Pi.lift stageLift)
    (fun {W} s hs ↦ by
      -- Compare the assembled lift coordinatewise and reduce to the stagewise kernel factorization.
      apply Pi.hom_ext
      intro n
      let stageLift : ∀ n : ℕ, W ⟶ S.X₁.obj (op n) :=
        fun n ↦
          let hsₙ : s ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) = 0 := by
            have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₃) n) hs
            simpa [Category.assoc, productMap_π] using hproj
          (stageKernel n).lift (KernelFork.ofι (s ≫ Pi.π (inverseSystemFamily S.X₂) n) hsₙ)
      have hsₙ : s ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) = 0 := by
        have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₃) n) hs
        simpa [Category.assoc, productMap_π] using hproj
      calc
        (Pi.lift stageLift ≫ productMap S.f) ≫ Pi.π (inverseSystemFamily S.X₂) n =
            Pi.lift stageLift ≫ Pi.π (inverseSystemFamily S.X₁) n ≫ S.f.app (op n) := by
              simp [Category.assoc, productMap_π]
        _ = stageLift n ≫ S.f.app (op n) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ S.f.app (op n)) (Pi.lift_π stageLift n)
        _ = s ≫ Pi.π (inverseSystemFamily S.X₂) n := by
              simpa [stageLift] using
                (stageKernel n).fac
                  (KernelFork.ofι (s ≫ Pi.π (inverseSystemFamily S.X₂) n) hsₙ)
                  WalkingParallelPair.zero)
    (fun {W} s hs m hm ↦ by
      apply Pi.hom_ext
      intro n
      let hsₙ : s ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) = 0 := by
        have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₃) n) hs
        simpa [Category.assoc, productMap_π] using hproj
      let stageLift : ∀ n : ℕ, W ⟶ S.X₁.obj (op n) :=
        fun n ↦
          let hsₙ : s ≫ Pi.π (inverseSystemFamily S.X₂) n ≫ S.g.app (op n) = 0 := by
            have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₃) n) hs
            simpa [Category.assoc, productMap_π] using hproj
          (stageKernel n).lift (KernelFork.ofι (s ≫ Pi.π (inverseSystemFamily S.X₂) n) hsₙ)
      have hmₙ :
          m ≫ Pi.π (inverseSystemFamily S.X₁) n ≫ S.f.app (op n) =
            s ≫ Pi.π (inverseSystemFamily S.X₂) n := by
        have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily S.X₂) n) hm
        simpa [Category.assoc, productMap_π] using hproj
      apply Fork.IsLimit.hom_ext (stageKernel n)
      calc
        m ≫ Pi.π (inverseSystemFamily S.X₁) n ≫ S.f.app (op n) =
            s ≫ Pi.π (inverseSystemFamily S.X₂) n := hmₙ
        _ = stageLift n ≫ S.f.app (op n) := by
              symm
              simpa [stageLift] using
                (stageKernel n).fac
                  (KernelFork.ofι (s ≫ Pi.π (inverseSystemFamily S.X₂) n) hsₙ)
                  WalkingParallelPair.zero
        _ = (Pi.lift stageLift ≫ Pi.π (inverseSystemFamily S.X₁) n) ≫ S.f.app (op n) := by
              simpa [Category.assoc] using
                congrArg (fun t ↦ t ≫ S.f.app (op n)) (Pi.lift_π stageLift n).symm)

/-- Helper for Lemma 15.87.2: the product map on the right term is epic because each component is
epic. -/
private theorem productMap_g_epi
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) (hS : S.ShortExact) :
    Epi (productMap S.g) := by
  -- Surjectivity is checked coordinatewise because products in `AddCommGrpCat` are concrete.
  classical
  refine ConcreteCategory.epi_of_surjective (productMap S.g) ?_
  intro y
  let stagePreimage : ∀ n : ℕ, S.X₂.obj (op n) :=
    fun n ↦
      Classical.choose <|
        (AddCommGrpCat.epi_iff_surjective (S.g.app (op n))).1
          (SequentialInverseSystem.shortExact_eval (S := S) (n := n) hS).epi_g
          ((Pi.π (inverseSystemFamily S.X₃) n) y)
  refine ⟨(Limits.Concrete.productEquiv (inverseSystemFamily S.X₂)).symm stagePreimage, ?_⟩
  apply Limits.Concrete.Pi.map_ext (F := 𝟭 AddCommGrpCat.{u})
  intro n
  -- Each coordinate is the chosen preimage under the stagewise surjection `g_n`.
  calc
    (ConcreteCategory.hom (Pi.π (inverseSystemFamily S.X₃) n))
        ((ConcreteCategory.hom (productMap S.g))
          ((Limits.Concrete.productEquiv (inverseSystemFamily S.X₂)).symm stagePreimage)) =
      (ConcreteCategory.hom (S.g.app (op n)))
        ((ConcreteCategory.hom (Pi.π (inverseSystemFamily S.X₂) n))
          ((Limits.Concrete.productEquiv (inverseSystemFamily S.X₂)).symm stagePreimage)) := by
            simpa [Category.assoc] using
              ConcreteCategory.congr_hom
                (productMap_π S.g n)
                ((Limits.Concrete.productEquiv (inverseSystemFamily S.X₂)).symm stagePreimage)
    _ = (ConcreteCategory.hom (S.g.app (op n))) (stagePreimage n) := by
          rw [Limits.Concrete.productEquiv_symm_apply_π]
    _ = (ConcreteCategory.hom (Pi.π (inverseSystemFamily S.X₃) n)) y := by
          exact
            Classical.choose_spec <|
              (AddCommGrpCat.epi_iff_surjective (S.g.app (op n))).1
                (SequentialInverseSystem.shortExact_eval (S := S) (n := n) hS).epi_g
                ((Pi.π (inverseSystemFamily S.X₃) n) y)

/-- Helper for Lemma 15.87.2: the product row attached to a short exact sequence of towers is
itself short exact. -/
private theorem productShortComplex_shortExact
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) (hS : S.ShortExact) :
    (productShortComplex S).ShortExact := by
  -- Combine the kernel presentation of the first map with coordinatewise surjectivity of the
  -- second map.
  have hExactMono : (productShortComplex S).Exact ∧ Mono (productShortComplex S).f := by
    exact (productShortComplex S).exact_and_mono_f_iff_f_is_kernel.2
      ⟨productMap_f_is_kernel S hS⟩
  exact ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 (productMap_g_epi S hS)

/-- Helper for Lemma 15.87.2: the inverse-limit row lands in the kernel of the Milnor
difference-row morphism. -/
private theorem limitToProductHom_zero
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    limitToProductHom S ≫ milnorDifferenceHom S = 0 := by
  -- The three components are exactly the ordinary Milnor kernel relations.
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact limitToProduct_comp_difference S.X₁
  · exact limitToProduct_comp_difference S.X₂
  · exact limitToProduct_comp_difference S.X₃

/-- Helper for Lemma 15.87.2: the cokernel row is annihilated by the Milnor difference-row
morphism. -/
private theorem productToFirstDerivedLimitHom_zero
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    milnorDifferenceHom S ≫ productToFirstDerivedLimitHom S = 0 := by
  -- The three components are the defining cokernel relations.
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · simpa using cokernel.condition (derivedLimitDifferenceMap S.X₁)
  · simpa using cokernel.condition (derivedLimitDifferenceMap S.X₂)
  · simpa using cokernel.condition (derivedLimitDifferenceMap S.X₃)

/-- Helper for Lemma 15.87.2: the inverse limit of a sequential tower is the kernel of its Milnor
difference map. -/
private noncomputable def limitToProduct_is_kernel (A : AbSeq.{u}) :
    IsLimit (KernelFork.ofι (limitToProduct A) (limitToProduct_comp_difference A)) := by
  -- A morphism into the Milnor product lies in the kernel exactly when its coordinates satisfy
  -- the cone compatibility relation for the inverse system.
  refine KernelFork.IsLimit.ofι (limitToProduct A) (limitToProduct_comp_difference A)
    (fun {W} s hs ↦
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) =
                0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [differenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      limit.lift A c)
    (fun {W} s hs ↦ by
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) =
                0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [differenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      -- The universal lift through the limit reproduces the original map after each product
      -- projection.
      apply Pi.hom_ext
      intro n
      calc
        (limit.lift A c ≫ limitToProduct A) ≫ Pi.π (inverseSystemFamily A) n =
            limit.lift A c ≫ limit.π A (op n) := by
              rw [Category.assoc, limitToProduct_π]
        _ = s ≫ Pi.π (inverseSystemFamily A) n := by
              simpa [c, stageHom] using limit.lift_π (F := A) (c := c) (j := op n))
    (fun {W} s hs m hm ↦ by
      let stageHom : ∀ n : ℕ, W ⟶ A.obj (op n) :=
        fun n ↦ s ≫ Pi.π (inverseSystemFamily A) n
      have hstageHom_naturality :
          ∀ n : ℕ,
            stageHom n = stageHom (n + 1) ≫ A.transitionMap (Nat.le_succ n) := by
        intro n
        have hproj :
            s ≫ Pi.π (inverseSystemFamily A) n -
              s ≫ Pi.π (inverseSystemFamily A) (n + 1) ≫ A.transitionMap (Nat.le_succ n) =
                0 := by
          have hproj' := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n) hs
          simpa [differenceMap_π_preassoc] using hproj'
        simpa [SequentialInverseSystem.transitionMap] using (sub_eq_zero.mp hproj)
      let c : Cone A := {
        pt := W
        π := NatTrans.ofOpSequence stageHom hstageHom_naturality
      }
      apply limit.hom_ext
      intro n
      have hproj := congrArg (fun t ↦ t ≫ Pi.π (inverseSystemFamily A) n.unop) hm
      simpa [c, stageHom, Category.assoc, limitToProduct_π] using hproj)

/-- Helper for Lemma 15.87.2: the inverse-limit row is the kernel row of the Milnor diagram in
`ShortComplex AbCat`. -/
private noncomputable def limitToProductHom_is_kernel
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    IsLimit (KernelFork.ofι (limitToProductHom S) (limitToProductHom_zero S)) := by
  -- Each component of the short-complex-valued kernel row is already the canonical Milnor kernel.
  let c : KernelFork (milnorDifferenceHom S) :=
    KernelFork.ofι (limitToProductHom S) (limitToProductHom_zero S)
  refine ShortComplex.isLimitOfIsLimitπ c ?_ ?_ ?_
  · exact (KernelFork.isLimitMapConeEquiv c ShortComplex.π₁).symm
      (limitToProduct_is_kernel S.X₁)
  · exact (KernelFork.isLimitMapConeEquiv c ShortComplex.π₂).symm
      (limitToProduct_is_kernel S.X₂)
  · exact (KernelFork.isLimitMapConeEquiv c ShortComplex.π₃).symm
      (limitToProduct_is_kernel S.X₃)

/-- Helper for Lemma 15.87.2: the `R^1 \!\varprojlim` row is the cokernel row of the Milnor
diagram in `ShortComplex AbCat`. -/
private noncomputable def productToFirstDerivedLimitHom_is_cokernel
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) :
    IsColimit (CokernelCofork.ofπ (productToFirstDerivedLimitHom S)
      (productToFirstDerivedLimitHom_zero S)) := by
  -- Each component of the bottom row is the defining cokernel presentation of `lim¹`.
  let c : CokernelCofork (milnorDifferenceHom S) :=
    CokernelCofork.ofπ (productToFirstDerivedLimitHom S) (productToFirstDerivedLimitHom_zero S)
  refine ShortComplex.isColimitOfIsColimitπ c ?_ ?_ ?_
  · exact (CokernelCofork.isColimitMapCoconeEquiv c ShortComplex.π₁).symm
      (cokernelIsCokernel (derivedLimitDifferenceMap S.X₁))
  · exact (CokernelCofork.isColimitMapCoconeEquiv c ShortComplex.π₂).symm
      (cokernelIsCokernel (derivedLimitDifferenceMap S.X₂))
  · exact (CokernelCofork.isColimitMapCoconeEquiv c ShortComplex.π₃).symm
      (cokernelIsCokernel (derivedLimitDifferenceMap S.X₃))

private noncomputable def limitSnakeInput
    (S : ShortComplex (SequentialInverseSystem (AddCommGrpCat.{u}))) (hS : S.ShortExact) :
    ShortComplex.SnakeInput (AddCommGrpCat.{u}) where
  L₀ := S.map lim
  L₁ := productShortComplex S
  L₂ := productShortComplex S
  L₃ := firstDerivedLimitShortComplex S
  v₀₁ := limitToProductHom S
  v₁₂ := milnorDifferenceHom S
  v₂₃ := productToFirstDerivedLimitHom S
  w₀₂ := limitToProductHom_zero S
  w₁₃ := productToFirstDerivedLimitHom_zero S
  h₀ := limitToProductHom_is_kernel S
  h₃ := productToFirstDerivedLimitHom_is_cokernel S
  L₁_exact := (productShortComplex_shortExact S hS).exact
  epi_L₁_g := (productShortComplex_shortExact S hS).epi_g
  L₂_exact := (productShortComplex_shortExact S hS).exact
  mono_L₂_f := (productShortComplex_shortExact S hS).mono_f

end SequentialInverseSystem

/-- The canonical connecting morphism
`lim C_i ⟶ lim¹ A_i` attached to a short exact sequence of sequential inverse systems of abelian
groups. -/
noncomputable abbrev sequentialAbelianGroupLimitδ
    (S : ShortComplex AbSeq.{u}) (hS : S.ShortExact) :
    limit S.X₃ ⟶ S.X₁.firstDerivedLimit :=
  (SequentialInverseSystem.limitSnakeInput S hS).δ

/-- Lemma 15.87.2: a short exact sequence of sequential inverse systems of abelian groups induces
an exact five-term segment
`lim A_i ⟶ lim B_i ⟶ lim C_i ⟶ lim¹ A_i ⟶ lim¹ B_i`,
where the connecting morphism is the canonical snake-lemma boundary map on the Milnor
difference-map diagram and the degree-one terms are expressed by the chapter owner
`SequentialInverseSystem.firstDerivedLimit`. -/
theorem sequentialAbelianGroupLimit_exact₅
    (S : ShortComplex AbSeq.{u}) (hS : S.ShortExact) :
    (mk₅
      (lim.map S.f)
      (lim.map S.g)
      (sequentialAbelianGroupLimitδ S hS)
      (SequentialInverseSystem.firstDerivedLimitMap S.f)
      (SequentialInverseSystem.firstDerivedLimitMap S.g)).Exact := by
  -- The target chain is exactly the snake sequence attached to the Milnor diagram.
  simpa [sequentialAbelianGroupLimitδ] using
    (SequentialInverseSystem.limitSnakeInput S hS).snake_lemma

/-- In the six-term exact sequence of Lemma 15.87.2, the first map
`lim A_i ⟶ lim B_i` is monic. -/
theorem sequentialAbelianGroupLimit_mono_map_f
    (S : ShortComplex AbSeq.{u}) (hS : S.ShortExact) :
    Mono (lim.map S.f) := by
  -- Left exactness of inverse limits identifies `lim.map S.f` with a kernel map.
  exact
    ((S.map lim).exact_and_mono_f_iff_f_is_kernel.2
      ⟨KernelFork.mapIsLimit _ hS.fIsKernel lim⟩).2

/-- In the six-term exact sequence of Lemma 15.87.2, the last displayed map
`lim¹ B_i ⟶ lim¹ C_i` is epic. -/
theorem sequentialAbelianGroupLimit_epi_map_g
    (S : ShortComplex AbSeq.{u}) (hS : S.ShortExact) :
    Epi (SequentialInverseSystem.firstDerivedLimitMap S.g) := by
  -- The right endpoint of the snake sequence is epic once the middle Milnor row is epic.
  letI : Epi ((SequentialInverseSystem.limitSnakeInput S hS).L₂.g) := by
    dsimp [SequentialInverseSystem.limitSnakeInput, SequentialInverseSystem.productShortComplex]
    exact SequentialInverseSystem.productMap_g_epi S hS
  simpa using (SequentialInverseSystem.limitSnakeInput S hS).epi_L₃_g
