import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2
import StacksProject_2024.Chap10.Lemma_10_131_9
import StacksProject_2024.Chap10.Lemma_10_131_11
import StacksProject_2024.Chap10.Lemma_10_148_3
import StacksProject_2024.Chap10.Lemma_10_138_9
import StacksProject_2024.Chap10.Lemma_10_149_1
import StacksProject_2024.Chap10.Lemma_10_149_4
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_149_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra TensorProduct
open Algebra.Extension
open TensorProduct.AlgebraTensorModule

universe u v w x y

namespace Algebra.Extension

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable (R) (P : Extension A B)

/- Domain-style sampling:
- primary domain: universal first-order thickenings, formal unramifiedness, and the
  Jacobi-Zariski/transitivity sequence for Kähler differentials over a tower `R → A → P.Ring → B`;
- sampled owner declarations:
  `Algebra.FormallyUnramified`,
  `Algebra.FormallyUnramified.iff_comp_injective`,
  `KaehlerDifferential.mapBaseChange`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`;
- best owner abstraction:
  part (1) is governed by the canonical owner predicate `FormallyUnramified A _`,
  while part (2) is governed by the owner map `KaehlerDifferential.mapBaseChange R A P.Ring`,
  further base changed along `P.Ring → B`;
- primitive data vs. derived API:
  the primitive data are the extension `P : Extension A B` and the universal first-order
  thickening hypothesis, while the tensor-reassociated comparison used below is only a thin
  auxiliary bridge/view of the owner `KaehlerDifferential.mapBaseChange`;
- source/core/bridge triage:
  `source-facing`: the formal-unramified consequence and the textbook isomorphism on the
    base-changed differential modules;
  `core/canonical`: `FormallyUnramified` and `KaehlerDifferential.mapBaseChange`;
  `bridge/view`: the tensor-order identification
    `B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`.

The previous local map definition rebuilt this bridge by hand with `rid`/`assoc`/`map`.
The canonical owner-level construction is the standard further base change of
`KaehlerDifferential.mapBaseChange` using `lTensor` and `cancelBaseChange`.
-/

/-- Lemma 10.149.5 (2), source-facing canonical map: after identifying the displayed textbook
comparison with the further base change of `KaehlerDifferential.mapBaseChange R A P.Ring` along
`P.Ring → B`, we obtain the canonical `B`-linear map
`B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`. -/
@[stacks 04EF]
noncomputable def universalFirstOrderThickening_kaehlerBaseChangeLinearMap
    : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  lTensor B B (KaehlerDifferential.mapBaseChange R A P.Ring) ∘ₗ
    (cancelBaseChange A P.Ring B B Ω[A⁄R]).symm.toLinearMap

variable {R} {P}


/-- Helper for Lemma 10.149.5: if an `A`-algebra equivalence of extension rings commutes with the
structure maps to `B`, then its inverse satisfies the symmetric commutative square as well. -/
lemma sourceAlgEquiv_symm_comp_eq
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    (IsScalarTower.toAlgHom A P.Ring B).comp e.symm.toAlgHom =
      IsScalarTower.toAlgHom A Q.Ring B := by
  ext x
  -- Evaluate the given commutative square at `e.symm x` and rewrite the composite.
  have hx := AlgHom.congr_fun he (e.symm x)
  simpa [AlgHom.comp_apply] using hx.symm

/-- Helper for Lemma 10.149.5: an `A`-algebra equivalence of extension rings also commutes with
the induced maps from any further base ring `R₀` along the tower `R₀ → A → P.Ring, Q.Ring`. -/
lemma sourceAlgEquiv_commutes_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (x : R₀) :
    e (algebraMap R₀ P.Ring x) = algebraMap R₀ Q.Ring x := by
  -- Proof comment: `e` is already an `A`-algebra equivalence, so we only need to rewrite the
  -- `R₀`-structure maps through `A`.
  rw [IsScalarTower.algebraMap_eq R₀ A P.Ring, IsScalarTower.algebraMap_eq R₀ A Q.Ring]
  exact e.commutes (algebraMap R₀ A x)

/-- Helper for Lemma 10.149.5: the inverse comparison equivalence satisfies the symmetric base-map
compatibility over any further base ring `R₀`. -/
lemma sourceAlgEquiv_symm_commutes_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (x : R₀) :
    e.symm (algebraMap R₀ Q.Ring x) = algebraMap R₀ P.Ring x := by
  -- Proof comment: this is the same `A`-algebra compatibility for the inverse equivalence.
  rw [IsScalarTower.algebraMap_eq R₀ A Q.Ring, IsScalarTower.algebraMap_eq R₀ A P.Ring]
  exact e.symm.commutes (algebraMap R₀ A x)

/-- Helper for Lemma 10.149.5: the `Q.Ring`-module of differentials is naturally a scalar tower
over any compatible map `P.Ring → Q.Ring`. -/
lemma sourceAlgEquiv_kaehler_isScalarTower
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] :
    IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] := by
  -- Proof comment: the `P.Ring`-action on `Ω[Q.Ring⁄R₀]` is exactly the one obtained by
  -- restricting scalars along `P.Ring → Q.Ring`.
  exact IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa

/-- Helper for Lemma 10.149.5: changing the tensor base from `P.Ring` to `Q.Ring` along a
compatible scalar tower `P.Ring → Q.Ring → B` is the canonical scalar-descent equivalence. -/
noncomputable def sourceAlgEquiv_tensorKaehler_desc
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] [IsScalarTower P.Ring Q.Ring B]
    (hPQ : Function.Surjective (algebraMap P.Ring Q.Ring)) :
    B ⊗[P.Ring] Ω[Q.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀] :=
  letI : IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_kaehler_isScalarTower (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
  letI : CompatibleSMul P.Ring Q.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    CompatibleSMul.of_algebraMap_surjective
      (R := P.Ring) (A := Q.Ring) (M := Q.Ring) (N := Ω[Q.Ring⁄R₀]) hPQ
  -- Proof comment: first reinsert the missing `Q.Ring` tensor factor via `cancelBaseChange`,
  -- then collapse `Q.Ring ⊗[P.Ring] Ω[Q.Ring⁄R₀]` back to `Ω[Q.Ring⁄R₀]` by the left-unit tensor
  -- equivalence.
  (cancelBaseChange P.Ring Q.Ring B B Ω[Q.Ring⁄R₀]).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl B B)
      (_root_.TensorProduct.lidOfCompatibleSMul P.Ring Q.Ring Ω[Q.Ring⁄R₀])

/-- Helper for Lemma 10.149.5: the scalar-descent equivalence sends a pure tensor `b ⊗ m` to the
same pure tensor after changing the tensor base to `Q.Ring`. -/
theorem sourceAlgEquiv_tensorKaehler_desc_tmul
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] [IsScalarTower P.Ring Q.Ring B]
    (hPQ : Function.Surjective (algebraMap P.Ring Q.Ring))
    (b : B) (m : Ω[Q.Ring⁄R₀]) :
    sourceAlgEquiv_tensorKaehler_desc (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q) hPQ
        (b ⊗ₜ[P.Ring] m) =
      b ⊗ₜ[Q.Ring] m := by
  let _ : IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_kaehler_isScalarTower (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
  let _ : CompatibleSMul P.Ring Q.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    CompatibleSMul.of_algebraMap_surjective
      (R := P.Ring) (A := Q.Ring) (M := Q.Ring) (N := Ω[Q.Ring⁄R₀]) hPQ
  -- Proof comment: both constituent equivalences have explicit pure-tensor formulas, so the
  -- composite reduces immediately to the same tensor over the smaller base ring.
  simp only [sourceAlgEquiv_tensorKaehler_desc, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, _root_.TensorProduct.lidOfCompatibleSMul_tmul, one_smul]

/-- Helper for Lemma 10.149.5: after installing the `P.Ring`-algebra structure on `Q.Ring`
coming from the comparison equivalence, the maps `R₀ → P.Ring → Q.Ring` form a scalar tower. -/
lemma sourceAlgEquiv_isScalarTower_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    IsScalarTower R₀ P.Ring Q.Ring := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  -- Proof comment: the comparison equivalence carries the `R₀`-structure map of `P.Ring` to that
  -- of `Q.Ring`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  simpa using (sourceAlgEquiv_commutes_base (A := A) (B := B) (R₀ := R₀) e x).symm

/-- Helper for Lemma 10.149.5: after installing the `P.Ring`-algebra structure on `Q.Ring`
coming from the comparison equivalence, the compatibility square with `B` gives the scalar tower
`P.Ring → Q.Ring → B`. -/
lemma sourceAlgEquiv_isScalarTower_target
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    IsScalarTower P.Ring Q.Ring B := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  -- Proof comment: the commuting square says exactly that the two maps `P.Ring → B` agree.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  simpa using (AlgHom.congr_fun he x).symm

/-- Helper for Lemma 10.149.5: the owner Kähler map induced by an `A`-algebra equivalence of
extension rings is bijective. -/
lemma sourceAlgEquiv_kaehler_map_bijective
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    let _ : IsScalarTower R₀ P.Ring Q.Ring :=
      sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
    Function.Bijective (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring) := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ P.Ring Q.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
  let _ : Algebra Q.Ring P.Ring := e.symm.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ Q.Ring P.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e.symm
  let _ : IsScalarTower P.Ring Q.Ring P.Ring := by
    -- Proof comment: with the source and target algebra structures coming from `e` and `e.symm`,
    -- the two-step action `P.Ring → Q.Ring → P.Ring` is literally the identity.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change x = e.symm (e x)
    simp
  let f : Ω[P.Ring⁄R₀] →ₗ[P.Ring] Ω[Q.Ring⁄R₀] :=
    KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring
  let g : Ω[Q.Ring⁄R₀] →ₗ[Q.Ring] Ω[P.Ring⁄R₀] :=
    KaehlerDifferential.map R₀ R₀ Q.Ring P.Ring
  have hleftMap : (g.restrictScalars P.Ring).comp f = LinearMap.id := by
    -- Proof comment: both endomorphisms of `Ω[P.Ring⁄R₀]` have the same composite with the
    -- universal derivation, so uniqueness of lifts from Kähler differentials identifies them.
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simpa [LinearMap.comp_apply, f, g, KaehlerDifferential.map_D] using
      congrArg (KaehlerDifferential.D R₀ P.Ring) (by
        change (algebraMap Q.Ring P.Ring) ((algebraMap P.Ring Q.Ring) x) = x
        change e.symm (e x) = x
        simp)
  have hleft : Function.LeftInverse (g.restrictScalars P.Ring) f := by
    intro x
    exact LinearMap.congr_fun hleftMap x
  -- Proof comment: surjectivity is the standard surjective-algebra-map statement because the
  -- installed `P.Ring → Q.Ring` algebra map is exactly the equivalence `e`.
  refine ⟨hleft.injective, ?_⟩
  simpa [f] using
    (KaehlerDifferential.map_surjective_of_surjective R₀ R₀ P.Ring Q.Ring
      (show Function.Surjective (algebraMap P.Ring Q.Ring) from e.surjective))

/-- Helper for Lemma 10.149.5: two `B`-linear maps out of the base-changed module
`B ⊗[A] Ω[A⁄R₀]` agree once they agree on the generators `1 ⊗ d a`. -/
lemma tensorBaseChange_currying_ext
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [Module R₀ M]
    [IsScalarTower A B M] [IsScalarTower R₀ A M]
    {f g : B ⊗[A] Ω[A⁄R₀] →ₗ[B] M}
    (h : ∀ a : A,
      f (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a) =
        g (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a)) :
    f = g := by
  let f₁ : Ω[A⁄R₀] →ₗ[A] M :=
    TensorProduct.AlgebraTensorModule.curry f 1
  let g₁ : Ω[A⁄R₀] →ₗ[A] M :=
    TensorProduct.AlgebraTensorModule.curry g 1
  have h₁ : f₁ = g₁ := by
    -- Proof comment: after currying, Kähler differentials are generated by the classes `d a`, so
    -- equality on those generators forces equality of the two `A`-linear maps.
    have hcomp :
        f₁.compDer (KaehlerDifferential.D R₀ A) =
          g₁.compDer (KaehlerDifferential.D R₀ A) := by
      ext a
      simpa [f₁, g₁, TensorProduct.AlgebraTensorModule.curry_apply] using h a
    exact Derivation.liftKaehlerDifferential_unique _ _ hcomp
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      -- Proof comment: both maps are linear, so they agree at `0`.
      simp
  | add z w hz hw =>
      -- Proof comment: additivity reduces the sum case to the induction hypotheses.
      simp [hz, hw]
  | tmul b η =>
      have hη : f ((1 : B) ⊗ₜ[A] η) = g ((1 : B) ⊗ₜ[A] η) := by
        simpa [f₁, g₁, TensorProduct.AlgebraTensorModule.curry_apply] using
          LinearMap.congr_fun h₁ η
      -- Proof comment: every pure tensor is a `B`-multiple of a generator `1 ⊗ η`, so the
      -- curried equality at `1` upgrades to equality on all pure tensors.
      calc
        f (b ⊗ₜ[A] η) = f (b • ((1 : B) ⊗ₜ[A] η)) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul]
        _ = b • f ((1 : B) ⊗ₜ[A] η) := by rw [LinearMap.map_smul]
        _ = b • g ((1 : B) ⊗ₜ[A] η) := by rw [hη]
        _ = g (b • ((1 : B) ⊗ₜ[A] η)) := by rw [LinearMap.map_smul]
        _ = g (b ⊗ₜ[A] η) := by
          rw [← TensorProduct.tmul_eq_smul_one_tmul (R := A) b η]

/-- Helper for Lemma 10.149.5: an `A`-algebra equivalence of extension rings over `B` induces the
corresponding `B`-linear equivalence on the base-changed `R`-relative Kähler modules, and this
equivalence intertwines the canonical maps from `Ω[A⁄R]`. -/
theorem universalFirstOrderThickening_kaehlerBaseChange_codomain_transport
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    ∃ E : B ⊗[P.Ring] Ω[P.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀],
      E.toLinearMap ∘ₗ universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P =
        universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ P.Ring Q.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
  let _ : IsScalarTower P.Ring Q.Ring B :=
    sourceAlgEquiv_isScalarTower_target (A := A) (B := B) e he
  let eΩ : Ω[P.Ring⁄R₀] ≃ₗ[P.Ring] Ω[Q.Ring⁄R₀] :=
    LinearEquiv.ofBijective
      (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring)
      (sourceAlgEquiv_kaehler_map_bijective (A := A) (B := B) (R₀ := R₀) e)
  let E₀ : B ⊗[P.Ring] Ω[P.Ring⁄R₀] ≃ₗ[B] B ⊗[P.Ring] Ω[Q.Ring⁄R₀] :=
    AlgebraTensorModule.congr (.refl B B) eΩ
  let E₁ : B ⊗[P.Ring] Ω[Q.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_tensorKaehler_desc (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
      (by simpa using e.surjective)
  refine ⟨E₀.trans E₁, ?_⟩
  -- Route correction: after packaging the owner equivalence on Kähler differentials, the
  -- conjugation check reduces to the universal generators `1 ⊗ d a`.
  apply tensorBaseChange_currying_ext (A := A) (B := B) (R₀ := R₀)
  intro a
  have hmap :
      eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) =
        KaehlerDifferential.D R₀ Q.Ring
          ((algebraMap P.Ring Q.Ring) (algebraMap A P.Ring a)) := by
    -- The owner equivalence is defined by the Kähler map induced from `e`.
    change (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring)
        (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) = _
    simpa using (KaehlerDifferential.map_D R₀ R₀ P.Ring Q.Ring (algebraMap A P.Ring a))
  calc
    (E₀.trans E₁)
        (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P
          (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a))
        = E₁ (E₀ (1 ⊗ₜ[P.Ring]
            KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a))) := by
              simp [E₀, E₁, universalFirstOrderThickening_kaehlerBaseChangeLinearMap]
    _ = E₁ (1 ⊗ₜ[P.Ring]
          eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a))) := by
            simp [E₀, AlgebraTensorModule.congr_tmul]
    _ = 1 ⊗ₜ[Q.Ring]
          eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) := by
            simp [E₁, sourceAlgEquiv_tensorKaehler_desc_tmul]
    _ = 1 ⊗ₜ[Q.Ring]
          KaehlerDifferential.D R₀ Q.Ring
            ((algebraMap P.Ring Q.Ring) (algebraMap A P.Ring a)) := by
              rw [hmap]
    _ = 1 ⊗ₜ[Q.Ring]
          KaehlerDifferential.D R₀ Q.Ring (algebraMap A Q.Ring a) := by
            congr 2
            exact sourceAlgEquiv_commutes_base (A := A) (B := B) (R₀ := A) e a
    _ = universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q
          (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a) := by
            simp [universalFirstOrderThickening_kaehlerBaseChangeLinearMap]

/-- Helper for Chap10 Lemma 10 149 5: if the image of a family spans after a linear map, then
the original family spans modulo the kernel. -/
lemma span_sup_ker_eq_top_of_span_image_eq_top
    {R₀ : Type*} {M N : Type*} [Semiring R₀]
    [AddCommGroup M] [Module R₀ M] [AddCommGroup N] [Module R₀ N]
    (φ : M →ₗ[R₀] N) (s : Set M)
    (hspan : Submodule.span R₀ (φ '' s) = ⊤) :
    Submodule.span R₀ s ⊔ LinearMap.ker φ = ⊤ := by
  -- Proof comment: rewrite the spanning hypothesis as surjectivity of `φ` from the span of `s`.
  rw [← Submodule.map_span] at hspan
  apply top_unique
  intro m _
  have hm : φ m ∈ Submodule.map φ (Submodule.span R₀ s) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases hm with ⟨m', hm', hφm'⟩
  -- Proof comment: decompose `m` as a span element plus a kernel element.
  refine Submodule.mem_sup.mpr ⟨m', hm', m - m', ?_, by abel⟩
  rw [LinearMap.mem_ker, map_sub, hφm', sub_self]

/-- Helper for Chap10 Lemma 10 149 5: the nilpotent Nakayama span form gives surjectivity of a
linear map once its range spans modulo the nilpotent ideal action. -/
lemma surjective_of_range_sup_ideal_smul_top_eq_top_of_isNilpotent
    {R₀ : Type*} {M N : Type*} [CommRing R₀]
    [AddCommGroup M] [Module R₀ M] [AddCommGroup N] [Module R₀ N]
    (I : Ideal R₀) (g : N →ₗ[R₀] M)
    (hsup : LinearMap.range g ⊔ I • (⊤ : Submodule R₀ M) = ⊤)
    (hI : IsNilpotent I) :
    Function.Surjective g := by
  -- Proof comment: apply the imported nilpotent Nakayama lemma to the range submodule.
  have hrange :
      LinearMap.range g = ⊤ :=
    eq_top_of_sup_eq_top_of_isNilpotent I (LinearMap.range g) (⊤ : Submodule R₀ M) hsup hI
  exact LinearMap.range_eq_top.mp hrange

/-- Helper for Chap10 Lemma 10 149 5: a family that spans after quotienting by `I • ⊤`
spans the original module modulo `I • ⊤`. -/
lemma span_sup_ideal_smul_top_eq_top_of_quotient_span_top
    {R₀ : Type*} {M : Type*} {ι : Type*} [CommRing R₀]
    [AddCommGroup M] [Module R₀ M]
    (I : Ideal R₀) (v : ι → M)
    (hspan : Submodule.span R₀
      (Set.range (fun i => (Submodule.mkQ (I • (⊤ : Submodule R₀ M))) (v i))) = ⊤) :
    Submodule.span R₀ (Set.range v) ⊔ I • (⊤ : Submodule R₀ M) = ⊤ := by
  -- Proof comment: rewrite the quotient spanning hypothesis as the image of the original span under
  -- the quotient map.
  have himage :
      Submodule.span R₀ ((Submodule.mkQ (I • (⊤ : Submodule R₀ M))) '' Set.range v) = ⊤ := by
    rw [show (Submodule.mkQ (I • (⊤ : Submodule R₀ M))) '' Set.range v =
        Set.range (fun i => (Submodule.mkQ (I • (⊤ : Submodule R₀ M))) (v i)) by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨v i, ⟨i, rfl⟩, rfl⟩]
    exact hspan
  rw [← Submodule.map_span] at himage
  apply top_unique
  intro m _
  have hm :
      (Submodule.mkQ (I • (⊤ : Submodule R₀ M))) m ∈
        Submodule.map (Submodule.mkQ (I • (⊤ : Submodule R₀ M)))
          (Submodule.span R₀ (Set.range v)) := by
    rw [himage]
    exact Submodule.mem_top
  rcases hm with ⟨m', hm', hφm'⟩
  -- Proof comment: lift a quotient representative from the span, leaving the difference in
  -- `I • ⊤`.
  refine Submodule.mem_sup.mpr ⟨m', hm', m - m', ?_, by abel⟩
  have hq : (Submodule.mkQ (I • (⊤ : Submodule R₀ M))) (m - m') = 0 := by
    rw [map_sub, hφm'.symm, sub_self]
  exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R₀ M))).mp hq

/-- Helper for Chap10 Lemma 10 149 5: a spanning family over a quotient algebra also spans after
restricting scalars along a surjective algebra map. -/
lemma span_restrictScalars_eq_top_of_surjective
    {R₀ S M₀ ι : Type*} [CommSemiring R₀] [CommSemiring S]
    [AddCommMonoid M₀] [Module R₀ M₀] [Module S M₀]
    [Algebra R₀ S] [IsScalarTower R₀ S M₀]
    (hRS : Function.Surjective (algebraMap R₀ S)) (v : ι → M₀)
    (hspan : Submodule.span S (Set.range v) = ⊤) :
    Submodule.span R₀ (Set.range v) = ⊤ := by
  -- Proof comment: reduce membership in the larger scalar span to the restricted scalar span by
  -- lifting each scalar coefficient through the surjective algebra map.
  apply top_unique
  intro m _
  have hmS : m ∈ Submodule.span S (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  exact Submodule.span_induction
    (p := fun x _ => x ∈ Submodule.span R₀ (Set.range v))
    (fun x hx => Submodule.subset_span hx)
    (Submodule.zero_mem _)
    (fun _ _ _ _ hx hy => Submodule.add_mem _ hx hy)
    (fun a x _ hxspan => by
      obtain ⟨r, hr⟩ := hRS a
      have hax : a • x = r • x := by
        rw [← hr]
        exact IsScalarTower.algebraMap_smul S r x
      rw [hax]
      exact Submodule.smul_mem _ r hxspan)
    hmS

/-- Helper for Chap10 Lemma 10 149 5: a tensor product over a surjective intermediate algebra
may be descended from the source algebra tensor product. -/
noncomputable def tensorDescOfSurjective
    (R₀ S T N : Type*) [CommSemiring R₀] [CommSemiring S] [Semiring T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T] [IsScalarTower R₀ S T]
    [AddCommMonoid N] [Module R₀ N] [Module S N] [IsScalarTower R₀ S N]
    (hRS : Function.Surjective (algebraMap R₀ S)) :
    T ⊗[R₀] N ≃ₗ[T] T ⊗[S] N :=
  letI : CompatibleSMul R₀ S S N :=
    CompatibleSMul.of_algebraMap_surjective
      (R := R₀) (A := S) (M := S) (N := N) hRS
  letI : CompatibleSMul R₀ S T N :=
    CompatibleSMul.of_algebraMap_surjective
      (R := R₀) (A := S) (M := T) (N := N) hRS
  (cancelBaseChange R₀ S T T N).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl T T)
      (_root_.TensorProduct.lidOfCompatibleSMul R₀ S N)

/-- Helper for Chap10 Lemma 10 149 5: the tensor-descent equivalence preserves pure tensors. -/
theorem tensorDescOfSurjective_tmul
    (R₀ S T N : Type*) [CommSemiring R₀] [CommSemiring S] [Semiring T]
    [Algebra R₀ S] [Algebra R₀ T] [Algebra S T] [IsScalarTower R₀ S T]
    [AddCommMonoid N] [Module R₀ N] [Module S N] [IsScalarTower R₀ S N]
    (hRS : Function.Surjective (algebraMap R₀ S)) (t : T) (n : N) :
    tensorDescOfSurjective R₀ S T N hRS (t ⊗ₜ[R₀] n) = t ⊗ₜ[S] n := by
  letI : CompatibleSMul R₀ S S N :=
    CompatibleSMul.of_algebraMap_surjective
      (R := R₀) (A := S) (M := S) (N := N) hRS
  letI : CompatibleSMul R₀ S T N :=
    CompatibleSMul.of_algebraMap_surjective
      (R := R₀) (A := S) (M := T) (N := N) hRS
  -- Proof comment: unfold the descent equivalence and use the two pure-tensor formulas in order.
  simp only [tensorDescOfSurjective, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, _root_.TensorProduct.lidOfCompatibleSMul_tmul, one_smul]

/-- Helper for Chap10 Lemma 10 149 5: if the image of a family under a linear equivalence spans,
then the original family spans. -/
lemma span_eq_top_of_linearEquiv_image_span_eq_top
    {R₀ M₀ N₀ ι : Type*} [Semiring R₀]
    [AddCommMonoid M₀] [Module R₀ M₀]
    [AddCommMonoid N₀] [Module R₀ N₀]
    (e : M₀ ≃ₗ[R₀] N₀) (v : ι → M₀)
    (hspan : Submodule.span R₀ (Set.range (fun i ↦ e (v i))) = ⊤) :
    Submodule.span R₀ (Set.range v) = ⊤ := by
  -- Proof comment: pull a spanning expression for `e m` back through the inverse equivalence.
  apply top_unique
  intro m _
  have hem : e m ∈ Submodule.span R₀ (Set.range (fun i ↦ e (v i))) := by
    rw [hspan]
    exact Submodule.mem_top
  let P : Submodule R₀ M₀ := Submodule.span R₀ (Set.range v)
  have hpre : e.symm (e m) ∈ P := by
    refine Submodule.span_induction
      (p := fun y _ ↦ e.symm y ∈ P) ?_ ?_ ?_ ?_ hem
    · rintro _ ⟨i, rfl⟩
      simpa [P] using Submodule.subset_span (Set.mem_range_self i)
    · simpa [P] using Submodule.zero_mem P
    · intro y z _ _ hy hz
      simpa using P.add_mem hy hz
    · intro a y _ hy
      simpa using P.smul_mem a hy
  simpa [P] using hpre

/-- Helper for Chap10 Lemma 10 149 5: a split section of the self-presentation cotangent complex
gives a spanning family after applying the cotangent-complex map. -/
theorem selfPresentation_section_quotient_cotangentComplex_section_span_top
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
    Submodule.span Q.Ring
      (Set.range (fun x : P0.CotangentSpace ↦ P0.cotangentComplex (l x))) = ⊤ := by
  intro P0 Q
  -- The split-section identity rewrites the displayed family to the identity family, whose range
  -- spans the whole cotangent space.
  have hpoint :
      (fun x : P0.CotangentSpace ↦ P0.cotangentComplex (l x)) =
        fun x : P0.CotangentSpace ↦ x := by
    funext x
    simpa [P0, LinearMap.comp_apply] using LinearMap.congr_fun hl x
  rw [hpoint]
  simpa [P0, Q] using
    selfPresentation_section_quotient_cotangentSpace_identity_span_top
      (A := A) (B := B) l

/-- Helper for Chap10 Lemma 10 149 5: applying the infinitesimal comparison to a section
cotangent-complex generator gives the corresponding differential tensor. -/
theorem selfPresentation_toInfinitesimal_cotangentComplex_sectionGenerator
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let sectionGenerator : P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    Extension.CotangentSpace.map P0.toInfinitesimal (P0.cotangentComplex (l x)) =
      (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
        KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
  intro P0 sectionGenerator
  -- Proof comment: represent the cotangent class by a kernel element, map it to the
  -- infinitesimal quotient, and identify that quotient element with the chosen section generator.
  rw [Extension.CotangentSpace.map_cotangentComplex]
  obtain ⟨kx, hkx⟩ := Extension.Cotangent.mk_surjective (l x)
  rw [← hkx, Extension.Cotangent.map_mk, Extension.cotangentComplex_mk]
  have hgen : P0.toInfinitesimal.toRingHom (kx : P0.Ring) =
      P0.ker.cotangentToQuotientSquare (l x).val := by
    have hval : P0.ker.toCotangent kx = (l x).val := by
      simpa [Extension.Cotangent.val_mk] using congrArg Extension.Cotangent.val hkx
    rw [← hval]
    simp [Extension.toInfinitesimal, Extension.infinitesimal,
      Ideal.toCotangent_to_quotient_square]
    rfl
  simpa [sectionGenerator] using congrArg
    (fun z : P0.infinitesimal.Ring ↦
      (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
        KaehlerDifferential.D A P0.infinitesimal.Ring z) hgen

/-- Helper for Chap10 Lemma 10 149 5: the infinitesimal section-generator differentials span the
infinitesimal cotangent space. -/
theorem selfPresentation_infinitesimal_sectionGenerator_span_top
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    Submodule.span P0.infinitesimal.Ring
      (Set.range (fun x : P0.CotangentSpace ↦
        let sectionGenerator : P0.infinitesimal.Ring :=
          (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
            P0.ker.cotangentIdeal)).1
        (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
          KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator)) = ⊤ := by
  intro P0
  let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  let v : P0.CotangentSpace → P0.CotangentSpace := fun x ↦ P0.cotangentComplex (l x)
  have hQspan : Submodule.span Q.Ring (Set.range v) = ⊤ := by
    simpa [P0, Q, v] using
      selfPresentation_section_quotient_cotangentComplex_section_span_top
        (A := A) (B := B) l hl
  have hBspan : Submodule.span B (Set.range v) = ⊤ := by
    have hres : Submodule.restrictScalars Q.Ring (Submodule.span B (Set.range v)) = ⊤ := by
      rw [Submodule.restrictScalars_span Q.Ring B Q.algebraMap_surjective (Set.range v),
        hQspan]
    rwa [Submodule.restrictScalars_eq_top_iff Q.Ring B P0.CotangentSpace] at hres
  let F : P0.CotangentSpace ≃ₗ[B] P0.infinitesimal.CotangentSpace :=
    LinearEquiv.ofBijective (Extension.CotangentSpace.map P0.toInfinitesimal)
      (Extension.CotangentSpace.map_toInfinitesimal_bijective P0)
  have hFspanB :
      Submodule.span B (Set.range (fun x : P0.CotangentSpace ↦ F (v x))) = ⊤ := by
    apply span_eq_top_of_linearEquiv_image_span_eq_top F.symm
      (fun x : P0.CotangentSpace ↦ F (v x))
    simpa [F] using hBspan
  have hFspanS :
      Submodule.span P0.infinitesimal.Ring
        (Set.range (fun x : P0.CotangentSpace ↦ F (v x))) = ⊤ := by
    exact span_restrictScalars_eq_top_of_surjective
      P0.infinitesimal.algebraMap_surjective
      (fun x : P0.CotangentSpace ↦ F (v x)) hFspanB
  -- Proof comment: the pointwise generator computation rewrites the transported span to the
  -- displayed infinitesimal differential generators.
  have hpoint :
      (fun x : P0.CotangentSpace ↦ F (v x)) =
        fun x : P0.CotangentSpace ↦
          let sectionGenerator : P0.infinitesimal.Ring :=
            (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
              P0.ker.cotangentIdeal)).1
          (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
            KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
    funext x
    simpa [F, v] using
      selfPresentation_toInfinitesimal_cotangentComplex_sectionGenerator
        (A := A) (B := B) l x
  rwa [hpoint] at hFspanS

/-- Helper for Chap10 Lemma 10 149 5: the explicit quotient map from the infinitesimal
self-presentation quotient to `B` forms the expected scalar tower. -/
lemma selfPresentation_section_quotient_map_isScalarTower
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let _ : Algebra (P0.infinitesimal.Ring ⧸ Jbar) B :=
      (selfPresentation_section_quotient_map (R := A) (S := B) l).toRingHom.toAlgebra
    IsScalarTower P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar) B := by
  intro P0 Jbar
  letI : Algebra (P0.infinitesimal.Ring ⧸ Jbar) B :=
    (selfPresentation_section_quotient_map (R := A) (S := B) l).toRingHom.toAlgebra
  -- Proof comment: the quotient algebra structure is defined by lifting the original
  -- infinitesimal map to `B`, so the two routes from the infinitesimal ring agree pointwise.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change algebraMap (P0.infinitesimal.Ring ⧸ Jbar) B (Ideal.Quotient.mk Jbar x) =
    algebraMap P0.infinitesimal.Ring B x
  rfl

/-- Helper for Chap10 Lemma 10 149 5: quotienting the middle tensor module by the infinitesimal
kernel identifies it with the infinitesimal cotangent space. -/
noncomputable def selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring]
      Ω[P0.infinitesimal.Ring⁄A]
    (M ⧸ P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)) ≃ₗ[P0.infinitesimal.Ring]
      P0.infinitesimal.CotangentSpace :=
  let P0 : Extension A B := (Generators.self A B).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
  let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring]
    Ω[P0.infinitesimal.Ring⁄A]
  letI : Algebra (P0.infinitesimal.Ring ⧸ Jbar) B :=
    (selfPresentation_section_quotient_map (R := A) (S := B) l).toRingHom.toAlgebra
  letI : IsScalarTower P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar) B :=
    selfPresentation_section_quotient_map_isScalarTower (A := A) (B := B) l
  let hSQ : Function.Surjective
      (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)) :=
    selfPresentation_section_quotient_a_relative_surjective (A := A) (B := B) l
  let eIB : (P0.infinitesimal.Ring ⧸ P0.infinitesimal.ker) ≃ₐ[P0.infinitesimal.Ring] B :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId P0.infinitesimal.Ring B) P0.infinitesimal.algebraMap_surjective
  let e0 := (TensorProduct.quotTensorEquivQuotSMul M P0.infinitesimal.ker).symm
  let e1 := LinearEquiv.rTensor M eIB.toLinearEquiv
  let e2 := (tensorDescOfSurjective P0.infinitesimal.Ring
    (P0.infinitesimal.Ring ⧸ Jbar) B M hSQ).restrictScalars P0.infinitesimal.Ring
  let e3 := (cancelBaseChange P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)
    B B Ω[P0.infinitesimal.Ring⁄A]).restrictScalars P0.infinitesimal.Ring
  e0.trans (e1.trans (e2.trans e3))

/-- Helper for Chap10 Lemma 10 149 5: the quotient-reduction equivalence sends the section
differential class to the corresponding infinitesimal cotangent-space generator. -/
theorem selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace_mk_sectionDifferential
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring]
      Ω[P0.infinitesimal.Ring⁄A]
    let sectionDifferential : P0.CotangentSpace → M := fun x ↦
      let sectionGenerator : P0.infinitesimal.Ring :=
        (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
          P0.ker.cotangentIdeal)).1
      (1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
        KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator
    let sectionGenerator : P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace
        (A := A) (B := B) l
        ((Submodule.mkQ
          (P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)))
            (sectionDifferential x)) =
      (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
        KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
  intro P0 Jbar M sectionDifferential sectionGenerator
  -- Proof comment: the four components of the equivalence evaluate successively by the quotient
  -- tensor formula, the quotient-kernel equivalence, tensor descent, and `cancelBaseChange`.
  simp only [selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace,
    sectionDifferential, sectionGenerator, Submodule.mkQ_apply,
    LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.rTensor_tmul,
    AlgEquiv.toLinearEquiv_apply, map_one]
  rw [tensorDescOfSurjective_tmul]
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  rw [one_smul]

/-- Helper for Chap10 Lemma 10 149 5: the canonical section quotient has surjective
`A`-relative conormal map. -/
theorem selfPresentation_section_quotient_a_relative_conormal_surjective
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Surjective
        ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap) := by
  intro P0 Jbar
  -- Route correction: the arbitrary-`l` conormal statement is too strong. The intended argument
  -- uses `hl` to identify the section-generator differentials with the identity family on
  -- `P0.CotangentSpace`; the generic span/Nakayama mechanics above reduce the proof to one
  -- quotient-middle kernel comparison.
  let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  have hsectionSpan :
      Submodule.span Q.Ring
        (Set.range (fun x : P0.CotangentSpace ↦ P0.cotangentComplex (l x))) = ⊤ := by
    simpa [Q, P0] using
      selfPresentation_section_quotient_cotangentComplex_section_span_top
        (A := A) (B := B) l hl
  let M :=
    (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]
  let g :=
    (KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
        (P0.infinitesimal.Ring ⧸ Jbar)).comp
      (Ideal.Cotangent.equivOfEq Jbar
        (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
        (selfPresentation_section_quotient_a_relative_ker_eq
          (A := A) (B := B) l).symm).toLinearMap
  let sectionDifferential : P0.CotangentSpace → M := fun x ↦
    let sectionGenerator : P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    (1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
      KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator
  have hsectionRange :
      Submodule.span P0.infinitesimal.Ring (Set.range sectionDifferential) ≤
        LinearMap.range g := by
    -- Proof comment: every section generator has the explicit conormal preimage supplied by the
    -- quotient conormal formula in the theorem-local support file.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simpa [g, sectionDifferential] using
      selfPresentation_section_quotient_a_relative_generator_mem_range
        (A := A) (B := B) l x
  have hnilInf : IsNilpotent P0.infinitesimal.ker := by
    -- Proof comment: the infinitesimal kernel is the cotangent ideal, hence square-zero.
    refine ⟨2, ?_⟩
    simpa [P0, Extension.ker_infinitesimal] using Ideal.cotangentIdeal_square P0.ker
  have hquotientSectionSpan :
      Submodule.span P0.infinitesimal.Ring
        (Set.range (fun x : P0.CotangentSpace ↦
          (Submodule.mkQ
            (P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)))
              (sectionDifferential x))) = ⊤ := by
    let E :=
      selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace
        (A := A) (B := B) l
    have hspanImage :
        Submodule.span P0.infinitesimal.Ring
          (Set.range (fun x : P0.CotangentSpace ↦
            E ((Submodule.mkQ
              (P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)))
                (sectionDifferential x)))) = ⊤ := by
      -- Proof comment: reduce the quotient classes to the infinitesimal cotangent generators, whose
      -- span was transported from the split section of the original cotangent complex.
      have hpoint :
          (fun x : P0.CotangentSpace ↦
            E ((Submodule.mkQ
              (P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)))
                (sectionDifferential x))) =
            fun x : P0.CotangentSpace ↦
              let sectionGenerator : P0.infinitesimal.Ring :=
                (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
                  P0.ker.cotangentIdeal)).1
              (1 : B) ⊗ₜ[P0.infinitesimal.Ring]
                KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
        funext x
        simpa [E, M, sectionDifferential] using
          selfPresentation_section_quotient_reductionQuotientEquivInfinitesimalCotangentSpace_mk_sectionDifferential
            (A := A) (B := B) l x
      rw [hpoint]
      exact selfPresentation_infinitesimal_sectionGenerator_span_top
        (A := A) (B := B) l hl
    -- Proof comment: since `E` is a linear equivalence, spanning after applying `E` pulls back to
    -- spanning in the quotient module.
    exact span_eq_top_of_linearEquiv_image_span_eq_top E
      (fun x : P0.CotangentSpace ↦
        (Submodule.mkQ
          (P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M)))
            (sectionDifferential x))
      hspanImage
  have hspanSup :
      Submodule.span P0.infinitesimal.Ring (Set.range sectionDifferential) ⊔
        P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M) = ⊤ := by
    -- Proof comment: lift the quotient spanning statement back to a Nakayama span statement.
    exact span_sup_ideal_smul_top_eq_top_of_quotient_span_top
      P0.infinitesimal.ker sectionDifferential hquotientSectionSpan
  have hrangeSup :
      LinearMap.range g ⊔ P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M) = ⊤ := by
    -- Proof comment: the section differentials already lie in the conormal range, so enlarging the
    -- left summand preserves the top span.
    apply top_unique
    intro m _
    have hm : m ∈
        Submodule.span P0.infinitesimal.Ring (Set.range sectionDifferential) ⊔
          P0.infinitesimal.ker • (⊤ : Submodule P0.infinitesimal.Ring M) := by
      rw [hspanSup]
      exact Submodule.mem_top
    exact (sup_le_sup hsectionRange le_rfl) hm
  -- Proof comment: nilpotent Nakayama converts the span modulo the infinitesimal kernel into
  -- surjectivity of the conormal map.
  simpa [g, M] using
    surjective_of_range_sup_ideal_smul_top_eq_top_of_isNilpotent
      P0.infinitesimal.ker g hrangeSup hnilInf

/-- Helper for Chap10 Lemma 10 149 5: exactness with surjective left and right maps forces the
terminal module in the sequence to be a subsingleton. -/
lemma subsingleton_of_exact_of_surjective_of_left_surjective
    {R : Type u} {L : Type v} {M : Type w} {N : Type*}
    [Semiring R]
    [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (g : L →ₗ[R] M) (f : M →ₗ[R] N)
    (hexact : Function.Exact g f) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Subsingleton N := by
  -- Exactness identifies the kernel of the right map with the range of the left map.
  have hker : LinearMap.ker f = ⊤ := by
    rw [Function.Exact.linearMap_ker_eq hexact]
    exact LinearMap.range_eq_top.2 hg
  refine ⟨fun y z => ?_⟩
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨z', rfl⟩ := hf z
  -- Since the right map has full kernel, any two chosen preimages have the same image.
  have hdiff : y' - z' ∈ LinearMap.ker f := by
    rw [hker]
    exact Submodule.mem_top
  have hzero : f (y' - z') = 0 := hdiff
  have hsub : f y' - f z' = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- Helper for Chap10 Lemma 10 149 5: the canonical self-presentation section quotient is
formally unramified over the base. -/
theorem selfPresentation_section_quotient_formallyUnramified
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    FormallyUnramified A (selfPresentation_section_quotient (R := A) (S := B) l).Ring := by
  let P0 : Extension A B := (Generators.self A B).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
  let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  let g := (((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap).restrictScalars A)
  let f := (KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)).restrictScalars A
  -- The conormal exact sequence for the quotient is the `A`-relative sequence from Lemma 10.131.9.
  have hexact : Function.Exact g f := by
    simpa [g, f, P0, Jbar] using
      (selfPresentation_section_quotient_a_relative_exact (A := A) (B := B) l).1
  have hf : Function.Surjective f := by
    simpa [f, P0, Jbar] using
      (selfPresentation_section_quotient_a_relative_exact (A := A) (B := B) l).2
  have hg : Function.Surjective g := by
    -- The split section is the missing side condition for the conormal surjectivity argument.
    simpa [g, P0, Jbar] using
      selfPresentation_section_quotient_a_relative_conormal_surjective (A := A) (B := B) l hl
  -- With the conormal map surjective, exactness kills all `A`-relative differentials of `Q`.
  have hsub : Subsingleton Ω[(P0.infinitesimal.Ring ⧸ Jbar)⁄A] :=
    subsingleton_of_exact_of_surjective_of_left_surjective g f hexact hf hg
  rw [Algebra.formallyUnramified_iff]
  simpa [Q, P0, Jbar] using hsub

/-- Helper for Chap10 Lemma 10 149 5: bijectivity of the Kähler comparison transports across an
`A`-algebra equivalence of extension rings that commutes with the maps to `B`. -/
theorem universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective_of_sourceAlgEquiv
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{max v w} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B)
    (hQ :
      Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q)) :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P) := by
  obtain ⟨E, hE⟩ :=
    universalFirstOrderThickening_kaehlerBaseChange_codomain_transport
      (A := A) (B := B) (R₀ := R₀) e he
  -- Proof comment: conjugate the `P`-comparison by the codomain equivalence and use the known
  -- bijectivity of the `Q`-comparison.
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hQ.1
    calc
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q x =
          E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P x) := by
            exact (LinearMap.congr_fun hE x).symm
      _ = E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P y) := by
            rw [hxy]
      _ = universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q y := by
            exact LinearMap.congr_fun hE y
  · intro y
    obtain ⟨x, hx⟩ := hQ.2 (E y)
    refine ⟨x, E.injective ?_⟩
    calc
      E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P x) =
          universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q x := by
            exact LinearMap.congr_fun hE x
      _ = E y := hx

/-- Helper for Chap10 Lemma 10 149 5: bijectivity of the owner-level tensorized
`mapBaseChange` implies bijectivity of the source-facing comparison map. -/
theorem kaehlerBaseChangeLinearMap_bijective_of_ownerTensorMapBaseChange_bijective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (P : Extension.{x} A B)
    (hOwner :
      Function.Bijective
        ((lTensor B B (KaehlerDifferential.mapBaseChange R₀ A P.Ring)) :
          B ⊗[P.Ring] (P.Ring ⊗[A] Ω[A⁄R₀]) →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R₀])) :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P) := by
  -- Proof comment: the displayed source-facing map is the owner tensor map after the canonical
  -- source `cancelBaseChange` equivalence, so injectivity and surjectivity transfer across that
  -- equivalence.
  constructor
  · intro x y hxy
    apply (cancelBaseChange A P.Ring B B Ω[A⁄R₀]).symm.injective
    apply hOwner.1
    simpa [universalFirstOrderThickening_kaehlerBaseChangeLinearMap] using hxy
  · intro y
    obtain ⟨z, hz⟩ := hOwner.2 y
    refine ⟨(cancelBaseChange A P.Ring B B Ω[A⁄R₀]) z, ?_⟩
    simpa [universalFirstOrderThickening_kaehlerBaseChangeLinearMap] using hz

/-- Helper for Chap10 Lemma 10 149 5: if the relative Kähler differentials over `A` vanish,
then the transitivity base-change map from `A` is surjective. -/
lemma kaehlerDifferential_mapBaseChange_surjective_of_subsingleton_kaehler
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {C : Type x} [CommRing C] [Algebra A C] [Algebra R₀ C] [IsScalarTower R₀ A C]
    [Subsingleton Ω[C⁄A]] :
    Function.Surjective (KaehlerDifferential.mapBaseChange R₀ A C) := by
  -- Proof comment: exactness of the transitivity sequence identifies the range with the kernel
  -- of `Ω[C⁄R₀] → Ω[C⁄A]`, and that kernel is all of the source when `Ω[C⁄A]` is subsingleton.
  intro x
  exact (KaehlerDifferential.exact_mapBaseChange_map R₀ A C x).mp (Subsingleton.elim _ _)

/-- Helper for Chap10 Lemma 10 149 5: if `C` is formally unramified over `A`, then an
`R₀`-derivation of `C` is determined by its restriction to `A`. -/
lemma formallyUnramified_derivation_compAlgebraMap_injective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {C : Type x} [CommRing C] [Algebra A C] [Algebra R₀ C] [IsScalarTower R₀ A C]
    {M : Type*} [AddCommGroup M] [Module C M] [Module A M] [Module R₀ M]
    [IsScalarTower A C M] [IsScalarTower R₀ C M]
    [FormallyUnramified A C] :
    Function.Injective (Derivation.compAlgebraMapL R₀ A C M) := by
  intro d₁ d₂ hcomp
  apply Derivation.ext
  intro c
  let dDiffA : Derivation A C M :=
    Derivation.mk'
      { toFun := fun c ↦ d₁ c - d₂ c
        map_add' := by
          intro c₁ c₂
          simp [map_add, sub_add_sub_comm]
        map_smul' := by
          intro a c
          have hres : d₁ (algebraMap A C a) = d₂ (algebraMap A C a) := by
            exact Derivation.congr_fun hcomp a
          -- The difference is `A`-linear because the two derivations agree after restriction to
          -- `A`; the Leibniz terms coming from `d a` cancel.
          rw [Algebra.smul_def, d₁.leibniz, d₂.leibniz, hres]
          simp [sub_eq_add_neg, add_comm, add_assoc] }
      (by
        intro c₁ c₂
        -- The difference of two derivations is again a derivation with the same Leibniz rule.
        simp [Derivation.leibniz, sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
  have hzero : dDiffA c = 0 := by
    have hD : KaehlerDifferential.D A C c = 0 := Subsingleton.elim _ _
    calc
      dDiffA c = dDiffA.liftKaehlerDifferential (KaehlerDifferential.D A C c) := by
        rw [Derivation.liftKaehlerDifferential_comp_D]
      _ = 0 := by rw [hD, map_zero]
  exact sub_eq_zero.mp hzero

/-- Helper for Chap10 Lemma 10 149 5: the second projection identifies the square-zero kernel
ideal of `TrivSqZeroExt B M` with the coefficient module `M`. -/
lemma trivSqZeroExtKerIdeal_snd_bijective
    (B : Type w) [CommRing B]
    (M : Type y) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    Function.Bijective
      ((TrivSqZeroExt.sndHom B M).comp
        ((Submodule.subtype (TrivSqZeroExt.kerIdeal B M)).restrictScalars B)) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hx : (x : TrivSqZeroExt B M) =
        TrivSqZeroExt.inr (TrivSqZeroExt.snd (x : TrivSqZeroExt B M)) := by
      -- Membership in the kernel ideal says that the first component is zero, so the element is
      -- recovered from its second component.
      exact (TrivSqZeroExt.mem_kerIdeal_iff_inr B M (x : TrivSqZeroExt B M)).mp x.2
    have hy : (y : TrivSqZeroExt B M) =
        TrivSqZeroExt.inr (TrivSqZeroExt.snd (y : TrivSqZeroExt B M)) := by
      -- Apply the same normal form to the second kernel element before comparing projections.
      exact (TrivSqZeroExt.mem_kerIdeal_iff_inr B M (y : TrivSqZeroExt B M)).mp y.2
    have hsnd :
        TrivSqZeroExt.snd (x : TrivSqZeroExt B M) =
          TrivSqZeroExt.snd (y : TrivSqZeroExt B M) := by
      simpa using hxy
    calc
      (x : TrivSqZeroExt B M) =
          TrivSqZeroExt.inr (TrivSqZeroExt.snd (x : TrivSqZeroExt B M)) := hx
      _ = TrivSqZeroExt.inr (TrivSqZeroExt.snd (y : TrivSqZeroExt B M)) := by rw [hsnd]
      _ = (y : TrivSqZeroExt B M) := hy.symm
  · intro m
    refine ⟨⟨TrivSqZeroExt.inr m, ?_⟩, ?_⟩
    · -- The pure infinitesimal element belongs to the kernel ideal by the standard normal form.
      rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
      simp
    · -- The chosen preimage has second component exactly `m`.
      simp

/-- Helper for Chap10 Lemma 10 149 5: the square-zero kernel ideal of `TrivSqZeroExt B M` is
canonically `B`-linearly equivalent to `M`. -/
noncomputable def trivSqZeroExtKerIdealLinearEquiv
    (B : Type w) [CommRing B]
    (M : Type y) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] :
    TrivSqZeroExt.kerIdeal B M ≃ₗ[B] M :=
  LinearEquiv.ofBijective
    ((TrivSqZeroExt.sndHom B M).comp
      ((Submodule.subtype (TrivSqZeroExt.kerIdeal B M)).restrictScalars B))
    (trivSqZeroExtKerIdeal_snd_bijective B M)

/-- Helper for Chap10 Lemma 10 149 5: an `M`-valued derivation of `A` pushes forward to a
derivation with values in the square-zero kernel ideal of `TrivSqZeroExt B M`. -/
noncomputable def trivSqZeroExtKerIdealDerivation
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) :
    Derivation R₀ A (TrivSqZeroExt.kerIdeal B M) :=
  ((trivSqZeroExtKerIdealLinearEquiv B M).symm.restrictScalars A).compDer dA

/-- Helper for Chap10 Lemma 10 149 5: the square-zero algebra map obtained by twisting the
standard `A → B → TrivSqZeroExt B M` map by an `R₀`-derivation of `A`. -/
noncomputable def trivSqZeroExtTwistedAlgebraMap
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) :
    A →ₐ[R₀] TrivSqZeroExt B M :=
  liftOfDerivationToSquareZero (TrivSqZeroExt.kerIdeal B M)
    (TrivSqZeroExt.kerIdeal_sq B M)
    (trivSqZeroExtKerIdealDerivation (A := A) (B := B) R₀ M dA)

/-- Helper for Chap10 Lemma 10 149 5: the first component of the twisted square-zero map is the
original structure map `A → B`. -/
theorem trivSqZeroExtTwistedAlgebraMap_fst
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (a : A) :
    TrivSqZeroExt.fst (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a) =
      algebraMap A B a := by
  -- Proof comment: `liftOfDerivationToSquareZero` adds an infinitesimal kernel element to the
  -- standard algebra map, and kernel elements have zero first component.
  have hkerFst :
      TrivSqZeroExt.fst
        ((trivSqZeroExtKerIdealDerivation (A := A) (B := B) R₀ M dA a :
            TrivSqZeroExt.kerIdeal B M) : TrivSqZeroExt B M) = 0 := by
    exact (trivSqZeroExtKerIdealDerivation (A := A) (B := B) R₀ M dA a).2
  rw [trivSqZeroExtTwistedAlgebraMap, liftOfDerivationToSquareZero_apply,
    TrivSqZeroExt.fst_add, hkerFst]
  simp [TrivSqZeroExt.algebraMap_eq_inl']

/-- Helper for Chap10 Lemma 10 149 5: the second component of the twisted square-zero map is the
chosen derivation of `A`. -/
theorem trivSqZeroExtTwistedAlgebraMap_snd
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (a : A) :
    TrivSqZeroExt.snd (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a) = dA a := by
  -- Proof comment: the inverse kernel equivalence was chosen from the second projection, so the
  -- infinitesimal part of the square-zero lift recovers exactly `dA a`.
  have hkerSecond :
      TrivSqZeroExt.snd
        ((trivSqZeroExtKerIdealDerivation (A := A) (B := B) R₀ M dA a :
            TrivSqZeroExt.kerIdeal B M) : TrivSqZeroExt B M) = dA a := by
    change
      (trivSqZeroExtKerIdealLinearEquiv B M)
        (trivSqZeroExtKerIdealDerivation (A := A) (B := B) R₀ M dA a) = dA a
    simpa [trivSqZeroExtKerIdealDerivation] using
    (trivSqZeroExtKerIdealLinearEquiv B M).apply_symm_apply (dA a)
  rw [trivSqZeroExtTwistedAlgebraMap, liftOfDerivationToSquareZero_apply,
    TrivSqZeroExt.snd_add, hkerSecond]
  simp [TrivSqZeroExt.algebraMap_eq_inl']

/-- Helper for Chap10 Lemma 10 149 5: the first projection is an `A`-algebra map for the
twisted `A`-algebra structure on `TrivSqZeroExt B M`. -/
noncomputable def trivSqZeroExtTwistedFstAlgHom
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) :
    letI : Algebra A (TrivSqZeroExt B M) :=
      (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
    TrivSqZeroExt B M →ₐ[A] B :=
  letI : Algebra A (TrivSqZeroExt B M) :=
    (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
  { (TrivSqZeroExt.fstHom B B M).toRingHom with
    commutes' := trivSqZeroExtTwistedAlgebraMap_fst (A := A) (B := B) R₀ M dA }

/-- Helper for Chap10 Lemma 10 149 5: the twisted first projection from
`TrivSqZeroExt B M` to `B` is surjective. -/
lemma trivSqZeroExtTwistedFstAlgHom_surjective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) :
    letI : Algebra A (TrivSqZeroExt B M) :=
      (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
    Function.Surjective (trivSqZeroExtTwistedFstAlgHom (A := A) (B := B) R₀ M dA) := by
  letI : Algebra A (TrivSqZeroExt B M) :=
    (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
  -- Proof comment: every element of `B` is the first component of its canonical `inl` lift.
  intro b
  refine ⟨TrivSqZeroExt.inl b, ?_⟩
  rfl

/-- Helper for Chap10 Lemma 10 149 5: quotienting the twisted square-zero extension by its
kernel ideal recovers `B` as an `A`-algebra. -/
noncomputable def trivSqZeroExtTwistedQuotientKerAlgEquiv
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) :
    letI : Algebra A (TrivSqZeroExt B M) :=
      (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
    (TrivSqZeroExt B M ⧸ TrivSqZeroExt.kerIdeal B M) ≃ₐ[A] B :=
  letI : Algebra A (TrivSqZeroExt B M) :=
    (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
  Ideal.quotientKerAlgEquivOfSurjective
    (f := trivSqZeroExtTwistedFstAlgHom (A := A) (B := B) R₀ M dA)
    (trivSqZeroExtTwistedFstAlgHom_surjective (A := A) (B := B) R₀ M dA)

/-- Helper for Chap10 Lemma 10 149 5: the twisted quotient equivalence sends a quotient class
to the first component of its representative. -/
theorem trivSqZeroExtTwistedQuotientKerAlgEquiv_mk
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (z : TrivSqZeroExt B M) :
    letI : Algebra A (TrivSqZeroExt B M) :=
      (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
    trivSqZeroExtTwistedQuotientKerAlgEquiv (A := A) (B := B) R₀ M dA
        (Ideal.Quotient.mk _ z) =
      TrivSqZeroExt.fst z := by
  letI : Algebra A (TrivSqZeroExt B M) :=
    (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
  -- Proof comment: the quotient equivalence is the first isomorphism theorem for the twisted
  -- first projection, so its class formula is the standard quotient-kernel formula.
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := trivSqZeroExtTwistedFstAlgHom (A := A) (B := B) R₀ M dA)
    (trivSqZeroExtTwistedFstAlgHom_surjective (A := A) (B := B) R₀ M dA) z

/-- Helper for Chap10 Lemma 10 149 5: the inverse twisted quotient equivalence sends `b : B`
to the class of `TrivSqZeroExt.inl b`. -/
theorem trivSqZeroExtTwistedQuotientKerAlgEquiv_symm_apply
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (b : B) :
    letI : Algebra A (TrivSqZeroExt B M) :=
      (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
    (trivSqZeroExtTwistedQuotientKerAlgEquiv (A := A) (B := B) R₀ M dA).symm b =
      Ideal.Quotient.mk _ (TrivSqZeroExt.inl b) := by
  letI : Algebra A (TrivSqZeroExt B M) :=
    (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA).toAlgebra
  -- Proof comment: rewrite `b` as the image of its `inl` lift and apply the inverse formula for
  -- the quotient-kernel equivalence.
  have hb :
      (trivSqZeroExtTwistedFstAlgHom (A := A) (B := B) R₀ M dA) (TrivSqZeroExt.inl b) =
        b := rfl
  rw [← hb]
  exact Ideal.quotientKerAlgEquivOfSurjective_symm_apply
    (f := trivSqZeroExtTwistedFstAlgHom (A := A) (B := B) R₀ M dA)
    (trivSqZeroExtTwistedFstAlgHom_surjective (A := A) (B := B) R₀ M dA)
    (TrivSqZeroExt.inl b)

/-- Helper for Chap10 Lemma 10 149 5: subtracting the ordinary `inl` lift from the twisted
square-zero lift lands in the kernel ideal. -/
lemma trivSqZeroExtTwistedAlgebraMap_sub_inl_mem_kerIdeal
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (a : A) :
    trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a -
        TrivSqZeroExt.inl (algebraMap A B a) ∈
      TrivSqZeroExt.kerIdeal B M := by
  -- Proof comment: membership in the kernel ideal is exactly vanishing first component, and the
  -- twisted lift has the same first component as the ordinary structure map.
  rw [TrivSqZeroExt.kerIdeal, RingHom.mem_ker]
  change
    TrivSqZeroExt.fst
        (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a -
          TrivSqZeroExt.inl (algebraMap A B a)) = 0
  rw [TrivSqZeroExt.fst_sub,
    trivSqZeroExtTwistedAlgebraMap_fst (A := A) (B := B) R₀ M dA]
  simp

/-- Helper for Chap10 Lemma 10 149 5: the second component of the difference between the twisted
lift and the ordinary `inl` lift is the chosen derivation value. -/
lemma trivSqZeroExtTwistedAlgebraMap_sub_inl_snd
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (a : A) :
    TrivSqZeroExt.snd
        (trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a -
          TrivSqZeroExt.inl (algebraMap A B a)) = dA a := by
  -- Proof comment: the ordinary `inl` lift has zero infinitesimal component, so only the twisted
  -- derivation component remains.
  rw [TrivSqZeroExt.snd_sub,
    trivSqZeroExtTwistedAlgebraMap_snd (A := A) (B := B) R₀ M dA]
  simp

/-- Helper for Chap10 Lemma 10 149 5: under the kernel equivalence, the kernel element obtained
by subtracting the ordinary lift from the twisted lift maps to the chosen derivation value. -/
lemma trivSqZeroExtKerIdealLinearEquiv_eq_of_coe_eq_sub_twistedAlgebraMap
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    (M : Type*) [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    [Module A M] [Module R₀ M] [IsScalarTower A B M] [IsScalarTower R₀ A M]
    [IsScalarTower R₀ B M]
    (dA : Derivation R₀ A M) (a : A) {k : TrivSqZeroExt.kerIdeal B M}
    (hk :
      (k : TrivSqZeroExt B M) =
        trivSqZeroExtTwistedAlgebraMap (A := A) (B := B) R₀ M dA a -
          TrivSqZeroExt.inl (algebraMap A B a)) :
    (trivSqZeroExtKerIdealLinearEquiv B M) k = dA a := by
  -- Proof comment: the kernel equivalence is defined by the second projection, so the preceding
  -- second-component computation gives the desired value.
  change TrivSqZeroExt.snd (k : TrivSqZeroExt B M) = dA a
  rw [hk]
  exact trivSqZeroExtTwistedAlgebraMap_sub_inl_snd (A := A) (B := B) R₀ M dA a

/-- Helper for Chap10 Lemma 10 149 5: the universal first-order thickening property and formal
unramifiedness give the owner-level tensorized Kähler base-change isomorphism. -/
theorem isUniversal_lTensor_mapBaseChange_bijective_of_formallyUnramified
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    (hfu : FormallyUnramified A P.Ring) :
    Function.Bijective
      ((lTensor B B (KaehlerDifferential.mapBaseChange R₀ A P.Ring)) :
        B ⊗[P.Ring] (P.Ring ⊗[A] Ω[A⁄R₀]) →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R₀]) := by
  -- Route correction: the quotient-range proof stalled on a missing range/intersection
  -- identification. The active route factors the problem through the twisted square-zero map
  -- above; the remaining missing step is the universal lifting argument that turns this map into a
  -- surjectivity theorem for `Derivation.compAlgebraMapL`.
  -- TODO: construct the inverse by twisting the trivial square-zero extension `TrivSqZeroExt B M`
  -- by a chosen `R₀`-derivation of `A`, applying `hP` to lift through the square-zero kernel, and
  -- using the injectivity lemma above plus `hfu` for uniqueness on Kähler generators.
  sorry

/-- Helper for Chap10 Lemma 10 149 5: the owner-level tensorized `mapBaseChange` for the
canonical self-presentation section quotient is surjective. -/
theorem selfPresentation_section_quotient_ownerTensorMapBaseChange_surjective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
    Function.Surjective
      ((lTensor B B (KaehlerDifferential.mapBaseChange R₀ A Q.Ring)) :
        B ⊗[Q.Ring] (Q.Ring ⊗[A] Ω[A⁄R₀]) →ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀]) := by
  intro Q
  have hQfu : FormallyUnramified A Q.Ring := by
    -- Proof comment: the preceding conormal/Nakayama argument proves the canonical quotient is
    -- formally unramified over `A`.
    simpa [Q] using selfPresentation_section_quotient_formallyUnramified (A := A) (B := B) l hl
  let _ : Subsingleton Ω[Q.Ring⁄A] :=
    (Algebra.formallyUnramified_iff A Q.Ring).mp hQfu
  have hOwnerSurj :
      Function.Surjective (KaehlerDifferential.mapBaseChange R₀ A Q.Ring) :=
    kaehlerDifferential_mapBaseChange_surjective_of_subsingleton_kaehler
      (A := A) (B := B) (R₀ := R₀)
  -- Proof comment: tensoring on the left preserves surjectivity of the owner base-change map.
  exact LinearMap.lTensor_surjective B hOwnerSurj

/-- Helper for Chap10 Lemma 10 149 5: the owner-level tensorized `mapBaseChange` for the
canonical self-presentation section quotient is bijective. -/
theorem selfPresentation_section_quotient_ownerTensorMapBaseChange_bijective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
    Function.Bijective
      ((lTensor B B (KaehlerDifferential.mapBaseChange R₀ A Q.Ring)) :
        B ⊗[Q.Ring] (Q.Ring ⊗[A] Ω[A⁄R₀]) →ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀]) := by
  intro Q
  -- Route correction: the previous quotient-range proof stalled on a missing intersection
  -- identification.  We now specialize the abstract universal-thickening comparison to the
  -- self-presentation quotient, using the already proved universality and formal-unramifiedness.
  exact
    isUniversal_lTensor_mapBaseChange_bijective_of_formallyUnramified
      (A := A) (B := B) (R₀ := R₀) (P := Q)
      (by simpa [Q] using selfPresentation_section_quotient_isUniversal (A := A) (B := B) l hl)
      (by
        simpa [Q] using
          selfPresentation_section_quotient_formallyUnramified (A := A) (B := B) l hl)

/-- Helper for Chap10 Lemma 10 149 5: the canonical self-presentation section quotient has the
base-changed Kähler comparison directly, before transporting the result to an arbitrary universal
first-order thickening. -/
theorem selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective_direct
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    Function.Bijective
      (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀
        (selfPresentation_section_quotient (R := A) (S := B) l)) := by
  -- Route correction: this is the canonical quotient case that remains after the arbitrary
  -- universal thickening has been transported to the self-presentation quotient. The owner-level
  -- tensorized comparison is isolated above; its hard part is exactly the quotient-by-conormal
  -- range identification from the Stacks presentation proof.
  let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  refine
    kaehlerBaseChangeLinearMap_bijective_of_ownerTensorMapBaseChange_bijective
      (A := A) (B := B) (R₀ := R₀) Q ?_
  simpa [Q] using
    selfPresentation_section_quotient_ownerTensorMapBaseChange_bijective
      (A := A) (B := B) (R₀ := R₀) l hl

/-- Helper for Chap10 Lemma 10 149 5: a universal first-order thickening gives a bijective
base-changed Kähler comparison map. -/
theorem universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective_of_isUniversal
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P) := by
  -- Route correction: conormal surjectivity proves the formal-unramified quotient case, but the
  -- Kähler comparison needs the owner-level universal derivation-lifting theorem.  The intended
  -- proof constructs an inverse by lifting the base-changed universal derivation through `hP`,
  -- then proves both inverse laws on Kähler generators.
  obtain ⟨l, hl⟩ := selfPresentation_cotangentComplex_has_section (R := A) (S := B)
  let Q : Extension.{max v w} A B := selfPresentation_section_quotient (R := A) (S := B) l
  obtain ⟨e, he⟩ :=
    universalFirstOrderThickening_selfPresentation_equiv
      (P := P) hP l hl
  have hQbij :
      Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q) := by
    -- The canonical quotient case has been isolated as the remaining owner-level comparison.
    simpa [Q] using
      selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective_direct
        (A := A) (B := B) (R₀ := R₀) l hl
  -- The existing codomain-transport helper carries the canonical quotient bijectivity across the
  -- universal comparison equivalence.
  exact
    universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective_of_sourceAlgEquiv
      (A := A) (B := B) (R₀ := R₀) e he hQbij

/-- Helper for Chap10 Lemma 10 149 5: the canonical self-presentation section quotient has the
base-changed Kähler comparison isomorphism. -/
theorem selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    Function.Bijective
      (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀
        (selfPresentation_section_quotient (R := A) (S := B) l)) := by
  let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  -- Proof comment: the canonical quotient comparison is now an instance of the owner-level
  -- canonical quotient theorem.
  simpa [Q] using
    selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective_direct
      (A := A) (B := B) (R₀ := R₀) l hl

/-- Helper for Chap10 Lemma 10 149 5: a universal first-order thickening satisfies the formal
unramifiedness conclusion and the base-changed Kähler comparison conclusion. -/
theorem universalFirstOrderThickening_formallyUnramified_and_kaehlerBaseChangeLinearMap_bijective
    (R₀ : Type y) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    FormallyUnramified A P.Ring ∧
      Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P) := by
  -- The universal thickening is compared with the canonical quotient cut out by a section of the
  -- self-presentation cotangent complex.
  obtain ⟨l, hl⟩ := selfPresentation_cotangentComplex_has_section (R := A) (S := B)
  let Q : Extension.{max v w} A B := selfPresentation_section_quotient (R := A) (S := B) l
  obtain ⟨e, he⟩ :=
    universalFirstOrderThickening_selfPresentation_equiv
      (P := P) hP l hl
  have hQfu : FormallyUnramified A Q.Ring := by
    -- The canonical quotient case follows from the `A`-relative conormal exact sequence.
    simpa [Q] using selfPresentation_section_quotient_formallyUnramified (A := A) (B := B) l hl
  have hPfu : FormallyUnramified A P.Ring := by
    -- Once the canonical quotient case is known, formal unramifiedness transports across the
    -- universal comparison equivalence over `B`.
    let _ : FormallyUnramified A Q.Ring := hQfu
    exact Algebra.FormallyUnramified.of_equiv e.symm
  have hPbij :
      Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P) := by
    have hQbij :
        Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q) := by
      -- The remaining canonical quotient comparison is isolated in its own helper.
      simpa [Q] using
        selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective
          (A := A) (B := B) (R₀ := R₀) l hl
    -- The codomain equivalence converts the canonical quotient bijectivity into the desired
    -- bijectivity for `P`.
    exact
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective_of_sourceAlgEquiv
        (A := A) (B := B) (R₀ := R₀) e he hQbij
  exact ⟨hPfu, hPbij⟩

-- Proof sketch: prove the combined statement on the canonical self-presentation quotient, then
-- transport it to the arbitrary universal thickening and project the first component here.
/-- Lemma 10.149.5 (1): a universal first-order thickening `B'` of a formally unramified
`A`-algebra `B` is itself formally unramified over `A`. -/
@[stacks 04EF]
theorem universalFirstOrderThickening_formallyUnramified
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    FormallyUnramified A P.Ring := by
  -- The first projection of the combined theorem is the formal-unramifiedness assertion.
  exact
    (universalFirstOrderThickening_formallyUnramified_and_kaehlerBaseChangeLinearMap_bijective
      (A := A) (B := B) (R₀ := A) (P := P) hP).1

variable (R) (P)

-- Proof sketch: use the canonical Jacobi-Zariski/transitivity maps for `R → A → P.Ring → B`.
-- Route correction: the owner-level route through `KaehlerDifferential.mapBaseChange R A P.Ring`
-- alone is too strong. The remaining proof has to follow the Stacks presentation argument on the
-- canonical self-presentation quotient, then transport bijectivity back to `P`.
/-- Lemma 10.149.5 (2), companion owner-level statement: the canonical base-changed comparison map
on Kähler differentials attached to a universal first-order thickening is bijective. -/
@[stacks 04EF]
theorem universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P) := by
  exact
    (universalFirstOrderThickening_formallyUnramified_and_kaehlerBaseChangeLinearMap_bijective
      (A := A) (B := B) (R₀ := R) (P := P) hP).2

/-- Lemma 10.149.5 (2): in the library-facing tensor order, the canonical base-changed map
`B ⊗[A] Ω[A⁄R] → B ⊗[B'] Ω[B'⁄R]` attached to a universal first-order thickening `B'`
induces a `B`-linear isomorphism. -/
@[stacks 04EF]
noncomputable def universalFirstOrderThickening_kaehlerBaseChange
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  LinearEquiv.ofBijective
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P)
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective
      (R := R) (P := P) hP)

@[simp] theorem universalFirstOrderThickening_kaehlerBaseChange_toLinearMap
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    (universalFirstOrderThickening_kaehlerBaseChange (R := R) (P := P) hP).toLinearMap =
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P :=
  by
    ext x
    rfl

end Algebra.Extension
