import Mathlib
import StacksProject_2024.Chap15.Lemma_15_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits CommRingCat

universe u

section

variable {ι R : Type u} [Finite ι] [CommRing R]
variable {P Q : Type u} {A B : ι → Type u}
variable [CommRing P] [CommRing Q] [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [Algebra R P] [Algebra R Q] [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]

/-- Helper for Lemma 15.5.2: the explicit `CommRingCat` pullback cone has the same finite-type
owner as the equalizer/fibre-product ring from Lemma 15.5.1. -/
lemma equalizer_finiteType_of_surjective_of_finite
    {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Algebra.FiniteType R T]
    (φ : S →ₐ[R] U) (ψ : T →ₐ[R] U) (hφ : Function.Surjective φ) (hψ : ψ.Finite) :
    Algebra.FiniteType R
      (AlgHom.equalizer (φ.comp (AlgHom.fst R S T)) (ψ.comp (AlgHom.snd R S T))) := by
  -- This is exactly the fibre-product owner from Lemma 15.5.1.
  simpa using finiteType_fiberProduct_of_surjective_of_finite φ ψ hφ hψ

/- Helper API for the finite-family reduction:
- `pi_option_algEquiv_prod` turns an `Option`-indexed product into a binary product, which is the
  induction step for finite products of finite-type algebras;
- `finiteType_pi_of_finiteType` packages the resulting finite-index induction;
- the two `Pi.algHom` helpers lift pointwise surjectivity and finiteness to the product maps used
  by the final pullback argument. -/

/-- Helper for Lemma 15.5.2: the canonical map from an `Option`-indexed product algebra to the
binary product of its distinguished coordinate and tail is bijective. -/
lemma pi_option_algHom_bijective
    {κ : Type u} (A : Option κ → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    Function.Bijective
      ((Pi.evalAlgHom R A none).prod
        (Pi.algHom R (fun i : κ ↦ A (some i)) fun i ↦ Pi.evalAlgHom R A (some i))) := by
  let Φ : (∀ i : Option κ, A i) →ₐ[R] A none × ∀ i : κ, A (some i) :=
    (Pi.evalAlgHom R A none).prod
      (Pi.algHom R (fun i : κ ↦ A (some i)) fun i ↦ Pi.evalAlgHom R A (some i))
  -- Compare with the standard `Option`-product equivalence on dependent functions.
  constructor
  · intro x y hxy
    exact (Equiv.piOptionEquivProd : (∀ i : Option κ, A i) ≃ A none × ∀ i : κ, A (some i)).injective
      (by simpa [Φ] using hxy)
  · intro y
    refine ⟨(Equiv.piOptionEquivProd : (∀ i : Option κ, A i) ≃ A none × ∀ i : κ, A (some i)).symm y, ?_⟩
    ext <;> rfl

/-- Helper for Lemma 15.5.2: an `Option`-indexed product algebra is canonically equivalent to the
product of its distinguished coordinate and the remaining family. -/
noncomputable def pi_option_algEquiv_prod
    {κ : Type u} (A : Option κ → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    (∀ i : Option κ, A i) ≃ₐ[R] A none × ∀ i : κ, A (some i) :=
  AlgEquiv.ofBijective
    ((Pi.evalAlgHom R A none).prod
      (Pi.algHom R (fun i : κ ↦ A (some i)) fun i ↦ Pi.evalAlgHom R A (some i)))
    (pi_option_algHom_bijective (R := R) A)

/-- Helper for Lemma 15.5.2: a finite product of finite-type commutative `R`-algebras is again of
finite type over `R`. -/
lemma finiteType_pi_of_finiteType
    (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FiniteType R (A i)] :
    Algebra.FiniteType R (∀ i, A i) := by
  classical
  cases nonempty_fintype ι
  let P : ∀ (κ : Type u) [Fintype κ], Prop := fun κ _ =>
    ∀ (B : κ → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
      [∀ i, Algebra.FiniteType R (B i)], Algebra.FiniteType R (∀ i, B i)
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e hα
      intro B hComm hAlg hFt
      letI : ∀ i, CommRing (B i) := hComm
      letI : ∀ i, Algebra R (B i) := hAlg
      letI : ∀ i, Algebra.FiniteType R (B i) := hFt
      -- Reindex the family along the equivalence before transporting finite type back.
      exact Algebra.FiniteType.equiv (hα (fun a ↦ B (e a)))
        (by simpa using (AlgEquiv.piCongrLeft R B e))
    · intro B hComm hAlg hFt
      letI : ∀ i, CommRing (B i) := hComm
      letI : ∀ i, Algebra R (B i) := hAlg
      letI : ∀ i, Algebra.FiniteType R (B i) := hFt
      -- The empty product is the terminal one-element ring, hence finite as a module.
      letI : IsEmpty PEmpty := inferInstance
      letI : Inhabited (∀ a : PEmpty, B a) := ⟨fun a ↦ (IsEmpty.false a).elim⟩
      letI : Subsingleton (∀ a : PEmpty, B a) := ⟨fun f g ↦ funext fun a ↦ (IsEmpty.false a).elim⟩
      infer_instance
    · intro α _ hα
      intro B hComm hAlg hFt
      letI : ∀ i, CommRing (B i) := hComm
      letI : ∀ i, Algebra R (B i) := hAlg
      letI : ∀ i, Algebra.FiniteType R (B i) := hFt
      -- Split off the distinguished `none` coordinate and use the product instance.
      letI : ∀ a, CommRing (B (some a)) := fun a ↦ hComm (some a)
      letI : ∀ a, Algebra R (B (some a)) := fun a ↦ hAlg (some a)
      letI : ∀ a, Algebra.FiniteType R (B (some a)) := fun a ↦ hFt (some a)
      letI : Algebra.FiniteType R (∀ a : α, B (some a)) := hα (fun a ↦ B (some a))
      exact Algebra.FiniteType.equiv inferInstance
        (by simpa using (pi_option_algEquiv_prod (R := R) B).symm)
  exact hP A

/-- Helper for Lemma 15.5.2: coordinatewise surjectivity makes the product map surjective. -/
lemma pi_algHom_surjective_of_surjective
    (φ : ∀ i, A i →ₐ[R] B i) (hφ : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (Pi.algHom R B fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)) := by
  classical
  intro b
  choose a ha using fun i ↦ hφ i (b i)
  refine ⟨fun i ↦ a i, ?_⟩
  ext i
  simpa using ha i

/-- Helper for Lemma 15.5.2: if every coordinate map `Q → Bᵢ` is finite, then the product map
`Q → ∏ Bᵢ` is finite as well. -/
lemma pi_algHom_finite_of_finite
    {κ : Type u} {Q' : Type u} {B' : κ → Type u}
    [Finite κ]
    [CommRing Q'] [∀ i, CommRing (B' i)] [Algebra R Q'] [∀ i, Algebra R (B' i)]
    (ψ : ∀ i, Q' →ₐ[R] B' i) (hψ : ∀ i, (ψ i).Finite) :
    (Pi.algHom R B' ψ).Finite := by
  classical
  -- The target product is a finite `Q'`-module once every coordinate is.
  letI : ∀ i, Algebra Q' (B' i) := fun i ↦ (ψ i).toAlgebra
  letI : ∀ i, Module.Finite Q' (B' i) := fun i ↦ by
    simpa [AlgHom.Finite, RingHom.Finite] using hψ i
  letI : Algebra Q' (∀ i, B' i) := Pi.algebra _ _
  change Module.Finite Q' (∀ i, B' i)
  infer_instance

/- Domain-style sampling:
- primary domain: finite-type stability for finite fibre products of commutative `R`-algebras,
  expressed through pullback squares in `CommRingCat`;
- sampled owner declarations:
  `CommRingCat.pullbackCone`,
  `CommRingCat.pullbackConeIsLimit`,
  `AlgHom.equalizer`,
  `finiteType_fiberProduct_of_surjective_of_finite`;
- best owner abstraction: the source-facing data is the finite family of comparison maps together
  with a categorical pullback witness in `CommRingCat`, while the canonical owner for the
  underlying binary fibre-product ring is still the equalizer/fibre-product API from
  `Lemma_15_5_1`;
- primitive data: the families `φ`, `ψ`, the maps `f`, `g`, the pointwise surjectivity
  hypotheses, and the pullback witness `hcart`;
- derived API: the finite-type conclusion for the pullback ring `P`.

Source/core/bridge triage:
- `source-facing`: the statement about an arbitrary pullback square in `CommRingCat`;
- `core/canonical`: `CommRingCat.pullbackCone` for the categorical owner and
  `finiteType_fiberProduct_of_surjective_of_finite` for the binary algebraic fibre-product
  owner;
- `bridge/view`: passing from the abstract pullback witness `hcart` to the canonical fibre-product
  presentation used by the binary finite-type theorem. -/

-- Proof sketch: induct on the finite index type `ι`. For the inductive step, split off one index
-- `i₀`, apply the induction hypothesis to the pullback defined by the remaining family, and then
-- apply Lemma 15.5.1 to the resulting binary fibre product square with `A i₀ → B i₀`.
/-- Lemma 15.5.2: for a finite family of surjections `Aᵢ → Bᵢ` and `Q → Bᵢ` over a Noetherian
base ring `R`, any pullback ring `P` of `Q → ∏ i, B i` and `∏ i, A i → ∏ i, B i` is of finite
type over `R` as soon as `Q` and all `Aᵢ` are of finite type over `R`; finite type of each `Bᵢ`
is derived from the surjections `Q → Bᵢ`. -/
@[stacks 08NI]
theorem finiteType_of_isPullback_pi_of_surjective
    [IsNoetherianRing R] [Algebra.FiniteType R Q]
    [∀ i, Algebra.FiniteType R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i) (f : P →ₐ[R] Q)
    (g : P →ₐ[R] ∀ i, A i) (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i)) (hcart : IsPullback (ofHom f.toRingHom)
      (ofHom g.toRingHom) (ofHom (Pi.algHom R B ψ).toRingHom)
      (ofHom (Pi.algHom R B fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)).toRingHom)) :
    Algebra.FiniteType R P := by
  classical
  let φpi : (∀ i, A i) →ₐ[R] ∀ i, B i :=
    Pi.algHom R B fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)
  let ψpi : Q →ₐ[R] ∀ i, B i := Pi.algHom R B ψ
  -- First package the product-side surjectivity and finiteness needed for Lemma 15.5.1.
  have hφpi : Function.Surjective φpi := by
    simpa [φpi] using pi_algHom_surjective_of_surjective (R := R) φ hφ
  have hψfinite : ∀ i, (ψ i).Finite := fun i ↦ AlgHom.Finite.of_surjective (ψ i) (hψ i)
  have hψpi : ψpi.Finite := by
    simpa [ψpi] using pi_algHom_finite_of_finite (R := R) ψ hψfinite
  have hApi : Algebra.FiniteType R (∀ i, A i) := finiteType_pi_of_finiteType (R := R) A
  let E := AlgHom.equalizer (φpi.comp (AlgHom.fst R (∀ i, A i) Q))
    (ψpi.comp (AlgHom.snd R (∀ i, A i) Q))
  have hE : Algebra.FiniteType R E :=
    equalizer_finiteType_of_surjective_of_finite (R := R) φpi ψpi hφpi hψpi
  let toEqualizer : P →ₐ[R] E :=
    (g.prod f).codRestrict E fun x ↦ by
      -- The pullback commutativity exactly says that `(g x, f x)` lies in the equalizer.
      change φpi (g x) = ψpi (f x)
      have hcomm :=
        congrArg (fun h : P →+* ∀ i, B i => h x) (congrArg Hom.hom hcart.w)
      simpa [φpi, ψpi] using hcomm.symm
  let fromEqualizerHom : CommRingCat.of E ⟶ CommRingCat.of P :=
    hcart.flip.isLimit.lift <|
      PullbackCone.mk
        (ofHom (((AlgHom.fst R (∀ i, A i) Q).comp E.val).toRingHom))
        (ofHom (((AlgHom.snd R (∀ i, A i) Q).comp E.val).toRingHom))
        (by
          ext x i
          exact congrFun x.property i)
  have h_from_left :
      fromEqualizerHom ≫ ofHom g.toRingHom =
        ofHom (((AlgHom.fst R (∀ i, A i) Q).comp E.val).toRingHom) := by
    simpa using hcart.flip.isLimit.fac
      (PullbackCone.mk
        (ofHom (((AlgHom.fst R (∀ i, A i) Q).comp E.val).toRingHom))
        (ofHom (((AlgHom.snd R (∀ i, A i) Q).comp E.val).toRingHom))
        (by
          ext x i
          exact congrFun x.property i))
      WalkingCospan.left
  have h_from_right :
      fromEqualizerHom ≫ ofHom f.toRingHom =
        ofHom (((AlgHom.snd R (∀ i, A i) Q).comp E.val).toRingHom) := by
    simpa using hcart.flip.isLimit.fac
      (PullbackCone.mk
        (ofHom (((AlgHom.fst R (∀ i, A i) Q).comp E.val).toRingHom))
        (ofHom (((AlgHom.snd R (∀ i, A i) Q).comp E.val).toRingHom))
        (by
          ext x i
          exact congrFun x.property i))
      WalkingCospan.right
  have h_to_from :
      toEqualizer.toRingHom.comp fromEqualizerHom.hom = RingHom.id E := by
    refine RingHom.ext ?_
    intro x
    apply Subtype.ext
    apply Prod.ext
    · have hx₁ := congrArg (fun h : E →+* ∀ i, A i => h x) (congrArg Hom.hom h_from_left)
      simpa [toEqualizer, RingHom.comp_apply] using hx₁
    · have hx₂ := congrArg (fun h : E →+* Q => h x) (congrArg Hom.hom h_from_right)
      simpa [toEqualizer, RingHom.comp_apply] using hx₂
  have h_from_to_cat :
      ofHom toEqualizer.toRingHom ≫ fromEqualizerHom = 𝟙 (CommRingCat.of P) := by
    apply PullbackCone.IsLimit.hom_ext hcart.flip.isLimit
    · calc
        ofHom toEqualizer.toRingHom ≫ fromEqualizerHom ≫ ofHom g.toRingHom
            = ofHom toEqualizer.toRingHom ≫ ofHom (((AlgHom.fst R (∀ i, A i) Q).comp E.val).toRingHom) := by
                rw [h_from_left]
        _ = ofHom g.toRingHom := by
          ext x
          rfl
        _ = 𝟙 (CommRingCat.of P) ≫ ofHom g.toRingHom := by simp
    · calc
        ofHom toEqualizer.toRingHom ≫ fromEqualizerHom ≫ ofHom f.toRingHom
            = ofHom toEqualizer.toRingHom ≫ ofHom (((AlgHom.snd R (∀ i, A i) Q).comp E.val).toRingHom) := by
                rw [h_from_right]
        _ = ofHom f.toRingHom := by
          ext x
          rfl
        _ = 𝟙 (CommRingCat.of P) ≫ ofHom f.toRingHom := by simp
  have h_from_to :
      fromEqualizerHom.hom.comp toEqualizer.toRingHom = RingHom.id P := by
    simpa [RingHom.comp_apply] using congrArg Hom.hom h_from_to_cat
  have hBij : Function.Bijective toEqualizer := by
    constructor
    · intro x y hxy
      have hx : fromEqualizerHom.hom (toEqualizer x) = x := by
        simpa [RingHom.comp_apply] using congrArg (fun h : P →+* P => h x) h_from_to
      have hy : fromEqualizerHom.hom (toEqualizer y) = y := by
        simpa [RingHom.comp_apply] using congrArg (fun h : P →+* P => h y) h_from_to
      rw [hxy] at hx
      exact hx.symm.trans hy
    · intro x
      refine ⟨fromEqualizerHom.hom x, ?_⟩
      have hx := congrArg (fun h : E →+* E => h x) h_to_from
      simpa [RingHom.comp_apply] using hx
  let eAlg : P ≃ₐ[R] E := AlgEquiv.ofBijective toEqualizer hBij
  exact Algebra.FiniteType.equiv hE eAlg.symm

end
