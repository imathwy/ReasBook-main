import Mathlib
import Mathlib.Order.KrullDimension
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Sets.Closeds

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

section

variable (X : Scheme.{u})

-- Semantic recall / analogue check:
-- * `lean_leansearch` found the canonical scheme-side assumptions `IsLocallyNoetherian` and
--   `IsIntegral`, but no existing owner for scheme-level Weil divisors in this workspace.
-- * Chapter 29's `IrreducibleComponent` uses a closed-immersion inclusion together with an
--   explicit `IrreducibleCloseds` support owner; the prime-divisor definition here follows that
--   established scheme-side pattern.
-- * The ambient noetherian/integral hypotheses enter later in Chapter 31 existence results, not
--   in the owner declarations themselves.
-- * Definition 5.28.4 is the canonical owner `LocallyFinite`, and Definition 5.11.1 identifies
--   codimension with `Order.coheight` on `IrreducibleCloseds`.

/-- Definition 31.26.2 (1): a prime divisor on a locally Noetherian integral scheme `X` is an
integral closed subscheme of codimension `1`. It is represented here by its closed-immersion
inclusion together with the associated irreducible closed subset of `X`. -/
structure PrimeDivisor where
  /-- The underlying integral closed subscheme. -/
  carrier : Scheme.{u}
  /-- The inclusion of the closed subscheme into `X`. -/
  ι : carrier ⟶ X
  /-- A prime divisor is a closed subscheme of `X`. -/
  isClosedImmersion_ι : IsClosedImmersion ι
  /-- The underlying closed subscheme is integral. -/
  isIntegral_carrier : IsIntegral carrier
  /-- The underlying closed subset of the prime divisor, packaged as an irreducible closed set. -/
  asIrreducibleClosed : TopologicalSpace.IrreducibleCloseds X
  /-- The underlying irreducible closed subset agrees with the image of the inclusion. -/
  asIrreducibleClosed_eq_range : (asIrreducibleClosed : Set X) = Set.range ι.base
  /-- The underlying irreducible closed subset has codimension `1` in `X`. -/
  coheight_asIrreducibleClosed : Order.coheight asIrreducibleClosed = 1

/-- The irreducible closed support underlying a prime divisor. -/
abbrev PrimeDivisor.support (Z : PrimeDivisor X) : TopologicalSpace.IrreducibleCloseds X :=
  Z.asIrreducibleClosed

/-- A prime divisor canonically determines its underlying irreducible closed subset. -/
instance instCoePrimeDivisorIrreducibleCloseds :
    Coe (PrimeDivisor X) (TopologicalSpace.IrreducibleCloseds X) where
  coe := fun Z ↦ Z.support

/-- The carrier of a prime divisor is integral. -/
instance instIsIntegralPrimeDivisorCarrier (Z : PrimeDivisor X) : IsIntegral Z.carrier :=
  Z.isIntegral_carrier

/-- The inclusion of a prime divisor into the ambient scheme is a closed immersion. -/
instance instIsClosedImmersionPrimeDivisorι (Z : PrimeDivisor X) : IsClosedImmersion Z.ι :=
  Z.isClosedImmersion_ι

/-- The support of a prime divisor is the image of its closed-immersion inclusion. -/
theorem PrimeDivisor.support_eq_range (Z : PrimeDivisor X) :
    (Z.support : Set X) = Set.range Z.ι.base :=
  Z.asIrreducibleClosed_eq_range

/-- The underlying irreducible closed subset of a prime divisor has codimension `1`. -/
theorem PrimeDivisor.coheight_eq_one (Z : PrimeDivisor X) :
    Order.coheight Z.support = 1 :=
  Z.coheight_asIrreducibleClosed

/-- The generic point of the support of a prime divisor. -/
noncomputable abbrev PrimeDivisor.genericPoint (Z : PrimeDivisor X) : X :=
  let hZ := Z.support.isIrreducible
  hZ.genericPoint

/-- Definition 31.26.2 (2): a Weil divisor on a locally Noetherian integral scheme `X` is a formal
integer linear combination of prime divisors whose nonzero-coefficient support is locally finite.
The additive group of all Weil divisors is denoted `Div(X)`. -/
structure WeilDivisor where
  /-- The integer coefficient of a prime divisor in the formal sum. -/
  coeff : PrimeDivisor X → ℤ
  /-- The family of prime divisors with nonzero coefficient is locally finite on `X`. -/
  locallyFinite_nonzeroCoefficients :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if coeff Z = 0 then (∅ : Set X) else (Z.support : Set X)

/-- The family attached to a Weil divisor, supported on those prime divisors with nonzero
coefficient. -/
abbrev WeilDivisor.supportFamily (D : WeilDivisor X) : PrimeDivisor X → Set X := fun Z ↦
  if D.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X)

/-- The nonzero-coefficient support family of a Weil divisor is locally finite. -/
theorem WeilDivisor.locallyFinite_supportFamily (D : WeilDivisor X) :
    LocallyFinite D.supportFamily :=
  D.locallyFinite_nonzeroCoefficients

private theorem locallyFinite_nonzeroCoefficients_add (D E : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if D.coeff Z + E.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) := by
  let f := D.supportFamily
  let g := E.supportFamily
  have hf : LocallyFinite f := D.locallyFinite_supportFamily
  have hg : LocallyFinite g := E.locallyFinite_supportFamily
  have hfg : LocallyFinite fun Z ↦ f Z ∪ g Z := by
    intro x
    rcases hf x with ⟨s, hs, hfs⟩
    rcases hg x with ⟨t, ht, hgt⟩
    refine ⟨s ∩ t, Filter.inter_mem hs ht, ?_⟩
    refine (hfs.union hgt).subset ?_
    intro Z hZ
    rcases hZ with ⟨y, hy⟩
    rcases hy with ⟨hyfg, hst⟩
    rcases hyfg with hyf | hyg
    · left
      exact ⟨y, hyf, hst.1⟩
    · right
      exact ⟨y, hyg, hst.2⟩
  refine hfg.subset ?_
  intro Z x hx
  by_cases hsum : D.coeff Z + E.coeff Z = 0
  · simp [hsum] at hx
  · have hx' : x ∈ (Z.support : Set X) := by
      simpa [hsum] using hx
    by_cases hD : D.coeff Z = 0
    · have hE : E.coeff Z ≠ 0 := by
        intro hE
        exact hsum (by simp [hD, hE])
      exact Or.inr <| by simpa [g, hE] using hx'
    · exact Or.inl <| by simpa [f, hD] using hx'

private theorem locallyFinite_nonzeroCoefficients_neg (D : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if -D.coeff Z = 0 then (∅ : Set X) else (Z.support : Set X) := by
  simpa [WeilDivisor.supportFamily, neg_eq_zero] using D.locallyFinite_supportFamily

@[ext]
theorem WeilDivisor.ext {D E : WeilDivisor X}
    (hcoeff : ∀ Z : PrimeDivisor X, D.coeff Z = E.coeff Z) : D = E := by
  cases D
  cases E
  cases funext hcoeff
  simp

/-- The zero Weil divisor has all coefficients equal to `0`. -/
instance instZeroWeilDivisor : Zero (WeilDivisor X) where
  zero :=
    { coeff := fun _ ↦ 0
      locallyFinite_nonzeroCoefficients := by
        intro x
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        simp }

/-- Addition of Weil divisors is defined coefficientwise. -/
instance instAddWeilDivisor : Add (WeilDivisor X) where
  add D E :=
    { coeff := fun Z ↦ D.coeff Z + E.coeff Z
      locallyFinite_nonzeroCoefficients := by
        simpa using locallyFinite_nonzeroCoefficients_add X D E }

/-- Negation of a Weil divisor is defined coefficientwise. -/
instance instNegWeilDivisor : Neg (WeilDivisor X) where
  neg D :=
    { coeff := fun Z ↦ -D.coeff Z
      locallyFinite_nonzeroCoefficients := by
        simpa using locallyFinite_nonzeroCoefficients_neg X D }

/-- Subtraction of Weil divisors is defined coefficientwise. -/
instance instSubWeilDivisor : Sub (WeilDivisor X) where
  sub D E :=
    { coeff := fun Z ↦ D.coeff Z - E.coeff Z
      locallyFinite_nonzeroCoefficients := by
        simpa [sub_eq_add_neg] using locallyFinite_nonzeroCoefficients_add X D (-E) }

@[simp] theorem WeilDivisor.coeff_zero (Z : PrimeDivisor X) : (0 : WeilDivisor X).coeff Z = 0 := rfl

@[simp] theorem WeilDivisor.coeff_add (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D + E).coeff Z = D.coeff Z + E.coeff Z := rfl

@[simp] theorem WeilDivisor.coeff_neg (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (-D).coeff Z = -D.coeff Z := rfl

@[simp] theorem WeilDivisor.coeff_sub (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D - E).coeff Z = D.coeff Z - E.coeff Z := rfl

instance instSMulNatWeilDivisor : SMul ℕ (WeilDivisor X) where
  smul := nsmulRec

instance instSMulIntWeilDivisor : SMul ℤ (WeilDivisor X) where
  smul := zsmulRec

@[simp] theorem WeilDivisor.coeff_nsmul (n : ℕ) (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (n • D).coeff Z = n • D.coeff Z := by
  induction n with
  | zero =>
      change (0 : WeilDivisor X).coeff Z = 0 • D.coeff Z
      rw [zero_nsmul]
      rfl
  | succ n ih =>
      change (nsmulRec n D + D).coeff Z = (n + 1) • D.coeff Z
      rw [WeilDivisor.coeff_add, succ_nsmul]
      simpa [HSMul.hSMul] using congrArg (fun x ↦ x + D.coeff Z) ih

@[simp] theorem WeilDivisor.coeff_zsmul (n : ℤ) (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (n • D).coeff Z = n • D.coeff Z := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact WeilDivisor.coeff_nsmul X n D Z
  | negSucc n =>
      change (-((nsmulRec (n + 1) D).coeff Z)) = (Int.negSucc n) • D.coeff Z
      rw [negSucc_zsmul]
      simpa [HSMul.hSMul] using congrArg Neg.neg
        (WeilDivisor.coeff_nsmul X (n + 1) D Z)

private theorem coeff_injective : Function.Injective (fun D : WeilDivisor X ↦ D.coeff) := by
  intro D E h
  ext Z
  exact congrFun h Z

/-- Weil divisors form an additive commutative group under pointwise operations on coefficients. -/
instance instAddCommGroupWeilDivisor : AddCommGroup (WeilDivisor X) :=
  Function.Injective.addCommGroup (fun D : WeilDivisor X ↦ D.coeff) (coeff_injective X)
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun D n ↦ funext <| WeilDivisor.coeff_nsmul X n D)
    (fun D n ↦ funext <| WeilDivisor.coeff_zsmul X n D)

notation "Div(" X ")" => WeilDivisor X

end

end AlgebraicGeometry
