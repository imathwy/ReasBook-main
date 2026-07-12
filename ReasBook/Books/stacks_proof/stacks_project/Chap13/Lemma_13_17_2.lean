import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe wA wQ uA vA

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits Q :=
  preservesFiniteLimits Q P

local instance : PreservesFiniteColimits Q :=
  preservesFiniteColimits Q P

/- Domain-style sampling for 13.17.2:
- primary domain: Serre localizations of abelian categories and the induced functor on derived
  categories;
- sampled owner declarations:
  `ObjectProperty.SerreClassLocalization.abelian`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteLimits`,
  `ObjectProperty.SerreClassLocalization.preservesFiniteColimits`,
  `CategoryTheory.Functor.mapDerivedCategory`,
  `CategoryTheory.Functor.EssSurj`;
- best owner abstraction: the derived functor owner `Q.mapDerivedCategory` of the
  canonical Serre quotient functor `Q := P.isoModSerre.Q`;
- primitive data: the Serre class `P` and the quotient functor `Q`;
- derived API: the abelian structure on `P.isoModSerre.Localization` and the finite-limit and
  finite-colimit preservation instances for `Q`, supplied canonically by the Serre-localization
  owner API and consumed directly by `Q.mapDerivedCategory`;
- source/core/bridge triage:
  `source-facing`: the essential-surjectivity statement for the derived Serre quotient functor;
  `core/canonical`: `Q.mapDerivedCategory`;
  `bridge/view`: objectwise preimages in the underived Serre quotient, transported to the derived
  category through complex representatives and the localization map `DerivedCategory.Q`.

This file therefore uses the Serre-localization owner instances directly instead of repackaging
them through a local exactness wrapper. -/

-- Proof sketch: represent an object of `D(A / P)` by a complex in the Serre quotient, then use
-- Lemma 12.10.6 degreewise to lift the differential data to a quasi-isomorphic complex in `A`.
-- The lifted complex becomes isomorphic to the original object after applying the derived functor,
-- producing the canonical owner witness `Q.mapDerivedCategory.EssSurj`.
/-- Helper for Lemma 13.17.2: every quotient complex is isomorphic to the conjugate complex on the
chosen objectwise preimages of `Q`. -/
lemma serre_quotient_complex_on_preimages
    (K : CochainComplex P.isoModSerre.Localization ℤ) :
    ∃ K₀ : CochainComplex P.isoModSerre.Localization ℤ,
      Nonempty (K₀ ≅ K) := by
  let δ : ∀ n : ℤ,
      (Q).obj ((Q).objPreimage (K.X n)) ⟶ (Q).obj ((Q).objPreimage (K.X (n + 1))) :=
    fun n ↦ ((Q).objObjPreimageIso (K.X n)).hom ≫ K.d n (n + 1) ≫
      ((Q).objObjPreimageIso (K.X (n + 1))).inv
  have hδ : ∀ n : ℤ, δ n ≫ δ (n + 1) = 0 := by
    intro n
    -- Transport the square-zero relation of `K` through the chosen objectwise isomorphisms.
    have h :=
      congrArg
        (fun t ↦ ((Q).objObjPreimageIso (K.X n)).hom ≫ t ≫
          ((Q).objObjPreimageIso (K.X (n + 1 + 1))).inv)
        (K.d_comp_d n (n + 1) (n + 1 + 1))
    simpa [δ, Category.assoc] using h
  let K₀ : CochainComplex P.isoModSerre.Localization ℤ :=
    CochainComplex.of
      (fun n ↦ (Q).obj ((Q).objPreimage (K.X n)))
      δ
      hδ
  refine ⟨K₀, ?_⟩
  refine ⟨HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (Q).objObjPreimageIso (K.X n))
      (fun i j hij ↦ ?_)⟩
  -- The componentwise preimage isomorphisms conjugate the normalized complex back to `K`.
  have h : i + 1 = j := by
    simpa using hij
  subst j
  simp [K₀, δ, Category.assoc]

/-- Helper for Lemma 13.17.2: once the source proof has produced degreewise objects, vertical
isomorphisms, and actual arrows in `A`, this data packages into a quotient complex isomorphic to
the original one. -/
lemma serre_quotient_complex_of_degreewise_presentation
    (K : CochainComplex P.isoModSerre.Localization ℤ)
    (X' : ℤ → A)
    (e : ∀ n, (Q).obj (X' n) ≅ K.X n)
    (δ : ∀ n : ℤ, X' n ⟶ X' (n + 1))
    (hδ : ∀ n : ℤ,
      (e n).hom ≫ K.d n (n + 1) ≫ (e (n + 1)).inv = (Q).map (δ n))
    (hsq : ∀ n : ℤ, δ n ≫ δ (n + 1) = 0) :
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).essImage K := by
  have hδ_nat :
      ∀ n : ℤ, (Q).map (δ n) ≫ (e (n + 1)).hom = (e n).hom ≫ K.d n (n + 1) := by
    intro n
    -- Move the comparison isomorphism on degree `n + 1` to the right to obtain the chain-map
    -- equation needed by `isoOfComponents`.
    simpa [Category.assoc] using
      (congrArg (fun t ↦ t ≫ (e (n + 1)).hom) (hδ n)).symm
  let L : CochainComplex A ℤ :=
    CochainComplex.of
      X'
      δ
      hsq
  refine ⟨L, ?_⟩
  refine ⟨HomologicalComplex.Hom.isoOfComponents e (fun i j hij ↦ ?_)⟩
  have h : i + 1 = j := by
    simpa using hij
  subst j
  -- The packaged complex is componentwise identified with `K` by the given conjugation data.
  simpa [L, Category.assoc] using (hδ_nat i).symm

/-- Helper for Lemma 13.17.2: a single positive-degree differential in the quotient with upstairs
source can be normalized by a pushout step, exactly as in the source proof. -/
lemma serre_quotient_nonnegative_step
    {X Z : A} (g : (Q).obj X ⟶ (Q).obj Z) :
    Nonempty (Σ' Y : A, Σ' e : (Q).obj Y ≅ (Q).obj Z, Σ' δ : X ⟶ Y,
      g ≫ e.inv = (Q).map δ) := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction Q P.isoModSerre g
  have hψ' : (Q).map ψ.f = (Q).map ψ.s ≫ g := by
    -- Precompose the fraction identity by the mapped denominator to obtain the commutative square
    -- used in the pushout step of the source proof.
    simpa [MorphismProperty.RightFraction.map, Category.assoc] using
      congrArg (fun k ↦ (Q).map ψ.s ≫ k) hψ.symm
  let Y := pushout ψ.s ψ.f
  let ePush : pushout ((Q).map ψ.s) ((Q).map ψ.f) ≅ (Q).obj Y :=
    PreservesPushout.iso Q ψ.s ψ.f
  haveI : IsIso ((Q).map ψ.s) :=
    Localization.inverts Q P.isoModSerre ψ.s ψ.hs
  haveI : IsIso (pushout.inr ((Q).map ψ.s) ((Q).map ψ.f)) := by infer_instance
  let e : (Q).obj Y ≅ (Q).obj Z :=
    ((asIso (pushout.inr ((Q).map ψ.s) ((Q).map ψ.f))) ≪≫ ePush).symm
  refine ⟨⟨Y, e, pushout.inl ψ.s ψ.f, ?_⟩⟩
  have he_inv :
      e.inv = (Q).map (pushout.inr ψ.s ψ.f) := by
    -- The new vertical isomorphism is the inverse of the mapped right coprojection after
    -- transporting the pushout through `Q`.
    dsimp [e]
    calc
      pushout.inr ((Q).map ψ.s) ((Q).map ψ.f) ≫ ePush.hom =
          ((Q).map (pushout.inr ψ.s ψ.f) ≫ ePush.inv) ≫ ePush.hom := by
            rw [PreservesPushout.inr_iso_inv Q ψ.s ψ.f]
      _ = (Q).map (pushout.inr ψ.s ψ.f) := by
            simp [Category.assoc]
  -- The pushout relation becomes the desired represented differential after canceling the mapped
  -- denominator, which is invertible in the localization.
  rw [he_inv]
  apply (cancel_epi ((Q).map ψ.s)).1
  calc
    (Q).map ψ.s ≫ (g ≫ (Q).map (pushout.inr ψ.s ψ.f)) =
        ((Q).map ψ.s ≫ g) ≫ (Q).map (pushout.inr ψ.s ψ.f) := by
          simp [Category.assoc]
    _ = (Q).map ψ.f ≫ (Q).map (pushout.inr ψ.s ψ.f) := by
          rw [hψ']
    _ = (Q).map (ψ.f ≫ pushout.inr ψ.s ψ.f) := by
          simp [Functor.map_comp]
    _ = (Q).map (ψ.s ≫ pushout.inl ψ.s ψ.f) := by
          rw [pushout.condition]
    _ = (Q).map ψ.s ≫ (Q).map (pushout.inl ψ.s ψ.f) := by
          simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: the degree-zero source term for the positive pushout recursion is
the canonical preimage object of `K₀.X 0`. -/
lemma serre_quotient_nonnegative_base
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    Nonempty (Σ' X0 : A, (Q).obj X0 ≅ K₀.X 0) := by
  -- The source proof starts the positive recursion from the chosen preimage of the degree-zero
  -- term.
  exact ⟨⟨(Q).objPreimage (K₀.X 0), (Q).objObjPreimageIso (K₀.X 0)⟩⟩

/-- Helper for Lemma 13.17.2: once degree `n` has an upstairs representative, the next quotient
differential can be normalized by one pushout step and transported back to `K₀.X (n + 1)`. -/
lemma serre_quotient_nonnegative_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n)) :
    Nonempty (Σ' Xnext : A, Σ' e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (n + 1)),
      Σ' δ_n : Xn ⟶ Xnext,
        (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ e_next.inv = (Q).map δ_n) := by
  let Z := (Q).objPreimage (K₀.X (Int.ofNat (n + 1)))
  let g : (Q).obj Xn ⟶ (Q).obj Z :=
    (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
      ((Q).objObjPreimageIso (K₀.X (Int.ofNat (n + 1)))).inv
  obtain ⟨Y, e, δ, hδ⟩ := serre_quotient_nonnegative_step (P := P) g
  let e_next : (Q).obj Y ≅ K₀.X (Int.ofNat (n + 1)) :=
    e ≪≫ (Q).objObjPreimageIso (K₀.X (Int.ofNat (n + 1)))
  refine ⟨⟨Y, e_next, δ, ?_⟩⟩
  -- Postcompose the pushout normalization with the canonical preimage isomorphism on the target.
  simpa [g, e_next, Category.assoc] using hδ

/-- Helper for Lemma 13.17.2: the positive-degree pushout construction can be iterated over all
natural degrees, producing actual upstairs differentials on every `n ≥ 0`. -/
lemma serre_quotient_nonnegative_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    Nonempty (Σ' Xplus : ℕ → A, Σ' eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n),
      Σ' δplus : ∀ n, Xplus n ⟶ Xplus (n + 1),
        ∀ n,
          (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
            (eplus (n + 1)).inv = (Q).map (δplus n)) := by
  classical
  let StepBundle (n : ℕ) : Type _ :=
    Σ' Xn : A, Σ' e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n),
      Σ' Xnext : A, Σ' e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (n + 1)),
        Σ' δ_n : Xn ⟶ Xnext,
          (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ e_next.inv = (Q).map δ_n
  obtain ⟨X0, e0⟩ := serre_quotient_nonnegative_base (P := P) K₀
  obtain ⟨X1, e1, δ0, hδ0⟩ := serre_quotient_nonnegative_succ_data (P := P) K₀ 0 X0 e0
  let bundle0 : StepBundle 0 := ⟨X0, e0, X1, e1, δ0, hδ0⟩
  let bundleSucc : ∀ n, StepBundle n → StepBundle (n + 1) := fun n b ↦ by
    let Xnext := b.2.2.1
    let e_next := b.2.2.2.1
    let data :=
      Classical.choice (serre_quotient_nonnegative_succ_data (P := P) K₀ (n + 1) Xnext e_next)
    -- Each successor step reuses the already-built degree `n + 1` term as the new source.
    exact ⟨Xnext, e_next, data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  let bundle : ∀ n, StepBundle n := Nat.rec bundle0 bundleSucc
  let Xplus : ℕ → A
    | 0 => (bundle 0).1
    | n + 1 => (bundle n).2.2.1
  let eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n)
    | 0 => by
        simpa [Xplus] using (bundle 0).2.1
    | n + 1 => by
        simpa [Xplus] using (bundle n).2.2.2.1
  let δplus : ∀ n, Xplus n ⟶ Xplus (n + 1)
    | 0 => by
        simpa [Xplus] using (bundle 0).2.2.2.2.1
    | n + 1 => by
        simpa [Xplus, bundle, bundleSucc] using (bundle (n + 1)).2.2.2.2.1
  refine ⟨⟨Xplus, eplus, δplus, ?_⟩⟩
  intro n
  cases n with
  | zero =>
      -- The base bundle stores the degree-zero differential equation.
      simpa [eplus, δplus, Xplus] using (bundle 0).2.2.2.2.2
  | succ n =>
      -- Bundle `n + 1` stores the equation for the differential from degree `n + 1`.
      simpa [eplus, δplus, Xplus, Nat.succ_eq_add_one] using
        (bundle (n + 1)).2.2.2.2.2

/-- Helper for Lemma 13.17.2: from an arbitrary nonnegative frontier object representing
`K₀.X m`, the positive pushout construction rebuilds the entire right tail of represented
differentials. -/
lemma serre_quotient_nonnegative_tail_from
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (m : ℕ) (Xm : A)
    (em : (Q).obj Xm ≅ K₀.X (Int.ofNat m)) :
    Nonempty (Σ' Xtail : ℕ → A, Σ' etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.ofNat (m + r)),
      Σ' δtail : ∀ r, Xtail r ⟶ Xtail (r + 1),
        Xtail 0 = Xm ∧
        ∀ r,
          (etail r).hom ≫ K₀.d (Int.ofNat (m + r)) (Int.ofNat (m + r + 1)) ≫
            (etail (r + 1)).inv = (Q).map (δtail r)) := by
  classical
  let StepBundle (r : ℕ) : Type _ :=
    Σ' Xr : A, Σ' e_r : (Q).obj Xr ≅ K₀.X (Int.ofNat (m + r)),
      Σ' Xnext : A, Σ' e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (m + r + 1)),
        Σ' δ_r : Xr ⟶ Xnext,
          (e_r).hom ≫ K₀.d (Int.ofNat (m + r)) (Int.ofNat (m + r + 1)) ≫
            e_next.inv = (Q).map δ_r
  obtain ⟨X1, e1, δ0, hδ0⟩ := serre_quotient_nonnegative_succ_data (P := P) K₀ m Xm em
  let bundle0 : StepBundle 0 := by
    -- The initial bundle records the given frontier and the first pushout step out of it.
    refine ⟨Xm, ?_, X1, ?_, δ0, ?_⟩
    · simpa using em
    · simpa using e1
    · simpa [Nat.add_zero] using hδ0
  let bundleSucc : ∀ r, StepBundle r → StepBundle (r + 1) := fun r b ↦ by
    let Xnext := b.2.2.1
    let e_next := b.2.2.2.1
    let data :=
      Classical.choice
        (serre_quotient_nonnegative_succ_data (P := P) K₀ (m + (r + 1)) Xnext e_next)
    -- Each successor step forgets the already-used source and extends the tail one degree further.
    refine ⟨Xnext, ?_, data.1, ?_, data.2.2.1, ?_⟩
    · simpa [Nat.add_assoc] using e_next
    · simpa [Nat.add_assoc] using data.2.1
    · simpa [Nat.add_assoc] using data.2.2.2
  let bundle : ∀ r, StepBundle r := Nat.rec bundle0 bundleSucc
  let Xtail : ℕ → A
    | 0 => (bundle 0).1
    | r + 1 => (bundle r).2.2.1
  let etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.ofNat (m + r))
    | 0 => by
        simpa [Xtail] using (bundle 0).2.1
    | r + 1 => by
        simpa [Xtail] using (bundle r).2.2.2.1
  let δtail : ∀ r, Xtail r ⟶ Xtail (r + 1)
    | 0 => by
        simpa [Xtail] using (bundle 0).2.2.2.2.1
    | r + 1 => by
        simpa [Xtail, bundle, bundleSucc] using (bundle (r + 1)).2.2.2.2.1
  refine ⟨⟨Xtail, etail, δtail, ?_⟩⟩
  constructor
  · -- The reconstructed tail starts at the prescribed frontier object.
    rfl
  · intro r
    cases r with
    | zero =>
        -- The base bundle stores the represented differential out of the frontier degree.
        simpa [etail, δtail, Xtail] using (bundle 0).2.2.2.2.2
    | succ r =>
        -- Bundle `r + 1` stores the represented differential out of degree `m + (r + 1)`.
        simpa [etail, δtail, Xtail, Nat.succ_eq_add_one, Nat.add_assoc] using
          (bundle (r + 1)).2.2.2.2.2

/-- Helper for Lemma 13.17.2: if the source of a morphism is zero, then its cokernel projection
is an isomorphism. -/
lemma cokernel_pi_isIso_of_isZero_src
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) (hX : IsZero X) :
    IsIso (cokernel.π f) := by
  have hf : f = 0 := hX.eq_of_src f 0
  -- Reduce to the canonical zero-arrow cokernel comparison.
  subst f
  simpa using (cokernel.π_of_zero (X := X) (Y := Y))

/-- Helper for Lemma 13.17.2: if a morphism is zero, then its kernel inclusion is an
isomorphism. -/
lemma kernel_ι_isIso_of_eq_zero
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsIso (kernel.ι f) := by
  -- Reduce to the canonical zero-arrow kernel comparison.
  subst f
  simpa using (kernel.ι_of_zero (X := X) (Y := Y))

/-- Helper for Lemma 13.17.2: a single negative-degree differential in the quotient with upstairs
target can be normalized by a pullback step, dual to the positive pushout step. -/
lemma serre_quotient_negative_step
    {X Z : A} (g : (Q).obj Z ⟶ (Q).obj X) :
    Nonempty (Σ' Y : A, Σ' e : (Q).obj Y ≅ (Q).obj Z, Σ' δ : Y ⟶ X,
      e.hom ≫ g = (Q).map δ) := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction Q P.isoModSerre g
  have hψ' : g ≫ (Q).map ψ.s = (Q).map ψ.f := by
    -- Cross-multiply the left-fraction presentation to obtain the pullback square in the source.
    have h :=
      MorphismProperty.LeftFraction.map_comp_map_s ψ Q
        (Localization.inverts Q P.isoModSerre)
    simpa [hψ] using h
  let Y := pullback ψ.f ψ.s
  let ePull : (Q).obj Y ≅ pullback ((Q).map ψ.f) ((Q).map ψ.s) :=
    PreservesPullback.iso Q ψ.f ψ.s
  haveI : IsIso ((Q).map ψ.s) :=
    Localization.inverts Q P.isoModSerre ψ.s ψ.hs
  haveI : IsIso (pullback.fst ((Q).map ψ.f) ((Q).map ψ.s)) := by infer_instance
  let e : (Q).obj Y ≅ (Q).obj Z :=
    ePull ≪≫ asIso (pullback.fst ((Q).map ψ.f) ((Q).map ψ.s))
  refine ⟨⟨Y, e, pullback.snd ψ.f ψ.s, ?_⟩⟩
  have he_hom :
      e.hom = (Q).map (pullback.fst ψ.f ψ.s) := by
    -- The new vertical isomorphism is the mapped first projection after transporting the pullback.
    dsimp [e]
    calc
      ePull.hom ≫ pullback.fst ((Q).map ψ.f) ((Q).map ψ.s) =
          ePull.hom ≫ pullback.fst ((Q).map ψ.f) ((Q).map ψ.s) := rfl
      _ = (Q).map (pullback.fst ψ.f ψ.s) := by
          rw [PreservesPullback.iso_hom_fst Q ψ.f ψ.s]
  rw [he_hom]
  apply (cancel_mono ((Q).map ψ.s)).1
  calc
    ((Q).map (pullback.fst ψ.f ψ.s) ≫ g) ≫ (Q).map ψ.s =
        (Q).map (pullback.fst ψ.f ψ.s) ≫ (g ≫ (Q).map ψ.s) := by
          simp [Category.assoc]
    _ = (Q).map (pullback.fst ψ.f ψ.s) ≫ (Q).map ψ.f := by
          rw [hψ']
    _ = (Q).map (pullback.fst ψ.f ψ.s ≫ ψ.f) := by
          simp [Functor.map_comp]
    _ = (Q).map (pullback.snd ψ.f ψ.s ≫ ψ.s) := by
          rw [pullback.condition]
    _ = (Q).map (pullback.snd ψ.f ψ.s) ≫ (Q).map ψ.s := by
          simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: once degree `-(n+1)` has an upstairs representative, the previous
negative differential can be normalized by one pullback step and transported back to
`K₀.X (Int.negSucc (n + 1))`. -/
lemma serre_quotient_negative_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.negSucc n)) :
    Nonempty (Σ' Xprev : A, Σ' e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1)),
      Σ' δ_prev : Xprev ⟶ Xn,
        (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ e_n.inv =
          (Q).map δ_prev) := by
  let Z := (Q).objPreimage (K₀.X (Int.negSucc (n + 1)))
  let g : (Q).obj Z ⟶ (Q).obj Xn :=
    ((Q).objObjPreimageIso (K₀.X (Int.negSucc (n + 1)))).hom ≫
      K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ e_n.inv
  obtain ⟨Y, e, δ, hδ⟩ := serre_quotient_negative_step (P := P) g
  let e_prev : (Q).obj Y ≅ K₀.X (Int.negSucc (n + 1)) :=
    e ≪≫ (Q).objObjPreimageIso (K₀.X (Int.negSucc (n + 1)))
  refine ⟨⟨Y, e_prev, δ, ?_⟩⟩
  -- Postcompose the pullback normalization with the canonical preimage isomorphism on the source.
  simpa [g, e_prev, Category.assoc] using hδ

/-- Helper for Lemma 13.17.2: the negative-degree pullback construction can be iterated over all
natural degrees, producing actual upstairs differentials on every `n < 0`. -/
lemma serre_quotient_negative_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (_hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n)) :
    Nonempty (Σ' Xminus : ℕ → A, Σ' eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n),
      Σ' δzero : Xminus 0 ⟶ Xplus 0, Σ' δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n,
        ((eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero) ∧
        (∀ n,
          (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
            (eminus n).inv = (Q).map (δminus n))) := by
  classical
  let Z0 := (Q).objPreimage (K₀.X (Int.negSucc 0))
  let g0 : (Q).obj Z0 ⟶ (Q).obj (Xplus 0) :=
    ((Q).objObjPreimageIso (K₀.X (Int.negSucc 0))).hom ≫ K₀.d (Int.negSucc 0) 0 ≫
      (eplus 0).inv
  obtain ⟨Xminus0, e0raw, δzero, hzero_raw⟩ := serre_quotient_negative_step (P := P) g0
  let eminus0 : (Q).obj Xminus0 ≅ K₀.X (Int.negSucc 0) :=
    e0raw ≪≫ (Q).objObjPreimageIso (K₀.X (Int.negSucc 0))
  have hzero :
      (eminus0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero := by
    -- The base pullback step packages the differential from degree `-1` to degree `0`.
    simpa [g0, eminus0, Category.assoc] using hzero_raw
  let Bundle (n : ℕ) : Type _ :=
    Σ Xn : A, (Q).obj Xn ≅ K₀.X (Int.negSucc n)
  let StepData (n : ℕ) (b : Bundle n) : Type _ :=
    Σ' Xprev : A, Σ' e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1)),
      Σ' δ_prev : Xprev ⟶ b.1,
        (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ b.2.inv = (Q).map δ_prev
  let stepData : ∀ n (b : Bundle n), StepData n b := fun n b ↦ by
    exact Classical.choice (serre_quotient_negative_succ_data (P := P) K₀ n b.1 b.2)
  let bundle0 : Bundle 0 := ⟨Xminus0, eminus0⟩
  let bundleSucc : ∀ n, Bundle n → Bundle (n + 1) := fun n b ↦
    ⟨(stepData n b).1, (stepData n b).2.1⟩
  let bundle : ∀ n, Bundle n := Nat.rec bundle0 bundleSucc
  let Xminus : ℕ → A := fun n ↦ (bundle n).1
  let eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n) := fun n ↦ (bundle n).2
  let δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n := fun n ↦ by
    -- Each recursive step produces the next negative differential into the previously built term.
    simpa [Xminus, bundle, bundleSucc] using (stepData n (bundle n)).2.2.1
  refine ⟨⟨Xminus, eminus, δzero, δminus, ?_⟩⟩
  constructor
  · -- The base step is exactly the degree `-1` differential representation.
    simpa [Xminus, eminus] using hzero
  · intro n
    -- The recursive bundle stores the represented differential from degree `-(n + 2)` to
    -- degree `-(n + 1)`.
    simpa [Xminus, eminus, δminus, bundle, bundleSucc] using (stepData n (bundle n)).2.2.2

/-- Helper for Lemma 13.17.2: from an arbitrary negative frontier object representing
`K₀.X (Int.negSucc m)`, the negative pullback construction rebuilds the entire left tail of
represented differentials. -/
lemma serre_quotient_negative_tail_from
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (m : ℕ) (Xm : A)
    (em : (Q).obj Xm ≅ K₀.X (Int.negSucc m)) :
    Nonempty (Σ' Xtail : ℕ → A, Σ' etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.negSucc (m + r)),
      Σ' δtail : ∀ r, Xtail (r + 1) ⟶ Xtail r,
        Xtail 0 = Xm ∧
        ∀ r,
          (etail (r + 1)).hom ≫
              K₀.d (Int.negSucc (m + (r + 1))) (Int.negSucc (m + r)) ≫
                (etail r).inv =
            (Q).map (δtail r)) := by
  classical
  let Bundle (r : ℕ) : Type _ :=
    Σ Xr : A, (Q).obj Xr ≅ K₀.X (Int.negSucc (m + r))
  let StepData (r : ℕ) (b : Bundle r) : Type _ :=
    Σ' Xprev : A, Σ' e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (m + (r + 1))),
      Σ' δ_prev : Xprev ⟶ b.1,
        (e_prev).hom ≫
            K₀.d (Int.negSucc (m + (r + 1))) (Int.negSucc (m + r)) ≫
              b.2.inv =
          (Q).map δ_prev
  let stepData : ∀ r (b : Bundle r), StepData r b := fun r b ↦ by
    let data :=
      Classical.choice (serre_quotient_negative_succ_data (P := P) K₀ (m + r) b.1 b.2)
    -- One pullback step extends the reconstructed tail one degree further to the left.
    refine ⟨data.1, ?_, data.2.2.1, ?_⟩
    · simpa [Nat.add_assoc] using data.2.1
    · simpa [Nat.add_assoc] using data.2.2.2
  let bundle0 : Bundle 0 := by
    -- The tail starts from the prescribed frontier object.
    refine ⟨Xm, ?_⟩
    simpa using em
  let bundleSucc : ∀ r, Bundle r → Bundle (r + 1) := fun r b ↦
    ⟨(stepData r b).1, (stepData r b).2.1⟩
  let bundle : ∀ r, Bundle r := Nat.rec bundle0 bundleSucc
  let Xtail : ℕ → A := fun r ↦ (bundle r).1
  let etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.negSucc (m + r)) := fun r ↦ (bundle r).2
  let δtail : ∀ r, Xtail (r + 1) ⟶ Xtail r := fun r ↦ by
    -- Each recursive step contributes the differential from the new left term into the old one.
    simpa [Xtail, bundle, bundleSucc] using (stepData r (bundle r)).2.2.1
  refine ⟨⟨Xtail, etail, δtail, ?_⟩⟩
  constructor
  · -- The reconstructed left tail begins at the given frontier.
    rfl
  · intro r
    -- Step `r` stores the represented differential from degree `-(m + r + 2)` into
    -- degree `-(m + r + 1)`.
    simpa [Xtail, etail, δtail, bundle, bundleSucc, Nat.succ_eq_add_one, Nat.add_assoc] using
      (stepData r (bundle r)).2.2.2

/-- Helper for Lemma 13.17.2: splice the positive and negative recursive packages into a single
`ℤ`-indexed family of upstairs objects and represented differentials. -/
lemma serre_quotient_spliced_degreewise_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n))
    (Xminus : ℕ → A)
    (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
    (δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (hzero :
      (eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero)
    (hminus : ∀ n,
      (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
        (eminus n).inv = (Q).map (δminus n)) :
    Nonempty (Σ' X : ℤ → A, Σ' e : ∀ i, (Q).obj (X i) ≅ K₀.X i, Σ' δ : ∀ i, X i ⟶ X (i + 1),
      ∀ i,
        (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i)) := by
  let X : ℤ → A
    | Int.ofNat n => Xplus n
    | Int.negSucc n => Xminus n
  let e : ∀ i, (Q).obj (X i) ≅ K₀.X i
    | Int.ofNat n => by
        simpa [X] using eplus n
    | Int.negSucc n => by
        simpa [X] using eminus n
  let δ : ∀ i, X i ⟶ X (i + 1)
    | Int.ofNat n => by
        simpa [X] using δplus n
    | Int.negSucc 0 => by
        simpa [X] using δzero
    | Int.negSucc (n + 1) => by
        simpa [X] using δminus n
  refine ⟨⟨X, e, δ, ?_⟩⟩
  intro i
  cases i with
  | ofNat n =>
      -- The nonnegative branch is exactly the positive pushout package.
      simpa [X, e, δ] using hplus n
  | negSucc n =>
      cases n with
      | zero =>
          -- Degree `-1` is the splice between the negative and nonnegative branches.
          simpa [X, e, δ] using hzero
      | succ n =>
          -- Lower negative degrees are exactly the recursive pullback package.
          simpa [X, e, δ, Nat.succ_eq_add_one] using hminus n

/-- Helper for Lemma 13.17.2: quotienting by the image of a zero composite kills that composite,
and the quotient map becomes an isomorphism after applying `Q`. -/
lemma serre_quotient_positive_square_zero_step
    {X₀ X₁ X₂ : A} (u : X₀ ⟶ X₁) (v : X₁ ⟶ X₂)
    (hzero : (Q).map (u ≫ v) = 0) :
    (u ≫ v) ≫ cokernel.π (Abelian.image.ι (u ≫ v)) = 0 ∧
      IsIso ((Q).map (cokernel.π (Abelian.image.ι (u ≫ v)))) := by
  let α : X₀ ⟶ X₂ := u ≫ v
  let q : X₂ ⟶ cokernel (Abelian.image.ι α) := cokernel.π (Abelian.image.ι α)
  have hq_zero : α ≫ q = 0 := by
    -- The quotient map kills the image inclusion, hence also the original composite.
    calc
      α ≫ q = Abelian.factorThruImage α ≫ (Abelian.image.ι α ≫ q) := by
        rw [← Category.assoc, Abelian.image.fac]
      _ = 0 := by
        simp [q]
  have hQimage_ι : (Q).map (Abelian.image.ι α) = 0 := by
    -- The mapped image inclusion is zero because its composite with the mapped epi
    -- `factorThruImage α` is the already-vanishing mapped composite.
    have hQα : (Q).map α = 0 := by
      simpa [α] using hzero
    apply zero_of_epi_comp ((Q).map (Abelian.factorThruImage α))
    rw [← Functor.map_comp, Abelian.image.fac]
    exact hQα
  have hQimage_zero : IsZero ((Q).obj (Abelian.image α)) :=
    IsZero.of_mono_eq_zero ((Q).map (Abelian.image.ι α)) hQimage_ι
  have hQq_iso :
      IsIso (cokernel.π ((Q).map (Abelian.image.ι α))) :=
    cokernel_pi_isIso_of_isZero_src ((Q).map (Abelian.image.ι α)) hQimage_zero
  let eCoker :
      (Q).obj (cokernel (Abelian.image.ι α)) ≅
        cokernel ((Q).map (Abelian.image.ι α)) :=
    PreservesCokernel.iso (Q) (Abelian.image.ι α)
  have hmap_q :
      (Q).map q ≫ eCoker.hom = cokernel.π ((Q).map (Abelian.image.ι α)) := by
    -- This is the canonical comparison between the mapped cokernel projection and the cokernel
    -- projection of the mapped arrow.
    have h := PreservesCokernel.π_iso_hom (G := Q) (f := Abelian.image.ι α)
    simpa [q, eCoker] using h
  have hmap_q' :
      (Q).map q = cokernel.π ((Q).map (Abelian.image.ι α)) ≫ eCoker.inv := by
    calc
      (Q).map q = ((Q).map q ≫ eCoker.hom) ≫ eCoker.inv := by
        simp [Category.assoc]
      _ = cokernel.π ((Q).map (Abelian.image.ι α)) ≫ eCoker.inv := by
        rw [hmap_q]
  constructor
  · simpa [α, q, Category.assoc] using hq_zero
  · rw [hmap_q']
    infer_instance

/-- Helper for Lemma 13.17.2: replacing the source by the kernel of a zero composite kills that
composite, and the kernel inclusion becomes an isomorphism after applying `Q`. -/
lemma serre_quotient_negative_square_zero_step
    {X₀ X₁ X₂ : A} (u : X₀ ⟶ X₁) (v : X₁ ⟶ X₂)
    (hzero : (Q).map (u ≫ v) = 0) :
    (kernel.ι (u ≫ v) ≫ u) ≫ v = 0 ∧
      IsIso ((Q).map (kernel.ι (u ≫ v))) := by
  let α : X₀ ⟶ X₂ := u ≫ v
  have hkernel_zero : (kernel.ι α ≫ u) ≫ v = 0 := by
    -- The kernel inclusion annihilates the offending double composite by definition.
    have h := kernel.condition α
    simpa [α, Category.assoc] using h
  let eKernel : (Q).obj (kernel α) ≅ kernel ((Q).map α) :=
    PreservesKernel.iso (Q) α
  have hQkernel_zero :
      IsIso (kernel.ι ((Q).map α)) := by
    -- After applying `Q`, the composite itself is literally zero, so the kernel inclusion is an iso.
    simpa [hzero] using
      (kernel_ι_isIso_of_eq_zero ((Q).map α) hzero)
  have hmap_kernel :
      (Q).map (kernel.ι α) = eKernel.hom ≫ kernel.ι ((Q).map α) := by
    -- Rewrite the mapped kernel inclusion through the canonical preservation isomorphism.
    calc
      (Q).map (kernel.ι α) = 𝟙 _ ≫ (Q).map (kernel.ι α) := by simp
      _ = eKernel.hom ≫ (eKernel.inv ≫ (Q).map (kernel.ι α)) := by
            simp
      _ = eKernel.hom ≫ kernel.ι ((Q).map α) := by
            rw [PreservesKernel.iso_inv_ι Q α]
  constructor
  · have h := hkernel_zero
    simpa [α] using h
  · rw [hmap_kernel]
    letI : IsIso (kernel.ι ((Q).map α)) := hQkernel_zero
    infer_instance

/-- Helper for Lemma 13.17.2: any degreewise presentation of a quotient complex sends each
represented double composite to zero after applying `Q`. -/
lemma serre_quotient_adjacent_represented_composite_map_zero
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    {i j k : ℤ} {Xi Xj Xk : A}
    (ei : (Q).obj Xi ≅ K₀.X i)
    (ej : (Q).obj Xj ≅ K₀.X j)
    (ek : (Q).obj Xk ≅ K₀.X k)
    (u : Xi ⟶ Xj)
    (v : Xj ⟶ Xk)
    (hu : ei.hom ≫ K₀.d i j ≫ ej.inv = (Q).map u)
    (hv : ej.hom ≫ K₀.d j k ≫ ek.inv = (Q).map v)
    (hd : K₀.d i j ≫ K₀.d j k = 0) :
    (Q).map (u ≫ v) = 0 := by
  -- Transport the square-zero relation of `K₀` through the chosen degreewise presentations.
  calc
    (Q).map (u ≫ v) = (Q).map u ≫ (Q).map v := by
      simp [Functor.map_comp]
    _ = (ei.hom ≫ K₀.d i j ≫ ej.inv) ≫ (ej.hom ≫ K₀.d j k ≫ ek.inv) := by
      rw [hu, hv]
    _ = ei.hom ≫ (K₀.d i j ≫ K₀.d j k) ≫ ek.inv := by
      simp [Category.assoc]
    _ = 0 := by
      rw [hd]
      simp

/-- Helper for Lemma 13.17.2: any degreewise presentation of a quotient complex sends each
represented double composite to zero after applying `Q`. -/
lemma serre_quotient_represented_double_composite_map_zero
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i)) :
    ∀ i, (Q).map (δ i ≫ δ (i + 1)) = 0 := by
  intro i
  exact serre_quotient_adjacent_represented_composite_map_zero
    (P := P) K₀ (e i) (e (i + 1)) (e (i + 1 + 1)) (δ i) (δ (i + 1))
    (hδ i) (hδ (i + 1)) (K₀.d_comp_d i (i + 1) (i + 1 + 1))

/-- Helper for Lemma 13.17.2: a represented bad double composite admits the local quotient repair
used in the positive square-zero pass, while preserving the quotient-side presentation of the
next differential. -/
lemma serre_quotient_cokernel_repair_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i))
    (i : ℤ) :
    Nonempty (Σ' Y : A, Σ' q : X (i + 1 + 1) ⟶ Y, Σ' eY : (Q).obj Y ≅ K₀.X (i + 1 + 1),
      δ i ≫ δ (i + 1) ≫ q = 0 ∧
      IsIso ((Q).map q) ∧
      (e (i + 1)).hom ≫ K₀.d (i + 1) (i + 1 + 1) ≫ eY.inv =
        (Q).map (δ (i + 1) ≫ q)) := by
  have hmapzero :
      (Q).map (δ i ≫ δ (i + 1)) = 0 :=
    serre_quotient_represented_double_composite_map_zero
      (P := P) K₀ X e δ hδ i
  let q : X (i + 1 + 1) ⟶ cokernel (Abelian.image.ι (δ i ≫ δ (i + 1))) :=
    cokernel.π (Abelian.image.ι (δ i ≫ δ (i + 1)))
  obtain ⟨hkill, hqiso⟩ :=
    serre_quotient_positive_square_zero_step (P := P) (u := δ i) (v := δ (i + 1)) hmapzero
  let eY : (Q).obj (cokernel (Abelian.image.ι (δ i ≫ δ (i + 1)))) ≅ K₀.X (i + 1 + 1) :=
    (asIso ((Q).map q)).symm ≪≫ e (i + 1 + 1)
  have heY_inv :
      eY.inv = (e (i + 1 + 1)).inv ≫ (Q).map q := by
    -- The new comparison iso is the old one followed by the mapped quotient arrow.
    simp [eY, q]
  refine ⟨⟨_, q, eY, ?_, hqiso, ?_⟩⟩
  · -- The quotient by the image kills the offending double composite upstairs.
    simpa [q, Category.assoc] using hkill
  · -- Postcompose the old represented differential by the new quotient map on degree `i + 2`.
    calc
      (e (i + 1)).hom ≫ K₀.d (i + 1) (i + 1 + 1) ≫ eY.inv =
          ((e (i + 1)).hom ≫ K₀.d (i + 1) (i + 1 + 1) ≫ (e (i + 1 + 1)).inv) ≫
            (Q).map q := by
        rw [heY_inv]
        simp [Category.assoc]
      _ = (Q).map (δ (i + 1)) ≫ (Q).map q := by
        rw [hδ (i + 1)]
      _ = (Q).map (δ (i + 1) ≫ q) := by
        simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: a represented bad double composite admits the local kernel repair
used in the negative square-zero pass, while preserving the quotient-side presentation of the
current differential. -/
lemma serre_quotient_kernel_repair_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i))
    (i : ℤ) :
    Nonempty (Σ' Y : A, Σ' ι : Y ⟶ X i, Σ' eY : (Q).obj Y ≅ K₀.X i,
      (ι ≫ δ i) ≫ δ (i + 1) = 0 ∧
      IsIso ((Q).map ι) ∧
      (eY).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv =
        (Q).map (ι ≫ δ i)) := by
  have hmapzero :
      (Q).map (δ i ≫ δ (i + 1)) = 0 :=
    serre_quotient_represented_double_composite_map_zero
      (P := P) K₀ X e δ hδ i
  let ι : kernel (δ i ≫ δ (i + 1)) ⟶ X i :=
    kernel.ι (δ i ≫ δ (i + 1))
  obtain ⟨hkill, hιiso⟩ :=
    serre_quotient_negative_square_zero_step (P := P) (u := δ i) (v := δ (i + 1)) hmapzero
  let eY : (Q).obj (kernel (δ i ≫ δ (i + 1))) ≅ K₀.X i :=
    asIso ((Q).map ι) ≪≫ e i
  have heY_hom :
      eY.hom = (Q).map ι ≫ (e i).hom := by
    -- The new comparison iso is the mapped kernel inclusion followed by the old comparison iso.
    simp [eY, ι]
  refine ⟨⟨_, ι, eY, ?_, hιiso, ?_⟩⟩
  · -- The kernel inclusion annihilates the offending double composite upstairs.
    have h := hkill
    simpa [ι, Category.assoc] using h
  · -- Precompose the old represented differential by the new kernel inclusion on degree `i`.
    calc
      (eY).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv =
          (Q).map ι ≫ ((e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv) := by
        rw [heY_hom]
        simp [Category.assoc]
      _ = (Q).map ι ≫ (Q).map (δ i) := by
        rw [hδ i]
      _ = (Q).map (ι ≫ δ i) := by
        simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: specialize the local cokernel repair engine to a nonnegative index,
so later stage-recursion code can stay on the `ℕ` side and avoid repeated `Int.ofNat` transport
bookkeeping. -/
lemma serre_quotient_cokernel_repair_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i))
    (n : ℕ) :
    Nonempty (Σ' Y : A, Σ' q : X (Int.ofNat (n + 2)) ⟶ Y, Σ' eY : (Q).obj Y ≅ K₀.X (Int.ofNat (n + 2)),
      δ (Int.ofNat n) ≫ δ (Int.ofNat (n + 1)) ≫ q = 0 ∧
      IsIso ((Q).map q) ∧
      (e (Int.ofNat (n + 1))).hom ≫ K₀.d (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) ≫ eY.inv =
        (Q).map (δ (Int.ofNat (n + 1)) ≫ q)) := by
  simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
    serre_quotient_cokernel_repair_data (P := P) K₀ X e δ hδ (Int.ofNat n)

/-- Helper for Lemma 13.17.2: specialize the local kernel repair engine to a negative index, so
later stage-recursion code can stay on the `Int.negSucc` side and avoid repeated index
normalization. -/
lemma serre_quotient_kernel_repair_data_negSucc
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i))
    (n : ℕ) :
    Nonempty (Σ' Y : A, Σ' ι : Y ⟶ X (Int.negSucc n), Σ' eY : (Q).obj Y ≅ K₀.X (Int.negSucc n),
      (ι ≫ δ (Int.negSucc n)) ≫ δ (Int.negSucc n + 1) = 0 ∧
      IsIso ((Q).map ι) ∧
      (eY).hom ≫ K₀.d (Int.negSucc n) (Int.negSucc n + 1) ≫ (e (Int.negSucc n + 1)).inv =
        (Q).map (ι ≫ δ (Int.negSucc n))) := by
  simpa using
    serre_quotient_kernel_repair_data (P := P) K₀ X e δ hδ (Int.negSucc n)

/-- Helper for Lemma 13.17.2: from one represented nonnegative differential, build the next
nonnegative differential and repair its target so the adjacent composite vanishes upstairs. -/
lemma serre_quotient_nonnegative_square_zero_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn Xn1 : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n))
    (e_n1 : (Q).obj Xn1 ≅ K₀.X (Int.ofNat (n + 1)))
    (δ_n : Xn ⟶ Xn1)
    (hδ_n :
      (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ (e_n1).inv = (Q).map δ_n) :
    Nonempty (Σ' Xn2 : A, Σ' e_n2 : (Q).obj Xn2 ≅ K₀.X (Int.ofNat (n + 2)),
      Σ' δ_n1 : Xn1 ⟶ Xn2,
        δ_n ≫ δ_n1 = 0 ∧
        (e_n1).hom ≫ K₀.d (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) ≫ (e_n2).inv =
          (Q).map δ_n1) := by
  obtain ⟨Xraw, e_raw, δ_raw, hδ_raw⟩ :=
    serre_quotient_nonnegative_succ_data (P := P) K₀ (n + 1) Xn1 e_n1
  have hmapzero : (Q).map (δ_n ≫ δ_raw) = 0 := by
    -- The represented adjacent quotient differentials compose to zero because `K₀` is a complex.
    exact serre_quotient_adjacent_represented_composite_map_zero
      (P := P) K₀ e_n e_n1 e_raw δ_n δ_raw hδ_n hδ_raw
      (K₀.d_comp_d (Int.ofNat n) (Int.ofNat (n + 1)) (Int.ofNat (n + 2)))
  let q : Xraw ⟶ cokernel (Abelian.image.ι (δ_n ≫ δ_raw)) :=
    cokernel.π (Abelian.image.ι (δ_n ≫ δ_raw))
  obtain ⟨hkill, hqiso⟩ :=
    serre_quotient_positive_square_zero_step (P := P) (u := δ_n) (v := δ_raw) hmapzero
  let e_n2 : (Q).obj (cokernel (Abelian.image.ι (δ_n ≫ δ_raw))) ≅ K₀.X (Int.ofNat (n + 2)) :=
    (asIso ((Q).map q)).symm ≪≫ e_raw
  have he_n2_inv :
      e_n2.inv = e_raw.inv ≫ (Q).map q := by
    -- The repaired comparison iso is the old target identification followed by the mapped quotient.
    change e_raw.inv ≫ (Q).map q = e_raw.inv ≫ (Q).map q
    rfl
  refine ⟨⟨_, e_n2, δ_raw ≫ q, ?_, ?_⟩⟩
  · -- The quotient kills the offending adjacent composite by construction.
    simpa [q, Category.assoc] using hkill
  · -- The repaired next differential still represents the quotient differential of `K₀`.
    calc
      (e_n1).hom ≫ K₀.d (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) ≫ e_n2.inv =
          ((e_n1).hom ≫ K₀.d (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) ≫ e_raw.inv) ≫
            (Q).map q := by
        rw [he_n2_inv]
        simpa only [Category.assoc]
      _ = (Q).map δ_raw ≫ (Q).map q := by
        rw [hδ_raw]
      _ = (Q).map (δ_raw ≫ q) := by
        simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: a verified two-step window on the nonnegative branch records three
consecutive objects, the represented differentials between them, and the literal square-zero
relation for the first adjacent pair. -/
structure SerreQuotientNonnegativeSquareZeroWindow
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) (n : ℕ) where
  Xn : A
  e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n)
  Xn1 : A
  e_n1 : (Q).obj Xn1 ≅ K₀.X (Int.ofNat (n + 1))
  δ_n : Xn ⟶ Xn1
  hδ_n :
    (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ (e_n1).inv = (Q).map δ_n
  Xn2 : A
  e_n2 : (Q).obj Xn2 ≅ K₀.X (Int.ofNat (n + 2))
  δ_n1 : Xn1 ⟶ Xn2
  hsq_n : δ_n ≫ δ_n1 = 0
  hδ_n1 :
    (e_n1).hom ≫ K₀.d (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) ≫ (e_n2).inv = (Q).map δ_n1

/-- Helper for Lemma 13.17.2: initialize the nonnegative square-zero recursion with the verified
window in degrees `0`, `1`, and `2`. -/
noncomputable def serre_quotient_nonnegative_square_zero_window_zero
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    SerreQuotientNonnegativeSquareZeroWindow (P := P) K₀ 0 :=
  let data0 := Classical.choice (serre_quotient_nonnegative_base (P := P) K₀)
  let data1 :=
    Classical.choice
      (serre_quotient_nonnegative_succ_data (P := P) K₀ 0 data0.1 data0.2)
  let data2 :=
    Classical.choice
      (serre_quotient_nonnegative_square_zero_succ_data (P := P) K₀ 0
        data0.1 data1.1 data0.2 data1.2.1 data1.2.2.1 data1.2.2.2)
  { Xn := data0.1
    e_n := data0.2
    Xn1 := data1.1
    e_n1 := data1.2.1
    δ_n := data1.2.2.1
    hδ_n := data1.2.2.2
    Xn2 := data2.1
    e_n2 := data2.2.1
    δ_n1 := data2.2.2.1
    hsq_n := data2.2.2.2.1
    hδ_n1 := data2.2.2.2.2 }

/-- Helper for Lemma 13.17.2: shift a verified nonnegative square-zero window one degree to the
right by repairing the next represented differential. -/
noncomputable def serre_quotient_nonnegative_square_zero_window_succ
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) (n : ℕ)
    (w : SerreQuotientNonnegativeSquareZeroWindow (P := P) K₀ n) :
    SerreQuotientNonnegativeSquareZeroWindow (P := P) K₀ (n + 1) :=
  let data :=
    Classical.choice
      (serre_quotient_nonnegative_square_zero_succ_data (P := P) K₀ (n + 1)
        w.Xn1 w.Xn2 w.e_n1 w.e_n2 w.δ_n1 w.hδ_n1)
  { Xn := w.Xn1
    e_n := by simpa [Nat.succ_eq_add_one] using w.e_n1
    Xn1 := w.Xn2
    e_n1 := by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using w.e_n2
    δ_n := w.δ_n1
    hδ_n := by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using w.hδ_n1
    Xn2 := data.1
    e_n2 := data.2.1
    δ_n1 := data.2.2.1
    hsq_n := data.2.2.2.1
    hδ_n1 := data.2.2.2.2 }

/-- Helper for Lemma 13.17.2: recursively repair the nonnegative branch so every adjacent pair of
upstairs differentials has literal zero composite. -/
lemma serre_quotient_nonnegative_square_zero_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    Nonempty (Σ' Xplus : ℕ → A, Σ' eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n),
      Σ' δplus : ∀ n, Xplus n ⟶ Xplus (n + 1),
        (∀ n,
          (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
            (eplus (n + 1)).inv = (Q).map (δplus n)) ∧
        ∀ n, δplus n ≫ δplus (n + 1) = 0) := by
  classical
  let window : ∀ n, SerreQuotientNonnegativeSquareZeroWindow (P := P) K₀ n :=
    Nat.rec
      (serre_quotient_nonnegative_square_zero_window_zero (P := P) K₀)
      (serre_quotient_nonnegative_square_zero_window_succ (P := P) K₀)
  let Xplus : ℕ → A := fun n ↦ (window n).Xn
  let eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n) := fun n ↦ (window n).e_n
  let δplus : ∀ n, Xplus n ⟶ Xplus (n + 1)
    | n => by
        simpa [Xplus] using (window n).δ_n
  refine ⟨⟨Xplus, eplus, δplus, ?_⟩⟩
  constructor
  · intro n
    -- Bundle `n` also stores the represented quotient differential in degree `n`.
    simpa [eplus, δplus, Xplus] using (window n).hδ_n
  · intro n
    -- The repaired two-arrow window records the literal square-zero relation at degree `n`.
    simpa [δplus, Xplus] using (window n).hsq_n

/-- Helper for Lemma 13.17.2: from a represented differential on the negative side, build the
preceding negative differential and repair its source so the adjacent composite vanishes upstairs.
-/
lemma serre_quotient_negative_square_zero_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn Xright : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.negSucc n))
    (e_right : (Q).obj Xright ≅ K₀.X (Int.negSucc n + 1))
    (δ_right : Xn ⟶ Xright)
    (hδ_right :
      (e_n).hom ≫ K₀.d (Int.negSucc n) (Int.negSucc n + 1) ≫ (e_right).inv =
        (Q).map δ_right) :
    Nonempty (Σ' Xprev : A, Σ' e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1)),
      Σ' δ_prev : Xprev ⟶ Xn,
        δ_prev ≫ δ_right = 0 ∧
        (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ (e_n).inv =
          (Q).map δ_prev) := by
  obtain ⟨Xraw, e_raw, δ_raw, hδ_raw⟩ :=
    serre_quotient_negative_succ_data (P := P) K₀ n Xn e_n
  have hmapzero : (Q).map (δ_raw ≫ δ_right) = 0 := by
    -- The represented adjacent quotient differentials compose to zero because `K₀` is a complex.
    exact serre_quotient_adjacent_represented_composite_map_zero
      (P := P) K₀ e_raw e_n e_right δ_raw δ_right hδ_raw hδ_right
      (K₀.d_comp_d (Int.negSucc (n + 1)) (Int.negSucc n) (Int.negSucc n + 1))
  let ι : kernel (δ_raw ≫ δ_right) ⟶ Xraw :=
    kernel.ι (δ_raw ≫ δ_right)
  obtain ⟨hkill, hιiso⟩ :=
    serre_quotient_negative_square_zero_step (P := P) (u := δ_raw) (v := δ_right) hmapzero
  let e_prev : (Q).obj (kernel (δ_raw ≫ δ_right)) ≅ K₀.X (Int.negSucc (n + 1)) :=
    asIso ((Q).map ι) ≪≫ e_raw
  have he_prev_hom :
      e_prev.hom = (Q).map ι ≫ e_raw.hom := by
    -- The repaired comparison iso is the mapped kernel inclusion followed by the old source iso.
    change (Q).map ι ≫ e_raw.hom = (Q).map ι ≫ e_raw.hom
    rfl
  refine ⟨⟨_, e_prev, ι ≫ δ_raw, ?_, ?_⟩⟩
  · -- The kernel repair kills the offending adjacent composite by construction.
    simpa [ι, Category.assoc] using hkill
  · -- The repaired predecessor still represents the quotient differential of `K₀`.
    calc
      e_prev.hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ e_n.inv =
          (Q).map ι ≫ ((e_raw).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ (e_n).inv) := by
        rw [he_prev_hom]
        simp [Category.assoc]
      _ = (Q).map ι ≫ (Q).map δ_raw := by
        rw [hδ_raw]
      _ = (Q).map (ι ≫ δ_raw) := by
        simp [Functor.map_comp]

/-- Helper for Lemma 13.17.2: a verified two-step window on the negative branch records the
current degree, the adjacent degree to its right, and the repaired predecessor degree together
with the represented differentials and square-zero relation between them. -/
structure SerreQuotientNegativeSquareZeroWindow
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) (n : ℕ) where
  Xn : A
  e_n : (Q).obj Xn ≅ K₀.X (Int.negSucc n)
  Xright : A
  e_right : (Q).obj Xright ≅ K₀.X (Int.negSucc n + 1)
  δ_right : Xn ⟶ Xright
  hδ_right :
    (e_n).hom ≫ K₀.d (Int.negSucc n) (Int.negSucc n + 1) ≫ (e_right).inv = (Q).map δ_right
  Xprev : A
  e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1))
  δ_prev : Xprev ⟶ Xn
  hsq_n : δ_prev ≫ δ_right = 0
  hδ_prev :
    (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ (e_n).inv = (Q).map δ_prev

/-- Helper for Lemma 13.17.2: initialize the negative square-zero recursion with the repaired
window in degrees `-2`, `-1`, and `0`. -/
noncomputable def serre_quotient_negative_square_zero_window_zero
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n)) :
    SerreQuotientNegativeSquareZeroWindow (P := P) K₀ 0 :=
  let Z0 := (Q).objPreimage (K₀.X (Int.negSucc 0))
  let g0 : (Q).obj Z0 ⟶ (Q).obj (Xplus 0) :=
    ((Q).objObjPreimageIso (K₀.X (Int.negSucc 0))).hom ≫
      K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv
  let data0 := Classical.choice (serre_quotient_negative_step (P := P) g0)
  let eminus0raw : (Q).obj data0.1 ≅ K₀.X (Int.negSucc 0) :=
    data0.2.1 ≪≫ (Q).objObjPreimageIso (K₀.X (Int.negSucc 0))
  have hzeroRaw' :
      (eminus0raw).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map data0.2.2.1 := by
    -- The raw pullback step represents the degree `-1 -> 0` differential.
    simpa [g0, eminus0raw, Category.assoc] using data0.2.2.2
  have hmapzero0 : (Q).map (data0.2.2.1 ≫ δplus 0) = 0 := by
    -- The raw degree `-1 -> 0` differential composes to zero with the repaired degree `0 -> 1`.
    exact serre_quotient_adjacent_represented_composite_map_zero
      (P := P) K₀ eminus0raw (eplus 0) (eplus 1) data0.2.2.1 (δplus 0)
      hzeroRaw' (hplus 0) (K₀.d_comp_d (Int.negSucc 0) 0 1)
  let ι0 : kernel (data0.2.2.1 ≫ δplus 0) ⟶ data0.1 := kernel.ι (data0.2.2.1 ≫ δplus 0)
  let killData :=
    serre_quotient_negative_square_zero_step (P := P) (u := data0.2.2.1) (v := δplus 0) hmapzero0
  let hkill0 := killData.1
  let hι0iso := killData.2
  letI : IsIso ((Q).map ι0) := hι0iso
  let eminus0 : (Q).obj (kernel (data0.2.2.1 ≫ δplus 0)) ≅ K₀.X (Int.negSucc 0) :=
    asIso ((Q).map ι0) ≪≫ eminus0raw
  let δzero : kernel (data0.2.2.1 ≫ δplus 0) ⟶ Xplus 0 := ι0 ≫ data0.2.2.1
  have heminus0_hom :
      eminus0.hom = (Q).map ι0 ≫ eminus0raw.hom := by
    -- The repaired degree `-1` comparison iso is the mapped kernel inclusion followed by the raw one.
    simp [eminus0, ι0]
  have hzero :
      (eminus0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero := by
    -- The kernel repair preserves the represented quotient differential in degree `-1`.
    calc
      (eminus0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv =
          (Q).map ι0 ≫ (eminus0raw.hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv) := by
        rw [heminus0_hom]
        simp [Category.assoc]
      _ = (Q).map ι0 ≫ (Q).map data0.2.2.1 := by
        rw [hzeroRaw']
      _ = (Q).map δzero := by
        simp [δzero, Functor.map_comp]
  have hsqzero : δzero ≫ δplus 0 = 0 := by
    -- The repaired degree `-1 -> 0` differential now composes trivially with degree `0 -> 1`.
    simpa [δzero, ι0, Category.assoc] using hkill0
  let data1 :=
    Classical.choice
      (serre_quotient_negative_square_zero_succ_data (P := P) K₀ 0
        (kernel (data0.2.2.1 ≫ δplus 0)) (Xplus 0) eminus0 (eplus 0) δzero hzero)
  let window0 : SerreQuotientNegativeSquareZeroWindow (P := P) K₀ 0 :=
    { Xn := kernel (data0.2.2.1 ≫ δplus 0)
      e_n := eminus0
      Xright := Xplus 0
      e_right := eplus 0
      δ_right := δzero
      hδ_right := hzero
      Xprev := data1.1
      e_prev := data1.2.1
      δ_prev := data1.2.2.1
      hsq_n := data1.2.2.2.1
      hδ_prev := data1.2.2.2.2 }
  window0

/-- Helper for Lemma 13.17.2: shift a verified negative square-zero window one degree to the left
by repairing the next predecessor differential. -/
noncomputable def serre_quotient_negative_square_zero_window_succ
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) (n : ℕ)
    (w : SerreQuotientNegativeSquareZeroWindow (P := P) K₀ n) :
    SerreQuotientNegativeSquareZeroWindow (P := P) K₀ (n + 1) :=
  let data :=
    Classical.choice
      (serre_quotient_negative_square_zero_succ_data (P := P) K₀ (n + 1)
        w.Xprev w.Xn w.e_prev w.e_n w.δ_prev w.hδ_prev)
  { Xn := w.Xprev
    e_n := by simpa [Nat.succ_eq_add_one] using w.e_prev
    Xright := w.Xn
    e_right := by simpa [Nat.succ_eq_add_one] using w.e_n
    δ_right := w.δ_prev
    hδ_right := by simpa [Nat.succ_eq_add_one] using w.hδ_prev
    Xprev := data.1
    e_prev := data.2.1
    δ_prev := data.2.2.1
    hsq_n := data.2.2.2.1
    hδ_prev := data.2.2.2.2 }

/-- Helper for Lemma 13.17.2: recursively repair the negative branch so every adjacent pair of
upstairs differentials has literal zero composite. -/
lemma serre_quotient_negative_square_zero_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n))
    (_hsqplus : ∀ n, δplus n ≫ δplus (n + 1) = 0) :
    Nonempty (Σ' Xminus : ℕ → A, Σ' eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n),
      Σ' δzero : Xminus 0 ⟶ Xplus 0, Σ' δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n,
        ((eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero) ∧
        (δzero ≫ δplus 0 = 0) ∧
        (∀ n,
          (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
            (eminus n).inv = (Q).map (δminus n)) ∧
        (δminus 0 ≫ δzero = 0) ∧
        (∀ n, δminus (n + 1) ≫ δminus n = 0)) := by
  classical
  let window0 :=
    serre_quotient_negative_square_zero_window_zero (P := P) K₀ Xplus eplus δplus hplus
  have hsqzero :
      (window0).δ_right ≫ δplus 0 = 0 := by
    let Z0 := (Q).objPreimage (K₀.X (Int.negSucc 0))
    let g0 : (Q).obj Z0 ⟶ (Q).obj (Xplus 0) :=
      ((Q).objObjPreimageIso (K₀.X (Int.negSucc 0))).hom ≫
        K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv
    let data0 := Classical.choice (serre_quotient_negative_step (P := P) g0)
    let eminus0raw : (Q).obj data0.1 ≅ K₀.X (Int.negSucc 0) :=
      data0.2.1 ≪≫ (Q).objObjPreimageIso (K₀.X (Int.negSucc 0))
    have hzeroRaw' :
        (eminus0raw).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map data0.2.2.1 := by
      simpa [g0, eminus0raw, Category.assoc] using data0.2.2.2
    have hmapzero0 : (Q).map (data0.2.2.1 ≫ δplus 0) = 0 := by
      exact serre_quotient_adjacent_represented_composite_map_zero
        (P := P) K₀ eminus0raw (eplus 0) (eplus 1) data0.2.2.1 (δplus 0)
        hzeroRaw' (hplus 0) (K₀.d_comp_d (Int.negSucc 0) 0 1)
    let ι0 : kernel (data0.2.2.1 ≫ δplus 0) ⟶ data0.1 := kernel.ι (data0.2.2.1 ≫ δplus 0)
    let δzero : kernel (data0.2.2.1 ≫ δplus 0) ⟶ Xplus 0 := ι0 ≫ data0.2.2.1
    let killData :=
      serre_quotient_negative_square_zero_step (P := P) (u := data0.2.2.1) (v := δplus 0) hmapzero0
    change δzero ≫ δplus 0 = 0
    simpa [window0, serre_quotient_negative_square_zero_window_zero, Z0, g0, eminus0raw, ι0, δzero, Category.assoc]
      using killData.1
  let window : ∀ n, SerreQuotientNegativeSquareZeroWindow (P := P) K₀ n :=
    Nat.rec
      window0
      (serre_quotient_negative_square_zero_window_succ (P := P) K₀)
  let Xminus : ℕ → A := fun n ↦ (window n).Xn
  let eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n) := fun n ↦ (window n).e_n
  let δzero : Xminus 0 ⟶ Xplus 0 := by
    simpa [Xminus, window] using (window 0).δ_right
  let δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n
    | n => by
        simpa [Xminus] using (window n).δ_prev
  refine ⟨⟨Xminus, eminus, δzero, δminus, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [δzero, Xminus, window] using (window 0).hδ_right
  · -- The repaired degree `-1 -> 0` differential now composes trivially with degree `0 -> 1`.
    simpa [δzero] using hsqzero
  · intro n
    -- Window `n` stores the represented quotient differential from degree `-(n + 2)`.
    simpa [eminus, δminus, Xminus] using (window n).hδ_prev
  ·
    -- The first repaired predecessor kills the splice differential `δzero`.
    simpa [δminus, Xminus, δzero] using (window 0).hsq_n
  · intro n
    -- Window `n + 1` records the next negative square-zero relation.
    simpa [δminus, Xminus, Nat.succ_eq_add_one] using (window (n + 1)).hsq_n

/-- Helper for Chap13 Lemma 13 17 2: the spliced degreewise object family uses the repaired
nonnegative branch on `Int.ofNat` and the repaired negative branch on `Int.negSucc`. -/
def serre_quotient_spliced_object
    (Xplus Xminus : ℕ → A) : ℤ → A
  | Int.ofNat n => Xplus n
  | Int.negSucc n => Xminus n

/-- Helper for Chap13 Lemma 13 17 2: on the nonnegative branch, the splice reuses the given
degreewise identification with `K₀`. -/
def serre_quotient_spliced_iso_ofNat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus Xminus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (_eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
    (n : ℕ) :
    (Q).obj (serre_quotient_spliced_object Xplus Xminus (Int.ofNat n)) ≅ K₀.X (Int.ofNat n) :=
  -- The positive splice branch is definitionally the given nonnegative package.
  eplus n

/-- Helper for Chap13 Lemma 13 17 2: on the negative branch, the splice reuses the given
degreewise identification with `K₀`. -/
def serre_quotient_spliced_iso_negSucc
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus Xminus : ℕ → A)
    (_eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
    (n : ℕ) :
    (Q).obj (serre_quotient_spliced_object Xplus Xminus (Int.negSucc n)) ≅ K₀.X (Int.negSucc n) :=
  -- The negative splice branch is definitionally the given left-tail package.
  eminus n

/-- Helper for Chap13 Lemma 13 17 2: package the branchwise comparison isomorphisms into one
`ℤ`-indexed family over the explicit splice. -/
def serre_quotient_spliced_iso
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus Xminus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n)) :
    ∀ i, (Q).obj (serre_quotient_spliced_object Xplus Xminus i) ≅ K₀.X i
  | Int.ofNat n => serre_quotient_spliced_iso_ofNat (P := P) K₀ Xplus Xminus eplus eminus n
  | Int.negSucc n => serre_quotient_spliced_iso_negSucc (P := P) K₀ Xplus Xminus eplus eminus n

/-- Helper for Chap13 Lemma 13 17 2: on a nonnegative degree, the spliced differential is the
repaired nonnegative differential. -/
def serre_quotient_spliced_differential_ofNat
    (Xplus Xminus : ℕ → A)
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (_δzero : Xminus 0 ⟶ Xplus 0)
    (_δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (n : ℕ) :
    serre_quotient_spliced_object Xplus Xminus (Int.ofNat n) ⟶
      serre_quotient_spliced_object Xplus Xminus (Int.ofNat n + 1) :=
  -- The right-hand half of the splice is exactly the nonnegative repaired branch.
  δplus n

/-- Helper for Chap13 Lemma 13 17 2: at degree `-1`, the spliced differential is the bridge from
the negative branch into degree `0`. -/
def serre_quotient_spliced_differential_negOne
    (Xplus Xminus : ℕ → A)
    (_δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (δzero : Xminus 0 ⟶ Xplus 0)
    (_δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n) :
    serre_quotient_spliced_object Xplus Xminus (Int.negSucc 0) ⟶
      serre_quotient_spliced_object Xplus Xminus (Int.negSucc 0 + 1) :=
  -- The splice degree `-1 -> 0` is the distinguished bridge differential `δzero`.
  δzero

/-- Helper for Chap13 Lemma 13 17 2: below degree `-1`, the spliced differential is the repaired
negative differential. -/
def serre_quotient_spliced_differential_negSucc
    (Xplus Xminus : ℕ → A)
    (_δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (_δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (n : ℕ) :
    serre_quotient_spliced_object Xplus Xminus (Int.negSucc (n + 1)) ⟶
      serre_quotient_spliced_object Xplus Xminus (Int.negSucc (n + 1) + 1) :=
  -- The deeper negative splice branch is definitionally the repaired left-tail differential.
  δminus n

/-- Helper for Chap13 Lemma 13 17 2: package the branchwise differentials into one explicit
`ℤ`-indexed differential family over the splice. -/
def serre_quotient_spliced_differential
    (Xplus Xminus : ℕ → A)
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n) :
    ∀ i,
      serre_quotient_spliced_object Xplus Xminus i ⟶
        serre_quotient_spliced_object Xplus Xminus (i + 1)
  | Int.ofNat n =>
      serre_quotient_spliced_differential_ofNat Xplus Xminus δplus δzero δminus n
  | Int.negSucc 0 =>
      serre_quotient_spliced_differential_negOne Xplus Xminus δplus δzero δminus
  | Int.negSucc (n + 1) =>
      serre_quotient_spliced_differential_negSucc Xplus Xminus δplus δzero δminus n

/-- Helper for Chap13 Lemma 13 17 2: the explicit `Int`-matched splice still represents each
quotient differential of `K₀` on the nose. -/
lemma serre_quotient_spliced_represented_differentials
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n))
    (Xminus : ℕ → A)
    (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
    (δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (hzero :
      (eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero)
    (hminus : ∀ n,
      (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
        (eminus n).inv = (Q).map (δminus n)) :
    ∀ i,
      (serre_quotient_spliced_iso (P := P) K₀ Xplus Xminus eplus eminus i).hom ≫
          K₀.d i (i + 1) ≫
            (serre_quotient_spliced_iso (P := P) K₀ Xplus Xminus eplus eminus (i + 1)).inv =
        (Q).map
          (serre_quotient_spliced_differential Xplus Xminus δplus δzero δminus i) := by
  intro i
  cases i with
  | ofNat n =>
      -- The nonnegative splice branch is exactly the repaired positive package.
      simpa [serre_quotient_spliced_iso, serre_quotient_spliced_differential] using hplus n
  | negSucc n =>
      cases n with
      | zero =>
          -- Degree `-1` is the unique bridge from the negative tail into degree `0`.
          simpa [serre_quotient_spliced_iso, serre_quotient_spliced_differential] using hzero
      | succ n =>
          -- Lower negative degrees are exactly the repaired negative recursion.
          simpa [serre_quotient_spliced_iso, serre_quotient_spliced_differential] using hminus n

/-- Helper for Chap13 Lemma 13 17 2: the explicit `Int`-matched splice has literally square-zero
adjacent composites upstairs. -/
lemma serre_quotient_spliced_square_zero_relations
    (Xplus Xminus : ℕ → A)
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hsqplus : ∀ n, δplus n ≫ δplus (n + 1) = 0)
    (δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (hsqzero : δzero ≫ δplus 0 = 0)
    (hsqminus0 : δminus 0 ≫ δzero = 0)
    (hsqminus : ∀ n, δminus (n + 1) ≫ δminus n = 0) :
    ∀ i,
      serre_quotient_spliced_differential Xplus Xminus δplus δzero δminus i ≫
        serre_quotient_spliced_differential Xplus Xminus δplus δzero δminus (i + 1) = 0 := by
  intro i
  cases i with
  | ofNat n =>
      -- Nonnegative degrees already satisfy square-zero by the repaired positive recursion.
      simpa [serre_quotient_spliced_differential] using hsqplus n
  | negSucc n =>
      cases n with
      | zero =>
          -- Degree `-1` composes trivially with degree `0 -> 1` by the splice repair.
          simpa [serre_quotient_spliced_differential] using hsqzero
      | succ n =>
          cases n with
          | zero =>
              -- Degree `-2` composes trivially with the bridge differential by construction.
              simpa [serre_quotient_spliced_differential] using hsqminus0
          | succ n =>
              -- Farther left, square-zero is exactly the recursive negative-branch relation.
              simpa [serre_quotient_spliced_differential] using hsqminus n

/-- Helper for Chap13 Lemma 13 17 2: bundle the repaired positive and negative branches into one
explicit square-zero degreewise presentation of `K₀`. -/
lemma serre_quotient_spliced_square_zero_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n))
    (hsqplus : ∀ n, δplus n ≫ δplus (n + 1) = 0)
    (Xminus : ℕ → A)
    (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
    (δzero : Xminus 0 ⟶ Xplus 0)
    (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n)
    (hzero :
      (eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero)
    (hsqzero : δzero ≫ δplus 0 = 0)
    (hminus : ∀ n,
      (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
        (eminus n).inv = (Q).map (δminus n))
    (hsqminus0 : δminus 0 ≫ δzero = 0)
    (hsqminus : ∀ n, δminus (n + 1) ≫ δminus n = 0) :
    Nonempty (Σ' X : ℤ → A, Σ' e : ∀ i, (Q).obj (X i) ≅ K₀.X i,
      Σ' δ : ∀ i, X i ⟶ X (i + 1),
        Σ' _hδ : ∀ i,
            (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i),
          ∀ i, δ i ≫ δ (i + 1) = 0) := by
  -- Package the explicit splice first, then attach the represented differential equations and
  -- the square-zero relations as separate certified fields.
  refine ⟨⟨serre_quotient_spliced_object Xplus Xminus,
      serre_quotient_spliced_iso (P := P) K₀ Xplus Xminus eplus eminus,
      serre_quotient_spliced_differential Xplus Xminus δplus δzero δminus, ?_, ?_⟩⟩
  · -- The branchwise represented-differential identities assemble into the global splice.
    exact serre_quotient_spliced_represented_differentials (P := P) K₀
      Xplus eplus δplus hplus Xminus eminus δzero δminus hzero hminus
  · -- The repaired positive and negative square-zero relations assemble into one global law.
    exact serre_quotient_spliced_square_zero_relations
      Xplus Xminus δplus hsqplus δzero δminus hsqzero hsqminus0 hsqminus

lemma serre_quotient_square_zero_repair_spliced
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (_hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i)) :
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).essImage K₀ := by
  -- Route correction: instead of elaborating the splice definitions, the represented-differential
  -- proof, the square-zero proof, and the final packaging all inline here, assemble the explicit
  -- square-zero splice once and then hand it to the generic packaging lemma.
  obtain ⟨Xplus, eplus, δplus, hplus, hsqplus⟩ :=
    serre_quotient_nonnegative_square_zero_data_nat (P := P) K₀
  -- The repaired positive branch gives a literal square-zero presentation on all nonnegative
  -- degrees.
  obtain ⟨Xminus, eminus, δzero, δminus, hzero, hsqzero, hminus, hsqminus0, hsqminus⟩ :=
    serre_quotient_negative_square_zero_data_nat (P := P) K₀
      Xplus eplus δplus hplus hsqplus
  -- The repaired negative branch contributes the bridge at degree `-1` and the entire left tail.
  obtain ⟨X', e', δ', hδ', hsq'⟩ :=
    serre_quotient_spliced_square_zero_data (P := P) K₀
      Xplus eplus δplus hplus hsqplus Xminus eminus δzero δminus
      hzero hsqzero hminus hsqminus0 hsqminus
  -- The generic degreewise-presentation packaging turns the explicit square-zero splice into an
  -- upstairs complex mapping to `K₀`.
  exact serre_quotient_complex_of_degreewise_presentation (P := P) K₀ X' e' δ' hδ' hsq'

/-- Helper for Lemma 13.17.2: every cochain complex in the Serre quotient should admit an
upstairs complex whose image under `Q.mapHomologicalComplex` is isomorphic to it. -/
lemma serre_quotient_complex_lift
    (K : CochainComplex P.isoModSerre.Localization ℤ) :
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).essImage K := by
  -- Route correction: the direct `EssSurj.mapDerivedCategory` owner theorem is absent, so the
  -- remaining source-faithful blocker is exactly the textbook complex-lifting argument.
  obtain ⟨K₀, ⟨e₀⟩⟩ := serre_quotient_complex_on_preimages (P := P) K
  -- The verified frontier is Step 1 of the source proof: we may replace `K` by a conjugate
  -- complex whose terms are literally the chosen preimages `Q.objPreimage (K.X n)`.
  obtain ⟨Xplus, eplus, δplus, hplus⟩ := serre_quotient_nonnegative_data_nat (P := P) K₀
  -- The positive half of the textbook normalization is now completed: every differential in
  -- nonnegative degree is represented by an actual arrow in `A`.
  obtain ⟨Xminus, eminus, δzero, δminus, hzero, hminus⟩ :=
    serre_quotient_negative_data_nat (P := P) K₀ Xplus eplus δplus hplus
  -- The dual pullback recursion is now packaged over all negative degrees.
  obtain ⟨X, e, δ, hδ⟩ :=
    serre_quotient_spliced_degreewise_data
      (P := P) K₀ Xplus eplus δplus hplus Xminus eminus δzero δminus hzero hminus
  -- The verified frontier now matches the source proof up to the single global splice: every
  -- differential of `K₀` is represented by an actual arrow in `A` on one `ℤ`-indexed family.
  obtain ⟨L, ⟨eLift⟩⟩ :=
    serre_quotient_square_zero_repair_spliced (P := P) K₀ X e δ hδ
  -- Composing the repaired lift of `K₀` with the initial conjugation `K₀ ≅ K` finishes the
  -- complex-level essential-surjectivity witness.
  exact ⟨L, ⟨eLift ≪≫ e₀⟩⟩

variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} (P.isoModSerre.Localization)]

/-- Helper for Lemma 13.17.2: a complex-level lift induces the corresponding isomorphism after
passing to derived categories. -/
noncomputable def serre_quotient_derived_preimage_iso
    (L : CochainComplex A ℤ) (K : CochainComplex P.isoModSerre.Localization ℤ)
    (e : ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ K) :
    ((Q).mapDerivedCategory).obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj K :=
  ((Q).mapDerivedCategoryFactors.app L) ≪≫ DerivedCategory.Q.mapIso e

/-- Chap13 Lemma 13 17 2. Lemma 13.17.2: if `P` is a Serre subcategory of an abelian category `A`, then the canonical
functor `D(A) ⟶ D(A/P)` induced by the Serre quotient functor is essentially surjective. -/
@[stacks 06XL]
theorem serreQuotientDerivedFunctor_essSurj :
    Functor.EssSurj ((Q).mapDerivedCategory) := by
  refine ⟨fun X ↦ ?_⟩
  let K : CochainComplex P.isoModSerre.Localization ℤ := DerivedCategory.Q.objPreimage X
  -- Lift a complex representative of `X` to a complex in `A`.
  obtain ⟨L, ⟨e⟩⟩ := serre_quotient_complex_lift (P := P) K
  refine ⟨DerivedCategory.Q.obj L, ⟨?_⟩⟩
  -- Convert the complex-level lift into the desired derived-category isomorphism.
  exact serre_quotient_derived_preimage_iso (P := P) L K e ≪≫
    DerivedCategory.Q.objObjPreimageIso X

end _root_.CategoryTheory.ObjectProperty
