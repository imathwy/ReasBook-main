import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

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

variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} (P.isoModSerre.Localization)]

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
      (∀ n, K₀.X n = (Q).obj ((Q).objPreimage (K.X n))) ∧
      (∀ n, K₀.d n (n + 1) =
        ((Q).objObjPreimageIso (K.X n)).hom ≫ K.d n (n + 1) ≫
          ((Q).objObjPreimageIso (K.X (n + 1))).inv) ∧
      Nonempty (K₀ ≅ K) := by
  let δ : ∀ n : ℤ,
      (Q).obj ((Q).objPreimage (K.X n)) ⟶ (Q).obj ((Q).objPreimage (K.X (n + 1))) :=
    fun n ↦ ((Q).objObjPreimageIso (K.X n)).hom ≫ K.d n (n + 1) ≫
      ((Q).objObjPreimageIso (K.X (n + 1))).inv
  have hδ : ∀ n : ℤ, δ n ≫ δ (n + 1) = 0 := by
    intro n
    -- Transport the square-zero relation of `K` through the chosen objectwise isomorphisms.
    simpa [δ, Category.assoc] using
      congrArg
        (fun t ↦ ((Q).objObjPreimageIso (K.X n)).hom ≫ t ≫
          ((Q).objObjPreimageIso (K.X (n + 2))).inv)
        (K.d_comp_d n (n + 1) (n + 2))
  let K₀ : CochainComplex P.isoModSerre.Localization ℤ :=
    CochainComplex.of
      (fun n ↦ (Q).obj ((Q).objPreimage (K.X n)))
      δ
      hδ
  refine ⟨K₀, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    -- On adjacent degrees, the transported differential is exactly the conjugated differential.
    simpa [K₀, δ] using
      (CochainComplex.of_d
        (X := fun m ↦ (Q).obj ((Q).objPreimage (K.X m)))
        (d := δ)
        (sq := hδ)
        n)
  · refine ⟨HomologicalComplex.Hom.isoOfComponents
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
      (e n).hom ≫ K.d n (n + 1) ≫ (e (n + 1)).inv = (Q).map (δ n)) :
    ∃ K' : CochainComplex P.isoModSerre.Localization ℤ,
      (∀ n, K'.X n = (Q).obj (X' n)) ∧
      (∀ n, K'.d n (n + 1) = (Q).map (δ n)) ∧
      Nonempty (K' ≅ K) := by
  have hδ_nat :
      ∀ n : ℤ, (Q).map (δ n) ≫ (e (n + 1)).hom = (e n).hom ≫ K.d n (n + 1) := by
    intro n
    -- Move the comparison isomorphism on degree `n + 1` to the right to obtain the chain-map
    -- equation needed by `isoOfComponents`.
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ (e (n + 1)).hom) (hδ n)
  have hsq : ∀ n : ℤ, (Q).map (δ n) ≫ (Q).map (δ (n + 1)) = 0 := by
    intro n
    -- Conjugate the square-zero relation of `K` through the component isomorphisms.
    calc
      (Q).map (δ n) ≫ (Q).map (δ (n + 1)) =
          ((e n).hom ≫ K.d n (n + 1) ≫ (e (n + 1)).inv) ≫
            ((e (n + 1)).hom ≫ K.d (n + 1) (n + 2) ≫ (e (n + 2)).inv) := by
        rw [hδ n, hδ (n + 1)]
      _ = (e n).hom ≫ (K.d n (n + 1) ≫ K.d (n + 1) (n + 2)) ≫ (e (n + 2)).inv := by
        simp [Category.assoc]
      _ = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ (e n).hom ≫ t ≫ (e (n + 2)).inv)
            (K.d_comp_d n (n + 1) (n + 2))
  let K' : CochainComplex P.isoModSerre.Localization ℤ :=
    CochainComplex.of
      (fun n ↦ (Q).obj (X' n))
      (fun n ↦ (Q).map (δ n))
      hsq
  refine ⟨K', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    -- On adjacent degrees, the packaged differential is exactly the mapped arrow we started with.
    simpa [K'] using
      (CochainComplex.of_d
        (X := fun m ↦ (Q).obj (X' m))
        (d := fun m ↦ (Q).map (δ m))
        (sq := hsq)
        n)
  · refine ⟨HomologicalComplex.Hom.isoOfComponents e (fun i j hij ↦ ?_)⟩
    have h : i + 1 = j := by
      simpa using hij
    subst j
    -- The packaged complex is componentwise identified with `K` by the given conjugation data.
    simpa [K', Category.assoc] using hδ_nat i

/-- Helper for Lemma 13.17.2: a single positive-degree differential in the quotient with upstairs
source can be normalized by a pushout step, exactly as in the source proof. -/
lemma serre_quotient_nonnegative_step
    {X Z : A} (g : (Q).obj X ⟶ (Q).obj Z) :
    ∃ (Y : A) (e : (Q).obj Y ≅ (Q).obj Z) (δ : X ⟶ Y),
      g ≫ e.inv = (Q).map δ := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction Q P.isoModSerre g
  have hψ' : (Q).map ψ.f = (Q).map ψ.s ≫ g := by
    -- Precompose the fraction identity by the mapped denominator to obtain the commutative square
    -- used in the pushout step of the source proof.
    simpa [MorphismProperty.RightFraction.map, Category.assoc] using
      congrArg (fun k ↦ (Q).map ψ.s ≫ k) hψ.symm
  let Y := pushout ψ.s ψ.f
  let ePush : pushout ((Q).map ψ.s) ((Q).map ψ.f) ≅ (Q).obj Y :=
    PreservesPushout.iso (F := (Q)) ψ.s ψ.f
  haveI : IsIso ((Q).map ψ.s) :=
    Localization.inverts Q P.isoModSerre ψ.s ψ.hs
  haveI : IsIso (pushout.inr ((Q).map ψ.s) ((Q).map ψ.f)) := by infer_instance
  let e : (Q).obj Y ≅ (Q).obj Z :=
    ((asIso (pushout.inr ((Q).map ψ.s) ((Q).map ψ.f))) ≪≫ ePush).symm
  refine ⟨Y, e, pushout.inl ψ.s ψ.f, ?_⟩
  have he_inv :
      e.inv = (Q).map (pushout.inr ψ.s ψ.f) := by
    -- The new vertical isomorphism is the inverse of the mapped right coprojection after
    -- transporting the pushout through `Q`.
    dsimp [e]
    calc
      pushout.inr ((Q).map ψ.s) ((Q).map ψ.f) ≫ ePush.hom =
          ((Q).map (pushout.inr ψ.s ψ.f) ≫ ePush.inv) ≫ ePush.hom := by
            rw [PreservesPushout.inr_iso_inv (F := (Q)) ψ.s ψ.f]
      _ = (Q).map (pushout.inr ψ.s ψ.f) := by
            simp [Category.assoc]
  -- The pushout relation becomes the desired represented differential after canceling the mapped
  -- denominator, which is invertible in the localization.
  rw [he_inv]
  apply (cancel_mono ((Q).map ψ.s)).1
  calc
    (Q).map ψ.s ≫ (g ≫ (Q).map (pushout.inr ψ.s ψ.f)) =
        ((Q).map ψ.s ≫ g) ≫ (Q).map (pushout.inr ψ.s ψ.f) := by
          simp [Category.assoc]
    _ = (Q).map ψ.f ≫ (Q).map (pushout.inr ψ.s ψ.f) := by
          rw [hψ']
    _ = (Q).map (ψ.f ≫ pushout.inr ψ.s ψ.f) := by
          simp [Functor.map_comp, Category.assoc]
    _ = (Q).map (ψ.s ≫ pushout.inl ψ.s ψ.f) := by
          rw [pushout.condition]
    _ = (Q).map ψ.s ≫ (Q).map (pushout.inl ψ.s ψ.f) := by
          simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 13.17.2: the degree-zero source term for the positive pushout recursion is
the canonical preimage object of `K₀.X 0`. -/
lemma serre_quotient_nonnegative_base
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    ∃ X0 : A, (Q).obj X0 ≅ K₀.X 0 := by
  -- The source proof starts the positive recursion from the chosen preimage of the degree-zero
  -- term.
  exact ⟨(Q).objPreimage (K₀.X 0), (Q).objObjPreimageIso (K₀.X 0)⟩

/-- Helper for Lemma 13.17.2: once degree `n` has an upstairs representative, the next quotient
differential can be normalized by one pushout step and transported back to `K₀.X (n + 1)`. -/
lemma serre_quotient_nonnegative_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n)) :
    ∃ (Xnext : A) (e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (n + 1))) (δ_n : Xn ⟶ Xnext),
      (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ e_next.inv = (Q).map δ_n := by
  let Z := (Q).objPreimage (K₀.X (Int.ofNat (n + 1)))
  let g : (Q).obj Xn ⟶ (Q).obj Z :=
    (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
      ((Q).objObjPreimageIso (K₀.X (Int.ofNat (n + 1)))).inv
  obtain ⟨Y, e, δ, hδ⟩ := serre_quotient_nonnegative_step (P := P) g
  let e_next : (Q).obj Y ≅ K₀.X (Int.ofNat (n + 1)) :=
    e ≪≫ (Q).objObjPreimageIso (K₀.X (Int.ofNat (n + 1)))
  refine ⟨Y, e_next, δ, ?_⟩
  -- Postcompose the pushout normalization with the canonical preimage isomorphism on the target.
  simpa [g, e_next, Category.assoc] using hδ

/-- Helper for Lemma 13.17.2: the positive-degree pushout construction can be iterated over all
natural degrees, producing actual upstairs differentials on every `n ≥ 0`. -/
lemma serre_quotient_nonnegative_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ) :
    ∃ (Xplus : ℕ → A) (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
      (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1)),
      ∀ n,
        (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
          (eplus (n + 1)).inv = (Q).map (δplus n) := by
  classical
  let StepBundle (n : ℕ) : Type _ :=
    Σ Xn : A, Σ e_n : (Q).obj Xn ≅ K₀.X (Int.ofNat n),
      Σ Xnext : A, Σ e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (n + 1)),
        Σ δ_n : Xn ⟶ Xnext,
          (e_n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫ e_next.inv = (Q).map δ_n
  obtain ⟨X0, e0⟩ := serre_quotient_nonnegative_base (P := P) K₀
  obtain ⟨X1, e1, δ0, hδ0⟩ := serre_quotient_nonnegative_succ_data (P := P) K₀ 0 X0 e0
  let bundle0 : StepBundle 0 := ⟨X0, e0, X1, e1, δ0, hδ0⟩
  let bundleSucc : ∀ n, StepBundle n → StepBundle (n + 1) := fun n b ↦ by
    let Xnext := b.2.2.1
    let e_next := b.2.2.2.1
    obtain ⟨Xnextnext, e_nextnext, δ_next, hδ_next⟩ :=
      serre_quotient_nonnegative_succ_data (P := P) K₀ (n + 1) Xnext e_next
    -- Each successor step reuses the already-built degree `n + 1` term as the new source.
    exact ⟨Xnext, e_next, Xnextnext, e_nextnext, δ_next, hδ_next⟩
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
        simpa [Xplus] using (bundle (n + 1)).2.2.2.2.1
  refine ⟨Xplus, eplus, δplus, ?_⟩
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
    ∃ (Xtail : ℕ → A) (etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.ofNat (m + r)))
      (δtail : ∀ r, Xtail r ⟶ Xtail (r + 1)),
      Xtail 0 = Xm ∧
      ∀ r,
        (etail r).hom ≫ K₀.d (Int.ofNat (m + r)) (Int.ofNat (m + r + 1)) ≫
          (etail (r + 1)).inv = (Q).map (δtail r) := by
  classical
  let StepBundle (r : ℕ) : Type _ :=
    Σ Xr : A, Σ e_r : (Q).obj Xr ≅ K₀.X (Int.ofNat (m + r)),
      Σ Xnext : A, Σ e_next : (Q).obj Xnext ≅ K₀.X (Int.ofNat (m + r + 1)),
        Σ δ_r : Xr ⟶ Xnext,
          (e_r).hom ≫ K₀.d (Int.ofNat (m + r)) (Int.ofNat (m + r + 1)) ≫
            e_next.inv = (Q).map δ_r
  have em0 : (Q).obj Xm ≅ K₀.X (Int.ofNat (m + 0)) := by
    simpa using em
  obtain ⟨X1, e1, δ0, hδ0⟩ := serre_quotient_nonnegative_succ_data (P := P) K₀ m Xm em
  let bundle0 : StepBundle 0 := by
    -- The initial bundle records the given frontier and the first pushout step out of it.
    refine ⟨Xm, em0, X1, ?_, δ0, ?_⟩
    · simpa using e1
    · simpa using hδ0
  let bundleSucc : ∀ r, StepBundle r → StepBundle (r + 1) := fun r b ↦ by
    let Xnext := b.2.2.1
    let e_next := b.2.2.2.1
    obtain ⟨Xnextnext, e_nextnext, δ_next, hδ_next⟩ :=
      serre_quotient_nonnegative_succ_data (P := P) K₀ (m + (r + 1)) Xnext e_next
    -- Each successor step forgets the already-used source and extends the tail one degree further.
    refine ⟨Xnext, ?_, Xnextnext, ?_, δ_next, ?_⟩
    · simpa [Nat.add_assoc] using e_next
    · simpa [Nat.add_assoc] using e_nextnext
    · simpa [Nat.add_assoc] using hδ_next
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
        simpa [Xtail] using (bundle (r + 1)).2.2.2.2.1
  refine ⟨Xtail, etail, δtail, ?_⟩
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
  let σ : cokernel f ⟶ Y :=
    cokernel.desc f (𝟙 Y) (by
      -- Every map out of a zero object vanishes, so the identity cocone is compatible with `f`.
      simpa using hX.eq_of_src (f ≫ 𝟙 Y) 0)
  refine ⟨⟨σ, ?_, ?_⟩⟩
  · -- The chosen descender is a right inverse to the cokernel projection by construction.
    exact cokernel.π_desc _ _ _
  · -- Since cokernel projections are epimorphisms, equality after precomposition by them is enough.
    apply (cancel_epi (cokernel.π f)).1
    simp [σ, Category.assoc]

/-- Helper for Lemma 13.17.2: if a morphism is zero, then its kernel inclusion is an
isomorphism. -/
lemma kernel_ι_isIso_of_eq_zero
    {C : Type*} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsIso (kernel.ι f) := by
  let ρ : X ⟶ kernel f :=
    kernel.lift f (𝟙 X) (by
      -- After rewriting `f` to zero, the identity on `X` lands in the kernel.
      simpa [hf] using (show (𝟙 X : X ⟶ X) ≫ (0 : X ⟶ Y) = 0 by simp))
  refine ⟨⟨ρ, ?_, ?_⟩⟩
  · -- The kernel lift was chosen so that postcomposing recovers the identity.
    exact kernel.lift_ι _ _ _
  · -- Kernel inclusions are monomorphisms, so equality can be checked after postcomposition.
    apply (cancel_mono (kernel.ι f)).1
    simp [ρ, Category.assoc]

/-- Helper for Lemma 13.17.2: a single negative-degree differential in the quotient with upstairs
target can be normalized by a pullback step, dual to the positive pushout step. -/
lemma serre_quotient_negative_step
    {X Z : A} (g : (Q).obj Z ⟶ (Q).obj X) :
    ∃ (Y : A) (e : (Q).obj Y ≅ (Q).obj Z) (δ : Y ⟶ X),
      e.hom ≫ g = (Q).map δ := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction Q P.isoModSerre g
  have hψ' : g ≫ (Q).map ψ.s = (Q).map ψ.f := by
    -- Cross-multiply the left-fraction presentation to obtain the pullback square in the source.
    simpa [hψ] using
      MorphismProperty.LeftFraction.map_comp_map_s ψ Q
        (Localization.inverts Q P.isoModSerre)
  let Y := pullback ψ.f ψ.s
  let ePull : (Q).obj Y ≅ pullback ((Q).map ψ.f) ((Q).map ψ.s) :=
    PreservesPullback.iso (F := (Q)) ψ.f ψ.s
  haveI : IsIso ((Q).map ψ.s) :=
    Localization.inverts Q P.isoModSerre ψ.s ψ.hs
  haveI : IsIso (pullback.fst ((Q).map ψ.f) ((Q).map ψ.s)) := by infer_instance
  let e : (Q).obj Y ≅ (Q).obj Z :=
    ePull ≪≫ asIso (pullback.fst ((Q).map ψ.f) ((Q).map ψ.s))
  refine ⟨Y, e, pullback.snd ψ.f ψ.s, ?_⟩
  have he_hom :
      e.hom = (Q).map (pullback.fst ψ.f ψ.s) := by
    -- The new vertical isomorphism is the mapped first projection after transporting the pullback.
    dsimp [e]
    calc
      ePull.hom ≫ pullback.fst ((Q).map ψ.f) ((Q).map ψ.s) =
          ePull.hom ≫ pullback.fst ((Q).map ψ.f) ((Q).map ψ.s) := rfl
      _ = (Q).map (pullback.fst ψ.f ψ.s) := by
          rw [PreservesPullback.iso_hom_fst (F := (Q)) ψ.f ψ.s]
  rw [he_hom]
  apply (cancel_mono ((Q).map ψ.s)).1
  calc
    (Q).map (pullback.fst ψ.f ψ.s) ≫ g ≫ (Q).map ψ.s =
        (Q).map (pullback.fst ψ.f ψ.s) ≫ (g ≫ (Q).map ψ.s) := by
          simp [Category.assoc]
    _ = (Q).map (pullback.fst ψ.f ψ.s) ≫ (Q).map ψ.f := by
          rw [hψ']
    _ = (Q).map (pullback.fst ψ.f ψ.s ≫ ψ.f) := by
          simp [Functor.map_comp, Category.assoc]
    _ = (Q).map (pullback.snd ψ.f ψ.s ≫ ψ.s) := by
          rw [pullback.condition]
    _ = (Q).map (pullback.snd ψ.f ψ.s) ≫ (Q).map ψ.s := by
          simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 13.17.2: once degree `-(n+1)` has an upstairs representative, the previous
negative differential can be normalized by one pullback step and transported back to
`K₀.X (Int.negSucc (n + 1))`. -/
lemma serre_quotient_negative_succ_data
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (n : ℕ) (Xn : A)
    (e_n : (Q).obj Xn ≅ K₀.X (Int.negSucc n)) :
    ∃ (Xprev : A) (e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1)))
      (δ_prev : Xprev ⟶ Xn),
      (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ e_n.inv = (Q).map δ_prev := by
  let Z := (Q).objPreimage (K₀.X (Int.negSucc (n + 1)))
  let g : (Q).obj Z ⟶ (Q).obj Xn :=
    ((Q).objObjPreimageIso (K₀.X (Int.negSucc (n + 1)))).hom ≫
      K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ e_n.inv
  obtain ⟨Y, e, δ, hδ⟩ := serre_quotient_negative_step (P := P) g
  let e_prev : (Q).obj Y ≅ K₀.X (Int.negSucc (n + 1)) :=
    e ≪≫ (Q).objObjPreimageIso (K₀.X (Int.negSucc (n + 1)))
  refine ⟨Y, e_prev, δ, ?_⟩
  -- Postcompose the pullback normalization with the canonical preimage isomorphism on the source.
  simpa [g, e_prev, Category.assoc] using hδ

/-- Helper for Lemma 13.17.2: the negative-degree pullback construction can be iterated over all
natural degrees, producing actual upstairs differentials on every `n < 0`. -/
lemma serre_quotient_negative_data_nat
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (Xplus : ℕ → A)
    (eplus : ∀ n, (Q).obj (Xplus n) ≅ K₀.X (Int.ofNat n))
    (δplus : ∀ n, Xplus n ⟶ Xplus (n + 1))
    (hplus : ∀ n,
      (eplus n).hom ≫ K₀.d (Int.ofNat n) (Int.ofNat (n + 1)) ≫
        (eplus (n + 1)).inv = (Q).map (δplus n)) :
    ∃ (Xminus : ℕ → A) (eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n))
      (δzero : Xminus 0 ⟶ Xplus 0) (δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n),
      ((eminus 0).hom ≫ K₀.d (Int.negSucc 0) 0 ≫ (eplus 0).inv = (Q).map δzero) ∧
      (∀ n,
        (eminus (n + 1)).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫
          (eminus n).inv = (Q).map (δminus n)) := by
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
    Σ Xprev : A, Σ e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (n + 1)),
      Σ δ_prev : Xprev ⟶ b.1,
        (e_prev).hom ≫ K₀.d (Int.negSucc (n + 1)) (Int.negSucc n) ≫ b.2.inv = (Q).map δ_prev
  let stepData : ∀ n (b : Bundle n), StepData n b := fun n b ↦ by
    exact Classical.choose (serre_quotient_negative_succ_data (P := P) K₀ n b.1 b.2)
  let bundle0 : Bundle 0 := ⟨Xminus0, eminus0⟩
  let bundleSucc : ∀ n, Bundle n → Bundle (n + 1) := fun n b ↦
    ⟨(stepData n b).1, (stepData n b).2.1⟩
  let bundle : ∀ n, Bundle n := Nat.rec bundle0 bundleSucc
  let Xminus : ℕ → A := fun n ↦ (bundle n).1
  let eminus : ∀ n, (Q).obj (Xminus n) ≅ K₀.X (Int.negSucc n) := fun n ↦ (bundle n).2
  let δminus : ∀ n, Xminus (n + 1) ⟶ Xminus n := fun n ↦ by
    -- Each recursive step produces the next negative differential into the previously built term.
    simpa [Xminus, bundle, bundleSucc] using (stepData n (bundle n)).2.2.1
  refine ⟨Xminus, eminus, δzero, δminus, ?_⟩
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
    ∃ (Xtail : ℕ → A) (etail : ∀ r, (Q).obj (Xtail r) ≅ K₀.X (Int.negSucc (m + r)))
      (δtail : ∀ r, Xtail (r + 1) ⟶ Xtail r),
      Xtail 0 = Xm ∧
      ∀ r,
        (etail (r + 1)).hom ≫
            K₀.d (Int.negSucc (m + (r + 1))) (Int.negSucc (m + r)) ≫
              (etail r).inv =
          (Q).map (δtail r) := by
  classical
  let Bundle (r : ℕ) : Type _ :=
    Σ Xr : A, (Q).obj Xr ≅ K₀.X (Int.negSucc (m + r))
  let StepData (r : ℕ) (b : Bundle r) : Type _ :=
    Σ Xprev : A, Σ e_prev : (Q).obj Xprev ≅ K₀.X (Int.negSucc (m + (r + 1))),
      Σ δ_prev : Xprev ⟶ b.1,
        (e_prev).hom ≫
            K₀.d (Int.negSucc (m + (r + 1))) (Int.negSucc (m + r)) ≫
              b.2.inv =
          (Q).map δ_prev
  let stepData : ∀ r (b : Bundle r), StepData r b := fun r b ↦ by
    obtain ⟨Xprev, e_prev, δ_prev, hδ_prev⟩ :=
      serre_quotient_negative_succ_data (P := P) K₀ (m + r) b.1 b.2
    -- One pullback step extends the reconstructed tail one degree further to the left.
    refine ⟨Xprev, ?_, δ_prev, ?_⟩
    · simpa [Nat.add_assoc] using e_prev
    · simpa [Nat.add_assoc] using hδ_prev
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
  refine ⟨Xtail, etail, δtail, ?_⟩
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
    ∃ (X : ℤ → A) (e : ∀ i, (Q).obj (X i) ≅ K₀.X i) (δ : ∀ i, X i ⟶ X (i + 1)),
      ∀ i,
        (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i) := by
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
  refine ⟨X, e, δ, ?_⟩
  intro i
  cases i using Int with
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
    rw [← Abelian.image.fac α]
    simp [q, Category.assoc]
  have hQimage_ι : (Q).map (Abelian.image.ι α) = 0 := by
    -- The mapped image inclusion is zero because its composite with the mapped epi
    -- `factorThruImage α` is the already-vanishing mapped composite.
    apply zero_of_epi_comp ((Q).map (Abelian.factorThruImage α))
    simpa [Functor.map_comp, Category.assoc, α] using hzero
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
    simpa [q, CategoryTheory.Limits.PreservesCokernel.iso] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (isColimitOfHasCokernelOfPreservesColimit (Q) (Abelian.image.ι α))
        (colimit.isColimit (parallelPair ((Q).map (Abelian.image.ι α)) 0))
        WalkingParallelPair.one)
  have hmap_q' :
      (Q).map q = cokernel.π ((Q).map (Abelian.image.ι α)) ≫ eCoker.inv := by
    calc
      (Q).map q = (Q).map q ≫ eCoker.hom ≫ eCoker.inv := by
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
    simpa [α, Category.assoc] using kernel.condition α
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
            simp [Category.assoc]
      _ = eKernel.hom ≫ kernel.ι ((Q).map α) := by
            rw [PreservesKernel.iso_inv_ι (F := (Q)) α]
  constructor
  · simpa [α] using hkernel_zero
  · rw [hmap_kernel]
    infer_instance

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
  -- Transport the square-zero relation of `K₀` through the chosen degreewise presentations.
  calc
    (Q).map (δ i ≫ δ (i + 1)) = (Q).map (δ i) ≫ (Q).map (δ (i + 1)) := by
      simp [Functor.map_comp]
    _ =
        ((e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv) ≫
          ((e (i + 1)).hom ≫ K₀.d (i + 1) (i + 2) ≫ (e (i + 2)).inv) := by
      rw [hδ i, hδ (i + 1)]
    _ = (e i).hom ≫ (K₀.d i (i + 1) ≫ K₀.d (i + 1) (i + 2)) ≫ (e (i + 2)).inv := by
      simp [Category.assoc]
    _ = 0 := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦ (e i).hom ≫ t ≫ (e (i + 2)).inv)
          (K₀.d_comp_d i (i + 1) (i + 2))

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
    ∃ (Y : A) (q : X (i + 2) ⟶ Y) (eY : (Q).obj Y ≅ K₀.X (i + 2)),
      δ i ≫ δ (i + 1) ≫ q = 0 ∧
      IsIso ((Q).map q) ∧
      (e (i + 1)).hom ≫ K₀.d (i + 1) (i + 2) ≫ eY.inv =
        (Q).map (δ (i + 1) ≫ q) := by
  have hmapzero :
      (Q).map (δ i ≫ δ (i + 1)) = 0 :=
    serre_quotient_represented_double_composite_map_zero
      (P := P) K₀ X e δ hδ i
  let q : X (i + 2) ⟶ cokernel (Abelian.image.ι (δ i ≫ δ (i + 1))) :=
    cokernel.π (Abelian.image.ι (δ i ≫ δ (i + 1)))
  obtain ⟨hkill, hqiso⟩ :=
    serre_quotient_positive_square_zero_step (P := P) (u := δ i) (v := δ (i + 1)) hmapzero
  let eY : (Q).obj (cokernel (Abelian.image.ι (δ i ≫ δ (i + 1)))) ≅ K₀.X (i + 2) :=
    (asIso ((Q).map q)).symm ≪≫ e (i + 2)
  have heY_inv :
      eY.inv = (e (i + 2)).inv ≫ (Q).map q := by
    -- The new comparison iso is the old one followed by the mapped quotient arrow.
    simp [eY, q, Category.assoc]
  refine ⟨_, q, eY, ?_, hqiso, ?_⟩
  · -- The quotient by the image kills the offending double composite upstairs.
    simpa [q, Category.assoc] using hkill
  · -- Postcompose the old represented differential by the new quotient map on degree `i + 2`.
    calc
      (e (i + 1)).hom ≫ K₀.d (i + 1) (i + 2) ≫ eY.inv =
          ((e (i + 1)).hom ≫ K₀.d (i + 1) (i + 2) ≫ (e (i + 2)).inv) ≫ (Q).map q := by
        rw [heY_inv]
        simp [Category.assoc]
      _ = (Q).map (δ (i + 1)) ≫ (Q).map q := by
        rw [hδ (i + 1)]
      _ = (Q).map (δ (i + 1) ≫ q) := by
        simp [Functor.map_comp, Category.assoc]

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
    ∃ (Y : A) (ι : Y ⟶ X i) (eY : (Q).obj Y ≅ K₀.X i),
      (ι ≫ δ i) ≫ δ (i + 1) = 0 ∧
      IsIso ((Q).map ι) ∧
      (eY).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv =
        (Q).map (ι ≫ δ i) := by
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
    simp [eY, ι, Category.assoc]
  refine ⟨_, ι, eY, ?_, hιiso, ?_⟩
  · -- The kernel inclusion annihilates the offending double composite upstairs.
    simpa [ι, Category.assoc] using hkill
  · -- Precompose the old represented differential by the new kernel inclusion on degree `i`.
    calc
      (eY).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv =
          (Q).map ι ≫ ((e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv) := by
        rw [heY_hom]
        simp [Category.assoc]
      _ = (Q).map ι ≫ (Q).map (δ i) := by
        rw [hδ i]
      _ = (Q).map (ι ≫ δ i) := by
        simp [Functor.map_comp, Category.assoc]

/-- Helper for Lemma 13.17.2: once every differential of `K₀` is represented on a single
`ℤ`-indexed family in `A`, the remaining source-faithful work is the two branchwise square-zero
repairs that turn this presentation into an actual upstairs complex. -/
lemma serre_quotient_square_zero_repair_spliced
    (K₀ : CochainComplex P.isoModSerre.Localization ℤ)
    (X : ℤ → A)
    (e : ∀ i, (Q).obj (X i) ≅ K₀.X i)
    (δ : ∀ i, X i ⟶ X (i + 1))
    (hδ : ∀ i,
      (e i).hom ≫ K₀.d i (i + 1) ≫ (e (i + 1)).inv = (Q).map (δ i)) :
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).essImage K₀ := by
  -- TODO: apply the source proof's rightward quotient repair on nonnegative degrees, using
  -- `serre_quotient_nonnegative_tail_from` to rebuild the suffix after each local cokernel step;
  -- then splice once and run the dual leftward kernel repair on negative degrees via
  -- `serre_quotient_negative_tail_from`, finally package the literal square-zero family with
  -- `serre_quotient_complex_of_degreewise_presentation`.
  sorry

/-- Helper for Lemma 13.17.2: every cochain complex in the Serre quotient should admit an
upstairs complex whose image under `Q.mapHomologicalComplex` is isomorphic to it. -/
lemma serre_quotient_complex_lift
    (K : CochainComplex P.isoModSerre.Localization ℤ) :
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).essImage K := by
  -- Route correction: the direct `EssSurj.mapDerivedCategory` owner theorem is absent, so the
  -- remaining source-faithful blocker is exactly the textbook complex-lifting argument.
  obtain ⟨K₀, _, _, ⟨e₀⟩⟩ := serre_quotient_complex_on_preimages (P := P) K
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

/-- Helper for Lemma 13.17.2: a complex-level lift induces the corresponding isomorphism after
passing to derived categories. -/
noncomputable def serre_quotient_derived_preimage_iso
    (L : CochainComplex A ℤ) (K : CochainComplex P.isoModSerre.Localization ℤ)
    (e : ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ K) :
    ((Q).mapDerivedCategory).obj (DerivedCategory.Q.obj L) ≅ DerivedCategory.Q.obj K :=
  ((Q).mapDerivedCategoryFactors.app L) ≪≫ DerivedCategory.Q.mapIso e

/-- Lemma 13.17.2: if `P` is a Serre subcategory of an abelian category `A`, then the canonical
functor `D(A) ⟶ D(A/P)` induced by the Serre quotient functor is essentially surjective. -/
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
