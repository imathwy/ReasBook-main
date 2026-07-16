import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveEnvelopeHom

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section ProjectiveCharacterCriterion

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
-- Serre's Chapter 18 modular system uses a *complete* DVR `A`; the projective scalar-extension
-- owner `projectiveCharacterScalarExtension` requires adic completeness of the maximal ideal.
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

/-
Domain-style sampling for Exercise `18-18.3-2`:
* primary domain: modular representation theory of finite groups, combining the projective
  scalar-extension owner `projectiveGrothendieckScalarExtensionHom A K`, the Chapter `16`
  Grothendieck-character owner `finiteRepGrothendieckCharacter`, the Chapter `12`
  scalar-extension owner `A ⊗R[K](G)`, and the Cartan owners `cartanCokernel` and
  `cartanMatrix`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `finiteRepGrothendieckCharacter`,
  `characterRingOverFieldAlgebraScalarExtension`,
  `cartanCokernel`,
  `cartanMatrix`.

Layer triage:
* source-facing: the projective-character span inside `A ⊗R[K](G)` and the invariant-factor
  formulas indexed by `p`-regular conjugacy-class representatives;
* core/canonical: the owner declarations
  `projectiveGrothendieckScalarExtensionHom A K`, `finiteRepGrothendieckCharacter K G`,
  `A ⊗R[K](G)`, `cartanCokernel`, and `cartanMatrix`;
* bridge/view: the codomain restriction from `R₀[K](G)` to `A ⊗R[K](G)` obtained from
  `finiteRepGrothendieckCharacter K G` and the canonical inclusion `R[K](G) ⊆ A ⊗R[K](G)`.

Ordinary-character regime check:
* the source-facing span in part `(1)` lives in the characteristic-zero ordinary-character setting
  used nearby in Chapter `18`;
* its primitive definition inside `A ⊗R[K](G)` needs only `[CharZero K]`, but the membership
  criterion below must stay in the standard large-field regime
  `[HasEnoughRootsOfUnity K (Monoid.exponent G)]`, matching the Chapter `16` image criterion and
  neighboring Theorem `18-18.3-1`.
-/
local notation "k" => IsLocalRing.ResidueField A
local notation "e" => (projectiveGrothendieckScalarExtensionHom A K : P₀[k](G) →+ R₀[K](G))
local instance instFintypeGRegularIndicator : Fintype G := Fintype.ofFinite G

namespace ConjClasses

/-- Helper for Exercise 18-18.3-2: the centralizer order attached to a conjugacy class is
the centralizer order of a chosen representative. This is the source-side scalar Serre later
splits into its `p`-part and prime-to-`p` part. -/
noncomputable def centralizerCard (c : ConjClasses G) : ℕ :=
  Nat.card (Subgroup.centralizer ({Classical.choose (ConjClasses.mk_surjective c)} : Set G))

/-- Helper for Exercise 18-18.3-2: Serre's centralizer order on a conjugacy class factors as the
centralizer `p`-part times its prime-to-`p` complement. -/
theorem centralizerCard_eq_centralizerPPart_mul_ordCompl
    (c : ConjClasses G) :
    centralizerCard c = centralizerPPart p c * ordCompl[p] (centralizerCard c) := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  -- On the chosen representative, this is exactly the standard `ordProj`/`ordCompl`
  -- factorization, and the class-level `p`-part is computed on the same representative.
  calc
    centralizerCard c =
        Nat.card (Subgroup.centralizer ({g} : Set G)) := by
          simp [ConjClasses.centralizerCard, g]
    _ =
        Representation.centralizerPPart p g *
          ordCompl[p] (Nat.card (Subgroup.centralizer ({g} : Set G))) := by
          simpa [Representation.centralizerPPart] using
            (Nat.ordProj_mul_ordCompl_eq_self
              (Nat.card (Subgroup.centralizer ({g} : Set G))) p).symm
    _ =
        ConjClasses.centralizerPPart p c * ordCompl[p] (centralizerCard c) := by
          have hppart : Representation.centralizerPPart p g = ConjClasses.centralizerPPart p c := by
            rw [← hg, ConjClasses.centralizerPPart_mk]
          have hcard :
              centralizerCard c = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
            simp [ConjClasses.centralizerCard, g]
          rw [hppart, hcard]

end ConjClasses

/-- Helper for Exercise 18-18.3-2: regular-class point masses use classical equality on
`PRegularConjClass G p`. -/
local instance decidableEqPRegularConjClass : DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: the prime-to-`p` factor in the centralizer order of a
`p`-regular class is a unit in the coefficient ring `A`. This is the source-side rescaling input
used to pass between the full indicator and the scaled indicator. -/
theorem ordCompl_centralizerCard_isUnit
    (c : PRegularConjClass G p) :
    IsUnit ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A)) := by
  -- Reduce unitness in the local ring `A` to nonvanishing in the residue field, then use the
  -- fact that the prime-to-`p` part is not divisible by `p`.
  refine
    (IsLocalRing.residue_ne_zero_iff_isUnit
      ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A))).1 ?_
  intro hzero
  have hpdiv : p ∣ ordCompl[p] (ConjClasses.centralizerCard c.1) := by
    exact (CharP.cast_eq_zero_iff k p _).mp hzero
  have hcard_ne : ConjClasses.centralizerCard c.1 ≠ 0 := by
    dsimp [ConjClasses.centralizerCard]
    exact
      (Finite.card_pos
        (α := Subgroup.centralizer ({Classical.choose (ConjClasses.mk_surjective c.1)} : Set G))).ne'
  exact Nat.not_dvd_ordCompl (Fact.out : Nat.Prime p) hcard_ne hpdiv

/-- Helper for Exercise 18-18.3-2: Serre's full regular indicator at `c` is the point mass whose
single nonzero value is the full centralizer order of `c`. -/
noncomputable def full_regular_indicator
    (c : PRegularConjClass G p) : PRegularConjClass G p → K :=
  Pi.single c (algebraMap A K (ConjClasses.centralizerCard c.1 : A))

/-- Helper for Exercise 18-18.3-2: Serre's prime-to-`p` regular indicator at `c` is the
`A`-valued point mass whose single nonzero value is the prime-to-`p` factor of the centralizer
order. Pairing this function with projective envelopes is the source-faithful route to the
`p`-part divisibility statement. -/
noncomputable def primeToP_regular_indicator
    (c : PRegularConjClass G p) : PRegularConjClass G p → A :=
  Pi.single c (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)

/-- Helper for Exercise 18-18.3-2: evaluating Serre's prime-to-`p` point mass at a `p`-regular
representative of the supporting class returns the prime-to-`p` factor of the centralizer order.
This is the positive branch of the source point-mass calculation. -/
theorem primeToP_regular_indicator_ofSubtype_eq_ordCompl
    (c : PRegularConjClass G p) {s : G} (hs : IsPRegular p s)
    (hmk : ConjClasses.mk s = c.1) :
    primeToP_regular_indicator (p := p) (A := A) (G := G) c
        (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩) =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  -- Rewrite the chosen representative back to the supporting `p`-regular conjugacy class `c`.
  have hEq : PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩ = c := Subtype.ext hmk
  -- Evaluating the point mass at its support returns the defining coefficient.
  simpa [primeToP_regular_indicator, Pi.single_apply, hEq]

/-- Helper for Exercise 18-18.3-2: evaluating Serre's prime-to-`p` point mass at a `p`-regular
representative outside the supporting class gives `0`. This is the negative branch of the source
point-mass calculation. -/
theorem primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
    (c : PRegularConjClass G p) {s : G} (hs : IsPRegular p s)
    (hmk : ConjClasses.mk s ≠ c.1) :
    primeToP_regular_indicator (p := p) (A := A) (G := G) c
        (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩) =
      0 := by
  -- A representative of a different conjugacy class cannot land on the support of the point mass.
  have hNe : PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩ ≠ c := by
    intro hEq
    exact hmk (by simpa [PRegularConjClass.coe_ofSubtype] using congrArg Subtype.val hEq)
  -- Evaluating the point mass away from its support is zero.
  simpa [primeToP_regular_indicator, Pi.single_apply, hNe]

/-- Helper for Exercise 18-18.3-2: summing a function constant on conjugacy classes over `G`
equals summing it over conjugacy classes weighted by class size. This is the bookkeeping step used
to collapse Serre's prime-to-`p` point masses. -/
theorem sum_over_group_eq_sum_over_conjClasses
    (a : ConjClasses G → K) :
    ∑ x : G, a (ConjClasses.mk x) =
      ∑ c : ConjClasses G, (Nat.card c.carrier : K) * a c := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let F : G → ConjClasses G := ConjClasses.mk
  have himage : (Finset.univ : Finset G).image F = (Finset.univ : Finset (ConjClasses G)) := by
    ext c
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      exact Finset.mem_image.mpr ⟨g, by simp [F]⟩
  have hfiberwise :
      ∑ c ∈ (Finset.univ : Finset G).image F,
          ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x)
        =
      ∑ x : G, a (F x) := by
    simpa [F] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset G))
        (t := (Finset.univ : Finset G).image F)
        (g := F)
        (fun x hx ↦ Finset.mem_image_of_mem F hx)
        (fun x : G ↦ a (F x)))
  have hcoeff (c : ConjClasses G) :
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) =
        (Nat.card c.carrier : K) * a c := by
    let fiber : Finset G := (Finset.univ : Finset G).filter (fun x ↦ F x = c)
    have hfiber_mem : ∀ x : G, x ∈ fiber ↔ x ∈ c.carrier := by
      intro x
      simp [fiber, F, ConjClasses.mem_carrier_iff_mk_eq]
    have hsum_const :
        ∑ x ∈ fiber, a (F x) = (fiber.card : K) * a c := by
      calc
        ∑ x ∈ fiber, a (F x) = ∑ x ∈ fiber, a c := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hx' : F x = c := by
            simpa [fiber] using hx
          simpa [hx']
        _ = (fiber.card : K) * a c := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : fiber.card = Nat.card c.carrier := by
      let _ : Fintype c.carrier := Fintype.ofFinset fiber (hfiber_mem ·)
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_ofFinset fiber (hfiber_mem ·)).symm
    -- On each conjugacy class fiber, the summand is constant.
    calc
      ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) = ∑ x ∈ fiber, a (F x) := by
        rfl
      _ = (fiber.card : K) * a c := hsum_const
      _ = (Nat.card c.carrier : K) * a c := by
        rw [hcard]
  -- Partition `G` by the fibers of `ConjClasses.mk`.
  calc
    ∑ x : G, a (ConjClasses.mk x) =
        ∑ c ∈ (Finset.univ : Finset G).image F,
          ∑ x ∈ (Finset.univ : Finset G) with F x = c, a (F x) := by
          simpa [F] using hfiberwise.symm
    _ = ∑ c : ConjClasses G, (Nat.card c.carrier : K) * a c := by
          rw [himage]
          refine Finset.sum_congr rfl ?_
          intro c hc
          exact hcoeff c

/-- Helper for Exercise 18-18.3-2: the zero extension of Serre's prime-to-`p` point mass at `c`
has total mass equal to the size of the conjugacy class times the prime-to-`p` factor of the
centralizer order. This is the source-side class-sum calculation needed before the orthogonality
comparison. -/
theorem sum_primeToP_regular_indicator_zeroExtension_eq_class_card_mul
    (c : PRegularConjClass G p) :
    ∑ s : G,
      (if hs : IsPRegular p s then
        algebraMap A K
          ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
            (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
      else 0) =
      (Nat.card c.1.carrier : K) *
        algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
  classical
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let a : ConjClasses G → K := fun d ↦
    if h : d = c.1 then
      algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A)
    else 0
  have hsum :
      ∑ s : G,
        (if hs : IsPRegular p s then
          algebraMap A K
            ((primeToP_regular_indicator (p := p) (A := A) (G := G) c)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
        else 0) =
        ∑ s : G, a (ConjClasses.mk s) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    by_cases hsp : IsPRegular p s
    · by_cases hmk : ConjClasses.mk s = c.1
      · -- On the supporting conjugacy class, the point mass takes its unique nonzero value.
        rw [dif_pos hsp,
          primeToP_regular_indicator_ofSubtype_eq_ordCompl
            (p := p) (A := A) (G := G) c hsp hmk]
        simp [a, hmk]
      · -- Away from the supporting conjugacy class, the point mass vanishes.
        rw [dif_pos hsp,
          primeToP_regular_indicator_ofSubtype_eq_zero_of_mk_ne
            (p := p) (A := A) (G := G) c hsp hmk]
        simp [a, hmk]
    · by_cases hmk : ConjClasses.mk s = c.1
      · have hs_reg : IsPRegular p s := by
          exact c.2 s (by simpa [ConjClasses.mem_carrier_iff_mk_eq] using hmk)
        exact (hsp hs_reg).elim
      · simp [a, hsp, hmk]
  -- Collapse the group sum to the unique conjugacy class supporting the point mass.
  rw [hsum, sum_over_group_eq_sum_over_conjClasses (G := G) (K := K) a]
  classical
  have hc_mem : c.1 ∈ (Finset.univ : Finset (ConjClasses G)) := by simp
  rw [Finset.sum_eq_single c.1]
  · simp [a]
  · intro d hd hdc
    simp [a, hdc]
  · intro hc
    exact (hc hc_mem).elim

/-- Helper for Exercise 18-18.3-2: inverting a conjugacy class does not change the order of the
centralizer of a representative. This isolates the only stable class-level datum needed to repair
the remaining `s⁻¹` pairing convention in Serre's orthogonality formula. -/
theorem nat_card_centralizer_eq_of_isConj
    {g h : G} (hgh : IsConj g h) :
    Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card (Subgroup.centralizer ({h} : Set G)) := by
  rcases hgh with ⟨u, hu⟩
  have hh : h = (u : G) * g * (u : G)⁻¹ := by
    symm
    exact mul_inv_eq_iff_eq_mul.mpr hu
  -- Conjugation by the witness carries `C_G(g)` isomorphically onto `C_G(h)`.
  let φ :
      Subgroup.centralizer ({g} : Set G) ≃*
        Subgroup.centralizer ({(u : G) * g * (u : G)⁻¹} : Set G) :=
    { toFun := fun x ↦
        ⟨(u : G) * x * (u : G)⁻¹, by
          have hx : (x : G) * g = g * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G) * t * (u : G)⁻¹) hx⟩
      invFun := fun x ↦
        ⟨(u : G)⁻¹ * x * (u : G), by
          have hx :
              (x : G) * ((u : G) * g * (u : G)⁻¹) =
                ((u : G) * g * (u : G)⁻¹) * x := by
            exact (Subgroup.mem_centralizer_singleton_iff).1 x.2
          simpa [Subgroup.mem_centralizer_singleton_iff, mul_assoc] using
            congrArg (fun t => (u : G)⁻¹ * t * (u : G)) hx⟩
      left_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      right_inv := fun x ↦ Subtype.ext <| by
        simp [mul_assoc]
      map_mul' := fun x y ↦ Subtype.ext <| by
        simp [mul_assoc] }
  have hcard :
      Nat.card (Subgroup.centralizer ({g} : Set G)) =
        Nat.card (Subgroup.centralizer ({(u : G) * g * (u : G)⁻¹} : Set G)) := by
    simpa using Nat.card_congr φ.toEquiv
  simpa [hh] using hcard

/-- Helper for Exercise 18-18.3-2: inverting a conjugacy class does not change the order of the
centralizer of a representative. This isolates the only stable class-level datum needed to repair
the remaining `s⁻¹` pairing convention in Serre's orthogonality formula. -/
theorem ConjClasses.centralizerCard_inv
    (c : ConjClasses G) :
    ConjClasses.centralizerCard c⁻¹ = ConjClasses.centralizerCard c := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  let h : G := Classical.choose (ConjClasses.mk_surjective c⁻¹)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  have hh : ConjClasses.mk h = c⁻¹ := Classical.choose_spec (ConjClasses.mk_surjective c⁻¹)
  have hhgInv : ConjClasses.mk h = ConjClasses.mk g⁻¹ := by
    calc
      ConjClasses.mk h = c⁻¹ := hh
      _ = (ConjClasses.mk g)⁻¹ := by rw [hg]
      _ = ConjClasses.mk g⁻¹ := by simp [ConjClasses.inv_mk]
  have hconj : IsConj h g⁻¹ := (ConjClasses.mk_eq_mk_iff_isConj).1 hhgInv
  have hcent :
      Subgroup.centralizer ({g⁻¹} : Set G) = Subgroup.centralizer ({g} : Set G) := by
    ext x
    have hcomm : x * g⁻¹ = g⁻¹ * x ↔ x * g = g * x := by
      constructor
      · intro hx
        have hx' : x = g⁻¹ * x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g) hx
        have hx'' : g * x = x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => g * t) hx'
        simpa [eq_comm] using hx''
      · intro hx
        have hx' : x = g * x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hx
        have hx'' : g⁻¹ * x = x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => g⁻¹ * t) hx'
        simpa [eq_comm] using hx''
    simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm
  -- Compare the chosen representative of `c⁻¹` with `g⁻¹`, then use the equality
  -- `C_G(g⁻¹) = C_G(g)` to return to the original class.
  calc
    ConjClasses.centralizerCard c⁻¹ =
        Nat.card (Subgroup.centralizer ({h} : Set G)) := by
          simp [ConjClasses.centralizerCard, h]
    _ = Nat.card (Subgroup.centralizer ({g⁻¹} : Set G)) :=
        nat_card_centralizer_eq_of_isConj hconj
    _ = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
          simp [hcent]
    _ = ConjClasses.centralizerCard c := by
          simp [ConjClasses.centralizerCard, g]

/-- Helper for Exercise 18-18.3-2: the inverse of a `p`-regular conjugacy class is again
`p`-regular. This lets the source proof keep the `s⁻¹` pairing convention explicit. -/
noncomputable def inversePRegularConjClass
    (c : PRegularConjClass G p) : PRegularConjClass G p :=
  ⟨c.1⁻¹, by
    intro x hx
    have hxmk : ConjClasses.mk x = c.1⁻¹ :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hx
    have hxinv : ConjClasses.mk x⁻¹ = c.1 := by
      simpa [ConjClasses.inv_mk] using congrArg Inv.inv hxmk
    have hxinv_mem : x⁻¹ ∈ c.1.carrier :=
      ConjClasses.mem_carrier_iff_mk_eq.mpr hxinv
    have hxinv_reg : IsPRegular p x⁻¹ := c.2 _ hxinv_mem
    simpa [IsPRegular, orderOf_inv] using hxinv_reg⟩

/-- Helper for Exercise 18-18.3-2: forgetting the inverse regular class recovers the inverse
ambient conjugacy class. -/
@[simp] theorem inversePRegularConjClass_val
    (c : PRegularConjClass G p) :
    ((inversePRegularConjClass (p := p) c : PRegularConjClass G p) : ConjClasses G) = c.1⁻¹ := by
  rfl

/-- Helper for Exercise 18-18.3-2: inverting a regular class twice returns the original class. -/
@[simp] theorem inversePRegularConjClass_involutive
    (c : PRegularConjClass G p) :
    inversePRegularConjClass (p := p) (inversePRegularConjClass (p := p) c) = c := by
  apply Subtype.ext
  simp [inversePRegularConjClass]

/-- Helper for Exercise 18-18.3-2: the centralizer `p`-part is unchanged by inverting a regular
conjugacy class. -/
@[simp] theorem ConjClasses.centralizerPPart_inv
    (c : ConjClasses G) :
    ConjClasses.centralizerPPart p c⁻¹ = ConjClasses.centralizerPPart p c := by
  let g : G := Classical.choose (ConjClasses.mk_surjective c)
  have hg : ConjClasses.mk g = c := Classical.choose_spec (ConjClasses.mk_surjective c)
  have hgInv : ConjClasses.mk g⁻¹ = c⁻¹ := by
    simpa [ConjClasses.inv_mk] using congrArg Inv.inv hg
  have hcent :
      Subgroup.centralizer ({g⁻¹} : Set G) = Subgroup.centralizer ({g} : Set G) := by
    ext x
    have hcomm : x * g⁻¹ = g⁻¹ * x ↔ x * g = g * x := by
      constructor
      · intro hx
        have hx' : x = g⁻¹ * x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g) hx
        have hx'' : g * x = x * g := by
          simpa [mul_assoc] using congrArg (fun t : G => g * t) hx'
        simpa [eq_comm] using hx''
      · intro hx
        have hx' : x = g * x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => t * g⁻¹) hx
        have hx'' : g⁻¹ * x = x * g⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : G => g⁻¹ * t) hx'
        simpa [eq_comm] using hx''
    simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm
  calc
    ConjClasses.centralizerPPart p c⁻¹ = Representation.centralizerPPart p g⁻¹ := by
      rw [← hgInv, ConjClasses.centralizerPPart_mk]
    _ = Representation.centralizerPPart p g := by
      simp [Representation.centralizerPPart, hcent]
    _ = ConjClasses.centralizerPPart p c := by
      rw [← hg, ConjClasses.centralizerPPart_mk]

/-- Helper for Exercise 18-18.3-2: the full regular indicator is the prime-to-`p` factor times
the scaled indicator. This is the source-faithful normalization step used before the two dual
expansions. -/
theorem full_regular_indicator_eq_ordCompl_smul_scaled_regular_indicator
    (c : PRegularConjClass G p) :
    Pi.single c (algebraMap A K (ConjClasses.centralizerCard c.1 : A)) =
      (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) •
        scaled_regular_indicator (p := p) (A := A) (K := K) c := by
  classical
  ext c'
  by_cases h : c' = c
  · subst c'
    -- At the distinguished class, rewrite the full centralizer order using the `p`-part split.
    have hcard :
        ConjClasses.centralizerCard c.1 =
          ConjClasses.centralizerPPart p c.1 *
            ordCompl[p] (ConjClasses.centralizerCard c.1) :=
      ConjClasses.centralizerCard_eq_centralizerPPart_mul_ordCompl
        (p := p) (G := G) c.1
    have hcast :
        algebraMap A K (ConjClasses.centralizerCard c.1 : A) =
          algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
            algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := by
      simpa [map_mul] using congrArg (fun n : ℕ => algebraMap A K (n : A)) hcard
    calc
      full_regular_indicator c c =
          algebraMap A K (ConjClasses.centralizerCard c.1 : A) := by
            simp [full_regular_indicator]
      _ =
          algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) *
            algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) := hcast
      _ =
          algebraMap A K (ordCompl[p] (ConjClasses.centralizerCard c.1) : A) *
            algebraMap A K (ConjClasses.centralizerPPart p c.1 : A) := by
              rw [mul_comm]
      _ =
          ((ordCompl[p] (ConjClasses.centralizerCard c.1) : A) •
            scaled_regular_indicator (p := p) (A := A) (K := K) c) c := by
              simp [scaled_regular_indicator, Algebra.smul_def]
  · -- Off the distinguished class, both point masses vanish.
    simp [full_regular_indicator, scaled_regular_indicator, h]
end ProjectiveCharacterCriterion

end Representation
