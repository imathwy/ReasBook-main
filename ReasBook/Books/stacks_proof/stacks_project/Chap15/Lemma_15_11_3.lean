import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap10.Definition_10_32_1
import stacks_proof.stacks_project.Chap10.Lemma_10_19_1
import stacks_proof.stacks_project.Chap10.Lemma_10_138_17
import stacks_proof.stacks_project.Chap10.Lemma_10_32_4
import stacks_proof.stacks_project.Chap15.Lemma_15_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open CommRingCat
open Polynomial

universe u

section

variable (F : SequentialInverseSystem CommRingCat.{u})

/-- Helper for Lemma 15.11.3: long transition maps factor through every intermediate stage. -/
theorem transitionMap_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  -- Proof comment: the unique arrow `k ⟶ i` in `ℕᵒᵖ` factors through the intermediate stage `j`.
  have hh :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 15.11.3: the underlying commutative ring of the inverse limit. -/
noncomputable abbrev limitRing : Type u :=
  ((limit F : CommRingCat) : Type u)

/-- Helper for Lemma 15.11.3: a point of the inverse limit ring determines its compatible family
of stagewise coordinates. -/
noncomputable def underlying_sections_of_limit (x : limitRing (F := F)) :
    (F ⋙ forget CommRingCat).sections :=
  Types.limitEquivSections _ ((preservesLimitIso (forget CommRingCat) F).hom x)

/-- Helper for Lemma 15.11.3: a compatible family of stagewise coordinates defines an element of
the inverse limit ring. -/
noncomputable def limit_of_underlying_sections
    (s : (F ⋙ forget CommRingCat).sections) : limitRing (F := F) :=
  (preservesLimitIso (forget CommRingCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget CommRingCat)).symm s)

/-- Helper for Lemma 15.11.3: the compatible-family description of a limit point is injective. -/
lemma underlying_sections_of_limit_injective :
    Function.Injective (underlying_sections_of_limit (F := F)) := by
  intro x y hxy
  -- Proof comment: compare in the underlying `Type`-valued limit and invert the preserved-limit
  -- isomorphism.
  have hlimit :
      (preservesLimitIso (forget CommRingCat) F).hom x =
        (preservesLimitIso (forget CommRingCat) F).hom y := by
    exact (Types.limitEquivSections (F ⋙ forget CommRingCat)).injective hxy
  simpa using congrArg ((preservesLimitIso (forget CommRingCat) F).inv) hlimit

/-- Helper for Lemma 15.11.3: reading off the compatible family of a limit element recovers each
limit projection. -/
lemma limit_π_underlying_sections_of_limit (x : limitRing (F := F)) (j : ℕᵒᵖ) :
    (limit.π F j).hom x = (underlying_sections_of_limit (F := F) x).val j := by
  -- Proof comment: first move to the underlying `Type`-valued limit, then use the explicit
  -- sections equivalence.
  let t : limit (F ⋙ forget CommRingCat) :=
    (preservesLimitIso (forget CommRingCat) F).hom x
  have hπ :
      limit.π (F ⋙ forget CommRingCat) j t = (limit.π F j).hom x := by
    exact congrArg (fun g => g x) (preservesLimitIso_hom_π (forget CommRingCat) F j)
  have ht :
      (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm
          (underlying_sections_of_limit (F := F) x) = t := by
    simpa [underlying_sections_of_limit, t] using
      (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm_apply_apply
        ((preservesLimitIso (forget CommRingCat) F).hom x)
  have hsections :
      limit.π (F ⋙ forget CommRingCat) j
          ((Types.limitEquivSections (F ⋙ forget CommRingCat)).symm
            (underlying_sections_of_limit (F := F) x)) =
        (underlying_sections_of_limit (F := F) x).val j := by
    simpa using
      Types.limitEquivSections_symm_apply (F ⋙ forget CommRingCat)
        (underlying_sections_of_limit (F := F) x) j
  exact hπ.symm.trans (ht ▸ hsections)

/-- Helper for Lemma 15.11.3: the limit point built from a compatible family has the expected
coordinate at every stage. -/
lemma limit_π_limit_of_underlying_sections
    (s : (F ⋙ forget CommRingCat).sections) (j : ℕᵒᵖ) :
    (limit.π F j).hom (limit_of_underlying_sections (F := F) s) = s.val j := by
  -- Proof comment: again pass through the underlying `Type`-valued limit and read off the chosen
  -- section coordinate.
  let t : limit (F ⋙ forget CommRingCat) :=
    (Types.limitEquivSections (F ⋙ forget CommRingCat)).symm s
  have hπ :
      (limit.π F j).hom ((preservesLimitIso (forget CommRingCat) F).inv t) =
        limit.π (F ⋙ forget CommRingCat) j t := by
    exact congrArg (fun g => g t) (preservesLimitIso_inv_π (forget CommRingCat) F j)
  simpa [limit_of_underlying_sections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget CommRingCat) s j)

/-- Helper for Lemma 15.11.3: if every projection of an element of the inverse limit ring is a
unit, then the element itself is a unit. -/
lemma isUnit_of_projection_isUnit (x : limitRing (F := F))
    (hx : ∀ j : ℕᵒᵖ, IsUnit ((limit.π F j).hom x)) :
    IsUnit x := by
  classical
  let u : ∀ j : ℕᵒᵖ, Units (F.obj j) := fun j ↦ (hx j).unit
  have hu_spec : ∀ j : ℕᵒᵖ, (((u j : Units (F.obj j)) : F.obj j)) = (limit.π F j).hom x := by
    intro j
    exact IsUnit.unit_spec (hx j)
  have hu_compat : ∀ ⦃j k : ℕᵒᵖ⦄ (f : j ⟶ k), Units.map (F.map f).hom (u j) = u k := by
    intro j k f
    apply Units.ext
    -- Proof comment: the chosen units are equal because both values are the projected image of
    -- `x` at stage `k`.
    calc
      (((Units.map (F.map f).hom (u j) : Units (F.obj k)) : F.obj k)) =
          (F.map f).hom (((u j : Units (F.obj j)) : F.obj j)) := rfl
      _ = (F.map f).hom ((limit.π F j).hom x) := by rw [hu_spec j]
      _ = (limit.π F k).hom x := by
        simpa using congrArg (fun g => g.hom x) (limit.w F f)
      _ = ((u k : Units (F.obj k)) : F.obj k) := by rw [hu_spec k]
  have huinv_compat :
      ∀ ⦃j k : ℕᵒᵖ⦄ (f : j ⟶ k), (F.map f).hom ↑((u j)⁻¹) = ↑((u k)⁻¹) := by
    intro j k f
    -- Proof comment: once the units themselves are compatible, their inverses are compatible too.
    simpa using
      congrArg (fun z : Units (F.obj k) => ((z⁻¹ : Units (F.obj k)) : F.obj k)) (hu_compat f)
  let s : (F ⋙ forget CommRingCat).sections :=
    ⟨fun j ↦ (((u j)⁻¹ : Units (F.obj j)) : F.obj j), fun {_ _} f ↦ huinv_compat f⟩
  let y : limitRing (F := F) := limit_of_underlying_sections (F := F) s
  have hxy : x * y = 1 := by
    apply underlying_sections_of_limit_injective (F := F)
    apply Subtype.ext
    funext j
    -- Proof comment: each projection multiplies `x` with the reassembled inverse to `1`.
    have hcoord :
        (underlying_sections_of_limit (F := F) (x * y)).val j = 1 := by
      calc
      (underlying_sections_of_limit (F := F) (x * y)).val j = (limit.π F j).hom (x * y) := by
        exact (limit_π_underlying_sections_of_limit (F := F) (x := x * y) (j := j)).symm
      _ = (limit.π F j).hom x * (limit.π F j).hom y := by rw [map_mul]
      _ = (limit.π F j).hom x * (((u j)⁻¹ : Units (F.obj j)) : F.obj j) := by
        rw [limit_π_limit_of_underlying_sections]
      _ = (((u j : Units (F.obj j)) : F.obj j)) * (((u j)⁻¹ : Units (F.obj j)) : F.obj j) := by
        rw [hu_spec j]
      _ = 1 := by simp
    have hone :
        (underlying_sections_of_limit (F := F) 1).val j = 1 := by
      simpa [map_one] using
        (limit_π_underlying_sections_of_limit (F := F) (x := 1) (j := j)).symm
    exact hcoord.trans hone.symm
  have hyx : y * x = 1 := by
    apply underlying_sections_of_limit_injective (F := F)
    apply Subtype.ext
    funext j
    -- Proof comment: the same coordinatewise inverse identity gives the opposite product.
    have hcoord :
        (underlying_sections_of_limit (F := F) (y * x)).val j = 1 := by
      calc
      (underlying_sections_of_limit (F := F) (y * x)).val j = (limit.π F j).hom (y * x) := by
        exact (limit_π_underlying_sections_of_limit (F := F) (x := y * x) (j := j)).symm
      _ = (limit.π F j).hom y * (limit.π F j).hom x := by rw [map_mul]
      _ = (((u j)⁻¹ : Units (F.obj j)) : F.obj j) * (limit.π F j).hom x := by
        rw [limit_π_limit_of_underlying_sections]
      _ = (((u j)⁻¹ : Units (F.obj j)) : F.obj j) * (((u j : Units (F.obj j)) : F.obj j)) := by
        rw [hu_spec j]
      _ = 1 := by simp
    have hone :
        (underlying_sections_of_limit (F := F) 1).val j = 1 := by
      simpa [map_one] using
        (limit_π_underlying_sections_of_limit (F := F) (x := 1) (j := j)).symm
    exact hcoord.trans hone.symm
  exact isUnit_iff_exists.mpr ⟨y, hxy, hyx⟩

/-- Helper for Lemma 15.11.3: every long transition kernel is locally nilpotent when the stepwise
kernels are locally nilpotent. -/
lemma transitionMap_ker_isLocallyNilpotent
    (n : ℕ)
    (h_locnil : ∀ r : ℕ, RingHom.ker (F.stepMap r).hom ≤ nilradical _) :
    ∀ {m : ℕ} (hnm : n ≤ m),
      RingHom.ker (F.transitionMap hnm).hom ≤ nilradical (F.obj (Opposite.op m)) := by
  intro m hnm
  induction hnm with
  | refl =>
      intro x hx
      -- Proof comment: the identity transition has zero kernel, so every kernel element is
      -- already nilpotent.
      rw [mem_nilradical]
      exact ⟨1, by simpa [SequentialInverseSystem.transitionMap] using hx⟩
  | @step m hnm ih =>
      intro x hx
      -- Proof comment: the image of `x` in stage `m` lies in the previous long kernel, so some
      -- power of `x` lands in the step kernel, where local nilpotence finishes the argument.
      have hx_image_mem :
          (F.stepMap m).hom x ∈ RingHom.ker (F.transitionMap hnm).hom := by
        change (F.transitionMap hnm).hom ((F.stepMap m).hom x) = 0
        have hcomp :
            F.transitionMap (Nat.le_trans hnm (Nat.le_succ m)) =
              F.stepMap m ≫ F.transitionMap hnm := by
          simpa [SequentialInverseSystem.stepMap] using
            transitionMap_comp (F := F) hnm (Nat.le_succ m)
        simpa [hcomp] using hx
      have hx_image_nil :
          IsNilpotent ((F.stepMap m).hom x) :=
        (Ideal.isLocallyNilpotent_iff (RingHom.ker (F.transitionMap hnm).hom)).mp ih
          _ hx_image_mem
      rcases hx_image_nil with ⟨N, hN⟩
      have hx_pow_mem : x ^ N ∈ RingHom.ker (F.stepMap m).hom := by
        change (F.stepMap m).hom (x ^ N) = 0
        simpa [RingHom.map_pow] using hN
      have hx_pow_nil : IsNilpotent (x ^ N) :=
        (Ideal.isLocallyNilpotent_iff (RingHom.ker (F.stepMap m).hom)).mp (h_locnil m)
          _ hx_pow_mem
      rcases hx_pow_nil with ⟨M, hM⟩
      rw [mem_nilradical]
      exact ⟨N * M, by simpa [pow_mul] using hM⟩

/-- Helper for Lemma 15.11.3: every element of `1 + ker(limit → A_n)` is a unit in the inverse
limit ring. -/
lemma isUnit_one_add_of_mem_limitProjectionKer
    (n : ℕ)
    (h_locnil : ∀ r : ℕ, RingHom.ker (F.stepMap r).hom ≤ nilradical _)
    (x : limitRing (F := F))
    (hx : x ∈ RingHom.ker (limit.π F (Opposite.op n)).hom) :
    IsUnit (1 + x) := by
  refine isUnit_of_projection_isUnit (F := F) (x := 1 + x) fun j ↦ ?_
  by_cases hnj : n ≤ j.unop
  · -- Proof comment: in the tail, the `j`-th coordinate is congruent to `1` modulo the locally
    -- nilpotent long kernel `ker(A_j → A_n)`, so Lemma `10.32.4` makes it a unit.
    have hproj_mem :
        (limit.π F j).hom x ∈ RingHom.ker (F.transitionMap hnj).hom := by
      change (F.transitionMap hnj).hom ((limit.π F j).hom x) = 0
      have hcomp :
          limit.π F j ≫ F.transitionMap hnj = limit.π F (Opposite.op n) := by
        simpa [SequentialInverseSystem.transitionMap] using
          limit.w F ((homOfLE hnj).op)
      have hx_zero :
          (limit.π F (Opposite.op n)).hom x = 0 := by
        simpa using hx
      simpa [hx_zero] using congrArg (fun f => f.hom x) hcomp
    have hloc :
        RingHom.ker (F.transitionMap hnj).hom ≤ nilradical (F.obj j) :=
      transitionMap_ker_isLocallyNilpotent (F := F) n h_locnil hnj
    have hquot :
        Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnj).hom)
            ((limit.π F j).hom (1 + x)) = 1 := by
      rw [map_add, map_one]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hproj_mem]
    have hunit_quot :
        IsUnit
          (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnj).hom)
            ((limit.π F j).hom (1 + x))) := by
      rw [hquot]
      exact isUnit_one
    exact
      (isUnit_iff_isUnit_quotient_mk_of_isLocallyNilpotent
        (RingHom.ker (F.transitionMap hnj).hom) hloc).2
        hunit_quot
  · -- Proof comment: before stage `n`, compatibility with the vanishing `n`-th coordinate forces
    -- the `j`-th coordinate of `x` itself to vanish.
    have hjn : j.unop ≤ n := Nat.le_of_not_ge hnj
    have hcomp :
        limit.π F (Opposite.op n) ≫ F.transitionMap hjn = limit.π F j := by
      simpa [SequentialInverseSystem.transitionMap] using
        limit.w F ((homOfLE hjn).op)
    have hx_zero :
        (limit.π F (Opposite.op n)).hom x = 0 := by
      simpa using hx
    have hj_zero : (limit.π F j).hom x = 0 := by
      have hcomp_apply :
          (limit.π F j).hom x =
            (F.transitionMap hjn).hom ((limit.π F (Opposite.op n)).hom x) := by
        simpa using congrArg (fun f => f.hom x) hcomp.symm
      simpa [hx_zero] using hcomp_apply
    simpa [map_add, hj_zero]

/-- Helper for Lemma 15.11.3: over a Jacobson ideal, two roots that are congruent modulo the
ideal coincide once the derivative at one of them is a unit modulo the ideal. -/
private lemma roots_eq_of_sub_mem_ideal_and_derivative_isUnit_mod_ideal
    {A : Type u} [CommRing A] (J : Ideal A) (hJac : J ≤ Ring.jacobson A) {f : A[X]} {a b : A}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hd : b - a ∈ J)
    (hder : IsUnit ((Ideal.Quotient.mk J) (f.derivative.eval a))) :
    a = b := by
  let d := b - a
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion f a d
  have hfactor :
      f.derivative.eval a * d + c * d ^ 2 = (f.derivative.eval a + c * d) * d := by
    -- Proof comment: factor the linear and quadratic correction terms by the common difference.
    dsimp [d]
    ring
  have hsum : 0 = f.derivative.eval a * d + c * d ^ 2 := by
    -- Proof comment: the binomial expansion collapses because both evaluation endpoints are
    -- roots.
    simpa [d, ha.eq_zero, hb.eq_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  have hrootEq : (f.derivative.eval a + c * d) * d = 0 := by
    rw [hfactor] at hsum
    exact hsum.symm
  have hd' : d ∈ J := by
    simpa [d] using hd
  have hcd : c * d ∈ J := by
    simpa [mul_comm] using J.mul_mem_left c hd'
  let _ : IsLocalHom (Ideal.Quotient.mk J) :=
    isLocalHom_of_le_jacobson_bot J (by simpa [Ideal.jacobson_bot] using hJac)
  have hunit : IsUnit (f.derivative.eval a + c * d) := by
    -- Proof comment: the quadratic correction term vanishes modulo `J`, so the derivative remains
    -- a unit after adding it.
    apply IsUnit.of_map (Ideal.Quotient.mk J)
    have hzero : (Ideal.Quotient.mk J) (c * d) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcd
    rw [map_add, hzero, add_zero]
    exact hder
  have hd_zero : d = 0 := hunit.mul_right_eq_zero.mp hrootEq
  exact (sub_eq_zero.mp (by simpa [d] using hd_zero)).symm

/-- Helper for Lemma 15.11.3: if `p(a)` is a unit, then `X - a` and `p` are coprime. -/
private theorem isCoprime_X_sub_C_of_isUnit_eval
    {R : Type u} [CommRing R] (a : R) (p : R[X]) (hp : IsUnit (p.eval a)) :
    IsCoprime (X - C a) p := by
  have hroot : (p - C (p.eval a)).IsRoot a := by
    -- Proof comment: subtracting the constant value `p(a)` forces the new polynomial to vanish
    -- at `a`.
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub]
    simp
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
  rcases hp with ⟨u, hu⟩
  refine ⟨-q * C (((u⁻¹ : Units R) : R)), C (((u⁻¹ : Units R) : R)), ?_⟩
  -- Proof comment: the Euclidean remainder identity writes a unit-valued constant combination of
  -- `X - C a` and `p`, which is then normalized to `1`.
  calc
    (-q * C (((u⁻¹ : Units R) : R))) * (X - C a) + C (((u⁻¹ : Units R) : R)) * p =
        C (((u⁻¹ : Units R) : R)) * (p - q * (X - C a)) := by
      ring
    _ = C (((u⁻¹ : Units R) : R)) * C (p.eval a) := by
      rw [show p - q * (X - C a) = C (p.eval a) by
        calc
          p - q * (X - C a) = p - ((X - C a) * q) := by rw [mul_comm]
          _ = p - (p - C (p.eval a)) := by rw [hq]
          _ = C (p.eval a) := by ring]
    _ = 1 := by
      rw [← hu]
      rw [← Polynomial.C_mul]
      simp

/-- Helper for Lemma 15.11.3: dividing a polynomial by `X - C a` at a root `a` evaluates to the
derivative at `a`. -/
private theorem divByMonic_X_sub_C_eval_eq_derivative_eval
    {R : Type u} [CommRing R] (p : R[X]) {a : R} (ha : p.IsRoot a) :
    (p /ₘ (X - C a)).eval a = p.derivative.eval a := by
  let q : R[X] := p /ₘ (X - C a)
  have hfactor : (X - C a) * q = p := by
    simpa [q] using (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha)
  have hderiv :=
    congrArg (fun r : R[X] => r.derivative.eval a) hfactor
  -- Proof comment: after differentiating the linear factorization, the `X - C a` term vanishes
  -- at `a`, leaving only the cofactor value.
  simpa [q, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] using hderiv

/-- Helper for Lemma 15.11.3: a monic polynomial of degree `1` has the expected explicit root. -/
private theorem isRoot_neg_coeff_zero_of_monic_natDegree_one
    {R : Type u} [CommRing R] {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = 1) :
    p.IsRoot (-p.coeff 0) := by
  have hcoeff : p.coeff 1 = 1 := by
    simpa [hdeg] using hp.coeff_natDegree
  have hshape : p = X + C (p.coeff 0) := by
    calc
      p = C (p.coeff 1) * X + C (p.coeff 0) := by
        exact Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
      _ = X + C (p.coeff 0) := by rw [hcoeff]; simp
  -- Proof comment: once the degree-one polynomial is normalized to `X + c`, its root is `-c`.
  rw [Polynomial.IsRoot.def, hshape]
  simp

/-- Helper for Lemma 15.11.3: if a monic polynomial maps to `X - C a`, then it already has degree
`1`. -/
private theorem natDegree_one_of_monic_map_eq_X_sub_C
    {R S : Type u} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {p : R[X]} (hp : p.Monic) {a : S}
    (hmap : p.map φ = X - C a) :
    p.natDegree = 1 := by
  have hdeg : p.degree = 1 := by
    -- Proof comment: mapping a monic polynomial preserves the degree because its leading
    -- coefficient stays nonzero.
    calc
      p.degree = (p.map φ).degree := by
        symm
        exact Polynomial.degree_map_eq_of_leadingCoeff_ne_zero φ (by
          simpa [hp.leadingCoeff] using (one_ne_zero : (1 : S) ≠ 0))
      _ = (X - C a).degree := by rw [hmap]
      _ = 1 := by simpa using Polynomial.degree_X_sub_C a
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- Helper for Lemma 15.11.3: if a locally nilpotent ideal has a subsingleton quotient, then the
base ring is already subsingleton. -/
private theorem subsingleton_of_subsingleton_quotient_of_isLocallyNilpotent
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    (hquot : Subsingleton (R ⧸ J)) :
    Subsingleton R := by
  have htop : J = ⊤ := by
    ext x
    constructor
    · intro hx
      simp
    · intro _
      have hxzero : Ideal.Quotient.mk J x = 0 := Subsingleton.elim _ _
      exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero
  have hnil : IsNilpotent (1 : R) :=
    (Ideal.isLocallyNilpotent_iff J).mp hJ 1 (by simpa [htop])
  rcases hnil with ⟨n, hn⟩
  -- Proof comment: once `1` is nilpotent, the ring collapses to the zero ring.
  refine ⟨fun x y ↦ ?_⟩
  have hone : (1 : R) = 0 := by simpa using hn
  calc
    x = x * 1 := by simp
    _ = x * 0 := by rw [hone]
    _ = 0 := by simp
    _ = y * 0 := by simp
    _ = y * 1 := by rw [hone]
    _ = y := by simp

/-- Helper for Lemma 15.11.3: an étale quotient equivalence over a locally nilpotent ideal
descends to an actual section over the base ring. -/
private theorem exists_section_of_etale_quotient_equiv_of_locally_nilpotent
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    (e : (R ⧸ J) ≃ₐ[R ⧸ J] (R' ⧸ Ideal.map (algebraMap R R') J)) :
    ∃ σ : R' →ₐ[R] R,
      (Ideal.Quotient.mkₐ R J).comp σ =
        ((e.symm.toAlgHom).restrictScalars R).comp
          (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R R') J)) := by
  let J' : Ideal R' := Ideal.map (algebraMap R R') J
  let σbar : R' →ₐ[R] R ⧸ J :=
    ((e.symm.toAlgHom).restrictScalars R).comp (Ideal.Quotient.mkₐ R J')
  obtain ⟨σ, hσ⟩ :=
    Algebra.smooth_exists_lift_of_quotient_by_locally_nilpotent
      (R := R) (S := R') (A := R) J hJ σbar
  -- Proof comment: the smooth lifting theorem produces exactly the desired section after
  -- packaging the quotient equivalence as a map into `R ⧸ J`.
  exact ⟨σ, by simpa [J', σbar] using hσ⟩

/-- Helper for Lemma 15.11.3: over a nontrivial quotient, a monic polynomial reducing to
`X - C b` already has a root lifting `b`. -/
private theorem exists_root_of_monic_mod_X_sub_C
    {R : Type u} [CommRing R] (J : Ideal R) [Nontrivial (R ⧸ J)]
    {g : R[X]} (hg : g.Monic) {b : R ⧸ J}
    (hmap : g.map (Ideal.Quotient.mk J) = X - C b) :
    ∃ a : R, g.IsRoot a ∧ Ideal.Quotient.mk J a = b := by
  refine ⟨-g.coeff 0, ?_, ?_⟩
  · -- Proof comment: the quotient identity forces `g` to have degree `1`, so its explicit root
    -- is the negated constant coefficient.
    exact
      isRoot_neg_coeff_zero_of_monic_natDegree_one hg
        (natDegree_one_of_monic_map_eq_X_sub_C (Ideal.Quotient.mk J) hg hmap)
  · -- Proof comment: comparing constant coefficients identifies the lifted root with the chosen
    -- residue class `b`.
    have hcoeff0 : Ideal.Quotient.mk J (g.coeff 0) = -b := by
      simpa using congrArg (fun p : (R ⧸ J)[X] => p.coeff 0) hmap
    calc
      Ideal.Quotient.mk J (-g.coeff 0) = -Ideal.Quotient.mk J (g.coeff 0) := by simp
      _ = -(-b) := by rw [hcoeff0]
      _ = b := by simp

/-- Helper for Lemma 15.11.3: a locally nilpotent ideal satisfies the Hensel root-lifting field
by the textbook factorization-and-descent route. -/
private theorem exists_hensel_root_of_locally_nilpotent_ideal
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.IsLocallyNilpotent)
    {f : R[X]} (hf : f.Monic) (a₀ : R) (ha₀ : f.eval a₀ ∈ J)
    (hderiv : IsUnit ((Ideal.Quotient.mk J) (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ J := by
  classical
  by_cases hquot : Subsingleton (R ⧸ J)
  · let _ : Subsingleton R :=
      subsingleton_of_subsingleton_quotient_of_isLocallyNilpotent J hJ hquot
    refine ⟨0, ?_, ?_⟩
    · -- Proof comment: in the zero ring every evaluation vanishes, so any element is a root.
      exact (Polynomial.IsRoot.def).2 (Subsingleton.elim _ _)
    · -- Proof comment: the congruence condition is automatic in a subsingleton ring.
      have hdiff : (0 : R) - a₀ = 0 := Subsingleton.elim _ _
      simpa [hdiff] using (J.zero_mem : (0 : R) ∈ J)
  · let _ : Nontrivial (R ⧸ J) := not_subsingleton_iff_nontrivial.mp hquot
    let abar : R ⧸ J := Ideal.Quotient.mk J a₀
    let fbar : (R ⧸ J)[X] := f.map (Ideal.Quotient.mk J)
    let gbar : (R ⧸ J)[X] := X - C abar
    let hbar : (R ⧸ J)[X] := fbar /ₘ gbar
    have hrootbar : fbar.IsRoot abar := by
      -- Proof comment: reducing `f(a₀)` modulo `J` gives the simple residue root `ā`.
      exact (Polynomial.IsRoot.def).2 <| by
        simpa [fbar, abar, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_apply] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr ha₀ :
            Ideal.Quotient.mk J (Polynomial.eval a₀ f) = 0)
    have hfactorbar : fbar = gbar * hbar := by
      -- Proof comment: the residue root forces the standard linear factorization by `X - C ā`.
      simpa [fbar, gbar, hbar] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hrootbar).symm
    have hgbar : gbar.Monic := by
      simpa [gbar] using (monic_X_sub_C abar)
    have hhbar : hbar.Monic := by
      -- Proof comment: the cofactor stays monic because `f̄` and `X - C ā` are both monic.
      have hfbar : fbar.Monic := by
        simpa [fbar] using hf.map (Ideal.Quotient.mk J)
      rw [hfactorbar] at hfbar
      exact (monic_X_sub_C abar).of_mul_monic_left hfbar
    have hderivbar :
        IsUnit (hbar.eval abar) := by
      -- Proof comment: at the residue root, the cofactor value is exactly the residue derivative.
      rw [show hbar.eval abar = fbar.derivative.eval abar by
            simpa [fbar, gbar, hbar] using
              divByMonic_X_sub_C_eval_eq_derivative_eval fbar hrootbar]
      have hmap_deriv :
          fbar.derivative.eval abar =
            (Ideal.Quotient.mk J) (f.derivative.eval a₀) := by
        simpa [fbar, abar, Polynomial.derivative_map, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_at_apply]
      rw [hmap_deriv]
      exact hderiv
    have hcoprime : IsCoprime gbar hbar := by
      simpa [gbar] using isCoprime_X_sub_C_of_isUnit_eval abar hbar hderivbar
    obtain ⟨R', _, _, _, e, g', h', hg', hh', hfactor', hgred, _⟩ :=
      Algebra.exists_etale_lift_factorization_of_monic_mod_ideal
        (A := R) J f gbar hbar hf hgbar hhbar hfactorbar hcoprime
    let J' : Ideal R' := Ideal.map (algebraMap R R') J
    let _ : Nontrivial (R' ⧸ J') := Function.Injective.nontrivial e.injective
    have hgred' : g'.map (Ideal.Quotient.mk J') = X - C (e abar) := by
      calc
        g'.map (Ideal.Quotient.mk J') = gbar.map e.toRingHom := hgred.symm
        _ = X - C (e abar) := by simp [gbar]
    obtain ⟨σ, hσ⟩ :=
      exists_section_of_etale_quotient_equiv_of_locally_nilpotent
        (J := J) hJ e
    obtain ⟨a', ha'root, ha'quot⟩ :=
      exists_root_of_monic_mod_X_sub_C (J := J') hg' hgred'
    let a : R := σ a'
    refine ⟨a, ?_, ?_⟩
    · have hmapRoot : (f.map (algebraMap R R')).IsRoot a' := by
        -- Proof comment: the lifted linear factor `g'` divides the lifted polynomial `f`.
        rw [Polynomial.IsRoot.def, hfactor', Polynomial.eval_mul, Polynomial.IsRoot.def.mp ha'root]
        simp
      have hrootMap :
          (Polynomial.map σ.toRingHom (f.map (algebraMap R R'))).IsRoot (σ a') :=
        Polynomial.IsRoot.map (f := σ.toRingHom) hmapRoot
      -- Proof comment: restricting scalars along the section collapses the coefficient map back
      -- to the original polynomial `f`.
      simpa [a, Polynomial.map_map] using hrootMap
    · have hσ_apply :
          Ideal.Quotient.mk J (σ a') = e.symm (Ideal.Quotient.mk J' a') := by
        have hσ_eval :=
          congrArg (fun φ : R' →ₐ[R] R ⧸ J => φ a') hσ
        simpa [J'] using hσ_eval
      -- Proof comment: evaluating the descended section on the lifted residue root shows that the
      -- final root is congruent to `a₀` modulo `J`.
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hσ_apply, ha'quot, AlgEquiv.symm_apply_apply]
      simp [abar]

/-- Helper for Lemma 15.11.3: a commutative ring is henselian at any locally nilpotent ideal. -/
private instance henselianRing_of_locally_nilpotent_ideal
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.IsLocallyNilpotent) :
    HenselianRing R J := by
  refine
    { jac := ?_
      is_henselian := ?_ }
  · -- Proof comment: locally nilpotent ideals lie in the nilradical, hence in the Jacobson
    -- radical.
    simpa [Ideal.jacobson_bot] using hJ.trans (nilradical_le_jacobson R)
  · -- Route correction: the source-faithful route here is to factor `f mod J` as
    -- `(X - ā) * h̄`, lift that factorization étale-locally via Lemma `15.9.5`, and then
    -- descend the resulting quotient section back to `R` with
    -- `Algebra.smooth_exists_lift_of_quotient_by_locally_nilpotent`.
    -- Proof comment: all remaining work is packaged in the exact-output Hensel root theorem
    -- above, which follows the source proof verbatim.
    intro f hf a₀ ha₀ hderiv
    exact exists_hensel_root_of_locally_nilpotent_ideal J hJ hf a₀ ha₀ hderiv

/- Domain-style sampling:
- primary domain: henselian pairs on inverse limits of commutative rings;
- sampled owner declarations of the same kind:
  `SequentialInverseSystem.stepMap`,
  `HenselianRing`,
  `henselianRing_of_isLocallyNilpotent`,
  `inverseSystem_limit_henselianRing`,
  `IsAdicComplete.henselianRing`;
- best owner abstraction: the sequential source-facing owner is `SequentialInverseSystem`, with
  `SequentialInverseSystem.stepMap` as the canonical stage-to-stage transition API; the core owner
  for the conclusion is `HenselianRing`, while the chapter-level inverse-limit owner is
  `inverseSystem_limit_henselianRing`; the locally nilpotent-kernel criterion from
  `henselianRing_of_isLocallyNilpotent` supplies the stagewise henselian ideals used in that
  inverse-limit owner;
- primitive data: the inverse system `F`, a stage `n`, and the stepwise transition hypotheses on
  `F.stepMap r`;
- derived API: henselianity of the kernel ideal of the projection `limit F → F.obj (op n)`.

Source/core/bridge triage:
- `source-facing`: the specialization to the projection-kernel ideal at a fixed stage `n`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: the sequential transition API `SequentialInverseSystem.stepMap` and the chapter
  owner `inverseSystem_limit_henselianRing`, fed by the stagewise locally nilpotent-kernel
  instances from `henselianRing_of_isLocallyNilpotent`.
-/

-- Proof sketch: fix `n`. The Jacobson-radical clause comes from the source proof's unit test:
-- if an element is `1` at stage `n`, then every later coordinate is a unit modulo the locally
-- nilpotent long kernel and every earlier coordinate is literally `1`, so the element is a unit in
-- the inverse limit. For the Hensel lifting clause, the remaining task is to lift a simple root at
-- each stage `m ≥ n`, prove those lifts are compatible, and reassemble them into a root in the
-- inverse limit.
/-- Lemma 15.11.3: if `F : SequentialInverseSystem CommRingCat` is an inverse system of rings
whose stepwise transition maps `A_{r + 1} → A_r` are surjective and have locally nilpotent
kernels, then for each `n` the pair consisting of the inverse limit `limit F` and the kernel of
the projection `limit F → F.obj (op n)` is henselian. -/
@[stacks 0CT7]
instance henselianRing_limitProjection_ker_of_surjective_of_isLocallyNilpotent
    (n : ℕ)
    (h_surj : ∀ r : ℕ, Function.Surjective (F.stepMap r).hom)
    (h_locnil : ∀ r : ℕ, RingHom.ker (F.stepMap r).hom ≤ nilradical _) :
    HenselianRing ((limit F : CommRingCat.{u}) : Type u)
      (RingHom.ker (limit.π F (Opposite.op n)).hom) :=
  by
    refine
      { jac := ?_
        is_henselian := ?_ }
    · -- Proof comment: the Jacobson clause is exactly the unit test for elements of
      -- `1 + ker(limit → A_n)`.
      simpa [Ideal.jacobson_bot] using
        (ideal_le_ring_jacobson_iff_isUnit_one_add
          (R := limitRing (F := F))
          (I := RingHom.ker (limit.π F (Opposite.op n)).hom)).2
          (fun x hx ↦ isUnit_one_add_of_mem_limitProjectionKer (F := F) n h_locnil x hx)
    · intro f hf a₀ ha₀ hderiv
      classical
      have ha₀_tail :
          ∀ m : ℕ, ∀ hnm : n ≤ m,
            (Polynomial.map ((limit.π F (Opposite.op m)).hom) f).eval
                ((limit.π F (Opposite.op m)).hom a₀) ∈
              RingHom.ker (F.transitionMap hnm).hom := by
        intro m hnm
        -- Proof comment: evaluating at stage `m` and then descending to stage `n` recovers the
        -- vanishing `n`-th coordinate of `f(a₀)`.
        change
          (F.transitionMap hnm).hom
              ((Polynomial.map ((limit.π F (Opposite.op m)).hom) f).eval
                ((limit.π F (Opposite.op m)).hom a₀)) = 0
        have hπ :
            (F.transitionMap hnm).hom
                ((Polynomial.map ((limit.π F (Opposite.op m)).hom) f).eval
                  ((limit.π F (Opposite.op m)).hom a₀)) =
              (limit.π F (Opposite.op n)).hom (Polynomial.eval a₀ f) := by
          simpa [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_apply] using
            congrArg (fun φ => φ.hom (Polynomial.eval a₀ f))
              (limit.w F ((homOfLE hnm).op))
        have ha₀_zero : (limit.π F (Opposite.op n)).hom (Polynomial.eval a₀ f) = 0 := by
          exact ha₀
        exact hπ.trans ha₀_zero
      have hderiv_tail :
          ∀ m : ℕ, ∀ hnm : n ≤ m,
            IsUnit
              ((Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnm).hom))
                (((Polynomial.map ((limit.π F (Opposite.op m)).hom) f).derivative).eval
                  ((limit.π F (Opposite.op m)).hom a₀))) := by
        intro m hnm
        -- Proof comment: the derivative unit modulo `ker(limit → A_n)` descends along the
        -- canonical quotient map to the quotient by `ker(A_m → A_n)`.
        let q :
            limitRing (F := F) ⧸ RingHom.ker (limit.π F (Opposite.op n)).hom →+*
              F.obj (Opposite.op m) ⧸ RingHom.ker (F.transitionMap hnm).hom :=
          Ideal.quotientMap (RingHom.ker (F.transitionMap hnm).hom)
            ((limit.π F (Opposite.op m)).hom) (by
              intro x hx
              change (F.transitionMap hnm).hom ((limit.π F (Opposite.op m)).hom x) = 0
              have hπx :
                  (F.transitionMap hnm).hom ((limit.π F (Opposite.op m)).hom x) =
                    (limit.π F (Opposite.op n)).hom x := by
                simpa [SequentialInverseSystem.transitionMap] using
                  congrArg (fun φ => φ.hom x) (limit.w F ((homOfLE hnm).op))
              simpa using hπx.trans (by simpa using hx))
        have hmap :
            IsUnit
              (q ((Ideal.Quotient.mk (RingHom.ker (limit.π F (Opposite.op n)).hom))
                (f.derivative.eval a₀))) :=
          IsUnit.map q hderiv
        simpa [q, Polynomial.derivative_map, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_at_apply] using hmap
      have htail :
          ∀ m : ℕ, ∀ hnm : n ≤ m,
            ∃ a : F.obj (Opposite.op m),
              (Polynomial.map ((limit.π F (Opposite.op m)).hom) f).IsRoot a ∧
                a - (limit.π F (Opposite.op m)).hom a₀ ∈
                  RingHom.ker (F.transitionMap hnm).hom := by
        intro m hnm
        letI :
            HenselianRing (F.obj (Opposite.op m))
              (RingHom.ker (F.transitionMap hnm).hom) :=
          henselianRing_of_locally_nilpotent_ideal
            (R := F.obj (Opposite.op m))
            (J := RingHom.ker (F.transitionMap hnm).hom)
            (transitionMap_ker_isLocallyNilpotent (F := F) n h_locnil hnm)
        exact
          HenselianRing.is_henselian
            (I := RingHom.ker (F.transitionMap hnm).hom)
            (Polynomial.map ((limit.π F (Opposite.op m)).hom) f)
            (by simpa using hf.map ((limit.π F (Opposite.op m)).hom))
            ((limit.π F (Opposite.op m)).hom a₀)
            (ha₀_tail m hnm)
            (hderiv_tail m hnm)
      choose aTail hrootTail hmemTail using htail
      have haTail_eq_base :
          aTail n (Nat.le_refl n) = (limit.π F (Opposite.op n)).hom a₀ := by
        -- Proof comment: at stage `n` the long kernel is zero, so the lifted root is forced to be
        -- the original stage-`n` approximation.
        have hmem :
            aTail n (Nat.le_refl n) - (limit.π F (Opposite.op n)).hom a₀ ∈
              RingHom.ker (F.transitionMap (Nat.le_refl n)).hom :=
          hmemTail n (Nat.le_refl n)
        have hzero :
            aTail n (Nat.le_refl n) - (limit.π F (Opposite.op n)).hom a₀ = 0 := by
          simpa [SequentialInverseSystem.transitionMap] using hmem
        exact sub_eq_zero.mp hzero
      let s : (F ⋙ forget CommRingCat).sections :=
        ⟨fun j ↦
            if hnj : n ≤ j.unop then
              aTail j.unop hnj
            else
              (limit.π F j).hom a₀,
          fun {j k} g ↦ by
            have hkj : k.unop ≤ j.unop := leOfHom g.unop
            by_cases hnj : n ≤ j.unop
            · by_cases hnk : n ≤ k.unop
              · have hnj' : n ≤ j.unop := Nat.le_trans hnk hkj
                -- Proof comment: once both stages lie in the tail, uniqueness of simple lifts
                -- over `ker(A_k → A_n)` forces compatibility.
                have hrootMap :
                    (Polynomial.map ((limit.π F k).hom) f).IsRoot
                      ((F.map g).hom (aTail j.unop hnj')) := by
                  have hmap :
                      (Polynomial.map (F.map g).hom
                        (Polynomial.map ((limit.π F j).hom) f)).IsRoot
                          ((F.map g).hom (aTail j.unop hnj')) :=
                    Polynomial.IsRoot.map (f := (F.map g).hom) (h := hrootTail j.unop hnj')
                  have hcomp :
                      (F.map g).hom.comp ((limit.π F j).hom) = (limit.π F k).hom := by
                    ext x
                    simpa using congrArg (fun φ => φ.hom x) (limit.w F g)
                  rw [Polynomial.map_map, hcomp] at hmap
                  simpa using hmap
                have hmemMap :
                    (F.map g).hom (aTail j.unop hnj') - (limit.π F k).hom a₀ ∈
                      RingHom.ker (F.transitionMap hnk).hom := by
                  have hmem :
                      (F.map g).hom
                          (aTail j.unop hnj' - (limit.π F j).hom a₀) ∈
                        RingHom.ker (F.transitionMap hnk).hom := by
                    change
                      (F.transitionMap hnk).hom
                          ((F.map g).hom
                            (aTail j.unop hnj' - (limit.π F j).hom a₀)) = 0
                    have hg :
                        F.map g = F.transitionMap hkj := by
                      simpa [SequentialInverseSystem.transitionMap] using congrArg F.map
                        (show g = (homOfLE hkj).op by subsingleton)
                    have hcomp :
                        F.transitionMap hnj' = (F.map g) ≫ F.transitionMap hnk := by
                      simpa [hg] using transitionMap_comp (F := F) hnk hkj
                    have hkern :
                        (F.transitionMap hnj').hom
                            (aTail j.unop hnj' - (limit.π F j).hom a₀) = 0 := by
                      simpa using hmemTail j.unop hnj'
                    simpa [hcomp, map_sub] using hkern
                  simpa [map_sub] using hmem
                have hdiff :
                    (F.map g).hom (aTail j.unop hnj') - aTail k.unop hnk ∈
                      RingHom.ker (F.transitionMap hnk).hom := by
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                    (RingHom.ker (F.transitionMap hnk).hom).sub_mem hmemMap
                      (hmemTail k.unop hnk)
                have hderivAtRoot :
                    IsUnit
                      ((Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                        (((Polynomial.map ((limit.π F k).hom) f).derivative).eval
                          (aTail k.unop hnk))) := by
                  have hq :
                      (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                          (((Polynomial.map ((limit.π F k).hom) f).derivative).eval
                            (aTail k.unop hnk)) =
                        (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                          (((Polynomial.map ((limit.π F k).hom) f).derivative).eval
                            ((limit.π F k).hom a₀)) := by
                    rw [← Polynomial.eval₂_at_apply
                        (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                        (aTail k.unop hnk)
                        (p := (Polynomial.map ((limit.π F k).hom) f).derivative)]
                    rw [← Polynomial.eval₂_at_apply
                        (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                        ((limit.π F k).hom a₀)
                        (p := (Polynomial.map ((limit.π F k).hom) f).derivative)]
                    rw [show
                          (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                              (aTail k.unop hnk) =
                            (Ideal.Quotient.mk (RingHom.ker (F.transitionMap hnk).hom))
                              ((limit.π F k).hom a₀) by
                          rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
                          exact hmemTail k.unop hnk]
                  rw [hq]
                  exact hderiv_tail k.unop hnk
                have hJac :
                    RingHom.ker (F.transitionMap hnk).hom ≤
                      Ring.jacobson (F.obj k) := by
                  exact
                    (transitionMap_ker_isLocallyNilpotent (F := F) n h_locnil hnk).trans
                      (nilradical_le_jacobson _)
                simpa [hnj, hnk] using
                  (roots_eq_of_sub_mem_ideal_and_derivative_isUnit_mod_ideal
                    (J := RingHom.ker (F.transitionMap hnk).hom) hJac
                    (ha := hrootTail k.unop hnk) (hb := hrootMap) hdiff hderivAtRoot).symm
              · -- Proof comment: mapping a tail lift to an earlier stage kills the error term
                -- because the long kernel factors through stage `n`.
                have hkn : k.unop ≤ n := Nat.le_of_not_ge hnk
                have hg :
                    F.map g = F.transitionMap hkj := by
                  simpa [SequentialInverseSystem.transitionMap] using congrArg F.map
                    (show g = (homOfLE hkj).op by subsingleton)
                have hkern :
                    (F.transitionMap hkj).hom
                        (aTail j.unop hnj - (limit.π F j).hom a₀) = 0 := by
                  have hcomp :
                      F.transitionMap hkj =
                        F.transitionMap hnj ≫ F.transitionMap hkn := by
                    simpa using transitionMap_comp (F := F) hkn hnj
                  have hkern' :
                      (F.transitionMap hnj).hom
                          (aTail j.unop hnj - (limit.π F j).hom a₀) = 0 := by
                    simpa using hmemTail j.unop hnj
                  simpa [hcomp, map_sub] using congrArg (fun x => (F.transitionMap hkn).hom x) hkern'
                have hzero :
                    (F.map g).hom (aTail j.unop hnj) =
                      (F.map g).hom ((limit.π F j).hom a₀) := by
                  have hsub :
                      (F.map g).hom
                          (aTail j.unop hnj - (limit.π F j).hom a₀) = 0 := by
                    simpa [hg, map_sub] using hkern
                  exact sub_eq_zero.mp (by simpa [map_sub] using hsub)
                have hbase :
                    (F.map g).hom ((limit.π F j).hom a₀) =
                      (limit.π F k).hom a₀ := by
                  simpa using congrArg (fun φ => φ.hom a₀) (limit.w F g)
                simpa [hnj, hnk, hbase] using hzero
            · have hnk : ¬ n ≤ k.unop := fun hk ↦ hnj (Nat.le_trans hk hkj)
              -- Proof comment: before stage `n`, compatibility is already built into the original
              -- limit point `a₀`.
              simpa [hnj, hnk] using congrArg (fun φ => φ.hom a₀) (limit.w F g)⟩
      let a : limitRing (F := F) := limit_of_underlying_sections (F := F) s
      refine ⟨a, ?_, ?_⟩
      · -- Proof comment: every coordinate of the reassembled point is a root, so the limit point
        -- itself is a root.
        apply (Polynomial.IsRoot.def).2
        apply underlying_sections_of_limit_injective (F := F)
        apply Subtype.ext
        funext j
        have hroot_coord :
            (Polynomial.map ((limit.π F j).hom) f).IsRoot (s.val j) := by
          by_cases hnj : n ≤ j.unop
          · simpa [s, hnj] using hrootTail j.unop hnj
          · -- Proof comment: before stage `n`, the original approximate root already becomes an
            -- exact root because the stage-`n` value of `f(a₀)` vanishes.
            apply (Polynomial.IsRoot.def).2
            have hjn : j.unop ≤ n := Nat.le_of_not_ge hnj
            have hcomp :
                limit.π F (Opposite.op n) ≫ F.transitionMap hjn = limit.π F j := by
              simpa [SequentialInverseSystem.transitionMap] using
                limit.w F ((homOfLE hjn).op)
            have ha₀_zero :
                (limit.π F (Opposite.op n)).hom (Polynomial.eval a₀ f) = 0 := by
              exact ha₀
            have hbase :
                (limit.π F j).hom (Polynomial.eval a₀ f) = 0 := by
              have hcomp_apply :
                  (limit.π F j).hom (Polynomial.eval a₀ f) =
                    (F.transitionMap hjn).hom
                      ((limit.π F (Opposite.op n)).hom (Polynomial.eval a₀ f)) := by
                simpa using congrArg (fun φ => φ.hom (Polynomial.eval a₀ f)) hcomp.symm
              simpa [ha₀_zero] using hcomp_apply
            simpa [Polynomial.IsRoot, s, hnj, Polynomial.eval₂_eq_eval_map,
              Polynomial.eval₂_at_apply] using hbase
        have hproj_eval :
            (limit.π F j).hom (Polynomial.eval a f) = 0 := by
          rw [← Polynomial.eval₂_at_apply ((limit.π F j).hom) a (p := f)]
          rw [Polynomial.eval₂_eq_eval_map]
          rw [show (limit.π F j).hom a = s.val j by
                simpa [a, s] using limit_π_limit_of_underlying_sections (F := F) s j]
          simpa [Polynomial.IsRoot] using hroot_coord
        have hcoord :
            (underlying_sections_of_limit (F := F) (Polynomial.eval a f)).val j =
              (limit.π F j).hom (0 : limitRing (F := F)) := by
          calc
            (underlying_sections_of_limit (F := F) (Polynomial.eval a f)).val j =
                (limit.π F j).hom (Polynomial.eval a f) := by
                  exact
                    (limit_π_underlying_sections_of_limit (F := F)
                      (x := Polynomial.eval a f) (j := j)).symm
            _ = 0 := hproj_eval
            _ = (limit.π F j).hom (0 : limitRing (F := F)) := by rw [map_zero]
        exact hcoord.trans (limit_π_underlying_sections_of_limit (F := F) (x := 0) (j := j))
      · -- Proof comment: the lifted limit point stays congruent to `a₀` modulo `ker(limit →
        -- A_n)` because the `n`-th coordinate was fixed at the original root.
        change (limit.π F (Opposite.op n)).hom (a - a₀) = 0
        rw [map_sub]
        rw [show (limit.π F (Opposite.op n)).hom a = s.val (Opposite.op n) by
              simpa [a, s] using
                limit_π_limit_of_underlying_sections (F := F) s (Opposite.op n)]
        simp [s, haTail_eq_base]

end
