import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

namespace RingHom

/- Domain-style sampling:
- primary domain: formal smoothness of adic ring maps and extension of absolute derivations across
  square-zero thickenings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.exists_continuous_lift_of_formally_smooth_for_adic`
  * `Derivation`
  * `Derivation.liftOfDerivationToSquareZero`
- best owner abstraction: an arbitrary ring map `f : A →+* B` together with the ideal
  `I : Ideal B` controlling the adic topology; the local/maximal-ideal case is a specialization.
- source/core/bridge triage:
  * `source-facing`: extension of an absolute derivation across a formally smooth adic map;
  * `core/canonical`: the owner lifting theorem
    `RingHom.exists_continuous_lift_of_formally_smooth_for_adic` together with the standard
    derivation/square-zero-extension API;
  * `bridge/view`: the complete-local maximal-ideal specialization below.
- primitive data: the ring map `f : A →+* B`, the ideal `I : Ideal B`, `I`-adic completeness of
  `B`, and the derivation `D : Derivation ℤ A A`.
- derived API: existence of an absolute derivation on `B` restricting to `D` along `f`.
-/

/-- Helper for Lemma 15.49.1: the standard square-zero map attached to the source derivation sends
`0` to `0`. -/
private theorem source_derivation_to_triv_sq_zero_map_zero
    (f : A →+* B) (D : Derivation ℤ A A) :
    TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (f (D 0)) = (0 : TrivSqZeroExt B B) := by
  -- Both components vanish because ring homomorphisms and derivations preserve zero.
  ext <;> simp

/-- Helper for Lemma 15.49.1: the standard square-zero map attached to the source derivation sends
`1` to `1`. -/
private theorem source_derivation_to_triv_sq_zero_map_one
    (f : A →+* B) (D : Derivation ℤ A A) :
    TrivSqZeroExt.inl (f 1) + TrivSqZeroExt.inr (f (D 1)) = (1 : TrivSqZeroExt B B) := by
  -- The scalar part is `1`, and every derivation kills `1`.
  ext <;> simp

/-- Helper for Lemma 15.49.1: the standard square-zero map attached to the source derivation
preserves addition. -/
private theorem source_derivation_to_triv_sq_zero_map_add
    (f : A →+* B) (D : Derivation ℤ A A) (x y : A) :
    TrivSqZeroExt.inl (f (x + y)) + TrivSqZeroExt.inr (f (D (x + y))) =
      (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (f (D x))) +
        (TrivSqZeroExt.inl (f y) + TrivSqZeroExt.inr (f (D y))) := by
  -- Additivity is componentwise for the trivial square-zero extension.
  ext <;> simp

/-- Helper for Lemma 15.49.1: the standard square-zero map attached to the source derivation
preserves multiplication. -/
private theorem source_derivation_to_triv_sq_zero_map_mul
    (f : A →+* B) (D : Derivation ℤ A A) (x y : A) :
    TrivSqZeroExt.inl (f (x * y)) + TrivSqZeroExt.inr (f (D (x * y))) =
      (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (f (D x))) *
        (TrivSqZeroExt.inl (f y) + TrivSqZeroExt.inr (f (D y))) := by
  -- The second component is exactly the Leibniz rule transported through `f`.
  ext <;> simp [D.leibniz, mul_comm]

/-- Helper for Lemma 15.49.1: the source derivation defines the usual map into the trivial
square-zero extension. -/
private def source_derivation_to_triv_sq_zero
    (f : A →+* B) (D : Derivation ℤ A A) : A →+* TrivSqZeroExt B B :=
  { toFun := fun a ↦ TrivSqZeroExt.inl (f a) + TrivSqZeroExt.inr (f (D a))
    map_zero' := source_derivation_to_triv_sq_zero_map_zero f D
    map_one' := source_derivation_to_triv_sq_zero_map_one f D
    map_add' := source_derivation_to_triv_sq_zero_map_add f D
    map_mul' := source_derivation_to_triv_sq_zero_map_mul f D }

/-- Helper for Lemma 15.49.1: the square-zero map built from `D` has the expected first
projection. -/
private theorem source_derivation_to_triv_sq_zero_fst
    (f : A →+* B) (D : Derivation ℤ A A) (a : A) :
    TrivSqZeroExt.fst (source_derivation_to_triv_sq_zero f D a) = f a := by
  -- The first component is the original structural map.
  simp [source_derivation_to_triv_sq_zero]

/-- Helper for Lemma 15.49.1: the square-zero map built from `D` has the expected second
projection. -/
private theorem source_derivation_to_triv_sq_zero_snd
    (f : A →+* B) (D : Derivation ℤ A A) (a : A) :
    TrivSqZeroExt.snd (source_derivation_to_triv_sq_zero f D a) = f (D a) := by
  -- The second component records the derivation value transported through `f`.
  simp [source_derivation_to_triv_sq_zero]

/-- Helper for Lemma 15.49.1: once a square-zero lift has first projection equal to the identity,
its second projection is a derivation. -/
private theorem snd_of_triv_sq_zero_lift_leibniz
    (φ : B →+* TrivSqZeroExt B B)
    (hfst : ∀ b : B, TrivSqZeroExt.fst (φ b) = b) :
    ∀ x y : B,
      TrivSqZeroExt.snd (φ (x * y)) =
        x * TrivSqZeroExt.snd (φ y) + y * TrivSqZeroExt.snd (φ x) := by
  intro x y
  -- Multiplication in the square-zero extension rewrites the second component into Leibniz form.
  rw [map_mul, TrivSqZeroExt.snd_mul, hfst x, hfst y]
  simp [mul_comm]

/-- Helper for Lemma 15.49.1: the ideal induced by `J` on `B[ε]` is coordinatewise in the
`fst`/`snd` coordinates. -/
private theorem triv_sq_zero_ext_mem_map_inl_iff
    (J : Ideal B) (x : TrivSqZeroExt B B) :
    x ∈ Ideal.map (TrivSqZeroExt.inlHom B B) J ↔
      TrivSqZeroExt.fst x ∈ J ∧ TrivSqZeroExt.snd x ∈ J := by
  let K : Ideal (TrivSqZeroExt B B) :=
    Submodule.mk
      { carrier := {y | TrivSqZeroExt.fst y ∈ J ∧ TrivSqZeroExt.snd y ∈ J}
        zero_mem' := by
          constructor <;> simpa using J.zero_mem
        add_mem' := by
          intro a b ha hb
          constructor
          · simpa using J.add_mem ha.1 hb.1
          · simpa using J.add_mem ha.2 hb.2 }
      (by
        intro a y hy
        constructor
        · simpa [smul_eq_mul] using J.mul_mem_left (TrivSqZeroExt.fst a) hy.1
        · rw [smul_eq_mul, TrivSqZeroExt.snd_mul]
          exact J.add_mem
            (by simpa [smul_eq_mul, mul_comm] using
              J.mul_mem_left (TrivSqZeroExt.fst a) hy.2)
            (by simpa [smul_eq_mul, mul_comm] using
              J.mul_mem_left (TrivSqZeroExt.snd a) hy.1))
  have hmap_le : Ideal.map (TrivSqZeroExt.inlHom B B) J ≤ K := by
    -- Any generator coming from `J` has both coordinates in `J`, so the whole mapped ideal does.
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change TrivSqZeroExt.inl y ∈ K
    simpa [K] using hy
  constructor
  · intro hx
    exact hmap_le hx
  · intro hx
    -- Rebuild `x` from its scalar part and its `ε`-part, and show each summand lies in the map.
    have hinl : TrivSqZeroExt.inl (TrivSqZeroExt.fst x) ∈
        Ideal.map (TrivSqZeroExt.inlHom B B) J :=
      Ideal.mem_map_of_mem _ hx.1
    have hinr_base : TrivSqZeroExt.inl (TrivSqZeroExt.snd x) ∈
        Ideal.map (TrivSqZeroExt.inlHom B B) J :=
      Ideal.mem_map_of_mem _ hx.2
    have hinr : TrivSqZeroExt.inr (TrivSqZeroExt.snd x) ∈
        Ideal.map (TrivSqZeroExt.inlHom B B) J := by
      have hmul :
          TrivSqZeroExt.inl (TrivSqZeroExt.snd x) * TrivSqZeroExt.inr (1 : B) =
            TrivSqZeroExt.inr (TrivSqZeroExt.snd x) := by
        ext <;> simp [mul_comm]
      rw [← hmul]
      exact Ideal.mul_mem_right _ _ hinr_base
    have hdecomp :
        TrivSqZeroExt.inl (TrivSqZeroExt.fst x) + TrivSqZeroExt.inr (TrivSqZeroExt.snd x) = x := by
      ext <;> simp
    rw [← hdecomp]
    exact Ideal.add_mem _ hinl hinr

/-- Helper for Lemma 15.49.1: the powers of the mapped ideal on `B[ε]` are still coordinatewise
in the `fst`/`snd` coordinates. -/
private theorem triv_sq_zero_ext_mem_map_inl_pow_iff
    (I : Ideal B) (x : TrivSqZeroExt B B) (n : ℕ) :
    x ∈ (Ideal.map (TrivSqZeroExt.inlHom B B) I) ^ n ↔
      TrivSqZeroExt.fst x ∈ I ^ n ∧ TrivSqZeroExt.snd x ∈ I ^ n := by
  -- `Ideal.map_pow` reduces the power statement to the basic coordinatewise description above.
  rw [← Ideal.map_pow, triv_sq_zero_ext_mem_map_inl_iff]

/-- Helper for Lemma 15.49.1: modulo `I ^ n`, congruence in a ring is the same as membership of
the difference in `I ^ n`. -/
private theorem ring_modEq_iff_mem_pow
    (I : Ideal B) (x y : B) (n : ℕ) :
    x ≡ y [SMOD I ^ n • (⊤ : Submodule B B)] ↔ x - y ∈ I ^ n := by
  -- For the ambient ring viewed as a module over itself, `I ^ n • ⊤` is just the ideal `I ^ n`.
  change Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ x - y ∈ I ^ n
  rw [Submodule.Quotient.eq]
  simpa [Ideal.smul_top_eq_map, Ideal.map_id]

/-- Helper for Lemma 15.49.1: congruence in the mapped adic filtration on `B[ε]` is equivalent to
coordinatewise congruence in the `I`-adic filtration on `B`. -/
private theorem triv_sq_zero_ext_modEq_iff
    (I : Ideal B) (x y : TrivSqZeroExt B B) (n : ℕ) :
    x ≡ y [SMOD (Ideal.map (TrivSqZeroExt.inlHom B B) I) ^ n •
      (⊤ : Submodule (TrivSqZeroExt B B) (TrivSqZeroExt B B))] ↔
      TrivSqZeroExt.fst x ≡ TrivSqZeroExt.fst y [SMOD I ^ n • (⊤ : Submodule B B)] ∧
        TrivSqZeroExt.snd x ≡ TrivSqZeroExt.snd y [SMOD I ^ n • (⊤ : Submodule B B)] := by
  constructor
  · intro hxy
    -- Read the `B[ε]` congruence as difference membership in the mapped ideal power.
    have hmem : x - y ∈ (Ideal.map (TrivSqZeroExt.inlHom B B) I) ^ n :=
      (ring_modEq_iff_mem_pow (B := TrivSqZeroExt B B)
        (I := Ideal.map (TrivSqZeroExt.inlHom B B) I) (x := x) (y := y) (n := n)).1 hxy
    have hcoord :=
      (triv_sq_zero_ext_mem_map_inl_pow_iff (I := I) (x := x - y) (n := n)).1 hmem
    constructor
    · exact (ring_modEq_iff_mem_pow (I := I) (x := TrivSqZeroExt.fst x)
        (y := TrivSqZeroExt.fst y) (n := n)).2 <| by
        simpa using hcoord.1
    · exact (ring_modEq_iff_mem_pow (I := I) (x := TrivSqZeroExt.snd x)
        (y := TrivSqZeroExt.snd y) (n := n)).2 <| by
        simpa using hcoord.2
  · intro hxy
    -- Conversely, coordinatewise `I`-adic congruence rebuilds a `B[ε]`-adic congruence.
    apply (ring_modEq_iff_mem_pow (B := TrivSqZeroExt B B)
      (I := Ideal.map (TrivSqZeroExt.inlHom B B) I) (x := x) (y := y) (n := n)).2
    exact (triv_sq_zero_ext_mem_map_inl_pow_iff (I := I) (x := x - y) (n := n)).2 <| by
      constructor
      · exact (ring_modEq_iff_mem_pow (I := I) (x := TrivSqZeroExt.fst x)
          (y := TrivSqZeroExt.fst y) (n := n)).1 hxy.1
      · exact (ring_modEq_iff_mem_pow (I := I) (x := TrivSqZeroExt.snd x)
          (y := TrivSqZeroExt.snd y) (n := n)).1 hxy.2

/-- Helper for Lemma 15.49.1: the dual numbers over an `I`-adically complete ring are complete
for the adic topology induced by the structural inclusion `B → B[ε]`. -/
private theorem triv_sq_zero_ext_isAdicComplete_map_inl
    (I : Ideal B) [IsAdicComplete I B] :
    IsAdicComplete (Ideal.map (TrivSqZeroExt.inlHom B B) I) (TrivSqZeroExt B B) := by
  -- Route correction: instead of searching for a separate completeness theorem for `B[ε]`, read
  -- the mapped adic filtration coordinatewise and transfer the Hausdorff/precomplete data from `B`.
  let Iε : Ideal (TrivSqZeroExt B B) := Ideal.map (TrivSqZeroExt.inlHom B B) I
  letI : IsHausdorff I B := inferInstance
  letI : IsPrecomplete I B := inferInstance
  let hHaus : IsHausdorff Iε (TrivSqZeroExt B B) := IsHausdorff.mk (fun x hx ↦ by
    -- Vanishing in every `Iε ^ n` forces both coordinates to vanish in every `I ^ n`.
    ext
    · exact IsHausdorff.haus' (I := I) (M := B) (x := TrivSqZeroExt.fst x) <| fun n ↦
        ((triv_sq_zero_ext_modEq_iff (I := I) (x := x) (y := 0) (n := n)).1 (hx n)).1
    · exact IsHausdorff.haus' (I := I) (M := B) (x := TrivSqZeroExt.snd x) <| fun n ↦
        ((triv_sq_zero_ext_modEq_iff (I := I) (x := x) (y := 0) (n := n)).1 (hx n)).2)
  let hPrec : IsPrecomplete Iε (TrivSqZeroExt B B) := IsPrecomplete.mk (fun f hf ↦ by
    -- A Cauchy sequence in `B[ε]` is coordinatewise Cauchy in `B`, so both coordinates converge.
    have hfst : ∀ {m n : ℕ}, m ≤ n →
        TrivSqZeroExt.fst (f m) ≡ TrivSqZeroExt.fst (f n) [SMOD I ^ m • (⊤ : Submodule B B)] := by
      intro m n hmn
      exact ((triv_sq_zero_ext_modEq_iff (I := I) (x := f m) (y := f n) (n := m)).1
        (hf hmn)).1
    have hsnd : ∀ {m n : ℕ}, m ≤ n →
        TrivSqZeroExt.snd (f m) ≡ TrivSqZeroExt.snd (f n) [SMOD I ^ m • (⊤ : Submodule B B)] := by
      intro m n hmn
      exact ((triv_sq_zero_ext_modEq_iff (I := I) (x := f m) (y := f n) (n := m)).1
        (hf hmn)).2
    obtain ⟨L₁, hL₁⟩ := IsPrecomplete.prec' (I := I) (M := B)
      (f := fun n ↦ TrivSqZeroExt.fst (f n)) hfst
    obtain ⟨L₂, hL₂⟩ := IsPrecomplete.prec' (I := I) (M := B)
      (f := fun n ↦ TrivSqZeroExt.snd (f n)) hsnd
    refine ⟨TrivSqZeroExt.inl L₁ + TrivSqZeroExt.inr L₂, ?_⟩
    intro n
    -- Reassemble the two coordinate limits into a limit in the square-zero extension.
    refine (triv_sq_zero_ext_modEq_iff (I := I) (x := f n)
      (y := TrivSqZeroExt.inl L₁ + TrivSqZeroExt.inr L₂) (n := n)).2 ?_
    constructor
    · simpa using hL₁ n
    · simpa using hL₂ n)
  letI : IsHausdorff Iε (TrivSqZeroExt B B) := hHaus
  letI : IsPrecomplete Iε (TrivSqZeroExt B B) := hPrec
  exact IsAdicComplete.mk

/-- Helper for Lemma 15.49.1: equality modulo the square-zero ideal forces the first component of
an element of `B[ε]` to equal the corresponding scalar. -/
private theorem fst_eq_of_quotient_eq_inl
    (x : TrivSqZeroExt B B) (b : B)
    (hx :
      (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal B B)) x =
        (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal B B)) (TrivSqZeroExt.inl b)) :
    TrivSqZeroExt.fst x = b := by
  -- Subtracting the two classes lands in the kernel ideal, whose elements have vanishing first
  -- component.
  have hmem : x - TrivSqZeroExt.inl b ∈ TrivSqZeroExt.kerIdeal B B := by
    let q : TrivSqZeroExt B B →+* TrivSqZeroExt B B ⧸ TrivSqZeroExt.kerIdeal B B :=
      Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal B B)
    have hsub' :
        q x - q (TrivSqZeroExt.inl b) =
          q (TrivSqZeroExt.inl b) - q (TrivSqZeroExt.inl b) :=
      congrArg (fun z ↦ z - q (TrivSqZeroExt.inl b)) hx
    have hsub : q x - q (TrivSqZeroExt.inl b) = 0 := by
      simpa using hsub'
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    simpa [q, RingHom.map_sub] using hsub
  rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at hmem
  have hfst := congrArg TrivSqZeroExt.fst hmem
  exact sub_eq_zero.mp <| by simpa using hfst

/-- Helper for Lemma 15.49.1: adic formal smoothness should provide a square-zero lift into
`B[ε]` extending the source derivation map. -/
private theorem exists_triv_sq_zero_lift_of_formally_smooth_for_adic
    (f : A →+* B) (I : Ideal B) [IsAdicComplete I B]
    (hfs : f.formally_smooth_for_adic I)
    (D : Derivation ℤ A A) :
    ∃ φ : B →+* TrivSqZeroExt B B,
      (∀ b : B, TrivSqZeroExt.fst (φ b) = b) ∧
        φ.comp f = source_derivation_to_triv_sq_zero f D := by
  let J : Ideal (TrivSqZeroExt B B) := TrivSqZeroExt.kerIdeal B B
  let Iε : Ideal (TrivSqZeroExt B B) := Ideal.map (TrivSqZeroExt.inlHom B B) I
  letI : TopologicalSpace B := I.adicTopology
  letI : TopologicalSpace (TrivSqZeroExt B B) := Iε.adicTopology
  letI : IsTopologicalRing B := inferInstance
  letI : IsTopologicalRing (TrivSqZeroExt B B) := inferInstance
  letI : IsAdicComplete Iε (TrivSqZeroExt B B) := triv_sq_zero_ext_isAdicComplete_map_inl I
  let ψ : B →+* TrivSqZeroExt B B ⧸ J := (Ideal.Quotient.mk J).comp (TrivSqZeroExt.inlHom B B)
  have hψ : Continuous ψ := by
    -- The inclusion `B → B[ε]` is continuous for the chosen adic topologies, and quotient maps are
    -- continuous by definition of the quotient topology.
    have hinl : Continuous (TrivSqZeroExt.inlHom B B) := by
      rw [RingHom.continuous_adic_iff_exists_pow_map_le]
      refine ⟨1, ?_⟩
      simpa [Iε, pow_one]
    exact continuous_quot_mk.comp hinl
  have hJClosed : IsClosed (J : Set (TrivSqZeroExt B B)) := by
    -- The square-zero ideal is the kernel of the continuous first projection into the separated
    -- `I`-adic ring `B`.
    letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    letI : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    have hB :
        CompleteSpace B ∧ T2Space B :=
      TopologicalRing.complete_space_and_t2_of_is_adic_complete (show IsAdic I by rfl)
        (inferInstance : IsAdicComplete I B)
    letI : CompleteSpace B := hB.1
    letI : T2Space B := hB.2
    have hfstcont : Continuous ((TrivSqZeroExt.fstHom ℤ B B).toRingHom) := by
      rw [RingHom.continuous_adic_iff_exists_pow_map_le]
      refine ⟨1, ?_⟩
      have hcomp :
          ((TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp (TrivSqZeroExt.inlHom B B)) = RingHom.id B := by
        ext b
        rfl
      have hmap :
          Ideal.map ((TrivSqZeroExt.fstHom ℤ B B).toRingHom)
              (Ideal.map (TrivSqZeroExt.inlHom B B) I) ≤ I := by
        exact le_of_eq <| by
          rw [Ideal.map_map, hcomp]
          simp
      simpa [Iε, pow_one] using hmap
    have hker :
        ((TrivSqZeroExt.fstHom ℤ B B).toRingHom ⁻¹' ({0} : Set B)) =
          (J : Set (TrivSqZeroExt B B)) := by
      ext x
      constructor
      · intro hx
        change x ∈ TrivSqZeroExt.kerIdeal B B
        rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
        ext
        · simpa using hx
        · simp
      · intro hx
        change x ∈ TrivSqZeroExt.kerIdeal B B at hx
        rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at hx
        change TrivSqZeroExt.fst x = 0
        simpa using congrArg TrivSqZeroExt.fst hx
    rw [← hker]
    exact isClosed_singleton.preimage hfstcont
  have hpow : ∃ t : ℕ+, J ^ (t : ℕ) ≤ Iε := by
    -- The square-zero ideal has square zero, so its second power lies in every ideal.
    refine ⟨2, ?_⟩
    simpa [J, TrivSqZeroExt.kerIdeal_sq B B] using (bot_le : (⊥ : Ideal (TrivSqZeroExt B B)) ≤ Iε)
  have hcomm :
      (Ideal.Quotient.mk J).comp (source_derivation_to_triv_sq_zero f D) = ψ.comp f := by
    -- Modulo the square-zero ideal, the `ε`-part disappears.
    ext a
    have hzero :
        (Ideal.Quotient.mk J) (TrivSqZeroExt.inr (f (D a)) : TrivSqZeroExt B B) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, TrivSqZeroExt.mem_kerIdeal_iff_inr]
      rfl
    change
      (Ideal.Quotient.mk J)
          (TrivSqZeroExt.inl (f a) + TrivSqZeroExt.inr (f (D a))) =
        (Ideal.Quotient.mk J) (TrivSqZeroExt.inl (f a))
    rw [RingHom.map_add, hzero, add_zero]
  have hI : IsAdic I := by
    rfl
  have hIε : IsAdic Iε := by
    rfl
  obtain ⟨φ, hφquot, hφcomp, _⟩ :=
    f.exists_continuous_lift_of_formally_smooth_for_adic I hfs hI
      Iε J hIε hJClosed hpow ψ hψ (source_derivation_to_triv_sq_zero f D) hcomm
  refine ⟨φ, ?_, hφcomp⟩
  intro b
  -- The quotient compatibility identifies `φ b` with the scalar lift of `b`, so the first
  -- component of `φ b` is exactly `b`.
  have hb :
      (Ideal.Quotient.mk J) (φ b) = (Ideal.Quotient.mk J) (TrivSqZeroExt.inl b) := by
    simpa [ψ] using RingHom.congr_fun hφquot b
  exact fst_eq_of_quotient_eq_inl (x := φ b) (b := b) hb

-- Proof sketch: form the square-zero thickening `B[ε]` and the map `A → B[ε]` sending
-- `a` to `f a + ε • f (D a)`. Because `B` is `I`-adically complete and `f` is formally smooth
-- for the `I`-adic topology, Lemma `15.37.5` provides a lift `B → B[ε]`. Taking the
-- `ε`-coefficient of that lift yields the required derivation on `B`, and the commutative square
-- forces it to agree with `D` on the image of `A`.
/-- A formally smooth adic ring map into an adically complete target extends absolute derivations
from the source to the target. -/
theorem exists_derivation_extension_of_formally_smooth_for_adic
    (f : A →+* B) (I : Ideal B) [IsAdicComplete I B]
    (hfs : f.formally_smooth_for_adic I)
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := by
  -- Lift the source derivation map into the square-zero extension and then read off the
  -- `ε`-coefficient.
  rcases exists_triv_sq_zero_lift_of_formally_smooth_for_adic f I hfs D with
    ⟨φ, hfst, hcomp⟩
  let D' : Derivation ℤ B B := Derivation.mk'
    (((TrivSqZeroExt.sndHom B B).restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap)
    (fun x y ↦ by
      -- The second projection of the lifted ring map satisfies Leibniz because the first
      -- projection is the identity.
      change TrivSqZeroExt.snd (φ (x * y)) =
          x • TrivSqZeroExt.snd (φ y) + y • TrivSqZeroExt.snd (φ x)
      rw [snd_of_triv_sq_zero_lift_leibniz φ hfst]
      simp [smul_eq_mul])
  refine ⟨D', ?_⟩
  intro a
  -- Restricting the lifted square-zero map along `f` recovers the original derivation data.
  simpa [D', source_derivation_to_triv_sq_zero_snd] using
    congrArg TrivSqZeroExt.snd (RingHom.congr_fun hcomp a)

end RingHom

section

open IsLocalRing

variable [Algebra A B] [IsCompleteLocalRing B]

/-- Lemma 15.49.1: if `B` is a complete local ring and `algebraMap A B` is formally smooth for
the `maximalIdeal B`-adic topology, then every absolute derivation `D : A → A` extends to an
absolute derivation `D' : B → B`. -/
theorem exists_derivation_extension_of_formally_smooth_for_completeLocal
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B))
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (algebraMap A B a) = algebraMap A B (D a) := by
  simpa using
    (algebraMap A B).exists_derivation_extension_of_formally_smooth_for_adic
      (maximalIdeal B) hfs D

end

end
