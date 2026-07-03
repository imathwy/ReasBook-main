import Mathlib
import stacks_project.Chap10.Lemma_10_106_3
import stacks_project.Chap10.Lemma_10_106_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- Domain-style sampling:
- primary domain: directed colimits in commutative local algebra;
- sampled owner declarations:
  `Ring.DirectLimit.of`,
  `Ring.DirectLimit.of_f`,
  `Ring.DirectLimit.exists_of`,
  `IsRegularLocalRing`;
- owner decision:
  `source-facing`: the Stacks Project statement that the directed colimit ring is local, and is
  regular local once it is Noetherian;
  `core/canonical`: `Ring.DirectLimit` as the owner of the colimit ring and its canonical maps;
  `bridge/view`: the stagewise maps `Ring.DirectLimit.of`.

Primitive data are the directed system `(R, φ)` and the stagewise local/regular-local hypotheses.
The direct-limit local-ring structure and the locality of the canonical maps are derived API on
`Ring.DirectLimit`, so this file should expose them on that owner surface rather than through
parallel free-standing wrappers.
-/
variable {I : Type v} [Preorder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j)

local notation "ρ" => fun i j h ↦ φ i j h
local notation "R∞" => Ring.DirectLimit R ρ

namespace Ring.DirectLimit

section Local

variable [Nonempty I] [IsDirectedOrder I] [DirectedSystem R (φ · · ·)]
variable [∀ i, IsLocalRing (R i)] [∀ i j hij, IsLocalHom (φ i j hij)]

-- Proof sketch: every element of the direct limit comes from some stage. If two elements of the
-- direct limit sum to a unit, represent them in a common stage using directedness; the transition
-- maps are local, so the corresponding sum in that local stage is a unit, forcing one summand to
-- be a unit there and hence in the colimit.
/-- A directed colimit of local rings along local ring maps is again a local ring. -/
theorem isLocalRing : IsLocalRing R∞ := by
  letI : ∀ i, Nontrivial (R i) := fun i ↦ inferInstance
  letI : Nontrivial R∞ := by
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨⟨0, 1, ?_⟩⟩
    change (0 : R∞) ≠ 1
    rw [← (Ring.DirectLimit.of R ρ i).map_one]
    intro h
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := R) (f' := ρ) h.symm
    rw [(φ i j hij).map_one] at hj
    exact one_ne_zero hj
  refine ⟨?_⟩
  intro a b hab
  rcases Ring.DirectLimit.exists_of (G := R) (f := ρ) a with ⟨i, x, rfl⟩
  rcases Ring.DirectLimit.exists_of (G := R) (f := ρ) b with ⟨j, y, rfl⟩
  rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
  have hzero : Ring.DirectLimit.of R ρ k (φ i k hik x + φ j k hjk y - 1) = 0 := by
    -- Proof comment: move the relation `a + b = 1` to a common stage and compare with `1`.
    calc
      Ring.DirectLimit.of R ρ k (φ i k hik x + φ j k hjk y - 1)
          = Ring.DirectLimit.of R ρ i x + Ring.DirectLimit.of R ρ j y - 1 := by
              simp [map_add, map_sub, Ring.DirectLimit.of_f]
      _ = 0 := by
            simpa [hab]
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact (G := R) (f' := ρ) hzero
  have hsum : φ i l (le_trans hik hkl) x + φ j l (le_trans hjk hkl) y = 1 := by
    -- Zero-exactness upgrades the colimit relation to a genuine equality at a later stage.
    have hstage : φ k l hkl (φ i k hik x + φ j k hjk y - 1) = 0 := hl
    have hstage' :
        φ i l (le_trans hik hkl) x + φ j l (le_trans hjk hkl) y - 1 = 0 := by
      simpa [map_add, map_sub, DirectedSystem.map_map'] using hstage
    exact sub_eq_zero.mp hstage'
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hx | hy
  · left
    -- A unit at the later stage remains a unit in the colimit.
    simpa [Ring.DirectLimit.of_f] using (Ring.DirectLimit.of R ρ l).isUnit_map hx
  · right
    -- The symmetric argument handles the second summand.
    simpa [Ring.DirectLimit.of_f] using (Ring.DirectLimit.of R ρ l).isUnit_map hy

instance : IsLocalRing R∞ :=
  isLocalRing R φ

-- Proof sketch: if the image of `x : R i` is a unit in the direct limit, represent its inverse in
-- some stage `j`, enlarge to a common upper bound `k`, and check there that the image of `x`
-- becomes a unit. Since `R i → R k` is local, `x` was already a unit in `R i`.
/-- The canonical map from any stage of a directed system of local rings to the direct limit is a
local ring homomorphism. -/
theorem of_isLocalHom (i : I) : IsLocalHom (Ring.DirectLimit.of R ρ i) := by
  refine ⟨fun x hx_map ↦ ?_⟩
  rcases hx_map with ⟨u, hu⟩
  rcases Ring.DirectLimit.exists_of (G := R) (f := ρ) ((↑u⁻¹ : Units R∞) : R∞) with
    ⟨j, y, hy⟩
  rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
  have hzero : Ring.DirectLimit.of R ρ k (φ i k hik x * φ j k hjk y - 1) = 0 := by
    -- Proof comment: at the common stage, `y` represents the inverse of the image of `x`.
    calc
      Ring.DirectLimit.of R ρ k (φ i k hik x * φ j k hjk y - 1)
          = Ring.DirectLimit.of R ρ i x * Ring.DirectLimit.of R ρ j y - 1 := by
              simp [map_sub, map_mul, Ring.DirectLimit.of_f]
      _ = Ring.DirectLimit.of R ρ i x * ((↑u⁻¹ : Units R∞) : R∞) - 1 := by
            rw [hy]
      _ = (↑u : R∞) * ((↑u⁻¹ : Units R∞) : R∞) - 1 := by
            rw [hu]
      _ = 0 := by
            simp
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact (G := R) (f' := ρ) hzero
  have hlmul : φ i l (le_trans hik hkl) x * φ j l (le_trans hjk hkl) y = 1 := by
    -- Proof comment: zero-exactness moves the inverse relation back to a genuine stage equality.
    have hl' : φ k l hkl (φ i k hik x * φ j k hjk y - 1) = 0 := hl
    have hstage :
        φ i l (le_trans hik hkl) x * φ j l (le_trans hjk hkl) y - 1 = 0 := by
      simpa [map_sub, map_mul, DirectedSystem.map_map'] using hl'
    exact sub_eq_zero.mp hstage
  have hunit_l : IsUnit (φ i l (le_trans hik hkl) x) := by
    -- The image of `x` is a unit in the larger stage because it has an explicit inverse there.
    exact isUnit_iff_exists_inv.mpr ⟨φ j l (le_trans hjk hkl) y, hlmul⟩
  -- Reflect units back along the local transition map `R i → R l`.
  exact isUnit_of_map_unit (φ i l (le_trans hik hkl)) x hunit_l

instance (i : I) : IsLocalHom (Ring.DirectLimit.of R ρ i) :=
  of_isLocalHom R φ i

end Local

section Domain

variable [Nonempty I] [IsDirectedOrder I] [DirectedSystem R (φ · · ·)]
variable [∀ i, IsDomain (R i)]

/-- Helper for Lemma 10.106.8: a directed colimit of domains is again a domain. -/
theorem isDomain : IsDomain R∞ := by
  haveI : Nontrivial R∞ := by
    obtain ⟨i⟩ := ‹Nonempty I›
    refine ⟨⟨0, 1, ?_⟩⟩
    change (0 : R∞) ≠ 1
    rw [← (Ring.DirectLimit.of R ρ i).map_one]
    intro h
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact (G := R) (f' := ρ) h.symm
    rw [(φ i j hij).map_one] at hj
    exact one_ne_zero hj
  haveI : NoZeroDivisors R∞ := by
    constructor
    intro x y hxy
    induction x using Ring.DirectLimit.induction_on with
    | ih i x =>
        induction y using Ring.DirectLimit.induction_on with
        | ih j y =>
            rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
            have hk : Ring.DirectLimit.of R ρ k (φ i k hik x * φ j k hjk y) = 0 := by
              -- Proof comment: move the vanishing product to a common stage.
              simpa [map_mul, Ring.DirectLimit.of_f] using hxy
            obtain ⟨l, hkl, hzero⟩ := Ring.DirectLimit.of.zero_exact (G := R) (f' := ρ) hk
            have hprod :
                φ i l (le_trans hik hkl) x * φ j l (le_trans hjk hkl) y = 0 := by
              simpa [map_mul, DirectedSystem.map_map'] using hzero
            rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with hx | hy
            · left
              simpa [Ring.DirectLimit.of_f] using congrArg (Ring.DirectLimit.of R ρ l) hx
            · right
              simpa [Ring.DirectLimit.of_f] using congrArg (Ring.DirectLimit.of R ρ l) hy
  exact NoZeroDivisors.to_isDomain R∞

end Domain

section Regular

variable [Nonempty I] [IsDirectedOrder I] [DirectedSystem R (φ · · ·)]
variable [∀ i, IsRegularLocalRing (R i)] [∀ i j hij, IsLocalHom (φ i j hij)]
variable [IsNoetherianRing (Ring.DirectLimit R ρ)]

open IsLocalRing

/-- Helper for Lemma 10.106.8: for a singleton parameter family, `parameterIdeal` is the
principal ideal generated by that element. -/
lemma parameterIdeal_fin1_eq_span_singleton {A : Type*} [CommRing A] [IsLocalRing A]
    (x : Fin 1 → maximalIdeal A) :
    parameterIdeal x = Ideal.span ({(x 0 : A)} : Set A) := by
  -- Proof comment: the range of a `Fin 1`-indexed family is the singleton containing its only
  -- value, so the two span descriptions coincide.
  rw [parameterIdeal_eq_span]
  congr 1
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    simp
  · intro ha
    refine ⟨0, ?_⟩
    simpa [Set.mem_singleton_iff] using ha.symm

/-- Helper for Lemma 10.106.8: an element outside `𝔪²` has nonzero cotangent class. -/
lemma cotangent_nonzero_of_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    (maximalIdeal A).toCotangent x ≠ 0 := by
  -- Proof comment: `Ideal.toCotangent_eq_zero` identifies the kernel with `𝔪²`.
  intro hx0
  exact hx (((maximalIdeal A).toCotangent_eq_zero x).mp hx0)

/-- Helper for Lemma 10.106.8: an element outside `𝔪²` forces positive embedding dimension. -/
lemma spanFinrank_pos_of_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    0 < (maximalIdeal A).spanFinrank := by
  -- Proof comment: a nonzero cotangent vector gives a positive residue-field dimension.
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨(maximalIdeal A).toCotangent x, cotangent_nonzero_of_not_mem_sq (x := x) hx⟩

/-- Helper for Lemma 10.106.8: a nonzero vector in a finite-dimensional vector space can be chosen
as the head of a `Fin`-indexed basis. -/
lemma cotangent_basis_with_prescribed_head
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hfinrank : Module.finrank k V = n + 1) (v : V) (hv : v ≠ 0) :
    ∃ b : Module.Basis (Fin (n + 1)) k V, b 0 = v := by
  classical
  let _ : Module.Finite k V := Module.finite_of_finrank_eq_succ hfinrank
  let s : Set V := {v}
  have hs : LinearIndepOn k id s := by
    -- Proof comment: the singleton containing a nonzero vector is linearly independent.
    simpa [s] using (linearIndepOn_singleton_iff (R := k) (v := id) (i := v)).2 hv
  let b : Module.Basis (hs.extend (Set.subset_univ s)) k V := Module.Basis.extend hs
  let i0 : hs.extend (Set.subset_univ s) :=
    ⟨v, hs.subset_extend (Set.subset_univ s) (by simp [s])⟩
  letI : Fintype (hs.extend (Set.subset_univ s)) := Fintype.ofFinite (hs.extend (Set.subset_univ s))
  have hcard : Fintype.card (hs.extend (Set.subset_univ s)) = n + 1 := by
    -- Proof comment: the extended basis has exactly the ambient finrank many vectors.
    rw [← Module.finrank_eq_card_basis b, hfinrank]
  let e0 : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
  let eidx : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) :=
    e0.trans (Equiv.swap (e0 i0) 0)
  let c : Module.Basis (Fin (n + 1)) k V := b.reindex eidx
  have heidx_zero : eidx i0 = 0 := by
    -- Proof comment: reindex the distinguished extended basis vector into the head slot.
    simp [eidx]
  have heidx_symm_zero : eidx.symm 0 = i0 := by
    exact eidx.symm_apply_eq.mpr heidx_zero.symm
  have hc_zero : c 0 = v := by
    -- Proof comment: after reindexing, the `0`th basis vector is the prescribed vector.
    calc
      c 0 = b (eidx.symm 0) := by simp [c]
      _ = b i0 := by rw [heidx_symm_zero]
      _ = v := by
            simpa [b, i0] using Module.Basis.extend_apply_self hs i0
  exact ⟨c, hc_zero⟩

/-- Helper for Lemma 10.106.8: reindexing a finite parameter family along a `Fin.cast` does not
change the generated ideal. -/
lemma parameterIdeal_comp_cast
    {A : Type*} [CommRing A] [IsLocalRing A] {d e : ℕ}
    (h : d = e) (x : Fin d → maximalIdeal A) :
    parameterIdeal (x ∘ Fin.cast h.symm) = parameterIdeal x := by
  -- Proof comment: reindexing by a `Fin.cast` bijection does not change the image set of the
  -- family, hence does not change the spanned parameter ideal.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
  congr 1
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast h.symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast h i, ?_⟩
    simp

/-- Helper for Lemma 10.106.8: the one-head family written with `Fin.append` generates the same
parameter ideal as the equivalent `Fin.cons` family. -/
lemma parameterIdeal_append_eq_cons
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ}
    (x : maximalIdeal A) (z : Fin n → maximalIdeal A) :
    parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) z) = parameterIdeal (Fin.cons x z) := by
  -- Proof comment: `Fin.append` and `Fin.cons` enumerate the same head-plus-tail family.
  rw [Fin.append_left_eq_cons]
  simpa using
    (parameterIdeal_comp_cast (A := A) (h := (Nat.add_comm 1 n).symm)
      (x := Fin.cons x z))

/-- Helper for Lemma 10.106.8: a nonzero cotangent class can be completed to a full regular
system of parameters with that class in the head position. -/
lemma cotangent_head_extends_to_regularSystemOfParameters
    {A : Type*} [CommRing A] [IsRegularLocalRing A] (x : maximalIdeal A)
    (hx : (maximalIdeal A).toCotangent x ≠ 0) :
    let e :=
      Module.finrank (ResidueField A)
        (CotangentSpace A ⧸
          Submodule.span (ResidueField A)
            ({(maximalIdeal A).toCotangent x} : Set (CotangentSpace A)))
    ∃ y : Fin e → maximalIdeal A,
      IsRegularSystemOfParameters (Fin.append (fun _ : Fin 1 ↦ x) y) := by
  let K : Submodule (ResidueField A) (CotangentSpace A) :=
    Submodule.span (ResidueField A) ({(maximalIdeal A).toCotangent x} : Set (CotangentSpace A))
  let e : ℕ := Module.finrank (ResidueField A) (CotangentSpace A ⧸ K)
  have hK_dim : Module.finrank (ResidueField A) K = 1 := by
    -- Proof comment: the span of one nonzero cotangent vector is one-dimensional.
    simpa [K] using
      (finrank_span_singleton
        (K := ResidueField A)
        (V := CotangentSpace A)
        hx)
  have hcot_dim : Module.finrank (ResidueField A) (CotangentSpace A) = e + 1 := by
    -- Proof comment: quotienting out the prescribed head direction removes exactly one basis
    -- vector from the cotangent space.
    have hrank :
        Module.finrank (ResidueField A) (CotangentSpace A ⧸ K) +
            Module.finrank (ResidueField A) K =
          Module.finrank (ResidueField A) (CotangentSpace A) := by
      simpa using
        (Submodule.finrank_quotient_add_finrank
          (R := ResidueField A)
          (M := CotangentSpace A)
          K)
    have hrank' : e + 1 = Module.finrank (ResidueField A) (CotangentSpace A) := by
      simpa [e, hK_dim] using hrank
    omega
  obtain ⟨b, hb0⟩ :=
    cotangent_basis_with_prescribed_head
      (k := ResidueField A)
      (V := CotangentSpace A)
      (n := e)
      hcot_dim
      ((maximalIdeal A).toCotangent x)
      hx
  choose y hy using
    fun i : Fin e ↦ (maximalIdeal A).toCotangent_surjective (b i.succ)
  have hparameter :
      parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) y) = maximalIdeal A := by
    let w : Fin (e + 1) → maximalIdeal A := Fin.cons x y
    have himage :
        (maximalIdeal A).toCotangent '' Set.range w = Set.range b := by
      ext z
      constructor
      · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ ?_ i
        · refine ⟨0, ?_⟩
          simpa [w, hb0]
        · intro j
          refine ⟨j.succ, ?_⟩
          simpa [w] using (hy j).symm
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ ?_ i
        · refine ⟨x, ⟨0, by simp [w]⟩, ?_⟩
          simpa [w, hb0]
        · intro j
          refine ⟨y j, ⟨j.succ, by simp [w]⟩, ?_⟩
          simpa [w] using hy j
    have hspan_image :
        Submodule.span (ResidueField A) ((maximalIdeal A).toCotangent '' Set.range w) = ⊤ := by
      -- Proof comment: the chosen lifts realize every prescribed basis vector in the cotangent
      -- space.
      rw [himage]
      simpa using b.span_eq
    have hspan_top :
        Submodule.span A (Set.range w) = ⊤ := by
      -- Proof comment: spanning the cotangent space is equivalent to generating the maximal
      -- ideal in a Noetherian local ring.
      exact (CotangentSpace.span_image_eq_top_iff (R := A) (s := Set.range w)).1 hspan_image
    have hspan_val :
        Submodule.span A (Set.range fun i : Fin (e + 1) ↦ ((w i : maximalIdeal A) : A)) =
          maximalIdeal A := by
      -- Proof comment: translate the spanning statement from the maximal-ideal subtype to the
      -- ambient ideal.
      exact (Submodule.span_range_subtype_eq_top_iff
        (p := maximalIdeal A)
        (s := fun i : Fin (e + 1) ↦ ((w i : maximalIdeal A) : A))
        (hs := fun i ↦ (w i).2)).1 (by simpa using hspan_top)
    have hparameter_cons : parameterIdeal w = maximalIdeal A := by
      -- Proof comment: `parameterIdeal` is precisely the ideal spanned by the chosen family.
      simpa [parameterIdeal_eq_span, w] using hspan_val
    calc
      parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) y) = parameterIdeal (Fin.cons x y) := by
        simpa using parameterIdeal_append_eq_cons (A := A) x y
      _ = maximalIdeal A := hparameter_cons
  have hdim : ringKrullDim A = ((1 + e : ℕ) : ℕ∞) := by
    -- Proof comment: regular-locality identifies Krull dimension with the cotangent-space
    -- dimension, and the prescribed head contributes exactly one dimension.
    calc
      ringKrullDim A = ((maximalIdeal A).spanFinrank : ℕ∞) := by
        simpa using
          ((isRegularLocalRing_iff (R := A)).1 (inferInstance : IsRegularLocalRing A)).symm
      _ = (Module.finrank (ResidueField A) (CotangentSpace A) : ℕ∞) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
      _ = (e + 1 : ℕ) := by
        exact_mod_cast hcot_dim
      _ = (1 + e : ℕ) := by
        simp [Nat.add_comm]
  refine ⟨y, ?_⟩
  -- Proof comment: a generating family of the maximal ideal with the correct cardinality is a
  -- regular system of parameters.
  exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq
    (R := A) (d := 1 + e) hdim (Fin.append (fun _ : Fin 1 ↦ x) y)).2 hparameter

/-- Helper for Lemma 10.106.8: a cotangent-space basis with prescribed head lifts to generators of
the maximal ideal. -/
lemma cotangent_lifts_generate_maximalIdeal_of_basis_with_head
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {n : ℕ}
    (x : maximalIdeal A)
    (b : Module.Basis (Fin (n + 1)) (ResidueField A) (CotangentSpace A))
    (hb0 : b 0 = (maximalIdeal A).toCotangent x)
    (z : Fin n → maximalIdeal A)
    (hz : ∀ i, (maximalIdeal A).toCotangent (z i) = b i.succ) :
    parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) z) = maximalIdeal A := by
  let w : Fin (n + 1) → maximalIdeal A := Fin.cons x z
  have himage :
      (maximalIdeal A).toCotangent '' Set.range w = Set.range b := by
    ext y
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      refine Fin.cases ?_ ?_ i
      · refine ⟨0, ?_⟩
        simpa [w, hb0]
      · intro j
        refine ⟨j.succ, ?_⟩
        simpa [w] using (hz j).symm
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ ?_ i
      · refine ⟨x, ⟨0, by simp [w]⟩, ?_⟩
        simpa [w, hb0]
      · intro j
        refine ⟨z j, ⟨j.succ, by simp [w]⟩, ?_⟩
        simpa [w] using hz j
  have hspan_image :
      Submodule.span (ResidueField A) ((maximalIdeal A).toCotangent '' Set.range w) = ⊤ := by
    -- Proof comment: every basis vector is realized as the cotangent image of one chosen lift.
    rw [himage]
    simpa using b.span_eq
  have hspan_top :
      Submodule.span A (Set.range w) = ⊤ := by
    -- Proof comment: spanning the cotangent space is equivalent to generating the maximal ideal.
    exact (CotangentSpace.span_image_eq_top_iff (R := A) (s := Set.range w)).1 hspan_image
  have hspan_val :
      Submodule.span A (Set.range fun i : Fin (n + 1) ↦ ((w i : maximalIdeal A) : A)) =
        maximalIdeal A := by
    -- Proof comment: translate the span statement from the maximal-ideal subtype to the ambient
    -- ideal.
    exact (Submodule.span_range_subtype_eq_top_iff
      (p := maximalIdeal A)
      (s := fun i : Fin (n + 1) ↦ ((w i : maximalIdeal A) : A))
      (hs := fun i ↦ (w i).2)).1 (by simpa using hspan_top)
  have hparameter_cons : parameterIdeal w = maximalIdeal A := by
    -- Proof comment: `parameterIdeal` is exactly the ideal generated by the chosen family.
    simpa [parameterIdeal_eq_span, w] using hspan_val
  calc
    parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) z) = parameterIdeal (Fin.cons x z) := by
      simpa using parameterIdeal_append_eq_cons (A := A) x z
    _ = maximalIdeal A := hparameter_cons

/-- Helper for Lemma 10.106.8: a prescribed nonzero cotangent class should be completed to a
generating family of the maximal ideal. -/
lemma prescribed_head_parameterIdeal_eq_maximalIdeal_of_not_mem_sq
    {A : Type*} [CommRing A] [IsRegularLocalRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    ∃ y : Fin ((maximalIdeal A).spanFinrank - 1) → maximalIdeal A,
      parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) y) = maximalIdeal A := by
  let n := (maximalIdeal A).spanFinrank - 1
  have hfinrank :
      Module.finrank (ResidueField A) (CotangentSpace A) = n + 1 := by
    -- Proof comment: a nonzero cotangent class forces positive embedding dimension, so the
    -- cotangent finrank has the required successor shape.
    have hpos : 0 < (maximalIdeal A).spanFinrank :=
      spanFinrank_pos_of_not_mem_sq (x := x) hx
    have hspan : (maximalIdeal A).spanFinrank = n + 1 := by
      dsimp [n]
      omega
    calc
      Module.finrank (ResidueField A) (CotangentSpace A) = (maximalIdeal A).spanFinrank := by
        rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
      _ = n + 1 := hspan
  obtain ⟨b, hb0⟩ :=
    cotangent_basis_with_prescribed_head
      (k := ResidueField A) (V := CotangentSpace A) (n := n)
      hfinrank ((maximalIdeal A).toCotangent x)
      (cotangent_nonzero_of_not_mem_sq (x := x) hx)
  choose y hy using
    fun i : Fin n ↦ (maximalIdeal A).toCotangent_surjective (b i.succ)
  refine ⟨y, ?_⟩
  exact cotangent_lifts_generate_maximalIdeal_of_basis_with_head
    (x := x) (b := b) hb0 y hy

/-- Helper for Lemma 10.106.8: in a regular local ring, an element of the maximal ideal whose
class in the cotangent space is nonzero is the first entry of a regular system of parameters. -/
lemma singleton_partOfRegularSystemOfParameters_of_not_mem_sq
    {A : Type*} [CommRing A] [IsRegularLocalRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank
      (fun _ : Fin 1 ↦ x) := by
  letI : IsNoetherianRing A := inferInstance
  let d : ℕ := (maximalIdeal A).spanFinrank
  obtain ⟨y, hy⟩ :=
    prescribed_head_parameterIdeal_eq_maximalIdeal_of_not_mem_sq (A := A) x hx
  refine ⟨y, ?_⟩
  have hpos : 0 < d := by
    simpa [d] using spanFinrank_pos_of_not_mem_sq (A := A) (x := x) hx
  have hdim : ringKrullDim A = ((1 + (d - 1) : ℕ) : ℕ∞) := by
    -- Proof comment: regular-locality identifies the Krull dimension with the embedding
    -- dimension, and positivity rewrites that dimension as a successor.
    calc
      ringKrullDim A = (d : ℕ∞) := by
        simpa [d] using
          ((isRegularLocalRing_iff (R := A)).1 (inferInstance : IsRegularLocalRing A)).symm
      _ = ((1 + (d - 1) : ℕ) : ℕ∞) := by
        have hd' : d = 1 + (d - 1) := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm] using (Nat.succ_pred_eq_of_pos hpos).symm
        exact congrArg (fun n : ℕ ↦ (((n : ℕ∞) : WithBot ℕ∞))) hd'
  -- Proof comment: once the completed family generates `maximalIdeal A`, the dimension equality
  -- upgrades it to a regular system of parameters.
  exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq
    (R := A) (d := 1 + (d - 1)) hdim (Fin.append (fun _ : Fin 1 ↦ x) y)).2 hy

/-- Helper for Lemma 10.106.8: quotienting a regular local ring by an element outside `𝔪^2`
again yields a regular local ring. -/
lemma stage_quotient_isRegularLocalRing_of_not_mem_sq
    {A : Type*} [CommRing A] [IsRegularLocalRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    IsRegularLocalRing (A ⧸ Ideal.span ({(x : A)} : Set A)) := by
  letI : IsNoetherianRing A := inferInstance
  let x1 : Fin 1 → maximalIdeal A := fun _ ↦ x
  have hpart :
      IsPartOfRegularSystemOfParameters (maximalIdeal A).spanFinrank x1 :=
    singleton_partOfRegularSystemOfParameters_of_not_mem_sq (A := A) x hx
  have hquot :
      IsRegularLocalRing (A ⧸ parameterIdeal x1) :=
    IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal
      (R := A) hpart
  rw [parameterIdeal_fin1_eq_span_singleton (A := A) x1] at hquot
  -- Proof comment: Lemma 10.106.3 already identifies quotienting by the parameter ideal of a
  -- partial regular system of parameters with a regular local quotient ring.
  simpa [x1] using hquot

/-- Helper for Lemma 10.106.8: quotienting a Noetherian local ring by an element outside `𝔪²`
strictly lowers the embedding dimension. -/
lemma spanFinrank_quotient_lt_of_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (x : maximalIdeal A)
    [Nontrivial (A ⧸ Ideal.span ({(x : A)} : Set A))]
    [IsLocalRing (A ⧸ Ideal.span ({(x : A)} : Set A))]
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    (maximalIdeal (A ⧸ Ideal.span ({(x : A)} : Set A))).spanFinrank <
      (maximalIdeal A).spanFinrank := by
  let d : ℕ := (maximalIdeal A).spanFinrank - 1
  have hpos : 0 < (maximalIdeal A).spanFinrank :=
    spanFinrank_pos_of_not_mem_sq (A := A) (x := x) hx
  have hspan : (maximalIdeal A).spanFinrank = d + 1 := by
    -- Proof comment: positive embedding dimension lets us rewrite the ambient span finrank as a
    -- successor, which is the size of a head-plus-tail generating family.
    dsimp [d]
    omega
  have hfinrank :
      Module.finrank (ResidueField A) (CotangentSpace A) = d + 1 := by
    -- Proof comment: in a Noetherian local ring the cotangent-space dimension is exactly the
    -- maximal-ideal span finrank.
    calc
      Module.finrank (ResidueField A) (CotangentSpace A) = (maximalIdeal A).spanFinrank := by
        rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
      _ = d + 1 := hspan
  obtain ⟨b, hb0⟩ :=
    cotangent_basis_with_prescribed_head
      (k := ResidueField A)
      (V := CotangentSpace A)
      (n := d)
      hfinrank
      ((maximalIdeal A).toCotangent x)
      (cotangent_nonzero_of_not_mem_sq (A := A) (x := x) hx)
  choose y hy using
    fun i : Fin d ↦ (maximalIdeal A).toCotangent_surjective (b i.succ)
  let w : Fin (d + 1) → maximalIdeal A := Fin.cons x y
  have hw_parameter : parameterIdeal w = maximalIdeal A := by
    calc
      parameterIdeal w = parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) y) := by
        symm
        simpa [w] using parameterIdeal_append_eq_cons (A := A) x y
      _ = maximalIdeal A := by
        -- Proof comment: the prescribed-head generator family from the cotangent-space argument
        -- already generates the maximal ideal upstairs.
        exact cotangent_lifts_generate_maximalIdeal_of_basis_with_head
          (A := A) (n := d) (x := x) (b := b) hb0 y hy
  have hhead :
      headParameterIdeal w = Ideal.span ({(x : A)} : Set A) := by
    simp [headParameterIdeal, w]
  have hhead_ne_top : headParameterIdeal w ≠ ⊤ := by
    rw [hhead]
    exact Ideal.Quotient.nontrivial_iff.mp inferInstance
  let ehead :
      (A ⧸ Ideal.span ({(x : A)} : Set A)) ≃+* (A ⧸ headParameterIdeal w) :=
    Ideal.quotEquivOfEq hhead.symm
  letI : Nontrivial (A ⧸ headParameterIdeal w) := Ideal.Quotient.nontrivial_iff.mpr hhead_ne_top
  letI : IsLocalRing (A ⧸ headParameterIdeal w) := RingEquiv.isLocalRing ehead
  let xbar : Fin d → maximalIdeal (A ⧸ headParameterIdeal w) := fun i ↦
    ⟨Ideal.Quotient.mk (headParameterIdeal w) (((w i.succ : maximalIdeal A) : A)),
      tail_image_mem_maximalIdeal w i⟩
  have hxbar_parameter : parameterIdeal xbar = maximalIdeal (A ⧸ headParameterIdeal w) := by
    -- Proof comment: mapping the upstairs parameter-ideal equality through the quotient kills the
    -- head parameter and leaves exactly the tail family downstairs.
    calc
      parameterIdeal xbar =
          Ideal.map (Ideal.Quotient.mk (headParameterIdeal w)) (parameterIdeal w) := by
            symm
            simpa [xbar] using map_parameterIdeal_eq_tail_parameterIdeal (A := A) w
      _ =
          Ideal.map (Ideal.Quotient.mk (headParameterIdeal w)) (maximalIdeal A) := by
            rw [hw_parameter]
      _ = maximalIdeal (A ⧸ headParameterIdeal w) := by
            exact IsLocalRing.map_maximalIdeal_of_surjective
              (Ideal.Quotient.mk (headParameterIdeal w))
              Ideal.Quotient.mk_surjective
  have hrange_ncard :
      (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
        A ⧸ headParameterIdeal w)).ncard ≤ d := by
    -- Proof comment: the quotient maximal ideal is generated by at most the `d` tail images.
    rw [← Nat.card_coe_set_eq]
    simpa using
      (Finite.card_range_le
        (fun i : Fin d ↦ ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
          A ⧸ headParameterIdeal w)))
  have hspanQ :
      (maximalIdeal (A ⧸ headParameterIdeal w)).spanFinrank ≤ d := by
    -- Proof comment: the mapped tail family spans the quotient maximal ideal, so the span finrank
    -- is bounded by the size of that family.
    have hspan_eq :
        maximalIdeal (A ⧸ headParameterIdeal w) =
          Ideal.span (Set.range fun i : Fin d ↦
            ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
              A ⧸ headParameterIdeal w)) := by
      simpa [parameterIdeal_eq_span] using hxbar_parameter.symm
    calc
      (maximalIdeal (A ⧸ headParameterIdeal w)).spanFinrank =
          (Ideal.span (Set.range fun i : Fin d ↦
            ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
              A ⧸ headParameterIdeal w))).spanFinrank := by
            exact congrArg Submodule.spanFinrank hspan_eq
      _ ≤
          (Set.range fun i : Fin d ↦ ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
            A ⧸ headParameterIdeal w)).ncard := by
            exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ d := hrange_ncard
  -- Proof comment: the quotient needs at most `d` generators, while the ambient maximal ideal has
  -- span finrank `d + 1`.
  calc
    (maximalIdeal (A ⧸ Ideal.span ({(x : A)} : Set A))).spanFinrank =
        (maximalIdeal (A ⧸ headParameterIdeal w)).spanFinrank := by
          rfl
    _ ≤ d := hspanQ
    _ < d + 1 := Nat.lt_succ_self d
    _ = (maximalIdeal A).spanFinrank := hspan.symm

/-- Helper for Lemma 10.106.8: an element in the square of a stage maximal ideal maps into the
square of the colimit maximal ideal. -/
lemma of_mem_maximalIdeal_sq {i : I} {x : R i}
    (hx : x ∈ maximalIdeal (R i) ^ 2) :
    Ring.DirectLimit.of R ρ i x ∈ maximalIdeal R∞ ^ 2 := by
  -- Proof comment: a local stage map sends the maximal ideal into the colimit maximal ideal, so
  -- the induced map sends its square into the square downstairs.
  have hmap :
      Ideal.map (Ring.DirectLimit.of R ρ i) (maximalIdeal (R i))
        ≤ maximalIdeal R∞ := by
    exact IsLocalRing.map_maximalIdeal_le (Ring.DirectLimit.of R ρ i)
  have hmap_sq :
      Ideal.map (Ring.DirectLimit.of R ρ i) (maximalIdeal (R i) ^ 2)
        ≤ maximalIdeal R∞ ^ 2 := by
    rw [Ideal.map_pow, pow_two, pow_two]
    exact Ideal.mul_mono hmap hmap
  exact hmap_sq (Ideal.mem_map_of_mem (Ring.DirectLimit.of R ρ i) hx)

/-- Helper for Lemma 10.106.8: if the colimit image of a lifted stage element lies outside
`𝔪^2`, then every later stage image also lies outside the square of the later maximal ideal. -/
lemma tail_image_not_mem_sq_of_colimit_not_mem_sq {i : I} (x_i : maximalIdeal (R i))
    (hx :
      Ring.DirectLimit.of R ρ i (x_i : R i) ∉ maximalIdeal R∞ ^ 2) :
    ∀ j : Set.Ici i, φ i j.1 j.2 (x_i : R i) ∉ maximalIdeal (R j.1) ^ 2 := by
  intro j hxj
  -- Proof comment: any square relation at a later stage would map to a square relation in the
  -- colimit, contradicting the hypothesis on the lifted element.
  apply hx
  simpa [Ring.DirectLimit.of_f] using
    of_mem_maximalIdeal_sq (R := R) (φ := φ)
      (i := j.1) (x := φ i j.1 j.2 (x_i : R i)) hxj

/-- Helper for Lemma 10.106.8: the principal quotient ideal in the colimit generated by the lift
of `x_i`. -/
private noncomputable abbrev quotientByLift_colimit_ideal
    (i : I) (x_i : maximalIdeal (R i)) : Ideal R∞ :=
  Ideal.span ({Ring.DirectLimit.of R ρ i (x_i : R i)} : Set R∞)

/-- Helper for Lemma 10.106.8: the principal quotient ideal in the tail stage `j`. -/
private abbrev quotientByLift_tail_ideal (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) :
    Ideal (R j.1) :=
  Ideal.span ({φ i j.1 j.2 (x_i : R i)} : Set (R j.1))

/-- Helper for Lemma 10.106.8: the tail family of quotients by the image of the chosen lift
`x_i`. -/
private abbrev quotientByLift_tail_family (i : I) (x_i : maximalIdeal (R i)) :
    Set.Ici i → Type u :=
  fun j ↦ R j.1 ⧸ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j

/-- Helper for Lemma 10.106.8: the quotient ideals along the tail are compatible with the
transition maps. -/
private theorem quotientByLift_tail_ideal_le_comap (i : I) (x_i : maximalIdeal (R i))
    {j k : Set.Ici i} (hjk : j ≤ k) :
    quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j ≤
      Ideal.comap (φ j.1 k.1 hjk)
        (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k) := by
  -- Proof comment: the generator of the stage-`j` quotient ideal maps to the corresponding
  -- generator at stage `k`, so the whole principal ideal lands in the comap.
  refine Ideal.span_le.2 ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  change φ j.1 k.1 hjk y ∈ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k
  subst y
  rw [show φ j.1 k.1 hjk (φ i j.1 j.2 (x_i : R i)) = φ i k.1 k.2 (x_i : R i) by
    simpa using
      (DirectedSystem.map_map'
        (f := fun a b hab ↦ φ a b hab) j.2 hjk (x_i : R i))]
  exact
    Ideal.subset_span
      (by
        simp : φ i k.1 k.2 (x_i : R i) ∈
          ({φ i k.1 k.2 (x_i : R i)} : Set (R k.1)))

/-- Helper for Lemma 10.106.8: the tail quotient transition map induced by the original directed
system. -/
private noncomputable def quotientByLift_tail_transition
    (i : I) (x_i : maximalIdeal (R i)) {j k : Set.Ici i} (hjk : j ≤ k) :
    quotientByLift_tail_family (R := R) (φ := φ) i x_i j →+*
      quotientByLift_tail_family (R := R) (φ := φ) i x_i k :=
  Ideal.quotientMap
    (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
    (φ j.1 k.1 hjk)
    (quotientByLift_tail_ideal_le_comap (R := R) (φ := φ) i x_i hjk)

/-- Helper for Lemma 10.106.8: the tail quotient transition sends a representative to the
corresponding later-stage representative. -/
@[simp] private theorem quotientByLift_tail_transition_mk
    (i : I) (x_i : maximalIdeal (R i)) {j k : Set.Ici i} (hjk : j ≤ k) (a : R j.1) :
    quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) =
      Ideal.Quotient.mk
        (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
        (φ j.1 k.1 hjk a) := by
  -- Proof comment: this is the defining computation rule of `Ideal.quotientMap`.
  rw [quotientByLift_tail_transition, Ideal.quotientMap_mk]

/-- Helper for Lemma 10.106.8: each tail quotient ideal is contained in the corresponding stage
maximal ideal. -/
lemma quotientByLift_tail_ideal_le_maximalIdeal
    (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) :
    quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j ≤ maximalIdeal (R j.1) := by
  -- Proof comment: the tail quotient ideal is principal, generated by the image of `x_i`, and
  -- local maps carry maximal-ideal elements into maximal ideals.
  have hgen :
      φ i j.1 j.2 (x_i : R i) ∈ maximalIdeal (R j.1) := by
    exact map_nonunit (φ i j.1 j.2) (x_i : R i) x_i.2
  simpa [quotientByLift_tail_ideal] using
    (Ideal.span_singleton_le_iff_mem (I := maximalIdeal (R j.1))
      (x := φ i j.1 j.2 (x_i : R i))).2 hgen

/-- Helper for Lemma 10.106.8: the quotient transition maps in the tail system are local ring
maps. -/
lemma quotientByLift_tail_transition_reflects_units_on_mk
    (i : I) (x_i : maximalIdeal (R i)) {j k : Set.Ici i} (hjk : j ≤ k) (a : R j.1)
    (ha :
      IsUnit
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
          (φ j.1 k.1 hjk a))) :
    IsUnit
      (Ideal.Quotient.mk
        (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) := by
  letI :
      Nontrivial
        (R j.1 ⧸ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) :=
    Ideal.Quotient.nontrivial_iff.mpr <| by
      intro htop
      exact (maximalIdeal.isMaximal (R j.1)).ne_top <|
        top_le_iff.mp (htop ▸ quotientByLift_tail_ideal_le_maximalIdeal
          (R := R) (φ := φ) i x_i j)
  letI :
      Nontrivial
        (R k.1 ⧸ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k) :=
    Ideal.Quotient.nontrivial_iff.mpr <| by
      intro htop
      exact (maximalIdeal.isMaximal (R k.1)).ne_top <|
        top_le_iff.mp (htop ▸ quotientByLift_tail_ideal_le_maximalIdeal
          (R := R) (φ := φ) i x_i k)
  letI :
      IsLocalRing
        (R j.1 ⧸ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j))
      Ideal.Quotient.mk_surjective
  letI :
      IsLocalRing
        (R k.1 ⧸ quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k))
      Ideal.Quotient.mk_surjective
  letI :
      IsLocalHom
        (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j)) :=
    IsLocalHom.of_surjective
      (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j))
      Ideal.Quotient.mk_surjective
  letI :
      IsLocalHom
        (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)) :=
    IsLocalHom.of_surjective
      (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k))
      Ideal.Quotient.mk_surjective
  have hunit_target : IsUnit (φ j.1 k.1 hjk a) := by
    -- Proof comment: first reflect the target quotient unit through the target quotient map.
    exact isUnit_of_map_unit
      (Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k))
      (φ j.1 k.1 hjk a) ha
  have hunit_source : IsUnit a := by
    -- Proof comment: then reflect the ambient unit through the original local transition map.
    exact isUnit_of_map_unit (φ j.1 k.1 hjk) a hunit_target
  -- Proof comment: finally map that source-stage unit into the source quotient.
  exact (Ideal.Quotient.mk
    (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j)).isUnit_map hunit_source

/-- Helper for Lemma 10.106.8: the quotient transition maps in the tail system are local ring
maps. -/
lemma quotientByLift_tail_transition_isLocalHom
    (i : I) (x_i : maximalIdeal (R i)) {j k : Set.Ici i} (hjk : j ≤ k) :
    IsLocalHom (quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk) := by
  refine ⟨?_⟩
  intro a
  refine Quotient.inductionOn' a (fun b => ?_)
  intro ha
  have ha' :
      IsUnit
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
          (φ j.1 k.1 hjk b)) := by
    -- Proof comment: rewrite the transition of the chosen representative using the defining
    -- quotient computation rule.
    simpa only [Ideal.Quotient.mk_eq_mk, quotientByLift_tail_transition_mk] using ha
  -- Proof comment: every quotient element has a stage representative, so locality reduces to the
  -- representative-level unit-reflection lemma.
  simpa only [Ideal.Quotient.mk_eq_mk] using
    quotientByLift_tail_transition_reflects_units_on_mk
      (R := R) (φ := φ) i x_i hjk b ha'

/-- Helper for Lemma 10.106.8: the tail quotient family is again a directed system. -/
private instance quotientByLift_tail_directedSystem
    (i : I) (x_i : maximalIdeal (R i)) :
    DirectedSystem
      (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
      (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk) where
  map_self := by
    intro j a
    -- Proof comment: quotient-induct to a stage representative and reduce the self-transition to
    -- the ambient identity map.
    refine Quotient.inductionOn' a ?_
    intro b
    calc
      (quotientByLift_tail_transition (R := R) (φ := φ) i x_i (j := j) (k := j) le_rfl)
          (Quotient.mk'' b) =
          Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j)
            (φ j.1 j.1 le_rfl b) := by
              simpa only [Ideal.Quotient.mk_eq_mk] using
                (quotientByLift_tail_transition_mk (R := R) (φ := φ) i x_i
                  (j := j) (k := j) le_rfl b)
      _ = Quotient.mk'' b := by
            rw [show φ j.1 j.1 le_rfl b = b by
              simpa using (DirectedSystem.map_self (f := fun a b hab ↦ φ a b hab) b)]
            rfl
  map_map := by
    intro j k ℓ hℓk hkℓ a
    -- Proof comment: on representatives, the quotient transition composite is induced by the
    -- ambient composite transition map.
    refine Quotient.inductionOn' a ?_
    intro b
    calc
      (quotientByLift_tail_transition (R := R) (φ := φ) i x_i hkℓ)
          ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i hℓk) (Quotient.mk'' b)) =
          Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j)
            (φ k.1 j.1 hkℓ (φ ℓ.1 k.1 hℓk b)) := by
              rw [show (quotientByLift_tail_transition (R := R) (φ := φ) i x_i hℓk)
                  (Quotient.mk'' b) =
                    Ideal.Quotient.mk
                      (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
                      (φ ℓ.1 k.1 hℓk b) by
                    simpa only [Ideal.Quotient.mk_eq_mk] using
                      (quotientByLift_tail_transition_mk (R := R) (φ := φ) i x_i
                        (j := ℓ) (k := k) hℓk b)]
              rw [quotientByLift_tail_transition_mk]
      _ =
          Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j)
            (φ ℓ.1 j.1 (le_trans hℓk hkℓ) b) := by
              exact congrArg
                (Ideal.Quotient.mk
                  (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j))
                (DirectedSystem.map_map' (f := fun a b hab ↦ φ a b hab) hℓk hkℓ b)
      _ =
          (quotientByLift_tail_transition (R := R) (φ := φ) i x_i (le_trans hℓk hkℓ))
            (Quotient.mk'' b) := by
              symm
              simpa only [Ideal.Quotient.mk_eq_mk] using
                (quotientByLift_tail_transition_mk (R := R) (φ := φ) i x_i
                  (j := ℓ) (k := j) (le_trans hℓk hkℓ) b)

/-- Helper for Lemma 10.106.8: the direct limit of the tail quotient family. -/
private abbrev quotientByLift_tail_directLimit (i : I) (x_i : maximalIdeal (R i)) :=
  Ring.DirectLimit
    (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
    (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)

/-- Helper for Lemma 10.106.8: the tail above a fixed stage is still directed. -/
private theorem quotientByLift_tail_index_isDirected (i : I) :
    IsDirectedOrder (Set.Ici i) := by
  constructor
  intro j k
  -- Proof comment: directedness of the ambient index set gives a common upper bound that still
  -- lies in the tail because both stages already dominate `i`.
  obtain ⟨ℓ, hjℓ, hkℓ⟩ := exists_ge_ge j.1 k.1
  exact ⟨⟨ℓ, le_trans j.2 hjℓ⟩, hjℓ, hkℓ⟩

/-- Helper for Lemma 10.106.8: choose a common upper bound of the ambient stage `j` and the base
stage `i` used for the tail quotient system. -/
private noncomputable def quotientByLift_tail_upper_bound (i j : I) : I :=
  (exists_ge_ge j i).choose

/-- Helper for Lemma 10.106.8: the chosen tail upper bound lies above the original ambient stage.
-/
private theorem le_quotientByLift_tail_upper_bound_left (i j : I) :
    j ≤ quotientByLift_tail_upper_bound i j :=
  (exists_ge_ge j i).choose_spec.1

/-- Helper for Lemma 10.106.8: the chosen tail upper bound lies above the base stage `i`. -/
private theorem le_quotientByLift_tail_upper_bound_right (i j : I) :
    i ≤ quotientByLift_tail_upper_bound i j :=
  (exists_ge_ge j i).choose_spec.2

/-- Helper for Lemma 10.106.8: every ambient stage maps canonically into the direct limit of the
tail quotient system by first moving to a chosen upper tail stage and then taking the quotient
class there. -/
private noncomputable def quotientByLift_full_stage_to_tail_directLimit
    (i : I) (x_i : maximalIdeal (R i)) (j : I) :
    R j →+* quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i :=
  let k : Set.Ici i :=
    ⟨quotientByLift_tail_upper_bound i j, le_quotientByLift_tail_upper_bound_right i j⟩
  (Ring.DirectLimit.of
      (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
      (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
      k).comp
    ((Ideal.Quotient.mk (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)).comp
      (φ j k.1 (le_quotientByLift_tail_upper_bound_left i j)))

/-- Helper for Lemma 10.106.8: the reverse ambient-stage map to the tail quotient direct limit can
be normalized at any explicit tail stage dominating the ambient stage. -/
private theorem quotientByLift_full_stage_to_tail_directLimit_eq_of_le
    (i : I) (x_i : maximalIdeal (R i)) {j : I} (ℓ : Set.Ici i) (h : j ≤ ℓ.1) (a : R j) :
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j a =
      Ring.DirectLimit.of
        (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
        (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
        ℓ
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ)
          (φ j ℓ.1 h a)) := by
  let k : Set.Ici i :=
    ⟨quotientByLift_tail_upper_bound i j, le_quotientByLift_tail_upper_bound_right i j⟩
  let m : Set.Ici i :=
    ⟨(exists_ge_ge k.1 ℓ.1).choose,
      le_trans k.2 (exists_ge_ge k.1 ℓ.1).choose_spec.1⟩
  have hkm : k ≤ m := (exists_ge_ge k.1 ℓ.1).choose_spec.1
  have hℓm : ℓ ≤ m := (exists_ge_ge k.1 ℓ.1).choose_spec.2
  -- Proof comment: move the chosen representative stage `k` and the explicit target stage `ℓ`
  -- to a common tail stage `m`, then compare the representatives there.
  calc
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j a =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          k
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
            (φ j k.1 (le_quotientByLift_tail_upper_bound_left i j) a)) := by
          simp [quotientByLift_full_stage_to_tail_directLimit, k]
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          m
          ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i hkm)
            (Ideal.Quotient.mk
              (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
              (φ j k.1 (le_quotientByLift_tail_upper_bound_left i j) a))) := by
          symm
          exact Ring.DirectLimit.of_f
            (f := fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
            hkm _
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          m
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i m)
            (φ j m.1
              (le_trans (le_quotientByLift_tail_upper_bound_left i j) hkm) a)) := by
          rw [quotientByLift_tail_transition_mk]
          exact congrArg
            (fun z ↦
              Ring.DirectLimit.of
                (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
                (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
                m
                (Ideal.Quotient.mk
                  (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i m) z))
            (DirectedSystem.map_map'
              (f := fun a b hab ↦ φ a b hab)
              (le_quotientByLift_tail_upper_bound_left i j) hkm a)
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          m
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i m)
            (φ ℓ.1 m.1 hℓm (φ j ℓ.1 h a))) := by
          exact congrArg
            (fun z ↦
              Ring.DirectLimit.of
                (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
                (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
                m
                (Ideal.Quotient.mk
                  (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i m) z))
            ((DirectedSystem.map_map'
              (f := fun a b hab ↦ φ a b hab) h hℓm a).symm)
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          m
          ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i hℓm)
            (Ideal.Quotient.mk
              (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ)
              (φ j ℓ.1 h a))) := by
          rw [quotientByLift_tail_transition_mk]
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          ℓ
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ)
            (φ j ℓ.1 h a)) := by
          exact Ring.DirectLimit.of_f
            (f := fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
            hℓm _

/-- Helper for Lemma 10.106.8: the ambient-stage maps into the tail quotient direct limit are
compatible with the original transition maps. -/
private theorem quotientByLift_full_stage_to_tail_directLimit_compatible
    (i : I) (x_i : maximalIdeal (R i)) {j k : I} (hjk : j ≤ k) (a : R j) :
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i k
        (φ j k hjk a) =
      quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j a := by
  let ℓ : Set.Ici i :=
    ⟨quotientByLift_tail_upper_bound i k, le_quotientByLift_tail_upper_bound_right i k⟩
  -- Proof comment: normalize both ambient-stage maps at the same explicit tail stage `ℓ`.
  calc
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i k
        (φ j k hjk a) =
      Ring.DirectLimit.of
        (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
        (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
        ℓ
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ)
          (φ k ℓ.1 (le_quotientByLift_tail_upper_bound_left i k) (φ j k hjk a))) := by
        exact quotientByLift_full_stage_to_tail_directLimit_eq_of_le
          (R := R) (φ := φ) i x_i ℓ
          (le_quotientByLift_tail_upper_bound_left i k) (φ j k hjk a)
    _ =
      Ring.DirectLimit.of
        (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
        (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
        ℓ
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ)
          (φ j ℓ.1
            (le_trans hjk (le_quotientByLift_tail_upper_bound_left i k)) a)) := by
        exact congrArg
          (fun z ↦
            Ring.DirectLimit.of
              (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
              (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
              ℓ
              (Ideal.Quotient.mk
                (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i ℓ) z))
          (DirectedSystem.map_map'
            (f := fun a b hab ↦ φ a b hab) hjk
            (le_quotientByLift_tail_upper_bound_left i k) a)
    _ =
      quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j a := by
        symm
        exact quotientByLift_full_stage_to_tail_directLimit_eq_of_le
          (R := R) (φ := φ) i x_i ℓ
          (le_trans hjk (le_quotientByLift_tail_upper_bound_left i k)) a

/-- Helper for Lemma 10.106.8: the ambient direct limit maps canonically to the direct limit of
the tail quotient system. -/
private noncomputable def quotientByLift_full_directLimitToTail
    (i : I) (x_i : maximalIdeal (R i)) :
    R∞ →+* quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i :=
  Ring.DirectLimit.lift R ρ
    (quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i)
    (fun j ↦ quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j)
    (fun _ _ hij a ↦
      quotientByLift_full_stage_to_tail_directLimit_compatible
        (R := R) (φ := φ) i x_i hij a)

/-- Helper for Lemma 10.106.8: the chosen lifted generator becomes zero in the tail quotient
direct limit, so the ambient map descends through the principal quotient. -/
private theorem quotientByLift_full_directLimit_to_tail_lifted_eq_zero
    (i : I) (x_i : maximalIdeal (R i)) :
    quotientByLift_full_directLimitToTail (R := R) (φ := φ) i x_i
        (Ring.DirectLimit.of R ρ i (x_i : R i)) = 0 := by
  let k : Set.Ici i :=
    ⟨quotientByLift_tail_upper_bound i i, le_quotientByLift_tail_upper_bound_right i i⟩
  -- Proof comment: at the chosen tail stage, the lifted element is the chosen generator of the
  -- quotient ideal, so its quotient class is zero.
  rw [quotientByLift_full_directLimitToTail, Ring.DirectLimit.lift_of]
  change Ring.DirectLimit.of
      (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
      (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
      k
      (Ideal.Quotient.mk
        (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
        (φ i k.1 (le_quotientByLift_tail_upper_bound_left i i) (x_i : R i))) = 0
  have hkzero :
      Ideal.Quotient.mk
        (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
        (φ i k.1 (le_quotientByLift_tail_upper_bound_left i i) (x_i : R i)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span
      (by simp : φ i k.1 (le_quotientByLift_tail_upper_bound_left i i) (x_i : R i) ∈
        ({φ i k.1 k.2 (x_i : R i)} : Set (R k.1)))
  rw [hkzero]
  simp

/-- Helper for Lemma 10.106.8: the ambient quotient maps back to the direct limit of tail
quotients because the lifted generator already vanishes there. -/
private noncomputable def quotientByLift_quotientToTail_directLimit
    (i : I) (x_i : maximalIdeal (R i)) :
    R∞ ⧸ quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i →+*
      quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i :=
  let hker :
      quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i ≤
        RingHom.ker (quotientByLift_full_directLimitToTail (R := R) (φ := φ) i x_i) := by
    -- Proof comment: the quotient ideal is generated by the lifted element already sent to zero.
    refine Ideal.span_le.2 ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact RingHom.mem_ker.mpr
      (quotientByLift_full_directLimit_to_tail_lifted_eq_zero (R := R) (φ := φ) i x_i)
  Ideal.Quotient.lift
    (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
    (quotientByLift_full_directLimitToTail (R := R) (φ := φ) i x_i)
    (fun a ha ↦ RingHom.mem_ker.mp (hker ha))

/-- Helper for Lemma 10.106.8: if the ambient representative already comes from a tail stage, the
reverse map lands on the corresponding canonical tail-stage class. -/
private theorem quotientByLift_full_stage_to_tail_directLimit_of_tail
    (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) (a : R j.1) :
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j.1 a =
      Ring.DirectLimit.of
        (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
        (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
        j
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) := by
  let k : Set.Ici i :=
    ⟨quotientByLift_tail_upper_bound i j.1, le_quotientByLift_tail_upper_bound_right i j.1⟩
  -- Proof comment: a tail-stage input is represented at the chosen upper tail stage by the
  -- quotient transition of its own canonical class, so `Ring.DirectLimit.of_f` collapses back to
  -- the original tail generator.
  calc
    quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j.1 a =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          k
          ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i
            (le_quotientByLift_tail_upper_bound_left i j.1))
            (Ideal.Quotient.mk
              (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a)) := by
          simp only [quotientByLift_full_stage_to_tail_directLimit, k, RingHom.comp_apply]
          rw [quotientByLift_tail_transition_mk]
    _ =
        Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
          j
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) := by
          exact Ring.DirectLimit.of_f
            (f := fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
            (le_quotientByLift_tail_upper_bound_left i j.1) _

/-- Helper for Lemma 10.106.8: on a tail-stage ambient quotient class, the descended reverse map
computes to the corresponding generator of the tail quotient direct limit. -/
@[simp] private theorem quotientByLift_quotientToTail_directLimit_mk_of_tail
    (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) (a : R j.1) :
    quotientByLift_quotientToTail_directLimit (R := R) (φ := φ) i x_i
        (Ideal.Quotient.mk
          (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
          (Ring.DirectLimit.of R ρ j.1 a)) =
      Ring.DirectLimit.of
        (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
        (fun a b hab ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hab)
        j
        (Ideal.Quotient.mk
          (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) := by
  -- Proof comment: the descended reverse map is defined by `Ideal.Quotient.lift`, so on a
  -- tail-stage ambient representative it is exactly the normalized full-stage map.
  rw [quotientByLift_quotientToTail_directLimit, Ideal.Quotient.lift_mk]
  exact quotientByLift_full_stage_to_tail_directLimit_of_tail (R := R) (φ := φ) i x_i j a

/-- Helper for Lemma 10.106.8: each tail-stage quotient maps canonically to the colimit quotient.
-/
private theorem quotientByLift_stage_ideal_le_colimit_comap
    (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) :
    quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j ≤
      Ideal.comap (Ring.DirectLimit.of R ρ j.1)
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i) := by
  -- Proof comment: the tail generator maps to the ambient generator by the direct-limit relation.
  refine Ideal.span_le.2 ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst y
  change Ring.DirectLimit.of R ρ j.1 (φ i j.1 j.2 (x_i : R i)) ∈
    quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i
  simpa [quotientByLift_colimit_ideal, Ring.DirectLimit.of_f] using
    (Ideal.subset_span
      (by simp : Ring.DirectLimit.of R ρ i (x_i : R i) ∈
        ({Ring.DirectLimit.of R ρ i (x_i : R i)} : Set R∞)))

/-- Helper for Lemma 10.106.8: the forward map from the direct limit of tail quotients to the
quotient of the ambient direct limit. -/
private theorem quotientByLift_directLimitToQuotient_compatible
    (i : I) (x_i : maximalIdeal (R i)) {j k : Set.Ici i} (hjk : j ≤ k)
    (a : quotientByLift_tail_family (R := R) (φ := φ) i x_i j) :
    Ideal.quotientMap
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
        (Ring.DirectLimit.of R ρ k.1)
        (quotientByLift_stage_ideal_le_colimit_comap (R := R) (φ := φ) i x_i k)
        ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk) a) =
      Ideal.quotientMap
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
        (Ring.DirectLimit.of R ρ j.1)
        (quotientByLift_stage_ideal_le_colimit_comap (R := R) (φ := φ) i x_i j)
        a := by
  -- Proof comment: quotient-induct to a stage representative, rewrite both quotient maps to the
  -- same ambient quotient constructor, and use the direct-limit relation upstairs.
  refine Quotient.inductionOn' a ?_
  intro b
  calc
    Ideal.quotientMap
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
        (Ring.DirectLimit.of R ρ k.1)
        (quotientByLift_stage_ideal_le_colimit_comap (R := R) (φ := φ) i x_i k)
        ((quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk) (Quotient.mk'' b)) =
        Ideal.Quotient.mk
          (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
          (Ring.DirectLimit.of R ρ k.1 (φ j.1 k.1 hjk b)) := by
            rw [show (quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
                (Quotient.mk'' b) =
                  Ideal.Quotient.mk
                    (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
                    (φ j.1 k.1 hjk b) by
                  simpa only [Ideal.Quotient.mk_eq_mk] using
                    (quotientByLift_tail_transition_mk (R := R) (φ := φ) i x_i
                      (j := j) (k := k) hjk b)]
            rw [Ideal.quotientMap_mk]
    _ =
        Ideal.Quotient.mk
          (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
          (Ring.DirectLimit.of R ρ j.1 b) := by
            exact congrArg
              (Ideal.Quotient.mk (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i))
              (Ring.DirectLimit.of_f (G := R) (f := ρ) hjk b)
    _ =
        Ideal.quotientMap
          (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
          (Ring.DirectLimit.of R ρ j.1)
          (quotientByLift_stage_ideal_le_colimit_comap (R := R) (φ := φ) i x_i j)
          (Quotient.mk'' b) := by
            rfl

/-- Helper for Lemma 10.106.8: the forward map from the direct limit of tail quotients to the
quotient of the ambient direct limit. -/
private noncomputable def quotientByLift_directLimitToQuotient
    (i : I) (x_i : maximalIdeal (R i)) :
    quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i →+*
      R∞ ⧸ quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i :=
  Ring.DirectLimit.lift
    (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
    (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
    (R∞ ⧸ quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
    (fun j ↦
      Ideal.quotientMap
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
        (Ring.DirectLimit.of R ρ j.1)
        (quotientByLift_stage_ideal_le_colimit_comap (R := R) (φ := φ) i x_i j))
    (fun j k hjk a ↦
      quotientByLift_directLimitToQuotient_compatible
        (R := R) (φ := φ) i x_i hjk a)

/-- Helper for Lemma 10.106.8: the forward quotient comparison sends a tail-stage generator to the
corresponding colimit quotient class. -/
@[simp] private theorem quotientByLift_equiv_directLimit_quotients_apply_of
    (i : I) (x_i : maximalIdeal (R i)) (j : Set.Ici i) (a : R j.1) :
    quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
        (Ring.DirectLimit.of
          (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
          (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
          j
          (Ideal.Quotient.mk
            (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a)) =
      Ideal.Quotient.mk
        (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
        (Ring.DirectLimit.of R ρ j.1 a) := by
  -- Proof comment: this is the defining `Ring.DirectLimit.lift_of` formula composed with
  -- `Ideal.quotientMap_mk`.
  rw [quotientByLift_directLimitToQuotient, Ring.DirectLimit.lift_of, Ideal.quotientMap_mk]

/-- Helper for Lemma 10.106.8: the quotient of the ambient direct limit by the lifted generator is
canonically the direct limit of the tail stagewise quotients. -/
private noncomputable def quotientByLift_equiv_directLimit_quotients
    (i : I) (x_i : maximalIdeal (R i)) :
    quotientByLift_tail_directLimit (R := R) (φ := φ) i x_i ≃+*
      R∞ ⧸ quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i :=
  { toFun := quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
    invFun := quotientByLift_quotientToTail_directLimit (R := R) (φ := φ) i x_i
    left_inv := by
      letI : IsDirectedOrder (Set.Ici i) := quotientByLift_tail_index_isDirected (i := i)
      intro z
      -- Proof comment: both comparison maps are defined stagewise, so it suffices to evaluate on
      -- a canonical generator from one tail stage.
      refine Ring.DirectLimit.induction_on z ?_
      intro j q
      refine Quotient.inductionOn' q ?_
      intro a
      calc
        quotientByLift_quotientToTail_directLimit (R := R) (φ := φ) i x_i
            (quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
              (Ring.DirectLimit.of
                (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
                (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
                j
                (Ideal.Quotient.mk
                  (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a))) =
          quotientByLift_quotientToTail_directLimit (R := R) (φ := φ) i x_i
            (Ideal.Quotient.mk
              (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
              (Ring.DirectLimit.of R ρ j.1 a)) := by
              rw [quotientByLift_equiv_directLimit_quotients_apply_of]
        _ =
          Ring.DirectLimit.of
            (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
            (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
            j
            (Ideal.Quotient.mk
              (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i j) a) := by
              exact quotientByLift_quotientToTail_directLimit_mk_of_tail
                (R := R) (φ := φ) i x_i j a
    right_inv := by
      intro z
      -- Proof comment: descend to an ambient stage representative, rewrite the reverse map to
      -- its defining tail-stage representative, and then use the direct-limit relation upstairs.
      refine Quotient.inductionOn' z ?_
      intro z
      refine Ring.DirectLimit.induction_on z ?_
      intro j a
      let k : Set.Ici i :=
        ⟨quotientByLift_tail_upper_bound i j, le_quotientByLift_tail_upper_bound_right i j⟩
      calc
        quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
            (quotientByLift_quotientToTail_directLimit (R := R) (φ := φ) i x_i
              (Ideal.Quotient.mk
                (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
                (Ring.DirectLimit.of R ρ j a))) =
          quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
            (quotientByLift_full_stage_to_tail_directLimit (R := R) (φ := φ) i x_i j a) := by
              rw [quotientByLift_quotientToTail_directLimit, Ideal.Quotient.lift_mk]
              rw [quotientByLift_full_directLimitToTail, Ring.DirectLimit.lift_of]
        _ =
          quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i
            (Ring.DirectLimit.of
              (quotientByLift_tail_family (R := R) (φ := φ) i x_i)
              (fun j k hjk ↦ quotientByLift_tail_transition (R := R) (φ := φ) i x_i hjk)
              k
              (Ideal.Quotient.mk
                (quotientByLift_tail_ideal (R := R) (φ := φ) i x_i k)
                (φ j k.1 (le_quotientByLift_tail_upper_bound_left i j) a))) := by
              simp [quotientByLift_full_stage_to_tail_directLimit, k]
        _ =
          Ideal.Quotient.mk
            (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
            (Ring.DirectLimit.of R ρ k.1
              (φ j k.1 (le_quotientByLift_tail_upper_bound_left i j) a)) := by
              rw [quotientByLift_equiv_directLimit_quotients_apply_of]
        _ =
          Ideal.Quotient.mk
            (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i)
            (Ring.DirectLimit.of R ρ j a) := by
              exact congrArg
                (Ideal.Quotient.mk
                  (quotientByLift_colimit_ideal (R := R) (φ := φ) i x_i))
                (Ring.DirectLimit.of_f (G := R) (f := ρ)
                  (le_quotientByLift_tail_upper_bound_left i j) a)
    map_mul' := by
      intro x y
      exact (quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i).map_mul x y
    map_add' := by
      intro x y
      exact (quotientByLift_directLimitToQuotient (R := R) (φ := φ) i x_i).map_add x y }

/-- Helper for Lemma 10.106.8: a directed colimit of regular local rings with local transition
maps is regular once its embedding dimension is bounded above by `n`. -/
theorem isRegularLocalRing_of_spanFinrank_le {n : ℕ}
    (hNoethR : IsNoetherianRing R∞)
    (hspan : (maximalIdeal R∞).spanFinrank ≤ n) :
    IsRegularLocalRing R∞ := by
  let haux :
        ∀ m : ℕ,
        ∀ {J : Type v} [Preorder J] (S : J → Type u) [∀ j, CommRing (S j)]
          (σ : ∀ j k, j ≤ k → S j →+* S k),
          [Nonempty J] → [IsDirectedOrder J] → [DirectedSystem S (σ · · ·)] →
          [∀ j, IsRegularLocalRing (S j)] → [∀ j k hjk, IsLocalHom (σ j k hjk)] →
          (hNoeth : IsNoetherianRing (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))) →
          (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank ≤ m →
          IsRegularLocalRing (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := by
      intro m
      induction m with
      | zero =>
          intro J _ S _ σ _ _ _ _ _ hNoeth hspanS
          letI : IsNoetherianRing (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := hNoeth
          have hspan0 :
              (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank = 0 :=
            Nat.eq_zero_of_le_zero hspanS
          have hfg :
              (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).FG :=
            (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).fg_of_isNoetherianRing
          have hbot :
              maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) = ⊥ :=
            (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan0
          have hfield :
              IsField (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) :=
            (IsLocalRing.isField_iff_maximalIdeal_eq
              (R := Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).2 hbot
          letI : Field (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := hfield.toField
          exact inferInstance
      | succ m ih =>
          intro J _ S _ σ _ _ _ _ _ hNoeth hspanS
          letI : IsNoetherianRing (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := hNoeth
          by_cases hzero :
              (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank = 0
          · have hfg :
                (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).FG :=
              (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).fg_of_isNoetherianRing
            have hbot :
                maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) = ⊥ :=
              (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hzero
            have hfield :
                IsField (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) :=
              (IsLocalRing.isField_iff_maximalIdeal_eq
                (R := Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).2 hbot
            letI : Field (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := hfield.toField
            exact inferInstance
          · have hpos :
                0 < (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank :=
              Nat.pos_of_ne_zero hzero
            have hfinrank_pos :
                0 <
                  Module.finrank
                    (ResidueField (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)))
                    (CotangentSpace (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))) := by
              simpa [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace
                (R := Ring.DirectLimit S (fun a b hab ↦ σ a b hab))] using hpos
            obtain ⟨v, hv⟩ :=
              Module.finrank_pos_iff_exists_ne_zero.mp hfinrank_pos
            obtain ⟨xInf, hxv⟩ :=
              (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).toCotangent_surjective v
            have hx_not_mem_sq :
                (xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ∉
                  maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ^ 2 := by
              intro hx_sq
              apply hv
              have hx_zero :
                  (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).toCotangent xInf = 0 :=
                ((maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).toCotangent_eq_zero xInf).2 hx_sq
              simpa [hxv] using hx_zero
            obtain ⟨i, a, ha⟩ :=
              Ring.DirectLimit.exists_of (G := S) (f := fun a b hab ↦ σ a b hab)
                (xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
            have ha_mem :
                a ∈ maximalIdeal (S i) := by
              -- Proof comment: the colimit image of `a` lies in the maximal ideal, so the local
              -- stage map forces `a` itself to be a nonunit.
              intro ha_unit
              exact xInf.2 <| by
                simpa [ha] using
                  (Ring.DirectLimit.of S (fun a b hab ↦ σ a b hab) i).isUnit_map ha_unit
            let x_i : maximalIdeal (S i) := ⟨a, ha_mem⟩
            have hx_colim :
                Ring.DirectLimit.of S (fun a b hab ↦ σ a b hab) i (x_i : S i) ∉
                  maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ^ 2 := by
              simpa [x_i, ha] using hx_not_mem_sq
            have htail_not_mem_sq :
                ∀ j : Set.Ici i,
                  σ i j.1 j.2 (x_i : S i) ∉ maximalIdeal (S j.1) ^ 2 :=
              tail_image_not_mem_sq_of_colimit_not_mem_sq (R := S) (φ := σ) x_i hx_colim
            let tailElem : ∀ j : Set.Ici i, maximalIdeal (S j.1) :=
              fun j ↦ ⟨σ i j.1 j.2 (x_i : S i), map_nonunit (σ i j.1 j.2) _ x_i.2⟩
            letI :
                ∀ j : Set.Ici i,
                  IsRegularLocalRing
                    (quotientByLift_tail_family (R := S) (φ := σ) i x_i j) :=
              fun j ↦ by
                simpa [quotientByLift_tail_family, quotientByLift_tail_ideal, tailElem] using
                  (stage_quotient_isRegularLocalRing_of_not_mem_sq
                    (A := S j.1) (x := tailElem j) (htail_not_mem_sq j))
            letI :
                ∀ j k hjk,
                  IsLocalHom
                    (quotientByLift_tail_transition (R := S) (φ := σ) i x_i (j := j) (k := k)
                      hjk) :=
              fun j k hjk ↦
                quotientByLift_tail_transition_isLocalHom (R := S) (φ := σ) i x_i hjk
            have hnoeth_quot :
                IsNoetherianRing
                  (((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)) :=
              inferInstance
            let equot :
                ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                  quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i) ≃+*
                  quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i :=
              (quotientByLift_equiv_directLimit_quotients (R := S) (φ := σ) i x_i).symm
            letI :
                IsNoetherianRing
                  (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i) :=
              @isNoetherianRing_of_ringEquiv
                ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                  quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)
                _
                (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i)
                _
                equot
            have htail_span_eq :
                (maximalIdeal (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i)).spanFinrank =
                  (maximalIdeal
                    ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                      quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)).spanFinrank := by
              -- Proof comment: the quotient/direct-limit comparison is a ring equivalence, so it
              -- preserves the maximal ideal and its span finrank.
              calc
                (maximalIdeal
                  ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)).spanFinrank =
                    (Ideal.map
                      (quotientByLift_equiv_directLimit_quotients (R := S) (φ := σ) i x_i)
                      (maximalIdeal
                        (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i))).spanFinrank := by
                          rw [IsLocalRing.map_ringEquiv_maximalIdeal]
                _ =
                    (maximalIdeal
                      (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i)).spanFinrank := by
                        simpa using Ideal.spanFinrank_map_eq_of_ringEquiv
                          (quotientByLift_equiv_directLimit_quotients (R := S) (φ := σ) i x_i)
                          (maximalIdeal
                            (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i))
            have hquot_lt :
                (maximalIdeal
                  ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)).spanFinrank <
                  (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank := by
              -- Proof comment: quotienting by an element outside `𝔪²` strictly lowers embedding
              -- dimension.
              simpa [quotientByLift_colimit_ideal, ha] using
                (spanFinrank_quotient_lt_of_not_mem_sq
                  (A := Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) (x := xInf) hx_not_mem_sq)
            have htail_span_le :
                (maximalIdeal (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i)).spanFinrank ≤
                  m := by
              -- Proof comment: the quotient direct limit has strictly smaller embedding dimension,
              -- so the induction hypothesis applies one step down.
              have htail_lt :
                  (maximalIdeal (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i)).spanFinrank <
                    (maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))).spanFinrank := by
                rw [htail_span_eq]
                exact hquot_lt
              omega
            have htail_regular :
                IsRegularLocalRing (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i) :=
              ih
                (S := quotientByLift_tail_family (R := S) (φ := σ) i x_i)
                (σ := fun j k hjk ↦ quotientByLift_tail_transition (R := S) (φ := σ) i x_i hjk)
                inferInstance
                htail_span_le
            have hquot_regular_lifted :
                IsRegularLocalRing
                  (((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)) := by
              letI :
                  IsRegularLocalRing
                    (quotientByLift_tail_directLimit (R := S) (φ := σ) i x_i) :=
                htail_regular
              exact IsRegularLocalRing.of_ringEquiv
                (quotientByLift_equiv_directLimit_quotients (R := S) (φ := σ) i x_i)
            have hquot_regular :
                IsRegularLocalRing
                  ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    Ideal.span ({(xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab))} : Set
                      (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)))) := by
              -- Proof comment: rewrite the lifted-generator quotient ideal to the quotient by the
              -- chosen colimit element itself.
              let e :
                  ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i) ≃+*
                    ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                      Ideal.span ({(xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab))} : Set
                        (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)))) :=
                Ideal.quotEquivOfEq <| by
                  simp [quotientByLift_colimit_ideal, ha]
              letI :
                  IsRegularLocalRing
                    (((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                      quotientByLift_colimit_ideal (R := S) (φ := σ) i x_i)) :=
                hquot_regular_lifted
              exact IsRegularLocalRing.of_ringEquiv e
            have hx_ne_zero :
                (xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ≠ 0 := by
              -- Proof comment: `0` always lies in `𝔪²`, so an element outside `𝔪²` is nonzero.
              intro hx0
              apply hx_not_mem_sq
              simpa [hx0] using
                (show (0 : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ∈
                  maximalIdeal (Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ^ 2 from
                    Ideal.zero_mem _)
            have hx_smul_regular :
                IsSMulRegular (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
                  (xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) := by
              -- Proof comment: the colimit is a domain, so every nonzero element acts regularly
              -- on the ring viewed as a module over itself.
              rw [isSMulRegular_iff_right_eq_zero_of_smul]
              intro y hy
              exact (mul_eq_zero.mp hy).resolve_left hx_ne_zero
            have hx_regular :
                IsRegular (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
                  [xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)] := by
              -- Proof comment: a singleton regular sequence is exactly one regular scalar action.
              exact IsRegular.cons hx_smul_regular
                (IsRegular.nil
                  (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
                  (QuotSMulTop (xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
                    (Ring.DirectLimit S (fun a b hab ↦ σ a b hab))))
            have hquot_regular_ofList :
                IsRegularLocalRing
                  ((Ring.DirectLimit S (fun a b hab ↦ σ a b hab)) ⧸
                    Ideal.ofList [xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)]) := by
              simpa [Ideal.ofList_singleton] using hquot_regular
            -- Proof comment: Lemma 10.106.7 lifts regular-locality back across quotienting by the
            -- singleton regular sequence generated by `xInf`.
            exact isRegularLocalRing_of_quotient_of_isRegular
              (R := Ring.DirectLimit S (fun a b hab ↦ σ a b hab))
              (rs := [xInf : Ring.DirectLimit S (fun a b hab ↦ σ a b hab)])
              hx_regular hquot_regular_ofList
  have hNoeth :
      IsNoetherianRing (Ring.DirectLimit R (fun a b hab ↦ φ a b hab)) := by
    simpa using hNoethR
  have hDirected : DirectedSystem R ρ := by
    simpa using (inferInstance : DirectedSystem R (φ · · ·))
  have hStageRegular : ∀ i : I, IsRegularLocalRing (R i) := fun i ↦ inferInstance
  have hStageLocalMap : ∀ i j hij, IsLocalHom (φ i j hij) := fun i j hij ↦ inferInstance
  exact @haux n I inferInstance R inferInstance ρ
    ‹Nonempty I› ‹IsDirectedOrder I› hDirected hStageRegular hStageLocalMap hNoeth hspan

-- Proof sketch: equip the direct limit with the local-ring structure from the previous instance.
-- The regular-local criterion can then be proved by induction on the embedding dimension of the
-- colimit, following the Stacks Project argument: kill an element outside `𝔪²`, use the quotient
-- regularity criterion on sufficiently large stages, and conclude from the nonzerodivisor
-- criterion for regular local rings.
/-- Lemma 10.106.8: if `(R i, φ i j)` is a directed system of regular local rings whose transition
maps are local ring maps, and if the direct limit ring `R∞` is Noetherian, then `R∞` is a regular
local ring. -/
theorem isRegularLocalRing (hNoethR : IsNoetherianRing R∞) :
    IsRegularLocalRing (Ring.DirectLimit R ρ) := by
  letI : IsLocalRing R∞ := Ring.DirectLimit.isLocalRing R φ
  letI : IsDomain R∞ := Ring.DirectLimit.isDomain R φ
  -- Route correction: the quotient comparison and the strict embedding-dimension drop are now
  -- formalized, so the remaining gap is the generic strong-induction packaging over arbitrary tail
  -- quotient systems.
  -- Proof comment: the source proof chooses `x ∈ maximalIdeal R∞ \ maximalIdeal R∞ ^ 2`,
  -- identifies `R∞ ⧸ Ideal.span ({x} : Set R∞)` with a tail direct limit of stagewise quotients,
  -- recurses on the strictly smaller quotient embedding dimension, and then lifts regularity back
  -- with Lemma 10.106.7.
  exact isRegularLocalRing_of_spanFinrank_le (R := R) (φ := φ)
    (n := (maximalIdeal R∞).spanFinrank)
    hNoethR
    le_rfl

instance [IsNoetherianRing R∞] : IsRegularLocalRing (Ring.DirectLimit R ρ) :=
  isRegularLocalRing R φ inferInstance

end Regular

end Ring.DirectLimit

end
