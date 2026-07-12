import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap10.Lemma_10_106_7
import StacksProject_2024.Chap10.Lemma_10_140_5
import StacksProject_2024.Chap10.Lemma_10_140_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open IsLocalRing

universe u v

namespace Algebra

section

variable {k : Type u} {S : Type v}
variable [Field k] [CharZero k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Domain-style sampling for Lemma 10.140.7:
- primary domain: primewise smoothness criteria for finite type algebras over a characteristic-zero
  field, organized around the local owner `Localization.AtPrime q`;
- sampled owner declarations:
  `Algebra.IsSmoothAt`,
  `Algebra.FormallySmooth.projective_kaehlerDifferential`,
  `KaehlerDifferential.finite`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- best owner abstraction: the canonical owner is the ideal-level smoothness predicate
  `IsSmoothAt k q` for a prime ideal `q : Ideal S`; the `PrimeSpectrum S` wrapper carried no extra
  mathematical data here, so the public theorem should live directly on `q`, with the localized
  Kähler module and the regular-local condition as derived views of the same owner local ring
  `Localization.AtPrime q`;
- primitive data: a prime ideal `q : Ideal S`;
- derived API: the finite/free condition on `Ω[Localization.AtPrime q⁄k]` and the regular-local
  condition on `Localization.AtPrime q`.

Source/core/bridge triage:
- `source-facing`: the three-way Stacks criterion relating smoothness, finite freeness of the local
  Kähler module, and regularity of the local ring;
- `core/canonical`: `IsSmoothAt k q`, equivalently `FormallySmooth k (Localization.AtPrime q)`,
  together with `IsRegularLocalRing (Localization.AtPrime q)`;
- `bridge/view`: the finite/free Kähler-differential clause, which is derived from the local smooth
  owner rather than a second owner abstraction.
-/

variable (q : Ideal S) [q.IsPrime]

local notation "S_q" => Localization.AtPrime q
local notation "Ω_q" => Ω[S_q⁄k]

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a vector in a free module over a local ring with nonzero
residue-field tensor has a linear functional taking the value `1` on it. -/
private theorem exists_linearMap_eq_one_of_residue_tensor_ne_zero
    {A M : Type*} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    [Module.Free A M] (m : M)
    (hm : (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m ≠ 0) :
    ∃ θ : M →ₗ[A] A, θ m = 1 := by
  classical
  -- Proof comment: choose coordinates for the free module and detect a nonzero residue
  -- coordinate of `m` after tensoring with the residue field.
  let b := Module.Free.chooseBasis A M
  let bK := Algebra.TensorProduct.basis (IsLocalRing.ResidueField A) b
  have hrepr_ne :
      bK.repr ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] m) ≠ 0 := by
    intro hzero
    apply hm
    exact bK.repr.injective hzero
  have hmap_ne :
      Finsupp.mapRange (algebraMap A (IsLocalRing.ResidueField A)) (map_zero _) (b.repr m) ≠
        0 := by
    intro hzero
    apply hrepr_ne
    simpa [bK, Algebra.TensorProduct.basis_repr_tmul] using hzero
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hmap_ne
  have hcoord_residue_ne :
      algebraMap A (IsLocalRing.ResidueField A) (b.repr m i) ≠ 0 := by
    simpa using hi
  have hcoord_not_mem : b.repr m i ∉ IsLocalRing.maximalIdeal A := by
    intro hmem
    apply hcoord_residue_ne
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using
      ((IsLocalRing.residue_eq_zero_iff (R := A) (x := b.repr m i)).mpr hmem)
  have hunit : IsUnit (b.repr m i) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact hcoord_not_mem
  -- Proof comment: rescale the selected coordinate functional by the inverse of that unit.
  let u : Aˣ := hunit.unit
  let θ : M →ₗ[A] A := (↑u⁻¹ : A) • b.coord i
  refine ⟨θ, ?_⟩
  have hcoord : b.coord i m = (b.repr m i) := by
    rfl
  have hu : (u : A) = b.repr m i := hunit.unit_spec
  calc
    θ m = (↑u⁻¹ : A) * b.coord i m := by rfl
    _ = (↑u⁻¹ : A) * (b.repr m i) := by rw [hcoord]
    _ = (↑u⁻¹ : A) * u := by rw [← hu]
    _ = 1 := by simp

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: an element of the maximal ideal outside its square has a
Kähler differential admitting a linear functional with value `1`. -/
private theorem exists_kaehlerFunctional_eq_one_of_not_mem_sq
    {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
    [Algebra.IsSeparableOver k (IsLocalRing.ResidueField A)] [Module.Free A Ω[A⁄k]]
    (x : IsLocalRing.maximalIdeal A) (hx : (x : A) ∉ IsLocalRing.maximalIdeal A ^ 2) :
    ∃ θ : Ω[A⁄k] →ₗ[A] A, θ (KaehlerDifferential.D k A (x : A)) = 1 := by
  -- Proof comment: identify the kernel of the residue map with the maximal ideal so the
  -- conormal injectivity theorem applies to the cotangent class of `x`.
  let K := IsLocalRing.ResidueField A
  have hker : RingHom.ker (algebraMap A K) = IsLocalRing.maximalIdeal A := by
    ext a
    simp [K, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  let eCot : (IsLocalRing.maximalIdeal A).Cotangent ≃ₗ[A]
      (RingHom.ker (algebraMap A K)).Cotangent :=
    Ideal.Cotangent.equivOfEq
      (IsLocalRing.maximalIdeal A) (RingHom.ker (algebraMap A K)) hker.symm
  have hxCot_ne : Ideal.toCotangent (IsLocalRing.maximalIdeal A) x ≠ 0 := by
    intro hzero
    apply hx
    exact ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero x).mp hzero
  have hImage_ne : (1 : K) ⊗ₜ[A] KaehlerDifferential.D k A (x : A) ≠ 0 := by
    have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor k A K) := by
      simpa [K] using
        residueCotangentToKaehler_injective_of_isSeparableOver (k := k) (R := A)
    intro hzero
    apply hxCot_ne
    have hmap_zero :
        KaehlerDifferential.kerCotangentToTensor k A K
            (eCot (Ideal.toCotangent (IsLocalRing.maximalIdeal A) x)) = 0 := by
      simpa [eCot, hker, K, KaehlerDifferential.kerCotangentToTensor_toCotangent] using hzero
    have hmap_zero' :
        KaehlerDifferential.kerCotangentToTensor k A K
            (eCot (Ideal.toCotangent (IsLocalRing.maximalIdeal A) x)) =
          KaehlerDifferential.kerCotangentToTensor k A K 0 := by
      simpa using hmap_zero
    have heq_zero : eCot (Ideal.toCotangent (IsLocalRing.maximalIdeal A) x) = 0 :=
      hinj hmap_zero'
    exact eCot.injective heq_zero
  -- Proof comment: the generic free-module lemma upgrades the nonzero residue tensor to a
  -- functional splitting the differential of `x`.
  exact exists_linearMap_eq_one_of_residue_tensor_ne_zero
    (A := A) (M := Ω[A⁄k]) (KaehlerDifferential.D k A (x : A)) hImage_ne

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: over a Noetherian local `ℚ`-algebra with separable residue
field, any cotangent direction outside `𝔪²` is a regular element when Kähler differentials are
free. -/
private theorem isRegular_of_not_mem_sq_of_free_kaehlerDifferential
    {A : Type v} [CommRing A] [Algebra k A] [Algebra ℚ A] [IsLocalRing A]
    [IsNoetherianRing A] [Nontrivial A]
    [Algebra.IsSeparableOver k (IsLocalRing.ResidueField A)] [Module.Free A Ω[A⁄k]]
    (x : IsLocalRing.maximalIdeal A) (hx : (x : A) ∉ IsLocalRing.maximalIdeal A ^ 2) :
    IsRegular (x : A) := by
  -- Proof comment: Lemma 10.140.6 turns the split differential into regularity of `x`.
  have hdf := exists_kaehlerFunctional_eq_one_of_not_mem_sq (k := k) (A := A) x hx
  exact isRegular_of_kaehlerDifferential_directSummand (R := k) (S := A) (f := (x : A)) hdf

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: quotienting a finite free module by a split unimodular
vector preserves finite freeness over a local ring. -/
private theorem finiteFree_quotient_span_singleton_of_split
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] {m : M}
    (hm : ∃ θ : M →ₗ[R] R, θ m = 1) :
    Module.Finite R (M ⧸ Submodule.span R ({m} : Set M)) ∧
      Module.Free R (M ⧸ Submodule.span R ({m} : Set M)) := by
  classical
  let N : Submodule R M := Submodule.span R ({m} : Set M)
  rcases hm with ⟨θ, hθ⟩
  let q : M →ₗ[R] M ⧸ N := Submodule.mkQ N
  let p : M →ₗ[R] M := LinearMap.id - ((LinearMap.toSpanSingleton R M m).comp θ)
  have hp_vanish : ∀ x ∈ N, p x = 0 := by
    -- Proof comment: `p` vanishes on the chosen split line, hence descends to the quotient.
    intro x hx
    change p x = 0
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨r, rfl⟩
    simp [p, hθ]
  let s : M ⧸ N →ₗ[R] M := N.liftQ p hp_vanish
  -- Proof comment: modulo the split line, `p` is congruent to the identity.
  have hqs : q ∘ₗ s = LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, hz⟩ := Submodule.mkQ_surjective N z
    rw [← hz]
    simp only [Submodule.mkQ_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    exact (Submodule.Quotient.eq N).mpr (by
      have hmN : m ∈ N := Submodule.subset_span (by simp)
      have hsmul : θ x • m ∈ N := Submodule.smul_mem N (θ x) hmN
      have hneg : -(θ x • m) ∈ N := Submodule.neg_mem N hsmul
      simpa [s, p, Submodule.liftQ_apply, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using hneg)
  -- Proof comment: the split quotient is projective, hence flat, and finite flat modules over
  -- local rings are free.
  have hproj : Module.Projective R (M ⧸ N) :=
    Module.Projective.of_split s q hqs
  have hflat : Module.Flat R (M ⧸ N) := by
    letI : Module.Projective R (M ⧸ N) := hproj
    infer_instance
  have hfinite : Module.Finite R (M ⧸ N) :=
    Module.Finite.quotient R N
  have hfree : Module.Free R (M ⧸ N) := by
    letI : Module.Finite R (M ⧸ N) := hfinite
    letI : Module.Flat R (M ⧸ N) := hflat
    exact Module.free_of_flat_of_isLocalRing
  exact ⟨hfinite, hfree⟩

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a surjective map from a finite free module has finite free
target when its kernel is generated by one split vector. -/
private theorem finiteFree_of_surjective_ker_eq_span_singleton_of_split
    {R M N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Free R M]
    (f : M →ₗ[R] N) {m : M} (hf : Function.Surjective f)
    (hker : LinearMap.ker f = Submodule.span R ({m} : Set M))
    (hm : ∃ θ : M →ₗ[R] R, θ m = 1) :
    Module.Finite R N ∧ Module.Free R N := by
  -- Proof comment: the target is finite because it is the image of the finite source.
  have hfinite : Module.Finite R N := Module.Finite.of_surjective f hf
  -- Proof comment: identify the target with the split quotient and transport freeness.
  have hquot := finiteFree_quotient_span_singleton_of_split (R := R) (M := M) (m := m) hm
  let e : (M ⧸ Submodule.span R ({m} : Set M)) ≃ₗ[R] N :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)
  have hfree : Module.Free R N := Module.Free.of_equiv' hquot.2 e
  exact ⟨hfinite, hfree⟩

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: positive embedding dimension supplies an element of the
maximal ideal outside its square. -/
private theorem exists_maximalIdeal_not_mem_sq_of_spanFinrank_pos
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hpos : 0 < (IsLocalRing.maximalIdeal A).spanFinrank) :
    ∃ x : IsLocalRing.maximalIdeal A, (x : A) ∉ IsLocalRing.maximalIdeal A ^ 2 := by
  -- Proof comment: rewrite the embedding dimension as the cotangent-space dimension and choose a
  -- nonzero cotangent class.
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hpos
  obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨x, rfl⟩ := (IsLocalRing.maximalIdeal A).toCotangent_surjective y
  refine ⟨x, ?_⟩
  -- Proof comment: membership in `𝔪²` is exactly vanishing of the cotangent class.
  intro hx
  apply hy
  exact ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero x).mpr hx

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: an element outside `𝔪²` has nonzero cotangent class. -/
private theorem cotangent_nonzero_of_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    (maximalIdeal A).toCotangent x ≠ 0 := by
  -- Proof comment: `Ideal.toCotangent_eq_zero` identifies vanishing in the cotangent space with
  -- membership in the square of the maximal ideal.
  intro hx0
  exact hx (((maximalIdeal A).toCotangent_eq_zero x).mp hx0)

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: an element outside `𝔪²` forces positive embedding
dimension. -/
private theorem spanFinrank_pos_of_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (x : maximalIdeal A)
    (hx : (x : A) ∉ maximalIdeal A ^ 2) :
    0 < (maximalIdeal A).spanFinrank := by
  -- Proof comment: the nonzero cotangent class gives a nonzero vector in the residue-field
  -- cotangent space, so its finrank is positive.
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨(maximalIdeal A).toCotangent x, cotangent_nonzero_of_not_mem_sq (x := x) hx⟩

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a nonzero vector in a finite-dimensional vector space can
be chosen as the head of a `Fin`-indexed basis. -/
private theorem cotangent_basis_with_prescribed_head
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {n : ℕ} (hfinrank : Module.finrank K V = n + 1) (v : V) (hv : v ≠ 0) :
    ∃ b : Module.Basis (Fin (n + 1)) K V, b 0 = v := by
  classical
  let _ : Module.Finite K V := Module.finite_of_finrank_eq_succ hfinrank
  let s : Set V := {v}
  have hs : LinearIndepOn K _root_.id s := by
    -- Proof comment: a singleton is linearly independent exactly when its vector is nonzero.
    simpa [s] using
      (linearIndepOn_singleton_iff (R := K) (v := _root_.id) (i := v)).2 hv
  let b : Module.Basis (hs.extend (Set.subset_univ s)) K V := Module.Basis.extend hs
  let i0 : hs.extend (Set.subset_univ s) :=
    ⟨v, hs.subset_extend (Set.subset_univ s) (by simp [s])⟩
  letI : Finite (hs.extend (Set.subset_univ s)) := Module.Finite.finite_basis b
  letI : Fintype (hs.extend (Set.subset_univ s)) :=
    Fintype.ofFinite (hs.extend (Set.subset_univ s))
  have hcard : Fintype.card (hs.extend (Set.subset_univ s)) = n + 1 := by
    -- Proof comment: the extended basis has cardinality equal to the ambient finrank.
    rw [← Module.finrank_eq_card_basis b, hfinrank]
  let e0 : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
  let eidx : hs.extend (Set.subset_univ s) ≃ Fin (n + 1) :=
    e0.trans (Equiv.swap (e0 i0) 0)
  let c : Module.Basis (Fin (n + 1)) K V := b.reindex eidx
  have heidx_zero : eidx i0 = 0 := by
    -- Proof comment: swap the distinguished vector into the head index.
    simp [eidx]
  have heidx_symm_zero : eidx.symm 0 = i0 :=
    eidx.symm_apply_eq.mpr heidx_zero.symm
  have hc_zero : c 0 = v := by
    -- Proof comment: after reindexing, evaluating the basis at `0` returns the prescribed
    -- vector.
    calc
      c 0 = b (eidx.symm 0) := by simp [c]
      _ = b i0 := by rw [heidx_symm_zero]
      _ = v := by
        simpa [b, i0] using Module.Basis.extend_apply_self hs i0
  exact ⟨c, hc_zero⟩

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: reindexing a finite parameter family along a `Fin.cast`
does not change the generated ideal. -/
private theorem parameterIdeal_comp_cast
    {A : Type*} [CommRing A] [IsLocalRing A] {d e : ℕ}
    (h : d = e) (x : Fin d → maximalIdeal A) :
    parameterIdeal (x ∘ Fin.cast h.symm) = parameterIdeal x := by
  -- Proof comment: `Fin.cast` is a bijective reindexing, so the range of generators is unchanged.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
  congr 1
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast h.symm i, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast h i, ?_⟩
    simp

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: the one-head family written with `Fin.append` generates
the same parameter ideal as the equivalent `Fin.cons` family. -/
private theorem parameterIdeal_append_eq_cons
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ}
    (x : maximalIdeal A) (z : Fin n → maximalIdeal A) :
    parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) z) = parameterIdeal (Fin.cons x z) := by
  -- Proof comment: `Fin.append` and `Fin.cons` enumerate the same head-plus-tail generators.
  rw [Fin.append_left_eq_cons]
  simpa using
    (parameterIdeal_comp_cast (A := A) (h := (Nat.add_comm 1 n).symm)
      (x := Fin.cons x z))

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: the ideal generated by the head of a parameter family. -/
private def headParameterIdeal {A : Type*} [CommRing A] [IsLocalRing A] {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal A) : Ideal A :=
  Ideal.span ({((x 0 : maximalIdeal A) : A)} : Set A)

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: in the head quotient, every tail parameter maps to the
quotient maximal ideal. -/
private theorem tail_image_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal A)
    [IsLocalRing (A ⧸ headParameterIdeal x)] (i : Fin d) :
    Ideal.Quotient.mk (headParameterIdeal x) (((x i.succ : maximalIdeal A) : A)) ∈
      maximalIdeal (A ⧸ headParameterIdeal x) := by
  let I : Ideal A := headParameterIdeal x
  let S := A ⧸ I
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmem :
      Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) := by
    -- Proof comment: the tail parameter already lies in the upstairs maximal ideal.
    refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
      (hf := Ideal.Quotient.mk_surjective) (I := maximalIdeal A)
      (y := Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)))).2 ?_
    exact ⟨((x i.succ : maximalIdeal A) : A), (x i.succ).2, rfl⟩
  simpa [I, S, hmap] using hmem

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: the full parameter ideal maps to the ideal generated by
the tail images after quotienting by the head. -/
private theorem map_parameterIdeal_eq_tail_parameterIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    {d : ℕ} (x : Fin (d + 1) → maximalIdeal A)
    [IsLocalRing (A ⧸ headParameterIdeal x)] :
    let xbar : Fin d → maximalIdeal (A ⧸ headParameterIdeal x) := fun i ↦
      ⟨Ideal.Quotient.mk (headParameterIdeal x) (((x i.succ : maximalIdeal A) : A)),
        tail_image_mem_maximalIdeal x i⟩
    Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (parameterIdeal x) = parameterIdeal xbar := by
  let I : Ideal A := headParameterIdeal x
  let S := A ⧸ I
  let xbar : Fin d → maximalIdeal S := fun i ↦
    ⟨Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)), tail_image_mem_maximalIdeal x i⟩
  -- Proof comment: map the span of all generators, observe that the head generator dies, and
  -- identify the remaining generators with the tail family.
  suffices
      hspan :
        Ideal.map (Ideal.Quotient.mk I)
            (Ideal.span (Set.range fun i ↦ ((x i : maximalIdeal A) : A))) =
          Ideal.span (Set.range fun i ↦ ((xbar i : maximalIdeal S) : S)) by
    simpa [parameterIdeal_eq_span, xbar] using hspan
  rw [Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ ?_ i
    · have hx0 : Ideal.Quotient.mk I (((x 0 : maximalIdeal A) : A)) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        dsimp [I, headParameterIdeal]
        exact Ideal.subset_span (by simp)
      simpa [hx0]
    · intro j
      exact Ideal.subset_span ⟨j, rfl⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨((x i.succ : maximalIdeal A) : A), ⟨i.succ, rfl⟩, rfl⟩

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a cotangent-space basis with prescribed head lifts to
generators of the maximal ideal. -/
private theorem cotangent_lifts_generate_maximalIdeal_of_basis_with_head
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
    -- Proof comment: the chosen lifts realize every vector of the cotangent basis.
    rw [himage]
    simpa using b.span_eq
  have hspan_top :
      Submodule.span A (Set.range w) = ⊤ := by
    -- Proof comment: spanning cotangent classes is equivalent to generating the maximal ideal in
    -- a Noetherian local ring.
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
    -- Proof comment: `parameterIdeal` is the ideal spanned by the chosen family.
    simpa [parameterIdeal_eq_span, w] using hspan_val
  calc
    parameterIdeal (Fin.append (fun _ : Fin 1 ↦ x) z) = parameterIdeal (Fin.cons x z) := by
      simpa using parameterIdeal_append_eq_cons (A := A) x z
    _ = maximalIdeal A := hparameter_cons

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: quotienting a Noetherian local ring by an element outside
`𝔪²` strictly lowers the embedding dimension. -/
private theorem spanFinrank_quotient_span_singleton_lt_of_not_mem_sq
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
    -- Proof comment: positivity writes the ambient embedding dimension as the successor of the
    -- tail length.
    dsimp [d]
    omega
  have hfinrank :
      Module.finrank (ResidueField A) (CotangentSpace A) = d + 1 := by
    -- Proof comment: the embedding dimension is the residue-field dimension of the cotangent
    -- space.
    calc
      Module.finrank (ResidueField A) (CotangentSpace A) = (maximalIdeal A).spanFinrank := by
        rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := A)]
      _ = d + 1 := hspan
  obtain ⟨b, hb0⟩ :=
    cotangent_basis_with_prescribed_head
      (K := ResidueField A)
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
        -- Proof comment: the prescribed-head cotangent basis lifts to generators of the maximal
        -- ideal upstairs.
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
    -- Proof comment: the quotient map kills the head parameter and maps the upstairs generating
    -- ideal to the tail-generated maximal ideal downstairs.
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
    -- Proof comment: a range indexed by `Fin d` has at most `d` elements.
    rw [← Nat.card_coe_set_eq]
    simpa using
      (Finite.card_range_le
        (fun i : Fin d ↦ ((xbar i : maximalIdeal (A ⧸ headParameterIdeal w)) :
          A ⧸ headParameterIdeal w)))
  have hspanQ :
      (maximalIdeal (A ⧸ headParameterIdeal w)).spanFinrank ≤ d := by
    -- Proof comment: the quotient maximal ideal is generated by the `d` tail images.
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
  -- Proof comment: the quotient needs at most `d` generators, while the ambient maximal ideal
  -- has embedding dimension `d + 1`.
  calc
    (maximalIdeal (A ⧸ Ideal.span ({(x : A)} : Set A))).spanFinrank =
        (maximalIdeal (A ⧸ headParameterIdeal w)).spanFinrank := by
          rfl
    _ ≤ d := hspanQ
    _ < d + 1 := Nat.lt_succ_self d
    _ = (maximalIdeal A).spanFinrank := hspan.symm

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: quotienting by an element of the maximal ideal gives a
nontrivial quotient ring. -/
private theorem nontrivial_quotient_span_singleton_of_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] (x : IsLocalRing.maximalIdeal A) :
    Nontrivial (A ⧸ Ideal.span ({(x : A)} : Set A)) := by
  -- Proof comment: if the principal ideal were the whole ring, `x` would be a unit, contradicting
  -- membership in the maximal ideal.
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have hxunit : IsUnit (x : A) := Ideal.span_singleton_eq_top.mp htop
  exact ((IsLocalRing.notMem_maximalIdeal).2 hxunit) x.2

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: quotienting a local ring by an element of the maximal ideal
is again local. -/
private theorem isLocalRing_quotient_span_singleton_of_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] (x : IsLocalRing.maximalIdeal A) :
    IsLocalRing (A ⧸ Ideal.span ({(x : A)} : Set A)) := by
  -- Proof comment: the quotient is nontrivial by the previous helper, so locality descends along
  -- the surjective quotient map.
  letI : Nontrivial (A ⧸ Ideal.span ({(x : A)} : Set A)) :=
    nontrivial_quotient_span_singleton_of_mem_maximalIdeal (A := A) x
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: the kernel of the canonical quotient by a principal ideal
is that principal ideal. -/
private theorem quotient_span_singleton_ker
    {A : Type*} [CommRing A] (x : A) :
    RingHom.ker (algebraMap A (A ⧸ Ideal.span ({x} : Set A))) =
      Ideal.span ({x} : Set A) := by
  -- Proof comment: membership in the quotient kernel is exactly vanishing modulo the ideal.
  ext a
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: the cotangent module of a principal ideal is generated by
the class of a chosen principal generator. -/
private theorem cotangent_span_top_of_eq_span_singleton
    {A : Type*} [CommRing A] {I : Ideal A} {x : A}
    (hI : I = Ideal.span ({x} : Set A)) (hx : x ∈ I) :
    Submodule.span A ({Ideal.toCotangent I ⟨x, hx⟩} : Set I.Cotangent) = ⊤ := by
  -- Proof comment: lift an arbitrary cotangent class to the ideal, write that lift as a
  -- multiple of the principal generator, and descend the equality to cotangent classes.
  apply Submodule.eq_top_iff'.mpr
  intro z
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective z
  have hy_span : (y : A) ∈ Ideal.span ({x} : Set A) := by
    simpa [← hI] using y.2
  rw [Ideal.mem_span_singleton] at hy_span
  rcases hy_span with ⟨a, ha⟩
  have hy_eq : y = a • (⟨x, hx⟩ : I) := by
    ext
    simpa [smul_eq_mul, mul_comm] using ha
  rw [hy_eq]
  exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a principal algebra-map kernel has conormal module
generated by the principal generator. -/
private theorem conormalCotangent_span_top_of_ker_eq_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {x : A}
    (hker : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A))
    (hx : x ∈ RingHom.ker (algebraMap A B)) :
    Submodule.span A
        ({Ideal.toCotangent (RingHom.ker (algebraMap A B)) ⟨x, hx⟩} :
          Set (RingHom.ker (algebraMap A B)).Cotangent) =
      ⊤ := by
  -- Proof comment: specialize the principal-ideal cotangent generator statement to the kernel.
  exact cotangent_span_top_of_eq_span_singleton
    (I := RingHom.ker (algebraMap A B)) hker hx

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: if the algebra-map kernel is principal, then the conormal
map has source-ring range generated by the tensor of the generator's differential. -/
private theorem range_kerCotangentToTensor_of_ker_eq_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
    {x : A} (hker : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A))
    (hx : x ∈ RingHom.ker (algebraMap A B)) :
    LinearMap.range (KaehlerDifferential.kerCotangentToTensor k A B) =
      Submodule.span A
        ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x} :
          Set (B ⊗[A] Ω[A⁄k])) := by
  -- Proof comment: the range is the image of the whole conormal module, and the previous helper
  -- replaces that whole module by the span of the principal conormal class.
  let gen : (RingHom.ker (algebraMap A B)).Cotangent :=
    Ideal.toCotangent (RingHom.ker (algebraMap A B)) ⟨x, hx⟩
  have htop :
      Submodule.span A ({gen} : Set (RingHom.ker (algebraMap A B)).Cotangent) = ⊤ := by
    simpa [gen] using
      conormalCotangent_span_top_of_ker_eq_span_singleton
        (A := A) (B := B) hker hx
  calc
    LinearMap.range (KaehlerDifferential.kerCotangentToTensor k A B) =
        Submodule.map (KaehlerDifferential.kerCotangentToTensor k A B) ⊤ := by
      rw [LinearMap.range_eq_map]
    _ = Submodule.map (KaehlerDifferential.kerCotangentToTensor k A B)
        (Submodule.span A ({gen} :
          Set (RingHom.ker (algebraMap A B)).Cotangent)) := by
      rw [htop]
    _ = Submodule.span A
        ((KaehlerDifferential.kerCotangentToTensor k A B) ''
          ({gen} : Set (RingHom.ker (algebraMap A B)).Cotangent)) := by
      rw [Submodule.map_span]
    _ = Submodule.span A
        ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x} :
          Set (B ⊗[A] Ω[A⁄k])) := by
      congr
      ext z
      simp [gen, KaehlerDifferential.kerCotangentToTensor_toCotangent]

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: exactness turns a principal conormal range into the
source-ring kernel of Kähler base change. -/
private theorem ker_mapBaseChange_restrictScalars_of_surjective_ker_eq_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] {x : A}
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A))
    (hx : x ∈ RingHom.ker (algebraMap A B)) :
    (LinearMap.ker (KaehlerDifferential.mapBaseChange k A B)).restrictScalars A =
      Submodule.span A
        ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x} :
          Set (B ⊗[A] Ω[A⁄k])) := by
  -- Proof comment: mathlib's conormal exactness identifies the restricted kernel with the
  -- conormal range, and the preceding range lemma computes that range for a principal kernel.
  calc
    (LinearMap.ker (KaehlerDifferential.mapBaseChange k A B)).restrictScalars A =
        LinearMap.range (KaehlerDifferential.kerCotangentToTensor k A B) := by
      exact (KaehlerDifferential.range_kerCotangentToTensor k A B hsurj).symm
    _ = Submodule.span A
        ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x} :
          Set (B ⊗[A] Ω[A⁄k])) := by
      exact range_kerCotangentToTensor_of_ker_eq_span_singleton
        (k := k) (A := A) (B := B) hker hx

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: exactness computes the actual target-ring kernel of
Kähler base change for a surjective algebra map with principal kernel. -/
private theorem ker_mapBaseChange_of_surjective_ker_eq_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] {x : A}
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span ({x} : Set A))
    (hx : x ∈ RingHom.ker (algebraMap A B)) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange k A B) =
      Submodule.span B
        ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x} :
          Set (B ⊗[A] Ω[A⁄k])) := by
  -- Proof comment: first use the already proved restricted-kernel normal form, then enlarge the
  -- singleton span from `A`-scalars to `B`-scalars.
  let gen : B ⊗[A] Ω[A⁄k] := (1 : B) ⊗ₜ[A] KaehlerDifferential.D k A x
  have hkerA :
      (LinearMap.ker (KaehlerDifferential.mapBaseChange k A B)).restrictScalars A =
        Submodule.span A ({gen} : Set (B ⊗[A] Ω[A⁄k])) := by
    simpa [gen] using
      ker_mapBaseChange_restrictScalars_of_surjective_ker_eq_span_singleton
        (k := k) (A := A) (B := B) hsurj hker hx
  apply le_antisymm
  · intro z hz
    have hzA :
        z ∈ (LinearMap.ker (KaehlerDifferential.mapBaseChange k A B)).restrictScalars A := hz
    rw [hkerA] at hzA
    rw [Submodule.mem_span_singleton] at hzA
    rcases hzA with ⟨a, ha⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨algebraMap A B a, ?_⟩
    calc
      (algebraMap A B a) • gen = a • gen := algebraMap_smul B a gen
      _ = z := ha
  · refine Submodule.span_le.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hgenA :
        gen ∈ (LinearMap.ker (KaehlerDifferential.mapBaseChange k A B)).restrictScalars A := by
      rw [hkerA]
      exact Submodule.subset_span (Set.mem_singleton _)
    exact hgenA

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: quotienting by a principal element whose differential is
split preserves finite freeness of Kähler differentials. -/
private theorem quotient_kaehlerDifferential_finite_free_of_split_differential
    {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]
    (x : IsLocalRing.maximalIdeal A)
    (hOmega : Module.Finite A Ω[A⁄k] ∧ Module.Free A Ω[A⁄k])
    (hdf : ∃ θ : Ω[A⁄k] →ₗ[A] A, θ (KaehlerDifferential.D k A (x : A)) = 1) :
    Module.Finite (A ⧸ Ideal.span ({(x : A)} : Set A))
        Ω[A ⧸ Ideal.span ({(x : A)} : Set A)⁄k] ∧
      Module.Free (A ⧸ Ideal.span ({(x : A)} : Set A))
        Ω[A ⧸ Ideal.span ({(x : A)} : Set A)⁄k] := by
  -- Proof comment: use the conormal kernel computation for the quotient map, then apply the
  -- generic finite-free transfer for a surjection with split singleton kernel.
  let I : Ideal A := Ideal.span ({(x : A)} : Set A)
  let B : Type v := A ⧸ I
  letI : CommRing B := inferInstance
  letI : Algebra A B := inferInstance
  letI : Algebra k B := inferInstance
  letI : IsScalarTower k A B := inferInstance
  letI : Nontrivial B :=
    nontrivial_quotient_span_singleton_of_mem_maximalIdeal (A := A) x
  letI : IsLocalRing B :=
    isLocalRing_quotient_span_singleton_of_mem_maximalIdeal (A := A) x
  letI : Module.Finite A Ω[A⁄k] := hOmega.1
  letI : Module.Free A Ω[A⁄k] := hOmega.2
  letI : Module.Finite B (B ⊗[A] Ω[A⁄k]) :=
    Module.Finite.base_change A B Ω[A⁄k]
  letI : Module.Free B (B ⊗[A] Ω[A⁄k]) :=
    Algebra.TensorProduct.instFree A B Ω[A⁄k]
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa [B, I] using (Ideal.Quotient.mk_surjective (I := I))
  have hker : RingHom.ker (algebraMap A B) = Ideal.span ({(x : A)} : Set A) := by
    simpa [B, I] using quotient_span_singleton_ker (A := A) (x := (x : A))
  have hxker : (x : A) ∈ RingHom.ker (algebraMap A B) := by
    rw [hker]
    exact Ideal.subset_span (by simp)
  have hkerMap :
      LinearMap.ker (KaehlerDifferential.mapBaseChange k A B) =
        Submodule.span B
          ({(1 : B) ⊗ₜ[A] KaehlerDifferential.D k A (x : A)} :
            Set (B ⊗[A] Ω[A⁄k])) :=
    ker_mapBaseChange_of_surjective_ker_eq_span_singleton
      (k := k) (A := A) (B := B) hsurj hker hxker
  rcases hdf with ⟨θ, hθ⟩
  have hsplit :
      ∃ Θ : B ⊗[A] Ω[A⁄k] →ₗ[B] B,
        Θ ((1 : B) ⊗ₜ[A] KaehlerDifferential.D k A (x : A)) = 1 := by
    let Θ : B ⊗[A] Ω[A⁄k] →ₗ[B] B :=
      LinearMap.liftBaseChange B ((Algebra.linearMap A B).comp θ)
    refine ⟨Θ, ?_⟩
    rw [LinearMap.liftBaseChange_tmul]
    simp [hθ]
  have hsurjMap : Function.Surjective (KaehlerDifferential.mapBaseChange k A B) :=
    KaehlerDifferential.mapBaseChange_surjective k A B hsurj
  simpa [B, I] using
    finiteFree_of_surjective_ker_eq_span_singleton_of_split
      (R := B) (M := B ⊗[A] Ω[A⁄k])
      (N := Ω[B⁄k]) (f := KaehlerDifferential.mapBaseChange k A B)
      (m := (1 : B) ⊗ₜ[A] KaehlerDifferential.D k A (x : A))
      hsurjMap hkerMap hsplit

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: a Noetherian local ring with zero embedding dimension is
regular local. -/
private theorem isRegularLocalRing_of_spanFinrank_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Nontrivial A]
    (h : (IsLocalRing.maximalIdeal A).spanFinrank = 0) :
    IsRegularLocalRing A := by
  -- Proof comment: the regular-local criterion only needs the maximal-ideal span finrank to be
  -- bounded above by the Krull dimension; zero embedding dimension gives that immediately.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := A) ?_
  rw [h]
  exact ringKrullDim_nonneg_of_nontrivial

omit [CharZero k] in
/-- Helper for Chap10 Lemma 10 140 7: regularity lifts across quotienting by one regular element
in the maximal ideal. -/
private theorem isRegularLocalRing_of_quotient_span_singleton_of_isRegular
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Nontrivial A]
    (x : IsLocalRing.maximalIdeal A) (hxreg : IsRegular (x : A))
    (hquot : IsRegularLocalRing (A ⧸ Ideal.span ({(x : A)} : Set A))) :
    IsRegularLocalRing A := by
  -- Proof comment: convert element regularity into the singleton regular sequence required by
  -- the already proved quotient-lifting theorem.
  have hxsmul : IsSMulRegular A (x : A) := by
    rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at hxreg
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro y hy
    exact hxreg y hy
  have hweak : RingTheory.Sequence.IsWeaklyRegular (M := A) [(x : A)] :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff (M := A) (x : A)).2 hxsmul
  have hmem : ∀ r ∈ [(x : A)], r ∈ IsLocalRing.maximalIdeal A := by
    intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact x.2
  have hreg : RingTheory.Sequence.IsRegular (M := A) [(x : A)] :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A hmem hweak
  have hquotList : IsRegularLocalRing (A ⧸ Ideal.ofList [(x : A)]) := by
    rw [Ideal.ofList_singleton]
    exact hquot
  exact isRegularLocalRing_of_quotient_of_isRegular
    (R := A) (rs := [(x : A)]) hreg hquotList

/-- Helper for Chap10 Lemma 10 140 7: the characteristic-zero local Jacobian criterion with an
explicit bound on the embedding dimension. -/
private theorem isRegularLocalRing_of_finite_free_kaehlerDifferential_local_charZero_of_spanFinrank_le
    (n : ℕ) :
    ∀ {A : Type v} [CommRing A] [Algebra k A] [Algebra ℚ A] [IsLocalRing A]
      [IsNoetherianRing A] [Nontrivial A] [Algebra.EssFiniteType k A]
      [Algebra.IsSeparableOver k (IsLocalRing.ResidueField A)],
      (IsLocalRing.maximalIdeal A).spanFinrank ≤ n →
      (Module.Finite A Ω[A⁄k] ∧ Module.Free A Ω[A⁄k]) → IsRegularLocalRing A := by
  -- Proof comment: induct on embedding dimension. A nonzero cotangent direction gives a regular
  -- element whose principal quotient has finite free differentials and smaller embedding dimension.
  induction n with
  | zero =>
      intro A _ _ _ _ _ _ _ _ hspan _hOmega
      exact isRegularLocalRing_of_spanFinrank_eq_zero
        (A := A) (Nat.eq_zero_of_le_zero hspan)
  | succ n ih =>
      intro A _ _ _ _ _ _ _ _ hspan hOmega
      by_cases hzero : (IsLocalRing.maximalIdeal A).spanFinrank = 0
      · exact isRegularLocalRing_of_spanFinrank_eq_zero (A := A) hzero
      · have hpos : 0 < (IsLocalRing.maximalIdeal A).spanFinrank :=
          Nat.pos_of_ne_zero hzero
        obtain ⟨x, hx⟩ :=
          exists_maximalIdeal_not_mem_sq_of_spanFinrank_pos (A := A) hpos
        letI : Module.Free A Ω[A⁄k] := hOmega.2
        have hdf :
            ∃ θ : Ω[A⁄k] →ₗ[A] A, θ (KaehlerDifferential.D k A (x : A)) = 1 :=
          exists_kaehlerFunctional_eq_one_of_not_mem_sq (k := k) (A := A) x hx
        have hxreg : IsRegular (x : A) :=
          isRegular_of_not_mem_sq_of_free_kaehlerDifferential (k := k) (A := A) x hx
        let B : Type v := A ⧸ Ideal.span ({(x : A)} : Set A)
        letI : CommRing B := inferInstance
        letI : Algebra A B := inferInstance
        letI : Algebra k B := inferInstance
        letI : Algebra ℚ B := inferInstance
        letI : IsScalarTower k A B := inferInstance
        letI : Nontrivial B :=
          nontrivial_quotient_span_singleton_of_mem_maximalIdeal (A := A) x
        letI : IsLocalRing B :=
          isLocalRing_quotient_span_singleton_of_mem_maximalIdeal (A := A) x
        letI : IsNoetherianRing B := inferInstance
        letI : Algebra.EssFiniteType k B := inferInstance
        letI : PerfectField k := PerfectField.ofCharZero
        letI : Algebra.IsSeparableOver k (IsLocalRing.ResidueField B) := inferInstance
        have hOmegaB : Module.Finite B Ω[B⁄k] ∧ Module.Free B Ω[B⁄k] := by
          simpa [B] using
            quotient_kaehlerDifferential_finite_free_of_split_differential
              (k := k) (A := A) x hOmega hdf
        have hdrop :
            (IsLocalRing.maximalIdeal B).spanFinrank <
              (IsLocalRing.maximalIdeal A).spanFinrank := by
          -- Proof comment: apply the local strict-drop helper to the quotient by the chosen
          -- cotangent-nonzero element.
          simpa [B] using
            spanFinrank_quotient_span_singleton_lt_of_not_mem_sq (A := A) x hx
        have hspanB : (IsLocalRing.maximalIdeal B).spanFinrank ≤ n := by
          omega
        have hquot : IsRegularLocalRing B :=
          ih (A := B) hspanB hOmegaB
        -- Proof comment: lift regularity from the principal quotient back to the original local
        -- ring using the singleton regular sequence generated by the chosen cotangent direction.
        exact isRegularLocalRing_of_quotient_span_singleton_of_isRegular
          (A := A) x hxreg (by simpa [B] using hquot)

/-- Helper for Chap10 Lemma 10 140 7: finite free Kähler differentials over a characteristic-zero
local algebra force the local ring to be regular. -/
private theorem isRegularLocalRing_of_finite_free_kaehlerDifferential_local_charZero
    {A : Type v} [CommRing A] [Algebra k A] [Algebra ℚ A] [IsLocalRing A]
    [IsNoetherianRing A] [Nontrivial A] [Algebra.EssFiniteType k A]
    [Algebra.IsSeparableOver k (IsLocalRing.ResidueField A)]
    (hOmega : Module.Finite A Ω[A⁄k] ∧ Module.Free A Ω[A⁄k]) :
    IsRegularLocalRing A := by
  -- Proof comment: specialize the bounded criterion to the actual embedding dimension.
  exact isRegularLocalRing_of_finite_free_kaehlerDifferential_local_charZero_of_spanFinrank_le
    (k := k) (n := (IsLocalRing.maximalIdeal A).spanFinrank) (A := A) le_rfl hOmega

/-- Helper for Chap10 Lemma 10 140 7: the direct characteristic-zero Jacobian criterion should
turn finite free local Kähler differentials into regularity of the localized local ring. -/
private theorem isRegularLocalRing_atPrime_of_finite_free_kaehlerDifferential_charZero
    (q : Ideal S) [q.IsPrime]
    (hOmega :
      Module.Finite (Localization.AtPrime q) Ω[Localization.AtPrime q⁄k] ∧
        Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄k]) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  -- Route correction: the previous proof tried to manufacture formal smoothness via
  -- `Subsingleton (H1Cotangent k S_q)`. The direct route now uses split differentials for
  -- elements outside `𝔪²`; the remaining missing step is the quotient finite-free induction that
  -- assembles those regular elements into regularity of the whole local ring.
  letI : Algebra.EssFiniteType S (Localization.AtPrime q) := .of_isLocalization _ q.primeCompl
  letI : Algebra.EssFiniteType k (Localization.AtPrime q) := .comp _ S _
  letI : IsNoetherianRing (Localization.AtPrime q) :=
    Algebra.EssFiniteType.isNoetherianRing k (Localization.AtPrime q)
  letI : Algebra ℚ (Localization.AtPrime q) :=
    RingHom.toAlgebra ((algebraMap k (Localization.AtPrime q)).comp (algebraMap ℚ k))
  letI : PerfectField k := PerfectField.ofCharZero
  letI : Algebra.IsSeparableOver k (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    inferInstance
  -- Proof comment: apply the abstract local induction to the prime localization.
  exact isRegularLocalRing_of_finite_free_kaehlerDifferential_local_charZero
    (k := k) (A := Localization.AtPrime q) hOmega

-- Proof sketch: under characteristic `0`, the residue-field extension `q.ResidueField / k` is
-- separable by the chapter's perfect-field owner, so Lemma `10.140.5` identifies smoothness at
-- `q` with regularity of `S_q`. If `S_q` is smooth over `k`, then `S_q` is formally smooth and
-- essentially of finite type, so `Ω_q` is finite and projective; since `S_q` is local, this makes
-- `Ω_q` free. The converse from finite freeness of `Ω_q` to regularity is the genuinely new local
-- argument of the present lemma.
/-- Chap10 Lemma 10 140 7: let `k` be a field of characteristic `0`, let `S` be a finite type
`k`-algebra, and let `q` be a prime ideal of `S`. The following are equivalent: `(1)` `S` is
smooth at `q` over `k`, i.e. `IsSmoothAt k q`; `(2)` the localized module of Kähler differentials
`Ω[Localization.AtPrime q⁄k]` is finite free over `Localization.AtPrime q`; and `(3)` the local
ring `Localization.AtPrime q` is regular. -/
@[stacks 00TX]
theorem isSmoothAt_tfae_finite_free_kaehlerDifferential_isRegularLocalRing_of_charZero :
    List.TFAE
      [ IsSmoothAt k q
      , Module.Finite S_q Ω_q ∧ Module.Free S_q Ω_q
      , IsRegularLocalRing S_q
      ] := by
  tfae_have 1 ↔ 3 := by
    letI : PerfectField k := PerfectField.ofCharZero
    letI : IsSeparableOver k q.ResidueField := inferInstance
    simpa using
      (isSmoothAt_iff_isRegularLocalRing_of_separable_residueField q)
  tfae_have 1 → 2 := by
    intro hsmooth
    letI : FormallySmooth k S_q := hsmooth
    letI : Algebra.EssFiniteType S S_q := .of_isLocalization _ q.primeCompl
    letI : Algebra.EssFiniteType k S_q := .comp _ S _
    letI : Module.Flat S_q Ω_q := Module.Flat.of_projective
    exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩
  tfae_have 2 → 3 := by
    intro hOmega
    -- Proof comment: use the direct local Jacobian criterion frontier instead of routing through
    -- first cotangent homology.
    exact isRegularLocalRing_atPrime_of_finite_free_kaehlerDifferential_charZero
      (k := k) (S := S) q hOmega
  tfae_finish

end

end Algebra
