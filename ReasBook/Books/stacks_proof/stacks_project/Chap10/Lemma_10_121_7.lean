import StacksProject_2024.Chap10.Lemma_10_121_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

open Submodule

/- Domain triage:
* primary domain: lattices in a fraction-field vector space and the order of vanishing of the
  determinant of a `K`-linear automorphism;
* sampled owner API: `Submodule.IsLattice`, `Submodule.latticeDistance`, `Ring.ordFrac`, and
  `WithZero.log`;
* core/canonical owners: `Submodule.IsLattice K` for latticehood and `Ring.ordFrac R` for the
  multiplicative order of vanishing;
* source-facing bridge: `WithZero.log` is the additive recovery map singled out in
  `Definition_10_121_2`;
* layer: this numbered item is a `bridge/view` theorem comparing the source-facing additive
  lattice distance with the canonical determinant valuation;
* primitive data: the lattice `M` and automorphism `φ`;
* derived API: the raw `Ring.ordFrac` equality is only a companion bridge, while the main theorem
  should live at the additive/source-facing layer.
-/

private instance isLattice_map_restrictScalars
    {W : Type w'} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
    (φ : V ≃ₗ[K] W) (M : Submodule R V) [IsLattice K M] :
    IsLattice K (M.map ((φ.restrictScalars R) : V →ₗ[R] W)) where
  fg := by
    -- A lattice image stays finitely generated because `Submodule.map` preserves finite generation.
    exact IsLattice.fg.map ((φ.restrictScalars R) : V →ₗ[R] W)
  span_eq_top := by
    let φR : V ≃ₗ[R] W := φ.restrictScalars R
    have himage :
        (φ : V →ₗ[K] W) '' (M : Set V) =
          ((M.map ((φ.restrictScalars R) : V →ₗ[R] W) : Submodule R W) : Set W) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Submodule.mem_map_of_mem hy
      · intro hx
        refine ⟨φ.symm x, ?_, by simp⟩
        simpa [φR] using
          (Submodule.mem_map_equiv
            (p := M) (e := φR) (x := x)).mp hx
    -- Map the spanning equality for `M` across the `K`-linear automorphism.
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := φ.surjective x
    have hy : y ∈ Submodule.span K (M : Set V) := by
      rw [IsLattice.span_eq_top]
      trivial
    have hφy : φ y ∈ (Submodule.span K (M : Set V)).map (φ : V →ₗ[K] W) :=
      Submodule.mem_map_of_mem hy
    rw [Submodule.map_span, himage] at hφy
    exact hφy

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: applying the same linear equivalence to both lattices
preserves their lattice distance. -/
private theorem latticeDistance_map_equiv
    [Ring.KrullDimLE 1 R]
    {W : Type w'} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
    (e : V ≃ₗ[K] W)
    (M N : Submodule R V) [IsLattice K M] [IsLattice K N] :
    latticeDistance (M.map ((e.restrictScalars R) : V →ₗ[R] W))
        (N.map ((e.restrictScalars R) : V →ₗ[R] W)) =
      latticeDistance M N := by
  let eR : V ≃ₗ[R] W := e.restrictScalars R
  have hmap_inf :
      (M ⊓ N).map (eR : V →ₗ[R] W) =
        M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) := by
    -- An automorphism carries the intersection of two lattices to the intersection of their images.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Submodule.mem_map_of_mem hy.1, Submodule.mem_map_of_mem hy.2⟩
    · intro hx
      obtain ⟨yM, hyM, hyMx⟩ := hx.1
      obtain ⟨yN, hyN, hyNx⟩ := hx.2
      have hx_eq : eR yM = eR yN := hyMx.trans hyNx.symm
      have hy_eq : yM = yN := eR.injective hx_eq
      have hyMN : yM ∈ N := by
        simpa [hy_eq] using hyN
      exact ⟨yM, ⟨hyM, hyMN⟩, hyMx⟩
  have hlen_left :
      Module.length R
          (M.map (eR : V →ₗ[R] W) ⧸
            ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
              (M.map (eR : V →ₗ[R] W)))) =
        Module.length R (M ⧸ (M ⊓ N).submoduleOf M) := by
    let eM : M ≃ₗ[R] M.map (eR : V →ₗ[R] W) :=
      Submodule.equivMapOfInjective (eR : V →ₗ[R] W) eR.injective M
    have hden :
        ((M ⊓ N).submoduleOf M).map (eM : M →ₗ[R] M.map (eR : V →ₗ[R] W)) =
          ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
            (M.map (eR : V →ₗ[R] W))) := by
      -- The quotient denominator is transported by the same equivalence.
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        change ((eM y : M.map (eR : V →ₗ[R] W)) : W) ∈
          M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)
        have hyV : (y : V) ∈ M ⊓ N := by
          exact ⟨y.2, by simpa [Submodule.submoduleOf] using hy⟩
        rw [← hmap_inf]
        exact Submodule.mem_map_of_mem hyV
      · intro x hx
        change (x : W) ∈ M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) at hx
        rw [← hmap_inf] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
        · simpa [Submodule.submoduleOf] using hy.2
        · apply Subtype.ext
          simpa [eM] using hyx
    -- The quotient modules are linearly equivalent, hence have the same length.
    simpa [hden] using
      (Submodule.Quotient.equiv
        ((M ⊓ N).submoduleOf M)
        (((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
          (M.map (eR : V →ₗ[R] W)))) eM hden).length_eq.symm
  have hlen_right :
      Module.length R
          (N.map (eR : V →ₗ[R] W) ⧸
            ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
              (N.map (eR : V →ₗ[R] W)))) =
        Module.length R (N ⧸ (M ⊓ N).submoduleOf N) := by
    let eN : N ≃ₗ[R] N.map (eR : V →ₗ[R] W) :=
      Submodule.equivMapOfInjective (eR : V →ₗ[R] W) eR.injective N
    have hden :
        ((M ⊓ N).submoduleOf N).map (eN : N →ₗ[R] N.map (eR : V →ₗ[R] W)) =
          ((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
            (N.map (eR : V →ₗ[R] W))) := by
      -- The symmetric denominator transport gives the second quotient-length equality.
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        change ((eN y : N.map (eR : V →ₗ[R] W)) : W) ∈
          M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)
        have hyV : (y : V) ∈ M ⊓ N := by
          exact ⟨by simpa [Submodule.submoduleOf] using hy, y.2⟩
        rw [← hmap_inf]
        exact Submodule.mem_map_of_mem hyV
      · intro x hx
        change (x : W) ∈ M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W) at hx
        rw [← hmap_inf] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨y, hy.2⟩, ?_, ?_⟩
        · simpa [Submodule.submoduleOf] using hy.1
        · apply Subtype.ext
          simpa [eN] using hyx
    -- Transport the second quotient across the induced quotient equivalence.
    simpa [hden] using
      (Submodule.Quotient.equiv
        ((M ⊓ N).submoduleOf N)
        (((M.map (eR : V →ₗ[R] W) ⊓ N.map (eR : V →ₗ[R] W)).submoduleOf
          (N.map (eR : V →ₗ[R] W)))) eN hden).length_eq.symm
  -- Unfold the distance and replace both quotient lengths by the transported lengths.
  rw [Submodule.latticeDistance_def, Submodule.latticeDistance_def]
  rw [hlen_left, hlen_right]

omit [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the distance from a lattice to its image under a fixed
automorphism is independent of the chosen lattice. -/
private theorem latticeDistance_image_eq_of_lattice
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V)
    (M N : Submodule R V) [IsLattice K M] [IsLattice K N] :
    latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
      latticeDistance N (N.map ((φ.restrictScalars R) : V →ₗ[R] V)) := by
  let φR : V →ₗ[R] V := (φ.restrictScalars R : V ≃ₗ[R] V)
  have hfirst :
      latticeDistance M (M.map φR) =
        latticeDistance M N + latticeDistance N (M.map φR) := by
    -- Insert `N` as the intermediate lattice in the distance from `M` to `φ(M)`.
    exact Submodule.latticeDistance_add (M := M) (M' := N) (M'' := M.map φR)
  have hsecond :
      latticeDistance N (M.map φR) =
        latticeDistance N (N.map φR) + latticeDistance (N.map φR) (M.map φR) := by
    -- Split the remaining distance through the image lattice `φ(N)`.
    exact Submodule.latticeDistance_add (M := N) (M' := N.map φR) (M'' := M.map φR)
  have htransport :
      latticeDistance (N.map φR) (M.map φR) = latticeDistance N M := by
    -- Transporting both lattices by `φ` does not change their mutual distance.
    simpa [φR] using latticeDistance_map_equiv (R := R) (K := K) (V := V) φ N M
  have hswap : latticeDistance N M = -latticeDistance M N := by
    -- Swap the two original lattices to cancel the inserted intermediate distance.
    exact Submodule.latticeDistance_neg_swap (M := N) (M' := M)
  rw [hfirst, hsecond, htransport, hswap]
  ring

omit [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the determinant formula is stable under composition of
linear equivalences. -/
private theorem exp_latticeDistance_trans
    [Ring.KrullDimLE 1 R] (f g : V ≃ₗ[K] V)
    (hf : ∀ (N : Submodule R V) [IsLattice K N],
      WithZero.exp (latticeDistance N (N.map ((f.restrictScalars R) : V →ₗ[R] V))) =
        Ring.ordFrac R (LinearEquiv.det f : K))
    (hg : ∀ (N : Submodule R V) [IsLattice K N],
      WithZero.exp (latticeDistance N (N.map ((g.restrictScalars R) : V →ₗ[R] V))) =
        Ring.ordFrac R (LinearEquiv.det g : K))
    (M : Submodule R V) [IsLattice K M] :
    WithZero.exp (latticeDistance M (M.map (((f.trans g).restrictScalars R) : V →ₗ[R] V))) =
      Ring.ordFrac R (LinearEquiv.det (f.trans g) : K) := by
  let fR : V →ₗ[R] V := (f.restrictScalars R : V ≃ₗ[R] V)
  let gR : V →ₗ[R] V := (g.restrictScalars R : V ≃ₗ[R] V)
  have hmap_comp :
      M.map (((f.trans g).restrictScalars R) : V →ₗ[R] V) = (M.map fR).map gR := by
    -- The image under the composite equivalence is the iterated image.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨f y, ?_, ?_⟩
      · exact Submodule.mem_map_of_mem hy
      · simp [gR]
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      simp [fR, gR]
  have hadd :
      latticeDistance M ((M.map fR).map gR) =
        latticeDistance M (M.map fR) + latticeDistance (M.map fR) ((M.map fR).map gR) := by
    -- Additivity splits the distance along the intermediate lattice `f(M)`.
    exact Submodule.latticeDistance_add (M := M) (M' := M.map fR) (M'' := (M.map fR).map gR)
  calc
    WithZero.exp (latticeDistance M (M.map (((f.trans g).restrictScalars R) : V →ₗ[R] V))) =
        WithZero.exp (latticeDistance M (M.map fR) + latticeDistance (M.map fR) ((M.map fR).map gR)) := by
          rw [hmap_comp, hadd]
    _ = WithZero.exp (latticeDistance M (M.map fR)) *
          WithZero.exp (latticeDistance (M.map fR) ((M.map fR).map gR)) := by
          rw [WithZero.exp_add]
    _ = Ring.ordFrac R (LinearEquiv.det f : K) * Ring.ordFrac R (LinearEquiv.det g : K) := by
          rw [hf M]
          rw [hg (M.map fR)]
    _ = Ring.ordFrac R (LinearEquiv.det (f.trans g) : K) := by
          rw [LinearEquiv.det_trans]
          simp [map_mul, mul_comm]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 121 7: the standard coordinate lattice generated by the
coordinate basis vectors. -/
private abbrev coordinateLattice (n : ℕ) : Submodule R (Fin n → K) :=
  Submodule.span R (Set.range fun i : Fin n => Pi.single i (1 : K))

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the standard coordinate lattice is the range of the
coordinatewise algebra map from `R^n` to `K^n`. -/
private theorem coordinateLattice_eq_range_algebraMapPi (n : ℕ) :
    coordinateLattice (R := R) (K := K) n =
      LinearMap.range (LinearMap.piMap fun _ : Fin n => Algebra.linearMap R K) := by
  -- Compare both submodules pointwise using the usual finite-support coordinates.
  ext x
  constructor
  · intro hx
    rw [coordinateLattice] at hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    ext j
    rw [← hc]
    simp [LinearMap.piMap, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨c, rfl⟩
    rw [coordinateLattice]
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    ext j
    simp [LinearMap.piMap, Pi.single_apply, Algebra.smul_def]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: a coordinatewise linear map preserves the standard
coordinate lattice if it sends every standard basis vector into that lattice. -/
private theorem coordinateLattice_map_le_of_basis_mem {n : ℕ}
    (f : (Fin n → K) →ₗ[R] (Fin n → K))
    (hf : ∀ i : Fin n, f (Pi.single i (1 : K)) ∈ coordinateLattice (R := R) (K := K) n) :
    (coordinateLattice (R := R) (K := K) n).map f ≤
      coordinateLattice (R := R) (K := K) n := by
  -- It is enough to check the image of the spanning coordinate basis.
  rw [coordinateLattice]
  rw [Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, rfl⟩ := hx
  simpa [coordinateLattice] using hf i

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: a linear equivalence preserves the standard coordinate
lattice when it and its inverse send each standard basis vector into that lattice. -/
private theorem coordinateLattice_map_eq_self_of_basis_mem {n : ℕ}
    (ψ : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (hψ : ∀ i : Fin n, ψ (Pi.single i (1 : K)) ∈ coordinateLattice (R := R) (K := K) n)
    (hψsymm : ∀ i : Fin n,
      ψ.symm (Pi.single i (1 : K)) ∈ coordinateLattice (R := R) (K := K) n) :
    (coordinateLattice (R := R) (K := K) n).map
        ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)) =
      coordinateLattice (R := R) (K := K) n := by
  -- Prove both inclusions by applying the one-sided basis criterion to `ψ` and to `ψ.symm`.
  apply le_antisymm
  · exact coordinateLattice_map_le_of_basis_mem
      (R := R) (K := K) ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)) hψ
  · intro x hx
    have hsymm_mem : ψ.symm x ∈ coordinateLattice (R := R) (K := K) n := by
      have hle := coordinateLattice_map_le_of_basis_mem
        (R := R) (K := K) ((ψ.symm.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K))
        hψsymm
      exact hle (Submodule.mem_map_of_mem hx)
    refine ⟨ψ.symm x, hsymm_mem, ?_⟩
    simp

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 121 7: the standard coordinate lattice is a lattice. -/
private theorem coordinateLattice_isLattice (n : ℕ) :
    IsLattice K (coordinateLattice (R := R) (K := K) n) := by
  refine ⟨?_, ?_⟩
  · -- The coordinate lattice is generated by the finite standard basis.
    exact Submodule.fg_span (Set.finite_range fun i : Fin n => Pi.single i (1 : K))
  · -- Extending scalars from `R` to `K` recovers the usual `K`-span of the standard basis.
    rw [coordinateLattice]
    rw [Submodule.span_span_of_tower (R := R) (S := K)]
    have hrange :
        Set.range (fun i : Fin n => Pi.single i (1 : K)) =
          Set.range ⇑(Pi.basisFun K (Fin n)) := by
      congr
      funext i j
      simp [Pi.basisFun_apply]
    rw [hrange]
    exact (Pi.basisFun K (Fin n)).span_eq

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: parameterize the lattice that scales one coordinate by
the scalar `u` and leaves the other coordinate directions standard. -/
private abbrev coordinateAxisParam (n : ℕ) (i : Fin n) (u : K) :
    (Fin n → R) →ₗ[R] (Fin n → K) :=
  LinearMap.pi fun j =>
    if j = i then u • ((Algebra.linearMap R K).comp (LinearMap.proj j))
    else (Algebra.linearMap R K).comp (LinearMap.proj j)

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the axis parameterization has the expected coordinatewise
formula. -/
private theorem coordinateAxisParam_apply {n : ℕ} (i j : Fin n) (u : K) (x : Fin n → R) :
    coordinateAxisParam (R := R) (K := K) n i u x j =
      if j = i then u * algebraMap R K (x j) else algebraMap R K (x j) := by
  -- Normalize the definition coordinate by coordinate; this is the stable rewrite form used below.
  by_cases hji : j = i
  · simp [coordinateAxisParam, hji]
  · simp [coordinateAxisParam, hji]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the standard coordinate lattice is the range of the
axis parameterization with unit parameter on any selected coordinate. -/
private theorem coordinateLattice_eq_range_coordinateAxisParam_one {n : ℕ} (i : Fin n) :
    coordinateLattice (R := R) (K := K) n =
      LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (1 : K)) := by
  have hmap :
      coordinateAxisParam (R := R) (K := K) n i (1 : K) =
        LinearMap.piMap fun _ : Fin n => Algebra.linearMap R K := by
    -- At parameter `1`, the selected coordinate has the same algebra-map formula as all others.
    apply LinearMap.ext
    intro x
    ext j
    rw [coordinateAxisParam_apply]
    by_cases hji : j = i
    · simp [hji, LinearMap.piMap]
    · simp [hji, LinearMap.piMap]
  -- Replace the coordinate lattice by the algebra-map range, then identify the maps.
  rw [coordinateLattice_eq_range_algebraMapPi (R := R) (K := K) n, hmap]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 121 7: a nonzero axis parameterization is injective on
coordinate vectors over the base ring. -/
private theorem coordinateAxisParam_injective_of_ne_zero {n : ℕ} (i : Fin n) {t : K}
    (ht : t ≠ 0) :
    Function.Injective (coordinateAxisParam (R := R) (K := K) n i t) := by
  intro x y hxy
  ext j
  by_cases hji : j = i
  · -- On the selected coordinate, cancel the nonzero scalar before using fraction-field
    -- injectivity of the algebra map.
    subst j
    have hcoord := congr_fun hxy i
    rw [coordinateAxisParam_apply, coordinateAxisParam_apply] at hcoord
    simp only [if_true] at hcoord
    exact (IsFractionRing.injective R K) (mul_left_cancel₀ ht hcoord)
  · -- Off the selected coordinate, the equality is already an equality after applying
    -- `algebraMap R K`.
    have hcoord := congr_fun hxy j
    rw [coordinateAxisParam_apply, coordinateAxisParam_apply] at hcoord
    simp only [hji, if_false] at hcoord
    exact (IsFractionRing.injective R K) hcoord

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 121 7: the quotient of the standard axis range by the range
with selected coordinate multiplied by `a` has the same length as `R/(a)`. -/
private theorem coordinateAxisParam_standard_quotient_length {n : ℕ} (i : Fin n)
    (a : nonZeroDivisors R) :
    Module.length R
        (LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (1 : K)) ⧸
          (LinearMap.range
            (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R)))).submoduleOf
            (LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (1 : K)))) =
      Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R)) := by
  classical
  let p : (Fin n → R) →ₗ[R] (Fin n → K) :=
    coordinateAxisParam (R := R) (K := K) n i (1 : K)
  let q : (Fin n → R) →ₗ[R] (Fin n → K) :=
    coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R))
  let L : Submodule R (Fin n → K) := LinearMap.range p
  let N : Submodule R (Fin n → K) := LinearMap.range q
  let I : Submodule R R := Ideal.span ({(a : R)} : Set R)
  have hp_inj : Function.Injective p := by
    -- The standard parameter is nonzero, so the range equivalence can recover coordinates.
    simpa [p] using
      coordinateAxisParam_injective_of_ne_zero (R := R) (K := K) (n := n) i (t := (1 : K))
        one_ne_zero
  let e : (Fin n → R) ≃ₗ[R] L := LinearEquiv.ofInjective p hp_inj
  let selectedQuotient : L →ₗ[R] R ⧸ I :=
    (Submodule.mkQ I).comp ((LinearMap.proj i).comp (e.symm : L →ₗ[R] (Fin n → R)))
  have hker : LinearMap.ker selectedQuotient = N.submoduleOf L := by
    -- The kernel consists exactly of those range elements whose recovered selected coordinate
    -- lies in the principal ideal `(a)`.
    ext z
    constructor
    · intro hz
      change (z : Fin n → K) ∈ N
      have hzI : e.symm z i ∈ I := by
        have hz0 : (Submodule.Quotient.mk (e.symm z i) : R ⧸ I) = 0 := by
          simpa [selectedQuotient, Submodule.mkQ_apply, LinearMap.mem_ker] using hz
        exact (Submodule.Quotient.mk_eq_zero I).mp hz0
      obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton'.mp hzI)
      refine ⟨fun j => if j = i then r else e.symm z j, ?_⟩
      ext j
      have hz_eq : p (e.symm z) = z := by
        change p ((LinearEquiv.ofInjective p hp_inj).symm z) = z
        exact LinearEquiv.ofInjective_symm_apply (f := p) (h := hp_inj) z
      have hz_coord := congr_fun hz_eq j
      by_cases hji : j = i
      · subst j
        have hz_coord_i : algebraMap R K (e.symm z i) = (z : Fin n → K) i := by
          simpa [p] using hz_coord
        simp only [q, coordinateAxisParam_apply, if_true]
        calc
          algebraMap R K (a : R) * algebraMap R K r =
              algebraMap R K (e.symm z i) := by
                rw [← map_mul, mul_comm, hr]
          _ = (z : Fin n → K) i := hz_coord_i
      ·
        have hz_coord_j : algebraMap R K (e.symm z j) = (z : Fin n → K) j := by
          simpa [p, hji] using hz_coord
        simpa [q, hji] using hz_coord_j
    · intro hz
      change (z : Fin n → K) ∈ N at hz
      obtain ⟨c, hc⟩ := hz
      rw [LinearMap.mem_ker]
      have hz_eq : p (e.symm z) = z := by
        change p ((LinearEquiv.ofInjective p hp_inj).symm z) = z
        exact LinearEquiv.ofInjective_symm_apply (f := p) (h := hp_inj) z
      have hcoord : algebraMap R K (e.symm z i) = algebraMap R K ((a : R) * c i) := by
        have hleft : algebraMap R K (e.symm z i) = (z : Fin n → K) i := by
          simpa [p] using congr_fun hz_eq i
        have hright' :
            algebraMap R K (a : R) * algebraMap R K (c i) = (z : Fin n → K) i := by
          simpa [q, Algebra.smul_def] using congr_fun hc i
        rw [map_mul]
        exact hleft.trans hright'.symm
      have hmemI : e.symm z i ∈ I := by
        rw [Ideal.mem_span_singleton']
        refine ⟨c i, ?_⟩
        rw [mul_comm]
        exact (IsFractionRing.injective R K hcoord).symm
      have hz0 : (Submodule.Quotient.mk (e.symm z i) : R ⧸ I) = 0 :=
        (Submodule.Quotient.mk_eq_zero I).mpr hmemI
      simpa [selectedQuotient, Submodule.mkQ_apply] using hz0
  have hsurj : Function.Surjective selectedQuotient := by
    -- Every principal quotient class is hit by the range vector supported at the selected axis.
    intro y
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I y
    refine ⟨e (Pi.single i r), ?_⟩
    simp [selectedQuotient, Submodule.mkQ_apply]
  have hquot :
      (L ⧸ N.submoduleOf L) ≃ₗ[R] R ⧸ I :=
    (Submodule.quotEquivOfEq (N.submoduleOf L) (LinearMap.ker selectedQuotient) hker.symm).trans
      (selectedQuotient.quotKerEquivOfSurjective hsurj)
  -- Transport module length across the quotient equivalence.
  simpa [p, q, L, N, I] using hquot.length_eq

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 121 7: if a unit is represented by `a / b`, then the quotient of
the scaled axis range by the common lower range has the same length as `R/(b)`. -/
private theorem coordinateAxisParam_scaled_quotient_length_of_mk_eq {n : ℕ} (i : Fin n)
    (a b : nonZeroDivisors R) (u : Kˣ)
    (hu : (u : K) = IsLocalization.mk' K (a : R) b) :
    Module.length R
        (LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K)) ⧸
          (LinearMap.range
            (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R)))).submoduleOf
            (LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K)))) =
      Module.length R (R ⧸ Ideal.span ({(b : R)} : Set R)) := by
  classical
  let p : (Fin n → R) →ₗ[R] (Fin n → K) :=
    coordinateAxisParam (R := R) (K := K) n i (u : K)
  let q : (Fin n → R) →ₗ[R] (Fin n → K) :=
    coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R))
  let L : Submodule R (Fin n → K) := LinearMap.range p
  let N : Submodule R (Fin n → K) := LinearMap.range q
  let I : Submodule R R := Ideal.span ({(b : R)} : Set R)
  have hspec :
      (u : K) * algebraMap R K (b : R) = algebraMap R K (a : R) := by
    -- This is the only scaled-case input: the chosen unit is the fraction `a / b`.
    rw [hu]
    exact IsLocalization.mk'_spec K (a : R) b
  have hp_inj : Function.Injective p := by
    -- A unit-scaled parameterization still recovers the original coordinate vector uniquely.
    simpa [p] using
      coordinateAxisParam_injective_of_ne_zero (R := R) (K := K) (n := n) i (t := (u : K))
        (Units.ne_zero u)
  let e : (Fin n → R) ≃ₗ[R] L := LinearEquiv.ofInjective p hp_inj
  let selectedQuotient : L →ₗ[R] R ⧸ I :=
    (Submodule.mkQ I).comp ((LinearMap.proj i).comp (e.symm : L →ₗ[R] (Fin n → R)))
  have hker : LinearMap.ker selectedQuotient = N.submoduleOf L := by
    -- The kernel condition is now divisibility by `b`; `u * b = a` converts it to membership in
    -- the lower axis range.
    ext z
    constructor
    · intro hz
      change (z : Fin n → K) ∈ N
      have hzI : e.symm z i ∈ I := by
        have hz0 : (Submodule.Quotient.mk (e.symm z i) : R ⧸ I) = 0 := by
          simpa [selectedQuotient, Submodule.mkQ_apply, LinearMap.mem_ker] using hz
        exact (Submodule.Quotient.mk_eq_zero I).mp hz0
      obtain ⟨r, hr⟩ := (Ideal.mem_span_singleton'.mp hzI)
      refine ⟨fun j => if j = i then r else e.symm z j, ?_⟩
      ext j
      have hz_eq : p (e.symm z) = z := by
        change p ((LinearEquiv.ofInjective p hp_inj).symm z) = z
        exact LinearEquiv.ofInjective_symm_apply (f := p) (h := hp_inj) z
      have hz_coord := congr_fun hz_eq j
      by_cases hji : j = i
      · subst j
        have hz_coord_i : (u : K) * algebraMap R K (e.symm z i) = (z : Fin n → K) i := by
          simpa [p] using hz_coord
        simp only [q, coordinateAxisParam_apply, if_true]
        calc
          algebraMap R K (a : R) * algebraMap R K r =
              (u : K) * algebraMap R K (e.symm z i) := by
                rw [← hr, map_mul, ← hspec]
                ring
          _ = (z : Fin n → K) i := hz_coord_i
      · have hz_coord_j : algebraMap R K (e.symm z j) = (z : Fin n → K) j := by
          simpa [p, hji] using hz_coord
        simpa [q, hji] using hz_coord_j
    · intro hz
      change (z : Fin n → K) ∈ N at hz
      obtain ⟨c, hc⟩ := hz
      rw [LinearMap.mem_ker]
      have hz_eq : p (e.symm z) = z := by
        change p ((LinearEquiv.ofInjective p hp_inj).symm z) = z
        exact LinearEquiv.ofInjective_symm_apply (f := p) (h := hp_inj) z
      have hcoord :
          algebraMap R K (e.symm z i) = algebraMap R K ((b : R) * c i) := by
        have hleft :
            (u : K) * algebraMap R K (e.symm z i) = (z : Fin n → K) i := by
          simpa [p] using congr_fun hz_eq i
        have hright' :
            algebraMap R K (a : R) * algebraMap R K (c i) = (z : Fin n → K) i := by
          simpa [q, Algebra.smul_def] using congr_fun hc i
        have hmul :
            (u : K) * algebraMap R K (e.symm z i) =
              (u : K) * algebraMap R K ((b : R) * c i) := by
          calc
            (u : K) * algebraMap R K (e.symm z i) = (z : Fin n → K) i := hleft
            _ = algebraMap R K (a : R) * algebraMap R K (c i) := hright'.symm
            _ = (u : K) * algebraMap R K ((b : R) * c i) := by
                  rw [map_mul, ← mul_assoc, hspec]
        exact mul_left_cancel₀ (Units.ne_zero u) hmul
      have hmemI : e.symm z i ∈ I := by
        rw [Ideal.mem_span_singleton']
        refine ⟨c i, ?_⟩
        rw [mul_comm]
        exact (IsFractionRing.injective R K hcoord).symm
      have hz0 : (Submodule.Quotient.mk (e.symm z i) : R ⧸ I) = 0 :=
        (Submodule.Quotient.mk_eq_zero I).mpr hmemI
      simpa [selectedQuotient, Submodule.mkQ_apply] using hz0
  have hsurj : Function.Surjective selectedQuotient := by
    -- The selected coordinate of a unit-scaled range element is still the chosen representative.
    intro y
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective I y
    refine ⟨e (Pi.single i r), ?_⟩
    simp [selectedQuotient, Submodule.mkQ_apply]
  have hquot :
      (L ⧸ N.submoduleOf L) ≃ₗ[R] R ⧸ I :=
    (Submodule.quotEquivOfEq (N.submoduleOf L) (LinearMap.ker selectedQuotient) hker.symm).trans
      (selectedQuotient.quotKerEquivOfSurjective hsurj)
  -- Transport module length across the selected-coordinate quotient equivalence.
  simpa [p, q, L, N, I] using hquot.length_eq

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 121 7: on a nonzerodivisor, the multiplicative order of
vanishing is the exponential of the principal quotient length. -/
private theorem ordMonoidWithZeroHom_eq_exp_length_span_singleton
    [Ring.KrullDimLE 1 R] (a : nonZeroDivisors R) :
    Ring.ordMonoidWithZeroHom R (a : R) =
      WithZero.exp ((Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R))).toNat : ℤ) := by
  have hfin : IsFiniteLength R (R ⧸ Ideal.span ({(a : R)} : Set R)) :=
    isFiniteLength_quotient_span_singleton R a.property
  have hne : Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R)) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hfin
  -- Unfold the owner definition only once, using finite length to turn the `ℕ∞` value into
  -- the integer exponent.
  simp only [Ring.ordMonoidWithZeroHom, Ring.ord, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, SetLike.coe_mem, if_true]
  rw [← ENat.coe_toNat hne]
  rfl

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the coordinate automorphism scaling only one axis by a
unit. -/
private abbrev coordinateAxisScale {n : ℕ} (i : Fin n) (u : Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.piCongrRight fun j =>
    if j = i then LinearEquiv.smulOfUnit u else LinearEquiv.refl K K

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: axis scaling acts by multiplication by the chosen unit on
the selected coordinate and by the identity elsewhere. -/
private theorem coordinateAxisScale_apply {n : ℕ} (i j : Fin n) (u : Kˣ) (x : Fin n → K) :
    coordinateAxisScale (K := K) i u x j =
      if j = i then (u : K) * x j else x j := by
  -- Expose the product equivalence one coordinate at a time.
  rw [LinearEquiv.piCongrRight_apply]
  by_cases hji : j = i
  · subst j
    simp only [if_true]
    change (u : K) • x i = (u : K) * x i
    rw [smul_eq_mul]
  · simp [hji]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the restricted-scalar form of axis scaling has the same
coordinatewise formula. -/
private theorem coordinateAxisScale_restrictScalars_apply {n : ℕ} (i j : Fin n) (u : Kˣ)
    (x : Fin n → K) :
    (((coordinateAxisScale (K := K) i u).restrictScalars R) :
        (Fin n → K) →ₗ[R] (Fin n → K)) x j =
      if j = i then (u : K) * x j else x j := by
  -- Restricting scalars does not change the underlying coordinate function.
  simpa using coordinateAxisScale_apply (K := K) i j u x

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: scaling the standard coordinate lattice along one axis is
the range of the corresponding axis parameterization. -/
private theorem coordinateLattice_map_coordinateAxisScale_eq_range_coordinateAxisParam {n : ℕ}
    (i : Fin n) (u : Kˣ) :
    (coordinateLattice (R := R) (K := K) n).map
        (((coordinateAxisScale (K := K) i u).restrictScalars R) :
          (Fin n → K) →ₗ[R] (Fin n → K)) =
      LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K)) := by
  rw [coordinateLattice_eq_range_algebraMapPi (R := R) (K := K) n]
  -- Compare the two ranges using the same coordinate vector in `R^n`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext j
    by_cases hji : j = i
    · rw [coordinateAxisParam_apply, coordinateAxisScale_restrictScalars_apply]
      simp only [hji, if_true]
      change (u : K) * algebraMap R K (c i) = (u : K) • algebraMap R K (c i)
      rw [smul_eq_mul]
    · rw [coordinateAxisParam_apply, coordinateAxisScale_restrictScalars_apply]
      simp [hji]
  · rintro ⟨c, rfl⟩
    refine ⟨LinearMap.piMap (fun _ : Fin n => Algebra.linearMap R K) c, ?_, ?_⟩
    · exact ⟨c, rfl⟩
    · ext j
      by_cases hji : j = i
      · rw [coordinateAxisParam_apply, coordinateAxisScale_restrictScalars_apply]
        simp only [hji, if_true]
        change (u : K) • algebraMap R K (c i) = (u : K) * algebraMap R K (c i)
        rw [smul_eq_mul]
      · rw [coordinateAxisParam_apply, coordinateAxisScale_restrictScalars_apply]
        simp [hji]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 121 7: the range of a unit-scaled axis parameterization is a
lattice. -/
private theorem coordinateAxisParam_unit_isLattice {n : ℕ} (i : Fin n) (u : Kˣ) :
    IsLattice K (LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K))) := by
  -- Use the just-proved range normal form and the general fact that linear equivalences preserve
  -- latticehood.
  letI : IsLattice K (coordinateLattice (R := R) (K := K) n) :=
    coordinateLattice_isLattice (R := R) (K := K) n
  rw [← coordinateLattice_map_coordinateAxisScale_eq_range_coordinateAxisParam
    (R := R) (K := K) i u]
  infer_instance

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 121 7: a nonzero base-ring axis parameterization is a lattice in
coordinate space. -/
private theorem coordinateAxisParam_algebraMap_isLattice {n : ℕ} (i : Fin n)
    (a : nonZeroDivisors R) :
    IsLattice K
      (LinearMap.range
        (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R)))) := by
  let u : Kˣ :=
    Units.mk0 (algebraMap R K (a : R))
      ((map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp a.property))
  -- Package the nonzero scalar as a field unit, then reuse the unit-scaled lattice result.
  simpa [u] using coordinateAxisParam_unit_isLattice (R := R) (K := K) i u

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: a base-ring axis multiple lies inside the standard
coordinate lattice. -/
private theorem coordinateAxisParam_algebraMap_le_coordinateLattice {n : ℕ} (i : Fin n)
    (a : R) :
    LinearMap.range
        (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K a)) ≤
      coordinateLattice (R := R) (K := K) n := by
  rw [coordinateLattice_eq_range_algebraMapPi (R := R) (K := K) n]
  -- Absorb the selected-axis factor into the `R^n` coordinate before applying the algebra map.
  rintro x ⟨c, rfl⟩
  refine ⟨fun j => if j = i then a * c j else c j, ?_⟩
  ext j
  by_cases hji : j = i
  · rw [coordinateAxisParam_apply]
    simp [hji, map_mul]
  · rw [coordinateAxisParam_apply]
    simp [hji]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 121 7: if a unit is represented by the fraction `a / b`, then
the axis lattice with parameter `a` lies inside the axis-scaled lattice with parameter that unit. -/
private theorem coordinateAxisParam_algebraMap_le_coordinateAxisParam_unit_of_mk_eq {n : ℕ}
    (i : Fin n) (a b : nonZeroDivisors R) (u : Kˣ)
    (hu : (u : K) = IsLocalization.mk' K (a : R) b) :
    LinearMap.range
        (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R))) ≤
      LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K)) := by
  have hspec :
      (u : K) * algebraMap R K (b : R) = algebraMap R K (a : R) := by
    -- The fraction presentation says exactly that multiplying `u = a / b` by `b` gives `a`.
    rw [hu]
    exact IsLocalization.mk'_spec K (a : R) b
  -- Replace an axis parameter `x_i` by `b * x_i` in the scaled lattice.
  rintro x ⟨c, rfl⟩
  refine ⟨fun j => if j = i then (b : R) * c j else c j, ?_⟩
  ext j
  by_cases hji : j = i
  · rw [coordinateAxisParam_apply, coordinateAxisParam_apply]
    simp only [hji, if_true, map_mul]
    rw [← mul_assoc, hspec]
  · rw [coordinateAxisParam_apply, coordinateAxisParam_apply]
    simp [hji]

/-- Helper for Chap10 Lemma 10 121 7: the determinant formula for scaling one coordinate by a
unit represented as a fraction `a / b`. -/
private theorem coordinateAxisScale_exp_latticeDistance_eq_ordFrac_of_mk_eq
    [Ring.KrullDimLE 1 R] {n : ℕ} (i : Fin n) (a b : nonZeroDivisors R) (u : Kˣ)
    (hu : (u : K) = IsLocalization.mk' K (a : R) b) :
    WithZero.exp
        (latticeDistance (coordinateLattice (R := R) (K := K) n)
          ((coordinateLattice (R := R) (K := K) n).map
            (((coordinateAxisScale (K := K) i u).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (u : K) := by
  classical
  let L : Submodule R (Fin n → K) :=
    LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (1 : K))
  let U : Submodule R (Fin n → K) :=
    LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (u : K))
  let N : Submodule R (Fin n → K) :=
    LinearMap.range (coordinateAxisParam (R := R) (K := K) n i (algebraMap R K (a : R)))
  have hL :
      coordinateLattice (R := R) (K := K) n = L := by
    -- Work in the range normal form where the quotient-length helpers apply directly.
    simpa [L] using coordinateLattice_eq_range_coordinateAxisParam_one (R := R) (K := K) i
  have hU :
      (coordinateLattice (R := R) (K := K) n).map
          (((coordinateAxisScale (K := K) i u).restrictScalars R) :
            (Fin n → K) →ₗ[R] (Fin n → K)) = U := by
    -- The image under the axis-scaling equivalence is the corresponding unit-scaled range.
    simpa [U] using
      coordinateLattice_map_coordinateAxisScale_eq_range_coordinateAxisParam (R := R) (K := K) i u
  have hU_L :
      L.map
          (((coordinateAxisScale (K := K) i u).restrictScalars R) :
            (Fin n → K) →ₗ[R] (Fin n → K)) = U := by
    -- The same image statement after rewriting the source lattice to its range normal form.
    rw [← hL]
    exact hU
  letI : IsLattice K L := by
    simpa [L] using
      coordinateAxisParam_unit_isLattice (R := R) (K := K) (n := n) i (1 : Kˣ)
  letI : IsLattice K U := by
    simpa [U] using coordinateAxisParam_unit_isLattice (R := R) (K := K) (n := n) i u
  letI : IsLattice K N := by
    simpa [N] using coordinateAxisParam_algebraMap_isLattice (R := R) (K := K) (n := n) i a
  by_cases hfield : IsField R
  · -- In the field case every lattice distance is zero and the order-of-vanishing map is trivial.
    have hord : Ring.ordFrac R (u : K) = 1 := by
      have hord_a : Ring.ordMonoidWithZeroHom R (a : R) = 1 := by
        have ha0 : (a : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.property
        rcases IsField.mul_inv_cancel hfield ha0 with ⟨ainv, hainv⟩
        have haunit : IsUnit (a : R) :=
          ⟨⟨(a : R), ainv, hainv, by simpa [mul_comm] using hainv⟩, rfl⟩
        have hspan : Ideal.span ({(a : R)} : Set R) = ⊤ :=
          Ideal.span_singleton_eq_top.mpr haunit
        have hlen : Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R)) = 0 := by
          simp [hspan]
        rw [ordMonoidWithZeroHom_eq_exp_length_span_singleton (R := R) a, hlen]
        simp
      have hord_b : Ring.ordMonoidWithZeroHom R (b : R) = 1 := by
        have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
        rcases IsField.mul_inv_cancel hfield hb0 with ⟨binv, hbinv⟩
        have hbunit : IsUnit (b : R) :=
          ⟨⟨(b : R), binv, hbinv, by simpa [mul_comm] using hbinv⟩, rfl⟩
        have hspan : Ideal.span ({(b : R)} : Set R) = ⊤ :=
          Ideal.span_singleton_eq_top.mpr hbunit
        have hlen : Module.length R (R ⧸ Ideal.span ({(b : R)} : Set R)) = 0 := by
          simp [hspan]
        rw [ordMonoidWithZeroHom_eq_exp_length_span_singleton (R := R) b, hlen]
        simp
      rw [hu, Ring.ordFrac_eq_div]
      rw [hord_a, hord_b]
      simp
    rw [hL, hU_L]
    rw [Submodule.latticeDistance_eq_zero_of_isField (M := L) (M' := U) hfield]
    rw [hord]
    simp
  · have hdim : ringKrullDim R = 1 :=
      Submodule.ringKrullDim_eq_one_of_not_isField (R := R) hfield
    have hNleL : N ≤ L := by
      rw [← hL]
      simpa [N] using
        coordinateAxisParam_algebraMap_le_coordinateLattice
          (R := R) (K := K) (n := n) i (a : R)
    have hNleU : N ≤ U := by
      simpa [U, N] using
        coordinateAxisParam_algebraMap_le_coordinateAxisParam_unit_of_mk_eq
          (R := R) (K := K) (n := n) i a b u hu
    have hdist :
        latticeDistance L U =
          ((Module.length R (L ⧸ N.submoduleOf L)).toNat : ℤ) -
            ((Module.length R (U ⧸ N.submoduleOf U)).toNat : ℤ) := by
      -- Replace the intersection in the definition by the common lower lattice `N`.
      rw [Submodule.latticeDistance_def]
      exact length_difference_inf_eq_length_difference_of_le_inf
        (R := R) (K := K) (V := Fin n → K) (M := L) (M' := U) (N := N)
        hdim (le_inf hNleL hNleU)
    have hlenL :
        Module.length R (L ⧸ N.submoduleOf L) =
          Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R)) := by
      simpa [L, N] using
        coordinateAxisParam_standard_quotient_length (R := R) (K := K) (n := n) i a
    have hlenU :
        Module.length R (U ⧸ N.submoduleOf U) =
          Module.length R (R ⧸ Ideal.span ({(b : R)} : Set R)) := by
      simpa [U, N] using
        coordinateAxisParam_scaled_quotient_length_of_mk_eq
          (R := R) (K := K) (n := n) i a b u hu
    calc
      WithZero.exp
          (latticeDistance (coordinateLattice (R := R) (K := K) n)
            ((coordinateLattice (R := R) (K := K) n).map
              (((coordinateAxisScale (K := K) i u).restrictScalars R) :
                (Fin n → K) →ₗ[R] (Fin n → K)))) =
          WithZero.exp (latticeDistance L U) := by
            rw [hL, hU_L]
      _ =
          WithZero.exp
            (((Module.length R (R ⧸ Ideal.span ({(a : R)} : Set R))).toNat : ℤ) -
              ((Module.length R (R ⧸ Ideal.span ({(b : R)} : Set R))).toNat : ℤ)) := by
            rw [hdist, hlenL, hlenU]
      _ = Ring.ordFrac R (u : K) := by
            rw [hu, Ring.ordFrac_eq_div]
            rw [ordMonoidWithZeroHom_eq_exp_length_span_singleton (R := R) a]
            rw [ordMonoidWithZeroHom_eq_exp_length_span_singleton (R := R) b]
            rw [WithZero.exp_sub]

/-- Helper for Chap10 Lemma 10 121 7: an invariant lattice for a determinant-one automorphism
already satisfies the determinant formula. -/
private theorem exp_latticeDistance_eq_ordFrac_det_of_map_eq_self_det_one
    [Ring.KrullDimLE 1 R] {n : ℕ} (ψ : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (M : Submodule R (Fin n → K)) [IsLattice K M]
    (hmap : M.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)) = M)
    (hdet : LinearEquiv.det ψ = 1) :
    WithZero.exp
        (latticeDistance M
          (M.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det ψ : K) := by
  -- Invariance makes the lattice distance zero.
  rw [hmap]
  rw [Submodule.latticeDistance_self]
  -- The determinant-one hypothesis makes the valuation side equal to one as well.
  rw [hdet]
  simp

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the determinant of a single-axis coordinate scaling is
the scaling unit. -/
private theorem coordinateAxisScale_det {n : ℕ} (i : Fin n) (u : Kˣ) :
    LinearEquiv.det (coordinateAxisScale (K := K) i u) = u := by
  -- Compute the determinant as the product of the coordinate determinants.
  rw [← Units.val_inj]
  let D : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal fun j => if j = i then (u : K) else 1
  have hlin :
      (coordinateAxisScale (K := K) i u : (Fin n → K) →ₗ[K] (Fin n → K)) =
        Matrix.toLin' D := by
    apply LinearMap.ext
    intro x
    funext j
    change coordinateAxisScale (K := K) i u x j = Matrix.toLin' D x j
    rw [coordinateAxisScale_apply, Matrix.diagonal_toLin']
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  rw [LinearEquiv.coe_det, hlin, LinearMap.det_toLin']
  change (Matrix.diagonal (fun j => if j = i then (u : K) else 1)).det = (u : K)
  rw [Matrix.det_diagonal]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Helper for Chap10 Lemma 10 121 7: the one-axis formula rewritten with the determinant of
the coordinate scaling. -/
private theorem coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] {n : ℕ} (i : Fin n) (u : Kˣ) :
    WithZero.exp
        (latticeDistance (coordinateLattice (R := R) (K := K) n)
          ((coordinateLattice (R := R) (K := K) n).map
            (((coordinateAxisScale (K := K) i u).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det (coordinateAxisScale (K := K) i u) : K) := by
  classical
  obtain ⟨a0, b0, hb0, hdiv⟩ := IsFractionRing.div_surjective R (u : K)
  have ha0 : a0 ∈ nonZeroDivisors R := by
    -- Since the represented fraction is the nonzero unit `u`, its numerator is nonzero.
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro ha
    have hu0 : (u : K) = 0 := by
      rw [← hdiv, ha, map_zero, zero_div]
    exact Units.ne_zero u hu0
  let a : nonZeroDivisors R := ⟨a0, ha0⟩
  let b : nonZeroDivisors R := ⟨b0, hb0⟩
  have hu : (u : K) = IsLocalization.mk' K (a : R) b := by
    -- Convert the fraction presentation from division notation to `mk'` notation.
    rw [IsFractionRing.mk'_eq_div]
    exact hdiv.symm
  -- Reuse the quotient-length axis computation and rewrite its right hand side by the determinant.
  simpa [coordinateAxisScale_det (K := K) i u] using
    coordinateAxisScale_exp_latticeDistance_eq_ordFrac_of_mk_eq
      (R := R) (K := K) (n := n) i a b u hu

/-- Helper for Chap10 Lemma 10 121 7: the one-axis determinant formula holds for any lattice,
not only for the standard coordinate lattice. -/
private theorem coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
    [Ring.KrullDimLE 1 R] {n : ℕ} (i : Fin n) (u : Kˣ)
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateAxisScale (K := K) i u).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det (coordinateAxisScale (K := K) i u) : K) := by
  let L : Submodule R (Fin n → K) := coordinateLattice (R := R) (K := K) n
  letI : IsLattice K L := coordinateLattice_isLattice (R := R) (K := K) n
  -- Lattice-independence transports the standard-lattice axis computation to `M`.
  calc
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateAxisScale (K := K) i u).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
        WithZero.exp
          (latticeDistance L
            (L.map
              (((coordinateAxisScale (K := K) i u).restrictScalars R) :
                (Fin n → K) →ₗ[R] (Fin n → K)))) := by
          rw [latticeDistance_image_eq_of_lattice
            (R := R) (K := K) (coordinateAxisScale (K := K) i u) M L]
    _ = Ring.ordFrac R (LinearEquiv.det (coordinateAxisScale (K := K) i u) : K) := by
          simpa [L] using
            coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det
              (R := R) (K := K) (n := n) i u

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: scale the coordinates in a chosen finite set by units and
fix the remaining coordinates. -/
private abbrev coordinatePartialScale {n : ℕ} (s : Finset (Fin n)) (u : Fin n → Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.piCongrRight fun j =>
    if j ∈ s then LinearEquiv.smulOfUnit (u j) else LinearEquiv.refl K K

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: partial coordinate scaling has the expected coordinate
formula. -/
private theorem coordinatePartialScale_apply {n : ℕ} (s : Finset (Fin n)) (u : Fin n → Kˣ)
    (x : Fin n → K) (j : Fin n) :
    coordinatePartialScale (K := K) s u x j =
      if j ∈ s then (u j : K) * x j else x j := by
  -- Expose the product equivalence coordinate by coordinate.
  rw [LinearEquiv.piCongrRight_apply]
  by_cases hjs : j ∈ s
  · simp only [hjs, ↓reduceIte]
    change (u j : K) • x j = (u j : K) * x j
    rw [smul_eq_mul]
  · simp only [hjs, ↓reduceIte, LinearEquiv.refl_apply]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: inserting one new coordinate into a partial scaling is
composition with the corresponding one-axis scaling. -/
private theorem coordinatePartialScale_insert {n : ℕ} (s : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ s) (u : Fin n → Kˣ) :
    coordinatePartialScale (K := K) (insert i s) u =
      (coordinateAxisScale (K := K) i (u i)).trans (coordinatePartialScale (K := K) s u) := by
  -- The inserted coordinate is scaled by the new axis map; all old coordinates are scaled by
  -- the previous partial scaling.
  ext x j
  rw [LinearEquiv.trans_apply]
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [hji]

/-- Helper for Chap10 Lemma 10 121 7: any finite product of coordinate-axis scalings satisfies
the determinant formula on every lattice. -/
private theorem coordinatePartialScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
    [Ring.KrullDimLE 1 R] {n : ℕ} (s : Finset (Fin n)) (u : Fin n → Kˣ) :
    ∀ (M : Submodule R (Fin n → K)) [IsLattice K M],
      WithZero.exp
          (latticeDistance M
            (M.map
              (((coordinatePartialScale (K := K) s u).restrictScalars R) :
                (Fin n → K) →ₗ[R] (Fin n → K)))) =
        Ring.ordFrac R (LinearEquiv.det (coordinatePartialScale (K := K) s u) : K) := by
  classical
  -- Induct over the finite set of scaled coordinates, composing in one axis at a time.
  refine Finset.induction_on s ?base ?step
  · intro M hM
    have hscale :
        coordinatePartialScale (K := K) (∅ : Finset (Fin n)) u =
          LinearEquiv.refl K (Fin n → K) := by
      ext x j
      simp
    rw [hscale]
    have hmap :
        M.map
            (((LinearEquiv.refl K (Fin n → K)).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)) = M := by
      ext x
      simp
    rw [hmap, Submodule.latticeDistance_self]
    simp
  · intro i s hi ih M hM
    rw [coordinatePartialScale_insert (K := K) s i hi u]
    exact exp_latticeDistance_trans
      (R := R) (K := K) (V := Fin n → K)
      (coordinateAxisScale (K := K) i (u i)) (coordinatePartialScale (K := K) s u)
      (fun N hN => coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
        (R := R) (K := K) i (u i) N)
      (fun N hN => ih N) M

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: diagonal coordinate scaling is the partial scaling on all
coordinates. -/
private abbrev coordinateDiagonalScale {n : ℕ} (u : Fin n → Kˣ) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  coordinatePartialScale (K := K) Finset.univ u

/-- Helper for Chap10 Lemma 10 121 7: a diagonal coordinate scaling satisfies the determinant
formula on every lattice. -/
private theorem coordinateDiagonalScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
    [Ring.KrullDimLE 1 R] {n : ℕ} (u : Fin n → Kˣ)
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateDiagonalScale (K := K) u).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det (coordinateDiagonalScale (K := K) u) : K) := by
  -- This is the full-set specialization of the partial-scaling induction.
  simpa [coordinateDiagonalScale] using
    coordinatePartialScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
      (R := R) (K := K) (s := Finset.univ) u M

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: a coordinate transvection has zero pairing between the
chosen covector and direction vector. -/
private theorem coordinateTransvection_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K) :
    (LinearMap.proj j : (Fin n → K) →ₗ[K] K) (Pi.single i c) = 0 := by
  -- The direction vector is supported away from the covector coordinate.
  simp [Pi.single_eq_of_ne hij.symm]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the coordinate transvection adding `c` times coordinate
`j` to coordinate `i`. -/
private abbrev coordinateTransvection {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.transvection (coordinateTransvection_zero (K := K) i j hij c)

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the coordinate transvection has the expected coordinate
formula. -/
private theorem coordinateTransvection_apply {n : ℕ} (i j k : Fin n) (hij : i ≠ j) (c : K)
    (x : Fin n → K) :
    coordinateTransvection (K := K) i j hij c x k =
      if k = i then x k + c * x j else x k := by
  -- Unfold the abstract transvection only to the coordinate formula needed below.
  by_cases hki : k = i
  · subst k
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      Pi.single_eq_same, smul_eq_mul, mul_comm]
  · have hik : i ≠ k := fun h => hki h.symm
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      hki, smul_eq_mul]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the inverse coordinate transvection is obtained by
negating the coefficient. -/
private theorem coordinateTransvection_symm_eq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K) :
    ((coordinateTransvection (K := K) i j hij c).symm :
        (Fin n → K) →ₗ[K] (Fin n → K)) =
      (coordinateTransvection (K := K) i j hij (-c) :
        (Fin n → K) →ₗ[K] (Fin n → K)) := by
  -- Compare both inverse candidates coordinatewise.
  apply LinearMap.ext
  intro x
  funext k
  by_cases hki : k = i
  · subst k
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      Pi.single_eq_same, smul_eq_mul, mul_comm]
  · have hik : i ≠ k := fun h => hki h.symm
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      hki, smul_eq_mul]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: the determinant of a coordinate transvection is one. -/
private theorem coordinateTransvection_det {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K) :
    LinearEquiv.det (coordinateTransvection (K := K) i j hij c) = 1 := by
  -- Use the determinant computation for abstract linear transvections.
  exact LinearEquiv.transvection.det_eq_one (coordinateTransvection_zero (K := K) i j hij c)

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: matrix transvections and coordinate transvections have
the same underlying linear map. -/
private theorem coordinateTransvection_toLin'_transvection {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (c : K) :
    Matrix.toLin' (Matrix.transvection i j c) =
      (coordinateTransvection (K := K) i j hij c :
        (Fin n → K) →ₗ[K] (Fin n → K)) := by
  -- Compare the matrix action and the abstract transvection coordinate by coordinate.
  apply LinearMap.ext
  intro x
  funext k
  by_cases hki : k = i
  · subst k
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      Matrix.transvection, Matrix.mulVec, Matrix.single, dotProduct, Pi.single_eq_same,
      smul_eq_mul, mul_comm]
  · have hik : i ≠ k := fun h => hki h.symm
    simp [coordinateTransvection, LinearEquiv.transvection, LinearMap.transvection,
      Matrix.transvection, Matrix.mulVec, Matrix.single, dotProduct, hki, hik, smul_eq_mul]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 121 7: an integral coordinate transvection maps the standard
coordinate lattice into itself. -/
private theorem coordinateLattice_map_coordinateTransvection_le {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (r : R) :
    (coordinateLattice (R := R) (K := K) n).map
        (((coordinateTransvection (K := K) i j hij (algebraMap R K r)).restrictScalars R) :
          (Fin n → K) →ₗ[R] (Fin n → K)) ≤
      coordinateLattice (R := R) (K := K) n := by
  rw [coordinateLattice_eq_range_algebraMapPi (R := R) (K := K) n]
  -- Update the `R`-coordinate vector by adding `r` times coordinate `j` to coordinate `i`.
  rintro x ⟨y, hy, rfl⟩
  rcases hy with ⟨c, rfl⟩
  refine ⟨Function.update c i (c i + r * c j), ?_⟩
  ext k
  change algebraMap R K (Function.update c i (c i + r * c j) k) =
    coordinateTransvection (K := K) i j hij (algebraMap R K r)
      ((LinearMap.piMap fun _ : Fin n => Algebra.linearMap R K) c) k
  rw [coordinateTransvection_apply]
  by_cases hki : k = i
  · subst k
    simp [LinearMap.piMap, map_add, map_mul]
  · simp [LinearMap.piMap, hki]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] in
/-- Helper for Chap10 Lemma 10 121 7: an integral coordinate transvection preserves the standard
coordinate lattice. -/
private theorem coordinateLattice_map_coordinateTransvection_eq_self {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (r : R) :
    (coordinateLattice (R := R) (K := K) n).map
        (((coordinateTransvection (K := K) i j hij (algebraMap R K r)).restrictScalars R) :
          (Fin n → K) →ₗ[R] (Fin n → K)) =
      coordinateLattice (R := R) (K := K) n := by
  let τ : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    coordinateTransvection (K := K) i j hij (algebraMap R K r)
  -- Prove both inclusions, using the inverse transvection with coefficient `-r` for the reverse.
  apply le_antisymm
  · exact coordinateLattice_map_coordinateTransvection_le (R := R) (K := K) i j hij r
  · intro x hx
    have hsymm_mem : τ.symm x ∈ coordinateLattice (R := R) (K := K) n := by
      have hneg :=
        coordinateLattice_map_coordinateTransvection_le (R := R) (K := K) i j hij (-r)
      have hmem := hneg (Submodule.mem_map_of_mem (f :=
        (((coordinateTransvection (K := K) i j hij (algebraMap R K (-r))).restrictScalars R) :
          (Fin n → K) →ₗ[R] (Fin n → K))) hx)
      have hsymm :
          τ.symm x =
            coordinateTransvection (K := K) i j hij (algebraMap R K (-r)) x := by
        calc
          τ.symm x =
              coordinateTransvection (K := K) i j hij (-(algebraMap R K r)) x :=
                LinearMap.congr_fun
                  (coordinateTransvection_symm_eq (K := K) i j hij (algebraMap R K r)) x
          _ = coordinateTransvection (K := K) i j hij (algebraMap R K (-r)) x := by
                simp
      simpa [hsymm] using hmem
    refine ⟨τ.symm x, hsymm_mem, ?_⟩
    simp [τ]

/-- Helper for Chap10 Lemma 10 121 7: integral coordinate transvections satisfy the determinant
formula on every lattice. -/
private theorem coordinateIntegralTransvection_exp_latticeDistance_eq_ordFrac_det_of_lattice
    [Ring.KrullDimLE 1 R] {n : ℕ} (i j : Fin n) (hij : i ≠ j) (r : R)
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateTransvection (K := K) i j hij (algebraMap R K r)).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R
        (LinearEquiv.det
          (coordinateTransvection (K := K) i j hij (algebraMap R K r)) : K) := by
  let τ : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    coordinateTransvection (K := K) i j hij (algebraMap R K r)
  let L : Submodule R (Fin n → K) := coordinateLattice (R := R) (K := K) n
  letI : IsLattice K L := coordinateLattice_isLattice (R := R) (K := K) n
  have hmap :
      L.map ((τ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)) = L := by
    simpa [τ, L] using
      coordinateLattice_map_coordinateTransvection_eq_self (R := R) (K := K) i j hij r
  have hdet : LinearEquiv.det τ = 1 := by
    simpa [τ] using coordinateTransvection_det (K := K) i j hij (algebraMap R K r)
  have hcoord :
      WithZero.exp
          (latticeDistance L
            (L.map ((τ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
        Ring.ordFrac R (LinearEquiv.det τ : K) :=
    exp_latticeDistance_eq_ordFrac_det_of_map_eq_self_det_one
      (R := R) (K := K) τ L hmap hdet
  -- Transport the invariant-lattice calculation from the standard lattice to `M`.
  calc
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateTransvection (K := K) i j hij (algebraMap R K r)).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
        WithZero.exp
          (latticeDistance L
            (L.map ((τ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) := by
          rw [latticeDistance_image_eq_of_lattice (R := R) (K := K) τ M L]
    _ = Ring.ordFrac R
          (LinearEquiv.det
            (coordinateTransvection (K := K) i j hij (algebraMap R K r)) : K) := by
          simpa [τ] using hcoord

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    [FiniteDimensional K V] in
/-- Helper for Chap10 Lemma 10 121 7: a nonzero coordinate transvection is a conjugate of the
unit integral transvection by one-axis scalings. -/
private theorem coordinateTransvection_factor {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    {c : K} (hc : c ≠ 0) :
    coordinateTransvection (K := K) i j hij c =
      (coordinateAxisScale (K := K) i (Units.mk0 c hc)⁻¹).trans
        ((coordinateTransvection (K := K) i j hij 1).trans
          (coordinateAxisScale (K := K) i (Units.mk0 c hc))) := by
  -- Check the conjugation identity on every coordinate.
  ext x k
  by_cases hki : k = i
  · subst k
    simp [coordinateAxisScale, coordinateTransvection, LinearEquiv.transvection,
      LinearMap.transvection, LinearEquiv.smulOfUnit, Pi.single_eq_same,
      hij.symm, smul_eq_mul, mul_comm]
  · have hik : i ≠ k := fun h => hki h.symm
    simp [coordinateAxisScale, coordinateTransvection, LinearEquiv.transvection,
      LinearMap.transvection, LinearEquiv.smulOfUnit, hki, smul_eq_mul]

/-- Helper for Chap10 Lemma 10 121 7: arbitrary coordinate transvections satisfy the determinant
formula on every lattice. -/
private theorem coordinateTransvection_exp_latticeDistance_eq_ordFrac_det_of_lattice
    [Ring.KrullDimLE 1 R] {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K)
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map
            (((coordinateTransvection (K := K) i j hij c).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det (coordinateTransvection (K := K) i j hij c) : K) := by
  by_cases hc : c = 0
  · subst c
    have hzero :
        coordinateTransvection (K := K) i j hij (0 : K) =
          LinearEquiv.refl K (Fin n → K) := by
      ext x k
      simp [coordinateTransvection_apply]
    -- The zero-coefficient transvection is the identity.
    rw [hzero]
    have hmap :
        M.map
            (((LinearEquiv.refl K (Fin n → K)).restrictScalars R) :
              (Fin n → K) →ₗ[R] (Fin n → K)) = M := by
      ext x
      simp
    rw [hmap, Submodule.latticeDistance_self]
    simp
  · let u : Kˣ := Units.mk0 c hc
    have hfactor :
        coordinateTransvection (K := K) i j hij c =
          (coordinateAxisScale (K := K) i u⁻¹).trans
            ((coordinateTransvection (K := K) i j hij 1).trans
              (coordinateAxisScale (K := K) i u)) := by
      simpa [u] using coordinateTransvection_factor (K := K) i j hij hc
    rw [hfactor]
    -- Compose axis scaling, the integral unit transvection, and the inverse axis scaling.
    exact exp_latticeDistance_trans
      (R := R) (K := K) (V := Fin n → K)
      (coordinateAxisScale (K := K) i u⁻¹)
      ((coordinateTransvection (K := K) i j hij 1).trans
        (coordinateAxisScale (K := K) i u))
      (fun N hN => coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
        (R := R) (K := K) i u⁻¹ N)
      (fun N hN =>
        exp_latticeDistance_trans
          (R := R) (K := K) (V := Fin n → K)
          (coordinateTransvection (K := K) i j hij 1)
          (coordinateAxisScale (K := K) i u)
          (fun P hP => by
            simpa using
              coordinateIntegralTransvection_exp_latticeDistance_eq_ordFrac_det_of_lattice
                (R := R) (K := K) i j hij (1 : R) P)
          (fun P hP => coordinateAxisScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
            (R := R) (K := K) i u P) N)
      M

/-- Helper for Chap10 Lemma 10 121 7: an invertible coordinate matrix satisfies the determinant
formula for every compatible linear equivalence. -/
private theorem coordinateMatrix_exp_latticeDistance_eq_ordFrac_det_of_toMatrix
    [Ring.KrullDimLE 1 R] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0)
    (ψ : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (hψ : Matrix.toLin' A = (ψ : (Fin n → K) →ₗ[K] (Fin n → K)))
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det ψ : K) := by
  classical
  let P : Matrix (Fin n) (Fin n) K → Prop := fun B =>
    ∀ (φ : (Fin n → K) ≃ₗ[K] (Fin n → K)),
      Matrix.toLin' B = (φ : (Fin n → K) →ₗ[K] (Fin n → K)) →
        ∀ (N : Submodule R (Fin n → K)) [IsLattice K N],
          WithZero.exp
              (latticeDistance N
                (N.map ((φ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
            Ring.ordFrac R (LinearEquiv.det φ : K)
  have hP : P A := by
    -- Reduce the matrix calculation to diagonal matrices, transvections, and products.
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero P A hA
    · intro D hD φ hφ N hN
      have hD_ne : ∀ i, D i ≠ 0 := by
        rw [Matrix.det_diagonal] at hD
        exact fun i => (Finset.prod_ne_zero_iff.mp hD) i (Finset.mem_univ i)
      let u : Fin n → Kˣ := fun i => Units.mk0 (D i) (hD_ne i)
      let δ : (Fin n → K) ≃ₗ[K] (Fin n → K) := coordinateDiagonalScale (K := K) u
      have hδ :
          Matrix.toLin' (Matrix.diagonal D) =
            (δ : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        apply LinearMap.ext
        intro x
        funext i
        rw [Matrix.diagonal_toLin']
        simp [δ, coordinateDiagonalScale, coordinatePartialScale, LinearEquiv.smulOfUnit,
          smul_eq_mul, u]
      have hφeq : φ = δ := by
        apply LinearEquiv.toLinearMap_injective
        exact hφ.symm.trans hδ
      -- Replace the compatible equivalence by the canonical diagonal equivalence.
      rw [hφeq]
      exact coordinateDiagonalScale_exp_latticeDistance_eq_ordFrac_det_of_lattice
        (R := R) (K := K) u N
    · intro t φ hφ N hN
      let τ : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
        coordinateTransvection (K := K) t.i t.j t.hij t.c
      have hτ :
          Matrix.toLin' t.toMatrix =
            (τ : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        simpa [Matrix.TransvectionStruct.toMatrix, τ] using
          coordinateTransvection_toLin'_transvection (K := K) t.i t.j t.hij t.c
      have hφeq : φ = τ := by
        apply LinearEquiv.toLinearMap_injective
        exact hφ.symm.trans hτ
      -- Replace the compatible equivalence by the canonical coordinate transvection.
      rw [hφeq]
      exact coordinateTransvection_exp_latticeDistance_eq_ordFrac_det_of_lattice
        (R := R) (K := K) t.i t.j t.hij t.c N
    · intro B C hB hC hPB hPC φ hφ N hN
      let eB : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
        Matrix.toLinearEquiv (Pi.basisFun K (Fin n)) B (isUnit_iff_ne_zero.mpr hB)
      let eC : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
        Matrix.toLinearEquiv (Pi.basisFun K (Fin n)) C (isUnit_iff_ne_zero.mpr hC)
      have heB :
          Matrix.toLin' B = (eB : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        change Matrix.toLin' B =
          Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) B
        rw [Matrix.toLin_eq_toLin']
      have heC :
          Matrix.toLin' C = (eC : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        change Matrix.toLin' C =
          Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) C
        rw [Matrix.toLin_eq_toLin']
      have hBC :
          Matrix.toLin' (B * C) =
            ((eC.trans eB) : (Fin n → K) →ₗ[K] (Fin n → K)) := by
        rw [Matrix.toLin'_mul, heB, heC]
        rfl
      have hφeq : φ = eC.trans eB := by
        apply LinearEquiv.toLinearMap_injective
        exact hφ.symm.trans hBC
      rw [hφeq]
      -- Product compatibility is exactly the already-proved transitivity of the distance formula.
      exact exp_latticeDistance_trans
        (R := R) (K := K) (V := Fin n → K) eC eB
        (fun L hL => hPC eC heC L)
        (fun L hL => hPB eB heB L) N
  exact hP ψ hψ M

/-- Chap10 Lemma 10 121 7: after lattice-independence, the determinant formula only
needs to be computed on the standard coordinate lattice. -/
private theorem coordinateLattice_exp_latticeDistance_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] {n : ℕ} (ψ : (Fin n → K) ≃ₗ[K] (Fin n → K)) :
    WithZero.exp
        (latticeDistance (coordinateLattice (R := R) (K := K) n)
          ((coordinateLattice (R := R) (K := K) n).map
            ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det ψ : K) := by
  let A : Matrix (Fin n) (Fin n) K :=
    LinearMap.toMatrix' (ψ : (Fin n → K) →ₗ[K] (Fin n → K))
  have hA : A.det ≠ 0 := by
    -- The matrix of a linear equivalence has nonzero determinant.
    change (LinearMap.toMatrix' (ψ : (Fin n → K) →ₗ[K] (Fin n → K))).det ≠ 0
    rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det]
    exact Units.ne_zero (LinearEquiv.det ψ)
  letI : IsLattice K (coordinateLattice (R := R) (K := K) n) :=
    coordinateLattice_isLattice (R := R) (K := K) n
  -- Apply the matrix-generation wrapper to the matrix of `ψ`.
  exact coordinateMatrix_exp_latticeDistance_eq_ordFrac_det_of_toMatrix
    (R := R) (K := K) A hA ψ (by
      change Matrix.toLin'
          (LinearMap.toMatrix' (ψ : (Fin n → K) →ₗ[K] (Fin n → K))) =
        (ψ : (Fin n → K) →ₗ[K] (Fin n → K))
      rw [Matrix.toLin'_toMatrix'])
    (coordinateLattice (R := R) (K := K) n)

/-- Helper for Chap10 Lemma 10 121 7: the determinant formula in coordinate space is the
remaining generator calculation after basis transport. -/
private theorem coordinate_exp_latticeDistance_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] {n : ℕ} (ψ : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (M : Submodule R (Fin n → K)) [IsLattice K M] :
    WithZero.exp
        (latticeDistance M
          (M.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
      Ring.ordFrac R (LinearEquiv.det ψ : K) := by
  let L : Submodule R (Fin n → K) := coordinateLattice (R := R) (K := K) n
  letI : IsLattice K L := coordinateLattice_isLattice (R := R) (K := K) n
  -- Route correction: reduce arbitrary coordinate lattices to the standard coordinate lattice
  -- first; the remaining work is the generator computation isolated above.
  calc
    WithZero.exp
        (latticeDistance M
          (M.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) =
        WithZero.exp
          (latticeDistance L
            (L.map ((ψ.restrictScalars R) : (Fin n → K) →ₗ[R] (Fin n → K)))) := by
          -- Lattice-independence lets the coordinate calculation be performed on `L`.
          rw [latticeDistance_image_eq_of_lattice (R := R) (K := K) ψ M L]
    _ = Ring.ordFrac R (LinearEquiv.det ψ : K) := by
          -- The remaining open computation is now isolated on the standard coordinate lattice.
          simpa [L] using
            coordinateLattice_exp_latticeDistance_eq_ordFrac_det (R := R) (K := K) ψ

-- Proof sketch: first prove the canonical multiplicative bridge in `Ring.ordFrac`, then pass to
-- the additive textbook order of vanishing by applying `WithZero.log` as in
-- `Definition_10_121_2`.
/-- Companion bridge: the lattice-distance identity expressed directly in the canonical
`Ring.ordFrac` owner. -/
theorem exp_latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    WithZero.exp (latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V))) =
      Ring.ordFrac R (LinearEquiv.det φ : K) := by
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  let ψ : (Fin (Module.finrank K V) → K) ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    (e.symm.trans φ).trans e
  let eR : V →ₗ[R] (Fin (Module.finrank K V) → K) := (e.restrictScalars R : V ≃ₗ[R] _)
  let ψR : (Fin (Module.finrank K V) → K) →ₗ[R] (Fin (Module.finrank K V) → K) :=
    (ψ.restrictScalars R : (Fin (Module.finrank K V) → K) ≃ₗ[R] _)
  have himage : (M.map ((φ.restrictScalars R) : V →ₗ[R] V)).map eR = (M.map eR).map ψR := by
    -- Transporting `φ(M)` by the basis equivalence is the same as applying the conjugate
    -- coordinate automorphism to the transported lattice.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨e z, Submodule.mem_map_of_mem hz, ?_⟩
      simp [eR, ψR, ψ]
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨φ z, Submodule.mem_map_of_mem hz, ?_⟩
      simp [eR, ψR, ψ]
  have hdist_map := latticeDistance_map_equiv (R := R) (K := K) (V := V) e M
    (M.map ((φ.restrictScalars R) : V →ₗ[R] V))
  have hdist :
      latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
        latticeDistance (M.map eR) ((M.map eR).map ψR) := by
    -- The distance is unchanged under the basis equivalence, after normalizing the image lattice.
    rw [himage] at hdist_map
    exact hdist_map.symm
  have hcoord := coordinate_exp_latticeDistance_eq_ordFrac_det (R := R) (K := K) ψ (M.map eR)
  have hdet : LinearEquiv.det ψ = LinearEquiv.det φ := by
    -- Determinants are invariant under conjugation by the chosen basis equivalence.
    simpa [ψ] using LinearEquiv.det_conj φ e
  calc
    WithZero.exp (latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V))) =
        WithZero.exp (latticeDistance (M.map eR) ((M.map eR).map ψR)) := by
          rw [hdist]
    _ = Ring.ordFrac R (LinearEquiv.det ψ : K) := hcoord
    _ = Ring.ordFrac R (LinearEquiv.det φ : K) := by
          rw [hdet]

/-- Additive form for Chap10 Lemma 10 121 7: for a lattice `M` in a finite-dimensional
`K`-vector space, the lattice distance between `M` and its image under a `K`-linear automorphism
`φ` equals the additive order of vanishing of `det φ`, recovered from the canonical
`Ring.ordFrac` owner by `WithZero.log`. -/
@[stacks 02MI]
theorem latticeDistance_image_eq_ordFrac_det
    [Ring.KrullDimLE 1 R] (φ : V ≃ₗ[K] V) (M : Submodule R V) [IsLattice K M] :
    latticeDistance M (M.map ((φ.restrictScalars R) : V →ₗ[R] V)) =
      WithZero.log (Ring.ordFrac R (LinearEquiv.det φ : K)) := by
  simpa using congrArg WithZero.log (exp_latticeDistance_image_eq_ordFrac_det φ M)

end
