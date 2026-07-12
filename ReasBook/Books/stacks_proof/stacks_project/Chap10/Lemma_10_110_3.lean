import StacksProject_2024.Chap10.Lemma_10_110_3.Index
import Mathlib.Tactic.StacksAttribute
-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: homological bounds for the residue field of a Noetherian local ring;
* sampled owner declarations:
  `CategoryTheory.projectiveDimension`,
  `IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `projectiveDimension_le_iff`;
* owner abstraction: the canonical owners are `projectiveDimension` on `ModuleCat R` and
  `CotangentSpace R` for the embedding-dimension side;
* layer: `source-facing`, since the textbook item is the lower bound comparing these two canonical
  invariants rather than defining a new owner object.
-/

-- Proof sketch: choose a basis of the cotangent space `CotangentSpace R = maximalIdeal R / (maximalIdeal R)^2`
-- and the corresponding Koszul complex. Compare it with a minimal finite free resolution of
-- `ResidueField R`; after tensoring with the residue field, the comparison maps are injective in
-- each degree, forcing the resolution to be nonzero through degree
-- `Module.finrank (ResidueField R) (CotangentSpace R)`.

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

/-- Helper for Lemma 10.110.3: the missing source Koszul comparison induction contradicts a
minimal finite free resolution that is shorter than the cotangent-space dimension. -/
lemma cotangentKoszulComparison_contradicts_short_minimalResolution
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 2)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    False := by
  classical
  -- Route correction: build the source comparison directly against the chosen minimal finite free
  -- resolution, instead of routing through public self-Tor for the local Koszul complex.
  have hfinrank_top :
      Module.finrank (ResidueField R) (CotangentSpace R) = (d + 1) + 1 := by
    simpa [Nat.add_assoc] using hfinrank
  obtain ⟨b, x, hx, _hspan⟩ :=
    cotangent_basis_lift_generates_maximalIdeal (R := R) (d := d + 1) hfinrank_top
  obtain ⟨α, hα⟩ := localKoszulComparisonMap_exists (R := R) x ρ hρ
  have htopTerm :
      Nontrivial
        (TensorProduct R (ResidueField R)
          ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).X ((d + 1) + 1))) :=
    residueTensor_localKoszul_topTerm_nontrivial (R := R) x
  have htarget :
      Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) :=
    topBaseChangeTerm_subsingleton_of_shortComplex (R := R) C
  -- The remaining comparison theorem consumes the assembled top-degree data and gives the
  -- contradiction with the zero top target.
  exact
    minimalComparison_topFirstOrder_contradiction
      (R := R) b x hx C ρ hρ α hα hminimal (by simpa [Nat.add_assoc] using htopTerm)
      htarget

/-- Helper for Lemma 10.110.3: the source Koszul comparison should inject the top exterior
cotangent class into the residue-field reduction of the top minimal-resolution term. -/
lemma cotangentExterior_injective_baseChangeTerm_of_minimalResolution
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 2)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    ∃ f :
      (⋀[ResidueField R]^(d + 2) (CotangentSpace R)) →
        TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2)),
    Function.Injective f := by
  -- Route correction: the target term is above the displayed length of `C`, so the requested
  -- injection can only be obtained after proving that the hypotheses are inconsistent.
  have hcontr : False := by
    -- The remaining source-facing gap is now isolated in one comparison theorem rather than
    -- hidden inside the construction of the requested injection.
    exact
      cotangentKoszulComparison_contradicts_short_minimalResolution
        (R := R) hfinrank C ρ hρ hminimal
  exact False.elim hcontr

/-- Helper for Lemma 10.110.3: a top exterior cotangent space of matching degree cannot inject
into a subsingleton target. -/
lemma topExteriorCotangentSpace_not_injective_to_subsingleton
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 2)
    {T : Type*} (hT : Subsingleton T)
    (f : (⋀[ResidueField R]^(d + 2) (CotangentSpace R)) → T) :
    ¬ Function.Injective f := by
  -- The finrank hypothesis identifies this exterior power as the top exterior power, so it is
  -- nontrivial.
  have hsource :
      Nontrivial (⋀[ResidueField R]^(d + 2) (CotangentSpace R)) := by
    simpa [Nat.add_assoc] using
      (top_exterior_cotangentSpace_nontrivial (R := R) (d := d + 1) hfinrank)
  intro hf
  have hsource_subsingleton :
      Subsingleton (⋀[ResidueField R]^(d + 2) (CotangentSpace R)) := by
    -- Injectivity transfers the subsingleton property of the target back to the source.
    constructor
    intro x y
    exact hf (hT.elim (f x) (f y))
  exact (not_subsingleton_iff_nontrivial.mpr hsource) hsource_subsingleton

/-- Helper for Lemma 10.110.3: a minimal finite free resolution contradicts the nonvanishing of
the top reduced Koszul differential in degree `d + 2`. -/
lemma minimal_resolution_koszul_top_degree_contradiction
    {d : ℕ}
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 2)
    (C : FiniteFreeComplex R (d + 1))
    (ρ : C.toChainComplex ⟶ moduleSingle[R] (ResidueField R))
    (hρ : ChainComplex.IsFiniteFreeResolution ρ)
    (hminimal :
      ∀ i : Fin (d + 1), ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
        FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R) :
    False := by
  -- Route correction: replace the old public top-Tor nonvanishing route by the source-facing
  -- Koszul comparison. The top exterior class injects into the reduced top term, but that target
  -- is zero above the finite-free-resolution length bound.
  obtain ⟨f, hf⟩ :=
    cotangentExterior_injective_baseChangeTerm_of_minimalResolution
      (R := R) hfinrank C ρ hρ hminimal
  have htarget :
      Subsingleton (TensorProduct R (ResidueField R) (C.toChainComplex.X (d + 2))) :=
    topBaseChangeTerm_subsingleton_of_shortComplex (R := R) C
  exact
    (topExteriorCotangentSpace_not_injective_to_subsingleton
      (R := R) hfinrank htarget f) hf

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: if the residue field is projective as an `R`-module, then the
maximal ideal of the local ring vanishes. -/
lemma maximalIdeal_eq_bot_of_projective_residueField
    (hproj : Module.Projective R (ResidueField R)) :
    maximalIdeal R = ⊥ := by
  let π : R →ₗ[R] ResidueField R := (Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap
  have hπ_surj : Function.Surjective π := by
    simpa [π] using (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  obtain ⟨σ, hσ⟩ :=
    (Module.Projective.iff_split_of_projective (R := R) (M := R)
      (P := ResidueField R) π hπ_surj).mp hproj
  let e : R := 1 - σ 1
  have hσ1 : Ideal.Quotient.mk (maximalIdeal R) (σ 1) = 1 := by
    -- The splitting sends the residue class of `1` back to a lift of `1`.
    simpa [π] using DFunLike.congr_fun hσ (1 : ResidueField R)
  have he_mem : e ∈ maximalIdeal R := by
    -- The defect `1 - σ(1)` lies in the kernel of the residue map, hence in `𝔪`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    calc
      Ideal.Quotient.mk (maximalIdeal R) e
          = 1 - Ideal.Quotient.mk (maximalIdeal R) (σ 1) := by
            simp [e]
      _ = 0 := by
            simp [hσ1]
  have hmul_right : ∀ {x : R}, x ∈ maximalIdeal R → x = x * e := by
    intro x hx
    have hxq : IsLocalRing.residue R x = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hσx : σ (IsLocalRing.residue R x) = x * σ 1 := by
      calc
        σ (IsLocalRing.residue R x) = σ (x • (1 : ResidueField R)) := by
          simp [Algebra.smul_def]
        _ = x • σ 1 := by
          rw [map_smul]
        _ = x * σ 1 := by
          simp [smul_eq_mul]
    have hxσ0 : x * σ 1 = 0 := by
      simpa [hσx] using congrArg σ hxq
    calc
      x = x * 1 := by simp
      _ = x * (e + σ 1) := by
        simp [e, sub_eq_add_neg, add_comm, add_left_comm]
      _ = x * e + x * σ 1 := by
        ring
      _ = x * e := by
        simp [hxσ0]
  have he_idem : IsIdempotentElem e := by
    -- Applying the kernel relation to `e` itself shows that `e` is idempotent.
    simpa [IsIdempotentElem] using (hmul_right he_mem).symm
  have hunit : IsUnit (1 - e) := by
    -- In a local ring, an element of `𝔪` has unit complement.
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits e
      ((IsLocalRing.mem_maximalIdeal e).1 he_mem)
  have he_zero : e = 0 := by
    -- Multiply `(1 - e) * e = 0` by the inverse of the unit `1 - e`.
    rcases hunit with ⟨u, hu⟩
    have hmul_zero : ((↑u : R) * e) = 0 := by
      simpa [hu] using he_idem.one_sub_mul_self
    have := congrArg (fun y : R => ↑u⁻¹ * y) hmul_zero
    simpa [mul_assoc] using this
  apply eq_bot_iff.mpr
  intro x hx
  -- Once `e = 0`, the kernel relation `x = x * e` forces every `x ∈ 𝔪` to vanish.
  calc
    x = x * e := hmul_right hx
    _ = 0 := by simp [he_zero]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: a projective residue field forces cotangent-space dimension `0`. -/
lemma finrank_cotangentSpace_eq_zero_of_projective_residueField
    (hproj : Module.Projective R (ResidueField R)) :
    Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
  have hfield : IsField R := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    exact maximalIdeal_eq_bot_of_projective_residueField (R := R) hproj
  let _ : Field R := hfield.toField
  -- Over a field the maximal ideal is zero, so the cotangent space is trivial.
  simpa using finrank_cotangentSpace_eq_zero (R := R)

/-- Helper for Lemma 10.110.3: a bounded finite free resolution shorter than the cotangent
dimension contradicts the top residue-field Tor class. -/
lemma finiteFreeResolutionLengthLE_contradicts_cotangentSpace_dimension_succ
    {d : ℕ}
    (hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d)
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1) :
    False := by
  cases d with
  | zero =>
      -- In length `0`, the residue field would be finite free, hence projective. The quotient map
      -- `R → κ` would then split, forcing `𝔪 = 0` and therefore cotangent-space dimension `0`.
      have hfree : Module.Free R (ResidueField R) :=
        (hasFiniteFreeResolutionLengthLE_zero_iff (R := R) (M := ResidueField R)).1 hres |>.1
      let _ : Module.Free R (ResidueField R) := hfree
      have hproj : Module.Projective R (ResidueField R) := inferInstance
      have hzero :
          Module.finrank (ResidueField R) (CotangentSpace R) = 0 :=
        finrank_cotangentSpace_eq_zero_of_projective_residueField (R := R) hproj
      have hcontra : (0 : ℕ) = 1 := by
        simpa [hzero] using hfinrank
      norm_num at hcontra
  | succ d =>
      obtain ⟨F, π, hπ, hFfree, hFfinite, hbound⟩ :=
        exists_residueField_finiteFreeResolution_data (R := R) hres
      let C : FiniteFreeComplex R (d + 1) :=
        finiteFreeComplex_of_bounded_resolution (R := R) F hFfree hFfinite hbound
      obtain ⟨Cmin, ρmin, hρmin, hminimal⟩ :=
        exists_minimal_residueField_finiteFreeComplex (R := R) C π hπ
      -- Minimalizing the bounded resolution puts every differential entry in `maximalIdeal R`;
      -- the Koszul top-degree contradiction then rules out the successor finrank case.
      exact
        minimal_resolution_koszul_top_degree_contradiction
          (R := R) hfinrank Cmin ρmin hρmin hminimal

/-- Helper for Lemma 10.110.3: the source proof's Koszul/minimal-resolution comparison should
show that the residue field cannot have projective dimension strictly smaller than the cotangent-
space dimension. -/
lemma residueField_not_hasProjectiveDimensionLT_finrank_cotangentSpace :
    ¬ HasProjectiveDimensionLT
        (ModuleCat.of R (ResidueField R))
        (Module.finrank (ResidueField R) (CotangentSpace R)) := by
  intro hpd
  -- Split the critical degree into the zero case and a successor degree where Tor detects the
  -- obstruction.
  cases hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) with
  | zero =>
      have hpd0 : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) 0 := by
        simpa [hfinrank] using hpd
      have hzero : Limits.IsZero (ModuleCat.of R (ResidueField R)) := by
        simpa using (CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero
          (X := ModuleCat.of R (ResidueField R))).mp hpd0
      exact residueField_module_not_isZero (R := R) hzero
  | succ d =>
      have hpd_succ : HasProjectiveDimensionLT (ModuleCat.of R (ResidueField R)) (d + 1) := by
        simpa [hfinrank, Nat.succ_eq_add_one] using hpd
      have hres : HasFiniteFreeResolutionLengthLE R (ResidueField R) d :=
        residueField_hasFiniteFreeResolutionLengthLE_of_hasProjectiveDimensionLT_succ (R := R)
          (d := d) hpd_succ
      have hfinrank_succ :
          Module.finrank (ResidueField R) (CotangentSpace R) = d + 1 := by
        simpa [Nat.succ_eq_add_one] using hfinrank
      -- The finite-resolution contradiction is now the single owner of the source Koszul
      -- obstruction, so the projective-dimension negation no longer mentions Tor directly.
      exact
        finiteFreeResolutionLengthLE_contradicts_cotangentSpace_dimension_succ
          (R := R) hres hfinrank_succ

/-- Chap10 Lemma 10 110 3: for a Noetherian local ring `R`, the projective dimension of the residue field
`ResidueField R` is at least the dimension of the cotangent space `CotangentSpace R = 𝔪 / 𝔪²`
over the residue field. -/
@[stacks 00OA]
theorem finrank_cotangentSpace_le_projectiveDimension_residueField :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤
      projectiveDimension (ModuleCat.of R (ResidueField R)) := by
  -- Route correction: isolate the source proof's Koszul comparison as the negation of
  -- `HasProjectiveDimensionLT` in the critical degree, then convert that owner-level statement to
  -- the desired lower bound via `projectiveDimension_ge_iff`.
  rw [CategoryTheory.projectiveDimension_ge_iff]
  exact residueField_not_hasProjectiveDimensionLT_finrank_cotangentSpace (R := R)

end
