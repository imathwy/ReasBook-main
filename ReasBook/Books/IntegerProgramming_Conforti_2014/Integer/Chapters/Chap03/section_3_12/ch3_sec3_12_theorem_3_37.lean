import Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_1
import Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_33

open scoped Pointwise

-- Domain sampling for this theorem:
-- * primary domain: polyhedra, recession cones, and exposed faces in `ℝ^n`
-- * source-facing owners: `is_polyhedron`, `IsExposed`, `recessionCone`, `linealitySpace`,
--   `IsMinimalFaceOf`
-- * core/canonical finite-family owner: `cone (Set.range rays)`
-- * derived face API used below: `IsExposed.isExtreme`
-- * core/canonical derived owner for `dim (lin P)`: `linealitySubmodule P`

section Theorem337

variable {n : ℕ}

/-- Helper for Theorem 3.37: every vector in the conic summand of a
`convexHull + cone + lineality` representation is a recession direction of the ambient set. -/
lemma cone_subset_recessionCone_of_repr
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Set (Fin n → ℝ))
    (X : ι → Fin n → ℝ)
    (Y : κ → Fin n → ℝ)
    (h_repr :
      P = convexHull ℝ (Set.range X) + cone (Set.range Y) + linealitySpace P) :
    cone (Set.range Y) ⊆ recessionCone P := by
  intro r hr x hx a ha
  rw [h_repr] at hx ⊢
  rw [Set.mem_add] at hx ⊢
  rcases hx with ⟨w, hw, l, hl, hsum⟩
  have hw' : w + a • r ∈ convexHull ℝ (Set.range X) + cone (Set.range Y) := by
    rw [Set.mem_add] at hw ⊢
    rcases hw with ⟨xc, hxc, yc, hyc, rfl⟩
    have har : a • r ∈ cone (Set.range Y) := by
      exact IsCone.smul_mem' hr ha
    have hyc' : yc + a • r ∈ cone (Set.range Y) := add_mem hyc har
    exact ⟨xc, hxc, yc + a • r, hyc', by simp [add_assoc]⟩
  refine ⟨w + a • r, hw', l, hl, ?_⟩
  have hsum' := congrArg (fun t : Fin n → ℝ ↦ t + a • r) hsum
  simpa [add_assoc, add_left_comm, add_comm] using hsum'

/-- Helper for Theorem 3.37: an exposing functional is constant along every ambient lineality
direction through a face point. -/
lemma face_functional_vanishes_on_lineality_of_exposed_face
    (F : Set (Fin n → ℝ))
    (x0 c : Fin n → ℝ)
    (δ : ℝ)
    (P : Set (Fin n → ℝ))
    (hx0 : x0 ∈ F)
    (hF_eq : F = face_set P c δ)
    (hvalid : is_valid_inequality P c δ) :
    ∀ d : Fin n → ℝ, d ∈ linealitySpace P → c ⬝ᵥ d = 0 := by
  have hx0_face : x0 ∈ face_set P c δ := by
    simpa [hF_eq] using hx0
  have hx0P : x0 ∈ P := (mem_face_set_iff.mp hx0_face).1
  have hx0_eq : c ⬝ᵥ x0 = δ := (mem_face_set_iff.mp hx0_face).2
  intro d hd
  have hplus_mem : x0 + d ∈ P := by
    simpa using (mem_linealitySpace_iff.mp hd) hx0P (1 : ℝ)
  have hminus_mem : x0 - d ∈ P := by
    have hminus' : x0 + (-1 : ℝ) • d ∈ P := (mem_linealitySpace_iff.mp hd) hx0P (-1 : ℝ)
    simpa [sub_eq_add_neg] using hminus'
  have hplus_le : c ⬝ᵥ (x0 + d) ≤ δ := hvalid hplus_mem
  have hminus_le : c ⬝ᵥ (x0 - d) ≤ δ := hvalid hminus_mem
  have hplus_exp : c ⬝ᵥ (x0 + d) = δ + c ⬝ᵥ d := by
    simpa [dotProduct_add, hx0_eq]
  have hminus_exp : c ⬝ᵥ (x0 - d) = δ - c ⬝ᵥ d := by
    simpa [dotProduct_sub, hx0_eq]
  -- The valid inequality on both opposite lineality translates forces zero directional change.
  linarith [hplus_le, hminus_le, hplus_exp, hminus_exp]

/-- Theorem 3.37 (1) (Decomposition Theorem for Polyhedra). If `P ⊆ ℝ^n` is a
polyhedron, `minimalFaces` is a finite family of minimal faces of `P`, `recessionFaces` is a
finite family of exposed faces of `recessionCone P` of dimension
`Module.finrank ℝ (linealitySubmodule P) + 1`, and `v i`, `r i` are chosen representatives with
`v i ∈ minimalFaces i` and `r i ∈ recessionFaces i \ linealitySpace P`, then
`P = conv({v i}) + cone({r i}) + lin(P)`. -/
theorem polyhedron_eq_convexHull_add_cone_add_linealitySpace
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Set (Fin n → ℝ))
    (hP_polyhedron : is_polyhedron P)
    (minimalFaces : ι → Set (Fin n → ℝ))
    (recessionFaces : κ → Set (Fin n → ℝ))
    (v : ι → Fin n → ℝ)
    (r : κ → Fin n → ℝ)
    (h_minimalFaces : ∀ i : ι, IsMinimalFaceOf ℝ P (minimalFaces i))
    (h_all_minimalFaces :
      ∀ F : Set (Fin n → ℝ), IsMinimalFaceOf ℝ P F → ∃ i : ι, minimalFaces i = F)
    (h_recessionFaces_face :
      ∀ i : κ, IsExposed ℝ (recessionCone P) (recessionFaces i))
    (h_recessionFaces_dim :
      ∀ i : κ,
        Module.finrank ℝ (affineSpan ℝ (recessionFaces i)).direction =
          Module.finrank ℝ (linealitySubmodule P) + 1)
    (h_all_recessionFaces :
      ∀ R : Set (Fin n → ℝ),
        IsExposed ℝ (recessionCone P) R →
        Module.finrank ℝ (affineSpan ℝ R).direction =
          Module.finrank ℝ (linealitySubmodule P) + 1 →
          ∃ i : κ, recessionFaces i = R)
    (hv : ∀ i : ι, v i ∈ minimalFaces i)
    (hr : ∀ i : κ, r i ∈ recessionFaces i)
    (hr_not_mem_lineality : ∀ i : κ, r i ∉ linealitySpace P) :
    P = convexHull ℝ (Set.range v) + cone (Set.range r) + linealitySpace P := by
  -- TODO: the remaining source-faithful step is the pointed-slice construction from the plan:
  -- build a complement to `linealitySubmodule P`, obtain a pointed `convexHull + cone`
  -- representation on the slice via Theorem 3.13, and then transport the chosen minimal-face
  -- and recession-face representatives back through Theorem 3.33 and the recession-face analogue.
  sorry

/-- Theorem 3.37 (2). If `P ⊆ ℝ^n` admits a representation
`P = conv(X) + cone(Y) + lin(P)` with `cone(Y)` pointed, then every face of `P` of dimension
`Module.finrank ℝ (linealitySubmodule P)` contains one of the generators from `X`. -/
theorem generators_meet_every_lineality_dimension_face
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Set (Fin n → ℝ))
    (X : ι → Fin n → ℝ)
    (Y : κ → Fin n → ℝ)
    (h_repr :
      P = convexHull ℝ (Set.range X) + cone (Set.range Y) + linealitySpace P)
    (hY_pointed : is_pointed (cone (Set.range Y)))
    (F : Set (Fin n → ℝ))
    (hF_nonempty : F.Nonempty)
    (hF_face : IsExposed ℝ P F)
    (hF_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = Module.finrank ℝ (linealitySubmodule P)) :
    ∃ i : ι, X i ∈ F := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨x0, hx0F⟩ := hF_nonempty
  rcases hF_face.exists_eq_face_set_of_nonempty ⟨x0, hx0F⟩ with ⟨c, δ, hvalid, hF_eq⟩
  have hx0_eq : c ⬝ᵥ x0 = δ := by
    rw [hF_eq] at hx0F
    exact (mem_face_set_iff.mp hx0F).2
  have hlineality_zero :
      ∀ d : Fin n → ℝ, d ∈ linealitySpace P → c ⬝ᵥ d = 0 :=
    face_functional_vanishes_on_lineality_of_exposed_face
      F x0 c δ P hx0F hF_eq hvalid
  have hcone_subset :
      cone (Set.range Y) ⊆ recessionCone P :=
    cone_subset_recessionCone_of_repr P X Y h_repr
  have hx0P : x0 ∈ P := hF_face.subset hx0F
  rw [h_repr] at hx0P
  rw [Set.mem_add] at hx0P
  rcases hx0P with ⟨w, hw, l, hl, hx0_decomp₁⟩
  rw [Set.mem_add] at hw
  rcases hw with ⟨xc, hxc, yc, hyc, hw_eq⟩
  have hl_zero : c ⬝ᵥ l = 0 := hlineality_zero l hl
  have hyc_rec : yc ∈ recessionCone P := hcone_subset hyc
  have hyc_le : c ⬝ᵥ yc ≤ 0 := by
    -- A recession direction cannot increase the exposing functional beyond its face value.
    have hx0_plus : x0 + yc ∈ P := by
      simpa using (mem_recessionCone_iff.mp hyc_rec) (hF_face.subset hx0F) 1 zero_le_one
    have hvalid_plus : c ⬝ᵥ (x0 + yc) ≤ δ := hvalid hx0_plus
    have hplus_exp : c ⬝ᵥ (x0 + yc) = δ + c ⬝ᵥ yc := by
      simpa [dotProduct_add, hx0_eq]
    linarith [hvalid_plus, hplus_exp]
  have hxc_mem : xc ∈ P := by
    -- Each convex generator candidate is feasible because the other two summands contain `0`.
    rw [h_repr]
    refine Set.mem_add.mpr ?_
    refine ⟨xc, ?_, 0, zero_mem_linealitySpace, by simp⟩
    exact Set.mem_add.mpr ⟨xc, hxc, 0, cone_zero_mem, by simp⟩
  have hxc_le : c ⬝ᵥ xc ≤ δ := hvalid hxc_mem
  have hsum_eq : xc + yc + l = x0 := by
    calc
      xc + yc + l = w + l := by rw [hw_eq]
      _ = x0 := hx0_decomp₁
  have hdot_decomp : c ⬝ᵥ x0 = c ⬝ᵥ xc + c ⬝ᵥ yc + c ⬝ᵥ l := by
    -- Expand the exposing functional across the three representation summands.
    calc
      c ⬝ᵥ x0 = c ⬝ᵥ (xc + yc + l) := by
        rw [← hsum_eq]
      _ = c ⬝ᵥ xc + c ⬝ᵥ yc + c ⬝ᵥ l := by
        simp [dotProduct_add, add_assoc, add_left_comm, add_comm]
  have hxc_eq : c ⬝ᵥ xc = δ := by
    -- Since the recession and lineality parts contribute at most `0`, the convex part must
    -- already attain the exposed value.
    linarith [hx0_eq, hxc_le, hyc_le, hl_zero, hdot_decomp]
  rcases mem_convexHull_range_iff_exists_barycentric_weights_fintype.mp hxc with
    ⟨lam, hlam_nonneg, hlam_sum, hxc_repr⟩
  have hpos : ∃ i : ι, 0 < lam i := by
    by_contra hpos
    have hlam_zero : ∀ i : ι, lam i = 0 := by
      intro i
      have hnot_pos : ¬ 0 < lam i := by
        exact fun hi ↦ hpos ⟨i, hi⟩
      linarith [hlam_nonneg i]
    have : (∑ i : ι, lam i) = 0 := by
      simp [hlam_zero]
    linarith [hlam_sum, this]
  rcases hpos with ⟨i, hi_pos⟩
  have hX_mem : ∀ j : ι, X j ∈ P := by
    intro j
    -- Every listed convex generator is itself feasible in the represented polyhedron.
    have hrange_subset : Set.range X ⊆ convexHull ℝ (Set.range X) :=
      subset_convexHull ℝ (Set.range X)
    have hXj_conv : X j ∈ convexHull ℝ (Set.range X) := by
      exact hrange_subset (Set.mem_range_self j)
    rw [h_repr]
    refine Set.mem_add.mpr ?_
    refine ⟨X j, ?_, 0, zero_mem_linealitySpace, by simp⟩
    exact
      Set.mem_add.mpr
        ⟨X j, hXj_conv, 0, cone_zero_mem, by simp⟩
  have hXi_le : c ⬝ᵥ X i ≤ δ := hvalid (hX_mem i)
  have hweighted : δ = ∑ j : ι, lam j * (c ⬝ᵥ X j) := by
    -- Rewrite the exposed convex part as a barycentric combination of listed generators.
    calc
      δ = c ⬝ᵥ xc := hxc_eq.symm
      _ = c ⬝ᵥ ∑ j : ι, lam j • X j := by rw [hxc_repr]
      _ = ∑ j : ι, c ⬝ᵥ (lam j • X j) := by
            simpa using (dotProduct_sum c Finset.univ (fun j : ι ↦ lam j • X j))
      _ = ∑ j : ι, lam j * (c ⬝ᵥ X j) := by
            simp [dotProduct_smul]
  have hXi_eq : c ⬝ᵥ X i = δ := by
    by_contra hne
    have hlt : c ⬝ᵥ X i < δ := lt_of_le_of_ne hXi_le hne
    have hsum_lt :
        ∑ j : ι, lam j * (c ⬝ᵥ X j) < ∑ j : ι, lam j * δ := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro j hj
        exact mul_le_mul_of_nonneg_left (hvalid (hX_mem j)) (hlam_nonneg j)
      · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hlt hi_pos⟩
    have hsum_eq :
        ∑ j : ι, lam j * δ = δ := by
      calc
        ∑ j : ι, lam j * δ = (∑ j : ι, lam j) * δ := by
              rw [Finset.sum_mul]
        _ = δ := by
              rw [hlam_sum, one_mul]
    linarith [hweighted, hsum_lt, hsum_eq]
  refine ⟨i, ?_⟩
  -- The chosen generator is feasible and tight, hence it lies on the exposed face.
  rw [hF_eq]
  exact (mem_face_set_iff).2 ⟨hX_mem i, hXi_eq⟩

/-- Theorem 3.37 (3). If `P ⊆ ℝ^n` admits a representation
`P = conv(X) + cone(Y) + lin(P)` with `cone(Y)` pointed, then every exposed face of
`recessionCone P` of dimension `Module.finrank ℝ (linealitySubmodule P) + 1` contains a generator
from `Y` that is not in `linealitySpace P`. -/
theorem recession_generators_meet_every_lineality_succ_dimension_face
    {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Set (Fin n → ℝ))
    (X : ι → Fin n → ℝ)
    (Y : κ → Fin n → ℝ)
    (h_repr :
      P = convexHull ℝ (Set.range X) + cone (Set.range Y) + linealitySpace P)
    (hY_pointed : is_pointed (cone (Set.range Y)))
    (R : Set (Fin n → ℝ))
    (hR_face : IsExposed ℝ (recessionCone P) R)
    (hR_dim :
      Module.finrank ℝ (affineSpan ℝ R).direction =
        Module.finrank ℝ (linealitySubmodule P) + 1) :
    ∃ j : κ, Y j ∈ R ∧ Y j ∉ linealitySpace P := by
  -- TODO: the missing step is the recession-face analogue of the proved exposed-face argument:
  -- show every `r ∈ recessionCone P` decomposes as `r = y + l` with `y ∈ cone (Set.range Y)` and
  -- `l ∈ linealitySpace P`, then use the exposing functional on `R` to force one positive-support
  -- generator `Y j` into `R` and outside `linealitySpace P`.
  sorry

end Theorem337
