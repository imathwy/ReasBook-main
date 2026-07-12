import Mathlib
import StacksProject_2024.Chap05.Lemma_5_18_5
import StacksProject_2024.Chap10.Proposition_10_35_19
import StacksProject_2024.Chap10.Lemma_10_29_4
import StacksProject_2024.Chap10.Lemma_10_30_2
import StacksProject_2024.Chap10.Lemma_10_30_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Topology PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsJacobsonRing R]

local notation "R₀" => closedPoints (PrimeSpectrum R)
local notation "S₀" => closedPoints (PrimeSpectrum S)
local notation "ιR" => (Subtype.val : R₀ → PrimeSpectrum R)
local notation "ιS" => (Subtype.val : S₀ → PrimeSpectrum S)

/- Layering for this item:
* source-facing: the closed-point image statement for constructible subsets and the density
  criterion for membership in `comap f '' E`;
* core/canonical owner: `closedPoints`, `PrimeSpectrum.comap`, and the restricted map
  `PrimeSpectrum.comapClosedPoints`;
* bridge/view: `preimage_comap_image_eq_image_comapClosedPoints`, which rewrites the source-facing
  closed-point image statement in owner-level closed-point-subspace form.
-/

section

variable (f : R →+* S) (hf : f.FiniteType)
variable {E : Set (PrimeSpectrum S)}

local notation "E₀" => ιS ⁻¹' E
local notation "fE₀" => ιR '' (comapClosedPoints f hf '' E₀)

-- Proof sketch: start with a closed point of the constructible subspace `comap f '' E`;
-- finite type over the Jacobson ring `R` makes `S` Jacobson by Proposition `10.35.19 (1)`,
-- so Jacobsonity of the constructible subspace `E` produces a closed point of `E` above it, and
-- Proposition `10.35.19 (2)` packages the induced map on ambient closed points as
-- `PrimeSpectrum.comapClosedPoints`.
/-- Lemma 10.35.21 (1): for a finite type ring map `f : R →+* S` from a Jacobson ring and a
constructible subset `E ⊆ Spec(S)`, the closed points of `f(E)` are exactly the images, under the
canonical restricted map on closed points, of the closed points of `E`. -/
@[stacks 00GD]
theorem closedPoints_comap_image_eq_image_closedPoints
    (hE : IsConstructible E) :
    Subtype.val '' closedPoints (comap f '' E) = fE₀ := by
  letI : Algebra R S := f.toAlgebra
  have hf' : (algebraMap R S).FiniteType := by
    simpa [RingHom.algebraMap_toAlgebra] using hf
  letI : Algebra.FiniteType R S := (RingHom.finiteType_algebraMap).mp hf'
  letI : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R) (B := S)
  letI : JacobsonSpace E :=
    jacobsonSpace_subtype_of_isLocallyConstructible hE.isLocallyConstructible
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨x', hx', rfl⟩
    let g : E → comap f '' E := fun y ↦ ⟨comap f y.1, ⟨y.1, y.2, rfl⟩⟩
    have hg_cont : Continuous g := by
      exact ((continuous_comap f).comp continuous_subtype_val).subtype_mk _
    let F : Set E := g ⁻¹' ({x'} : Set (comap f '' E))
    have hF_nonempty : F.Nonempty := by
      rcases x'.2 with ⟨y, hyE, hyx⟩
      have hy_mem : g ⟨y, hyE⟩ = x' := by
        apply Subtype.ext
        simpa [g] using hyx
      refine ⟨⟨y, hyE⟩, ?_⟩
      simpa [F] using hy_mem
    have hF_loc : IsLocallyClosed F := by
      have hx'_closed : IsClosed ({x'} : Set (comap f '' E)) := by
        exact hx'
      exact (hx'_closed.preimage hg_cont).isLocallyClosed
    -- Choose a closed point of the closed fiber inside the Jacobson subspace `E`.
    obtain ⟨y, hyF, hyclosed⟩ := nonempty_inter_closedPoints hF_nonempty hF_loc
    have hy_closed_ambient :
        ((y : E) : PrimeSpectrum S) ∈ closedPoints (PrimeSpectrum S) := by
      exact
        (closedPoints_subset_preimage_closedPoints_of_isLocallyConstructible
          (T := E) hE.isLocallyConstructible) hyclosed
    let y₀ : S₀ := ⟨((y : E) : PrimeSpectrum S), hy_closed_ambient⟩
    refine ⟨comapClosedPoints f hf y₀, ?_, ?_⟩
    · refine ⟨y₀, ?_, rfl⟩
      simpa [y₀] using (y : E).2
    · have hy_eq : g y = x' := by
        simpa [F] using hyF
      have hy_eq' : comap f ((y : E) : PrimeSpectrum S) = (x' : PrimeSpectrum R) := by
        exact congrArg Subtype.val hy_eq
      simpa [PrimeSpectrum.val_comapClosedPoints] using hy_eq'
  · intro x hx
    rcases hx with ⟨x₀, hx₀, rfl⟩
    rcases hx₀ with ⟨y₀, hy₀E, rfl⟩
    let z : comap f '' E := ⟨comap f y₀, ⟨(y₀ : PrimeSpectrum S), hy₀E, rfl⟩⟩
    have hz_closed :
        z ∈ closedPoints (comap f '' E) := by
      have hz_ambient : (z : PrimeSpectrum R) ∈ closedPoints (PrimeSpectrum R) := by
        simpa [z, PrimeSpectrum.val_comapClosedPoints] using
          (show ((comapClosedPoints f hf y₀ : R₀) : PrimeSpectrum R) ∈
            closedPoints (PrimeSpectrum R) from (comapClosedPoints f hf y₀).2)
      exact
        (preimage_closedPoints_subset
          (f := (Subtype.val : comap f '' E → PrimeSpectrum R))
          Subtype.val_injective continuous_subtype_val) hz_ambient
    -- The image of a closed point of `E` is already closed in the image subspace.
    refine ⟨z, hz_closed, ?_⟩
    simpa [z, PrimeSpectrum.val_comapClosedPoints]

-- Proof sketch: Chevalley makes `comap f '' E` constructible, so Lemma `5.18.8` identifies the
-- closed points of the constructible subspace `comap f '' E` with the trace of `comap f '' E` on
-- `R₀`. The first theorem identifies those closed points with the image of the closed points of
-- `E`, and Proposition `10.35.19` packages the ambient map on closed points as
-- `PrimeSpectrum.comapClosedPoints`.
/-- Lemma 10.35.21 (1), owner-level bridge: tracing the constructible image `f(E)` to the
closed-point subspace of `Spec(R)` agrees with applying the restricted spectrum map on closed
points to the trace of `E` on the closed-point subspace of `Spec(S)`. -/
@[stacks 00GD]
theorem preimage_comap_image_eq_image_comapClosedPoints
    (hE : IsConstructible E) :
    ιR ⁻¹' (comap f '' E) = comapClosedPoints f hf '' E₀ := by
  apply Set.Subset.antisymm
  · intro x hx
    let z : comap f '' E := ⟨(x : PrimeSpectrum R), hx⟩
    have hz_closed : z ∈ closedPoints (comap f '' E) := by
      exact
        (preimage_closedPoints_subset
          (f := (Subtype.val : comap f '' E → PrimeSpectrum R))
          Subtype.val_injective continuous_subtype_val) x.2
    have hz_image :
        ((x : R₀) : PrimeSpectrum R) ∈ Subtype.val '' closedPoints (comap f '' E) := by
      exact ⟨z, hz_closed, rfl⟩
    rw [closedPoints_comap_image_eq_image_closedPoints f hf hE] at hz_image
    rcases hz_image with ⟨x', hx', hxEq⟩
    have hxx' : x = x' := Subtype.ext hxEq.symm
    simpa [hxx'] using hx'
  · intro x hx
    rcases hx with ⟨y, hyE, rfl⟩
    -- Read the closed-point witness directly in the ambient image.
    change comap f (y : PrimeSpectrum S) ∈ comap f '' E
    refine ⟨(y : PrimeSpectrum S), hyE, ?_⟩
    rfl

section

variable {ξ : PrimeSpectrum R}

local notation "Zξ" => closure (Set.singleton ξ : Set (PrimeSpectrum R))
local notation "ιξ" => (Subtype.val : Zξ → PrimeSpectrum R)

/-- Helper for Lemma 10.35.21: after quotienting by `ξ.asIdeal`, every closed point of
`closure {ξ}` coming from a closed point of `Spec(S)` already lies in the image of the quotient
spectrum map `Spec(S / ξS) → Spec(R / ξ)`. -/
lemma quotient_preimage_closed_trace_subset_range
    (f : R →+* S) (hf : f.FiniteType) :
    let p : Ideal R := ξ.asIdeal
    let pS : Ideal S := Ideal.map f p
    let φ : R ⧸ p →+* S ⧸ pS := Ideal.quotientMap pS f Ideal.le_comap_map
    let e : PrimeSpectrum (R ⧸ p) ≃ₜ Zξ :=
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p).trans
        (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
    e ⁻¹' (ιξ ⁻¹' (ιR '' (comapClosedPoints f hf '' (Set.univ : Set S₀)))) ⊆
      Set.range (PrimeSpectrum.comap φ) := by
  intro p pS φ e
  intro w hw
  rcases hw with ⟨x₀, hx₀, hxw⟩
  rcases hx₀ with ⟨y₀, -, rfl⟩
  have hp_le :
      p ≤ ((e w : Zξ) : PrimeSpectrum R).asIdeal := by
    change p ≤ Ideal.comap (Ideal.Quotient.mk p) w.asIdeal
    have hker :
        RingHom.ker (Ideal.Quotient.mk p) ≤ Ideal.comap (Ideal.Quotient.mk p) w.asIdeal := by
      rw [RingHom.ker_eq_comap_bot]
      exact Ideal.comap_mono bot_le
    simpa [Ideal.mk_ker] using hker
  have hp_le_comap :
      p ≤ Ideal.comap f (y₀ : PrimeSpectrum S).asIdeal := by
    have hξ_le' :
        p ≤ ((comapClosedPoints f hf y₀ : R₀) : PrimeSpectrum R).asIdeal := by
      exact hxw.symm ▸ hp_le
    simpa [PrimeSpectrum.val_comapClosedPoints, PrimeSpectrum.comap_asIdeal] using hξ_le'
  have hpS_le : pS ≤ (y₀ : PrimeSpectrum S).asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hp_le_comap
  let yV : V((pS : Set S)) :=
    ⟨(y₀ : PrimeSpectrum S), (mem_V pS (y₀ : PrimeSpectrum S)).2 hpS_le⟩
  let qbar : PrimeSpectrum (S ⧸ pS) :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus pS).symm yV
  refine ⟨qbar, ?_⟩
  apply e.injective
  apply Subtype.ext
  have hφ :
      φ.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk pS).comp f := by
    ext r
    rfl
  have hqbar :
      PrimeSpectrum.comap (Ideal.Quotient.mk pS) qbar = (y₀ : PrimeSpectrum S) := by
    exact congrArg Subtype.val
      ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus pS).apply_symm_apply yV)
  calc
    PrimeSpectrum.comap (Ideal.Quotient.mk p) (PrimeSpectrum.comap φ qbar)
        = PrimeSpectrum.comap (φ.comp (Ideal.Quotient.mk p)) qbar := by
          rw [PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap ((Ideal.Quotient.mk pS).comp f) qbar := by
          rw [hφ]
    _ = PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk pS) qbar) := by
          rw [← PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap f y₀ := by
          rw [hqbar]
    _ = ((e w : Zξ) : PrimeSpectrum R) := by
          simpa [PrimeSpectrum.val_comapClosedPoints] using hxw
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk p) w := by
          rfl

/-- Helper for Lemma 10.35.21: in the special case `E = Spec(S)`, density of the trace of the
image of ambient closed points on `closure {ξ}` forces `ξ` to lie in the image of `Spec(S)`. -/
lemma mem_range_comap_of_dense_closed_point_trace_univ
    (f : R →+* S) (hf : f.FiniteType)
    (hDense : Dense (ιξ ⁻¹' (ιR '' (comapClosedPoints f hf '' (Set.univ : Set S₀))))) :
    ξ ∈ comap f '' (Set.univ : Set (PrimeSpectrum S)) := by
  let p : Ideal R := ξ.asIdeal
  let pS : Ideal S := Ideal.map f p
  letI : IsDomain (R ⧸ p) := (Ideal.Quotient.isDomain_iff_prime (I := p)).2 ξ.isPrime
  let φ : R ⧸ p →+* S ⧸ pS := Ideal.quotientMap pS f Ideal.le_comap_map
  let e : PrimeSpectrum (R ⧸ p) ≃ₜ Zξ :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus p).trans
      (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
  have hDenseQuotient :
      Dense (e ⁻¹' (ιξ ⁻¹' (ιR '' (comapClosedPoints f hf '' (Set.univ : Set S₀))))) := by
    exact hDense.preimage e.isOpenMap
  have hsubset :
      e ⁻¹' (ιξ ⁻¹' (ιR '' (comapClosedPoints f hf '' (Set.univ : Set S₀)))) ⊆
        Set.range (PrimeSpectrum.comap φ) := by
    simpa [p, pS, φ, e] using quotient_preimage_closed_trace_subset_range
      (f := f) (hf := hf) (ξ := ξ)
  have hDenseRange : DenseRange (PrimeSpectrum.comap φ) :=
    Dense.mono hsubset hDenseQuotient
  have hbot :
      (⊥ : PrimeSpectrum (R ⧸ p)) ∈ Set.range (PrimeSpectrum.comap φ) := by
    exact ((ringHom_injective_tfae_of_image_contains_dense_set φ).out 1 2).1 hDenseRange
  rcases hbot with ⟨qbar, hqbar⟩
  refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk pS) qbar, by simp, ?_⟩
  have hφ :
      φ.comp (Ideal.Quotient.mk p) = (Ideal.Quotient.mk pS).comp f := by
    ext r
    rfl
  have hξ_bot :
      PrimeSpectrum.comap (Ideal.Quotient.mk p) (⊥ : PrimeSpectrum (R ⧸ p)) = ξ := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk p) (⊥ : Ideal (R ⧸ p)) = ξ.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  -- The quotient witness contracts to the zero prime, whose image under `Spec(R / ξ) → Spec(R)`
  -- is exactly `ξ`.
  calc
    PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk pS) qbar)
        = PrimeSpectrum.comap ((Ideal.Quotient.mk pS).comp f) qbar := by
          rw [← PrimeSpectrum.comap_comp_apply]
    _ = PrimeSpectrum.comap (φ.comp (Ideal.Quotient.mk p)) qbar := by
          rw [hφ.symm]
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk p) (PrimeSpectrum.comap φ qbar) := by
          rw [PrimeSpectrum.comap_comp_apply]
    _ = ξ := by
          rw [hqbar, hξ_bot]

-- Proof sketch: if `ξ ∈ f(E)`, Lemma `10.30.2` gives an open dense subset of `closure {ξ}`
-- contained in `f(E)`, and the owner-level bridge above identifies the closed points of that
-- constructible trace with the image of the closed-point trace of `E` under
-- `PrimeSpectrum.comapClosedPoints`. Conversely, write the constructible set `E` as the image of a
-- finitely presented map using Lemma `10.29.4`, reduce to the case `E = Spec(S)`, and apply Lemma
-- `10.30.4` to the induced map over the residue domain at `ξ`.
/-- If `ξ : Spec(R)` lies in the image of a constructible subset `E ⊆ Spec(S)`, then the trace of
`f(E_0)` on `closure {ξ}` is dense there; conversely, density of that trace characterizes
membership of `ξ` in `f(E)`. -/
theorem mem_comap_image_iff_dense_preimage_closedPoints
    (hE : IsConstructible E) :
    ξ ∈ comap f '' E ↔ Dense (ιξ ⁻¹' fE₀) := by
  constructor
  · intro hξ
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      exists_open_dense_subset_closure_singleton_of_mem_comap_image_constructible
        (f := f) (E := E) (ξ := ξ) hf hE hξ
    letI : JacobsonSpace Zξ :=
      JacobsonSpace.of_isClosedEmbedding isClosed_closure.isClosedEmbedding_subtypeVal
    have hDenseClosed : Dense ((U : Set Zξ) ∩ closedPoints Zξ) := by
      rw [dense_iff_closure_eq]
      calc
        closure ((U : Set Zξ) ∩ closedPoints Zξ) = closure (U : Set Zξ) := by
          simpa using
            (JacobsonSpace.closure_inter_closedPoints_eq_closure
              (S := (U : Set Zξ)) U.2.isLocallyClosed)
        _ = Set.univ := hU_dense.closure_eq
    have hsubset_trace :
        ((U : Set Zξ) ∩ closedPoints Zξ) ⊆ ιξ ⁻¹' fE₀ := by
      intro z hz
      have hzU : z ∈ (U : Set Zξ) := hz.1
      have hzclosed : z ∈ closedPoints Zξ := hz.2
      have hz_closed_ambient :
          ((z : Zξ) : PrimeSpectrum R) ∈ closedPoints (PrimeSpectrum R) := by
        have hzpre :
            z ∈ ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹'
              closedPoints (PrimeSpectrum R)) := by
          rw [isClosed_closure.isClosedEmbedding_subtypeVal.preimage_closedPoints]
          exact hzclosed
        simpa using hzpre
      let z₀ : R₀ := ⟨((z : Zξ) : PrimeSpectrum R), hz_closed_ambient⟩
      have hz_image : z₀ ∈ ιR ⁻¹' (comap f '' E) := by
        simpa using hU_subset hzU
      have hz_closed_image : z₀ ∈ comapClosedPoints f hf '' E₀ := by
        rw [preimage_comap_image_eq_image_comapClosedPoints f hf hE] at hz_image
        exact hz_image
      exact ⟨z₀, hz_closed_image, rfl⟩
    -- Dense closed points inside the dense open subset already lie in the desired trace.
    exact Dense.mono hsubset_trace hDenseClosed
  ·
    intro hDense
    obtain ⟨S', _, g, hg, hEeq⟩ :=
      exists_finitePresentation_comap_range_eq_of_isConstructible (R := S) (T := E) hE
    let f' : R →+* S' := g.comp f
    have hg_ft : g.FiniteType := RingHom.FiniteType.of_finitePresentation hg
    have hf' : f'.FiniteType := RingHom.FiniteType.comp hg_ft hf
    have himage :
        comap f '' E = comap f' '' (Set.univ : Set (PrimeSpectrum S')) := by
      rw [← hEeq]
      ext x
      constructor
      · rintro ⟨y, ⟨z, -, rfl⟩, rfl⟩
        refine ⟨z, by simp, ?_⟩
        simp [f', PrimeSpectrum.comap_comp_apply]
      · rintro ⟨z, -, rfl⟩
        refine ⟨PrimeSpectrum.comap g z, ?_, ?_⟩
        · simpa [hEeq] using (show PrimeSpectrum.comap g z ∈ Set.range (PrimeSpectrum.comap g) from
            ⟨z, rfl⟩)
        · simp [f', PrimeSpectrum.comap_comp_apply]
    have hclosedImage :
        fE₀ =
          ιR '' (comapClosedPoints f' hf' '' (Set.univ : Set (closedPoints (PrimeSpectrum S')))) := by
      calc
        fE₀ = Subtype.val '' closedPoints (comap f '' E) := by
          symm
          exact closedPoints_comap_image_eq_image_closedPoints (f := f) (hf := hf) hE
        _ = Subtype.val '' closedPoints (comap f' '' (Set.univ : Set (PrimeSpectrum S'))) := by
          rw [himage]
        _ =
            ιR '' (comapClosedPoints f' hf' '' (Set.univ : Set (closedPoints (PrimeSpectrum S')))) := by
          simpa using
            closedPoints_comap_image_eq_image_closedPoints
              (f := f') (hf := hf') (E := (Set.univ : Set (PrimeSpectrum S')))
              Topology.IsConstructible.univ
    have hDense' :
        Dense (ιξ ⁻¹'
          (ιR '' (comapClosedPoints f' hf' '' (Set.univ : Set (closedPoints (PrimeSpectrum S')))))) := by
      simpa [hclosedImage] using hDense
    have hξ_range :
        ξ ∈ comap f' '' (Set.univ : Set (PrimeSpectrum S')) :=
      mem_range_comap_of_dense_closed_point_trace_univ (f := f') (hf := hf') (ξ := ξ) hDense'
    rcases hξ_range with ⟨z, -, hz⟩
    refine ⟨PrimeSpectrum.comap g z, ?_, ?_⟩
    · simpa [hEeq] using (show PrimeSpectrum.comap g z ∈ Set.range (PrimeSpectrum.comap g) from
        ⟨z, rfl⟩)
    · simpa [f', PrimeSpectrum.comap_comp_apply] using hz

end

end

end
