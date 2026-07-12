import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap15.Definition_15_33_2
import StacksProject_2024.Chap15.Lemma_15_34_1_Cartier_equality
import StacksProject_2024.Chap15.Lemma_15_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u

namespace Algebra

namespace H1Cotangent

section

variable {F E : Type u}
variable [Field F] [Field E] [Algebra F E] [Algebra.FiniteType F E]

/-- Helper for Lemma 15.34.3: a directed family of subalgebras with supremum `⊤` captures every
finite subset of the ambient field at one stage. -/
private lemma exists_stage_subalgebra_contains_finset
    {ι : Type*} [Nonempty ι] (S : ι → Subalgebra F E) (hdir : Directed (· ≤ ·) S)
    (hSup : iSup S = ⊤)
    (s : Finset E) :
    ∃ i, (↑s : Set E) ⊆ S i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.choice ‹Nonempty ι›, ?_⟩
      simp
  | @insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      have ha_mem : a ∈ iSup S := by
        simpa [hSup] using (show a ∈ (⊤ : Subalgebra F E) from trivial)
      have ha_mem' : ∃ j, a ∈ S j := by
        change a ∈ ((iSup S : Subalgebra F E) : Set E) at ha_mem
        rw [Subalgebra.coe_iSup_of_directed hdir] at ha_mem
        simpa [Set.mem_iUnion] using ha_mem
      rcases ha_mem' with ⟨j, hj⟩
      rcases hdir i j with ⟨m, him, hjm⟩
      refine ⟨m, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, SetLike.mem_coe] at hx ⊢
      rcases hx with rfl | hx
      · exact hjm hj
      · exact him (hi hx)

/-- Helper for Lemma 15.34.3: a finite-type field algebra is itself a global complete
intersection. -/
private lemma global_complete_intersection_of_finiteType_field :
    IsGlobalCompleteIntersection F E := by
  classical
  obtain ⟨ι, S, hdir, hGCI, hSup⟩ :=
    exists_directed_globalCompleteIntersection_subalgebra_family (k := F) (K := E)
  by_cases hne : Nonempty ι
  · let _ : Nonempty ι := hne
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := F) (A := E)
    rcases exists_stage_subalgebra_contains_finset (F := F) (E := E) S hdir hSup s with
      ⟨i, hi⟩
    -- Once one stage contains a finite generating set of the field, that stage is already `⊤`.
    have hle : Algebra.adjoin F (↑s : Set E) ≤ S i := by
      refine Algebra.adjoin_le ?_
      intro x hx
      exact hi hx
    have htop_le : (⊤ : Subalgebra F E) ≤ S i := by
      simpa [hs] using hle
    have htop : S i = ⊤ := top_le_iff.mp htop_le
    exact IsGlobalCompleteIntersection.of_algEquiv (hGCI i) <|
      (Subalgebra.equivOfEq (S i) ⊤ htop).trans (Subalgebra.topEquiv (R := F) (A := E))
  · let _ : IsEmpty ι := not_nonempty_iff.mp hne
    have hbot : iSup S = (⊥ : Subalgebra F E) := by
      simp
    -- In the empty-family case, `⊤ = ⊥`, so the algebra map is surjective and the empty
    -- presentation already describes the field extension.
    have hsurj : Function.Surjective (algebraMap F E) := by
      intro x
      have htopbot : (⊤ : Subalgebra F E) = ⊥ := hSup.symm.trans hbot
      have hx : x ∈ (⊥ : Subalgebra F E) := by
        rw [← htopbot]
        trivial
      change ∃ y : F, algebraMap F E y = x at hx
      exact hx
    let e0 : Fin 0 ≃ PEmpty.{1} :=
      { toFun := Fin.elim0
        invFun := PEmpty.elim
        left_inv := fun i ↦ Fin.elim0 i
        right_inv := fun x : PEmpty.{1} ↦ PEmpty.elim x }
    let P : Algebra.Presentation F E (Fin 0) (Fin 0) :=
      (Algebra.Presentation.ofBijectiveAlgebraMap (R := F) (S := E)
          ⟨(algebraMap F E).injective, hsurj⟩).reindex e0 e0
    refine
      { presentation_or_subsingleton := Or.inr ⟨0, 0, P, ?_⟩ }
    have hPdim : P.dimension = 0 := by
      simp [P, Algebra.Presentation.ofBijectiveAlgebraMap_dimension]
    rw [hPdim]
    exact ringKrullDim_eq_zero_of_field E

/-- Helper for Lemma 15.34.3: extract a finite presentation from the global-complete-intersection
description of a finitely generated field extension. -/
private lemma exists_gci_presentation_of_field :
    ∃ (n c : ℕ) (P : Algebra.Presentation F E (Fin n) (Fin c)),
      ringKrullDim E = P.dimension := by
  let hE : IsGlobalCompleteIntersection F E :=
    global_complete_intersection_of_finiteType_field (F := F) (E := E)
  -- Over a field target, the presentation branch is the only possible branch of the dichotomy.
  rcases hE.presentation_or_subsingleton with hsub | ⟨n, c, P, hP⟩
  · exfalso
    exact one_ne_zero (Subsingleton.elim (1 : E) 0)
  · exact ⟨n, c, P, hP⟩

/-- Helper for Lemma 15.34.3: over a field base, every residue field is canonically identified
with the base field itself. -/
private noncomputable def field_prime_residueField_algEquiv_self (p : PrimeSpectrum F) :
    p.asIdeal.ResidueField ≃ₐ[F] F := by
  let φ : F →ₐ[F] p.asIdeal.ResidueField := IsScalarTower.toAlgHom F F p.asIdeal.ResidueField
  have hκ : Function.Bijective φ := by
    constructor
    · exact RingHom.injective _
    · simpa using (Ideal.algebraMap_residueField_surjective p.asIdeal)
  exact (AlgEquiv.ofBijective φ hκ).symm

/-- Helper for Lemma 15.34.3: every fiber of a field extension over a prime of the base field is
canonically another copy of the target field. -/
private noncomputable def field_prime_fiber_algEquiv_self (p : PrimeSpectrum F) :
    p.asIdeal.Fiber E ≃ₐ[F] E :=
  (Algebra.TensorProduct.congr
      (field_prime_residueField_algEquiv_self (F := F) p)
      (AlgEquiv.refl : E ≃ₐ[F] E)).trans
    (Algebra.TensorProduct.lid F E)

/-- Helper for Lemma 15.34.3: the fibers of `E / F` over primes of the base field have the same
Krull dimension as `E` itself. -/
private lemma ringKrullDim_field_fiber_eq (p : PrimeSpectrum F) :
    ringKrullDim (p.asIdeal.Fiber E) = ringKrullDim E := by
  -- The source proof compares every fiber with the unique field target before invoking any
  -- relative complete-intersection owner.
  simpa using
    ringKrullDim_eq_of_ringEquiv
      (field_prime_fiber_algEquiv_self (F := F) (E := E) p).toRingEquiv

/-- Helper for Lemma 15.34.3: a presentation of a finitely generated field extension whose
dimension matches `ringKrullDim E` is automatically a relative global complete intersection
presentation. -/
private lemma presentation_isRelativeGlobalCompleteIntersection_of_field
    {n c : ℕ} (P : Algebra.Presentation F E (Fin n) (Fin c))
    (hP : ringKrullDim E = P.dimension) :
    P.IsRelativeGlobalCompleteIntersection := by
  intro p hp
  -- Over a field base, the fiber dimension statement is exactly the global dimension statement.
  calc
    ringKrullDim (p.asIdeal.Fiber E) = ringKrullDim E :=
      ringKrullDim_field_fiber_eq (F := F) (E := E) p
    _ = P.dimension := hP

/-- Helper for Lemma 15.34.3: once the chosen field presentation has a Koszul-regular kernel in
the canonical `algebraMap` algebra structure, it packages directly into the Chapter 15 local
complete-intersection owner. -/
private theorem canonical_presentation_packages_lci
    (h :
      let _ : Algebra F E := (algebraMap F E).toAlgebra
      ∃ (n c : ℕ) (P : Algebra.Presentation F E (Fin n) (Fin c)),
        P.ker.IsKoszulRegularIdeal) :
    RingHom.IsLocalCompleteIntersection (algebraMap F E) := by
  refine RingHom.IsLocalCompleteIntersection.mk ?_
  let _ : Algebra F E := (algebraMap F E).toAlgebra
  -- Package the chosen polynomial presentation into the generator-based Chapter 15 owner.
  rcases h with ⟨n, c, P, hker⟩
  refine ⟨n, P.toGenerators, ?_⟩
  simpa using hker

/-- Helper for Lemma 15.34.3: a finitely generated field extension is a local complete
intersection ring map in the Chapter 15 ring-hom sense. -/
theorem fieldExtension_isLocalCompleteIntersection :
    RingHom.IsLocalCompleteIntersection (algebraMap F E) := by
  let _ : IsGlobalCompleteIntersection F E :=
    global_complete_intersection_of_finiteType_field (F := F) (E := E)
  -- Route correction: avoid the broken upstream `15.33.4` import chain and reuse the earlier
  -- Chapter 15 bridge from field global complete intersections to the ring-hom owner.
  exact
    globalCompleteIntersection_packages_ringHom_isLocalCompleteIntersection
      (L := F) (A := E)

/-- Helper for Lemma 15.34.3: the conormal module of a finite presentation of a field is
finite-dimensional over the target field. -/
private lemma presentationCotangent_finiteDimensional
    {n c : ℕ} (P : Algebra.Presentation F E (Fin n) (Fin c)) :
    FiniteDimensional E P.toExtension.Cotangent := by
  let _ : Module.Finite E P.toExtension.Cotangent := Extension.Cotangent.finite P.fg_ker
  exact (Module.Free.chooseBasis E P.toExtension.Cotangent).finiteDimensional_of_finite

/-- For a finitely generated field extension `E / F`, the first cotangent homology
`H¹(L_{E/F})` is finite-dimensional over `E`. -/
theorem finiteDimensional_of_finiteType_fieldExtension :
    FiniteDimensional E (H1Cotangent F E) := by
  obtain ⟨n, c, P, _hP⟩ := exists_gci_presentation_of_field (F := F) (E := E)
  let _ : FiniteDimensional E P.toExtension.Cotangent :=
    presentationCotangent_finiteDimensional (F := F) (E := E) P
  -- The presentation-level `H¹` term embeds into the finite-dimensional conormal module.
  let _ : FiniteDimensional E P.toExtension.H1Cotangent :=
    FiniteDimensional.of_injective P.toExtension.h1Cotangentι
      P.toExtension.h1Cotangentι_injective
  -- Transport finite dimensionality across the canonical comparison with `H1Cotangent F E`.
  exact FiniteDimensional.of_injective P.equivH1Cotangent.symm.toLinearMap
    P.equivH1Cotangent.symm.injective

end

end H1Cotangent

end Algebra

namespace KaehlerDifferential

section

variable {k k' K K' : Type u}
variable [Field k] [Field k'] [Field K] [Field K']
variable [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
variable [IsScalarTower k k' K'] [IsScalarTower k K K']
variable [Algebra.FiniteType k k'] [Algebra.FiniteType K K']

variable (k k' K K')

/-- Helper for Lemma 15.34.3: a finite module over a field is finite-dimensional. -/
private theorem finiteDimensional_of_moduleFinite
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V] [Module.Finite F V] :
    FiniteDimensional F V := by
  -- Over a field, the standard basis construction turns finite generation into finite dimension.
  exact (Module.Free.chooseBasis F V).finiteDimensional_of_finite

/-- Helper for Lemma 15.34.3: in an exact sequence `U → V → W`, if the left and right terms are
finite-dimensional and the right map is surjective, then the middle term is finite-dimensional. -/
private theorem finiteDimensional_middle_of_exact_of_surjective
    {F : Type u} [Field F]
    {U V W : Type u}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (f : U →ₗ[F] V) (g : V →ₗ[F] W)
    (hExact : Function.Exact f g)
    (hg : Function.Surjective g) :
    FiniteDimensional F V := by
  -- Exactness identifies the kernel of `g` with the finite-dimensional image of `f`.
  have hker : FiniteDimensional F (LinearMap.ker g) := by
    have hEq : LinearMap.ker g = LinearMap.range f := hExact.linearMap_ker_eq
    exact hEq ▸ (inferInstance : FiniteDimensional F (LinearMap.range f))
  -- Split the surjection `g`; the middle term is generated by a copy of `ker g` and a section of
  -- the finite-dimensional right term.
  obtain ⟨s, hs⟩ :=
    LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.2 hg)
  let p : LinearMap.ker g × W →ₗ[F] V :=
    { toFun := fun x ↦ x.1 + s x.2
      map_add' := by
        intro x y
        simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a x
        simp [smul_add] }
  have hp : Function.Surjective p := by
    intro v
    have hs_apply : g (s (g v)) = g v := by
      simpa using LinearMap.congr_fun hs (g v)
    have hk : g (v - s (g v)) = 0 := by
      rw [map_sub, hs_apply, sub_self]
    refine ⟨⟨⟨v - s (g v), hk⟩, g v⟩, ?_⟩
    simp [p]
  let _ : FiniteDimensional F (LinearMap.ker g × W) := by
    infer_instance
  exact FiniteDimensional.of_surjective p hp

/-- The canonical comparison map
`K' ⊗[K] Ω[K⁄k] → Ω[K'⁄k']` induced by the commutative square of field extensions. -/
noncomputable abbrev baseFieldComparison :
    K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] :=
  (KaehlerDifferential.map k k' K' K').comp (KaehlerDifferential.mapBaseChange k K K')

/-- Helper for Lemma 15.34.3: an element of the kernel of a composite map satisfies the expected
equation after forgetting the subtype wrapper. -/
private theorem composite_ker_equation
    {F : Type u} [Field F]
    {V W X : Type u}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [AddCommGroup X] [Module F X]
    (ε₂ : V →ₗ[F] W) (ζ₁ : W →ₗ[F] X)
    (x : LinearMap.ker (ζ₁.comp ε₂)) :
    ζ₁ (ε₂ x.1) = 0 := by
  -- Forgetting the subtype turns membership in the kernel of the composite into the displayed
  -- equation in the ambient codomain.
  change (ζ₁.comp ε₂) x.1 = 0
  exact x.2

-- Proof sketch: compare the two Jacobi-Zariski exact sequences for
-- `k ⊆ k' ⊆ K'` and `k ⊆ K ⊆ K'`. The kernel and cokernel identify with subquotients of the
-- finite-dimensional vector spaces `Ω[k'⁄k]` and `Ω[K'⁄K]`, whose finite dimensionality comes
-- from Cartier's equality.
/-- The kernel of the comparison map on Kähler differentials is finite-dimensional over `K'`. -/
theorem finiteDimensional_ker_baseFieldComparison :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := by
  let ε₁ : K' ⊗[k'] Ω[k'⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k k' K'
  let ε₂ : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k K K'
  let ζ₁ : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.map k k' K' K'
  let α : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] := baseFieldComparison k k' K K'
  let δ₂ : Algebra.H1Cotangent K K' →ₗ[K'] K' ⊗[K] Ω[K⁄k] := Algebra.H1Cotangent.δ k K K'
  have hα : α = ζ₁.comp ε₂ := by
    -- This is the defining factorization of the comparison map through `Ω[K'⁄k]`.
    rfl
  have hExact₁ : Function.Exact ε₁ ζ₁ := by
    -- The upper Jacobi-Zariski row for `k ⊆ k' ⊆ K'` identifies `range ε₁` with `ker ζ₁`.
    simpa [ε₁, ζ₁] using KaehlerDifferential.exact_mapBaseChange_map k k' K'
  have hExact₂ : Function.Exact δ₂ ε₂ := by
    -- The lower Jacobi-Zariski row for `k ⊆ K ⊆ K'` identifies `ker ε₂` with `range δ₂`.
    simpa [δ₂, ε₂] using Algebra.H1Cotangent.exact_δ_mapBaseChange k K K'
  let I : Submodule K' Ω[K'⁄k] := LinearMap.range ε₁ ⊓ LinearMap.range ε₂
  let f : LinearMap.ker ε₂ →ₗ[K'] LinearMap.ker α :=
    { toFun := fun x ↦
        ⟨x.1, by
          -- Vanishing under `ε₂` implies vanishing under the composite `α = ζ₁ ∘ ε₂`.
          have hx0 : ε₂ x.1 = 0 := by
            simpa using x.2
          simpa [hα, LinearMap.comp_apply, hx0]⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  let g : LinearMap.ker α →ₗ[K'] I :=
    { toFun := fun x ↦ by
        let x' : LinearMap.ker (ζ₁.comp ε₂) := ⟨x.1, by
          have hx0 : α x.1 = 0 := by
            simpa using x.2
          simpa [hα, LinearMap.comp_apply] using hx0⟩
        have hxcomp : ζ₁ (ε₂ x.1) = 0 := composite_ker_equation ε₂ ζ₁ x'
        have hxker : ε₂ x.1 ∈ LinearMap.ker ζ₁ := by
          -- The transport helper keeps the subtype coercions out of the exactness argument.
          change ζ₁ (ε₂ x.1) = 0
          exact hxcomp
        have hxleft : ε₂ x.1 ∈ LinearMap.range ε₁ := by
          -- Exactness in the upper row turns the kernel condition into membership in `range ε₁`.
          rw [hExact₁.linearMap_ker_eq] at hxker
          exact hxker
        refine ⟨ε₂ x.1, ?_⟩
        exact ⟨hxleft, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change ε₂ ((x + y : LinearMap.ker α).1) = ε₂ x.1 + ε₂ y.1
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        change ε₂ ((a • x : LinearMap.ker α).1) = a • ε₂ x.1
        simp }
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      -- If the intersection term vanishes, then `x` already lies in `ker ε₂`, hence comes from
      -- the left exact endpoint.
      refine ⟨⟨x.1, ?_⟩, ?_⟩
      · change ε₂ x.1 = 0
        exact congrArg Subtype.val hx
      · apply Subtype.ext
        rfl
    · rintro ⟨y, rfl⟩
      -- Conversely, the defining equation of `ker ε₂` makes the intersection term zero.
      apply Subtype.ext
      change ε₂ y.1 = 0
      exact y.2
  have hg : Function.Surjective g := by
    intro z
    rcases z.2.2 with ⟨x, hx⟩
    have hzker : z.1 ∈ LinearMap.ker ζ₁ := by
      -- Membership in the upper intersection term means exactly that the representative comes
      -- from `range ε₁ = ker ζ₁`.
      rw [hExact₁.linearMap_ker_eq]
      exact z.2.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · -- Route correction: instead of transporting directly through `ker α`, first rewrite the
      -- representative inside `Ω[K'⁄k]`, then use `range ε₁ = ker ζ₁`.
      change α x = 0
      rw [hα, LinearMap.comp_apply, hx]
      exact hzker
    · apply Subtype.ext
      exact hx
  have hfdInf : FiniteDimensional K' I := by
    let _ : FiniteDimensional k' Ω[k'⁄k] :=
      finiteDimensional_of_moduleFinite (F := k') (V := Ω[k'⁄k])
    let _ : FiniteDimensional K' (K' ⊗[k'] Ω[k'⁄k]) := by
      infer_instance
    have hfdRangeε₁ : FiniteDimensional K' (LinearMap.range ε₁) := by
      infer_instance
    -- The shared intersection term is a submodule of the finite-dimensional range of `ε₁`.
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (show I ≤ LinearMap.range ε₁ from by
        dsimp [I]
        exact inf_le_left))
      (Submodule.inclusion_injective (show I ≤ LinearMap.range ε₁ from by
        dsimp [I]
        exact inf_le_left))
  let _ : FiniteDimensional K' I := hfdInf
  have hfdH1 : FiniteDimensional K' (Algebra.H1Cotangent K K') :=
    Algebra.H1Cotangent.finiteDimensional_of_finiteType_fieldExtension (F := K) (E := K')
  have hfdKerε₂ : FiniteDimensional K' (LinearMap.ker ε₂) := by
    -- Route correction: instead of searching for a direct finite-dimensionality instance on
    -- `ker ε₂`, rewrite it as `range δ₂` and use the finite-dimensional left endpoint.
    have hEq : LinearMap.ker ε₂ = LinearMap.range δ₂ := hExact₂.linearMap_ker_eq
    have hfdRangeδ₂ : FiniteDimensional K' (LinearMap.range δ₂) := by
      let _ : FiniteDimensional K' (Algebra.H1Cotangent K K') := hfdH1
      infer_instance
    exact hEq ▸ hfdRangeδ₂
  let _ : FiniteDimensional K' (LinearMap.ker ε₂) := hfdKerε₂
  exact finiteDimensional_middle_of_exact_of_surjective f g hfg hg

-- Proof sketch: use the same pair of Jacobi-Zariski exact sequences as for the kernel statement.
-- The cokernel is a quotient of a finite-dimensional term in those exact sequences, so it is
-- finite-dimensional.
/-- The cokernel of the comparison map on Kähler differentials is finite-dimensional over `K'`. -/
theorem finiteDimensional_cokernel_baseFieldComparison :
    FiniteDimensional K' (Ω[K'⁄k'] ⧸ LinearMap.range (baseFieldComparison k k' K K')) := by
  let αK : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k K K'
  let αK' : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄K] := KaehlerDifferential.map k K K' K'
  let αk : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.map k k' K' K'
  let α : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] := baseFieldComparison k k' K K'
  have hα : α = αk.comp αK := by
    -- This is the defining factorization of the comparison map.
    rfl
  have hExactK : Function.Exact αK αK' := by
    simpa [αK, αK'] using KaehlerDifferential.exact_mapBaseChange_map k K K'
  have hEq :
      LinearMap.range αK = LinearMap.ker αK' := by
    simpa using hExactK.linearMap_ker_eq.symm
  have hSurjK : Function.Surjective αK' := by
    simpa [αK'] using KaehlerDifferential.map_surjective k K K'
  have hCokerαK :
      FiniteDimensional K' (Ω[K'⁄k] ⧸ LinearMap.range αK) := by
    let e :
        (Ω[K'⁄k] ⧸ LinearMap.range αK) ≃ₗ[K'] Ω[K'⁄K] :=
      (Submodule.quotEquivOfEq
        (p := LinearMap.range αK) (p' := LinearMap.ker αK') hEq).trans
        (LinearMap.quotKerEquivOfSurjective αK' hSurjK)
    have hOmegafd : FiniteDimensional K' Ω[K'⁄K] :=
      finiteDimensional_of_moduleFinite (F := K') (V := Ω[K'⁄K])
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  let φ : (Ω[K'⁄k] ⧸ LinearMap.range αK) →ₗ[K'] Ω[K'⁄k'] ⧸ LinearMap.range α :=
    (LinearMap.range αK).liftQ
      ((LinearMap.range α).mkQ.comp αk)
      (by
        intro x hx
        rcases hx with ⟨y, rfl⟩
        -- The image of `range αK` lands in `range α` after applying `αk`.
        simp [α, hα, LinearMap.comp_apply])
  have hφsurj : Function.Surjective φ := by
    -- Surjectivity of `αk` lets us lift every cokernel class through the quotient by `range αK`.
    intro z
    refine Quotient.inductionOn z ?_
    intro y
    obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective k k' K' y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rfl
  exact FiniteDimensional.of_surjective φ hφsurj

end

end KaehlerDifferential

namespace Algebra

section

variable {k k' K K' : Type u}
variable [Field k] [Field k'] [Field K] [Field K']
variable [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
variable [IsScalarTower k k' K'] [IsScalarTower k K K']
variable [Algebra.FiniteType k k'] [Algebra.FiniteType K K']

/- The source proof ends with an alternating-dimension computation on exact rows. The helper below
packages the linear-algebra part of that computation for a single two-term complex, so the
remaining blocker stays focused on the Jacobi-Zariski comparison itself. -/
/-- Helper for Lemma 15.34.3: for a linear map between finite-dimensional vector spaces, the
kernel-cokernel Euler characteristic is the source dimension minus the target dimension. -/
private theorem finrank_ker_sub_finrank_cokernel_eq_finrank_source_sub_finrank_target
    {F : Type u} [Field F]
    {V W : Type u}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (f : V →ₗ[F] W) :
    Int.ofNat (Module.finrank F (LinearMap.ker f)) -
      Int.ofNat (Module.finrank F (W ⧸ LinearMap.range f)) =
        Int.ofNat (Module.finrank F V) - Int.ofNat (Module.finrank F W) := by
  have hdom :
      Module.finrank F (LinearMap.ker f) + Module.finrank F (LinearMap.range f) =
        Module.finrank F V := by
    -- The source splits into the kernel and a complementary copy of the image.
    simpa [add_comm] using LinearMap.finrank_range_add_finrank_ker f
  have hcod :
      Module.finrank F (W ⧸ LinearMap.range f) + Module.finrank F (LinearMap.range f) =
        Module.finrank F W := by
    -- The quotient by the image measures exactly the missing codimension in the target.
    simpa [add_comm] using Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F V - Module.finrank F (LinearMap.range f) := by
    omega
  have hcoker :
      Module.finrank F (W ⧸ LinearMap.range f) =
        Module.finrank F W - Module.finrank F (LinearMap.range f) := by
    omega
  -- Cancelling the shared image dimension leaves the advertised Euler characteristic identity.
  rw [hker, hcoker]
  omega

/-- Helper for Lemma 15.34.3: a six-term exact row with injective left edge and surjective right
edge has the expected alternating finrank identity. -/
private theorem alternating_finrank_of_six_term_exact_row
    {F : Type u} [Field F]
    {A₀ A₁ A₂ A₃ A₄ A₅ : Type u}
    [AddCommGroup A₀] [Module F A₀] [FiniteDimensional F A₀]
    [AddCommGroup A₁] [Module F A₁] [FiniteDimensional F A₁]
    [AddCommGroup A₂] [Module F A₂] [FiniteDimensional F A₂]
    [AddCommGroup A₃] [Module F A₃] [FiniteDimensional F A₃]
    [AddCommGroup A₄] [Module F A₄] [FiniteDimensional F A₄]
    [AddCommGroup A₅] [Module F A₅] [FiniteDimensional F A₅]
    (f₀ : A₀ →ₗ[F] A₁) (f₁ : A₁ →ₗ[F] A₂) (f₂ : A₂ →ₗ[F] A₃)
    (f₃ : A₃ →ₗ[F] A₄) (f₄ : A₄ →ₗ[F] A₅)
    (hf₀ : Function.Injective f₀)
    (h₀₁ : Function.Exact f₀ f₁) (h₁₂ : Function.Exact f₁ f₂)
    (h₂₃ : Function.Exact f₂ f₃) (h₃₄ : Function.Exact f₃ f₄)
    (hf₄ : Function.Surjective f₄) :
    Int.ofNat (Module.finrank F A₁) - Int.ofNat (Module.finrank F A₂) +
        Int.ofNat (Module.finrank F A₃) - Int.ofNat (Module.finrank F A₄) =
      Int.ofNat (Module.finrank F A₀) - Int.ofNat (Module.finrank F A₅) := by
  have hA₁ :
      Module.finrank F A₁ =
        Module.finrank F A₀ + Module.finrank F (LinearMap.range f₁) := by
    have hker :
        Module.finrank F (LinearMap.ker f₁) = Module.finrank F A₀ := by
      let e : A₀ ≃ₗ[F] LinearMap.range f₀ := LinearEquiv.ofInjective f₀ hf₀
      calc
        Module.finrank F (LinearMap.ker f₁) = Module.finrank F (LinearMap.range f₀) := by
          rw [h₀₁.linearMap_ker_eq]
        _ = Module.finrank F A₀ := by
          simpa using (LinearEquiv.finrank_eq e).symm
    have hrank := LinearMap.finrank_range_add_finrank_ker f₁
    rw [hker] at hrank
    simpa [add_comm] using hrank.symm
  have hA₂ :
      Module.finrank F A₂ =
        Module.finrank F (LinearMap.range f₁) + Module.finrank F (LinearMap.range f₂) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker f₂
    rw [h₁₂.linearMap_ker_eq] at hrank
    simpa [add_comm] using hrank.symm
  have hA₃ :
      Module.finrank F A₃ =
        Module.finrank F (LinearMap.range f₂) + Module.finrank F (LinearMap.range f₃) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker f₃
    rw [h₂₃.linearMap_ker_eq] at hrank
    simpa [add_comm] using hrank.symm
  have hA₄ :
      Module.finrank F A₄ =
        Module.finrank F (LinearMap.range f₃) + Module.finrank F A₅ := by
    have hrange :
        Module.finrank F (LinearMap.range f₄) = Module.finrank F A₅ := by
      have htop : LinearMap.range f₄ = ⊤ := LinearMap.range_eq_top.2 hf₄
      calc
        Module.finrank F (LinearMap.range f₄) = Module.finrank F (⊤ : Submodule F A₅) := by
          rw [htop]
        _ = Module.finrank F A₅ := by simp
    have hrank := LinearMap.finrank_range_add_finrank_ker f₄
    rw [h₃₄.linearMap_ker_eq, hrange] at hrank
    simpa [add_comm] using hrank.symm
  -- The four short rank formulas telescope to the endpoint identity.
  omega

/- Domain triage:
* primary domain: Kähler differentials and first cotangent homology for a commutative square of
  finitely generated field extensions;
* sampled owner declarations:
  - `KaehlerDifferential.mapBaseChange`,
  - `KaehlerDifferential.map`,
  - `H1Cotangent.map`,
  - `H1Cotangent.exact_map_δ`,
  - `field_jacobi_zariski_left_injective`;
* best owner abstraction: the primitive data are the two canonical comparison maps obtained by
  composing the owner maps on `Ω` and `H1Cotangent`; kernel/cokernel finite-dimensionality and the
  Euler-characteristic identity are derived API;
* layer triage:
  - `source-facing`: the Euler-characteristic formula for this square of field extensions;
  - `core/canonical`: the owner maps on `Ω` and `H1Cotangent`, together with the Jacobi-Zariski
    exactness theorems from the Jacobi-Zariski sequence;
  - `bridge/view`: the two named comparison composites below.

The public surface should therefore speak directly in terms of these canonical comparison maps and
their kernels, ranges, and finranks, rather than re-expanding rank computations on the same owner
data.
-/

namespace H1Cotangent

variable (k k' K K')

/-- The canonical comparison map
`K' ⊗[K] H1Cotangent k K → H1Cotangent k' K'` induced by extension of scalars from `K` to `K'`
followed by change of base field from `k` to `k'`. -/
noncomputable abbrev baseFieldComparison :
    K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k' K' :=
  (H1Cotangent.map k k' K' K').comp
    (LinearMap.liftBaseChange K' (H1Cotangent.map k k K K'))

/-- Helper for Lemma 15.34.3: the source of the cotangent-homology base-field comparison is
finite-dimensional over `K'` once the intermediate field extension `K / k` is also finite type.
This extra hypothesis is not available in Lemma `15.34.3` itself, so the theorem is only an
auxiliary specialization and not part of the main source-proof route. -/
private theorem finiteDimensional_baseFieldComparison_source
    [Algebra.FiniteType k K] :
    FiniteDimensional K' (K' ⊗[K] H1Cotangent k K) := by
  -- First control `H₁(L_{K/k})` over `K`, then extend scalars along the field extension `K → K'`.
  let _ : FiniteDimensional K (H1Cotangent k K) :=
    finiteDimensional_of_finiteType_fieldExtension (F := k) (E := K)
  infer_instance

/-- Helper for Lemma 15.34.3: the target of the cotangent-homology base-field comparison is
finite-dimensional over `K'`. -/
private theorem finiteDimensional_baseFieldComparison_target :
    FiniteDimensional K' (H1Cotangent k' K') := by
  -- The target is another finitely generated field extension, so the field case of Cartier's
  -- equality already gives finite dimensionality.
  exact finiteDimensional_of_finiteType_fieldExtension (F := k') (E := K')

/-- Helper for Lemma 15.34.3: the upper Jacobi-Zariski change-of-source map
`H₁(L_{K'/k}) → H₁(L_{K'/k'})` has finite-dimensional kernel because the chosen finite local
complete-intersection presentation of `K' / k'` supplies the left-extended exact row. -/
private theorem finiteDimensional_ker_sourceChange_h1_map :
    FiniteDimensional K' (LinearMap.ker (H1Cotangent.map k k' K' K')) := by
  let P : Generators k k' k' := Generators.self k k'
  let hLci : RingHom.IsLocalCompleteIntersection (algebraMap k' K') :=
    fieldExtension_isLocalCompleteIntersection (F := k') (E := K')
  rcases hLci.exists_generators_ker_isKoszulRegular with ⟨n, Q, hQ⟩
  have hShort :
      (compPresentationConormalSequence P Q).ShortExact :=
    comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel P Q hQ
  have hExactComp :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
        (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) :=
    tensor_presentation_cotangent_h1_to_comp_generators_h1_exact_of_conormal_shortExact
      P Q hShort
  have hExactOwner :
      Function.Exact
        (tensor_presentation_cotangent_h1_to_h1_cotangent K' P)
        (H1Cotangent.map k k' K' K') :=
    tensor_presentation_cotangent_h1_to_h1_cotangent_exact_of_comp_exact
      (P := P) (Q := Q) hExactComp
  have hfdSource :
      FiniteDimensional K'
        (LinearMap.ker (LinearMap.baseChange K' P.toExtension.cotangentComplex)) := by
    have hfdCotangent : FiniteDimensional k' P.toExtension.Cotangent := by
      let _ : Module.Finite k' P.toExtension.Cotangent := Extension.Cotangent.finite P.fg_ker
      -- The cotangent module of the self-presentation is finite over the finite-type field.
      exact (Module.Free.chooseBasis k' P.toExtension.Cotangent).finiteDimensional_of_finite
    let _ : FiniteDimensional K' (K' ⊗[k'] P.toExtension.Cotangent) := by
      infer_instance
    -- The left source of the presentation row sits inside the base-changed cotangent module.
    infer_instance
  have hker :
      LinearMap.ker (H1Cotangent.map k k' K' K') =
        LinearMap.range (tensor_presentation_cotangent_h1_to_h1_cotangent K' P) := by
    exact hExactOwner.linearMap_ker_eq
  have hfdRange :
      FiniteDimensional K'
        (LinearMap.range (tensor_presentation_cotangent_h1_to_h1_cotangent K' P)) := by
    let _ :
        FiniteDimensional K'
          (LinearMap.ker (LinearMap.baseChange K' P.toExtension.cotangentComplex)) := hfdSource
    infer_instance
  -- Exactness identifies the owner kernel with the finite-dimensional source image.
  exact hker ▸ hfdRange

-- Proof sketch: compare the Jacobi-Zariski exact sequences for the two towers of fields and read
-- off the kernel of the cotangent-homology comparison as a subquotient of the finite-dimensional
-- spaces appearing in Lemma `15.34.1`.
/-- The kernel of the comparison map on first cotangent homology is finite-dimensional over `K'`. -/
theorem finiteDimensional_ker_baseFieldComparison :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := by
  let ιK : K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k K' :=
    LinearMap.liftBaseChange K' (H1Cotangent.map k k K K')
  let μk : H1Cotangent k K' →ₗ[K'] H1Cotangent k' K' := H1Cotangent.map k k' K' K'
  let β : K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k' K' :=
    baseFieldComparison k k' K K'
  have hβ : β = μk.comp ιK := by
    -- This is the defining factorization of the comparison map through `H₁(L_{K'/k})`.
    rfl
  have hιK :
      Function.Injective ιK :=
    field_jacobi_zariski_left_injective (K := k) (L := K) (M := K')
  have hfdUpper :
      FiniteDimensional K' (LinearMap.ker μk) :=
    finiteDimensional_ker_sourceChange_h1_map (k := k) (k' := k') (K' := K')
  let liftKer : LinearMap.ker β →ₗ[K'] LinearMap.ker μk :=
    { toFun := fun x ↦
        ⟨ιK x.1, by
          -- Membership in `ker β` becomes the vanishing equation in the middle `H₁` term.
          change μk (ιK x.1) = 0
          simpa [hβ, LinearMap.comp_apply] using x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  -- Route correction: instead of the invalid finite-source shortcut, inject `ker β` into the
  -- finite-dimensional kernel of the upper source-change map `μk`.
  exact FiniteDimensional.of_injective liftKer <| by
    intro x y hxy
    apply Subtype.ext
    exact hιK (congrArg Subtype.val hxy)

-- Proof sketch: the same exact sequences show that the cokernel of the cotangent-homology
-- comparison is a subquotient of the finite-dimensional endpoint terms, hence is finite-dimensional.
/-- The cokernel of the comparison map on first cotangent homology is finite-dimensional over
`K'`. -/
theorem finiteDimensional_cokernel_baseFieldComparison :
    FiniteDimensional K' (H1Cotangent k' K' ⧸ LinearMap.range (baseFieldComparison k k' K K')) :=
  by
  -- The cokernel is a quotient of the target, so control the target once and descend to the
  -- quotient.
  let _ : FiniteDimensional K' (H1Cotangent k' K') :=
    finiteDimensional_baseFieldComparison_target (k' := k') (K' := K')
  -- The cokernel is a quotient of the finite-dimensional target.
  infer_instance

end H1Cotangent

/-- Helper for Lemma 15.34.3: the kernel of the cotangent-homology base-field comparison has the
same finrank as the common intersection of the two left Jacobi-Zariski images inside
`H₁(L_{K'/k})`. -/
private theorem h1_baseFieldComparison_ker_finrank_eq_range_inf :
    Module.finrank K' (LinearMap.ker (H1Cotangent.baseFieldComparison k k' K K')) =
      Module.finrank K'
        (LinearMap.range (LinearMap.liftBaseChange K' (H1Cotangent.map k k k' K')) ⊓
          LinearMap.range (LinearMap.liftBaseChange K' (H1Cotangent.map k k K K'))) := by
  let ιk : K' ⊗[k'] H1Cotangent k k' →ₗ[K'] H1Cotangent k K' :=
    LinearMap.liftBaseChange K' (H1Cotangent.map k k k' K')
  let ιK : K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k K' :=
    LinearMap.liftBaseChange K' (H1Cotangent.map k k K K')
  let μk : H1Cotangent k K' →ₗ[K'] H1Cotangent k' K' :=
    H1Cotangent.map k k' K' K'
  let β : K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k' K' :=
    H1Cotangent.baseFieldComparison k k' K K'
  let I : Submodule K' (H1Cotangent k K') := LinearMap.range ιk ⊓ LinearMap.range ιK
  have hβ : β = μk.comp ιK := by
    -- This is the defining factorization of the comparison map through `H₁(L_{K'/k})`.
    rfl
  have hExactk : Function.Exact ιk μk := by
    -- The upper Jacobi-Zariski row identifies `ker μk` with `range ιk`.
    simpa [ιk, μk] using H1Cotangent.exact_map_δ k k' K'
  let f : LinearMap.ker β →ₗ[K'] I :=
    { toFun := fun x ↦ by
        have hx0 : μk (ιK x.1) = 0 := by
          change β x.1 = 0
          simpa [hβ, LinearMap.comp_apply] using x.2
        have hxleft : ιK x.1 ∈ LinearMap.range ιk := by
          rw [← hExactk.linearMap_ker_eq]
          exact hx0
        refine ⟨ιK x.1, ?_⟩
        exact ⟨hxleft, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change ιK ((x + y : LinearMap.ker β).1) = ιK x.1 + ιK y.1
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        change ιK ((a • x : LinearMap.ker β).1) = a • ιK x.1
        simp }
  have hf_inj : Function.Injective f := by
    have hιK :
        Function.Injective ιK :=
      field_jacobi_zariski_left_injective (K := k) (L := K) (M := K')
    intro x y hxy
    apply Subtype.ext
    exact hιK (congrArg Subtype.val hxy)
  have hf_surj : Function.Surjective f := by
    intro z
    rcases z.2.2 with ⟨y, hy⟩
    have hzker : z.1 ∈ LinearMap.ker μk := by
      rw [hExactk.linearMap_ker_eq]
      exact z.2.1
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change β y = 0
      change μk (ιK y) = 0
      simpa [hy] using hzker
    · apply Subtype.ext
      exact hy
  -- Transport finrank across the explicit linear equivalence with the common intersection term.
  simpa using
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

/-- Helper for Lemma 15.34.3: the kernel of the Kähler comparison splits into the lower
`mapBaseChange` kernel and the common intersection term in `Ω[K'⁄k]`. -/
private theorem kaehler_baseFieldComparison_ker_split :
    Module.finrank K' (LinearMap.ker (KaehlerDifferential.baseFieldComparison k k' K K')) =
      Module.finrank K' (LinearMap.ker (KaehlerDifferential.mapBaseChange k K K')) +
        Module.finrank K'
          (LinearMap.range (KaehlerDifferential.mapBaseChange k k' K') ⊓
            LinearMap.range (KaehlerDifferential.mapBaseChange k K K')) := by
  let εk : K' ⊗[k'] Ω[k'⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k k' K'
  let εK : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k K K'
  let ζk : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.map k k' K' K'
  let α : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.baseFieldComparison k k' K K'
  let I : Submodule K' Ω[K'⁄k] := LinearMap.range εk ⊓ LinearMap.range εK
  have hα : α = ζk.comp εK := by
    -- This is the defining factorization of the comparison map through `Ω[K'⁄k]`.
    rfl
  have hExactk : Function.Exact εk ζk := by
    -- The upper Jacobi-Zariski row identifies `ker ζk` with `range εk`.
    simpa [εk, ζk] using KaehlerDifferential.exact_mapBaseChange_map k k' K'
  let f : LinearMap.ker εK →ₗ[K'] LinearMap.ker α :=
    { toFun := fun x ↦
        ⟨x.1, by
          have hx0 : εK x.1 = 0 := by
            simpa using x.2
          simpa [hα, LinearMap.comp_apply, hx0]⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  let g : LinearMap.ker α →ₗ[K'] I :=
    { toFun := fun x ↦ by
        have hx0 : ζk (εK x.1) = 0 := by
          change α x.1 = 0
          simpa [hα, LinearMap.comp_apply] using x.2
        have hxleft : εK x.1 ∈ LinearMap.range εk := by
          rw [← hExactk.linearMap_ker_eq]
          exact hx0
        refine ⟨εK x.1, ?_⟩
        exact ⟨hxleft, ⟨x.1, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change εK ((x + y : LinearMap.ker α).1) = εK x.1 + εK y.1
        simp
      map_smul' := by
        intro a x
        apply Subtype.ext
        change εK ((a • x : LinearMap.ker α).1) = a • εK x.1
        simp }
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x.1, ?_⟩, ?_⟩
      · change εK x.1 = 0
        exact congrArg Subtype.val hx
      · apply Subtype.ext
        rfl
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      change εK y.1 = 0
      exact y.2
  have hg_surj : Function.Surjective g := by
    intro z
    rcases z.2.2 with ⟨x, hx⟩
    have hzker : z.1 ∈ LinearMap.ker ζk := by
      rw [hExactk.linearMap_ker_eq]
      exact z.2.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change α x = 0
      rw [hα, LinearMap.comp_apply, hx]
      exact hzker
    · apply Subtype.ext
      exact hx
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  have hkerg :
      Module.finrank K' (LinearMap.ker g) = Module.finrank K' (LinearMap.ker εK) := by
    let e : LinearMap.ker εK ≃ₗ[K'] LinearMap.range f := LinearEquiv.ofInjective f hf_inj
    calc
      Module.finrank K' (LinearMap.ker g) = Module.finrank K' (LinearMap.range f) := by
        rw [hfg.linearMap_ker_eq]
      _ = Module.finrank K' (LinearMap.ker εK) := by
        simpa using (LinearEquiv.finrank_eq e).symm
  have hsurj_finrank :
      Module.finrank K' (LinearMap.range g) =
        Module.finrank K' I := by
    have htop : LinearMap.range g = ⊤ := LinearMap.range_eq_top.2 hg_surj
    calc
      Module.finrank K' (LinearMap.range g) = Module.finrank K' (⊤ : Submodule K' I) := by
        rw [htop]
      _ = Module.finrank K' I := by
        simp
  have hsplit :
      Module.finrank K' (LinearMap.ker α) =
        Module.finrank K' (LinearMap.ker g) + Module.finrank K' I := by
    have hrg := LinearMap.finrank_range_add_finrank_ker g
    rw [hsurj_finrank] at hrg
    simpa [add_comm] using hrg.symm
  -- The short exact sequence `0 → ker εK → ker α → I → 0` yields the finrank splitting.
  rw [hkerg] at hsplit
  exact hsplit

/-- Helper for Lemma 15.34.3: Cartier's equality together with base-change finrank preserves the
endpoint contribution of the two Jacobi-Zariski rows. -/
private theorem baseFieldComparison_endpoint_finrank_eq_trdeg_difference :
    Int.ofNat (Module.finrank K' (K' ⊗[k'] Ω[k'⁄k])) -
      Int.ofNat (Module.finrank K' Ω[K'⁄K]) -
      Int.ofNat (Module.finrank K' (K' ⊗[k'] H1Cotangent k k')) +
      Int.ofNat (Module.finrank K' (H1Cotangent K K')) =
      Int.ofNat (Cardinal.toNat (Algebra.trdeg k k')) -
        Int.ofNat (Cardinal.toNat (Algebra.trdeg K K')) := by
  have hfdTopOmega : FiniteDimensional k' Ω[k'⁄k] := by
    let _ : Module.Finite k' Ω[k'⁄k] := inferInstance
    -- Finite type over a field makes the Kähler module finite-dimensional.
    exact (Module.Free.chooseBasis k' Ω[k'⁄k]).finiteDimensional_of_finite
  have hfdTopH1 : FiniteDimensional k' (H1Cotangent k k') :=
    H1Cotangent.finiteDimensional_of_finiteType_fieldExtension (F := k) (E := k')
  have hTopOmega :
      Module.finrank K' (K' ⊗[k'] Ω[k'⁄k]) = Module.finrank k' Ω[k'⁄k] := by
    -- Extending scalars between fields preserves the finite dimension of the endpoint module.
    exact Module.finrank_baseChange
  have hTopH1 :
      Module.finrank K' (K' ⊗[k'] H1Cotangent k k') = Module.finrank k' (H1Cotangent k k') := by
    -- The same base-change formula applies to the upper `H₁` endpoint.
    exact Module.finrank_baseChange
  have hTop := Algebra.cartier_equality (k := k) (K := k')
  have hBottom := Algebra.cartier_equality (k := K) (K := K')
  -- Rewrite the tensor endpoints over `K'`, then combine the two Cartier equalities.
  rw [hTopOmega, hTopH1]
  omega

/-- Helper for Lemma 15.34.3: the cotangent-homology comparison contributes the upper-left
endpoint, the lower `δ`-kernel, and the upper Kähler kernel to the final Euler characteristic.
-/
private theorem h1_baseFieldComparison_euler_piece :
    - Int.ofNat (Module.finrank K' (LinearMap.ker (H1Cotangent.baseFieldComparison k k' K K'))) +
        Int.ofNat
          (Module.finrank K'
            (H1Cotangent k' K' ⧸ LinearMap.range (H1Cotangent.baseFieldComparison k k' K K'))) =
      - Int.ofNat (Module.finrank K' (K' ⊗[k'] H1Cotangent k k')) +
        Int.ofNat (Module.finrank K' (LinearMap.ker (H1Cotangent.δ k K K'))) +
        Int.ofNat (Module.finrank K' (LinearMap.ker (KaehlerDifferential.mapBaseChange k k' K'))) := by
  -- Route correction: the remaining `H₁` calculation must use the descended upper-row quotient
  -- `K' ⊗[k'] H₁(L_{k'/k}) → H₁(L_{K'/k}) ⧸ range ιK → coker β → ker εk`. The blocker is the
  -- source-faithful field exactness `ker μk = range ιk`, which is stronger than the owner
  -- exactness currently imported in this file.
  -- TODO: once the upper-left field Jacobi-Zariski exactness is available in canonical owner form,
  -- build the quotient row
  -- `0 → ker β → K' ⊗[k'] H₁(L_{k'/k}) → H₁(L_{K'/k}) ⧸ range ιK → coker β → ker εk → 0`,
  -- identify `H₁(L_{K'/k}) ⧸ range ιK` with `ker (H1Cotangent.δ k K K')`, and finish with
  -- `alternating_finrank_of_six_term_exact_row`.
  sorry

/-- Helper for Lemma 15.34.3: the Kähler comparison contributes the lower `mapBaseChange` kernel,
the upper Kähler image, and the lower endpoint module to the final Euler characteristic. -/
private theorem kaehler_baseFieldComparison_euler_piece :
    Int.ofNat (Module.finrank K' (LinearMap.ker (KaehlerDifferential.baseFieldComparison k k' K K'))) -
        Int.ofNat
          (Module.finrank K'
            (Ω[K'⁄k'] ⧸ LinearMap.range (KaehlerDifferential.baseFieldComparison k k' K K'))) =
      Int.ofNat (Module.finrank K' (LinearMap.ker (KaehlerDifferential.mapBaseChange k K K'))) +
        Int.ofNat (Module.finrank K' (LinearMap.range (KaehlerDifferential.mapBaseChange k k' K'))) -
        Int.ofNat (Module.finrank K' Ω[K'⁄K]) := by
  let εk : K' ⊗[k'] Ω[k'⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k k' K'
  let εK : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k K K'
  let ζk : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.map k k' K' K'
  let ζK : Ω[K'⁄k] →ₗ[K'] Ω[K'⁄K] := KaehlerDifferential.map k K K' K'
  let α : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] := KaehlerDifferential.baseFieldComparison k k' K K'
  let I : Submodule K' Ω[K'⁄k] := LinearMap.range εk ⊓ LinearMap.range εK
  let Q : Type u := Ω[K'⁄k] ⧸ LinearMap.range εK
  let C : Type u := Ω[K'⁄k'] ⧸ LinearMap.range α
  have hα : α = ζk.comp εK := by
    -- This is the defining factorization of the Kähler comparison map.
    rfl
  have hExactk : Function.Exact εk ζk := by
    -- The upper Jacobi-Zariski row identifies `ker ζk` with `range εk`.
    simpa [εk, ζk] using KaehlerDifferential.exact_mapBaseChange_map k k' K'
  have hExactK : Function.Exact εK ζK := by
    -- The lower Jacobi-Zariski row identifies `ker ζK` with `range εK`.
    simpa [εK, ζK] using KaehlerDifferential.exact_mapBaseChange_map k K K'
  have hSurjK : Function.Surjective ζK := by
    -- The lower Kähler tail ends in the surjective map to `Ω[K'⁄K]`.
    simpa [ζK] using KaehlerDifferential.map_surjective k K K'
  let iI : I →ₗ[K'] LinearMap.range εk :=
    Submodule.inclusion (show I ≤ LinearMap.range εk from inf_le_left)
  let qα : LinearMap.range εk →ₗ[K'] Q :=
    (LinearMap.range εK).mkQ.comp (LinearMap.range εk).subtype
  let τbar : Q →ₗ[K'] C :=
    (LinearMap.range εK).liftQ
      ((LinearMap.range α).mkQ.comp ζk)
      (by
        intro x hx
        rcases hx with ⟨y, rfl⟩
        -- Elements coming from `range εK` land in `range α` after applying `ζk`.
        change ((LinearMap.range α).mkQ) (α y) = 0
        rw [Submodule.Quotient.eq_zero_iff_mem]
        exact ⟨y, rfl⟩)
  have hComp_iI_qα : qα.comp iI = 0 := by
    ext x
    change ((LinearMap.range εK).mkQ) x.1 = 0
    rw [Submodule.Quotient.eq_zero_iff_mem]
    exact x.2.2
  have hExact_iI_qα : Function.Exact iI qα := by
    refine LinearMap.exact_of_comp_of_mem_range hComp_iI_qα ?_
    intro x hx
    -- A class in `range εk` vanishes in the quotient precisely when it already lies in `range εK`.
    rw [Submodule.Quotient.eq_zero_iff_mem] at hx
    refine ⟨⟨x.1, ⟨x.2, hx⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hComp_qα_τbar : τbar.comp qα = 0 := by
    ext x
    rcases x.2 with ⟨y, rfl⟩
    -- The upper Jacobi-Zariski row makes `ζk ∘ εk` vanish.
    change ((LinearMap.range α).mkQ) (ζk (εk y)) = 0
    have hy0 : ζk (εk y) = 0 := by
      simpa using DFunLike.congr_fun hExactk.linearMap_comp_eq_zero y
    simpa [hy0]
  have hExact_qα_τbar : Function.Exact qα τbar := by
    refine LinearMap.exact_of_comp_of_mem_range hComp_qα_τbar ?_
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range εK) x
    change ((LinearMap.range α).mkQ) (ζk y) = 0 at hx
    rw [Submodule.Quotient.eq_zero_iff_mem] at hx
    rcases hx with ⟨z, hz⟩
    have hyker : y - εK z ∈ LinearMap.ker ζk := by
      -- Subtract a chosen lower-row representative to move into the upper kernel.
      change ζk (y - εK z) = 0
      rw [map_sub, hz, hα, LinearMap.comp_apply, sub_self]
    have hyεk : y - εK z ∈ LinearMap.range εk := by
      rw [hExactk.linearMap_ker_eq] at hyker
      exact hyker
    rcases hyεk with ⟨w, hw⟩
    refine ⟨⟨εk w, ⟨w, rfl⟩⟩, ?_⟩
    change ((LinearMap.range εK).mkQ) (εk w) = (LinearMap.range εK).mkQ y
    rw [hw, map_sub]
    have hz0 : ((LinearMap.range εK).mkQ) (εK z) = 0 := by
      rw [Submodule.Quotient.eq_zero_iff_mem]
      exact ⟨z, rfl⟩
    simpa [hz0]
  have hτbar_surj : Function.Surjective τbar := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range α) x
    obtain ⟨z, rfl⟩ := KaehlerDifferential.map_surjective k k' K' y
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rfl
  have hker_qα :
      Module.finrank K' (LinearMap.ker qα) = Module.finrank K' I := by
    let e : I ≃ₗ[K'] LinearMap.range iI := LinearEquiv.ofInjective iI <|
      Submodule.inclusion_injective (show I ≤ LinearMap.range εk from inf_le_left)
    calc
      Module.finrank K' (LinearMap.ker qα) = Module.finrank K' (LinearMap.range iI) := by
        rw [hExact_iI_qα.linearMap_ker_eq]
      _ = Module.finrank K' I := by
        simpa using (LinearEquiv.finrank_eq e).symm
  let eQ :
      Q ≃ₗ[K'] Ω[K'⁄K] :=
    (Submodule.quotEquivOfEq
      (p := LinearMap.range εK) (p' := LinearMap.ker ζK) hExactK.linearMap_ker_eq.symm).trans
      (LinearMap.quotKerEquivOfSurjective ζK hSurjK)
  have hQfinrank : Module.finrank K' Q = Module.finrank K' Ω[K'⁄K] := by
    simpa using LinearEquiv.finrank_eq eQ
  have hcoker_qα :
      Module.finrank K' (Q ⧸ LinearMap.range qα) = Module.finrank K' C := by
    let eC :
        (Q ⧸ LinearMap.range qα) ≃ₗ[K'] C :=
      (Submodule.quotEquivOfEq
        (p := LinearMap.range qα) (p' := LinearMap.ker τbar) hExact_qα_τbar.linearMap_ker_eq.symm)
        .trans (LinearMap.quotKerEquivOfSurjective τbar hτbar_surj)
    simpa using LinearEquiv.finrank_eq eC
  have hfdRangeεk : FiniteDimensional K' (LinearMap.range εk) := by
    let _ : FiniteDimensional k' Ω[k'⁄k] := by
      let _ : Module.Finite k' Ω[k'⁄k] := inferInstance
      exact (Module.Free.chooseBasis k' Ω[k'⁄k]).finiteDimensional_of_finite
    let _ : FiniteDimensional K' (K' ⊗[k'] Ω[k'⁄k]) := by
      infer_instance
    infer_instance
  have hfdQ : FiniteDimensional K' Q := by
    exact FiniteDimensional.of_injective eQ.toLinearMap eQ.injective
  let _ : FiniteDimensional K' (LinearMap.range εk) := hfdRangeεk
  let _ : FiniteDimensional K' Q := hfdQ
  have hEuler_qα :
      Int.ofNat (Module.finrank K' (LinearMap.ker qα)) -
          Int.ofNat (Module.finrank K' (Q ⧸ LinearMap.range qα)) =
        Int.ofNat (Module.finrank K' (LinearMap.range εk)) -
          Int.ofNat (Module.finrank K' Q) := by
    -- Apply the generic two-term Euler characteristic formula to the descended quotient map.
    simpa using
      finrank_ker_sub_finrank_cokernel_eq_finrank_source_sub_finrank_target (F := K') qα
  -- Combine the short exact splitting for `ker α` with the quotient-row Euler identity.
  rw [kaehler_baseFieldComparison_ker_split]
  rw [hker_qα, hcoker_qα, hQfinrank] at hEuler_qα
  omega

-- Proof sketch: compare the two Jacobi-Zariski exact sequences for
-- `k ⊆ k' ⊆ K'` and `k ⊆ K ⊆ K'`. The kernels and cokernels of this comparison map identify with
-- subquotients of the finite-dimensional vector spaces `Ω[k'⁄k]`, `Ω[K'⁄K]`, `H1Cotangent k k'`,
-- and `H1Cotangent K K'`, whose finite dimensionality comes from Cartier's equality.
/-- Lemma 15.34.3: for a commutative square of field extensions with `k' / k` and `K' / K`
finitely generated, the alternating sum of the kernel and cokernel dimensions of the canonical
comparison maps on Kähler differentials and first cotangent homology equals
`trdeg_k(k') - trdeg_K(K')`. -/
theorem baseFieldComparison_eulerCharacteristic_eq_trdeg_sub_trdeg :
    Int.ofNat (Module.finrank K' (LinearMap.ker (KaehlerDifferential.baseFieldComparison k k' K K'))) -
      Int.ofNat
        (Module.finrank K'
          (Ω[K'⁄k'] ⧸ LinearMap.range (KaehlerDifferential.baseFieldComparison k k' K K'))) -
      Int.ofNat (Module.finrank K' (LinearMap.ker (H1Cotangent.baseFieldComparison k k' K K'))) +
      Int.ofNat
        (Module.finrank K'
          (H1Cotangent k' K' ⧸ LinearMap.range (H1Cotangent.baseFieldComparison k k' K K'))) =
      Int.ofNat (Cardinal.toNat (Algebra.trdeg k k')) -
        Int.ofNat (Cardinal.toNat (Algebra.trdeg K K')) := by
  let εk : K' ⊗[k'] Ω[k'⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k k' K'
  let εK : K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k] := KaehlerDifferential.mapBaseChange k K K'
  let δK : H1Cotangent K K' →ₗ[K'] K' ⊗[K] Ω[K⁄k] := H1Cotangent.δ k K K'
  have hExactδKεK : Function.Exact δK εK := by
    -- The lower Jacobi-Zariski row identifies `ker εK` with `range δK`.
    simpa [δK, εK] using H1Cotangent.exact_δ_mapBaseChange k K K'
  have hkerεK : LinearMap.ker εK = LinearMap.range δK := hExactδKεK.linearMap_ker_eq
  have hRangeKerεk :
      Module.finrank K' (LinearMap.range εk) + Module.finrank K' (LinearMap.ker εk) =
        Module.finrank K' (K' ⊗[k'] Ω[k'⁄k]) := by
    -- Rank-nullity on the upper Kähler base-change map turns the image/kernel pair into the
    -- upper endpoint module from the source proof.
    simpa [εk, add_comm] using LinearMap.finrank_range_add_finrank_ker εk
  have hRangeKerδK :
      Module.finrank K' (LinearMap.range δK) + Module.finrank K' (LinearMap.ker δK) =
        Module.finrank K' (H1Cotangent K K') := by
    -- The same rank-nullity step on the lower `δ` map recovers the lower `H₁` endpoint.
    simpa [δK, add_comm] using LinearMap.finrank_range_add_finrank_ker δK
  have hEndpoint := baseFieldComparison_endpoint_finrank_eq_trdeg_difference
  -- Route correction: the invalid source-minus-target shortcut has been replaced by two
  -- source-faithful one-sided Euler pieces, one for `Ω` and one for `H₁`.
  rw [kaehler_baseFieldComparison_euler_piece, h1_baseFieldComparison_euler_piece]
  rw [hkerεK]
  omega

end

end Algebra
