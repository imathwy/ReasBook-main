import stacks_proof.stacks_project.Chap10.Lemma_10_150_4
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap10.Lemma_10_14_2
import stacks_proof.stacks_project.Chap10.Lemma_10_24_5
import stacks_proof.stacks_project.Chap10.Lemma_10_39_18
import stacks_proof.stacks_project.Chap10.Lemma_10_168_1
import stacks_proof.stacks_project.Chap15.«15_18_0_1»
import stacks_proof.stacks_project.Chap15.Lemma_15_11_13
import stacks_proof.stacks_project.Chap15.Lemma_15_81_8
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x y

noncomputable section

section DirectLimitDescent

variable {R : Type u} {S : Type v} {M : Type w} {Λ : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
variable [Preorder Λ] [IsDirectedOrder Λ] [Nonempty Λ]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
- primary domain: directed colimits of commutative `R`-algebras and flat-over-base loci after
  base change;
- sampled owner declarations:
  `Ring.DirectLimit.algebraMap`,
  `Ring.DirectLimit.algebraMap_eq_of`,
  `Ring.DirectLimit.instAlgebra`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the canonical direct-limit `R`-algebra owner
  `Ring.DirectLimit.algebraMap`;
- layer triage:
  - `source-facing`: Lemma 15.18.3;
  - `core/canonical`: `Module.flatOverBaseLocus` and `Ring.DirectLimit.algebraMap`;
  - `bridge/view`: passing from the `AlgHom`-valued directed system to its underlying ring-hom
    system when forming `Ring.DirectLimit`.

Primitive data are the stage rings, their `R`-algebra structures, the directed system, and the
stage ideals. Their extensions to `S ⊗[R] A i` and to the direct-limit base change are derived
API, as is the direct-limit `R`-algebra structure; all of these should come directly from the
canonical owner built from the directed system of `R`-algebra morphisms.
-/

section

variable (A : Λ → Type y) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (φ : ∀ i j, i ≤ j → A i →ₐ[R] A j)
variable [DirectedSystem A fun i j h ↦ (φ i j h : A i →+* A j)]
variable (I : ∀ i, Ideal (A i))

local notation "ρ" => fun i j h ↦ (φ i j h : A i →+* A j)
local notation "A∞" => Ring.DirectLimit A ρ
local notation "ι∞" => Ring.DirectLimit.of A ρ
local notation "I∞" => ⨆ i, Ideal.map (ι∞ i) (I i)
local notation "S∞" => S ⊗[R] A∞
local notation "M∞" => S∞ ⊗[S] M
local notation "S[" i "]" => S ⊗[R] A i
local notation "M[" i "]" => S[i] ⊗[S] M

/-- Helper for Lemma 15.18.3: the canonical map from a stage algebra `A i` to the direct limit
commutes with the base `R`-algebra structure. -/
lemma stageToDirectLimit_commutes (i : Λ) (r : R) :
    ι∞ i (algebraMap R (A i) r) = algebraMap R A∞ r := by
  -- This is exactly the canonical description of the direct-limit `R`-algebra map.
  simpa using (Ring.DirectLimit.algebraMap_eq_of (R := R) (S := A) (φ := φ) i r).symm

/-- Helper for Lemma 15.18.3: the canonical map from a stage algebra to the direct limit is an
`R`-algebra homomorphism. -/
noncomputable def stageToDirectLimitAlgHom (i : Λ) : A i →ₐ[R] A∞ :=
  { toRingHom := ι∞ i
    commutes' := stageToDirectLimit_commutes (A := A) (φ := φ) i }

/-- Helper for Lemma 15.18.3: tensoring the transition map `A i → A j` with `S` gives the
canonical stage-to-stage map on the base-changed algebras. -/
noncomputable def tensorBaseChangeMap (i j : Λ) (hij : i ≤ j) : S[i] →ₐ[S] S[j] :=
  Algebra.TensorProduct.map (AlgHom.id S S) (φ i j hij)

/-- Helper for Lemma 15.18.3: tensoring the stage map `A i → A∞` with `S` gives the canonical
map from the stage base change `S[i]` to the limit base change `S∞`. -/
noncomputable def tensorBaseChangeToLimit (i : Λ) : S[i] →ₐ[S] S∞ :=
  Algebra.TensorProduct.map (AlgHom.id S S) (stageToDirectLimitAlgHom (A := A) (φ := φ) i)

/-- Helper for Lemma 15.18.3: finite presentation is preserved by tensor-product base change for
both the algebra and module appearing in the statement. -/
lemma finitePresentation_tensorBaseChange
    (B : Type*) [CommRing B] [Algebra R B] :
    Algebra.FinitePresentation B (S ⊗[R] B) ∧
      Module.FinitePresentation (S ⊗[R] B) ((S ⊗[R] B) ⊗[S] M) := by
  have hsource : (algebraMap B (B ⊗[R] S)).FinitePresentation := by
    simpa using
      (Algebra.FinitePresentation.baseChange (A := S) (B := B) :
        Algebra.FinitePresentation B (B ⊗[R] S))
  have hcomm :
      ((Algebra.TensorProduct.comm R B S : B ⊗[R] S ≃ₐ[R] S ⊗[R] B).toRingHom).FinitePresentation := by
    -- The tensor-symmetry equivalence is a surjective algebra map with trivial kernel.
    refine AlgHom.FinitePresentation.of_surjective
      (f := (Algebra.TensorProduct.comm R B S : B ⊗[R] S →ₐ[R] S ⊗[R] B))
      (Algebra.TensorProduct.comm R B S).surjective ?_
    have hker :
        RingHom.ker
            ((Algebra.TensorProduct.comm R B S : B ⊗[R] S →ₐ[R] S ⊗[R] B).toRingHom) =
          ⊥ := by
      ext x
      simp
    simpa [hker] using (Submodule.fg_bot : (⊥ : Ideal (B ⊗[R] S)).FG)
  have htarget :
      (algebraMap B (S ⊗[R] B)).FinitePresentation := by
    have hcomp :
        (((Algebra.TensorProduct.comm R B S : B ⊗[R] S ≃ₐ[R] S ⊗[R] B).toRingHom).comp
          (algebraMap B (B ⊗[R] S))).FinitePresentation :=
      RingHom.FinitePresentation.comp hcomm hsource
    have hEq :
        ((Algebra.TensorProduct.comm R B S : B ⊗[R] S ≃ₐ[R] S ⊗[R] B).toRingHom).comp
            (algebraMap B (B ⊗[R] S)) =
          algebraMap B (S ⊗[R] B) := by
      ext b
      change 1 ⊗ₜ[R] b = (algebraMap B (S ⊗[R] B)) b
      change 1 ⊗ₜ[R] b = 1 ⊗ₜ[R] b
      rfl
    simpa [hEq] using hcomp
  -- The module-side base-change finite-presentation instance is already available canonically.
  exact ⟨htarget, inferInstance⟩

/-- Helper for Lemma 15.18.3: the stage-to-limit tensor map after a stage transition agrees with
the original stage-to-limit tensor map. -/
lemma tensorBaseChange_toLimit_comp_stageMap_hom (i j : Λ) (hij : i ≤ j) :
    ((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
        (tensorBaseChangeMap (A := A) (φ := φ) i j hij) : S[i] →ₐ[S] S∞) =
      tensorBaseChangeToLimit (A := A) (φ := φ) i := by
  -- Compare the algebra maps on pure tensors; the direct-limit relation `of_f` is the only
  -- non-definitional step.
  apply AlgHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simpa using
      map_zero
        (((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
          (tensorBaseChangeMap (A := A) (φ := φ) i j hij)) : S[i] →ₐ[S] S∞)
  · intro s a
    change
      tensorBaseChangeToLimit (A := A) (φ := φ) j
          (tensorBaseChangeMap (A := A) (φ := φ) i j hij (s ⊗ₜ[R] a)) =
        tensorBaseChangeToLimit (A := A) (φ := φ) i (s ⊗ₜ[R] a)
    rw [tensorBaseChangeMap, tensorBaseChangeToLimit, tensorBaseChangeToLimit,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul]
    change s ⊗ₜ[R] (ι∞ j ((φ i j hij) a)) = s ⊗ₜ[R] (ι∞ i a)
    simpa using congrArg (fun z : A∞ ↦ s ⊗ₜ[R] z) (Ring.DirectLimit.of_f hij a)
  · intro x y hx hy
    calc
      ((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
          (tensorBaseChangeMap (A := A) (φ := φ) i j hij)) (x + y) =
        ((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
            (tensorBaseChangeMap (A := A) (φ := φ) i j hij)) x +
          ((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
            (tensorBaseChangeMap (A := A) (φ := φ) i j hij)) y := by
              simpa using
                map_add
                  (((tensorBaseChangeToLimit (A := A) (φ := φ) j).comp
                    (tensorBaseChangeMap (A := A) (φ := φ) i j hij)) : S[i] →ₐ[S] S∞)
                  x y
      _ = tensorBaseChangeToLimit (A := A) (φ := φ) i x +
            tensorBaseChangeToLimit (A := A) (φ := φ) i y := by
              rw [hx, hy]
      _ = tensorBaseChangeToLimit (A := A) (φ := φ) i (x + y) := by
              symm
              simpa using map_add (tensorBaseChangeToLimit (A := A) (φ := φ) i) x y

/-- Helper for Lemma 15.18.3: the stage-to-limit tensor maps compose exactly as the underlying
direct-limit structure maps do. -/
lemma tensorBaseChange_toLimit_comp_stageMap (i j : Λ) (hij : i ≤ j) (x : S[i]) :
    tensorBaseChangeToLimit (A := A) (φ := φ) j
        (tensorBaseChangeMap (A := A) (φ := φ) i j hij x) =
      tensorBaseChangeToLimit (A := A) (φ := φ) i x := by
  -- Apply the map-level comparison to the chosen tensor element.
  simpa using
    congrArg (fun f : S[i] →ₐ[S] S∞ ↦ f x)
      (tensorBaseChange_toLimit_comp_stageMap_hom (A := A) (φ := φ) i j hij)

/-- Helper for Lemma 15.18.3: every element of the limit tensor product `S∞` is represented at
some stage tensor product `S[i]`. -/
lemma exists_stage_tensorBaseChange_lift (x : S∞) :
    ∃ i : Λ, ∃ xi : S[i],
      tensorBaseChangeToLimit (A := A) (φ := φ) i xi = x := by
  -- Represent pure tensors by descending the direct-limit factor, then use directedness to merge
  -- stage representatives in the additive case.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · obtain ⟨i⟩ := ‹Nonempty Λ›
    refine ⟨i, 0, ?_⟩
    simpa using map_zero (tensorBaseChangeToLimit (A := A) (φ := φ) i)
  · intro s a
    rcases Ring.DirectLimit.exists_of (G := A) (f := ρ) a with ⟨i, ai, rfl⟩
    refine ⟨i, s ⊗ₜ[R] ai, ?_⟩
    -- On a pure tensor, the limit map is just tensoring the stage representative into `A∞`.
    rw [tensorBaseChangeToLimit, Algebra.TensorProduct.map_tmul]
    change s ⊗ₜ[R] (ι∞ i ai) = s ⊗ₜ[R] (ι∞ i ai)
    rfl
  · intro x y hx hy
    rcases hx with ⟨i, xi, hxi⟩
    rcases hy with ⟨j, yj, hyj⟩
    rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
    refine ⟨k,
      tensorBaseChangeMap (A := A) (φ := φ) i k hik xi +
        tensorBaseChangeMap (A := A) (φ := φ) j k hjk yj,
      ?_⟩
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) k
          (tensorBaseChangeMap (A := A) (φ := φ) i k hik xi +
            tensorBaseChangeMap (A := A) (φ := φ) j k hjk yj) =
        tensorBaseChangeToLimit (A := A) (φ := φ) k
            (tensorBaseChangeMap (A := A) (φ := φ) i k hik xi) +
          tensorBaseChangeToLimit (A := A) (φ := φ) k
            (tensorBaseChangeMap (A := A) (φ := φ) j k hjk yj) := by
              simpa using
                map_add (tensorBaseChangeToLimit (A := A) (φ := φ) k)
                  (tensorBaseChangeMap (A := A) (φ := φ) i k hik xi)
                  (tensorBaseChangeMap (A := A) (φ := φ) j k hjk yj)
      _ = tensorBaseChangeToLimit (A := A) (φ := φ) i xi +
            tensorBaseChangeToLimit (A := A) (φ := φ) j yj := by
              rw [tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) i k hik xi,
                tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) j k hjk yj]
      _ = x + y := by rw [hxi, hyj]

/-- Helper for Lemma 15.18.3: a finite family of elements in the limit tensor product is already
represented at one common stage. -/
lemma exists_common_stage_lifts_of_finite_limit_family {n : ℕ} (fInf : Fin n → S∞) :
    ∃ i : Λ, ∃ fi : Fin n → S[i],
      ∀ a, tensorBaseChangeToLimit (A := A) (φ := φ) i (fi a) = fInf a := by
  induction n with
  | zero =>
      obtain ⟨i⟩ := ‹Nonempty Λ›
      refine ⟨i, Fin.elim0, ?_⟩
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      obtain ⟨i0, x0, hx0⟩ :=
        exists_stage_tensorBaseChange_lift (A := A) (φ := φ) (x := fInf 0)
      obtain ⟨i, fi, hfi⟩ := ih (fun a : Fin n ↦ fInf a.succ)
      rcases exists_ge_ge i0 i with ⟨j, hi0j, hij⟩
      refine ⟨j,
        Fin.cases
          (tensorBaseChangeMap (A := A) (φ := φ) i0 j hi0j x0)
          (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a)),
        ?_⟩
      intro a
      refine Fin.cases ?_ ?_ a
      · -- The zeroth entry is the chosen representative of `fInf 0`, transported to the common
        -- stage `j`.
        calc
          tensorBaseChangeToLimit (A := A) (φ := φ) j
              (tensorBaseChangeMap (A := A) (φ := φ) i0 j hi0j x0) =
            tensorBaseChangeToLimit (A := A) (φ := φ) i0 x0 := by
              exact tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) i0 j hi0j x0
          _ = fInf 0 := hx0
      · intro b
        -- The tail entries follow from the inductive common-stage lift after transport to `j`.
        calc
          tensorBaseChangeToLimit (A := A) (φ := φ) j
              (tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi b)) =
            tensorBaseChangeToLimit (A := A) (φ := φ) i (fi b) := by
              exact tensorBaseChange_toLimit_comp_stageMap (A := A) (φ := φ) i j hij (fi b)
          _ = fInf b.succ := hfi b

/-- Helper for Lemma 15.18.3: if a stage element already maps into the direct-limit ideal `I∞`,
then above any prescribed lower bound it lands in a later stage ideal. -/
lemma exists_stage_mem_directLimit_ideal_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    {i j₀ : Λ} (hij₀ : i ≤ j₀) {x : A i}
    (hx : ι∞ i x ∈ I∞) :
    ∃ j : Λ, ∃ hj₀j : j₀ ≤ j, (φ i j (le_trans hij₀ hj₀j)) x ∈ I j := by
  -- First descend the ideal membership somewhere above `i`, then raise to the requested lower
  -- bound `j₀`.
  obtain ⟨k, hik, hkx⟩ :=
    exists_ge_mem_stage_ideal_of_mem_directLimit_ideal
      (A := A) (I := I) (f := ρ) hI hx
  rcases exists_ge_ge j₀ k with ⟨j, hj₀j, hkj⟩
  have hmem_map : (φ k j hkj) ((φ i k hik) x) ∈ I j := by
    exact (hI hkj) (Ideal.mem_map_of_mem _ hkx)
  -- The directed-system cocycle rewrites the transported element into the desired stage map.
  refine ⟨j, hj₀j, ?_⟩
  have hmap_eq :
      (φ k j hkj) ((φ i k hik) x) = (φ i j (le_trans hij₀ hj₀j)) x := by
    simpa using (DirectedSystem.map_map' (f := ρ) hik hkj x)
  exact hmap_eq ▸ hmem_map

/-- Helper for Lemma 15.18.3: a finite family of stage elements whose images lie in `I∞`
simultaneously lands in one later stage ideal above any prescribed lower bound. -/
lemma exists_common_stage_mem_directLimit_ideal_of_stage_family_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    {n : ℕ} {i j₀ : Λ} (hij₀ : i ≤ j₀) (x : Fin n → A i)
    (hx : ∀ a, ι∞ i (x a) ∈ I∞) :
    ∃ j : Λ, ∃ hj₀j : j₀ ≤ j, ∀ a, (φ i j (le_trans hij₀ hj₀j)) (x a) ∈ I j := by
  induction n generalizing j₀ with
  | zero =>
      refine ⟨j₀, le_rfl, ?_⟩
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      have hx₀ : ι∞ i (x 0) ∈ I∞ := hx 0
      obtain ⟨j₁, hj₀j₁, hx₁⟩ :=
        exists_stage_mem_directLimit_ideal_above
          (A := A) (φ := φ) (I := I) hI hij₀ hx₀
      have htail :
          ∀ a : Fin n, ι∞ i (x a.succ) ∈ I∞ := by
        intro a
        exact hx a.succ
      obtain ⟨j, hj₁j, htail_mem⟩ :=
        ih (j₀ := j₁) (le_trans hij₀ hj₀j₁) (fun a : Fin n ↦ x a.succ) htail
      have hhead_mem : (φ i j (le_trans hij₀ (le_trans hj₀j₁ hj₁j))) (x 0) ∈ I j := by
        have hmem_map :
            (φ j₁ j hj₁j) ((φ i j₁ (le_trans hij₀ hj₀j₁)) (x 0)) ∈ I j := by
          exact (hI hj₁j) (Ideal.mem_map_of_mem _ hx₁)
        -- Route correction: keep the source route by transporting the already-descended head
        -- witness along the transition, rather than re-descending it from the limit again.
        have hmap_eq :
            (φ j₁ j hj₁j) ((φ i j₁ (le_trans hij₀ hj₀j₁)) (x 0)) =
              (φ i j (le_trans hij₀ (le_trans hj₀j₁ hj₁j))) (x 0) := by
          simpa using
            (DirectedSystem.map_map' (f := ρ) (le_trans hij₀ hj₀j₁) hj₁j (x 0))
        exact hmap_eq ▸ hmem_map
      refine ⟨j, le_trans hj₀j₁ hj₁j, ?_⟩
      intro a
      refine Fin.cases hhead_mem ?_ a
      intro b
      simpa using htail_mem b

/-- Helper for Lemma 15.18.3: if the closed subset cut out by an ideal lies in the flat-over-base
locus of a finitely presented module, then finitely many basic opens already cover that closed
subset inside the flat locus, and their generators together with the ideal generate the unit
ideal. -/
lemma exists_finite_basicOpen_cover_of_zeroLocus_subset_flatOverBaseLocus
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    [Algebra.FinitePresentation A T] [Module.FinitePresentation T N]
    (J : Ideal T)
    (hsubset : zeroLocus (J : Set T) ⊆ Module.flatOverBaseLocus A T N) :
    ∃ n : ℕ, ∃ f : Fin n → T,
      (∀ a, (basicOpen (f a) : Set (PrimeSpectrum T)) ⊆ Module.flatOverBaseLocus A T N) ∧
      Ideal.span (Set.range f) + J = ⊤ := by
  let flatLocus : Set (PrimeSpectrum T) := Module.flatOverBaseLocus A T N
  have hopen : IsOpen flatLocus := by
    simpa [flatLocus] using Module.isOpen_flatOverBaseLocus_of_finitePresentation (R := A)
      (S := T) (M := N)
  have hcompact : IsCompact (zeroLocus (J : Set T)) := by
    simpa using (isClosed_zeroLocus (J : Set T)).isCompact
  -- Each point of the closed subset admits a basic-open neighborhood contained in the flat locus.
  have hbasic :
      ∀ x : zeroLocus (J : Set T),
        ∃ g : T,
          x.1 ∈ (basicOpen g : Set (PrimeSpectrum T)) ∧
            (basicOpen g : Set (PrimeSpectrum T)) ⊆ flatLocus := by
    intro x
    have hxnhds : flatLocus ∈ nhds x.1 := hopen.mem_nhds (hsubset x.2)
    rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hxnhds with
      ⟨U, hU, hxU, hUsub⟩
    rcases hU with ⟨g, rfl⟩
    exact ⟨g, hxU, hUsub⟩
  choose g hgmem hgsub using hbasic
  obtain ⟨t, ht⟩ :=
    hcompact.elim_finite_subcover
      (fun x : zeroLocus (J : Set T) ↦ (basicOpen (g x) : Set (PrimeSpectrum T)))
      (fun x ↦ (basicOpen (g x)).2)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hgmem ⟨x, hx⟩⟩)
  let ι := ↥t
  let fsub : ι → T := fun a ↦ g a.1
  have hflat_basic : ∀ a : ι, (basicOpen (fsub a) : Set (PrimeSpectrum T)) ⊆ flatLocus := by
    intro a
    exact hgsub a.1
  have hcover :
      zeroLocus (J : Set T) ⊆ ⋃ a : ι, (basicOpen (fsub a) : Set (PrimeSpectrum T)) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (ht hx) with ⟨y, hyt, hy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hy⟩
  -- A maximal ideal containing the generated ideal would define a prime in `V(J)` outside the
  -- asserted basic-open cover, which is impossible.
  have hspan_sub : Ideal.span (Set.range fsub) + J = ⊤ := by
    by_contra htop
    obtain ⟨m, hmmax, hmle⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range fsub) + J) htop
    let q : PrimeSpectrum T := ⟨m, hmmax.isPrime⟩
    have hJm : J ≤ m := le_trans le_sup_right hmle
    have hqJ : q ∈ zeroLocus (J : Set T) := (mem_zeroLocus q (J : Set T)).2 hJm
    rcases Set.mem_iUnion.mp (hcover hqJ) with ⟨a, ha⟩
    have hspanm : Ideal.span (Set.range fsub) ≤ m := le_trans le_sup_left hmle
    have hfm : fsub a ∈ m := hspanm (Ideal.subset_span (Set.mem_range_self a))
    exact (PrimeSpectrum.mem_basicOpen (fsub a) q).1 ha hfm
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f : Fin (Fintype.card ι) → T := fun a ↦ fsub (e.symm a)
  have hflat_basic_fin :
      ∀ a : Fin (Fintype.card ι), (basicOpen (f a) : Set (PrimeSpectrum T)) ⊆ flatLocus := by
    intro a
    exact hflat_basic (e.symm a)
  have hrange : Set.range f = Set.range fsub := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, by simp [f, fsub, e]⟩
  refine ⟨Fintype.card ι, f, hflat_basic_fin, ?_⟩
  simpa [hrange] using hspan_sub

/-- Helper for Lemma 15.18.3: the limit-side closed-subset hypothesis can be read primewise using
the flat-locus owner statement `15.18.0.1`. -/
lemma limit_zeroLocus_subset_flatOverBaseLocus_primewise
    (hflat_inf :
      zeroLocus (Ideal.map (algebraMap A∞ S∞) I∞ : Set S∞) ⊆
        Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∀ q : PrimeSpectrum S∞,
      q ∈ zeroLocus (Ideal.map (algebraMap A∞ S∞) I∞ : Set S∞) →
        Module.Flat A∞ (LocalizedModule.AtPrime q.asIdeal M∞) := by
  -- Rewrite the inclusion into the flat locus using the chapter-level primewise characterization.
  exact
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := A∞) (S := S∞) (M := M∞)
      (Ideal.map (algebraMap A∞ S∞) I∞)).1 hflat_inf

/-- Helper for Lemma 15.18.3: the limit-side unit-ideal cover can be reduced to finitely many
elements coming either from the chosen finite family `fInf` or from images of the colimit ideal
`I∞`. -/
lemma exists_finite_mixed_generating_family_of_cover
    {n : ℕ} (fInf : Fin n → S∞)
    (hcover : Ideal.span (Set.range fInf) + Ideal.map (algebraMap A∞ S∞) I∞ = ⊤) :
    ∃ t : Finset S∞,
      (↑t : Set S∞) ⊆
        (Set.range fInf ∪ (algebraMap A∞ S∞) '' (I∞ : Set A∞)) ∧
      Ideal.span (↑t : Set S∞) = ⊤ := by
  classical
  let sI : Set A∞ := ⋃ i, (Ideal.map (ι∞ i) (I i) : Set A∞)
  have hsI : Ideal.span sI = I∞ := by
    -- The limit ideal is the supremum of the stagewise ideal images, and each summand is already
    -- equal to the span of its underlying set.
    calc
      Ideal.span sI = ⨆ i, Ideal.span ((Ideal.map (ι∞ i) (I i) : Ideal A∞) : Set A∞) := by
        simpa [sI] using
          (Ideal.span_iUnion
            (s := fun i : Λ ↦ ((Ideal.map (ι∞ i) (I i) : Ideal A∞) : Set A∞)))
      _ = ⨆ i, Ideal.map (ι∞ i) (I i) := by
        simp only [Ideal.span_eq]
      _ = I∞ := rfl
  have hspan_union' :
      Ideal.span (Set.range fInf ∪ (algebraMap A∞ S∞) '' sI) = ⊤ := by
    -- Work with the frozen set alias `sI`; the final statement is recovered by `simpa [sI]`.
    calc
      Ideal.span (Set.range fInf ∪ (algebraMap A∞ S∞) '' sI) =
          Ideal.span (Set.range fInf) ⊔
            Ideal.span ((algebraMap A∞ S∞) '' sI) := by
              rw [Ideal.span_union]
      _ = Ideal.span (Set.range fInf) ⊔
            Ideal.map (algebraMap A∞ S∞) (Ideal.span sI) := by
              rw [← Ideal.map_span]
      _ = Ideal.span (Set.range fInf) ⊔ Ideal.map (algebraMap A∞ S∞) I∞ := by
            rw [hsI]
      _ = ⊤ := by
            simpa using hcover
  have hspan_union :
      Ideal.span (Set.range fInf ∪ (algebraMap A∞ S∞) '' (I∞ : Set A∞)) = ⊤ := by
    -- Re-express the original union with the frozen ideal-set alias and reuse the normalized
    -- calculation above.
    simpa [sI] using hspan_union'
  exact (Ideal.span_eq_top_iff_finite _).mp hspan_union

/-- Helper for Lemma 15.18.3: a finite span equal to the top ideal yields the explicit unit
relation needed for stagewise cover descent. -/
lemma one_mem_span_of_span_eq_top
    {T : Type*} [CommRing T] (t : Finset T)
    (htTop : Ideal.span (↑t : Set T) = ⊤) :
    (1 : T) ∈ Ideal.span (↑t : Set T) := by
  -- Repackage the equality with `⊤` as the concrete `1 ∈ span(t)` witness used later.
  simpa [Ideal.eq_top_iff_one] using htTop

/-- Helper for Lemma 15.18.3: a prime of `T` lies in the basic open `D(g)` exactly when it is
the contraction of a prime of the away localization `T_g`. -/
lemma mem_basicOpen_iff_exists_prime_localizationAway
    {T : Type*} [CommRing T] (g : T) (p : PrimeSpectrum T) :
    p ∈ (basicOpen g : Set (PrimeSpectrum T)) ↔
      ∃ q : PrimeSpectrum (Localization.Away g),
        PrimeSpectrum.comap (algebraMap T (Localization.Away g)) q = p := by
  constructor
  · intro hp
    -- Rewrite `D(g)` as the image of the spectrum map induced by the away localization.
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hp
    rcases hp with ⟨q, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    -- A contracted prime from `Spec(T_g)` lands in that image by construction.
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact Set.mem_range_self q

/-- Helper for Lemma 15.18.3: the contraction of a prime of `Spec(T_g)` always lies in the
basic open `D(g)`. -/
lemma comap_localizationAway_mem_basicOpen
    {T : Type*} [CommRing T] (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway ∈
      (basicOpen g : Set (PrimeSpectrum T)) := by
  -- Rewrite `D(g)` as the image of the spectrum map induced by the away localization.
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
  exact Set.mem_range_self qAway

/-- Helper for Lemma 15.18.3: if a prime of `T` lies in `D(g)`, then every power of `g` avoids
that prime. -/
lemma powers_le_primeCompl_of_mem_basicOpen
    {T : Type*} [CommRing T] {g : T} {q : PrimeSpectrum T}
    (hq : q ∈ (basicOpen g : Set (PrimeSpectrum T))) :
    Submonoid.powers g ≤ q.asIdeal.primeCompl := by
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact q.asIdeal.primeCompl.pow_mem ((PrimeSpectrum.mem_basicOpen g q).1 hq) n

/-- Helper for Lemma 15.18.3: after contracting `qAway : Spec(T_g)` back to `Spec(T)`, the two
local rings `(T_g)_{qAway}` and `T_q` are canonically identified. -/
noncomputable abbrev away_atPrime_algEquiv
    {T : Type*} [CommRing T] (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal ≃ₐ[T]
      Localization.AtPrime qAway.asIdeal :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers g) qAway.asIdeal

/-- Helper for Lemma 15.18.3: the universal property of `N[g⁻¹]` gives the canonical `T`-linear
map from the away localization to the prime localization `N_q`, where `q` is the contraction of a
prime `qAway` of `Spec(T_g)`. -/
noncomputable def away_to_atPrime_linearMap
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    LocalizedModule.Away g N →ₗ[T]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N :=
  let q : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway
  let hpow : Submonoid.powers g ≤ q.asIdeal.primeCompl :=
    powers_le_primeCompl_of_mem_basicOpen (q := q)
      (comap_localizationAway_mem_basicOpen (T := T) g qAway)
  -- Normalize the comparison as the canonical map between two module localizations.
  LocalizedModule.liftOfLE (Submonoid.powers g) q.asIdeal.primeCompl hpow

/-- Helper for Lemma 15.18.3: the canonical away-to-at-prime comparison sends a standard fraction
`m / s` to the same fraction in the prime localization after viewing `s` in `qᶜ`. -/
lemma away_to_atPrime_linearMap_apply_mk
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g))
    (m : N) (s : Submonoid.powers g) :
    away_to_atPrime_linearMap (T := T) (N := N) g qAway (LocalizedModule.mk m s) =
      IsLocalizedModule.mk'
        (LocalizedModule.mkLinearMap
          (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl N)
        m
        ⟨s.1,
          (powers_le_primeCompl_of_mem_basicOpen
            (q := PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway)
            (comap_localizationAway_mem_basicOpen (T := T) g qAway)) s.2⟩ := by
  -- Reduce the comparison map to the canonical `liftOfLE` formula on localized generators.
  simp only [away_to_atPrime_linearMap, IsLocalizedModule.mk_eq_mk',
    IsLocalizedModule.liftOfLE_mk']

/-- Helper for Lemma 15.18.3: on the denominator-`1` generators of `N[g⁻¹]`, the canonical
away-to-at-prime comparison is exactly the prime-localization map from `N`. -/
lemma away_to_atPrime_linearMap_apply_mk_one
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g))
    (m : N) :
    away_to_atPrime_linearMap (T := T) (N := N) g qAway (LocalizedModule.mk m 1) =
      LocalizedModule.mkLinearMap
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl N m := by
  -- Evaluate the comparison on the standard generator `m / 1` and simplify the trivial
  -- denominator on the target prime localization.
  rw [away_to_atPrime_linearMap_apply_mk]
  simpa [LocalizedModule.mkLinearMap_apply] using
    (IsLocalizedModule.mk'_one
      (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl
      (LocalizedModule.mkLinearMap
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl N)
      m)

/-- Helper for Lemma 15.18.3: the away-to-at-prime comparison extends the canonical localization
map from `N` to the prime localization `N_q`. -/
lemma away_to_atPrime_linearMap_comp_mkLinearMap
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    (away_to_atPrime_linearMap (T := T) (N := N) g qAway).comp
        (LocalizedModule.mkLinearMap (Submonoid.powers g) N) =
      LocalizedModule.mkLinearMap
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl N := by
  -- Compare the two `T`-linear maps on the original module `N`; both send `m` to the same
  -- denominator-`1` class in the target localization.
  ext m
  simpa using away_to_atPrime_linearMap_apply_mk_one (T := T) (N := N) g qAway m

/-- Helper for Lemma 15.18.3: the local ring `N_q` inherits a canonical `T_g`-module structure
through the iterated-localization ring equivalence. -/
private noncomputable instance away_atPrime_targetModule
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    Module (Localization.Away g)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
  Module.compHom _
    (((away_atPrime_algEquiv (T := T) g qAway).symm.toRingHom).comp
      (algebraMap (Localization.Away g) (Localization.AtPrime qAway.asIdeal)))

/-- Helper for Lemma 15.18.3: the contracted-prime localization target carries the canonical
`(T_g)_{qAway}`-module structure transported across the iterated-localization ring equivalence. -/
private noncomputable instance away_atPrime_targetAtPrimeModule
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    Module (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
  Module.compHom _
    (away_atPrime_algEquiv (T := T) g qAway).symm.toRingHom

/-- Helper for Lemma 15.18.3: the transported `(T_g)_{qAway}`-action on the contracted-prime
localization target extends its canonical `T_g`-action. -/
private noncomputable instance away_atPrime_target_isScalarTower_over_localized_base
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    IsScalarTower (Localization.Away g) (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) := by
  let e := away_atPrime_algEquiv (T := T) g qAway
  let _ : Module (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_targetAtPrimeModule (T := T) (N := N) g qAway
  let _ : Module (Localization.Away g)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_targetModule (T := T) (N := N) g qAway
  -- Both scalar actions are defined through the same iterated-localization comparison ring map.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro z m
  change e.symm (algebraMap (Localization.Away g) (Localization.AtPrime qAway.asIdeal) z) • m =
    z • m
  rfl

/-- Helper for Lemma 15.18.3: after transporting the codomain actions, the identity map on the
contracted-prime localization target is already the owner localization map over `T_g`. -/
private noncomputable instance away_atPrime_target_id_isLocalizedModule_over_localized_base
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    IsLocalizedModule qAway.asIdeal.primeCompl
      (LinearMap.id :
        LocalizedModule.AtPrime
            (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N →ₗ[Localization.Away g]
          LocalizedModule.AtPrime
            (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) := by
  let _ : Module (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_targetAtPrimeModule (T := T) (N := N) g qAway
  let _ : IsScalarTower (Localization.Away g) (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_target_isScalarTower_over_localized_base (T := T) (N := N) g qAway
  -- The target already carries the localization-ring action, so the identity map is the correct
  -- owner-level localization witness.
  simpa using
    (isLocalizedModule_id qAway.asIdeal.primeCompl
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N)
      (Localization.AtPrime qAway.asIdeal))

/-- Helper for Lemma 15.18.3: the canonical away-to-at-prime comparison is already linear over
the localized base ring `T_g` after upgrading the codomain scalar action from `T` to `T_g`. -/
private noncomputable abbrev away_to_atPrime_linearMap_over_localized_base
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    LocalizedModule.Away g N →ₗ[Localization.Away g]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N :=
  -- TODO: recover the missing `IsScalarTower T (Localization.Away g) (...)` bridge for the
  -- transported target module and then upgrade `away_to_atPrime_linearMap` via
  -- `LinearMap.extendScalarsOfIsLocalizationEquiv`.
  sorry

/-- Helper for Lemma 15.18.3: upgrading the away-to-at-prime comparison to the localized base
ring `T_g` does not change its value on denominator-`1` generators. -/
private lemma away_to_atPrime_linearMap_over_localized_base_apply_mk_one
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g))
    (m : N) :
    away_to_atPrime_linearMap_over_localized_base (T := T) (N := N) g qAway
      (LocalizedModule.mk m 1) =
      LocalizedModule.mkLinearMap
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal.primeCompl N m := by
  -- TODO: once the localized-base linear map is restored, this is the denominator-`1`
  -- computation inherited from `away_to_atPrime_linearMap_apply_mk_one`.
  sorry

/-- Helper for Lemma 15.18.3: the upgraded away-to-at-prime comparison is the actual
`Localization.Away g`-localization map of `LocalizedModule.Away g N` at the prime `qAway`. -/
private lemma away_to_atPrime_isLocalizedModule_over_localized_base
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    IsLocalizedModule qAway.asIdeal.primeCompl
      (away_to_atPrime_linearMap_over_localized_base (T := T) (N := N) g qAway) := by
  -- TODO: prove the owner-localization axioms once the localized-base comparison map is restored;
  -- the missing steps are target-denominator surjectivity and source-equality clearing.
  sorry

/-- Helper for Lemma 15.18.3: localizing the away-localized module at a prime of `Spec(T_g)`
agrees with localizing the original module at the corresponding prime of `Spec(T)`, first over the
owner ring `T_g`. -/
noncomputable def away_atPrime_linear_equiv_over_localized_base
    {T : Type*} {N : Type*}
    [CommRing T]
    [AddCommGroup N] [Module T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    LocalizedModule.AtPrime qAway.asIdeal (LocalizedModule.Away g N) ≃ₗ[Localization.Away g]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N := by
  -- TODO: once `away_to_atPrime_isLocalizedModule_over_localized_base` is proved, this is the
  -- universal `IsLocalizedModule.linearEquiv`.
  sorry

/-- Helper for Lemma 15.18.3: after transporting along the iterated-localization ring
identification, the base-prime local ring map through `T_g` is exactly the canonical local ring
map to `T_q`. -/
lemma away_atPrime_base_localRingHom_comp_eq
    {A : Type*} {T : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    let q : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway
    ((away_atPrime_algEquiv (T := T) g qAway).symm.toRingHom).comp
        (Localization.localRingHom
          (qAway.asIdeal.under A) qAway.asIdeal (algebraMap A (Localization.Away g)) rfl) =
      Localization.localRingHom
        (qAway.asIdeal.under A) q.asIdeal (algebraMap A T) rfl := by
  -- TODO: identify the transported local-ring map with the canonical one by uniqueness of
  -- `Localization.localRingHom` after normalizing both composites on `A`.
  sorry

/-- Helper for Lemma 15.18.3: after transporting the codomain along the iterated-localization
ring equivalence, it inherits the base-prime action coming from the canonical map
`A_(qAway ∩ A) → (T_g)_{qAway}`. -/
private noncomputable instance away_atPrime_targetBaseAtPrimeModule
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    Module (Localization.AtPrime (qAway.asIdeal.under A))
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
  Module.compHom _
    (((away_atPrime_algEquiv (T := T) g qAway).symm.toRingHom).comp
      (Localization.localRingHom
        (qAway.asIdeal.under A) qAway.asIdeal (algebraMap A (Localization.Away g)) rfl))

/-- Helper for Lemma 15.18.3: the transported base-prime action on the codomain is compatible
with its `(T_g)_{qAway}`-action. -/
private noncomputable instance away_atPrime_target_isScalarTower_over_base_atPrime
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    IsScalarTower (Localization.AtPrime (qAway.asIdeal.under A))
      (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) := by
  let e := away_atPrime_algEquiv (T := T) g qAway
  let _ : Module (Localization.AtPrime qAway.asIdeal)
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_targetAtPrimeModule (T := T) (N := N) g qAway
  let _ : Module (Localization.AtPrime (qAway.asIdeal.under A))
      (LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N) :=
    away_atPrime_targetBaseAtPrimeModule (A := A) (T := T) (N := N) g qAway
  -- Both actions are defined through the same composite into `T_q`, so the tower relation is
  -- definitionally the transported scalar action.
  refine IsScalarTower.of_algebraMap_smul ?_
  intro z m
  change e.symm ((Localization.localRingHom
    (qAway.asIdeal.under A) qAway.asIdeal (algebraMap A (Localization.Away g)) rfl) z) • m =
    z • m
  rfl

/-- Helper for Lemma 15.18.3: the iterated-localization comparison is already linear over the
contracted base-prime localization `A_(qAway ∩ A)`. -/
noncomputable def away_atPrime_linear_equiv_over_base_atPrime
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    LocalizedModule.AtPrime qAway.asIdeal (LocalizedModule.Away g N) ≃ₗ[
        Localization.AtPrime (qAway.asIdeal.under A)]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N := by
  -- TODO: extend scalars from `T_g` to `(T_g)_{qAway}` and then transport the base-prime action
  -- using `away_atPrime_base_localRingHom_comp_eq`.
  sorry

/-- Helper for Lemma 15.18.3: localizing the away-localized module at a prime of `Spec(T_g)`
agrees with localizing the original module at the corresponding prime of `Spec(T)`. -/
noncomputable def away_atPrime_linear_equiv
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    (g : T) (qAway : PrimeSpectrum (Localization.Away g)) :
    LocalizedModule.AtPrime qAway.asIdeal (LocalizedModule.Away g N) ≃ₗ[A]
      LocalizedModule.AtPrime
        (PrimeSpectrum.comap (algebraMap T (Localization.Away g)) qAway).asIdeal N := by
  -- TODO: forget scalars along `A → A_(qAway ∩ A)` once the base-at-prime comparison is proved.
  sorry

/-- Helper for Lemma 15.18.3: if a principal basic open lies in the flat-over-base locus, then
the corresponding away localization of the module is flat over the base ring. -/
lemma flat_localizedAway_of_basicOpen_subset_flatOverBaseLocus
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    [Algebra.FinitePresentation A T] [Module.FinitePresentation T N]
    (g : T)
    (hbasic :
      (basicOpen g : Set (PrimeSpectrum T)) ⊆ Module.flatOverBaseLocus A T N) :
    Module.Flat A (LocalizedModule.Away g N) := by
  -- TODO: this is the primewise transport of flatness across
  -- `away_atPrime_linear_equiv_over_base_atPrime`.
  sorry

/-- Helper for Lemma 15.18.3: flatness of the away localization implies that the corresponding
principal basic open lies in the flat-over-base locus. -/
lemma basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    [Algebra.FinitePresentation A T] [Module.FinitePresentation T N]
    (g : T)
    (hflat : Module.Flat A (LocalizedModule.Away g N)) :
    (basicOpen g : Set (PrimeSpectrum T)) ⊆ Module.flatOverBaseLocus A T N := by
  -- TODO: this is the converse primewise transport once the iterated-localization comparison is
  -- available over the contracted base prime.
  sorry

/-- Helper for Lemma 15.18.3: once the limit-side away localizations at finitely many generators
are flat, they become simultaneously flat at one sufficiently large stage above the chosen lifts.
-/
lemma exists_common_stage_flat_localizedAway_family_above
    {n : ℕ} {i : Λ} (fInf : Fin n → S∞) (fi : Fin n → S[i])
    (hfi : ∀ a, tensorBaseChangeToLimit (A := A) (φ := φ) i (fi a) = fInf a)
    (hflatInf : ∀ a, Module.Flat A∞ (LocalizedModule.Away (fInf a) M∞)) :
    ∃ j : Λ, ∃ hij : i ≤ j,
      ∀ a, Module.Flat (A j)
        (LocalizedModule.Away
          (tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a)) M[j]) := by
  -- TODO: package the tail system of away localizations above `i` into the approximation object
  -- expected by `eventually_flat_stageModules_of_flat_limit`, prove eventual flatness for each
  -- fixed generator, and then synchronize the finitely many resulting lower bounds.
  let _ := hfi
  let _ := hflatInf
  sorry

/-- Helper for Lemma 15.18.3: the finite limit-side unit relation can be descended to one stage
above a prescribed lower bound, yielding the unit-ideal cover relation needed for the final basic
open argument. -/
lemma exists_stage_cover_relation_above
    {n : ℕ} {i j₀ : Λ} (hij₀ : i ≤ j₀) (fi : Fin n → S[i]) (t : Finset S∞)
    (ht_membership :
      ∀ x ∈ (↑t : Set S∞),
        x ∈ Set.range (fun a ↦ tensorBaseChangeToLimit (A := A) (φ := φ) i (fi a)) ∨
          x ∈ (algebraMap A∞ S∞) '' (I∞ : Set A∞))
    (hOne : (1 : S∞) ∈ Ideal.span (↑t : Set S∞)) :
    ∃ j : Λ, ∃ hj₀j : j₀ ≤ j,
      Ideal.span
          (Set.range
            (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j
              (le_trans hij₀ hj₀j) (fi a))) +
        Ideal.map (algebraMap (A j) S[j]) (I j) = ⊤ := by
  -- TODO: descend the finitely many coefficients in the span expression for `1`, descend the
  -- finitely many ideal-side witnesses using
  -- `exists_common_stage_mem_directLimit_ideal_of_stage_family_above`, and then apply
  -- `Ring.DirectLimit.of.zero_exact` to obtain a stage equality certifying the unit ideal.
  let _ := ht_membership
  let _ := hOne
  sorry

/-- Helper for Lemma 15.18.3: once the stagewise mixed cover relation is the unit ideal,
pushing it forward to any later stage keeps it equal to the unit ideal. -/
lemma stage_cover_relation_persists_above
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    {n : ℕ} {i j : Λ} (hij : i ≤ j) (fi : Fin n → S[i])
    (hTopi :
      Ideal.span (Set.range fi) + Ideal.map (algebraMap (A i) S[i]) (I i) = ⊤) :
    Ideal.span
        (Set.range
          (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) +
      Ideal.map (algebraMap (A j) S[j]) (I j) = ⊤ := by
  let τ : S[i] →+* S[j] := (tensorBaseChangeMap (A := A) (φ := φ) (S := S) i j hij).toRingHom
  have hmap_le :
      Ideal.map τ (Ideal.span (Set.range fi) + Ideal.map (algebraMap (A i) S[i]) (I i)) ≤
        Ideal.span
            (Set.range
              (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) +
          Ideal.map (algebraMap (A j) S[j]) (I j) := by
    rw [Ideal.add_eq_sup, Ideal.map_sup]
    refine sup_le ?_ ?_
    · -- Push the span summand forward and identify its image with the span of the transported
      -- generators.
      calc
        Ideal.map τ (Ideal.span (Set.range fi)) =
            Ideal.span (τ '' Set.range fi) := by
              rw [Ideal.map_span]
        _ ≤ Ideal.span
              (Set.range
                (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) := by
              refine Ideal.span_le.2 ?_
              rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
              exact Ideal.subset_span ⟨a, rfl⟩
        _ ≤
            Ideal.span
                (Set.range
                  (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) +
              Ideal.map (algebraMap (A j) S[j]) (I j) := le_sup_left
    · -- The ideal summand persists by the compatibility hypothesis on the stage ideals.
      calc
        Ideal.map τ (Ideal.map (algebraMap (A i) S[i]) (I i)) =
            Ideal.map (τ.comp (algebraMap (A i) S[i])) (I i) := by
              simpa using
                (Ideal.map_map (algebraMap (A i) S[i]) τ (I := I i))
        _ =
            Ideal.map ((algebraMap (A j) S[j]).comp (φ i j hij)) (I i) := by
              congr 1
        _ = Ideal.map (algebraMap (A j) S[j]) (Ideal.map (φ i j hij) (I i)) := by
              symm
              simpa using
                (Ideal.map_map (φ i j hij).toRingHom (algebraMap (A j) S[j]) (I := I i))
        _ ≤ Ideal.map (algebraMap (A j) S[j]) (I j) := Ideal.map_mono (hI hij)
        _ ≤
            Ideal.span
                (Set.range
                  (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) +
              Ideal.map (algebraMap (A j) S[j]) (I j) := le_sup_right
  have hmap_top :
      Ideal.map τ (Ideal.span (Set.range fi) + Ideal.map (algebraMap (A i) S[i]) (I i)) = ⊤ := by
    -- Apply the stage transition to the unit-ideal relation at stage `i`.
    simpa [hTopi] using (Ideal.map_top τ)
  have htop_le :
      (⊤ : Ideal S[j]) ≤
        Ideal.span
            (Set.range
              (fun a ↦ tensorBaseChangeMap (A := A) (φ := φ) i j hij (fi a))) +
          Ideal.map (algebraMap (A j) S[j]) (I j) := by
    rw [← hmap_top]
    exact hmap_le
  exact top_le_iff.mp htop_le

/-- Helper for Lemma 15.18.3: once finitely many basic opens in the flat-over-base locus cover
the closed subset cut out by `J`, the whole closed subset lies in the flat locus. -/
lemma zeroLocus_subset_flatOverBaseLocus_of_basicOpen_cover
    {A : Type*} {T : Type*} {N : Type*}
    [CommRing A] [CommRing T] [Algebra A T]
    [AddCommGroup N] [Module T N] [Module A N] [IsScalarTower A T N]
    {n : ℕ} (f : Fin n → T) (J : Ideal T)
    (hbasic :
      ∀ a, (basicOpen (f a) : Set (PrimeSpectrum T)) ⊆ Module.flatOverBaseLocus A T N)
    (hspan : Ideal.span (Set.range f) + J = ⊤) :
    zeroLocus (J : Set T) ⊆ Module.flatOverBaseLocus A T N := by
  intro q hq
  by_contra hqflat
  have hJq : J ≤ q.asIdeal := (mem_zeroLocus q (J : Set T)).1 hq
  have hspan_range : Ideal.span (Set.range f) ≤ q.asIdeal := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    -- If `f a ∉ q`, then `q ∈ D(f a)` and the assumed basic-open containment forces flatness.
    by_contra hfa
    have hqbasic : q ∈ (basicOpen (f a) : Set (PrimeSpectrum T)) :=
      (PrimeSpectrum.mem_basicOpen (f a) q).2 hfa
    exact hqflat (hbasic a hqbasic)
  have htop_le : (⊤ : Ideal T) ≤ q.asIdeal := by
    rw [← hspan]
    exact sup_le hspan_range hJq
  exact q.2.ne_top (top_le_iff.mp htop_le)

-- Proof sketch: apply openness of the flat locus for finitely presented modules after base
-- change, cover the closed set cut out by the colimit ideal by finitely many basic opens on which
-- the base-changed module is flat, then descend the finitely many elements and their flatness data
-- to some sufficiently large stage using finite presentation and the directed-colimit hypotheses.
/-- Lemma 15.18.3: if the canonical closed-subset inclusion `(15.18.0.1)` holds for the base
change of `(R → S, M)` to the direct limit of a directed system of `R`-algebras and for the
colimit ideal of a compatible family of stage ideals, then the same inclusion already holds after
base change to some stage. -/
@[stacks 05LM]
theorem exists_stage_zeroLocus_subset_flatOverBaseLocus_of_direct_limit_base_change
    (hI : ∀ ⦃i j⦄, (hij : i ≤ j) → Ideal.map (ρ i j hij) (I i) ≤ I j)
    (hflat_inf :
      zeroLocus (Ideal.map (algebraMap A∞ S∞) I∞ : Set S∞) ⊆
        Module.flatOverBaseLocus A∞ S∞ M∞) :
    ∃ i : Λ,
      zeroLocus (Ideal.map (algebraMap (A i) S[i]) (I i) : Set S[i]) ⊆
        Module.flatOverBaseLocus (A i) S[i] M[i] := by
  -- Route correction: instead of trying to descend the limit-side open containment directly, first
  -- extract the finite basic-open cover on the limit side and then descend only its finite
  -- algebraic witnesses.
  letI : Algebra.FinitePresentation A∞ S∞ :=
    (finitePresentation_tensorBaseChange (R := R) (S := S) (M := M) A∞).1
  letI : Module.FinitePresentation S∞ M∞ :=
    (finitePresentation_tensorBaseChange (R := R) (S := S) (M := M) A∞).2
  obtain ⟨n, fInf, hbasicInf, hcoverInf⟩ :=
    exists_finite_basicOpen_cover_of_zeroLocus_subset_flatOverBaseLocus
      (A := A∞) (T := S∞) (N := M∞)
      (Ideal.map (algebraMap A∞ S∞) I∞) hflat_inf
  obtain ⟨i, fi, hfi⟩ :=
    exists_common_stage_lifts_of_finite_limit_family (A := A) (φ := φ) (fInf := fInf)
  obtain ⟨t, htSub, htTop⟩ :=
    exists_finite_mixed_generating_family_of_cover
      (A := A) (φ := φ) (I := I) (fInf := fInf) hcoverInf
  have hOneInf : (1 : S∞) ∈ Ideal.span (↑t : Set S∞) := by
    -- The cover part is now normalized to the explicit unit relation required by the source
    -- proof's final finite descent step.
    exact one_mem_span_of_span_eq_top t htTop
  have ht_membership :
      ∀ x ∈ (↑t : Set S∞),
        x ∈ Set.range fInf ∨ x ∈ (algebraMap A∞ S∞) '' (I∞ : Set A∞) := by
    intro x hx
    exact htSub hx
  have ht_membership_stage :
      ∀ x ∈ (↑t : Set S∞),
        x ∈ Set.range (fun a ↦ tensorBaseChangeToLimit (A := A) (φ := φ) i (fi a)) ∨
          x ∈ (algebraMap A∞ S∞) '' (I∞ : Set A∞) := by
    intro x hx
    rcases ht_membership x hx with hxRange | hxIdeal
    · rcases hxRange with ⟨a, rfl⟩
      exact Or.inl ⟨a, hfi a⟩
    · exact Or.inr hxIdeal
  have hflatAwayInf :
      ∀ a, Module.Flat A∞ (LocalizedModule.Away (fInf a) M∞) := by
    -- Convert each limit-side basic-open inclusion into the corresponding away-localized flatness
    -- statement, which is the input expected by the stagewise descent helper.
    intro a
    exact flat_localizedAway_of_basicOpen_subset_flatOverBaseLocus (A := A∞) (T := S∞)
      (N := M∞) (g := fInf a) (hbasicInf a)
  -- First descend the finitely many away-localized flatness statements to one common stage.
  obtain ⟨j, hij, hflatAwayj⟩ :=
    exists_common_stage_flat_localizedAway_family_above
      (A := A) (φ := φ) (fInf := fInf) (i := i) (fi := fi) hfi hflatAwayInf
  -- Next descend the explicit unit-ideal cover relation to a later stage above that flatness
  -- stage.
  obtain ⟨k, hjk, hcoverk⟩ :=
    exists_stage_cover_relation_above
      (A := A) (φ := φ) (I := I) (hij₀ := hij) (fi := fi) t ht_membership_stage hOneInf
  let fk : Fin n → S[k] := fun a ↦
    tensorBaseChangeMap (A := A) (φ := φ) i k (le_trans hij hjk) (fi a)
  have hfk :
      ∀ a, tensorBaseChangeToLimit (A := A) (φ := φ) k (fk a) = fInf a := by
    intro a
    -- The stage-`k` representatives still lift the original limit-side generators.
    calc
      tensorBaseChangeToLimit (A := A) (φ := φ) k (fk a) =
          tensorBaseChangeToLimit (A := A) (φ := φ) i (fi a) := by
            simpa [fk] using
              (tensorBaseChange_toLimit_comp_stageMap
                (A := A) (φ := φ) i k (le_trans hij hjk) (fi a))
      _ = fInf a := hfi a
  -- Re-synchronize the away-flatness descent above the cover stage `k`.
  obtain ⟨l, hkl, hflatAwayl⟩ :=
    exists_common_stage_flat_localizedAway_family_above
      (A := A) (φ := φ) (fInf := fInf) (i := k) (fi := fk) hfk hflatAwayInf
  let fl : Fin n → S[l] := fun a ↦
    tensorBaseChangeMap (A := A) (φ := φ) k l hkl (fk a)
  letI : Algebra.FinitePresentation (A l) S[l] :=
    (finitePresentation_tensorBaseChange (R := R) (S := S) (M := M) (A l)).1
  letI : Module.FinitePresentation S[l] M[l] :=
    (finitePresentation_tensorBaseChange (R := R) (S := S) (M := M) (A l)).2
  have hbasicl :
      ∀ a,
        (basicOpen (fl a) : Set (PrimeSpectrum S[l])) ⊆
          Module.flatOverBaseLocus (A l) S[l] M[l] := by
    intro a
    -- Convert the synchronized away-localized flatness back into the basic-open containment at
    -- stage `l`.
    simpa [fl] using
      (basicOpen_subset_flatOverBaseLocus_of_flat_localizedAway
        (A := A l) (T := S[l]) (N := M[l]) (g := fl a) (hflatAwayl a))
  have hcoverl :
      Ideal.span (Set.range fl) + Ideal.map (algebraMap (A l) S[l]) (I l) = ⊤ := by
    -- Push the stage-`k` cover relation forward to the same stage `l`.
    simpa [fk, fl] using
      (stage_cover_relation_persists_above
        (A := A) (φ := φ) (I := I) hI hkl fk hcoverk)
  refine ⟨l, ?_⟩
  -- With a finite basic-open cover inside the flat locus and the descended cover relation at the
  -- same stage, the stagewise closed subset lies in the flat-over-base locus.
  exact
    zeroLocus_subset_flatOverBaseLocus_of_basicOpen_cover
      (A := A l) (T := S[l]) (N := M[l]) (f := fl)
      (J := Ideal.map (algebraMap (A l) S[l]) (I l))
      hbasicl hcoverl

end

end DirectLimitDescent
