import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_81_1 (from Chap10) -/
universe u v

section

open LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.81.1: transport the kernel-factorization criterion from
`Fin n → R` to `Fin n →₀ R` along `Finsupp.linearEquivFunOnFinite`. -/
lemma finsupp_kernel_factorization_of_pi_kernel_factorization
    (h :
      ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
        f x = 0 →
          ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
            f = g ∘ₗ h' ∧ h' x = 0) :
    ∀ ⦃n : ℕ⦄ (f : (Fin n →₀ R) →ₗ[R] M) (x : Fin n →₀ R),
      f x = 0 →
        ∃ (m : ℕ) (h' : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ h' x = 0 := by
  intro n f x hx
  let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R := Finsupp.linearEquivFunOnFinite R R (Fin n)
  -- Move the problem to the function model `Fin n → R`, where the hypothesis applies directly.
  obtain ⟨m, h', g, hfactor, hx'⟩ :=
    h (f ∘ₗ e.symm.toLinearMap) (e x) (by simpa [e] using hx)
  use m
  use h' ∘ₗ e.toLinearMap
  use g
  constructor
  · -- Postcompose the transported factorization with `e` to return to the `Finsupp` domain.
    simpa [LinearMap.comp_assoc] using congrArg (fun φ => φ ∘ₗ e.toLinearMap) hfactor
  · simpa [e] using hx'

/-- Helper for Lemma 10.81.1: the `Fin n → R` factorization criterion implies flatness by
transporting it to mathlib's `Finsupp`-based equational criterion. -/
lemma flat_of_pi_kernel_factorization
    (h :
      ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
        f x = 0 →
          ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
            f = g ∘ₗ h' ∧ h' x = 0) :
    Module.Flat R M := by
  have hFinsupp :=
    finsupp_kernel_factorization_of_pi_kernel_factorization (R := R) (M := M) h
  -- After transport, the owner flatness criterion closes the argument.
  exact Module.Flat.of_forall_exists_factorization fun {l} {f} {x} hx ↦ hFinsupp x f hx

/-- Helper for Lemma 10.81.1: clause (3) lets one kill the span of any finite family of kernel
elements by adjoining those generators one at a time. -/
lemma exists_factorization_killing_span_finset
    (h :
      ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R))
        (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
        N ≤ ker f →
          N ≤ ker h' →
          (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h') →
          ∀ x : Fin n → R,
            f x = 0 →
              ∃ (m' : ℕ) (h'' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h'' ∧
                  ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h'') :
    ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (s : Finset (Fin n → R)),
      (∀ x ∈ s, f x = 0) →
        ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ Submodule.span R (s : Set (Fin n → R)) ≤ ker h' := by
  classical
  intro n f s hs
  induction s using Finset.induction with
  | empty =>
      let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R := Finsupp.linearEquivFunOnFinite R R (Fin n)
      -- The empty generating set is handled by the canonical equivalence with the free `Finsupp`.
      use n
      use e.symm.toLinearMap
      use f ∘ₗ e.toLinearMap
      constructor
      · ext x
        simp [e]
      · simpa
  | insert x s hx_not_mem ih =>
      have hs_tail : ∀ y ∈ s, f y = 0 := by
        intro y hy
        exact hs y (Finset.mem_insert_of_mem hy)
      obtain ⟨m, h', g, hfactor, hkill⟩ := ih hs_tail
      have hspan_ker_f : Submodule.span R (s : Set (Fin n → R)) ≤ ker f := by
        rw [hfactor]
        exact hkill.trans (LinearMap.ker_le_ker_comp h' g)
      have hx_zero : f x = 0 := hs x (Finset.mem_insert_self x s)
      -- Refine the current factorization so that it also kills the new generator `x`.
      obtain ⟨m', h'', hsup, g', hfactor'⟩ :=
        h f (Submodule.span R (s : Set (Fin n → R))) h' hspan_ker_f hkill ⟨g, hfactor⟩ x hx_zero
      use m'
      use h''
      use g'
      constructor
      · exact hfactor'
      · -- Rewriting `span (insert x s)` as `span s + Rx` matches the output of clause (3).
        rw [Finset.coe_insert, Submodule.span_insert]
        simpa [Submodule.add_eq_sup, sup_comm] using hsup

-- Proof sketch: clause (1) is the equational criterion `Module.Flat.iff_forall_isTrivialRelation`
-- rewritten for maps out of finite free modules. Clause (2) implies clause (3) by factoring the
-- intermediate map `g` further to kill `h x`. Clause (3) implies clause (4) by induction on a
-- finite set of generators of `N`, adjoining one generator at a time. Clause (4) implies clause
-- (2) by taking `N = ⊥`.
/-- Lemma 10.81.1: for an `R`-module `M`, the following are equivalent: `M` is flat; every kernel
element of a map `R^n → M` can be killed after factoring through some finite free module; a
factorization that kills a submodule `N` can be refined to kill `N + Rx` for any additional kernel
element `x`; and every finitely generated submodule of such a kernel can be killed by a
factorization through a finite free module. -/
theorem flat_tfae_kernel_factorization_criterion :
    List.TFAE
      [ Module.Flat R M,
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
          f x = 0 →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ h x = 0,
        ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R))
          (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
          N ≤ ker f →
            N ≤ ker h →
            (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h) →
            ∀ x : Fin n → R,
              f x = 0 →
                ∃ (m' : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                  N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h' ∧
                    ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h',
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R)),
          N ≤ ker f →
            N.FG →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ N ≤ ker h ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hflat n f x hx
      letI : Module.Flat R M := hflat
      -- The forward direction is the owner equational criterion for finite free modules.
      simpa using
        (Module.Flat.exists_factorization_of_apply_eq_zero_of_free
          (R := R) (M := M) (N := Fin n → R) (f := x) (x := f) hx)
    · intro h
      -- Transport clause (2) to mathlib's `Finsupp` formulation of flatness.
      exact flat_of_pi_kernel_factorization (R := R) (M := M) h
  tfae_have 2 → 3 := by
    intro h n m f N h' hNkerf hNkerh hfactor x hx
    have hFinsupp :=
      finsupp_kernel_factorization_of_pi_kernel_factorization (R := R) (M := M) h
    obtain ⟨g, hg⟩ := hfactor
    -- Factor the intermediate map `g` further so that the image of `x` is also killed.
    obtain ⟨m', h'', g', hg', hhx⟩ :=
      hFinsupp g (h' x) (by simpa [hg, LinearMap.comp_apply] using hx)
    use m'
    use h'' ∘ₗ h'
    constructor
    · -- The new map kills both the old submodule `N` and the extra generator `x`.
      rw [Submodule.add_eq_sup]
      refine sup_le ?_ ?_
      · exact hNkerh.trans (LinearMap.ker_le_ker_comp h' h'')
      · have hxker : x ∈ ker (h'' ∘ₗ h') := by
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hhx
        refine Submodule.span_le.2 ?_
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hxker
    · use g'
      calc
        f = g ∘ₗ h' := hg
        _ = (g' ∘ₗ h'') ∘ₗ h' := by rw [hg']
        _ = g' ∘ₗ (h'' ∘ₗ h') := by rw [LinearMap.comp_assoc]
  tfae_have 3 → 4 := by
    intro h n f N hNkerf hNfg
    classical
    obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hNfg
    let s : Finset (Fin n → R) := hSfinite.toFinset
    have hs_span : Submodule.span R (s : Set (Fin n → R)) = N := by
      simpa [s] using hSspan
    have hs_zero : ∀ x ∈ s, f x = 0 := by
      intro x hx
      have hxN : x ∈ N := by
        rw [← hs_span]
        exact Submodule.subset_span hx
      simpa [LinearMap.mem_ker] using hNkerf hxN
    -- Inductively adjoining generators yields a factorization killing the whole finitely generated
    -- submodule.
    obtain ⟨m, h', g, hfactor, hkill⟩ :=
      exists_factorization_killing_span_finset (R := R) (M := M) h f s hs_zero
    use m
    use h'
    use g
    constructor
    · exact hfactor
    · rw [← hs_span]
      exact hkill
  tfae_have 4 → 2 := by
    intro h n f x hx
    have hxspan : Submodule.span R ({x} : Set (Fin n → R)) ≤ ker f := by
      refine Submodule.span_le.2 ?_
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [LinearMap.mem_ker] using hx
    have hfg : (Submodule.span R ({x} : Set (Fin n → R))).FG := by
      simpa using (Submodule.fg_span_singleton (R := R) x)
    -- Killing the cyclic submodule generated by `x` recovers the one-element criterion.
    obtain ⟨m, h', g, hfactor, hkill⟩ := h f (Submodule.span R ({x} : Set (Fin n → R))) hxspan hfg
    use m
    use h'
    use g
    constructor
    · exact hfactor
    · have hxker : x ∈ ker h' := hkill (Submodule.subset_span (by simp))
      simpa [LinearMap.mem_ker] using hxker
  tfae_finish

end

/-! ### Lemma_10_81_2 (from Chap10) -/
universe u v w

section

open Module.Flat ULift

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: the forward implication is the existing mathlib theorem
-- `Module.Flat.exists_factorization_of_isFinitelyPresented`. For the converse, descend a map
-- `x : R^l → M` killing `f ∈ R^l` to the finitely presented quotient `R^l / Rf`; factor that
-- quotient map through a finite free module by hypothesis; then pull the factorization back along
-- the quotient map and conclude via `Module.Flat.iff_forall_exists_factorization`.
/-- Lemma 10.81.2: an `R`-module `M` is flat if and only if every linear map from a finitely
presented `R`-module to `M` factors through some finite free `R`-module. -/
theorem flat_iff_factorization_through_finite_free_of_finitelyPresented :
    Module.Flat R M ↔
      ∀ ⦃P : Type (max u w)⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M),
        ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R)) (g : (Fin n →₀ R) →ₗ[R] M), f = g ∘ₗ h := by
  constructor
  · intro _ P _ _ _ f
    exact exists_factorization_of_isFinitelyPresented f
  · intro h
    refine iff_forall_exists_factorization.mpr ?_
    intro l f x hxf
    let K : Submodule R (Fin l →₀ R) := Submodule.span R ({f} : Set (Fin l →₀ R))
    have hK : K ≤ LinearMap.ker x := by
      change Submodule.span R ({f} : Set (Fin l →₀ R)) ≤ LinearMap.ker x
      rw [Submodule.span_le]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [LinearMap.mem_ker] using hxf
    have hKfg : K.FG := by
      change (Submodule.span R ({f} : Set (Fin l →₀ R))).FG
      exact Submodule.fg_span (Set.toFinite _)
    let Q : Type u := (Fin l →₀ R) ⧸ K
    letI : Module.FinitePresentation R Q := by
      exact Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective <| by
        show (LinearMap.ker K.mkQ).FG
        simpa [Submodule.ker_mkQ] using hKfg
    let e : ULift.{w} Q ≃ₗ[R] Q := moduleEquiv
    letI : Module.FinitePresentation R (ULift.{w} Q) :=
      Module.FinitePresentation.of_equiv e.symm
    let q : Q →ₗ[R] M := K.liftQ x hK
    let xbar : ULift.{w} Q →ₗ[R] M := q ∘ₗ e.toLinearMap
    obtain ⟨k, a, y, hxbar⟩ := h xbar
    have hqbar : q = y ∘ₗ a ∘ₗ e.symm.toLinearMap := by
      calc
        q = xbar ∘ₗ e.symm.toLinearMap := by
          simp [xbar, q, LinearMap.comp_assoc]
        _ = (y ∘ₗ a) ∘ₗ e.symm.toLinearMap := by rw [hxbar]
        _ = y ∘ₗ a ∘ₗ e.symm.toLinearMap := by
          exact LinearMap.comp_assoc e.symm.toLinearMap a y
    refine ⟨k, a ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ, y, ?_, ?_⟩
    · calc
        x = q ∘ₗ K.mkQ := by
          symm
          have hq : q ∘ₗ K.mkQ = x := by
            change (K.liftQ x hK) ∘ₗ K.mkQ = x
            exact K.liftQ_mkQ x hK
          exact hq
        _ = (y ∘ₗ a ∘ₗ e.symm.toLinearMap) ∘ₗ K.mkQ := by rw [hqbar]
        _ = y ∘ₗ (a ∘ₗ e.symm.toLinearMap ∘ₗ K.mkQ) := by
          exact LinearMap.comp_assoc K.mkQ (a ∘ₗ e.symm.toLinearMap) y
    · have hmkQ : K.mkQ f = 0 := by
        exact (Submodule.Quotient.mk_eq_zero K).2 <| by
          change f ∈ Submodule.span R ({f} : Set (Fin l →₀ R))
          exact Submodule.mem_span_singleton_self f
      change a (ULift.up (K.mkQ f)) = 0
      rw [hmkQ]
      change a (0 : ULift.{w} Q) = 0
      exact LinearMap.map_zero a

end

/-! ### Lemma_10_81_3 (from Chap10) -/
universe u v w w'

section

open Finsupp

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: if `M` is flat, apply Lemma `10.81.2` to factor a map `P → M` through a finite
-- free module, then lift that finite free factorization across the surjection `N → M`. Conversely,
-- apply the stated surjectivity to a free surjection onto `M`; every map from a finitely presented
-- module then factors through a finite free submodule of the source, so Lemma `10.81.2` yields
-- flatness.
/-- Lemma 10.81.3: an `R`-module `M` is flat if and only if for every finitely presented
`R`-module `P` and every surjective linear map `N → M`, postcomposition induces a surjection
`Hom_R(P, N) → Hom_R(P, M)`. -/
theorem flat_iff_postcompose_surjective_on_hom_from_finitelyPresented :
    Module.Flat R M ↔
      ∀ ⦃P : Type (max u w)⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        ⦃N : Type (max u (max v w'))⦄ [AddCommGroup N] [Module R N]
        (π : N →ₗ[R] M), Function.Surjective π →
    Function.Surjective (fun f : P →ₗ[R] N ↦ π ∘ₗ f) := by
  constructor
  · intro hflat P _ _ _ N _ _ π hπ f
    obtain ⟨n, a, b, rfl⟩ :=
      flat_iff_factorization_through_finite_free_of_finitelyPresented.mp hflat f
    obtain ⟨c, hc⟩ := Module.projective_lifting_property π b hπ
    refine ⟨c ∘ₗ a, ?_⟩
    exact congrArg (fun t ↦ t ∘ₗ a) hc
  · intro hsurj
    refine flat_iff_factorization_through_finite_free_of_finitelyPresented.mpr ?_
    intro P _ _ _ f
    classical
    let π : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
    let e₀ : ULift.{w'} (M →₀ R) ≃ₗ[R] (M →₀ R) := ULift.moduleEquiv
    let π' : ULift.{w'} (M →₀ R) →ₗ[R] M := π ∘ₗ e₀.toLinearMap
    obtain ⟨g', hg'⟩ := hsurj π' ((Finsupp.linearCombination_id_surjective R M).comp e₀.surjective) f
    let g : P →ₗ[R] M →₀ R := e₀.toLinearMap ∘ₗ g'
    have hg : π ∘ₗ g = f := by
      simpa [g, π', LinearMap.comp_assoc] using hg'
    have hPfin : ∃ n, ∃ s : Fin n → P, Submodule.span R (Set.range s) = ⊤ :=
      Module.Finite.exists_fin
    obtain ⟨n, s, hs⟩ := hPfin
    let t : Finset M := Finset.univ.biUnion fun i ↦ (g (s i)).support
    let K : Submodule R (M →₀ R) := Finsupp.supported R R (↑t : Set M)
    have hsK : ∀ i, g (s i) ∈ K := by
      intro i
      change ↑(g (s i)).support ⊆ (↑t : Set M)
      intro x hx
      change x ∈ t
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
    have htop : (⊤ : Submodule R P) ≤ K.comap g := by
      rw [← hs]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hsK i
    have hgK : ∀ x : P, g x ∈ K := fun x ↦ htop trivial
    let gK : P →ₗ[R] K := g.codRestrict K hgK
    let e : K ≃ₗ[R] (↑t →₀ R) := Finsupp.supportedEquivFinsupp (↑t : Set M)
    let e' : (↑t →₀ R) ≃ₗ[R] (Fin (Fintype.card ↑t) →₀ R) :=
      Finsupp.domLCongr (Fintype.equivFin ↑t)
    refine ⟨Fintype.card ↑t, e'.toLinearMap ∘ₗ e.toLinearMap ∘ₗ gK,
      π ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap ∘ₗ e'.symm.toLinearMap, ?_⟩
    rw [← hg]
    calc
      π ∘ₗ g = π ∘ₗ K.subtype ∘ₗ gK := by
        simp [gK]
      _ = π ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap ∘ₗ e'.symm.toLinearMap ∘ₗ
          e'.toLinearMap ∘ₗ e.toLinearMap ∘ₗ gK := by
        simp

end

/-! ### Theorem_10_81_4_Lazard_s_theorem (from Chap10) -/
open CategoryTheory.ObjectProperty
open CategoryTheory Limits

universe u

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat.{u} R)

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the object property of finite free
`R`-modules. -/
abbrev finite_free_property : ObjectProperty (ModuleCat.{u} R) :=
  fun N ↦ Module.Free R N ∧ Module.Finite R N

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the full subcategory of finite free
`R`-modules. -/
abbrev finite_free_subcategory :=
  (finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).FullSubcategory

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the standard rank-`k` finite free module. -/
noncomputable abbrev finite_free_rank (k : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin k →₀ R)

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a finite free `R`-module is finitely
presentable as an object of `ModuleCat R`. -/
lemma finite_free_isFinitelyPresentable_moduleCat
    {N : ModuleCat.{u} R} (hN : finite_free_property (R := R) N) :
    IsFinitelyPresentable.{u} N := by
  letI : Module.Free R N := hN.1
  letI : Module.Finite R N := hN.2
  letI : Module.Projective R N := Module.Projective.of_free
  letI : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  -- Finite free modules are finitely presented algebraically, and Lemma `10.11.4` transports
  -- that statement to the categorical owner `IsFinitelyPresentable`.
  exact
    (module_finitePresentation_iff_isFinitelyPresentable (R := R) (M := N)).mp inferInstance

/-- Helper for Theorem 10.81.4 (Lazard's theorem): the full subcategory of finite free modules is
essentially small because it embeds fully faithfully into `FGModuleCat R`. -/
lemma finite_free_fullSubcategory_essentiallySmall :
    EssentiallySmall.{u} (finite_free_subcategory (R := R)) := by
  -- Route correction: keep the source-faithful finite-free indexing category, but realize its
  -- smallness through the canonical fully faithful inclusion into `FGModuleCat.{u} R`.
  let F :
      finite_free_subcategory (R := R) ⥤ FGModuleCat.{u} R :=
    ObjectProperty.ιOfLE (fun N hN ↦ hN.2)
  -- The ambient category of finitely generated modules is essentially small in the same universe.
  letI : EssentiallySmall.{u} (FGModuleCat.{u} R) := by infer_instance
  exact essentiallySmall_of_fully_faithful F

/-- Helper for Theorem 10.81.4 (Lazard's theorem): finite free arrows into a flat module form a
filtered category. -/
lemma finite_free_costructuredArrow_isFiltered
    (hM : Module.Flat R M) :
    IsFiltered (CostructuredArrow
      ((finite_free_property (R := R) : ObjectProperty (ModuleCat.{u} R)).ι) M) := by
  -- Route correction: the same-universe smallness bridge is now closed, so the remaining
  -- source-faithful work is purely the explicit filteredness packaging.
  -- TODO: build the zero stage, the two-object upper bound, and the equalizer stage from
  -- `Module.Flat.exists_factorization_of_comp_eq_zero_of_free`, keeping the coercions inside
  -- `ObjectProperty.homMk` and `CostructuredArrow.homMk` aligned.
  let _ := hM
  sorry

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a filtered colimit of finite free modules is
flat. -/
lemma flat_of_ind_finite_free
    (hM : ind (finite_free_property (R := R)) M) :
    Module.Flat R M := by
  -- TODO: map the small filtered presentation into the universe expected by
  -- `flat_of_isColimit_filtered_system` and transport flatness back along the canonical
  -- universe-lift equivalence on `ModuleCat`.
  sorry

/-- Helper for Theorem 10.81.4 (Lazard's theorem): a flat module lies in the filtered-colimit
closure of the finite free modules. -/
lemma ind_finite_free_of_flat
    (hM : Module.Flat R M) :
    ind (finite_free_property (R := R)) M := by
  -- TODO: after `finite_free_costructuredArrow_isFiltered` is in place, the remaining step is to
  -- package the tautological cocone and prove it is colimiting via
  -- `Types.FilteredColimit.isColimitOf'` together with `forget_reflectsFilteredColimits`.
  sorry

-- Proof sketch: if `M` is the colimit of a directed system of finite free modules, then each stage
-- is flat and filtered colimits of modules preserve exactness, so `M` is flat. Conversely, the
-- finite free arrows into a flat module form a filtered dense diagram by Lemma `10.81.2`.
/-- Theorem 10.81.4 (Lazard's theorem): an `R`-module `M` is flat if and only if it is isomorphic
to the colimit of a directed system of finite free `R`-modules. In the canonical owner
formulation, this says that `M`, viewed as an object of `ModuleCat R`, belongs to the
filtered-colimit closure of the finite free `R`-modules. -/
theorem flat_iff_isomorphic_colimit_of_directed_system_of_finite_free :
    Module.Flat R M ↔
      ind (finite_free_property (R := R)) M := by
  constructor
  · -- For a flat module, finite free arrows into `M` form a filtered dense diagram.
    exact ind_finite_free_of_flat (R := R) (M := M)
  · -- For a filtered colimit of finite free stages, apply stability of flatness under colimits.
    exact flat_of_ind_finite_free (R := R) (M := M)

end
