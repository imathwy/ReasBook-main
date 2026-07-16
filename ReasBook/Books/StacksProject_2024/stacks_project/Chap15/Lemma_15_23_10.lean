import StacksProject_2024.stacks_project.Chap10.Definition_10_5_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_157_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_72_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- Helper for Lemma 15.23.10: finite powers preserve any lower depth bound carried by `N`. -/
lemma moduleDepth_fin_fun_ge_of_moduleDepth_ge (n : ℕ) {k : ℕ}
    (hN : (k : ℕ∞) ≤ moduleDepth R N) :
    (k : ℕ∞) ≤ moduleDepth R (Fin n → N) := by
  induction n with
  | zero =>
      -- The zero power is the zero module, so its depth is top.
      have htop : IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin 0 → N)) = ⊤ := by
        ext x
        have hx : x = 0 := by
          ext i
          exact Fin.elim0 i
        subst hx
        constructor
        · intro _
          simp
        · intro _
          simpa using
            (Submodule.zero_mem
              (IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Fin 0 → N))))
      rw [show moduleDepth R (Fin 0 → N) = ⊤ from
        Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal R) (Fin 0 → N) htop]
      simp
  | succ n ih =>
      -- Rewrite `Fin (n + 1) → N` as `N × (Fin n → N)` and apply the short-exact depth bound
      -- for the split sequence `0 → N → N × (Fin n → N) → Fin n → N → 0`.
      let e₁ : (Fin (n + 1) → N) ≃ₗ[R] ((Fin n ⊕ Fin 1) → N) :=
        LinearEquiv.funCongrLeft (R := R) (M := N) (finSumFinEquiv (m := n) (n := 1))
      let e₂ : ((Fin n ⊕ Fin 1) → N) ≃ₗ[R] ((Fin n → N) × (Fin 1 → N)) :=
        LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin 1) R N
      let e₃ : ((Fin n → N) × (Fin 1 → N)) ≃ₗ[R] ((Fin n → N) × N) :=
        LinearEquiv.prodCongr (LinearEquiv.refl R _) (LinearEquiv.funUnique (Fin 1) R N)
      let e₄ : ((Fin n → N) × N) ≃ₗ[R] (N × (Fin n → N)) :=
        LinearEquiv.prodComm R (Fin n → N) N
      let e : (Fin (n + 1) → N) ≃ₗ[R] (N × (Fin n → N)) := e₁.trans (e₂.trans (e₃.trans e₄))
      let S : CategoryTheory.ShortComplex (ModuleCat R) :=
        CategoryTheory.ShortComplex.mk
          (ModuleCat.ofHom (LinearMap.inl R N (Fin n → N)))
          (ModuleCat.ofHom (LinearMap.snd R N (Fin n → N)))
          (by ext x <;> rfl)
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (by simpa [S] using (Function.Exact.inl_snd : Function.Exact
          (LinearMap.inl R N (Fin n → N)) (LinearMap.snd R N (Fin n → N))))
        LinearMap.inl_injective
        LinearMap.snd_surjective
      have hMin :
          (k : ℕ∞) ≤
            min (moduleDepth R N) (moduleDepth R (Fin n → N)) :=
        le_min hN ih
      have hProd :
          (k : ℕ∞) ≤ moduleDepth R (N × (Fin n → N)) :=
        hMin.trans
          (CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min hS)
      have hEq :
          moduleDepth R (Fin (n + 1) → N) = moduleDepth R (N × (Fin n → N)) :=
        moduleDepth_eq_of_equiv e
      simpa [hEq] using hProd

/-- Helper for Lemma 15.23.10: lower depth bounds pass from `N` to `Hom_R(R^n, N)`. -/
lemma moduleDepth_linearMap_fin_ge_of_moduleDepth_ge (n : ℕ) {k : ℕ}
    (hN : (k : ℕ∞) ≤ moduleDepth R N) :
    (k : ℕ∞) ≤ moduleDepth R ((Fin n → R) →ₗ[R] N) := by
  letI : Module.Finite R ((Fin n → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin n → R) N
  -- Transport the finite-power depth bound along the canonical linear equivalence
  -- `Hom_R(R^n, N) ≃ N^n`.
  have hFin : (k : ℕ∞) ≤ moduleDepth R (Fin n → N) :=
    moduleDepth_fin_fun_ge_of_moduleDepth_ge (R := R) (N := N) n hN
  have hEq :
      moduleDepth R ((Fin n → R) →ₗ[R] N) = moduleDepth R (Fin n → N) :=
    moduleDepth_eq_of_equiv (LinearEquiv.piRing R N (Fin n) R)
  simpa [hEq] using hFin

/-- Helper for Lemma 15.23.10: dualizing a finite free presentation gives a short exact sequence
with quotient the range of the next dual map. -/
lemma lcomp_presentation_shortExact {n m : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] M)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    let S : CategoryTheory.ShortComplex (ModuleCat R) :=
      CategoryTheory.ShortComplex.mk
        (ModuleCat.ofHom (LinearMap.lcomp R N g))
        (ModuleCat.ofHom (LinearMap.rangeRestrict (LinearMap.lcomp R N f)))
        (by
          ext φ x
          have hcomp : g (f (Pi.single x 1)) = 0 := by
            simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero (Pi.single x 1)
          simp [hcomp])
    S.ShortExact := by
  let α : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) := LinearMap.lcomp R N g
  let β : ((Fin n → R) →ₗ[R] N) →ₗ[R] LinearMap.range (LinearMap.lcomp R N f) :=
    (LinearMap.lcomp R N f).rangeRestrict
  let S : CategoryTheory.ShortComplex (ModuleCat R) :=
    CategoryTheory.ShortComplex.mk
      (ModuleCat.ofHom α)
      (ModuleCat.ofHom β)
      (by
        ext φ x
        have hcomp : g (f (Pi.single x 1)) = 0 := by
          simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero (Pi.single x 1)
        simp [α, β, hcomp])
  have hExactLcomp : Function.Exact α (LinearMap.lcomp R N f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective N hfg hg
  have hExact : Function.Exact α β := by
    intro φ
    constructor
    · intro hβ
      have hzero : (LinearMap.lcomp R N f) φ = 0 := by
        ext x
        simpa [β] using LinearMap.congr_fun (congrArg Subtype.val hβ) (Pi.single x 1)
      exact (hExactLcomp φ).1 hzero
    · rintro ⟨ψ, rfl⟩
      apply Subtype.ext
      ext x
      have hcomp : g (f (Pi.single x 1)) = 0 := by
        simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero (Pi.single x 1)
      simp [α, β, hcomp]
  have hInj : Function.Injective α :=
    LinearMap.lcomp_injective_of_surjective g hg
  have hSurj : Function.Surjective β := (LinearMap.lcomp R N f).surjective_rangeRestrict
  simpa [S, α, β] using ModuleCat.shortComplex_shortExact S hExact hInj hSurj

/-- Helper for Lemma 15.23.10: the image of a dual presentation map has depth at least `1` when
`N` has depth at least `2`. -/
lemma moduleDepth_range_lcomp_ge_one_of_depth_ge_two {m n : ℕ}
    (f : (Fin m → R) →ₗ[R] (Fin n → R))
    (hN : (2 : ℕ∞) ≤ moduleDepth R N) :
    (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) := by
  let T : CategoryTheory.ShortComplex (ModuleCat R) :=
    CategoryTheory.ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.range (LinearMap.lcomp R N f)).subtype)
      (ModuleCat.ofHom (Submodule.mkQ (LinearMap.range (LinearMap.lcomp R N f))))
      (by ext x <;> simp)
  letI : Module.Finite R ((Fin m → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin m → R) N
  letI : Module.Finite R (LinearMap.range (LinearMap.lcomp R N f)) :=
    Module.Finite.of_injective (LinearMap.range (LinearMap.lcomp R N f)).subtype
      (Submodule.injective_subtype _)
  letI : Module.Finite R (((Fin m → R) →ₗ[R] N) ⧸ LinearMap.range (LinearMap.lcomp R N f)) :=
    Module.Finite.quotient R (LinearMap.range (LinearMap.lcomp R N f))
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (by simpa [T] using LinearMap.exact_subtype_mkQ (LinearMap.range (LinearMap.lcomp R N f)))
    (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _)
  -- Apply the left-term depth inequality to the canonical quotient sequence of the range submodule.
  have hMid :
      (2 : ℕ∞) ≤ moduleDepth R ((Fin m → R) →ₗ[R] N) :=
    moduleDepth_linearMap_fin_ge_of_moduleDepth_ge (R := R) (N := N) m hN
  have hMin :
      (1 : ℕ∞) ≤
        min (moduleDepth R ((Fin m → R) →ₗ[R] N))
          (moduleDepth R (((Fin m → R) →ₗ[R] N) ⧸
            LinearMap.range (LinearMap.lcomp R N f)) + 1) := by
    refine le_min ?_ ?_
    · exact le_trans (by norm_num) hMid
    · simp
  have hDepth :
      moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) ≥
        min (moduleDepth R ((Fin m → R) →ₗ[R] N))
          (moduleDepth R (((Fin m → R) →ₗ[R] N) ⧸
            LinearMap.range (LinearMap.lcomp R N f)) + 1) := by
    simpa [T] using CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min hT
  exact hMin.trans hDepth

/-
Domain triage:
* primary domain: local commutative algebra of module depth for `Hom` modules over Noetherian
  local rings;
* sampled owner declarations:
  `moduleDepth`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min`,
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min`,
  `Module.FinitePresentation`;
* owner abstraction: the local-depth bridge `moduleDepth R _`, with the finite module structures
  on `M` and `N` as primitive data. Over a Noetherian ring, any finite module is finitely
  presented internally, so finite presentations and the finiteness of `M →ₗ[R] N` are derived
  support for the proof rather than primitive public data;
* derived API: the Chapter 10 short-exact depth inequalities above are the internal support for
  this file, while Lemma `15.23.11` gives the later `bridge/view` packaging into
  `Module.SerreConditionS`;
* layer: `source-facing`.

Primitive data here are just the finite module structures on `M` and `N`; the depth hypotheses in
the theorems are source-facing assumptions rather than extra packaged data. The short exact
sequence built from a finite presentation of `M` is proof-internal, and the Serre-condition
statements are derived downstream packaging that should not replace this local owner-level file.
-/

/- Source/core/bridge triage:
* `source-facing`: the local depth bounds for `Hom_R(M, N)`;
* `core/canonical`: `moduleDepth` and the Chapter 10 short-exact depth inequalities;
* `bridge/view`: Lemma `15.23.11`, which repackages these local statements as Serre conditions.
-/

-- Proof sketch: choose a finite presentation of the finite module `M`, dualize against `N`, and
-- obtain a short exact sequence `0 → Hom_R(M, N) → N^n → N' → 0`. Since finite modules over a
-- Noetherian ring are finitely presented, the presentation is internal support rather than public
-- data. Apply `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min` to this sequence
-- and use `moduleDepth N^n = moduleDepth N` to conclude.
/-- Lemma 15.23.10 (1): if `N` has depth at least `1`, then `Hom_R(M, N)` has depth at least `1`.
-/
theorem moduleDepth_linearMap_ge_one
    (hN : 1 ≤ moduleDepth R N) :
    1 ≤ moduleDepth R (M →ₗ[R] N) := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  -- Unpack a finite free presentation of `M`, dualize it, and apply the left-term depth bound
  -- to the induced short exact sequence.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  letI : Module.Finite R (M →ₗ[R] N) := Module.Finite.of_injective (LinearMap.lcomp R N g)
    (LinearMap.lcomp_injective_of_surjective g hg)
  letI : Module.Finite R ((Fin n → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin n → R) N
  letI : Module.Finite R (LinearMap.range (LinearMap.lcomp R N f)) :=
    Module.Finite.of_injective (LinearMap.range (LinearMap.lcomp R N f)).subtype
      (Submodule.injective_subtype _)
  let S : CategoryTheory.ShortComplex (ModuleCat R) :=
    CategoryTheory.ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.lcomp R N g))
      (ModuleCat.ofHom (LinearMap.rangeRestrict (LinearMap.lcomp R N f)))
      (by
        ext φ x
        have hcomp : g (f (Pi.single x 1)) = 0 := by
          simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero (Pi.single x 1)
        simp [hcomp])
  have hS : S.ShortExact := lcomp_presentation_shortExact (R := R) (M := M) (N := N) f g hfg hg
  have hMid :
      (1 : ℕ∞) ≤ moduleDepth R ((Fin n → R) →ₗ[R] N) :=
    moduleDepth_linearMap_fin_ge_of_moduleDepth_ge (R := R) (N := N) n hN
  have hMin :
      (1 : ℕ∞) ≤
        min (moduleDepth R ((Fin n → R) →ₗ[R] N))
          (moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) + 1) := by
    refine le_min ?_ ?_
    · exact hMid
    · simp
  exact hMin.trans (CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min hS)

-- Proof sketch: use the same short exact sequence
-- `0 → Hom_R(M, N) → N^n → N' → 0`. Part `(1)` gives `moduleDepth R N' ≥ 1` when
-- `moduleDepth R N ≥ 2`, while `moduleDepth R N^n ≥ 2`. Then apply the canonical Chapter 10 owner
-- theorem `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min` to recover
-- `moduleDepth R Hom_R(M, N) ≥ 2`.
/-- Lemma 15.23.10 (2): if `N` has depth at least `2`, then `Hom_R(M, N)` has depth at least `2`.
-/
theorem moduleDepth_linearMap_ge_two
    (hN : 2 ≤ moduleDepth R N) :
    2 ≤ moduleDepth R (M →ₗ[R] N) := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  -- Reuse the dual short exact sequence from part `(1)`, but now also control the quotient term
  -- by viewing it as a submodule of another finite free dual module.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence R M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  letI : Module.Finite R (M →ₗ[R] N) := Module.Finite.of_injective (LinearMap.lcomp R N g)
    (LinearMap.lcomp_injective_of_surjective g hg)
  letI : Module.Finite R ((Fin n → R) →ₗ[R] N) := Module.Finite.linearMap R R (Fin n → R) N
  letI : Module.Finite R (LinearMap.range (LinearMap.lcomp R N f)) :=
    Module.Finite.of_injective (LinearMap.range (LinearMap.lcomp R N f)).subtype
      (Submodule.injective_subtype _)
  let S : CategoryTheory.ShortComplex (ModuleCat R) :=
    CategoryTheory.ShortComplex.mk
      (ModuleCat.ofHom (LinearMap.lcomp R N g))
      (ModuleCat.ofHom (LinearMap.rangeRestrict (LinearMap.lcomp R N f)))
      (by
        ext φ x
        have hcomp : g (f (Pi.single x 1)) = 0 := by
          simpa using LinearMap.congr_fun hfg.linearMap_comp_eq_zero (Pi.single x 1)
        simp [hcomp])
  have hS : S.ShortExact := lcomp_presentation_shortExact (R := R) (M := M) (N := N) f g hfg hg
  have hMid :
      (2 : ℕ∞) ≤ moduleDepth R ((Fin n → R) →ₗ[R] N) :=
    moduleDepth_linearMap_fin_ge_of_moduleDepth_ge (R := R) (N := N) n hN
  have hRange :
      (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) :=
    moduleDepth_range_lcomp_ge_one_of_depth_ge_two (R := R) (N := N) f hN
  have hMin :
      (2 : ℕ∞) ≤
        min (moduleDepth R ((Fin n → R) →ₗ[R] N))
          (moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) + 1) := by
    refine le_min ?_ ?_
    · exact hMid
    · by_cases htop : moduleDepth R (LinearMap.range (LinearMap.lcomp R N f)) = ⊤
      · simp [htop]
      · rcases ENat.ne_top_iff_exists.mp htop with ⟨r, hr⟩
        have hrange_enat : (1 : ℕ∞) ≤ (r : ℕ∞) := by
          simpa [hr] using hRange
        have hrange_nat : 1 ≤ r := ENat.coe_le_coe.mp hrange_enat
        rw [← hr]
        exact_mod_cast Nat.succ_le_succ hrange_nat
  exact hMin.trans (CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min hS)

end
