import StacksProject_2024.stacks_project.Chap10.Lemma_10_85_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_129_1_Eilenberg_s_lemma
import StacksProject_2024.stacks_project.Chap15.Lemma_15_129_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P] [Module.Projective R P]
variable [IsNoetherianRing (R ⧸ Ring.jacobson R)]

open Module

/- Domain triage:
- primary domain: projective modules, countable generation, and freeness criteria via free
  and stably free direct summands;
- sampled owner declarations:
  `Module.CountablyGenerated`,
  `exists_finiteStablyFree_directSummand_submodule_containing`,
  `exists_perturbation_with_cyclicSpan_free_directSummand`,
  and `Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty`;
- `source-facing`: the numbered theorem is the Chapter 15 freeness statement for one countably
  generated projective module under the maximal-localization infinite-rank hypothesis;
- `core/canonical`: the ambient owners are `Module.CountablyGenerated R P` and `Module.Free R P`;
- `bridge/view`: Lemma `15.129.5` gives the source-facing finite stably free summands, and
  Lemma `15.129.4` is the free rank-one splitting step used in the Stacks proof to upgrade those
  summands to a countable free decomposition.

Primitive data are the ambient projective module `P`, the countable-generation hypothesis, and the
local maximal-ideal non-finiteness condition. The Chapter 10 owner
`Module.HasFiniteFreeComplementSummandProperty R P` is stronger than Lemma `15.129.5` and is not
the direct output of Lemma `15.129.5`, so the source-facing theorem should remain the main public
entry while this file provides a separate bridge to that owner. The maximal-local condition should
still use the chapter’s canonical `MaximalSpectrum R` indexing rather than an `Ideal` parameter
with a hidden `[IsMaximal]` binder. -/

namespace Module

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a surjective linear image of a countably generated module is
again countably generated. -/
lemma countablyGenerated_of_surjective
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) (hf : Function.Surjective f)
    (hcg : CountablyGenerated R P) :
    CountablyGenerated R Q := by
  -- Push a countable spanning set for `P` through the surjective map `f`.
  rcases (Module.countablyGenerated_iff (R := R) (M := P)).1 hcg with ⟨s, hsCount, hsSpan⟩
  refine (Module.countablyGenerated_iff (R := R) (M := Q)).2 ?_
  refine ⟨f '' s, hsCount.image f, ?_⟩
  apply top_unique
  intro q _
  rcases hf q with ⟨p, rfl⟩
  have hp : p ∈ Submodule.span R s := by
    simpa [hsSpan]
  -- Rewrite the target span as the image of the source span.
  rw [Submodule.span_image]
  exact Submodule.mem_map_of_mem hp

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: countable generation is preserved by a linear equivalence. -/
lemma countablyGenerated_of_linearEquiv
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (e : P ≃ₗ[R] Q) (hcg : CountablyGenerated R P) :
    CountablyGenerated R Q := by
  -- Reduce to the surjective-image form using the forward map of the equivalence.
  exact countablyGenerated_of_surjective e.toLinearMap e.surjective hcg

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a complemented summand of a countably generated module is itself
countably generated. -/
lemma countablyGenerated_of_isCompl_right
    {N N' : Submodule R P} (hNN' : IsCompl N N')
    (hcg : CountablyGenerated R P) :
    CountablyGenerated R N := by
  let eQuot : (P ⧸ N') ≃ₗ[R] N :=
    Submodule.quotientEquivOfIsCompl N' N hNN'.symm
  have hquot : CountablyGenerated R (P ⧸ N') :=
    countablyGenerated_of_surjective N'.mkQ N'.mkQ_surjective hcg
  -- Identify the complement with the quotient by the opposite summand.
  exact countablyGenerated_of_linearEquiv eQuot hquot

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: after removing a finite complemented summand, the maximal-local
non-finiteness hypothesis persists on the complementary summand. -/
lemma localizations_not_finite_of_isCompl_of_finite_right
    {N N' : Submodule R P} (hNN' : IsCompl N N')
    [Module.Finite R N']
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) := by
  intro m hNloc
  let eQuot : (P ⧸ N) ≃ₗ[R] N' :=
    Submodule.quotientEquivOfIsCompl N N' hNN'
  have hfiniteQuot : Module.Finite R (P ⧸ N) := by
    -- The quotient by the complementary summand is identified with the finite discarded piece.
    exact Module.Finite.equiv eQuot.symm
  have hlocalizedN :
      Module.Finite (Localization.AtPrime m.asIdeal)
        ((Submodule.localized (p := m.asIdeal.primeCompl) N :
            Submodule (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal P))) := by
    -- Convert finiteness of the localized module to finiteness of the localized submodule.
    letI :
        Module.Finite (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal N) := hNloc
    exact localized_submodule_finite_of_localized_module_finite (R := R) N m
  -- A finite localized complement and a finite quotient would force the ambient localization to be
  -- finite, contradicting the standing hypothesis.
  exact localized_common_kernel_not_finite_at_lieover
    (R := R) (P := P) m hfiniteQuot (hnotFiniteAtMax m) hlocalizedN

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: maximal-local non-finiteness already forces the ambient module to
be non-finite. -/
lemma not_finite_of_localizations_not_finite
    [Nontrivial R]
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ¬ Module.Finite R P := by
  intro hP
  letI : Module.Finite R P := hP
  obtain ⟨I, hImax, _⟩ := Ideal.exists_le_maximal (I := (⊥ : Ideal R)) bot_ne_top
  let m : MaximalSpectrum R := ⟨I, hImax⟩
  -- Any finite module stays finite after localization, contradicting the hypothesis at each
  -- maximal ideal.
  exact hnotFiniteAtMax m inferInstance

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a countably generated projective module splits off from the
countable free module. -/
lemma exists_split_countableFree_of_countablyGenerated
    (hcg : CountablyGenerated R P) :
    ∃ i : P →ₗ[R] (ℕ →₀ R), ∃ s : (ℕ →₀ R) →ₗ[R] P, s.comp i = LinearMap.id := by
  classical
  rcases (Module.countablyGenerated_iff (R := R) (M := P)).1 hcg with ⟨S, hScount, hSspan⟩
  letI : Encodable S := hScount.toEncodable
  let v : ℕ → P := fun n ↦
    match Encodable.decode (α := S) n with
    | some x => x
    | none => 0
  have hSsubset : S ⊆ Set.range v := by
    intro x hx
    let xS : S := ⟨x, hx⟩
    refine ⟨Encodable.encode xS, ?_⟩
    simp [v, xS]
  have hspanv : Submodule.span R (Set.range v) = ⊤ := by
    apply top_le_iff.mp
    rw [← hSspan]
    exact Submodule.span_mono hSsubset
  let s : (ℕ →₀ R) →ₗ[R] P := Finsupp.linearCombination R v
  have hs_surj : Function.Surjective s := by
    intro x
    have hx_span : x ∈ Submodule.span R (Set.range v) := by
      simpa [hspanv] using (show x ∈ (⊤ : Submodule R P) from by simp)
    rcases (Finsupp.mem_span_range_iff_exists_finsupp).1 hx_span with
      ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [s] using hc
  obtain ⟨i, hi⟩ :=
    Module.projective_lifting_property s (LinearMap.id : P →ₗ[R] P) hs_surj
  -- The projective lifting property gives the desired split inclusion into the countable free
  -- module.
  exact ⟨i, s, hi⟩

omit [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: over a nontrivial ring, a countably generated projective module
becomes free after adjoining the countable free module. -/
lemma free_prod_countableFree_of_countablyGenerated_projective
    [Nontrivial R]
    (hcg : CountablyGenerated R P) :
    Module.Free R (P × (ℕ →₀ R)) := by
  obtain ⟨i, s, hs⟩ := exists_split_countableFree_of_countablyGenerated (R := R) (P := P) hcg
  have hcount_not_finite : ¬ Module.Finite R (ℕ →₀ R) := by
    intro hfinite
    rcases Module.finite_finsupp_self_iff.1 hfinite with hsub | hfin
    · exact not_subsingleton R hsub
    · letI : Finite ℕ := hfin
      exact (inferInstance : Infinite ℕ).false
  obtain ⟨eSplit⟩ :=
    split_linearEquiv_prod_ker (R := R) (P := P) (F := ℕ →₀ R) i s hs
  obtain ⟨e⟩ :=
    prod_nonfinitely_generated_free_absorption
      (R := R) (P := P) (Q := LinearMap.ker s) (F := ℕ →₀ R) hcount_not_finite eSplit.symm
  -- Once `P` is a retract of the countable free module, Eilenberg absorption makes the product
  -- with that countable free module free again.
  exact Module.Free.of_equiv e.symm

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: over a nontrivial ring, the standard countable free module is
not finitely generated. -/
lemma not_finite_countableFree [Nontrivial R] :
    ¬ Module.Finite R (ℕ →₀ R) := by
  intro hfinite
  rcases Module.finite_finsupp_self_iff.1 hfinite with hsub | hfin
  · exact not_subsingleton R hsub
  · letI : Finite ℕ := hfin
    exact (inferInstance : Infinite ℕ).false

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a finite submodule of an increasing countable chain whose supremum
is `⊤` is already contained in one stage. -/
lemma finite_submodule_le_some_of_iSup_eq_top
    (H : Nat → Submodule R P) (hmono : Monotone H) (hH : iSup H = ⊤)
    (K : Submodule R P) [Module.Finite R K] :
    ∃ n : Nat, K ≤ H n := by
  classical
  have hdir : Directed (· ≤ ·) H := by
    intro i j
    refine ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  have hKfg : (⊤ : Submodule R K).FG := Module.Finite.fg_top (R := R) (M := K)
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hKfg
  let stageOf : K → Nat := fun x ↦
    if hx : x ∈ S then
      Classical.choose <|
        (Submodule.mem_iSup_of_directed H hdir).mp <|
          show ((x : K) : P) ∈ iSup H by
            simpa [hH] using (show ((x : K) : P) ∈ (⊤ : Submodule R P) from by simp)
    else
      0
  let n : Nat := hSfinite.toFinset.sup stageOf
  have hgenerators_le : Submodule.span R S ≤ (H n).comap K.subtype := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    have hxstage : ((x : K) : P) ∈ H (stageOf x) := by
      have hx' : x ∈ S := hx
      simp only [stageOf, dif_pos hx']
      exact Classical.choose_spec <|
        (Submodule.mem_iSup_of_directed H hdir).mp <|
          show ((x : K) : P) ∈ iSup H by
            simpa [hH] using (show ((x : K) : P) ∈ (⊤ : Submodule R P) from by simp)
    exact hmono (Finset.le_sup (hSfinite.mem_toFinset.mpr hx)) hxstage
  have htop_le : (⊤ : Submodule R K) ≤ (H n).comap K.subtype := by
    rw [← hSspan]
    exact hgenerators_le
  have hcomap : (H n).comap K.subtype = ⊤ := top_le_iff.mp htop_le
  -- Passing back across the subtype map turns the equality of the comap with `⊤` into the desired
  -- inclusion of the original finite submodule.
  exact ⟨n, (Submodule.comap_subtype_eq_top.mp hcomap)⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a countably generated module admits a spanning sequence indexed by
`ℕ`. -/
lemma exists_countable_spanning_sequence
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hcg : CountablyGenerated R Q) :
    ∃ x : ℕ → Q, Submodule.span R (Set.range x) = ⊤ := by
  -- Enumerate a countable spanning set by decoding the chosen encodable witness.
  rcases (Module.countablyGenerated_iff (R := R) (M := Q)).1 hcg with ⟨S, hScount, hSspan⟩
  letI : Encodable S := hScount.toEncodable
  let x : ℕ → Q := fun n ↦
    match Encodable.decode (α := S) n with
    | some s => s
    | none => 0
  have hSsubset : S ⊆ Set.range x := by
    intro s hs
    let sS : S := ⟨s, hs⟩
    refine ⟨Encodable.encode sS, ?_⟩
    simp [x, sS]
  refine ⟨x, ?_⟩
  apply top_unique
  rw [← hSspan]
  exact Submodule.span_mono hSsubset

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: an element of a submodule that is sent to `1` by a linear form
produces a split rank-one copy of `R` inside that submodule. -/
lemma exists_split_maps_of_mem_with_eval_one
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {B : Submodule R Q} {t : Q} (ht : t ∈ B)
    {ψ : Q →ₗ[R] R} (hψ : ψ t = 1) :
    ∃ eta : R →ₗ[R] B, ∃ eps : B →ₗ[R] R, eps.comp eta = LinearMap.id := by
  let b : B := ⟨t, ht⟩
  let eta : R →ₗ[R] B := LinearMap.smulRight (LinearMap.id : R →ₗ[R] R) b
  let eps : B →ₗ[R] R := ψ.comp B.subtype
  have heps : eps.comp eta = LinearMap.id := by
    -- Evaluating the chosen linear form on the distinguished generator recovers the scalar.
    have hb : ψ ↑b = 1 := by
      simpa [b] using hψ
    ext a
    simp [eta, eps, hb]
  exact ⟨eta, eps, heps⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a free module that is not finitely generated has an infinite
chosen basis index type. -/
lemma choose_basis_index_infinite_of_not_finite
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F) :
    Infinite (Module.Free.ChooseBasisIndex R F) := by
  classical
  by_contra hι
  let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  letI : Finite (Module.Free.ChooseBasisIndex R F) := Finite.of_not_infinite hι
  -- A finite basis would force finite generation, contradicting the hypothesis.
  exact hF (Module.Finite.of_basis b)

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: adjoining finitely many points to an infinite index type does not
change its cardinality. -/
lemma fin_sum_equiv_self_of_infinite
    (n : ℕ) {ι : Type v} [Infinite ι] :
    Nonempty (Fin n ⊕ ι ≃ ι) := by
  have hcard : Cardinal.mk (Fin n ⊕ ι) = Cardinal.mk ι := by
    rw [Cardinal.mk_sum, Cardinal.mk_fintype]
    have hLift : Cardinal.lift.{0, v} (Cardinal.mk ι) = Cardinal.mk ι := by
      simp
    rw [hLift]
    have hAleph : Cardinal.aleph0 ≤ Cardinal.mk ι := Cardinal.aleph0_le_mk ι
    have hnat : (Fintype.card (Fin n) : Cardinal) ≤ Cardinal.aleph0 := by
      simpa using (Cardinal.nat_lt_aleph0 n).le
    have hn : (Fintype.card (Fin n) : Cardinal) ≤ Cardinal.mk ι := le_trans hnat hAleph
    -- Move the finite block to the right and collapse the resulting maximum back to the infinite
    -- cardinal.
    calc
      Cardinal.lift.{v, 0} (Fintype.card (Fin n) : Cardinal) + Cardinal.mk ι
          = Cardinal.mk ι + Cardinal.lift.{v, 0} (Fintype.card (Fin n) : Cardinal) := by
              rw [add_comm]
      _ = max (Cardinal.mk ι) (Cardinal.lift.{v, 0} (Fintype.card (Fin n) : Cardinal)) := by
              rw [Cardinal.add_eq_max hAleph]
      _ = Cardinal.mk ι := by
              exact max_eq_left (by simpa using hn)
  exact Cardinal.eq.mp hcard

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a finitely generated free module is absorbed by a non-finitely
generated free module. -/
lemma nonfinitely_generated_free_absorbs_finite_free
    {G : Type*} [AddCommGroup G] [Module R G] [Module.Free R G] [Module.Finite R G]
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F) :
    Nonempty ((G × F) ≃ₗ[R] F) := by
  obtain ⟨n, ⟨eG⟩⟩ := CategoryTheory.ShortComplex.finite_free_linearEquiv_fin (R := R) (F := G)
  let ι := Module.Free.ChooseBasisIndex R F
  let b : Module.Basis ι R F := Module.Free.chooseBasis R F
  let eF : F ≃ₗ[R] (ι →₀ R) := b.repr
  letI : Infinite ι := choose_basis_index_infinite_of_not_finite (R := R) (F := F) hF
  obtain ⟨eIndex⟩ := fin_sum_equiv_self_of_infinite (n := n) (ι := ι)
  let eFin : (Fin n → R) ≃ₗ[R] (Fin n →₀ R) :=
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm
  let eSplit : ((Fin n →₀ R) × (ι →₀ R)) ≃ₗ[R] ((Fin n ⊕ ι) →₀ R) :=
    (Finsupp.sumFinsuppLEquivProdFinsupp (M := R) R).symm
  let eStd : ((Fin n → R) × F) ≃ₗ[R] F :=
    (LinearEquiv.prodCongr eFin eF).trans
      (eSplit.trans ((Finsupp.domLCongr eIndex).trans eF.symm))
  -- Replace the finite free factor by a finite coordinate block, then absorb those coordinates
  -- into the infinite basis of `F`.
  exact ⟨(LinearEquiv.prodCongr eG (LinearEquiv.refl R F)).trans eStd⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a finite stably free module becomes free after adjoining a
non-finitely generated free module. -/
lemma free_prod_of_finite_stablyFree_of_nonfinitely_generated_free
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.StablyFree R A]
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F) :
    Module.Free R (A × F) := by
  obtain ⟨m, n, ⟨eA⟩⟩ :=
    CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := R) (M := A)
  obtain ⟨eLeft⟩ :=
    nonfinitely_generated_free_absorbs_finite_free (R := R) (G := Fin m → R) (F := F) hF
  obtain ⟨eRight⟩ :=
    nonfinitely_generated_free_absorbs_finite_free (R := R) (G := Fin n → R) (F := F) hF
  let eExpand : (A × F) ≃ₗ[R] (A × ((Fin m → R) × F)) :=
    LinearEquiv.prodCongr (LinearEquiv.refl R A) eLeft.symm
  let eAssoc : (A × ((Fin m → R) × F)) ≃ₗ[R] ((A × (Fin m → R)) × F) :=
    (LinearEquiv.prodAssoc R A (Fin m → R) F).symm
  let eStab : ((A × (Fin m → R)) × F) ≃ₗ[R] ((Fin n → R) × F) :=
    LinearEquiv.prodCongr eA (LinearEquiv.refl R F)
  let eTotal : (A × F) ≃ₗ[R] F :=
    eExpand.trans (eAssoc.trans (eStab.trans eRight))
  -- Insert the finite stabilization of `A`, rewrite it to a free finite block, and absorb that
  -- block into `F`.
  exact Module.Free.of_equiv eTotal.symm

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: the submodule `Submodule.prod ⊤ F` of `A × Q` is canonically
the same module as `A × F`. -/
lemma prod_top_equiv_prod_nonempty
    {A : Type*} [AddCommGroup A] [Module R A]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (F : Submodule R Q) :
    Nonempty (↥(Submodule.prod (⊤ : Submodule R A) F) ≃ₗ[R] (A × F)) := by
  let toFun : ↥(Submodule.prod (⊤ : Submodule R A) F) → (A × F) :=
    fun x ↦ (x.1.1, ⟨x.1.2, x.2.2⟩)
  let invFun : (A × F) → ↥(Submodule.prod (⊤ : Submodule R A) F) :=
    fun x ↦ ⟨(x.1, x.2), ⟨by trivial, x.2.2⟩⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    rfl
  have hright : Function.RightInverse invFun toFun := by
    intro x
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  -- The ambient proof term carries no additional algebraic content beyond the right-coordinate
  -- membership in `F`.
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := hleft
       right_inv := hright
       map_add' := by
         intro x y
         rfl
       map_smul' := by
         intro a x
         rfl }⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: if `F` is complemented in `Q`, then `Submodule.prod ⊤ F` is
complemented in `A × Q`. -/
lemma prod_top_isComplemented_of_isComplemented
    {A : Type*} [AddCommGroup A] [Module R A]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {F : Submodule R Q} (hF : IsComplemented F) :
    IsComplemented (Submodule.prod (⊤ : Submodule R A) F) := by
  rcases hF with ⟨F', hFF'⟩
  refine ⟨Submodule.prod (⊥ : Submodule R A) F', ?_⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxLeft hxRight
    apply Prod.ext
    · simpa using hxRight.1
    · exact (Submodule.disjoint_def.mp hFF'.disjoint) x.2 hxLeft.2 hxRight.2
  · rw [codisjoint_iff]
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      have hxQ : x.2 ∈ F ⊔ F' := by
        simpa [hFF'.codisjoint.eq_top] using (show x.2 ∈ (⊤ : Submodule R Q) from by simp)
      rcases Submodule.mem_sup.1 hxQ with ⟨y, hyF, z, hzF', hyz⟩
      refine Submodule.mem_sup.2 ?_
      refine ⟨(x.1, y), ?_, (0, z), ?_, ?_⟩
      · exact ⟨by trivial, hyF⟩
      · exact ⟨by simp, hzF'⟩
      · ext <;> simp [hyz]

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: freeness of a submodule is preserved by transport across an
ambient linear equivalence. -/
lemma free_map_of_linearEquiv
    {A : Type*} [AddCommGroup A] [Module R A]
    {B : Type*} [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (K : Submodule R A) (hKfree : Module.Free R K) :
    Module.Free R (K.map e.toLinearMap) := by
  let eK : K ≃ₗ[R] K.map e.toLinearMap :=
    LinearEquiv.ofSubmodules e K (K.map e.toLinearMap) rfl
  letI : Module.Free R K := hKfree
  -- Restrict the ambient equivalence to the transported submodule.
  exact Module.Free.of_equiv eK

/-- Helper for Theorem 15.129.6: one stage of the recursive head/tail construction records the
current finite head and its complementary tail. -/
structure HeadTailState
    {Q : Type*} [AddCommGroup Q] [Module R Q] where
  H : Submodule R Q
  T : Submodule R Q
  hCompl : IsCompl H T
  hFinite : Module.Finite R H

/-- Helper for Theorem 15.129.6: one source-faithful head/tail extension step adds a finite
stably free band to the current finite head. -/
structure HeadTailStepData
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (x : Q) (H T : Submodule R Q) where
  A : Submodule R Q
  H' : Submodule R Q
  T' : Submodule R Q
  hA_le : A ≤ T
  hH_eq : H' = H ⊔ A
  hCompl : IsCompl H' T'
  hT_le : T' ≤ T
  hx : x ∈ H'
  hHfinite : Module.Finite R H'
  hAfinite : Module.Finite R A
  hAstablyFree : Module.StablyFree R A

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: the submodule `Submodule.prod ⊥ F` of `A × Q` is canonically
the same module as `F`. -/
lemma prod_bot_equiv_right_nonempty
    {A : Type*} [AddCommGroup A] [Module R A]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (F : Submodule R Q) :
    Nonempty (↥(Submodule.prod (⊥ : Submodule R A) F) ≃ₗ[R] F) := by
  let toFun : ↥(Submodule.prod (⊥ : Submodule R A) F) → F :=
    fun x ↦ ⟨x.1.2, x.2.2⟩
  let invFun : F → ↥(Submodule.prod (⊥ : Submodule R A) F) :=
    fun x ↦ ⟨(0, x), by simp [x.2]⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · symm
      simpa using x.2.1
    · rfl
  have hright : Function.RightInverse invFun toFun := by
    intro x
    apply Subtype.ext
    rfl
  -- The left coordinate is forced to be zero, so this product submodule is exactly the right
  -- factor.
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := hleft
       right_inv := hright
       map_add' := by
         intro x y
         rfl
       map_smul' := by
         intro a x
         rfl }⟩

omit [Projective R P] in
/-- Helper for Theorem 15.129.6: one source-faithful head/tail step splits off a finite stably free
head and preserves the countable-generation and maximal-local non-finiteness invariants on the
complementary tail. -/
lemma exists_finiteStablyFree_head_tail_step
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (hcg : CountablyGenerated R Q)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (s : Q) :
    ∃ A T : Submodule R Q,
      s ∈ A ∧ IsCompl A T ∧ Module.Finite R A ∧ Module.StablyFree R A ∧
        CountablyGenerated R T ∧
        (∀ m : MaximalSpectrum R,
          ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal T)) := by
  obtain ⟨A, hsA, hAcompl, hAfinite, hAstablyFree⟩ :=
    exists_finiteStablyFree_directSummand_submodule_containing
      (R := R) (P := Q) s hnotFiniteAtMax
  rcases hAcompl with ⟨T, hAT⟩
  letI : Module.Finite R A := hAfinite
  -- The source recursion keeps only the finite stably free head and passes the same two
  -- induction hypotheses to the complementary tail.
  have hTcg : CountablyGenerated R T :=
    countablyGenerated_of_isCompl_right (R := R) (P := Q) hAT.symm hcg
  have hTnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal T) :=
    localizations_not_finite_of_isCompl_of_finite_right
      (R := R) (P := Q) hAT.symm hnotFiniteAtMax
  exact ⟨A, T, hsA, hAT, hAfinite, hAstablyFree, hTcg, hTnotFiniteAtMax⟩

/-- Helper for Theorem 15.129.6: one step of the source head/tail recursion enlarges a finite head
by a finite stably free band containing the chosen tail component of `x`. -/
lemma exists_head_tail_chain_step
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q] [Nontrivial R]
    (hcgQ : CountablyGenerated R Q)
    (hnotFiniteAtMaxQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (x : Q)
    (H T : Submodule R Q) (hHT : IsCompl H T)
    [Module.Finite R H] :
    Nonempty (HeadTailStepData (R := R) x H T) := by
  let πT : Q →ₗ[R] T := T.linearProjOfIsCompl H hHT.symm
  let xt : T := πT x
  have hTproj : Module.Projective R T := by
    -- The complementary tail stays projective because the explicit projection onto `T` splits the
    -- inclusion `T → Q`.
    exact
      Module.Projective.of_split T.subtype πT
        (by
          simpa [πT] using T.linearProjOfIsCompl_comp_subtype hHT.symm)
  letI : Module.Projective R T := hTproj
  have hTcg : CountablyGenerated R T :=
    countablyGenerated_of_isCompl_right (R := R) (P := Q) hHT.symm hcgQ
  have hTnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal T) :=
    localizations_not_finite_of_isCompl_of_finite_right
      (R := R) (P := Q) hHT.symm hnotFiniteAtMaxQ
  obtain ⟨A₀, T₀, hxtA₀, hA₀T₀, hA₀finite, hA₀stablyFree, _, _⟩ :=
    exists_finiteStablyFree_head_tail_step
      (R := R) (Q := T) hTcg hTnotFiniteAtMax xt
  let eHT : (H × T) ≃ₗ[R] Q := Submodule.prodEquivOfIsCompl H T hHT
  let Aprod : Submodule R (H × T) := Submodule.prod (⊥ : Submodule R H) A₀
  let Hprod : Submodule R (H × T) := Submodule.prod (⊤ : Submodule R H) A₀
  let Tprod : Submodule R (H × T) := Submodule.prod (⊥ : Submodule R H) T₀
  let A : Submodule R Q := Aprod.map eHT.toLinearMap
  let H' : Submodule R Q := Hprod.map eHT.toLinearMap
  let T' : Submodule R Q := Tprod.map eHT.toLinearMap
  have hAprodCompl : IsCompl Hprod Tprod := by
    constructor
    · rw [Submodule.disjoint_def]
      intro y hyH hyT
      apply Prod.ext
      · simpa using hyT.1
      · exact (Submodule.disjoint_def.mp hA₀T₀.disjoint) y.2 hyH.2 hyT.2
    · rw [codisjoint_iff]
      ext y
      constructor
      · intro hy
        simp
      · intro hy
        have hyT : y.2 ∈ A₀ ⊔ T₀ := by
          simpa [hA₀T₀.codisjoint.eq_top] using (show y.2 ∈ (⊤ : Submodule R T) from by simp)
        rcases Submodule.mem_sup.1 hyT with ⟨a, haA₀, t, htT₀, hat⟩
        refine Submodule.mem_sup.2 ?_
        refine ⟨(y.1, a), ?_, (0, t), ?_, ?_⟩
        · exact ⟨by trivial, haA₀⟩
        · exact ⟨by simp, htT₀⟩
        · ext <;> simp [hat]
  have hA_le_T : A ≤ T := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw0 : w.1 = 0 := by
      simpa using hw.1
    -- The image of a pair with zero head-coordinate lands in the original tail.
    change eHT w ∈ T
    rw [Submodule.coe_prodEquivOfIsCompl' (p := H) (q := T) (h := hHT)]
    simpa [hw0]
  have hT'_le_T : T' ≤ T := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw0 : w.1 = 0 := by
      simpa using hw.1
    -- The new complementary tail still lies inside the old tail because only the right factor
    -- survives under the product equivalence.
    change eHT w ∈ T
    rw [Submodule.coe_prodEquivOfIsCompl' (p := H) (q := T) (h := hHT)]
    simpa [hw0]
  have hHleft_eq : (Submodule.prod (⊤ : Submodule R H) (⊥ : Submodule R T)).map eHT.toLinearMap = H := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hw, rfl⟩
      have hw0 : w.2 = 0 := by
        simpa using hw.2
      change eHT w ∈ H
      rw [Submodule.coe_prodEquivOfIsCompl' (p := H) (q := T) (h := hHT)]
      simpa [hw0]
    · intro hz
      let zH : H := ⟨z, hz⟩
      refine ⟨(zH, 0), ?_, ?_⟩
      · exact ⟨by trivial, by simp⟩
      change eHT (zH, 0) = z
      rw [Submodule.coe_prodEquivOfIsCompl' (p := H) (q := T) (h := hHT)]
      change ((zH : H) : Q) + (0 : Q) = z
      rw [add_zero]
  have hHprod_split :
      Hprod =
        Submodule.prod (⊤ : Submodule R H) (⊥ : Submodule R T) ⊔ Aprod := by
    ext y
    constructor
    · intro hy
      refine Submodule.mem_sup.2 ?_
      refine ⟨(y.1, 0), ?_, (0, y.2), ?_, ?_⟩
      · exact ⟨by trivial, by simp⟩
      · exact ⟨by simp, hy.2⟩
      · ext <;> simp
    · intro hy
      rcases Submodule.mem_sup.1 hy with ⟨u, hu, v, hv, huv⟩
      have hu2 : u.2 = 0 := by
        simpa using hu.2
      have hv1 : v.1 = 0 := by
        simpa using hv.1
      constructor
      · trivial
      · have hy2 : y.2 = v.2 := by
          rw [← huv]
          simp [hu2, hv1]
        simpa [hy2] using hv.2
  have hH_eq : H' = H ⊔ A := by
    -- The new head is the old head together with the newly added tail band.
    calc
      Hprod.map eHT.toLinearMap
          = (Submodule.prod (⊤ : Submodule R H) (⊥ : Submodule R T)).map eHT.toLinearMap ⊔
              A := by
              rw [hHprod_split, Submodule.map_sup]
      _ = H ⊔ A := by
            rw [hHleft_eq]
  have hH'T' : IsCompl H' T' := by
    -- Transport the explicit product decomposition across the complement equivalence `H × T ≃ Q`.
    simpa [H', T'] using (Submodule.orderIsoMapComap eHT).isCompl hAprodCompl
  have hx_mem : x ∈ H' := by
    have hxpair :
        eHT.symm x ∈ Hprod := by
      have hsymm :
          eHT.symm x = ((H.linearProjOfIsCompl T hHT) x, xt) := by
        simpa [eHT, πT, xt] using
          (Submodule.prodEquivOfIsCompl_symm_apply (p := H) (q := T) hHT x)
      rw [hsymm]
      exact ⟨by trivial, hxtA₀⟩
    exact ⟨eHT.symm x, hxpair, by simp [H']⟩
  have hAprodFinite : Module.Finite R Aprod := by
    obtain ⟨eBot⟩ := prod_bot_equiv_right_nonempty (R := R) (A := H) (Q := T) A₀
    letI : Module.Finite R A₀ := hA₀finite
    exact Module.Finite.equiv eBot.symm
  have hAprodStablyFree : Module.StablyFree R Aprod := by
    obtain ⟨eBot⟩ := prod_bot_equiv_right_nonempty (R := R) (A := H) (Q := T) A₀
    letI : Module.StablyFree R A₀ := hA₀stablyFree
    exact Module.StablyFree.of_linearEquiv (R := R) eBot
  have hAfinite : Module.Finite R A := by
    -- The added band is the transported right-factor copy of the tail-level finite stably free
    -- summand.
    exact module_finite_map_of_linearEquiv (R := R) eHT Aprod hAprodFinite
  have hAstablyFree : Module.StablyFree R A := by
    -- Stable freeness survives transport across the ambient complement equivalence.
    exact stablyFree_map_of_linearEquiv (R := R) eHT Aprod hAprodFinite hAprodStablyFree
  have hHprodFinite : Module.Finite R Hprod := by
    obtain ⟨eProd⟩ := prod_top_equiv_prod_nonempty (R := R) (A := H) (Q := T) A₀
    letI : Module.Finite R (H × A₀) := by
      letI : Module.Finite R H := inferInstance
      letI : Module.Finite R A₀ := hA₀finite
      infer_instance
    exact Module.Finite.equiv eProd.symm
  have hH'finite : Module.Finite R H' := by
    -- Finite generation of the enlarged head is computed on the explicit product model.
    exact module_finite_map_of_linearEquiv (R := R) eHT Hprod hHprodFinite
  exact
    ⟨{ A := A
       H' := H'
       T' := T'
       hA_le := hA_le_T
       hH_eq := hH_eq
       hCompl := hH'T'
       hT_le := hT'_le_T
       hx := hx_mem
       hHfinite := hH'finite
       hAfinite := hAfinite
       hAstablyFree := hAstablyFree }⟩

/-- Helper for Theorem 15.129.6: in the `s = 0`, `M = ⊤` case of Lemma `15.129.4`, the
resulting perturbation and linear form can be normalized so that the evaluation is exactly `1`. -/
lemma exists_nonzero_cyclic_split_data_of_localizations_not_finite
    [Nontrivial R]
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ t : P, ∃ φ : P →ₗ[R] R, t ≠ 0 ∧ φ t = 1 := by
  have hspan : R ∙ (0 : P) + (⊤ : Submodule R P) = ⊤ := by
    simp
  have hquot :
      ∃ m : (⊤ : Submodule R P), ∃ φbar : P →ₗ[R] (R ⧸ Ring.jacobson R), φbar ((0 : P) + m) = 1 :=
    exists_linearForm_eval_one_mod_jacobson_of_isNoetherianRing
      (R := R) (P := P) (M := ⊤) (s := 0) hnotFiniteAtMax hspan
  obtain ⟨m, φ, hunit⟩ :=
    exists_unit_linearForm_of_eval_one_mod_jacobson
      (R := R) (P := P) (M := ⊤) (s := 0) hquot
  rcases hunit with ⟨u, hu⟩
  let ψ : P →ₗ[R] R := (↑u⁻¹ : R) • φ
  have hψ : ψ (m : P) = 1 := by
    -- Rescale the unit-valued form so the chosen element is sent exactly to `1`.
    change (↑u⁻¹ : R) * φ (m : P) = 1
    have hu' : (u : R) = φ (m : P) := by
      simpa using hu
    rw [← hu']
    exact Units.inv_mul u
  have hm_ne_zero : (m : P) ≠ 0 := by
    -- The normalized evaluation cannot take the value `1` on the zero vector.
    intro hm_zero
    have hzero : ψ (m : P) = 0 := by
      simpa [hm_zero] using (show ψ (m : P) = ψ 0 from rfl)
    have h01 : (0 : R) = 1 := by
      rw [← hzero, hψ]
    exact zero_ne_one h01
  exact ⟨m, ψ, hm_ne_zero, hψ⟩

/-- Helper for Theorem 15.129.6: the `s = 0`, `M = ⊤` case of Lemma `15.129.4` already produces
one nonzero cyclic free direct summand. This is the source-faithful seed for the later blocked-band
construction. -/
lemma exists_nonzero_cyclic_free_directSummand_of_localizations_not_finite
    [Nontrivial R]
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ L : Submodule R P,
      L ≠ ⊥ ∧ IsComplemented L ∧ Module.Free R L ∧ Module.Finite R L := by
  obtain ⟨t, φ, ht_ne_zero, hφ⟩ :=
    exists_nonzero_cyclic_split_data_of_localizations_not_finite
      (R := R) (P := P) hnotFiniteAtMax
  let L : Submodule R P := R ∙ t
  have hL_ne_bot : L ≠ ⊥ := by
    -- A singleton span is trivial only when its generator is zero.
    intro hL_bot
    have ht_mem : t ∈ L := by
      simpa [L] using (Submodule.mem_span_singleton_self t)
    have ht_zero : t = 0 := by
      simpa [hL_bot] using ht_mem
    exact ht_ne_zero ht_zero
  have hLsplit : IsComplemented L ∧ Module.Free R L := by
    -- Apply the normalized split datum to the concrete cyclic span.
    simpa [L] using
      cyclicSpan_free_directSummand_of_exists_unit_linearForm
        (R := R) (P := P) (x := t) ⟨φ, by simpa [hφ] using (isUnit_one : IsUnit (1 : R))⟩
  rcases hLsplit with ⟨hLcompl, hLfree⟩
  exact ⟨L, hL_ne_bot, hLcompl, hLfree, inferInstance⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: the standard left factor
`Submodule.prod ⊤ ⊥ ⊆ (ℕ →₀ R) × K` is canonically the countable free module. -/
lemma prod_top_bot_equiv_countableFree
    {K : Type*} [AddCommGroup K] [Module R K] :
    Nonempty (↥(Submodule.prod (⊤ : Submodule R (ℕ →₀ R)) (⊥ : Submodule R K)) ≃ₗ[R] (ℕ →₀ R)) := by
  let toFun : ↥(Submodule.prod (⊤ : Submodule R (ℕ →₀ R)) (⊥ : Submodule R K)) → (ℕ →₀ R) :=
    fun x ↦ x.1.1
  let invFun :
      (ℕ →₀ R) → ↥(Submodule.prod (⊤ : Submodule R (ℕ →₀ R)) (⊥ : Submodule R K)) :=
    fun x ↦ ⟨(x, 0), by simp⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx0 : x.1.2 = 0 := by
        simpa using x.2.2
      exact hx0.symm
  have hright : Function.RightInverse invFun toFun := by
    intro x
    rfl
  -- The right coordinate is forced to be zero, so this submodule is exactly the left free factor.
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := hleft
       right_inv := hright
       map_add' := by
         intro x y
         rfl
       map_smul' := by
         intro a x
         rfl }⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: a split copy of the countable free module inside `Q` yields a
complemented free direct summand that is not finitely generated. -/
lemma exists_nonfinitely_generated_free_directSummand_of_split_countableFree
    [Nontrivial R]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (i : (ℕ →₀ R) →ₗ[R] Q) (r : Q →ₗ[R] (ℕ →₀ R))
    (hr : r.comp i = LinearMap.id) :
    ∃ F : Submodule R Q, IsComplemented F ∧ Module.Free R F ∧ ¬ Module.Finite R F := by
  obtain ⟨eSplit⟩ :=
    split_linearEquiv_prod_ker (R := R) (P := ℕ →₀ R) (F := Q) i r hr
  let F₀ : Submodule R ((ℕ →₀ R) × LinearMap.ker r) :=
    Submodule.prod (⊤ : Submodule R (ℕ →₀ R)) (⊥ : Submodule R (LinearMap.ker r))
  have hbotCompl : IsComplemented (⊥ : Submodule R (LinearMap.ker r)) := by
    refine ⟨⊤, ?_⟩
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx _
      simpa using hx
    · rw [codisjoint_iff]
      simp
  have hF₀compl : IsComplemented F₀ :=
    prod_top_isComplemented_of_isComplemented
      (R := R) (A := ℕ →₀ R) (Q := LinearMap.ker r)
      (F := (⊥ : Submodule R (LinearMap.ker r))) hbotCompl
  obtain ⟨eF₀⟩ := prod_top_bot_equiv_countableFree (R := R) (K := LinearMap.ker r)
  have hF₀free : Module.Free R F₀ := by
    -- Transport freeness from the countable free factor across the explicit identification.
    exact Module.Free.of_equiv eF₀.symm
  have hF₀notFinite : ¬ Module.Finite R F₀ := by
    intro hfinite
    letI : Module.Finite R F₀ := hfinite
    have : Module.Finite R (ℕ →₀ R) := Module.Finite.equiv eF₀
    exact not_finite_countableFree (R := R) this
  let F : Submodule R Q := F₀.map eSplit.symm.toLinearMap
  have hFcompl : IsComplemented F :=
    isComplemented_map_of_linearEquiv (R := R) eSplit.symm F₀ hF₀compl
  have hFfree : Module.Free R F :=
    free_map_of_linearEquiv (R := R) eSplit.symm F₀ hF₀free
  have hFnotFinite : ¬ Module.Finite R F := by
    intro hfinite
    let eF : F₀ ≃ₗ[R] F := LinearEquiv.ofSubmodules eSplit.symm F₀ F rfl
    have : Module.Finite R F₀ := Module.Finite.equiv eF.symm
    exact hF₀notFinite this
  exact ⟨F, hFcompl, hFfree, hFnotFinite⟩

omit [Projective R P] [IsNoetherianRing (R ⧸ Ring.jacobson R)] in
/-- Helper for Theorem 15.129.6: an internal countable family of split rank-one summands packages
into a split copy of the standard countable free module. -/
lemma exists_split_countableFree_of_internal_rankOne_band_family
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (B : ℕ → Submodule R Q)
    (hB : DirectSum.IsInternal B)
    (eta : ∀ n : ℕ, R →ₗ[R] B n)
    (eps : ∀ n : ℕ, B n →ₗ[R] R)
    (heps : ∀ n : ℕ, (eps n).comp (eta n) = LinearMap.id) :
    ∃ i : (ℕ →₀ R) →ₗ[R] Q, ∃ r : Q →ₗ[R] (ℕ →₀ R), r.comp i = LinearMap.id := by
  classical
  letI : DirectSum.Decomposition B := DirectSum.IsInternal.chooseDecomposition B hB
  let eCount : (ℕ →₀ R) ≃ₗ[R] DirectSum ℕ fun _ ↦ R :=
    finsuppLEquivDirectSum R R ℕ
  let eB : Q ≃ₗ[R] DirectSum ℕ fun n ↦ B n := DirectSum.decomposeLinearEquiv B
  let iBands : (DirectSum ℕ fun _ ↦ R) →ₗ[R] DirectSum ℕ fun n ↦ B n :=
    DirectSum.toModule R ℕ (DirectSum ℕ fun n ↦ B n)
      (fun n ↦ (DirectSum.lof R ℕ (fun n ↦ B n) n).comp (eta n))
  let rBands : (DirectSum ℕ fun n ↦ B n) →ₗ[R] DirectSum ℕ fun _ ↦ R :=
    DirectSum.toModule R ℕ (DirectSum ℕ fun _ ↦ R)
      (fun n ↦ (DirectSum.lof R ℕ (fun _ ↦ R) n).comp (eps n))
  let i : (ℕ →₀ R) →ₗ[R] Q := eB.symm.toLinearMap.comp (iBands.comp eCount.toLinearMap)
  let r : Q →ₗ[R] (ℕ →₀ R) := eCount.symm.toLinearMap.comp (rBands.comp eB.toLinearMap)
  have hrBands : rBands.comp iBands = LinearMap.id := by
    -- The direct-sum universal property reduces the split identity to each rank-one band.
    apply DirectSum.linearMap_ext
    intro n
    have hcomp1 : (eps n) ((eta n) 1) = 1 := by
      have h := congrArg (fun f : R →ₗ[R] R => f 1) (heps n)
      simpa using h
    ext a
    simp [iBands, rBands, hcomp1]
  have hr : r.comp i = LinearMap.id := by
    -- Transport the bandwise split identity across the canonical internal decomposition.
    have hri :
        r.comp i =
          eCount.symm.toLinearMap.comp ((rBands.comp iBands).comp eCount.toLinearMap) := by
      ext x n
      simp [r, i, LinearMap.comp_assoc]
    have hrewrite :
        eCount.symm.toLinearMap.comp ((rBands.comp iBands).comp eCount.toLinearMap) =
          eCount.symm.toLinearMap.comp (LinearMap.id.comp eCount.toLinearMap) := by
      exact congrArg (fun f => eCount.symm.toLinearMap.comp (f.comp eCount.toLinearMap)) hrBands
    calc
      r.comp i
          = eCount.symm.toLinearMap.comp ((rBands.comp iBands).comp eCount.toLinearMap) := hri
      _ = eCount.symm.toLinearMap.comp (LinearMap.id.comp eCount.toLinearMap) := hrewrite
      _ = LinearMap.id := by
            ext x
            simp
  exact ⟨i, r, hr⟩

/-- Helper for Theorem 15.129.6: the source recursion produces a countable chain of finite heads
and complementary tails whose successive differences are finite stably free bands. -/
lemma exists_countable_finiteStablyFree_head_chain_of_countablyGenerated_and_localizations_not_finite
    [Nontrivial R]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (hcgQ : CountablyGenerated R Q)
    (hnotFiniteAtMaxQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q)) :
    ∃ x : ℕ → Q, ∃ H T A : ℕ → Submodule R Q,
      H 0 = ⊥ ∧ T 0 = ⊤ ∧
      (∀ n, IsCompl (H n) (T n)) ∧
      (∀ n, Module.Finite R (H n)) ∧
      (∀ n, A n ≤ T n) ∧
      (∀ n, H (n + 1) = H n ⊔ A n) ∧
      (∀ n, T (n + 1) ≤ T n) ∧
      (∀ n, Module.Finite R (A n)) ∧
      (∀ n, Module.StablyFree R (A n)) ∧
      (∀ n, x n ∈ H (n + 1)) ∧
      Monotone H ∧ Antitone T ∧ iSup H = ⊤ := by
  classical
  obtain ⟨x, hxspan⟩ := exists_countable_spanning_sequence (R := R) (Q := Q) hcgQ
  let base : HeadTailState (R := R) (Q := Q) :=
    { H := ⊥
      T := ⊤
      hCompl := by
        constructor
        · rw [Submodule.disjoint_def]
          intro y hy
          simpa using hy
        · rw [codisjoint_iff]
          simp
      hFinite := inferInstance }
  let nextStep :
      ∀ (y : Q) (s : HeadTailState (R := R) (Q := Q)),
        HeadTailStepData (R := R) y s.H s.T :=
    fun y s ↦
      letI : Module.Finite R s.H := s.hFinite
      Classical.choice <|
        exists_head_tail_chain_step
          (R := R) (Q := Q) hcgQ hnotFiniteAtMaxQ y s.H s.T s.hCompl
  let state : ℕ → HeadTailState (R := R) (Q := Q) :=
    Nat.rec base fun n s ↦
      let step := nextStep (x n) s
      { H := step.H'
        T := step.T'
        hCompl := step.hCompl
        hFinite := step.hHfinite }
  let H : ℕ → Submodule R Q := fun n ↦ (state n).H
  let T : ℕ → Submodule R Q := fun n ↦ (state n).T
  let A : ℕ → Submodule R Q := fun n ↦ (nextStep (x n) (state n)).A
  have hH0 : H 0 = ⊥ := by
    rfl
  have hT0 : T 0 = ⊤ := by
    rfl
  have hCompl : ∀ n, IsCompl (H n) (T n) := by
    intro n
    exact (state n).hCompl
  have hFiniteH : ∀ n, Module.Finite R (H n) := by
    intro n
    exact (state n).hFinite
  have hAle : ∀ n, A n ≤ T n := by
    intro n
    exact (nextStep (x n) (state n)).hA_le
  have hHsucc : ∀ n, H (n + 1) = H n ⊔ A n := by
    intro n
    exact (nextStep (x n) (state n)).hH_eq
  have hTsucc : ∀ n, T (n + 1) ≤ T n := by
    intro n
    exact (nextStep (x n) (state n)).hT_le
  have hAfinite : ∀ n, Module.Finite R (A n) := by
    intro n
    exact (nextStep (x n) (state n)).hAfinite
  have hAstablyFree : ∀ n, Module.StablyFree R (A n) := by
    intro n
    exact (nextStep (x n) (state n)).hAstablyFree
  have hxmem : ∀ n, x n ∈ H (n + 1) := by
    intro n
    exact (nextStep (x n) (state n)).hx
  have hmono : Monotone H := by
    refine monotone_nat_of_le_succ ?_
    intro n
    rw [hHsucc n]
    exact le_sup_left
  have hanti : Antitone T := by
    refine antitone_nat_of_succ_le ?_
    intro n
    exact hTsucc n
  have hspan_le : Submodule.span R (Set.range x) ≤ iSup H := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact Submodule.mem_iSup_of_mem (n + 1) (hxmem n)
  have hiSupH : iSup H = ⊤ := by
    apply top_unique
    rw [← hxspan]
    exact hspan_le
  exact ⟨x, H, T, A, hH0, hT0, hCompl, hFiniteH, hAle, hHsucc, hTsucc,
    hAfinite, hAstablyFree, hxmem, hmono, hanti, hiSupH⟩

/-- Helper for Theorem 15.129.6: a later head in the recursive chain splits as the earlier head
plus the part that still lies in the earlier tail. -/
lemma head_chain_split_at_le
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (H T : ℕ → Submodule R Q)
    (hCompl : ∀ n, IsCompl (H n) (T n))
    (hmono : Monotone H)
    {n m : ℕ} (hnm : n ≤ m) :
    H m = H n ⊔ (H m ⊓ T n) ∧ Disjoint (H n) (H m ⊓ T n) := by
  constructor
  · calc
      H m = H m ⊓ (H n ⊔ T n) := by
            rw [(hCompl n).codisjoint.eq_top, inf_top_eq]
      _ = (H n ⊔ T n) ⊓ H m := by
            rw [inf_comm]
      _ = H n ⊔ (T n ⊓ H m) := by
            exact sup_inf_assoc_of_le (y := T n) (hmono hnm)
      _ = H n ⊔ (H m ⊓ T n) := by
            rw [inf_comm]
  · exact (hCompl n).disjoint.mono_right inf_le_right

/-- Helper for Theorem 15.129.6: every tail in the head/tail chain contains a later blocked band
with a split rank-one copy of `R`. -/
lemma exists_rankOne_split_data_in_later_blocked_band_of_head_chain
    [Nontrivial R]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (H T : ℕ → Submodule R Q)
    (hCompl : ∀ n, IsCompl (H n) (T n))
    (hFiniteH : ∀ n, Module.Finite R (H n))
    (hmono : Monotone H)
    (hHtop : iSup H = ⊤)
    (hnotFiniteAtMaxQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q))
    (n : ℕ) :
    ∃ m : ℕ, n < m ∧
      ∃ eta : R →ₗ[R] ↥(H m ⊓ T n), ∃ eps : ↥(H m ⊓ T n) →ₗ[R] R,
        eps.comp eta = LinearMap.id := by
  letI : Module.Finite R (H n) := hFiniteH n
  have hTnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal (T n)) :=
    localizations_not_finite_of_isCompl_of_finite_right
      (R := R) (P := Q) (hCompl n).symm hnotFiniteAtMaxQ
  have hTproj : Module.Projective R (T n) := by
    -- The stage-`n` tail is again projective because the stage decomposition gives an explicit
    -- split projection onto it.
    exact
      Module.Projective.of_split (T n).subtype
        ((T n).linearProjOfIsCompl (H n) (hCompl n).symm)
        (by
          simpa using (T n).linearProjOfIsCompl_comp_subtype (hCompl n).symm)
  letI : Module.Projective R (T n) := hTproj
  obtain ⟨t, φ, ht_ne_zero, hφ⟩ :=
    exists_nonzero_cyclic_split_data_of_localizations_not_finite
      (R := R) (P := T n) hTnotFiniteAtMax
  obtain ⟨m, hmle⟩ :=
    finite_submodule_le_some_of_iSup_eq_top
      (R := R) (P := Q) H hmono hHtop (R ∙ ((t : T n) : Q))
  have ht_memHm : ((t : T n) : Q) ∈ H m := by
    exact hmle (by simpa using Submodule.mem_span_singleton_self ((t : T n) : Q))
  have hnm : n < m := by
    by_contra hnm
    have hmn : m ≤ n := Nat.not_lt.mp hnm
    have ht_memHn : ((t : T n) : Q) ∈ H n := hmono hmn ht_memHm
    have ht_memTn : ((t : T n) : Q) ∈ T n := t.2
    have ht_zero : ((t : T n) : Q) = 0 := by
      exact (Submodule.disjoint_def.mp (hCompl n).disjoint) _ ht_memHn ht_memTn
    apply ht_ne_zero
    ext
    exact ht_zero
  let πT : Q →ₗ[R] T n := (T n).linearProjOfIsCompl (H n) (hCompl n).symm
  let ψQ : Q →ₗ[R] R := φ.comp πT
  have hψ : ψQ ((t : T n) : Q) = 1 := by
    -- The projection onto the stage-`n` tail fixes elements already in that tail.
    rw [LinearMap.comp_apply]
    rw [show πT ((t : T n) : Q) = t by
      simpa [πT] using
        (Submodule.linearProjOfIsCompl_apply_left (p := T n) (q := H n) (hCompl n).symm t)]
    exact hφ
  have ht_memBand : ((t : T n) : Q) ∈ H m ⊓ T n := by
    exact ⟨ht_memHm, t.2⟩
  obtain ⟨eta, eps, heps⟩ :=
    exists_split_maps_of_mem_with_eval_one
      (R := R) (B := H m ⊓ T n) (t := ((t : T n) : Q)) ht_memBand (ψ := ψQ) hψ
  exact ⟨m, hnm, eta, eps, heps⟩

/-- Helper for Theorem 15.129.6: a source-faithful blocked-band recursion inside the head/tail
chain yields an internal countable family carrying split rank-one copies of `R`. -/
lemma exists_internal_rankOne_band_family_of_head_chain
    [Nontrivial R]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    (H T : ℕ → Submodule R Q)
    (hH0 : H 0 = ⊥)
    (hCompl : ∀ n, IsCompl (H n) (T n))
    (hFiniteH : ∀ n, Module.Finite R (H n))
    (hmono : Monotone H)
    (hanti : Antitone T)
    (hHtop : iSup H = ⊤)
    (hnotFiniteAtMaxQ : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q)) :
    ∃ B : ℕ → Submodule R Q, ∃ eta : ∀ n, R →ₗ[R] B n, ∃ eps : ∀ n, B n →ₗ[R] R,
      DirectSum.IsInternal B ∧ ∀ n, (eps n).comp (eta n) = LinearMap.id := by
  -- TODO: package the later blocked-band split data into an internal family by choosing a strict
  -- increasing index sequence `idx`, defining `B n = H (idx (n + 1)) ⊓ T (idx n)`, proving
  -- `DirectSum.IsInternal B`, and then reusing the split maps returned by
  -- `exists_rankOne_split_data_in_later_blocked_band_of_head_chain`.
  sorry

/-- Helper for Theorem 15.129.6: over a nontrivial ring, countable generation together with the
maximal-local non-finiteness hypothesis yields a complemented free tail that is itself not finitely
generated. The `Nontrivial R` assumption removes the vacuous zero-ring case, where the conclusion
would be false. -/
lemma exists_nonfinitely_generated_free_directSummand_of_countablyGenerated_and_localizations_not_finite
    [Nontrivial R]
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    ∃ F : Submodule R P, IsComplemented F ∧ Module.Free R F ∧ ¬ Module.Finite R F := by
  -- Route correction: the earlier exact-tail route was stronger than the source proof. The source
  -- only needs one nonzero cyclic free summand in each complementary tail, and the helper above
  -- now supplies the first such tail summand together with the recursive invariants on its
  -- complement.
  obtain ⟨L₀, hL₀_ne_bot, hL₀compl, hL₀free, hL₀finite⟩ :=
    exists_nonzero_cyclic_free_directSummand_of_localizations_not_finite
      (R := R) (P := P) hnotFiniteAtMax
  rcases hL₀compl with ⟨Q₀, hL₀Q₀⟩
  letI : Module.Finite R L₀ := hL₀finite
  letI : Module.Free R L₀ := hL₀free
  have hQ₀proj : Module.Projective R Q₀ := by
    -- The complementary tail remains projective because the splitting map onto `Q₀` is explicit.
    exact
      Module.Projective.of_split Q₀.subtype
        (Q₀.linearProjOfIsCompl L₀ hL₀Q₀.symm)
        (Q₀.linearProjOfIsCompl_comp_subtype hL₀Q₀.symm)
  letI : Module.Projective R Q₀ := hQ₀proj
  have hQ₀cg : CountablyGenerated R Q₀ :=
    countablyGenerated_of_isCompl_right (R := R) (P := P) hL₀Q₀.symm hcg
  have hQ₀notFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q₀) :=
    localizations_not_finite_of_isCompl_of_finite_right
      (R := R) (P := P) hL₀Q₀.symm hnotFiniteAtMax
  have hsplit :
      ∃ i : (ℕ →₀ R) →ₗ[R] Q₀, ∃ r : Q₀ →ₗ[R] (ℕ →₀ R), r.comp i = LinearMap.id := by
    obtain ⟨x, H, T, A, hH0, hT0, hCompl, hFiniteH, hAle, hHsucc, hTsucc,
        hAfinite, hAstablyFree, hxmem, hmono, hanti, hHtop⟩ :=
      exists_countable_finiteStablyFree_head_chain_of_countablyGenerated_and_localizations_not_finite
        (R := R) (Q := Q₀) hQ₀cg hQ₀notFiniteAtMax
    obtain ⟨B, eta, eps, hInternal, heps⟩ :=
      exists_internal_rankOne_band_family_of_head_chain
        (R := R) (Q := Q₀) H T hH0 hCompl hFiniteH hmono hanti hHtop hQ₀notFiniteAtMax
    -- The blocked-band family now packages directly into a split countable free submodule of `Q₀`.
    exact exists_split_countableFree_of_internal_rankOne_band_family B hInternal eta eps heps
  rcases hsplit with ⟨i, r, hr⟩
  obtain ⟨FQ, hFQcompl, hFQfree, hFQnotFinite⟩ :=
    exists_nonfinitely_generated_free_directSummand_of_split_countableFree
      (R := R) (Q := Q₀) i r hr
  letI : Module.Free R FQ := hFQfree
  have hL₀FQfree : Module.Free R (L₀ × FQ) :=
    free_prod_of_finite_stablyFree_of_nonfinitely_generated_free
      (R := R) (A := L₀) (F := FQ) hFQnotFinite
  let K₀ : Submodule R (L₀ × Q₀) := Submodule.prod (⊤ : Submodule R L₀) FQ
  have hK₀compl : IsComplemented K₀ :=
    prod_top_isComplemented_of_isComplemented (R := R) (A := L₀) hFQcompl
  obtain ⟨eK₀⟩ := prod_top_equiv_prod_nonempty (R := R) (A := L₀) (Q := Q₀) FQ
  have hK₀free : Module.Free R K₀ := by
    -- Rewrite the product-shaped summand to the honest product module `L₀ × FQ`.
    letI : Module.Free R (L₀ × FQ) := hL₀FQfree
    exact Module.Free.of_equiv eK₀.symm
  have hK₀notFinite : ¬ Module.Finite R K₀ := by
    intro hfinite
    letI : Module.Finite R K₀ := hfinite
    have hprodFinite : Module.Finite R (L₀ × FQ) := Module.Finite.equiv eK₀
    letI : Module.Finite R (L₀ × FQ) := hprodFinite
    have hFQfinite : Module.Finite R FQ :=
      Module.Finite.of_surjective (LinearMap.snd R L₀ FQ) LinearMap.snd_surjective
    exact hFQnotFinite hFQfinite
  let eL₀Q₀ : (L₀ × Q₀) ≃ₗ[R] P := Submodule.prodEquivOfIsCompl L₀ Q₀ hL₀Q₀
  let K : Submodule R P := K₀.map eL₀Q₀.toLinearMap
  have hKcompl : IsComplemented K :=
    isComplemented_map_of_linearEquiv (R := R) eL₀Q₀ K₀ hK₀compl
  have hKfree : Module.Free R K :=
    free_map_of_linearEquiv (R := R) eL₀Q₀ K₀ hK₀free
  have hKnotFinite : ¬ Module.Finite R K := by
    intro hfinite
    let eK : K₀ ≃ₗ[R] K := LinearEquiv.ofSubmodules eL₀Q₀ K₀ K rfl
    have : Module.Finite R K₀ := Module.Finite.equiv eK.symm
    exact hK₀notFinite this
  exact ⟨K, hKcompl, hKfree, hKnotFinite⟩

/-- Helper for Theorem 15.129.6: under countable generation and maximal-local non-finiteness,
every element lies in some free direct summand. -/
lemma exists_free_directSummand_submodule_containing_of_countablyGenerated_and_localizations_not_finite
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P))
    (x : P) :
    ∃ F : Submodule R P, x ∈ F ∧ IsComplemented F ∧ Module.Free R F := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI : Subsingleton R := hR
    letI : Subsingleton P := Module.subsingleton R P
    refine ⟨⊥, ?_, ?_, ?_⟩
    · -- Over the zero ring every module element is zero, so the bottom summand contains `x`.
      simpa using (show x = 0 from Subsingleton.elim _ _)
    · refine ⟨⊤, ?_⟩
      constructor
      · rw [Submodule.disjoint_def]
        intro y hy _
        simpa using hy
      · rw [codisjoint_iff]
        exact Subsingleton.elim _ _
    · letI : Subsingleton (⊥ : Submodule R P) := by infer_instance
      exact Module.Free.of_subsingleton (R := R) (N := (⊥ : Submodule R P))
  · letI : Nontrivial R := hR
    obtain ⟨A, hxA, hAcompl, hAfinite, hAstablyFree⟩ :=
      exists_finiteStablyFree_directSummand_submodule_containing
        (R := R) (P := P) x hnotFiniteAtMax
    rcases hAcompl with ⟨Q, hAQ⟩
    letI : Module.Finite R A := hAfinite
    letI : Module.StablyFree R A := hAstablyFree
    have hQproj : Module.Projective R Q := by
      -- The complementary summand inherits projectivity from the split projection.
      exact
        Module.Projective.of_split Q.subtype
          (Q.linearProjOfIsCompl A hAQ.symm)
          (Q.linearProjOfIsCompl_comp_subtype hAQ.symm)
    letI : Module.Projective R Q := hQproj
    have hQcg : CountablyGenerated R Q :=
      countablyGenerated_of_isCompl_right (R := R) (P := P) hAQ.symm hcg
    have hQnotFiniteAtMax : ∀ m : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal Q) :=
      localizations_not_finite_of_isCompl_of_finite_right (R := R) (P := P) hAQ.symm hnotFiniteAtMax
    obtain ⟨F, hFcompl, hFfree, hFnotFinite⟩ :=
      exists_nonfinitely_generated_free_directSummand_of_countablyGenerated_and_localizations_not_finite
        (R := R) (P := Q) hQcg hQnotFiniteAtMax
    letI : Module.Free R F := hFfree
    have hAFfree : Module.Free R (A × F) :=
      free_prod_of_finite_stablyFree_of_nonfinitely_generated_free
        (R := R) (A := A) (F := F) hFnotFinite
    let K0 : Submodule R (A × Q) := Submodule.prod (⊤ : Submodule R A) F
    have hK0compl : IsComplemented K0 :=
      prod_top_isComplemented_of_isComplemented (R := R) (A := A) hFcompl
    obtain ⟨eK0⟩ := prod_top_equiv_prod_nonempty (R := R) (A := A) (Q := Q) F
    have hK0free : Module.Free R K0 := by
      -- Rewrite the source-facing product submodule as the actual product module `A × F`.
      letI : Module.Free R (A × F) := hAFfree
      exact Module.Free.of_equiv eK0.symm
    let eAQ : (A × Q) ≃ₗ[R] P := Submodule.prodEquivOfIsCompl A Q hAQ
    let K : Submodule R P := K0.map eAQ.toLinearMap
    have hxK : x ∈ K := by
      let xA : A := ⟨x, hxA⟩
      have hxK0 : (xA, ((0 : F) : Q)) ∈ K0 := by
        exact ⟨by simp, by simpa using (show ((0 : F) : Q) ∈ F from by simp)⟩
      refine ⟨(xA, ((0 : F) : Q)), hxK0, ?_⟩
      -- Under the complement equivalence, the chosen point in the head factor maps back to `x`.
      have hImage :
          Submodule.prodEquivOfIsCompl A Q hAQ (xA, ((0 : F) : Q)) =
            xA + ((0 : F) : Q) :=
        Submodule.coe_prodEquivOfIsCompl' (p := A) (q := Q) (h := hAQ)
          (x := (xA, ((0 : F) : Q)))
      change Submodule.prodEquivOfIsCompl A Q hAQ (xA, ((0 : F) : Q)) = x
      rw [hImage]
      change ((xA : A) : P) + (0 : P) = x
      simpa using (show ((xA : A) : P) = x from rfl)
    have hKcompl : IsComplemented K :=
      isComplemented_map_of_linearEquiv (R := R) eAQ K0 hK0compl
    have hKfree : Module.Free R K :=
      free_map_of_linearEquiv (R := R) eAQ K0 hK0free
    -- Route correction: the remaining source-faithful work is isolated in the free-tail theorem,
    -- while the head absorption and transport back to `P` are now verified.
    exact ⟨K, hxK, hKcompl, hKfree⟩

/-- Bridge from the Chapter 15 maximal-local hypothesis to the Chapter 10 owner
`HasFiniteFreeComplementSummandProperty`. This packages the repeated finite-summand splitting
argument needed to invoke Lemma `10.85.2`, while keeping the source-facing freeness theorem below
as the main public statement for Theorem `15.129.6`. -/
theorem hasFiniteFreeComplementSummandProperty_of_localizations_not_finite
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    HasFiniteFreeComplementSummandProperty R P := by
  intro N N' hNN' hN'finite hN'free x
  letI : Module.Finite R N' := hN'finite
  letI : Module.Free R N' := hN'free
  have hNproj : Module.Projective R N :=
    Module.Projective.of_split N.subtype
      (N.linearProjOfIsCompl N' hNN')
      (N.linearProjOfIsCompl_comp_subtype hNN')
  letI : Module.Projective R N := hNproj
  have hNcg : CountablyGenerated R N :=
    countablyGenerated_of_isCompl_right (R := R) (P := P) hNN' hcg
  have hNnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) :=
    localizations_not_finite_of_isCompl_of_finite_right (R := R) (P := P) hNN' hnotFiniteAtMax
  -- Route correction: after repairing the bridge to carry `hcg`, the owner property reduces to
  -- the source-faithful elementwise free-summand statement on the complementary summand `N`.
  obtain ⟨F, hxF, hFcompl, hFfree⟩ :=
    exists_free_directSummand_submodule_containing_of_countablyGenerated_and_localizations_not_finite
      (R := R) (P := N) hNcg hNnotFiniteAtMax x
  rcases hFcompl with ⟨F', hFF'⟩
  exact ⟨F, F', hxF, hFfree, hFF'⟩

end Module

-- Proof sketch: first pass from the maximal-local hypothesis to the Chapter 10 owner
-- `Module.HasFiniteFreeComplementSummandProperty R P` via the bridge theorem above, then apply
-- Lemma `10.85.2`.
/-- Theorem 15.129.6: if `R ⧸ Ring.jacobson R` is Noetherian and `P` is a countably generated
projective `R`-module whose localizations at maximal ideals are not finitely generated, then `P`
is free. This is the Lean rendering of the condition that each `P_𝔪` has infinite rank. -/
theorem free_of_countablyGenerated_projective_of_localizations_not_finite
    (hcg : CountablyGenerated R P)
    (hnotFiniteAtMax : ∀ m : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal P)) :
    Free R P := by
  exact Module.free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty hcg
    (Module.hasFiniteFreeComplementSummandProperty_of_localizations_not_finite hcg hnotFiniteAtMax)

end
