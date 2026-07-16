import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_14_Emmanouil
import StacksProject_2024.stacks_project.Chap15.Lemma_15_95_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AdicCompletion
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat A ⥤ DMod)
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling for Lemma 15.95.6:
- primary domain: derived `I`-adic completion of degree-zero objects in `D(A)`, together with the
  module-theoretic tensor and localization realizations that feed the source text;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `singleFunctorIso_of_isGE_of_isLE`,
  `derivedCompletionOfModule_cohomology_shortExact`,
  `DerivedCategory.homology_derivedCompletionOf_iso_adicCompletion`,
  `AdicCompletion`,
  `tor_eventually_zero_map_quotient_pow`,
  `LocalizedModule.equivTensorProduct`;
- best owner abstraction: the main public statements should identify the canonical derived
  completion object `((single₀).obj X)^∧[I, I.fg_of_isNoetherianRing]` itself with the canonical
  degree-zero owner `(single₀).obj (AdicCompletion I X)` in `D(A)`, formalized propositionally as
  `IsIsomorphic` because this file does not yet expose a canonical comparison morphism; the
  degree-zero comparison and off-zero vanishing remain companion API used to build that
  identification through `singleFunctorIso_of_isGE_of_isLE`; the Milnor short exact sequence of
  Lemma `15.95.3` is the core owner input, while the tensor-product/localization descriptions
  remain bridge/view input to the proof;
- primitive vs. derived:
  primitive data are the ideal `I`, the finite module `M`, and the auxiliary flat or localized
  module appearing in the two source statements;
  derived API is the source-facing identification of the actual derived-completion object with the
  degree-zero object on `AdicCompletion I X`, together with degree-zero comparison and off-zero
  vanishing as supporting companions.

Source/core/bridge triage:
- `source-facing`: the two derived-category completion isomorphisms below for `M ⊗[A] N` and
  `Away f M`;
- `core/canonical`: `ModuleCat.single0Functor`, `DerivedCategory.derivedCompletionOf`, the
  Milnor short exact sequence owner `derivedCompletionOfModule_cohomology_shortExact`,
  `singleFunctorIso_of_isGE_of_isLE`, and the module-side completion owner `AdicCompletion`;
- `bridge/view`: the tensor-product model and the localization/tensor comparison
  `LocalizedModule.equivTensorProduct`. -/

-- Proof sketch: apply Lemma `15.95.3` to `X := M ⊗[A] N`. Since `N` is flat, the Tor towers
-- `Tor_i^A(X, A / I^(n+1))` identify with `Tor_i^A(M, A / I^(n+1)) ⊗[A] N`, so Lemma `15.27.3`
-- makes them pro-zero for `i > 0`. The `i = 0` term is the usual quotient tower
-- `(M ⊗[A] N) / I^(n+1)(M ⊗[A] N)`.
/-- Helper for Lemma `15.95.6`: an abelian-group tower with eventual zero transition maps has
vanishing inverse limit and vanishing first derived inverse limit. -/
theorem addCommGroup_limit_and_firstDerivedLimit_isZero_of_eventually_zero_transition
    (T : SequentialInverseSystem AddCommGrpCat)
    (hzero : ∀ n : ℕ, ∃ (m : ℕ) (hnm : n ≤ m), T.transitionMap hnm = 0) :
    IsZero (limit T) ∧ IsZero T.firstDerivedLimit := by
  have hlimit : IsZero (limit T) := by
    -- Proof comment: every limit projection factors through a late zero transition map, so each
    -- projection is zero and hence the limit object itself is zero.
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply limit.hom_ext
    intro n
    rcases hzero n.unop with ⟨m, hnm, htm⟩
    calc
      limit.π T (Opposite.op n.unop) =
          limit.π T (Opposite.op m) ≫ T.transitionMap hnm := by
            simpa [SequentialInverseSystem.transitionMap] using
              (limit.w T ((homOfLE hnm).op)).symm
      _ = 0 := by simp [htm]
  have hml : T.IsMittagLeffler := by
    -- Proof comment: once a transition into stage `i` is zero, every later image into stage `i`
    -- is already the zero image, so the images stabilize at `⊥`.
    intro i
    rcases hzero i with ⟨c, hic, htc⟩
    refine ⟨c, hic, ?_⟩
    intro k hck
    have hcomp :
        T.transitionMap (hic.trans hck) = T.transitionMap hck ≫ T.transitionMap hic := by
      have hh :
          (homOfLE (hic.trans hck)).op = (homOfLE hck).op ≫ (homOfLE hic).op := by
        subsingleton
      simpa [SequentialInverseSystem.transitionMap, Functor.map_comp] using congrArg T.map hh
    calc
      imageSubobject (T.transitionMap (hic.trans hck))
          = imageSubobject (T.transitionMap hck ≫ T.transitionMap hic) := by
              rw [hcomp]
      _ = imageSubobject (0 : T.obj (Opposite.op k) ⟶ T.obj (Opposite.op i)) := by
            simp [htc, Category.assoc]
      _ = imageSubobject (T.transitionMap hic) := by
            simpa [htc]
  -- Proof comment: Emmanouil's criterion now turns the Mittag-Leffler property into the desired
  -- vanishing of `R^1 lim`.
  have hfirst :
      IsZero T.firstDerivedLimit ∧ IsZero T.countableCoproduct.firstDerivedLimit :=
    (CategoryTheory.SequentialInverseSystem
      .isMittagLeffler_iff_firstDerivedLimit_and_countableCoproduct_firstDerivedLimit_isZero
        T).1 hml
  exact ⟨hlimit, hfirst.1⟩

/-- Helper for Lemma `15.95.6`: a fixed-gap zero condition on an abelian-group tower forces both
`lim` and `R^1 lim` to vanish. -/
theorem addCommGroup_limit_and_firstDerivedLimit_isZero_of_fixed_gap_zero
    (T : SequentialInverseSystem AddCommGrpCat) (c : ℕ)
    (hzero : ∀ n : ℕ, T.transitionMap (Nat.le_add_right n c) = 0) :
    IsZero (limit T) ∧ IsZero T.firstDerivedLimit := by
  -- Proof comment: this is just the fixed-gap specialization of the eventual-zero transition
  -- statement above.
  refine addCommGroup_limit_and_firstDerivedLimit_isZero_of_eventually_zero_transition T ?_
  intro n
  exact ⟨n + c, Nat.le_add_right n c, hzero n⟩

/-- Helper for Lemma `15.95.6`: in a short exact sequence of modules, vanishing of the outer
terms forces vanishing of the middle term. -/
theorem shortComplex_isZero_middle_of_exact_of_isZero_ends
    {X₁ X₂ X₃ : ModuleCat A}
    {α : X₁ ⟶ X₂} {β : X₂ ⟶ X₃} {hαβ : α ≫ β = 0}
    (hexact : (ShortComplex.mk α β hαβ).Exact)
    (h₁ : IsZero X₁) (h₃ : IsZero X₃) :
    IsZero X₂ := by
  -- Proof comment: exactness and a zero source make `β` mono; a mono into a zero object then
  -- forces the middle module to vanish.
  have hmono : Mono β := by
    exact ((ShortComplex.mk α β hαβ).exact_iff_mono (h₁.eq_of_src _ _)).1 hexact
  exact IsZero.of_mono β h₃

/-- Helper for Lemma `15.95.6`: a natural isomorphism of module-valued sequential inverse
systems induces the corresponding isomorphism on inverse limits. -/
theorem module_sequential_limit_iso_of_natIso
    {Msys Nsys : SequentialInverseSystem (ModuleCat A)} (e : Msys ≅ Nsys) :
    limit Msys ≅ limit Nsys := by
  -- Proof comment: this is the canonical limit comparison attached to a natural isomorphism of
  -- inverse systems.
  exact HasLimit.isoOfNatIso e

/-- Helper for Lemma `15.95.6`: a natural isomorphism of module-valued sequential inverse
systems induces the corresponding isomorphism on the first derived inverse limit. -/
theorem module_sequential_firstDerivedLimit_iso_of_natIso
    {Msys Nsys : SequentialInverseSystem (ModuleCat A)} (e : Msys ≅ Nsys) :
    Msys.firstDerivedLimit ≅ Nsys.firstDerivedLimit := by
  -- Proof comment: `R^1 lim` is defined as the Milnor cokernel, so the inverse natural
  -- transformation gives the inverse map after applying `firstDerivedLimitMap`.
  refine ⟨SequentialInverseSystem.firstDerivedLimitMap e.hom,
    SequentialInverseSystem.firstDerivedLimitMap e.inv, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π (SequentialInverseSystem.derivedLimitDifferenceMap Msys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]
  · apply (cancel_epi (cokernel.π (SequentialInverseSystem.derivedLimitDifferenceMap Nsys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]

/-- Helper for Lemma `15.95.6`: quotient-stage evaluations on an adic completion commute with the
transition maps of the positive quotient tower. -/
theorem completion_eval_factor
    (I : Ideal A) {X : Type u} [AddCommGroup X] [Module A X]
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I X) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let p : AdicCompletion I X → Prop := fun y =>
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y
  change p x
  -- Proof comment: descend to a Cauchy representative so the compatibility becomes the defining
  -- relation among the quotient coordinates of that representative.
  refine AdicCompletion.induction_on (I := I) (M := X) x ?_
  intro f
  change
    Ideal.Quotient.factorPow I hmn
        (AdicCompletion.evalₐ I n (AdicCompletion.mk I X f)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mk I X f)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simpa using AdicCompletion.Ideal.mk_eq_mk (I := I) hmn f

/-- Helper for Lemma `15.95.6`: the positive quotient tower of a module, whose stage `n` is
`X ⧸ I ^ (n + 1) • ⊤`. -/
abbrev positive_quotient_tower
    (I : Ideal A) (X : Type u) [AddCommGroup X] [Module A X] :
    SequentialInverseSystem (ModuleCat A) :=
  Functor.ofOpSequence fun n ↦
    ModuleCat.ofHom <| Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))

/-- Helper for Lemma `15.95.6`: the adic completion evaluations define a compatible family of
stage maps for the positive quotient tower. -/
theorem positive_quotient_tower_completion_compatible
    (I : Ideal A) {X : Type u} [AddCommGroup X] [Module A X] (n : ℕ) :
    ModuleCat.ofHom (AdicCompletion.evalₐ I (n + 2)) ≫
        (positive_quotient_tower (A := A) (I := I) X).map (homOfLE (Nat.le_succ n)).op =
      ModuleCat.ofHom (AdicCompletion.evalₐ I (n + 1)) := by
  -- Proof comment: unfold the successor map of the explicit quotient tower and then apply the
  -- stagewise compatibility lemma for `AdicCompletion.evalₐ`.
  ext x
  simpa [positive_quotient_tower, Functor.ofOpSequence_map_homOfLE_succ] using
    completion_eval_factor (I := I) (m := n + 1) (n := n + 2) (Nat.le_succ (n + 1)) x

/-- Helper for Lemma `15.95.6`: the inverse limit of the positive quotient tower is the usual
adic completion. -/
noncomputable def positive_quotient_tower_limit_iso_adicCompletion
    (I : Ideal A) (X : Type u) [AddCommGroup X] [Module A X] :
    limit (positive_quotient_tower (A := A) (I := I) X) ≅
      ModuleCat.of A (AdicCompletion I X) := by
  let T : SequentialInverseSystem (ModuleCat A) :=
    positive_quotient_tower (A := A) (I := I) X
  let toCompletion :
      limit T ⟶ ModuleCat.of A (AdicCompletion I X) :=
    ModuleCat.ofHom
      { toFun := fun x ↦
          ⟨fun
            | 0 => 0
            | n + 1 => (limit.π T (Opposite.op n)).hom x,
            by
              intro m n hmn
              cases m with
              | zero =>
                  simp
              | succ m =>
                  cases n with
                  | zero =>
                      cases Nat.not_succ_le_zero _ hmn
                  | succ n =>
                      have hmn' : m ≤ n := Nat.succ_le_succ_iff.mp hmn
                      cases Nat.eq_or_lt_of_le hmn' with
                      | inl hEq =>
                          subst hEq
                          simp
                      | inr hlt =>
                          have hstep : m + 1 ≤ n := Nat.succ_le_of_lt hlt
                          calc
                            Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn')
                                ((limit.π T (Opposite.op n)).hom x)
                                = Ideal.Quotient.factorPow I (Nat.le_succ m)
                                    ((limit.π T (Opposite.op (m + 1))).hom x) := by
                                      simpa [T, positive_quotient_tower,
                                        Functor.ofOpSequence_map_homOfLE_succ] using
                                        congrArg (fun f ↦ f.hom x)
                                          (limit.w T ((homOfLE hstep).op))
                            _ = (limit.π T (Opposite.op m)).hom x := by
                                  simpa [T, positive_quotient_tower,
                                    Functor.ofOpSequence_map_homOfLE_succ] using
                                    congrArg (fun f ↦ f.hom x)
                                      (limit.w T ((homOfLE (Nat.le_succ m)).op)) }
        map_add' := by
          intro x y
          ext n
          cases n with
          | zero =>
              simp
          | succ n =>
              simp
        map_smul' := by
          intro a x
          ext n
          cases n with
          | zero =>
              simp
          | succ n =>
              simp }
  let fromCompletion :
      ModuleCat.of A (AdicCompletion I X) ⟶ limit T :=
    limit.lift T
      { pt := ModuleCat.of A (AdicCompletion I X)
        π := NatTrans.ofOpSequence
          (fun n ↦ ModuleCat.ofHom (AdicCompletion.eval I X (n + 1)))
          (fun n ↦ by
            -- Proof comment: the completion coordinates already satisfy the quotient transition
            -- relation, so these stage maps form a cone over the positive quotient tower.
            ext x
            simp [T, positive_quotient_tower, Functor.ofOpSequence_map_homOfLE_succ,
              AdicCompletion.transitionMap_comp_eval]) }
  refine
    ⟨toCompletion.hom, fromCompletion, ?_, ?_⟩
  · -- Proof comment: two endomorphisms of the limit agree once all stage projections agree.
    apply limit.hom_ext
    intro n
    cases Opposite.rec' n with
    | _ n =>
        ext x
        simp [toCompletion, fromCompletion, T]
  · -- Proof comment: two completion elements agree once all quotient coordinates agree.
    ext x n
    cases n with
    | zero =>
        simp [toCompletion, fromCompletion]
    | succ n =>
        simp [toCompletion, fromCompletion, T]

/-- Helper for Lemma `15.95.6`: after transporting the positive-degree Tor tower through flat
tensoring, the shifted positive Tor tower for `M ⊗[A] N` should have vanishing `lim` and
`R^1 lim`. -/
theorem tensor_positive_tor_tower_limit_and_firstDerivedLimit_isZero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N]
    (p : ℕ) (hp : 0 < p) :
    IsZero (limit ((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) p).shift 1)) ∧
      IsZero (((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) p).shift 1).firstDerivedLimit) := by
  -- Route correction: the remaining source-faithful blocker is not the Milnor exact sequence
  -- itself, but the tensor/Tor comparison needed to move the pro-zero transition maps from
  -- `Tor_p^A(M, A / I^(n+1))` to the corresponding tower for `M ⊗[A] N`.
  -- TODO: compare each shifted stage
  -- `Tor[A, p](M ⊗[A] N, A ⧸ I^(n + 1) • ⊤)` with
  -- `Tor[A, p](M, A ⧸ I^(n + 1) • ⊤) ⊗[A] N`, prove that the fixed-gap zero transition maps from
  -- `tor_eventually_zero_map_quotient_pow` survive under flat tensoring, transport `lim` and
  -- `R^1 lim` along that tower isomorphism via
  -- `module_sequential_limit_iso_of_natIso` and
  -- `module_sequential_firstDerivedLimit_iso_of_natIso`, and then apply
  -- `addCommGroup_limit_and_firstDerivedLimit_isZero_of_fixed_gap_zero` to the forgotten tower.
  sorry

/-- Helper for Lemma `15.95.6`: the degree-zero shifted Tor tower for `M ⊗[A] N` should be the
ordinary positive quotient tower, so its limit is the usual adic completion. -/
theorem tensor_zero_tor_tower_limit_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    (N : Type u) [AddCommGroup N] [Module A N] :
    Nonempty
      (limit ((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) 0).shift 1) ≅
        ModuleCat.of A (AdicCompletion I (M ⊗[A] N))) := by
  -- Route correction: the degree-zero branch is now reduced to an owner-level comparison.
  -- TODO: package the stagewise `Tor_0`-to-quotient identification into a natural isomorphism
  -- from `((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) 0).shift 1)` to
  -- `positive_quotient_tower I (M ⊗[A] N)`, then identify the limit of
  -- `positive_quotient_tower I (M ⊗[A] N)` with `AdicCompletion I (M ⊗[A] N)` using the
  -- compatible family from `positive_quotient_tower_completion_compatible` and the universal
  -- property of `limit`.
  sorry

/-- Degree-zero companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then the
zero-th cohomology of the derived completion of `(M ⊗[A] N)[0]` is isomorphic to the ordinary
`I`-adic completion of `M ⊗[A] N`. This is the degree-zero input used to build the full
derived-object identification in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`. -/
theorem tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (M ⊗[A] N))) := by
  -- Route correction: the source-faithful proof uses the degree-zero Milnor short exact sequence
  -- from Lemma `15.95.3`, not Lemma `15.95.4`, because `M ⊗[A] N` need not be finite.
  rcases
      derivedCompletionOfModule_cohomology_shortExact
        (I := I) (M := M ⊗[A] N) 0 with
    ⟨ι, π, hιπ, hshort⟩
  have hleft :
      IsZero (((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) 1).shift 1).firstDerivedLimit) :=
    (tensor_positive_tor_tower_limit_and_firstDerivedLimit_isZero I M N 1 (by omega)).2
  -- Proof comment: once the left Milnor obstruction vanishes, exactness makes the right map
  -- `π` mono; short exactness already records that it is epi, hence `π` is an isomorphism.
  have hmono : Mono π := by
    exact ((ShortComplex.mk ι π hιπ).exact_iff_mono (hleft.eq_of_src _ _)).1 hshort.exact
  let _ : Mono π := hmono
  let _ : Epi π := hshort.epi_g
  let eπ :
      (H 0).obj (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[
        I, I.fg_of_isNoetherianRing]) ≅
        limit ((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) 0).shift 1) :=
    asIso π
  let eLimit :
      limit ((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) 0).shift 1) ≅
        ModuleCat.of A (AdicCompletion I (M ⊗[A] N)) :=
    Classical.choice (tensor_zero_tor_tower_limit_isomorphic_adicCompletion I M N)
  exact ⟨eπ ≪≫ eLimit⟩

-- Proof sketch: for `X = M ⊗[A] N`, flatness of `N` identifies the tower
-- `Tor_i^A(X, A / I^(n + 1))` with `Tor_i^A(M, A / I^(n + 1)) ⊗[A] N`. Lemma `15.27.3` makes the
-- positive-degree Tor towers pro-zero, so Lemma `15.95.3` yields that the derived `I`-adic
-- completion of `X[0]` has no nonzero cohomology outside degree `0`. This off-zero vanishing,
-- together with
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, supplies the
-- proposition-level
-- derived-category isomorphism in `tensor_finite_flat_derivedCompletion_usual_adicCompletion`.
/-- Off-zero vanishing companion for Lemma `15.95.6 (1)`: if `M` is finite and `N` is flat, then
the derived completion of `(M ⊗[A] N)[0]` has zero cohomology in every degree `n ≠ 0`. Together
with `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion`, this yields
the full derived-object identification with the degree-zero object on the ordinary completion. -/
theorem tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])) := by
  by_cases hneg : n < 0
  · let i : ℕ := Int.natAbs n
    have hi : 0 < i := by
      dsimp [i]
      exact Int.natAbs_pos.mpr hn
    have hn' : -((i : ℤ)) = n := by
      dsimp [i]
      simpa using Int.neg_natAbs_of_nonpos (le_of_lt hneg)
    rcases
        derivedCompletionOfModule_cohomology_shortExact
          (I := I) (M := M ⊗[A] N) i with
      ⟨ι, π, hιπ, hshort⟩
    have hleft :
        IsZero (((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) (i + 1)).shift 1)
          .firstDerivedLimit) :=
      (tensor_positive_tor_tower_limit_and_firstDerivedLimit_isZero I M N (i + 1)
        (Nat.succ_pos _)).2
    have hright :
        IsZero (limit ((idealPowerQuotientTorInverseSystem I (M ⊗[A] N) i).shift 1)) :=
      (tensor_positive_tor_tower_limit_and_firstDerivedLimit_isZero I M N i hi).1
    have hmiddle :
        IsZero ((H (-((i : ℤ)))).obj
          (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])) := by
      -- Proof comment: in negative degrees, Lemma `15.95.3` gives a short exact sequence whose
      -- two outer terms are killed by the positive-Tor pro-zero input.
      exact shortComplex_isZero_middle_of_exact_of_isZero_ends hshort.exact hleft hright
    simpa [hn'] using hmiddle
  · have hpos : 0 < n := by
      omega
    let K :
        DMod :=
      (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])
    -- Proof comment: positive cohomology vanishes once the derived completion object is known to
    -- stay in `D^{≤ 0}`.
    let _ : K.IsLE 0 := inferInstance
    simpa [K] using DerivedCategory.isZero_of_isLE K 0 n hpos

-- Proof sketch: combine the degree-zero comparison
-- `tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion` with the off-zero
-- vanishing in `tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero` to obtain the
-- canonical bounds `IsGE 0` and `IsLE 0`, then identify the resulting single-degree object with
-- the ordinary completion.
/-- Lemma 15.95.6 (1): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `N` is a flat `A`-module, then the derived `I`-adic completion of `M ⊗[A] N`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M ⊗[A] N`. -/
theorem tensor_finite_flat_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module.Flat A N] :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (M ⊗[A] N)))) := by
  classical
  let K :
      DMod :=
    (((single₀).obj (ModuleCat.of A (M ⊗[A] N)))^∧[I, I.fg_of_isNoetherianRing])
  have hGE : K.IsGE 0 := by
    -- Proof comment: the off-zero vanishing companion kills all negative homology of `K`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact
      tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero I M N i
        (by omega)
  have hLE : K.IsLE 0 := by
    -- Proof comment: the same companion kills all positive homology of `K`.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact
      tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero I M N i
        (by omega)
  let eSingle :
      K ≅ (single₀).obj ((H 0).obj K) := by
    -- Proof comment: once `K` is concentrated in degree `0`, the standard `t`-structure owner
    -- identifies it with the degree-zero single object on its zeroth homology.
    let _ : K.IsGE 0 := hGE
    let _ : K.IsLE 0 := hLE
    simpa [K] using
      (singleFunctorIso_of_isGE_of_isLE (A := ModuleCat A) K (0 : ℤ))
  let eZero :
      ((H 0).obj K) ≅ ModuleCat.of A (AdicCompletion I (M ⊗[A] N)) :=
    Classical.choice
      (tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion I M N)
  exact ⟨eSingle ≪≫ (single₀).mapIso eZero⟩

-- Proof sketch: specialize the tensor statement to `N = Localization.Away f`, then transport the
-- conclusion across the canonical localization/tensor equivalence
-- `LocalizedModule.equivTensorProduct`.
/-- Degree-zero companion for Lemma `15.95.6 (2)`: for a finite module `M`, the zero-th
cohomology of the derived completion of `M_f[0]` is isomorphic to the ordinary `I`-adic
completion of the localization `M_f`. This is obtained by transporting part `(1)` along
`LocalizedModule.equivTensorProduct`. -/
theorem localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing]))
      (ModuleCat.of A (AdicCompletion I (Away f M))) := by
  classical
  let eLinear : (M ⊗[A] Localization.Away f) ≃ₗ[A] Away f M :=
    (TensorProduct.comm A M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars A)
  let eModule :
      ModuleCat.of A (M ⊗[A] Localization.Away f) ≅ ModuleCat.of A (Away f M) :=
    eLinear.toModuleIso
  let eSource :
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] Localization.Away f)))^∧[
          I, I.fg_of_isNoetherianRing])) ≅
        ((H 0).obj
          (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])) :=
    (H 0).mapIso
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).mapIso
        ((single₀).mapIso eModule))
  let eTarget :
      ModuleCat.of A (AdicCompletion I (M ⊗[A] Localization.Away f)) ≅
        ModuleCat.of A (AdicCompletion I (Away f M)) :=
    (AdicCompletion.congr I eLinear).toModuleIso
  let eTensor :
      ((H 0).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] Localization.Away f)))^∧[
          I, I.fg_of_isNoetherianRing])) ≅
        ModuleCat.of A (AdicCompletion I (M ⊗[A] Localization.Away f)) :=
    Classical.choice
      (tensor_finite_flat_homology_zero_derivedCompletion_isomorphic_adicCompletion
        I M (Localization.Away f))
  -- Proof comment: transport the tensor-product degree-zero comparison across the standard
  -- identification `M_f ≃ M ⊗[A] A_f` and then across ordinary completion.
  exact ⟨eSource.symm ≪≫ eTensor ≪≫ eTarget⟩

-- Proof sketch: specialize the previous tensor-product statement to `N = Localization.Away f`,
-- use the standard identification of `M_f` with `M ⊗[A] A_f`, and transport the resulting
-- degree-zero cohomology description along that localization equivalence, and reuse the same
-- Tor-vanishing argument to conclude that all other cohomology groups vanish.
/-- Off-zero vanishing companion for Lemma `15.95.6 (2)`: for a finite module `M`, the derived
completion of `M_f[0]` has zero cohomology in every degree `n ≠ 0`. -/
theorem localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A)
    (n : ℤ) (hn : n ≠ 0) :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])) := by
  let eLinear : (M ⊗[A] Localization.Away f) ≃ₗ[A] Away f M :=
    (TensorProduct.comm A M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars A)
  let eModule :
      ModuleCat.of A (M ⊗[A] Localization.Away f) ≅ ModuleCat.of A (Away f M) :=
    eLinear.toModuleIso
  let eSource :
      ((H n).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] Localization.Away f)))^∧[
          I, I.fg_of_isNoetherianRing])) ≅
        ((H n).obj
          (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])) :=
    (H n).mapIso
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).mapIso
        ((single₀).mapIso eModule))
  have hTensor :
      IsZero ((H n).obj
        (((single₀).obj (ModuleCat.of A (M ⊗[A] Localization.Away f)))^∧[
          I, I.fg_of_isNoetherianRing])) :=
    tensor_finite_flat_homology_derivedCompletion_isZero_of_ne_zero
      I M (Localization.Away f) n hn
  -- Proof comment: the off-zero vanishing statement is invariant under the same localization
  -- comparison isomorphism on the source object.
  exact IsZero.of_iso hTensor eSource

-- Proof sketch: combine
-- `localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion` with
-- `localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero` to obtain the canonical
-- `t`-structure bounds and conclude by `singleFunctorIso_of_isGE_of_isLE`.
/-- Lemma 15.95.6 (2): if `I` is an ideal in a Noetherian ring `A`, `M` is a finite `A`-module,
and `f ∈ A`, then the derived `I`-adic completion of the localization `M_f`, viewed as a
degree-zero object of `D(A)`, is isomorphic to the degree-zero object on the ordinary `I`-adic
completion of `M_f`. -/
theorem localizationAway_finite_derivedCompletion_usual_adicCompletion
    (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (f : A) :
    IsIsomorphic
      (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])
      ((single₀).obj (ModuleCat.of A (AdicCompletion I (Away f M)))) := by
  classical
  let K :
      DMod :=
    (((single₀).obj (ModuleCat.of A (Away f M)))^∧[I, I.fg_of_isNoetherianRing])
  have hGE : K.IsGE 0 := by
    -- Proof comment: the localized off-zero vanishing companion kills every negative homology.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact
      localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero I M f i
        (by omega)
  have hLE : K.IsLE 0 := by
    -- Proof comment: it also kills every positive homology.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact
      localizationAway_finite_homology_derivedCompletion_isZero_of_ne_zero I M f i
        (by omega)
  let eSingle :
      K ≅ (single₀).obj ((H 0).obj K) := by
    -- Proof comment: concentration in degree `0` identifies `K` with the degree-zero single
    -- object on its zeroth homology.
    let _ : K.IsGE 0 := hGE
    let _ : K.IsLE 0 := hLE
    simpa [K] using
      (singleFunctorIso_of_isGE_of_isLE (A := ModuleCat A) K (0 : ℤ))
  let eZero :
      ((H 0).obj K) ≅ ModuleCat.of A (AdicCompletion I (Away f M)) :=
    Classical.choice
      (localizationAway_finite_homology_zero_derivedCompletion_isomorphic_adicCompletion
        I M f)
  exact ⟨eSingle ≪≫ (single₀).mapIso eZero⟩

end
