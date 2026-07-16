import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.QuotientKernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

lemma isZero_tor_one_module_of_linearEquiv_right
    {K L : Type u} [AddCommGroup K] [Module A K] [AddCommGroup L] [Module A L]
    (e : K ≃ₗ[A] L)
    (hK : IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A K)))) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A L))) := by
  -- Functoriality in the second Tor variable transports vanishing across the induced module
  -- isomorphism.
  exact IsZero.of_iso hK
    ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).mapIso e.toModuleIso).symm)

/-- Helper for Lemma 10.99.17: in `ModuleCat`, an exact row with both adjacent morphisms zero has
zero middle object. This isolates the categorical exactness-to-vanishing step used in the degree-1
Tor bootstrap. -/
lemma isZero_of_exact_zero_zero
    {X₁ X₂ X₃ : ModuleCat A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    (hExact : Function.Exact f.hom g.hom) (hf : f = 0) (hg : g = 0) :
    IsZero X₂ := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk f.hom g.hom (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.Exact := by
    -- Repackage the function-level exactness as exactness of the associated short complex.
    simpa [S] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).2 hExact
  -- Exactness with zero outer maps forces the middle object to vanish.
  simpa [S] using hS.isZero_X₂ hf hg

/-- Helper for Lemma 10.99.17: for a short exact row, the public module-first owner
`Tor₁^A(M, -)` is exact on the first two arrows. This is the degree-`1` public exactness window
read off from `ModuleCat.torTensorSixTermSequence_exact`. -/
lemma tor_one_module_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    Function.Exact ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f).hom)
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g).hom) := by
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of A M) hS
  -- Read the first short-complex window off the public six-term exact row.
  simpa [T, ModuleCat.torTensorSixTermSequence, ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (T.sc hT.toIsComplex 0))).1
      (hT.exact 0)

/-- Helper for Lemma 10.99.17: the degree-`1` module-first six-term row is also exact at the
middle `Tor₁^A(M, K₃)` term. This packages the source proof's first tail window
`Tor₁(M, K₂) → Tor₁(M, K₃) → M ⊗ K₁`. -/
lemma tor_one_module_middle_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    Function.Exact ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g).hom)
      (((ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS).map' 2 3).hom) := by
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of A M) hS
  -- Proof comment: exactness at index `1` is the window
  -- `Tor₁(M, K₂) → Tor₁(M, K₃) → M ⊗ K₁`.
  simpa [T, ModuleCat.torTensorSixTermSequence, ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (T.sc hT.toIsComplex 1))).1
      (hT.exact 1)

/-- Helper for Lemma 10.99.17: the degree-`1` module-first six-term row is exact at the tensor
tail `M ⊗ K₁`. This isolates the source-proof window `Tor₁(M, K₃) → M ⊗ K₁ → M ⊗ K₂`. -/
lemma tor_one_tensor_tail_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    Function.Exact (((ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS).map' 2 3).hom)
      (((tensorLeft (ModuleCat.of A M)).map S.f).hom) := by
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of A M) hS
  -- Proof comment: exactness at index `2` is the tail window
  -- `Tor₁(M, K₃) → M ⊗ K₁ → M ⊗ K₂`.
  simpa [T, ModuleCat.torTensorSixTermSequence, ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (T.sc hT.toIsComplex 2))).1
      (hT.exact 2)

/-- Helper for Lemma 10.99.17: for a short exact sequence `0 → K₁ → K₂ → K₃ → 0`, vanishing of
the outer degree-`1` module-first Tor terms forces vanishing of the middle term. This is the
degree-`1` exact-sequence step reused in the source proof before the higher-degree bootstrap is
added. -/
lemma isZero_tor_one_module_of_shortExact_of_outer_vanishing
    {K₁ K₂ K₃ : Type u} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₂] [Module A K₂]
    [AddCommGroup K₃] [Module A K₃]
    (u : K₁ →ₗ[A] K₂) (v : K₂ →ₗ[A] K₃)
    (hu_injective : Function.Injective u) (hv_surjective : Function.Surjective v)
    (huv_exact : Function.Exact u v)
    (h₁ : IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A K₁))))
    (h₃ : IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A K₃)))) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A K₂))) := by
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk u v (Function.Exact.linearMap_comp_eq_zero huv_exact)
  have hS : S.ShortExact := by
    -- Package the function-level short exact sequence as a `ModuleCat` short exact row.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using huv_exact
    · simpa [S] using (ModuleCat.mono_iff_injective (ModuleCat.ofHom u)).2 hu_injective
    · simpa [S] using (ModuleCat.epi_iff_surjective (ModuleCat.ofHom v)).2 hv_surjective
  have hExact :
      Function.Exact ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f).hom)
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g).hom) := by
    -- Use the public six-term exact row directly, avoiding the stale owner-swap route.
    simpa [S] using tor_one_module_exact_of_shortExact (A := A) (M := M) hS
  have hLeft : (((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f) = 0 :=
    h₁.eq_of_src _ _
  have hRight : (((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) = 0 :=
    h₃.eq_of_tgt _ _
  -- Exactness with zero outer terms kills the middle public-owner object.
  simpa [S] using isZero_of_exact_zero_zero hExact hLeft hRight

end
