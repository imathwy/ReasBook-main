import Mathlib
import Mathlib.CategoryTheory.Limits.MonoCoprod
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap19.Lemma_19_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory
namespace CochainComplex

section

variable (C : Type u) [Category.{v} C] [Abelian C]

local notation "Cpx" => CochainComplex C ℤ

/- Domain-style sampling for Lemma 19.12.2:
- primary domain: acyclic cochain complexes in a Grothendieck abelian category, together with the
  canonical bounded-above predicate and termwise subobject-cardinality bounds;
- sampled owner declarations:
  `CochainComplex.Acyclic`,
  `CochainComplex.minus`,
  `CochainComplex.minus_iff`,
  `Cardinal.mk (Subobject (K.X n))`,
  `exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size`;
- best owner abstraction: the recurring Chapter 19 owner is the single-complex predicate
  `MinusAcyclicSubobjectCardinalLE C κ K`, combining bounded-above support, acyclicity, and the
  canonical termwise size bound `∀ n, Cardinal.mk (Subobject (K.X n)) ≤ κ`;
- primitive data: a cardinal `κ` and a cochain complex `K`;
- derived API: the source-facing predicates `SmallAcyclicSubcomplexBound C κ` and
  `AcyclicCoproductPresentationBound C κ`, together with the combined existence theorem and its
  two projections; the coproduct-presentation predicate additionally uses the canonical coproduct
  owner `HasCoproducts C`.

Source/core/bridge triage:
- `source-facing`: the `κ`-small bounded-above acyclic cochain complexes of the source lemma,
  recorded by `MinusAcyclicSubobjectCardinalLE C κ`, together with the existence of one cardinal
  `κ` controlling both the small nonzero acyclic subcomplexes and the coproduct presentations;
- `core/canonical`: `CochainComplex.minus C K`, `K.Acyclic`, and
  `Cardinal.mk (Subobject (K.X n))`;
- `bridge/view`: the two cardinal-indexed predicates below, which express the two source
  conclusions in terms of the single-complex owner. -/

/-- A `κ`-small bounded-above acyclic cochain complex, measured by termwise subobject
cardinality. -/
def MinusAcyclicSubobjectCardinalLE (κ : Cardinal.{max u v + 1}) (K : Cpx) : Prop :=
  CochainComplex.minus C K ∧
    K.Acyclic ∧
    ∀ n : ℤ, Cardinal.lift.{max u v + 1, max u v} (Cardinal.mk (Subobject (K.X n))) ≤ κ

namespace MinusAcyclicSubobjectCardinalLE

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Cardinal.{max u v + 1}}
variable {K : CochainComplex C ℤ}

theorem minus (hK : MinusAcyclicSubobjectCardinalLE C κ K) :
    CochainComplex.minus C K :=
  hK.1

theorem acyclic (hK : MinusAcyclicSubobjectCardinalLE C κ K) :
    K.Acyclic :=
  hK.2.1

theorem subobjectCardinalLE (hK : MinusAcyclicSubobjectCardinalLE C κ K) (n : ℤ) :
    Cardinal.lift.{max u v + 1, max u v} (Cardinal.mk (Subobject (K.X n))) ≤ κ :=
  hK.2.2 n

end MinusAcyclicSubobjectCardinalLE

/-- A cardinal bound for nonzero acyclic cochain complexes: every such complex admits a nonzero
bounded-above acyclic subcomplex whose terms all have at most `κ` subobjects. -/
def SmallAcyclicSubcomplexBound (κ : Cardinal.{max u v + 1}) : Prop :=
  ∀ (M : Cpx) (_ : M.Acyclic) (_ : ¬ IsZero M),
    ∃ N : Subobject M,
      ¬ IsZero (N : Cpx) ∧
        MinusAcyclicSubobjectCardinalLE C κ (N : Cpx)

/-- A cardinal bound for acyclic cochain complexes: every acyclic complex is a quotient of a
coproduct of bounded-above acyclic complexes whose terms all have at most `κ` subobjects. -/
def AcyclicCoproductPresentationBound [HasCoproducts C] (κ : Cardinal.{max u v + 1}) : Prop :=
  ∀ (M : Cpx) (_ : M.Acyclic),
    ∃ (ι : Type w) (Mi : ι → Cpx) (f : (∐ fun i : ι ↦ Mi i) ⟶ M),
      Epi f ∧
        ∀ i : ι, MinusAcyclicSubobjectCardinalLE C κ (Mi i)

noncomputable section Grothendieck

variable [IsGrothendieckAbelian.{w} C]

omit [IsGrothendieckAbelian.{w} C] in
/-- Helper for Lemma 19.12.2: the image of a morphism has no more subobjects than its source. -/
lemma subobject_cardinal_image_le_source {A B : C} (f : A ⟶ B) :
    Cardinal.mk (Subobject (imageSubobject f : C)) ≤ Cardinal.mk (Subobject A) := by
  let e : A ⟶ (imageSubobject f : C) := factorThruImageSubobject f
  let S : ShortComplex C := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact := by
    -- The factorization through the image is an epimorphic quotient of the source.
    refine ShortComplex.ShortExact.mk ?_
    simpa [S, e] using ShortComplex.exact_kernel e
  -- Compare subobject cardinals across the resulting short exact sequence.
  simpa [S, e] using subobject_cardinal_quotient_le_of_shortExact hS

/-- Helper for Lemma 19.12.2: Lemma 19.12.1 specialized to the canonical separator produces a
subobject still surjecting onto the target and bounded by the separator-indexed coproduct over the
target subobject lattice. -/
lemma exists_separator_coproduct_bound_subobject_surjecting_onto_of_epi
    {M N : C} (π : M ⟶ N) [Epi π] :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
        Cardinal.mk (Subobject (M' : C)) ≤
          Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ separator C)) := by
  -- This is exactly Lemma 19.12.1 with `U := separator C`.
  simpa using
    (exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size
      (C := C) (U := separator C) (M := M) (N := N) (isSeparator_separator C) π)

/-- Helper for Lemma 19.12.2: if every morphism from the canonical separator into each term of a
cochain complex vanishes, then the whole complex is zero. -/
lemma isZero_of_separator_vanish {M : Cpx}
    (hvanish : ∀ n : ℤ, ∀ ψ : separator C ⟶ M.X n, ψ = 0) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  have hterm : IsZero (M.X n) := by
    by_contra hterm
    have hbot : (⊥ : Subobject (M.X n)) ≠ ⊤ := by
      intro htop
      have hIso : IsIso ((⊥ : Subobject (M.X n)).arrow) :=
        (Subobject.isIso_arrow_iff_eq_top _).2 htop
      have hbotZero : IsZero (((⊥ : Subobject (M.X n)) : C)) :=
        (isZero_zero C).of_iso Subobject.botCoeIsoZero
      exact hterm (hbotZero.of_iso (asIso ((⊥ : Subobject (M.X n)).arrow)).symm)
    obtain ⟨ψ, hψ⟩ :=
      (isSeparator_iff_exists_not_factors_subobject C (separator C)).mp
        (isSeparator_separator C) (⊥ : Subobject (M.X n)) hbot
    exact hψ ((Subobject.bot_factors_iff_zero ψ).2 (hvanish n ψ))
  -- Evaluate the identity of the complex at degree `n` and use the zero-object criterion there.
  simpa using hterm.eq_of_src (𝟙 (M.X n)) 0

/-- Helper for Lemma 19.12.2: a nonzero acyclic complex has a nonzero separator-valued seed in
some degree. -/
lemma exists_nonzero_separator_map {M : Cpx} (hM : ¬ IsZero M) :
    ∃ n : ℤ, ∃ ψ : separator C ⟶ M.X n, ψ ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact hM (isZero_of_separator_vanish (C := C) (M := M) h)

/-- Helper for Lemma 19.12.2: if every map from the canonical separator to the codomain factors
through `f`, then `f` is an epimorphism. -/
lemma epi_of_separator_factorization {X Y : C} (f : X ⟶ Y)
    (hfactor : ∀ ψ : separator C ⟶ Y, ∃ φ : separator C ⟶ X, φ ≫ f = ψ) :
    Epi f := by
  have htop : imageSubobject f = (⊤ : Subobject Y) := by
    by_contra himage
    obtain ⟨ψ, hψ⟩ :=
      (isSeparator_iff_exists_not_factors_subobject C (separator C)).mp
        (isSeparator_separator C) (imageSubobject f) himage
    rcases hfactor ψ with ⟨φ, rfl⟩
    exact hψ (imageSubobject_factors_comp_self f φ)
  -- Once the image fills the codomain, the standard image criterion gives epimorphy.
  exact epi_of_imageSubobject_eq_top f htop

/-- Helper for Lemma 19.12.2: any subobject already contained in `Im(d^{k-1})` is covered by a
pullback object in the previous term, and that pullback projection is epimorphic. -/
lemma exists_previous_term_cover_of_subobject_image
    {M : Cpx} (k : ℤ) (P : Subobject (M.X k))
    (hP : P ≤ imageSubobject (M.d (k - 1) k)) :
    ∃ (A : C) (ι : A ⟶ M.X (k - 1)) (_ : Mono ι) (σ : A ⟶ (P : C)) (_ : Epi σ),
      ι ≫ M.d (k - 1) k = σ ≫ P.arrow := by
  let e : M.X (k - 1) ⟶ (imageSubobject (M.d (k - 1) k) : C) :=
    factorThruImageSubobject (M.d (k - 1) k)
  let t : (P : C) ⟶ (imageSubobject (M.d (k - 1) k) : C) :=
    Subobject.ofLE P _ hP
  refine ⟨pullback e t, pullback.fst e t, inferInstance, pullback.snd e t, ?_, ?_⟩
  · -- The pullback of the epimorphic image quotient still surjects onto `P`.
    simpa [e, t] using Abelian.epi_snd_of_isLimit e t (IsPullback.of_hasPullback e t).isLimit
  · -- Postcomposing with the image arrow reduces the pullback square to the original differential.
    calc
      pullback.fst e t ≫ M.d (k - 1) k
          = pullback.fst e t ≫ e ≫ (imageSubobject (M.d (k - 1) k)).arrow := by
              simp [e, Category.assoc, imageSubobject_arrow_comp]
      _ = pullback.snd e t ≫ t ≫ (imageSubobject (M.d (k - 1) k)).arrow := by
            simpa [Category.assoc] using
              congrArg
                (fun m : pullback e t ⟶ (imageSubobject (M.d (k - 1) k) : C) ↦
                  m ≫ (imageSubobject (M.d (k - 1) k)).arrow)
                (pullback.condition (f := e) (g := t))
      _ = pullback.snd e t ≫ P.arrow := by
            simp [t, Category.assoc, Subobject.ofLE_arrow]

/-- Helper for Lemma 19.12.2: the cycles of a restricted differential land in the ambient image
from the previous degree once the ambient complex is acyclic. -/
lemma restricted_cycle_subobject_le_image_of_acyclic
    {M : Cpx} (hM : M.Acyclic) (k : ℤ)
    (Nk : Subobject (M.X k)) (Nk1 : Subobject (M.X (k + 1)))
    (δk : (Nk : C) ⟶ (Nk1 : C))
    (hδ : Nk.arrow ≫ M.d k (k + 1) = δk ≫ Nk1.arrow) :
    Subobject.mk ((kernelSubobject δk).arrow ≫ Nk.arrow) ≤ imageSubobject (M.d (k - 1) k) := by
  -- Rewrite acyclicity as exactness at degree `k`, matching the source proof's cycle/image step.
  rw [HomologicalComplex.acyclic_iff] at hM
  have hExact : (M.sc k).Exact := by
    simpa [HomologicalComplex.exactAt_iff] using hM k
  have hprev : (ComplexShape.up ℤ).prev k = k - 1 := by
    simpa [ComplexShape.up, ComplexShape.up'] using
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up']))
  have hnext : (ComplexShape.up ℤ).next k = k + 1 := by
    simpa [ComplexShape.up, ComplexShape.up'] using
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up']))
  have hImageEqKernel :
      imageSubobject (M.d (k - 1) k) = kernelSubobject (M.d k (k + 1)) := by
    -- `HomologicalComplex.sc` packages the two differentials around degree `k`.
    have hImageEqKernel' :
        imageSubobject (M.d ((ComplexShape.up ℤ).prev k) k) =
          kernelSubobject (M.d k ((ComplexShape.up ℤ).next k)) :=
      (ShortComplex.exact_iff_image_eq_kernel (M.sc k)).mp hExact
    rw [hprev, hnext] at hImageEqKernel'
    exact hImageEqKernel'
  -- The restricted cycles are ambient cycles because the square with `Nk.arrow` commutes.
  rw [hImageEqKernel]
  have hCycle :
      ((kernelSubobject δk).arrow ≫ Nk.arrow) ≫ M.d k (k + 1) = 0 := by
    calc
      ((kernelSubobject δk).arrow ≫ Nk.arrow) ≫ M.d k (k + 1)
          = (kernelSubobject δk).arrow ≫ (Nk.arrow ≫ M.d k (k + 1)) := by
              simp [Category.assoc]
      _ = (kernelSubobject δk).arrow ≫ (δk ≫ Nk1.arrow) := by rw [hδ]
      _ = ((kernelSubobject δk).arrow ≫ δk) ≫ Nk1.arrow := by
            simp [Category.assoc]
      _ = 0 := by
            simp [kernelSubobject_arrow_comp]
  refine le_kernelSubobject _ _ ?_
  -- Rewrite the `Subobject.mk` arrow through its canonical underlying isomorphism once.
  rw [← Subobject.underlyingIso_hom_comp_eq_mk ((kernelSubobject δk).arrow ≫ Nk.arrow),
    Category.assoc]
  simp [Category.assoc, hCycle]

/-- Helper for Lemma 19.12.2: the source-proof object `d^{-1}(\ker δ_k)` is obtained by pulling
back the restricted cycle subobject along the previous differential. -/
lemma exists_previous_term_cover_of_restricted_cycles
    {M : Cpx} (hM : M.Acyclic) (k : ℤ)
    (Nk : Subobject (M.X k)) (Nk1 : Subobject (M.X (k + 1)))
    (δk : (Nk : C) ⟶ (Nk1 : C))
    (hδ : Nk.arrow ≫ M.d k (k + 1) = δk ≫ Nk1.arrow) :
    ∃ (A : C) (ι : A ⟶ M.X (k - 1)) (_ : Mono ι)
      (σ : A ⟶ (Subobject.mk ((kernelSubobject δk).arrow ≫ Nk.arrow) : C)) (_ : Epi σ),
      ι ≫ M.d (k - 1) k =
        σ ≫ (Subobject.mk ((kernelSubobject δk).arrow ≫ Nk.arrow)).arrow := by
  -- Route correction: separate the ambient exactness step from the pullback-epi construction.
  exact
    exists_previous_term_cover_of_subobject_image (C := C) (M := M) (k := k)
      (P := Subobject.mk ((kernelSubobject δk).arrow ≫ Nk.arrow))
      (restricted_cycle_subobject_le_image_of_acyclic
        (C := C) (M := M) hM k Nk Nk1 δk hδ)

/-- Helper for Lemma 19.12.2: kernels contribute no more subobjects than their source term. -/
lemma subobject_cardinal_kernel_le_source {A B : C} (f : A ⟶ B) :
    Cardinal.mk (Subobject (kernelSubobject f : C)) ≤ Cardinal.mk (Subobject A) := by
  -- The kernel subobject injects into the source term through its defining monomorphism.
  exact Cardinal.mk_le_of_injective (Subobject.map_obj_injective (kernelSubobject f).arrow)

/-- Helper for Lemma 19.12.2: a `w`-small model of `Subobject N` embeds into `λ.out` once
`#(Subobject N) ≤ λ`. This is the theorem-local cardinal transport used in the source proof. -/
lemma subobject_shrink_embeds_into_cardinal_out
    {N : C} {κ : Cardinal.{max u v}}
    (hN : Cardinal.mk (Subobject N) ≤ κ) :
    Nonempty (Shrink.{w} (Subobject N) ↪ κ.out) := by
  let ι := Shrink.{w} (Subobject N)
  have hι :
      Cardinal.lift.{max u v} (Cardinal.mk ι) =
        Cardinal.lift.{w} (Cardinal.mk (Subobject N)) :=
    Cardinal.lift_mk_eq'.2 ⟨(equivShrink (Subobject N)).symm⟩
  have hι_le :
      Cardinal.lift.{max u v} (Cardinal.mk ι) ≤
        Cardinal.lift.{w} (Cardinal.mk κ.out) := by
    -- Rewrite the shrink back to the original subobject lattice before comparing to `κ.out`.
    rw [hι, Cardinal.mk_out]
    exact Cardinal.lift_le.2 hN
  exact (Cardinal.lift_mk_le').1 hι_le

/-- Helper for Lemma 19.12.2: if the lifted subobject-cardinality of `N` is bounded by a
lower-universe cardinal `λ`, then the shrunken subobject lattice embeds into the canonical owner
`λ.out`. -/
lemma subobject_shrink_embeds_into_lower_out_of_lift_le
    {N : C} {kappa : Cardinal.{w}}
    (hN : Cardinal.lift.{w} (Cardinal.mk (Subobject N)) ≤ Cardinal.lift.{max u v} kappa) :
    Nonempty (Shrink.{w} (Subobject N) ↪ kappa.out) := by
  let ι := Shrink.{w} (Subobject N)
  have hι :
      Cardinal.lift.{max u v} (Cardinal.mk ι) =
        Cardinal.lift.{w} (Cardinal.mk (Subobject N)) :=
    Cardinal.lift_mk_eq'.2 ⟨(equivShrink (Subobject N)).symm⟩
  have hι_le_lift :
      Cardinal.lift.{max u v} (Cardinal.mk ι) ≤ Cardinal.lift.{max u v} kappa := by
    -- Route correction: compare directly with the lower-universe owner `kappa.out`,
    -- instead of introducing a second shrink of an ambient cardinal representative.
    rw [hι]
    exact hN
  have hι_le :
      Cardinal.mk ι ≤ Cardinal.mk kappa.out := by
    rw [Cardinal.mk_out]
    exact Cardinal.lift_le.1 hι_le_lift
  exact (Cardinal.lift_mk_le').1 (by simpa using hι_le)

/-- Helper for Lemma 19.12.2: once the ambient representative `κ.out` is itself `w`-small, the
shrunken subobject lattice embeds into the canonical index `Shrink.{w} κ.out`. -/
lemma subobject_shrink_embeds_into_shrink_out
    {N : C} {κ : Cardinal.{max u v}} [Small.{w} κ.out]
    (hN : Cardinal.mk (Subobject N) ≤ κ) :
    Nonempty (Shrink.{w} (Subobject N) ↪ Shrink.{w} κ.out) := by
  rcases subobject_shrink_embeds_into_cardinal_out (C := C) (N := N) (κ := κ) hN with ⟨σ⟩
  -- Compose the ambient embedding with the canonical equivalence to the shrunken owner.
  exact ⟨σ.trans (equivShrink κ.out).toEmbedding⟩

/-- Helper for Lemma 19.12.2: an embedding of the shrunken subobject lattice into a `w`-small
ambient index induces the corresponding separator-coproduct cardinal bound. -/
lemma separator_coproduct_subobject_cardinal_le_of_embedding
    {N : C} {ι : Type w}
    (σ : Shrink.{w} (Subobject N) ↪ ι) :
    Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ separator C)) ≤
      Cardinal.mk (Subobject (∐ fun _ : ι ↦ separator C)) := by
  classical
  let F : ι → C := fun _ ↦ separator C
  let g :
      (∐ fun _ : Shrink.{w} (Subobject N) ↦ separator C) ⟶
        (∐ fun _ : ι ↦ separator C) :=
    Limits.Sigma.map' σ (fun _ ↦ 𝟙 (separator C))
  have hg : Mono g := by
    -- The index embedding gives a mono between the two constant separator coproducts.
    simpa [g, F] using
      (Limits.MonoCoprod.mono_map'_of_injective (C := C) (X := F) (ι := σ) σ.injective :
        Mono (Limits.Sigma.map' σ (fun j ↦ 𝟙 ((F ∘ σ) j))))
  letI : Mono g := hg
  -- Subobjects of the smaller coproduct inject into subobjects of the ambient coproduct.
  exact Cardinal.mk_le_of_injective (Subobject.map_obj_injective g)

/-- Helper for Lemma 19.12.2: the source proof's one-step separator coproduct bound can be
measured against the fixed ambient index `Shrink.{w} κ.out` once that owner exists. -/
lemma separator_coproduct_subobject_cardinal_le_stepBound
    {N : C} {κ : Cardinal.{max u v}} [Small.{w} κ.out]
    (hN : Cardinal.mk (Subobject N) ≤ κ) :
    Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ separator C)) ≤
      Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} κ.out ↦ separator C)) := by
  rcases subobject_shrink_embeds_into_shrink_out (C := C) (N := N) (κ := κ) hN with ⟨σ⟩
  -- This specializes the generic embedding comparison to the canonical fixed-cardinal owner.
  exact
    separator_coproduct_subobject_cardinal_le_of_embedding
      (C := C) (N := N) (ι := Shrink.{w} κ.out) σ

/-- Helper for Lemma 19.12.2: the source proof's one-step separator-coproduct bound can be
measured directly against the lower-universe owner `λ.out` once the subobject lattice of `N` is
bounded by `λ` after lifting. -/
lemma separator_coproduct_subobject_cardinal_le_lift_stepBound
    {N : C} {kappa : Cardinal.{w}}
    (hN : Cardinal.lift.{w} (Cardinal.mk (Subobject N)) ≤ Cardinal.lift.{max u v} kappa) :
    Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ separator C)) ≤
      Cardinal.mk (Subobject (∐ fun _ : kappa.out ↦ separator C)) := by
  rcases
      subobject_shrink_embeds_into_lower_out_of_lift_le
        (C := C) (N := N) (kappa := kappa) hN with
    ⟨σ⟩
  -- Compare the two separator coproducts along the induced embedding of their index types.
  exact
    separator_coproduct_subobject_cardinal_le_of_embedding
      (C := C) (N := N) (ι := kappa.out) σ

/-- Helper for Lemma 19.12.2: a fixed ambient universe cardinal bounds every subobject lattice
appearing in this file. -/
abbrev univCardinal : Cardinal.{max u v + 1} :=
  Cardinal.univ.{max u v, max u v + 1}

/-- Helper for Lemma 19.12.2: an epimorphism into a subobject has that subobject as its image. -/
lemma imageSubobject_comp_arrow_eq_of_epi
    {A B : C} (P : Subobject B) (σ : A ⟶ (P : C)) [Epi σ] :
    imageSubobject (σ ≫ P.arrow) = P := by
  -- Compare the image of the composite with the image of the mono `P.arrow`.
  have hle :
      imageSubobject (σ ≫ P.arrow) ≤ imageSubobject P.arrow :=
    imageSubobject_comp_le σ P.arrow
  haveI : Epi (Subobject.ofLE _ _ hle) :=
    imageSubobject_comp_le_epi_of_epi σ P.arrow
  haveI : IsIso (Subobject.ofLE _ _ hle) :=
    isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
  have hEq :
      imageSubobject (σ ≫ P.arrow) = imageSubobject P.arrow := by
    exact Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by
      simp [Subobject.ofLE_arrow])
  simpa [imageSubobject_mono] using hEq

/-- Helper for Lemma 19.12.2: the seeded source map determines the top two degrees of the
descending acyclic subcomplex. -/
lemma existsSeededTopPair
    {M : Cpx} {n : ℤ} (ψ : separator C ⟶ M.X n) :
    ∃ Nk : Subobject (M.X n), ∃ Nk1 : Subobject (M.X (n + 1)),
      ∃ φ : separator C ⟶ (Nk : C), ∃ δn : (Nk : C) ⟶ (Nk1 : C),
        φ ≫ Nk.arrow = ψ ∧
          Nk.arrow ≫ M.d n (n + 1) = δn ≫ Nk1.arrow ∧
          imageSubobject δn = ⊤ := by
  let Nk : Subobject (M.X n) := imageSubobject ψ
  let φ : separator C ⟶ (Nk : C) := factorThruImageSubobject ψ
  let δraw : (Nk : C) ⟶ M.X (n + 1) := Nk.arrow ≫ M.d n (n + 1)
  let Nk1 : Subobject (M.X (n + 1)) := imageSubobject δraw
  let δn : (Nk : C) ⟶ (Nk1 : C) := factorThruImageSubobject δraw
  refine ⟨Nk, Nk1, φ, δn, ?_, ?_, ?_⟩
  · -- The seed factors through its image by the canonical image map.
    simpa [Nk, φ] using imageSubobject_arrow_comp ψ
  · -- The differential out of the seeded degree factors through its image in degree `n + 1`.
    simpa [δraw, Nk1, δn, Category.assoc] using imageSubobject_arrow_comp δraw
  · -- The factor through an image object is always epimorphic onto that image.
    letI : Epi δn := inferInstance
    have hArrowEpi : Epi (imageSubobject δn).arrow := by
      have : Epi (factorThruImageSubobject δn ≫ (imageSubobject δn).arrow) := by
        simpa [imageSubobject_arrow_comp] using (inferInstance : Epi δn)
      exact epi_of_epi (factorThruImageSubobject δn) (imageSubobject δn).arrow
    have hArrowIso : IsIso (imageSubobject δn).arrow :=
      isIso_of_mono_of_epi (imageSubobject δn).arrow
    exact (Subobject.isIso_arrow_iff_eq_top (imageSubobject δn)).mp hArrowIso

/-- Helper for Lemma 19.12.2: one descending step replaces the restricted cycles at degree `k`
by a predecessor term whose image is exactly those cycles. -/
lemma existsSeededPredecessor
    {M : Cpx} (hM : M.Acyclic) {k : ℤ}
    (Nk : Subobject (M.X k)) (Nk1 : Subobject (M.X (k + 1)))
    (δk : (Nk : C) ⟶ (Nk1 : C))
    (hδ : Nk.arrow ≫ M.d k (k + 1) = δk ≫ Nk1.arrow) :
    ∃ NkPrev : Subobject (M.X (k - 1)), ∃ δPrev : (NkPrev : C) ⟶ (Nk : C),
      NkPrev.arrow ≫ M.d (k - 1) k = δPrev ≫ Nk.arrow ∧
        imageSubobject δPrev = kernelSubobject δk := by
  let K : Subobject (M.X k) := Subobject.mk ((kernelSubobject δk).arrow ≫ Nk.arrow)
  rcases
      exists_previous_term_cover_of_restricted_cycles
        (C := C) (M := M) hM k Nk Nk1 δk hδ with
    ⟨A, ι, _, σ, _, hσ⟩
  let NkPrev : Subobject (M.X (k - 1)) := Subobject.mk ι
  let ePrev : (NkPrev : C) ⟶ A := (Subobject.underlyingIso ι).hom
  let eKer : (K : C) ⟶ (kernelSubobject δk : C) :=
    (Subobject.underlyingIso ((kernelSubobject δk).arrow ≫ Nk.arrow)).hom
  let δPrev : (NkPrev : C) ⟶ (Nk : C) :=
    ePrev ≫ σ ≫ eKer ≫ (kernelSubobject δk).arrow
  refine ⟨NkPrev, δPrev, ?_, ?_⟩
  · -- Rewrite the pullback cover identity through the canonical underlying isomorphisms.
    calc
      NkPrev.arrow ≫ M.d (k - 1) k
          = ePrev ≫ ι ≫ M.d (k - 1) k := by
              rw [← Subobject.underlyingIso_hom_comp_eq_mk ι, Category.assoc]
      _ = ePrev ≫ σ ≫ K.arrow := by
            simpa [K, Category.assoc] using congrArg (fun t ↦ ePrev ≫ t) hσ
      _ = ePrev ≫ σ ≫ eKer ≫ (kernelSubobject δk).arrow ≫ Nk.arrow := by
            rw [← Category.assoc, ← Category.assoc,
              Subobject.underlyingIso_hom_comp_eq_mk ((kernelSubobject δk).arrow ≫ Nk.arrow)]
      _ = δPrev ≫ Nk.arrow := by
            simp [δPrev, Category.assoc]
  · -- The cover is epi onto the restricted-cycle subobject, so its image is exactly that kernel.
    let σ' : (NkPrev : C) ⟶ (kernelSubobject δk : C) := ePrev ≫ σ ≫ eKer
    have hδPrev : δPrev = σ' ≫ (kernelSubobject δk).arrow := by
      simp [δPrev, σ', Category.assoc]
    letI : Epi σ' := inferInstance
    rw [hδPrev]
    exact imageSubobject_comp_arrow_eq_of_epi (C := C) (P := kernelSubobject δk) σ'

/-- Helper for Lemma 19.12.2: the canonical zero cochain complex. -/
private noncomputable abbrev zeroCpx : Cpx := HomologicalComplex.zero

/-- Helper for Lemma 19.12.2: the zero complex is automatically bounded above, acyclic, and
`Cardinal.univ`-small. -/
lemma minusAcyclicSubobjectCardinalLE_zero_univ :
    MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) (zeroCpx (C := C)) := by
  refine ⟨zero_mem_minus C, ?_, ?_⟩
  · -- The zero complex is acyclic because every homology object is zero.
    simpa [zeroCpx] using
      (HomologicalComplex.acyclic_of_isZero
        (zeroCpx (C := C))
        (HomologicalComplex.isZero_zero : IsZero (zeroCpx (C := C))))
  · -- Every term of the zero complex has subobject-cardinality below `Cardinal.univ`.
    intro n
    exact le_of_lt
      (Cardinal.lift_lt_univ' (Cardinal.mk (Subobject ((zeroCpx (C := C)).X n))))

/-- Helper for Lemma 19.12.2: a degreewise subobject family inherits `d² = 0` from the ambient
complex once its squares with the ambient differentials commute. -/
lemma subobjectFamily_dSquared_zero
    {M : Cpx}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow)
    (i : ℤ) :
    δ i ≫ δ (i + 1) = 0 := by
  -- Postcompose with the mono arrow into `M` and reduce to `M.d ≫ M.d = 0`.
  have hcomp : (δ i ≫ δ (i + 1)) ≫ (X (i + 1 + 1)).arrow = 0 := by
    calc
      (δ i ≫ δ (i + 1)) ≫ (X (i + 1 + 1)).arrow
        = δ i ≫ (δ (i + 1) ≫ (X (i + 1 + 1)).arrow) := by
            simp [Category.assoc]
      _ = δ i ≫ ((X (i + 1)).arrow ≫ M.d (i + 1) (i + 1 + 1)) := by
            rw [hcomm (i + 1)]
      _ = (δ i ≫ (X (i + 1)).arrow) ≫ M.d (i + 1) (i + 1 + 1) := by
            simp [Category.assoc]
      _ = ((X i).arrow ≫ M.d i (i + 1)) ≫ M.d (i + 1) (i + 1 + 1) := by
            rw [hcomm i]
      _ = (X i).arrow ≫ (M.d i (i + 1) ≫ M.d (i + 1) (i + 1 + 1)) := by
            simp [Category.assoc]
      _ = 0 := by
            simp [Category.assoc, M.d_comp_d]
  exact (cancel_mono (X (i + 1 + 1)).arrow).1 (by simpa [Category.assoc] using hcomp)

/-- Helper for Lemma 19.12.2: the degreewise seeded family packages into a cochain complex with
the chosen subobjects as its terms. -/
noncomputable def subobjectFamilyComplex
    {M : Cpx}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow) :
    Cpx :=
  CochainComplex.of
    (fun i ↦ (X i : C))
    δ
    (subobjectFamily_dSquared_zero (C := C) (M := M) X δ hcomm)

/-- Helper for Lemma 19.12.2: the packaged degreewise family maps into the ambient complex by the
given subobject arrows. -/
noncomputable def subobjectFamilyInclusion
    {M : Cpx}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow) :
    subobjectFamilyComplex (C := C) X δ hcomm ⟶ M :=
  HomologicalComplex.Hom.mk
    (fun i ↦ (X i).arrow)
    (fun i j hij ↦ by
      rcases hij with rfl
      simpa [subobjectFamilyComplex, CochainComplex.of_d] using hcomm i)

/-- Helper for Lemma 19.12.2: the packaged inclusion is mono because every component is a
subobject arrow. -/
lemma subobjectFamilyInclusion_mono
    {M : Cpx}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow) :
    Mono (subobjectFamilyInclusion (C := C) X δ hcomm) := by
  -- The chapter's inclusion of the packaged family is degreewise mono, hence mono globally.
  refine HomologicalComplex.mono_of_mono_f _ ?_
  intro i
  simpa [subobjectFamilyInclusion] using (show Mono ((X i).arrow) from inferInstance)

/-- Helper for Lemma 19.12.2: packaging a degreewise subobject family with commuting squares
produces a mono of cochain complexes. -/
lemma packageSubobjectFamilyAsMono
    {M : Cpx}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow) :
    ∃ N : Cpx, ∃ ι : N ⟶ M, Mono ι := by
  -- Route correction: keep the packaged complex and its inclusion as named constructions.
  refine ⟨subobjectFamilyComplex (C := C) X δ hcomm,
    subobjectFamilyInclusion (C := C) X δ hcomm,
    subobjectFamilyInclusion_mono (C := C) X δ hcomm⟩

/-- Helper for Lemma 19.12.2: the packaged seeded family is bounded above, acyclic, and
`Cardinal.univ`-small once its exactness and support data are recorded degreewise. -/
lemma minusAcyclicSubobjectCardinalLE_ofSubobjectFamily
    {M : Cpx} {n : ℤ}
    (X : ∀ i : ℤ, Subobject (M.X i))
    (δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C))
    (hcomm : ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow)
    (htop : imageSubobject (δ n) = ⊤)
    (hexact : ∀ i : ℤ, i < n → imageSubobject (δ i) = kernelSubobject (δ (i + 1)))
    (hzeroX : ∀ i : ℤ, n + 2 ≤ i → X i = ⊥)
    (hzeroδ : ∀ i : ℤ, n + 1 ≤ i → δ i = 0) :
    MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1})
      (subobjectFamilyComplex (C := C) X δ hcomm) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: support vanishes above `n + 1`, so the packaged complex is bounded above.
    refine (CochainComplex.minus_iff C _).2 ⟨n + 1, ?_⟩
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hXi : X i = ⊥ := hzeroX i (by omega)
    have hXi_zero : IsZero (((⊥ : Subobject (M.X i)) : C)) := by
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    simpa [subobjectFamilyComplex, CochainComplex.of_d, hXi] using
      hXi_zero
  · -- Proof comment: exactness below `n + 1` comes from the recursive identities, and above
    -- that bound the middle term is already zero.
    intro i
    have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by
      simpa [ComplexShape.up, ComplexShape.up'] using
        (ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up']))
    have hnext : (ComplexShape.up ℤ).next i = i + 1 := by
      simpa [ComplexShape.up, ComplexShape.up'] using
        (ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up']))
    by_cases hi_le : i ≤ n
    · have hiExact :
        ((subobjectFamilyComplex (C := C) X δ hcomm).sc i).Exact := by
          refine
            (ShortComplex.exact_iff_image_eq_kernel
              ((subobjectFamilyComplex (C := C) X δ hcomm).sc i)).2 ?_
          have hi_lt : i - 1 < n := by
            omega
          change
            imageSubobject
                ((subobjectFamilyComplex (C := C) X δ hcomm).d ((ComplexShape.up ℤ).prev i) i) =
              kernelSubobject
                ((subobjectFamilyComplex (C := C) X δ hcomm).d i ((ComplexShape.up ℤ).next i))
          rw [hprev, hnext]
          change imageSubobject (δ (i - 1)) = kernelSubobject (δ (i - 1 + 1))
          simpa using hexact (i - 1) hi_lt
      simpa [HomologicalComplex.exactAt_iff] using hiExact
    · by_cases hi_succ : i = n + 1
      · have hiExact :
        ((subobjectFamilyComplex (C := C) X δ hcomm).sc i).Exact := by
          refine
            (ShortComplex.exact_iff_image_eq_kernel
              ((subobjectFamilyComplex (C := C) X δ hcomm).sc i)).2 ?_
          change
            imageSubobject
                ((subobjectFamilyComplex (C := C) X δ hcomm).d ((ComplexShape.up ℤ).prev i) i) =
              kernelSubobject
                ((subobjectFamilyComplex (C := C) X δ hcomm).d i ((ComplexShape.up ℤ).next i))
          rw [hprev, hnext]
          subst hi_succ
          have hpred : n + 1 - 1 = n := by omega
          rw [hpred]
          simp [subobjectFamilyComplex, CochainComplex.of_d]
          rw [hzeroδ (n + 1) (le_rfl : n + 1 ≤ n + 1)]
          simpa using htop
        simpa [HomologicalComplex.exactAt_iff] using hiExact
      · rw [HomologicalComplex.exactAt_iff]
        have hi_ge : n + 2 ≤ i := by
          omega
        refine ShortComplex.exact_of_isZero_X₂ _ ?_
        have hXi : X i = ⊥ := hzeroX i hi_ge
        have hXi_zero : IsZero (((⊥ : Subobject (M.X i)) : C)) := by
          exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
        simpa [subobjectFamilyComplex, CochainComplex.of_d, hXi] using
          hXi_zero
  · -- Proof comment: every term automatically has subobject-cardinality below `Cardinal.univ`.
    intro i
    exact le_of_lt
      (Cardinal.lift_lt_univ'
        (Cardinal.mk
          (Subobject
            ((subobjectFamilyComplex (C := C) X δ hcomm).X i))))

/-- Helper for Lemma 19.12.2: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : Cpx} (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Read acyclicity degreewise and move each exactness witness across the isomorphism.
  intro i
  exact HomologicalComplex.ExactAt.of_iso (hK i) e

/-- Helper for Lemma 19.12.2: an isomorphism of cochain complexes induces an isomorphism on each
degree. -/
private lemma cochainComponentIso
    {K L : Cpx} (e : K ≅ L) (i : ℤ) :
    K.X i ≅ L.X i := by
  -- Proof comment: evaluate the inverse identities of `e` at degree `i`.
  refine
    { hom := e.hom.f i
      inv := e.inv.f i
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · simpa [HomologicalComplex.comp_f] using
      congrArg (fun g : K ⟶ K ↦ g.f i) e.hom_inv_id
  · simpa [HomologicalComplex.comp_f] using
      congrArg (fun g : L ⟶ L ↦ g.f i) e.inv_hom_id

/-- Helper for Lemma 19.12.2: isomorphic terms have equally large subobject lattices. -/
private theorem subobjectCardinal_eq_of_iso
    {A B : C} (e : A ≅ B) :
    Cardinal.mk (Subobject A) = Cardinal.mk (Subobject B) := by
  -- The canonical order isomorphism on subobjects gives the cardinal comparison.
  exact Cardinal.mk_congr (Subobject.mapIsoToOrderIso e).toEquiv

/-- Helper for Lemma 19.12.2: a descending stage records two adjacent degrees of the seeded
subcomplex together with their restricted differential inside the ambient complex. -/
private structure SeededAdjacentStage (M : Cpx) (k : ℤ) where
  left : Subobject (M.X k)
  right : Subobject (M.X (k + 1))
  differential : (left : C) ⟶ (right : C)
  comm : left.arrow ≫ M.d k (k + 1) = differential ≫ right.arrow

/-- Helper for Lemma 19.12.2: the recursive predecessor stage indexed by `((n - m) - 1)`
is exactly the next stage indexed by `n - (m + 1)`. -/
private def castSeededAdjacentStageSucc
    (M : Cpx) (n : ℤ) (m : ℕ)
    (S : SeededAdjacentStage (C := C) M ((n - (m : ℤ)) - 1)) :
    SeededAdjacentStage (C := C) M (n - ((m + 1 : ℕ) : ℤ)) := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using S

/-- Helper for Lemma 19.12.2: the recursive stage at degree `i ≤ n` is indexed by the natural
distance from `i` to `n`. -/
private lemma seededStageIndex_of_le (n i : ℤ) (hi : i ≤ n) :
    n - (Int.toNat (n - i) : ℤ) = i := by
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hi)]
  omega

/-- Helper for Lemma 19.12.2: consecutive degrees differ by one in the natural-distance indexing
used for the descending recursion. -/
private lemma seededStageDistance_succ (n i : ℤ) (hi : i < n) :
    Int.toNat (n - i) = Int.toNat (n - (i + 1)) + 1 := by
  have hcast :
      (Int.toNat (n - i) : ℤ) = Int.toNat (n - (i + 1)) + 1 := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hi.le),
      Int.toNat_of_nonneg (by omega)]
    omega
  exact_mod_cast hcast

/-- Helper for Lemma 19.12.2: once the top differential is epi onto its image, the next ambient
differential vanishes on the top image term. -/
private lemma topStage_arrow_comp_next_zero
    {M : Cpx} {n : ℤ}
    {N0 : Subobject (M.X n)} {N1 : Subobject (M.X (n + 1))}
    (δ0 : (N0 : C) ⟶ (N1 : C))
    (hcomm : N0.arrow ≫ M.d n (n + 1) = δ0 ≫ N1.arrow)
    (htop : imageSubobject δ0 = ⊤) :
    N1.arrow ≫ M.d (n + 1) (n + 2) = 0 := by
  letI : Epi δ0 := epi_of_imageSubobject_eq_top δ0 htop
  have hcomp : δ0 ≫ (N1.arrow ≫ M.d (n + 1) (n + 2)) = 0 := by
    calc
      δ0 ≫ (N1.arrow ≫ M.d (n + 1) (n + 2))
          = (δ0 ≫ N1.arrow) ≫ M.d (n + 1) (n + 2) := by simp [Category.assoc]
      _ = (N0.arrow ≫ M.d n (n + 1)) ≫ M.d (n + 1) (n + 2) := by rw [hcomm]
      _ = N0.arrow ≫ (M.d n (n + 1) ≫ M.d (n + 1) (n + 2)) := by simp [Category.assoc]
      _ = 0 := by simp [Category.assoc, M.d_comp_d]
  exact (cancel_epi δ0).1 (by simpa [Category.assoc] using hcomp)

/-- Helper for Lemma 19.12.2: a nonzero separator seed extends to a full descending family of
subobjects realizing the source proof's bounded-above exact construction. -/
lemma existsSeededDescendingFamily
    {M : Cpx} (hM : M.Acyclic) {n : ℤ}
    (ψ : separator C ⟶ M.X n) (hψ : ψ ≠ 0) :
    ∃ X : ∀ i : ℤ, Subobject (M.X i),
      ∃ δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C),
        ∃ φ : separator C ⟶ (X n : C),
          φ ≫ (X n).arrow = ψ ∧
            (∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow) ∧
            imageSubobject (δ n) = ⊤ ∧
            (∀ i : ℤ, i < n → imageSubobject (δ i) = kernelSubobject (δ (i + 1))) ∧
            (∀ i : ℤ, n + 2 ≤ i → X i = ⊥) ∧
            (∀ i : ℤ, n + 1 ≤ i → δ i = 0) := by
  classical
  rcases existsSeededTopPair (C := C) (M := M) ψ with
    ⟨Nn, Nn1, φ, δn, hφ, hδn, htop⟩
  let topStage : SeededAdjacentStage (C := C) M (n - (0 : ℤ)) := by
    simpa using
      ({ left := Nn
         right := Nn1
         differential := δn
         comm := hδn } : SeededAdjacentStage (C := C) M n)
  let rec stage : (m : ℕ) → SeededAdjacentStage (C := C) M (n - (m : ℤ))
    | 0 => topStage
    | m + 1 =>
        let current := stage m
        let hprev :=
          existsSeededPredecessor (C := C) (M := M) hM
            (k := n - (m : ℤ)) current.left current.right current.differential current.comm
        let NkPrev := Classical.choose hprev
        let hprevδ := Classical.choose_spec hprev
        let δPrev := Classical.choose hprevδ
        let hprevSpec := Classical.choose_spec hprevδ
        castSeededAdjacentStageSucc (C := C) M n m
          { left := NkPrev
            right := current.left
            differential := δPrev
            comm := hprevSpec.1 }
  have stageExact :
      ∀ m : ℕ, imageSubobject ((stage (m + 1)).differential) = kernelSubobject ((stage m).differential) := by
    intro m
    let current := stage m
    let hprev :=
      existsSeededPredecessor (C := C) (M := M) hM
        (k := n - (m : ℤ)) current.left current.right current.differential current.comm
    let hprevδ := Classical.choose_spec hprev
    let hprevSpec := Classical.choose_spec hprevδ
    simpa [stage, current, hprev, hprevδ, hprevSpec, castSeededAdjacentStageSucc] using hprevSpec.2
  let X : ∀ i : ℤ, Subobject (M.X i) := by
    intro i
    by_cases hi : i ≤ n
    · simpa [seededStageIndex_of_le n i hi] using (stage (Int.toNat (n - i))).left
    · by_cases hi_succ : i = n + 1
      · simpa [hi_succ] using topStage.right
      · exact ⊥
  let δ : ∀ i : ℤ, (X i : C) ⟶ (X (i + 1) : C) := by
    intro i
    by_cases hi : i < n
    · have hi_le : i ≤ n := hi.le
      have hi_succ_le : i + 1 ≤ n := by omega
      have hdist : Int.toNat (n - i) = Int.toNat (n - (i + 1)) + 1 :=
        seededStageDistance_succ n i hi
      simpa [X, hi_le, hi_succ_le, seededStageIndex_of_le n i hi_le,
        seededStageIndex_of_le n (i + 1) hi_succ_le, hdist, stage] using
        (stage (Int.toNat (n - i))).differential
    · by_cases hi_eq : i = n
      · subst hi_eq
        have hnot : ¬ n + 1 ≤ n := by omega
        simpa [X, seededStageIndex_of_le n n le_rfl, hnot] using topStage.differential
      · have hi_ge : n + 1 ≤ i := by omega
        exact 0
  let φX : separator C ⟶ (X n : C) := by
    simpa [X, seededStageIndex_of_le n n le_rfl] using φ
  have hφX : φX ≫ (X n).arrow = ψ := by
    simpa [φX, X, seededStageIndex_of_le n n le_rfl] using hφ
  have hcomm :
      ∀ i : ℤ, (X i).arrow ≫ M.d i (i + 1) = δ i ≫ (X (i + 1)).arrow := by
    intro i
    by_cases hi : i < n
    · have hi_le : i ≤ n := hi.le
      have hi_succ_le : i + 1 ≤ n := by omega
      have hdist : Int.toNat (n - i) = Int.toNat (n - (i + 1)) + 1 :=
        seededStageDistance_succ n i hi
      simpa [X, δ, hi, hi_le, hi_succ_le, seededStageIndex_of_le n i hi_le,
        seededStageIndex_of_le n (i + 1) hi_succ_le, hdist] using
        (stage (Int.toNat (n - i))).comm
    · by_cases hi_eq : i = n
      · subst i
        have hnot : ¬ n + 1 ≤ n := by omega
        simpa [X, δ, seededStageIndex_of_le n n le_rfl, hnot] using topStage.comm
      · by_cases hi_succ : i = n + 1
        · subst i
          have hnot₁ : ¬ n + 1 ≤ n := by omega
          have hnot₂ : ¬ n + 2 ≤ n + 1 := by omega
          simpa [X, δ, hnot₁, hnot₂] using
            topStage_arrow_comp_next_zero (C := C) (M := M) δn hδn htop
        · have hi_ge : n + 2 ≤ i := by omega
          have hi_not_le : ¬ i ≤ n := by omega
          have hi_succ_not_le : ¬ i + 1 ≤ n := by omega
          have hi_not_succ : i ≠ n + 1 := hi_succ
          have hi_next_not_succ : i + 1 ≠ n + 1 := by omega
          have hXi : X i = ⊥ := by
            simp [X, hi_not_le, hi_not_succ]
          have hXi_succ : X (i + 1) = ⊥ := by
            simp [X, hi_succ_not_le, hi_next_not_succ]
          simp [hXi, hXi_succ, δ, hi, hi_eq]
  have htopδ : imageSubobject (δ n) = ⊤ := by
    have hnot : ¬ n + 1 ≤ n := by omega
    simpa [δ, X, seededStageIndex_of_le n n le_rfl, hnot] using htop
  have hexact :
      ∀ i : ℤ, i < n → imageSubobject (δ i) = kernelSubobject (δ (i + 1)) := by
    intro i hi
    by_cases hi_succ : i + 1 < n
    · have hi_le : i ≤ n := hi.le
      have hi_succ_le : i + 1 ≤ n := by omega
      have hdist : Int.toNat (n - i) = Int.toNat (n - (i + 1)) + 1 :=
        seededStageDistance_succ n i hi
      simpa [δ, X, hi, hi_succ, hi_le, hi_succ_le, seededStageIndex_of_le n i hi_le,
        seededStageIndex_of_le n (i + 1) hi_succ_le, hdist] using
        stageExact (Int.toNat (n - (i + 1)))
    · have hi_eq : i + 1 = n := by omega
      have hi_pred : i = n - 1 := by omega
      subst i
      have hnot : ¬ n + 1 ≤ n := by omega
      simpa [δ, X, seededStageIndex_of_le n (n - 1) (by omega),
        seededStageIndex_of_le n n le_rfl, seededStageDistance_succ n (n - 1) (by omega),
        hnot] using stageExact 0
  have hzeroX : ∀ i : ℤ, n + 2 ≤ i → X i = ⊥ := by
    intro i hi
    have hi_not_le : ¬ i ≤ n := by omega
    have hi_not_succ : i ≠ n + 1 := by omega
    simp [X, hi_not_le, hi_not_succ]
  have hzeroδ : ∀ i : ℤ, n + 1 ≤ i → δ i = 0 := by
    intro i hi
    by_cases hi_lt : i < n
    · omega
    · by_cases hi_eq : i = n
      · omega
      · simp [δ, hi_lt, hi_eq]
  exact ⟨X, δ, φX, hφX, hcomm, htopδ, hexact, hzeroX, hzeroδ⟩

/-- Helper for Lemma 19.12.2: once a nonzero separator-valued seed factors through a nonzero
bounded-above acyclic subcomplex, the `Cardinal.univ` size bound is automatic. -/
lemma existsSeededUnivSmallAcyclicSubcomplex
    {M : Cpx} (hM : M.Acyclic) {n : ℤ}
    (ψ : separator C ⟶ M.X n) (hψ : ψ ≠ 0) :
    ∃ N : Subobject M,
      (∃ φ : separator C ⟶ (N : Cpx).X n, φ ≫ N.arrow.f n = ψ) ∧
        ¬ IsZero (N : Cpx) ∧
          MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) (N : Cpx) := by
  classical
  rcases existsSeededDescendingFamily (C := C) (M := M) hM ψ hψ with
    ⟨X, δ, φ, hφ, hcomm, htop, hexact, hzeroX, hzeroδ⟩
  let N₀ : Cpx := subobjectFamilyComplex (C := C) X δ hcomm
  let ι : N₀ ⟶ M := subobjectFamilyInclusion (C := C) X δ hcomm
  have hιmono : Mono ι := subobjectFamilyInclusion_mono (C := C) X δ hcomm
  letI : Mono ι := hιmono
  let N : Subobject M := Subobject.mk ι
  let e : N₀ ≅ (N : Cpx) := (Subobject.underlyingIso ι).symm
  let φN : separator C ⟶ (N : Cpx).X n := φ ≫ e.hom.f n
  have hφN : φN ≫ N.arrow.f n = ψ := by
    have hcomp : e.hom ≫ N.arrow = ι := by
      simpa [e, N] using (Subobject.underlyingIso_arrow ι)
    have hcomp_f : (e.hom ≫ N.arrow).f n = ι.f n := by
      simpa [HomologicalComplex.comp_f] using
        congrArg (fun g : N₀ ⟶ M ↦ g.f n) hcomp
    calc
      φN ≫ N.arrow.f n = φ ≫ ((e.hom ≫ N.arrow).f n) := by
        simp [φN, HomologicalComplex.comp_f]
      _ = φ ≫ ι.f n := by rw [hcomp_f]
      _ = φ ≫ (X n).arrow := by rfl
      _ = ψ := hφ
  have hN_nonzero : ¬ IsZero (N : Cpx) := by
    have hφN_nonzero : φN ≠ 0 := by
      intro hzero
      have hψzero : ψ = 0 := by
        rw [← hφN, hzero]
        simp
      exact hψ hψzero
    intro hZero
    rw [IsZero.iff_id_eq_zero] at hZero
    have hZeroTerm : IsZero ((N : Cpx).X n) := by
      rw [IsZero.iff_id_eq_zero]
      simpa using congrArg (fun g : (N : Cpx) ⟶ (N : Cpx) ↦ g.f n) hZero
    have hZeroMap : φN = 0 := by
      exact hZeroTerm.eq_of_tgt φN 0
    exact hφN_nonzero hZeroMap
  have hN₀small :
      MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) N₀ := by
    exact
      minusAcyclicSubobjectCardinalLE_ofSubobjectFamily
        (C := C) (M := M) (n := n) X δ hcomm htop hexact hzeroX hzeroδ
  have hNsmall :
      MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) (N : Cpx) := by
    refine ⟨?_, ?_, ?_⟩
    · rcases MinusAcyclicSubobjectCardinalLE.minus (C := C) hN₀small with ⟨m, hm⟩
      refine (CochainComplex.minus_iff C _).2 ⟨m, ?_⟩
      rw [CochainComplex.isStrictlyLE_iff] at hm ⊢
      intro i hi
      let ei : (N : Cpx).X i ≅ N₀.X i := cochainComponentIso (C := C) e.symm i
      exact (hm i hi).of_iso ei
    · exact
        acyclic_of_iso (C := C) e
          (MinusAcyclicSubobjectCardinalLE.acyclic (C := C) hN₀small)
    · intro i
      have hbound := MinusAcyclicSubobjectCardinalLE.subobjectCardinalLE (C := C) hN₀small i
      let ei : N₀.X i ≅ (N : Cpx).X i := cochainComponentIso (C := C) e i
      have hcard :
          Cardinal.mk (Subobject (N₀.X i)) = Cardinal.mk (Subobject ((N : Cpx).X i)) := by
        simpa using subobjectCardinal_eq_of_iso (C := C) ei
      simpa [hcard] using hbound
  exact ⟨N, ⟨φN, hφN⟩, hN_nonzero, hNsmall⟩

/-- Helper for Lemma 19.12.2: a seeded bounded-above acyclic subcomplex immediately yields the
small-subcomplex half once the ambient cardinal is `Cardinal.univ`. -/
lemma smallAcyclicSubcomplexBound_univ_ofSeeded
    (hseed :
      ∀ {M : Cpx} (hM : M.Acyclic) {n : ℤ} (ψ : separator C ⟶ M.X n), ψ ≠ 0 →
        ∃ N : Subobject M,
          (∃ φ : separator C ⟶ (N : Cpx).X n, φ ≫ N.arrow.f n = ψ) ∧
            ¬ IsZero (N : Cpx) ∧
              MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) (N : Cpx)) :
    SmallAcyclicSubcomplexBound C (Cardinal.univ.{max u v, max u v + 1}) := by
  intro M hM hM_nonzero
  -- Extract a nonzero separator seed from the ambient nonzero acyclic complex.
  rcases exists_nonzero_separator_map (C := C) (M := M) hM_nonzero with ⟨n, ψ, hψ⟩
  rcases hseed hM ψ hψ with ⟨N, -, hN_nonzero, hNsmall⟩
  exact ⟨N, hN_nonzero, hNsmall⟩

/-- Helper for Lemma 19.12.2: taking the coproduct over all separator maps packages the seeded
subcomplexes into a `Cardinal.univ`-small presentation. -/
lemma acyclicCoproductPresentationBound_univ_ofSeeded
    (hseed :
      ∀ {M : Cpx} (hM : M.Acyclic) {n : ℤ} (ψ : separator C ⟶ M.X n), ψ ≠ 0 →
        ∃ N : Subobject M,
          (∃ φ : separator C ⟶ (N : Cpx).X n, φ ≫ N.arrow.f n = ψ) ∧
            ¬ IsZero (N : Cpx) ∧
              MinusAcyclicSubobjectCardinalLE C (Cardinal.univ.{max u v, max u v + 1}) (N : Cpx)) :
    AcyclicCoproductPresentationBound C (Cardinal.univ.{max u v, max u v + 1}) := by
  classical
  intro M hM
  let I : Type w := Σ n : ℤ, Shrink.{w} (separator C ⟶ M.X n)
  let seed : ∀ p : I, separator C ⟶ M.X p.1 := fun p ↦
    (equivShrink (separator C ⟶ M.X p.1)).symm p.2
  let Mi : I → Cpx := fun p ↦
    if hψ : seed p = 0 then
      zeroCpx (C := C)
    else
      ((Classical.choose (hseed hM (seed p) hψ)) : Subobject M)
  let toM : ∀ p : I, Mi p ⟶ M := fun p ↦ by
    by_cases hψ : seed p = 0
    · simpa [Mi, hψ] using (0 : zeroCpx (C := C) ⟶ M)
    · simpa [Mi, hψ] using
        (((Classical.choose (hseed hM (seed p) hψ)) : Subobject M).arrow)
  let f : (∐ fun i : I ↦ Mi i) ⟶ M := Limits.Sigma.desc toM
  refine ⟨I, Mi, f, ?_, ?_⟩
  · -- Each separator-valued seed factors through its own indexed summand.
    refine HomologicalComplex.epi_of_epi_f _ ?_
    intro m
    refine epi_of_separator_factorization (C := C) (f := f.f m) ?_
    intro ψ
    let p : I := ⟨m, equivShrink (separator C ⟶ M.X m) ψ⟩
    have hι :
        Limits.Sigma.ι (fun i : I ↦ Mi i) p ≫ f = toM p := by
      simpa [f] using Limits.Sigma.ι_desc toM p
    have hιf :
        (Limits.Sigma.ι (fun i : I ↦ Mi i) p).f m ≫ f.f m = (toM p).f m := by
      simpa [HomologicalComplex.comp_f] using congrArg (fun g : Mi p ⟶ M ↦ g.f m) hι
    by_cases hψ : ψ = 0
    · refine ⟨0, ?_⟩
      calc
        0 ≫ f.f m = 0 := by simp
        _ = ψ := by simpa [hψ]
    · have hseedp : seed p ≠ 0 := by
        simpa [seed, p] using hψ
      rcases (Classical.choose_spec (hseed hM (seed p) hseedp)).1 with ⟨φ, hφ⟩
      have hφm :
          φ ≫ ((Classical.choose (hseed hM (seed p) hseedp) : Subobject M).arrow.f m) = ψ := by
        simpa [seed, p] using hφ
      let φ' : separator C ⟶ (Mi p).X m := by
        simpa [Mi, seed, p, hψ] using φ
      have hφ' : φ' ≫ (toM p).f m = ψ := by
        simpa [φ', Mi, toM, seed, p, hψ] using hφm
      refine ⟨φ' ≫ (Limits.Sigma.ι (fun i : I ↦ Mi i) p).f m, ?_⟩
      calc
        (φ' ≫ (Limits.Sigma.ι (fun i : I ↦ Mi i) p).f m) ≫ f.f m
            = φ' ≫ ((Limits.Sigma.ι (fun i : I ↦ Mi i) p).f m ≫ f.f m) := by
                simp [Category.assoc]
        _ = φ' ≫ (toM p).f m := by rw [hιf]
        _ = ψ := hφ'
  · -- Every chosen summand is either the zero complex or one of the seeded small subcomplexes.
    intro p
    by_cases hψ : seed p = 0
    · simpa [Mi, hψ] using minusAcyclicSubobjectCardinalLE_zero_univ (C := C)
    · simpa [Mi, hψ] using (Classical.choose_spec (hseed hM (seed p) hψ)).2.2

-- Proof sketch: choose a generator `U` of `C`, apply Lemma `19.12.1` in a descending induction to
-- every nonzero acyclic complex to obtain nonzero bounded-above acyclic subcomplexes with a
-- uniform termwise size bound, and then use these small subcomplexes through all morphisms
-- `U ⟶ M.X n` to assemble a coproduct of bounded-above acyclic small complexes surjecting onto
-- the original acyclic complex.
/-- Lemma 19.12.2: there is a cardinal `κ` such that every nonzero acyclic cochain complex has a
nonzero `κ`-small bounded-above acyclic subcomplex, and every acyclic cochain complex is a
quotient of a coproduct of `κ`-small bounded-above acyclic complexes. -/
@[stacks 079K]
theorem exists_cardinal_for_small_acyclic_subcomplexes_and_coproduct_presentations
    :
    ∃ κ : Cardinal.{max u v + 1},
      SmallAcyclicSubcomplexBound C κ ∧
        AcyclicCoproductPresentationBound C κ := by
  refine ⟨Cardinal.univ.{max u v, max u v + 1}, ?_, ?_⟩
  · -- The small-subcomplex half is now a direct wrapper around the seeded construction.
    exact
      smallAcyclicSubcomplexBound_univ_ofSeeded (C := C)
        (fun {M} hM {n} ψ hψ ↦ existsSeededUnivSmallAcyclicSubcomplex (C := C) hM ψ hψ)
  · -- The coproduct-presentation half uses the same seeded witnesses, indexed by all separator
    -- maps into the ambient acyclic complex.
    exact
      acyclicCoproductPresentationBound_univ_ofSeeded (C := C)
        (fun {M} hM {n} ψ hψ ↦ existsSeededUnivSmallAcyclicSubcomplex (C := C) hM ψ hψ)

/-- The small-acyclic-subcomplex half of Lemma 19.12.2. -/
theorem exists_cardinal_for_small_acyclic_subcomplexes :
    ∃ κ : Cardinal.{max u v + 1}, SmallAcyclicSubcomplexBound C κ := by
  rcases exists_cardinal_for_small_acyclic_subcomplexes_and_coproduct_presentations C with
    ⟨κ, hκ, _⟩
  exact ⟨κ, hκ⟩

/-- The coproduct-presentation half of Lemma 19.12.2. -/
theorem exists_cardinal_for_acyclic_coproduct_presentations :
    ∃ κ : Cardinal.{max u v + 1}, AcyclicCoproductPresentationBound C κ := by
  rcases exists_cardinal_for_small_acyclic_subcomplexes_and_coproduct_presentations C with
    ⟨κ, _, hκ⟩
  exact ⟨κ, hκ⟩

end Grothendieck

end
end CochainComplex
end CategoryTheory
