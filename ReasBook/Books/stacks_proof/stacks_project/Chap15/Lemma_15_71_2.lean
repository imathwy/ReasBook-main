import Mathlib
import StacksProject_2024.Chap15.Lemma_15_71_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
* primary domain: factorization of linear maps through finite projective modules;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `Module.Finite`,
  `Module.Projective`,
  `Module.FiniteProjective`;
* best owner abstraction: the canonical owner predicates on the intermediate module are
  `Module.Finite R P` and `Module.Projective R P`; the source-facing public owner in this file is
  the induced predicate on a linear map recording factorization through such an intermediate
  module, since the project-level abbreviation `Module.FiniteProjective` is restricted to the
  commutative-ring/additive-group setting and would strengthen the present semiring semantics;
* layer triage:
  `Module.Finite` and `Module.Projective` are `core/canonical`,
  `FactorsThroughFiniteProjective` is `source-facing`,
  `FactorsThroughFiniteProjective.factorsThroughProjective` is the `bridge/view` that forgets
  finiteness;
* primitive data: an intermediate module `P` together with maps `M →ₗ[R] P →ₗ[R] N`;
* derived API: forgetting finiteness yields a projective factorization, and when `M` is finite a
  projective factorization upgrades to a finite-projective one by shrinking a free factorization
  to a finite free submodule.
-/

namespace LinearMap

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {F : Type*} [AddCommMonoid F] [Module R F]
variable {ι : Type*}

/-- A linear map factors through a finite projective `R`-module. -/
def FactorsThroughFiniteProjective (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P)
    (_ : Module.Finite R P) (_ : Module.Projective R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

-- Proof sketch: forget the finiteness assumption on the intermediate module in the defining
-- factorization.
/-- A finite-projective factorization is in particular a projective factorization. -/
theorem FactorsThroughFiniteProjective.factorsThroughProjective {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughFiniteProjective) : φ.FactorsThroughProjective := by
  -- Forget the finite-generation field from the chosen intermediate module.
  rcases hφ with ⟨P, _, _, _, _, f, g, hcomp⟩
  exact ⟨P, inferInstance, inferInstance, inferInstance, f, g, hcomp⟩

/-- Helper for Lemma 15.71.2: the span of finitely many basis vectors is a free module. -/
lemma span_basis_image_free (b : Module.Basis ι R F) (t : Finset ι) :
    Module.Free R (Submodule.span R (b '' (↑t : Set ι))) := by
  classical
  let v : {i // i ∈ (↑t : Set ι)} → F := fun i ↦ b i
  have hv : LinearIndependent R v := by
    simpa [v] using b.linearIndependent.comp (fun i : {i // i ∈ (↑t : Set ι)} ↦ (i : ι))
      Subtype.val_injective
  have hrange : Set.range v = b '' (↑t : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hspan : Submodule.span R (Set.range v) = Submodule.span R (b '' (↑t : Set ι)) := by
    rw [hrange]
  -- Reindex the ambient basis by the finite subtype cut out by `t`.
  let _ : Module.Free R (Submodule.span R (Set.range v)) := Module.Free.of_basis (Module.Basis.span hv)
  exact Module.Free.of_equiv (LinearEquiv.ofEq _ _ hspan)

/-- Helper for Lemma 15.71.2: the span of finitely many basis vectors is a finite module. -/
lemma span_basis_image_finite (b : Module.Basis ι R F) (t : Finset ι) :
    Module.Finite R (Submodule.span R (b '' (↑t : Set ι))) := by
  classical
  let v : {i // i ∈ (↑t : Set ι)} → F := fun i ↦ b i
  have hv : LinearIndependent R v := by
    simpa [v] using b.linearIndependent.comp (fun i : {i // i ∈ (↑t : Set ι)} ↦ (i : ι))
      Subtype.val_injective
  have hfinite : Finite {i // i ∈ (↑t : Set ι)} := t.finite_toSet.to_subtype
  have hrange : Set.range v = b '' (↑t : Set ι) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hspan : Submodule.span R (Set.range v) = Submodule.span R (b '' (↑t : Set ι)) := by
    rw [hrange]
  -- The finite subtype of indices supplies a finite basis for the span.
  letI : Finite {i // i ∈ (↑t : Set ι)} := hfinite
  let _ : Module.Finite R (Submodule.span R (Set.range v)) := Module.Finite.of_basis (Module.Basis.span hv)
  exact Module.Finite.equiv (LinearEquiv.ofEq _ _ hspan)

/-- Helper for Lemma 15.71.2: coordinate support inside `t` puts a vector in the span of the
corresponding basis vectors. -/
lemma mem_span_basis_image_of_support_subset (b : Module.Basis ι R F) (t : Finset ι) (x : F)
    (hx : ↑(b.repr x).support ⊆ (↑t : Set ι)) :
    x ∈ Submodule.span R (b '' (↑t : Set ι)) := by
  -- Translate the support bound into the standard basis-span criterion.
  exact (b.mem_span_image).2 hx

/-- Helper for Lemma 15.71.2: support control on a finite generating set forces the whole linear
map to land in the corresponding finite span of basis vectors. -/
lemma linearMap_maps_into_span_basis_image_of_fg (s : Finset M)
    (hs : Submodule.span R (↑s : Set M) = ⊤) (f : M →ₗ[R] F) (b : Module.Basis ι R F)
    (t : Finset ι)
    (hgen : ∀ m ∈ s, ↑(b.repr (f m)).support ⊆ (↑t : Set ι)) :
    ∀ x : M, f x ∈ Submodule.span R (b '' (↑t : Set ι)) := by
  intro x
  have hxspan : x ∈ Submodule.span R (↑s : Set M) := by
    simpa [hs] using (show x ∈ (⊤ : Submodule R M) from trivial)
  -- Extend generator-wise membership to all of `M` by span induction.
  refine Submodule.span_induction (p := fun y _ ↦ f y ∈ Submodule.span R (b '' (↑t : Set ι)))
    ?_ ?_ ?_ ?_ hxspan
  · intro y hy
    exact mem_span_basis_image_of_support_subset (b := b) (t := t) (x := f y) (hgen y hy)
  · simpa using (Submodule.zero_mem (Submodule.span R (b '' (↑t : Set ι))))
  · intro y z _ _ hy hz
    simpa [LinearMap.map_add] using
      Submodule.add_mem (Submodule.span R (b '' (↑t : Set ι))) hy hz
  · intro a y _ hy
    simpa [LinearMap.map_smul] using
      Submodule.smul_mem (Submodule.span R (b '' (↑t : Set ι))) a hy

-- Proof sketch: by Lemma `15.71.1`, first factor `φ` through a free module. Because `M` is finite,
-- finitely many generators of `M` have images supported on only finitely many basis vectors, so
-- the factorization lands in a finite free submodule. A finite free module is finite projective.
/-- Lemma 15.71.2: if an `R`-linear map `φ : M →ₗ[R] N` factors through a projective module and
`M` is a finite `R`-module, then `φ` factors through a finite projective `R`-module. -/
@[stacks 0G91]
theorem FactorsThroughProjective.factorsThroughFiniteProjective [Module.Finite R M]
    {φ : M →ₗ[R] N} (hφ : φ.FactorsThroughProjective) :
    φ.FactorsThroughFiniteProjective := by
  classical
  rcases (factorsThroughProjective_iff_factorsThroughFree (R := R) (M := M) (N := N) φ).mp hφ with
    ⟨F, _, _, _, f, g, hcomp⟩
  let b : Module.Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  have hfg_top : (⊤ : Submodule R M).FG :=
    (Module.Finite.iff_fg (R := R) (N := (⊤ : Submodule R M))).mp inferInstance
  obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hfg_top
  let s : Finset M := hSfinite.toFinset
  have hs : Submodule.span R (↑s : Set M) = ⊤ := by
    simpa [s, hSfinite.coe_toFinset] using hSspan
  let t : Finset (Module.Free.ChooseBasisIndex R F) :=
    s.biUnion fun m ↦ (b.repr (f m)).support
  let Q : Submodule R F := Submodule.span R (b '' (↑t : Set (Module.Free.ChooseBasisIndex R F)))
  have hgen :
      ∀ m ∈ s, ↑(b.repr (f m)).support ⊆ (↑t : Set (Module.Free.ChooseBasisIndex R F)) := by
    intro m hm
    exact Finset.subset_biUnion_of_mem (fun x ↦ (b.repr (f x)).support) hm
  have hQ : ∀ x : M, f x ∈ Q := by
    -- The finite generating set controls every basis coordinate needed by `f`.
    simpa [Q] using
      linearMap_maps_into_span_basis_image_of_fg (R := R) (F := F)
        (ι := Module.Free.ChooseBasisIndex R F) s hs f b t hgen
  let _ : Module.Free R Q :=
    span_basis_image_free (R := R) (F := F) (ι := Module.Free.ChooseBasisIndex R F) b t
  let _ : Module.Finite R Q :=
    span_basis_image_finite (R := R) (F := F) (ι := Module.Free.ChooseBasisIndex R F) b t
  let f' : M →ₗ[R] Q := LinearMap.codRestrict Q f hQ
  -- Factor through the finite free submodule generated by the coordinates used on generators.
  refine ⟨Q, inferInstance, inferInstance, inferInstance, inferInstance, f',
    g.comp Q.subtype, ?_⟩
  ext x
  rw [hcomp]
  rfl

end

end LinearMap
