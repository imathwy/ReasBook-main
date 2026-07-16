import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_51_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped Pointwise

section

variable {A : Type u} {B : Type x} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

namespace LinearMap

open Submodule

variable {P Q : Submodule A M} {P' Q' : Submodule A N}

/-- Helper for Lemma 15.4.3: base change identifies the tensorized subtype of `range f` with the
range of the tensorized map `f.baseChange B`. -/
lemma range_subtype_baseChange_eq_range_baseChange {f : M →ₗ[A] N} :
    LinearMap.range (((LinearMap.range f).subtype).baseChange B) = LinearMap.range (f.baseChange B) := by
  -- Rewrite `f` as the inclusion of its range composed with the range restriction before tensoring.
  have hfactor : f = (LinearMap.range f).subtype.comp f.rangeRestrict := by
    ext x
    rfl
  have hcomp :
      f.baseChange B =
        ((LinearMap.range f).subtype.baseChange B).comp (f.rangeRestrict.baseChange B) := by
    -- Base change respects the factorization of `f` through its range restriction.
    have hbase :=
      LinearMap.baseChange_comp (A := B) (f := f.rangeRestrict) ((LinearMap.range f).subtype)
    rw [hfactor] at hbase
    exact hbase
  -- After base change, the surjective tensorized range restriction does not change the range.
  rw [hcomp, LinearMap.range_comp_of_range_eq_top]
  rw [LinearMap.range_eq_top]
  simpa [LinearMap.baseChange_eq_ltensor] using
    LinearMap.lTensor_surjective B f.surjective_rangeRestrict

/-- Helper for Lemma 15.4.3: inclusions of submodules remain inclusions after base change. -/
lemma submodule_baseChange_mono (hPQ : P ≤ Q) : P.baseChange B ≤ Q.baseChange B := by
  -- Tensor the inclusion `P ↪ Q` and compose it with the tensorized subtype of `Q`.
  let i : P →ₗ[A] Q := Submodule.inclusion hPQ
  have hcomp0 : Q.subtype.comp i = P.subtype := by
    ext x
    rfl
  have hcomp : (Q.subtype.baseChange B).comp (i.baseChange B) = P.subtype.baseChange B := by
    -- Tensor the identity `Q.subtype ∘ i = P.subtype`.
    simpa [hcomp0] using
      (LinearMap.baseChange_comp (A := B) (f := i) Q.subtype).symm
  -- Any element in `P.baseChange B` lies in the range of the tensorized inclusion into `Q`.
  rw [Submodule.baseChange]
  intro x hx
  rw [← hcomp] at hx
  exact LinearMap.range_comp_le_range _ _ hx

/-- Helper for Lemma 15.4.3: the image of a submodule commutes with flat base change. -/
lemma submodule_map_baseChange_eq {f : M →ₗ[A] N} (P : Submodule A M) :
    (Submodule.map f P).baseChange B = Submodule.map (f.baseChange B) (P.baseChange B) := by
  -- First rewrite the mapped submodule as the range of the restricted map `P → N`.
  have hmap :
      Submodule.map f P = LinearMap.range (f.comp P.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  -- Then tensor that restricted map and identify the resulting range.
  rw [Submodule.baseChange, hmap]
  rw [range_subtype_baseChange_eq_range_baseChange (B := B) (f := f.comp P.subtype)]
  rw [LinearMap.baseChange_comp, LinearMap.range_comp]
  -- The range of the tensorized subtype is exactly `P.baseChange B`.
  simp [Submodule.baseChange]

/-- Helper for Lemma 15.4.3: after distributing tensors across a product target, base change of a
pair map is the pair of the base-changed maps. -/
lemma baseChange_prod_eq
    {N₁ : Type*} {N₂ : Type*}
    [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
    (f : M →ₗ[A] N₁) (g : M →ₗ[A] N₂) :
    (TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp ((LinearMap.prod f g).baseChange B) =
      LinearMap.prod (f.baseChange B) (g.baseChange B) := by
  -- Compare the two tensorized pair maps on pure tensors and extend by bilinearity.
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      rfl
  | tmul b m =>
      ext <;> simp [LinearMap.baseChange_tmul]
  | add x y hx hy =>
      simp [map_add, hx, hy]

/-- Helper for Lemma 15.4.3: composing with `TensorProduct.prodRight` does not change the kernel
of a map into a tensorized product. -/
lemma ker_comp_prodRight_eq
    {N₁ : Type*} {N₂ : Type*}
    [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
    (h : (TensorProduct A B M) →ₗ[B] (TensorProduct A B (N₁ × N₂))) :
    LinearMap.ker ((TensorProduct.prodRight A B B N₁ N₂).toLinearMap.comp h) = LinearMap.ker h := by
  -- `TensorProduct.prodRight` is a linear equivalence, so composing with it preserves kernels.
  simpa using
    (LinearEquiv.ker_comp (e'' := TensorProduct.prodRight A B B N₁ N₂) h)

namespace Submodule

/-- Helper for Lemma 15.4.3: after flat base change, the tensorized quotient map by `P` has
kernel exactly the base change of `P`. -/
lemma ker_mkQ_baseChange_eq (P : Submodule A M) :
    LinearMap.ker (P.mkQ.baseChange B) = P.baseChange B := by
  -- Route correction: use the quotient-owner theorem directly instead of rebuilding it from the
  -- generic flat-kernel transport, and compare membership via the tensor exactness owner theorem.
  ext x
  have hx := congrArg (fun S : Submodule A (TensorProduct A B M) => x ∈ S) (lTensor_mkQ B P)
  simpa [LinearMap.baseChange_eq_ltensor, Submodule.baseChange] using hx

/-- Helper for Lemma 15.4.3: rewrite `P.baseChange B` as the span of pure tensors `1 ⊗ x` with
`x ∈ P`. -/
lemma baseChange_eq_span_tmul_mem (P : Submodule A M) :
    P.baseChange B =
      Submodule.span B {z | ∃ x ∈ P, z = TensorProduct.tmul A 1 x} := by
  -- Freeze the standard base-change generators into the exact pure-tensor shape used below.
  rw [Submodule.baseChange_eq_span]
  congr 1
  ext z
  constructor
  · intro hz
    rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.4.3: flatness upgrades the owner `lTensor` kernel identity to the
rewrite-friendly statement for `LinearMap.baseChange`. -/
lemma ker_baseChange_eq_of_flat {g : M →ₗ[A] N} :
    LinearMap.ker (g.baseChange B) = (LinearMap.ker g).baseChange B := by
  -- Rewrite `g.baseChange B` into the owner `lTensor` form once and apply flat exactness there.
  calc
    LinearMap.ker (g.baseChange B) =
        LinearMap.range (((LinearMap.ker g).subtype).baseChange B) := by
          simpa [LinearMap.baseChange_eq_ltensor] using
            (Module.Flat.ker_lTensor_eq (S := B) (M := B) g)
    _ = (LinearMap.ker g).baseChange B := by
          rw [Submodule.baseChange]

/-- Helper for Lemma 15.4.3: flat base change carries intersections of submodules to intersections
of their base changes. -/
lemma inf_baseChange_eq_of_flat (P Q : Submodule A M) :
    ((P ⊓ Q).baseChange B : _root_.Submodule B (TensorProduct A B M)) =
      P.baseChange B ⊓ Q.baseChange B := by
  -- Route correction: compare both sides as kernels of the tensorized pair quotient map
  -- `(P.mkQ, Q.mkQ)` and isolate the `TensorProduct.prodRight` transport in one rewrite.
  let φ : M →ₗ[A] ((M ⧸ P) × (M ⧸ Q)) := LinearMap.prod P.mkQ Q.mkQ
  -- First identify the source intersection as the kernel of the pair quotient map and tensor it.
  calc
    ((P ⊓ Q).baseChange B : _root_.Submodule B (TensorProduct A B M)) =
        (LinearMap.ker φ).baseChange B := by
          simp [φ, LinearMap.ker_prod]
    _ = LinearMap.ker (φ.baseChange B) := by
          rw [← ker_baseChange_eq_of_flat (B := B) (g := φ)]
    -- Then move to the product owner shape and peel the kernel apart coordinatewise.
    _ = LinearMap.ker
          ((TensorProduct.prodRight A B B (M ⧸ P) (M ⧸ Q)).toLinearMap.comp (φ.baseChange B)) := by
          simpa using
            (ker_comp_prodRight_eq (A := A) (B := B)
              (N₁ := M ⧸ P) (N₂ := M ⧸ Q)
              (h := φ.baseChange B)).symm
    _ = LinearMap.ker (LinearMap.prod (P.mkQ.baseChange B) (Q.mkQ.baseChange B)) := by
          simpa [φ] using
            congrArg LinearMap.ker (baseChange_prod_eq (A := A) (B := B) P.mkQ Q.mkQ)
    _ = LinearMap.ker (P.mkQ.baseChange B) ⊓ LinearMap.ker (Q.mkQ.baseChange B) := by
          rw [LinearMap.ker_prod]
    _ = P.baseChange B ⊓ Q.baseChange B := by
          rw [ker_mkQ_baseChange_eq, ker_mkQ_baseChange_eq]

/-- Helper for Lemma 15.4.3: base change sends `J • ⊤` to the corresponding extended ideal acting
on the base-changed module. -/
lemma smul_top_baseChange_eq (J : Ideal A) :
    (((J • (⊤ : Submodule A M)).baseChange B : _root_.Submodule B (TensorProduct A B M))) =
      (J.map (algebraMap A B)) • (⊤ : _root_.Submodule B (TensorProduct A B M)) := by
  let L : Submodule B (TensorProduct A B M) :=
    (((J • (⊤ : Submodule A M)).baseChange B : _root_.Submodule B (TensorProduct A B M)))
  have hL :
      L =
        Submodule.span B
          {z | ∃ x ∈ J • (⊤ : Submodule A M), z = TensorProduct.tmul A (1 : B) x} := by
    -- Freeze the left side in the pure-tensor generator form used by both inclusions.
    simpa [L] using (baseChange_eq_span_tmul_mem (B := B) (P := J • (⊤ : Submodule A M)))
  have htmul_of_mem_map :
      ∀ b ∈ J.map (algebraMap A B), ∀ m : M, TensorProduct.tmul A b m ∈ L := by
    intro b hb m
    have hspan :
        J.map (algebraMap A B) = Ideal.span ((algebraMap A B) '' (↑J : Set A)) := by
      -- Rewrite membership in the extended ideal as span membership in the image generators.
      simpa [Ideal.span_eq] using (Ideal.map_span (algebraMap A B) (↑J : Set A))
    rw [hspan] at hb
    -- Induct on the ideal-span presentation of the first tensor factor.
    refine Submodule.span_induction (p := fun b _ => TensorProduct.tmul A b m ∈ L)
      ?_ ?_ ?_ ?_ hb
    · intro b hb
      rcases hb with ⟨a, ha, rfl⟩
      have hsmul : a • m ∈ J • (⊤ : Submodule A M) := by
        exact Submodule.smul_mem_smul ha (by simp)
      rw [hL]
      have hgen :
          TensorProduct.tmul A (1 : B) (a • m) ∈
            Submodule.span B
              {z | ∃ x ∈ J • (⊤ : Submodule A M), z = TensorProduct.tmul A (1 : B) x} := by
        exact Submodule.subset_span ⟨a • m, hsmul, rfl⟩
      have hcoef :
          TensorProduct.tmul A ((algebraMap A B) a) m = TensorProduct.tmul A (1 : B) (a • m) := by
        calc
          TensorProduct.tmul A ((algebraMap A B) a) m = TensorProduct.tmul A (a • (1 : B)) m := by
            simp [Algebra.smul_def]
          _ = a • TensorProduct.tmul A (1 : B) m := by
            rfl
          _ = TensorProduct.tmul A (1 : B) (a • m) := by
            simpa using (TensorProduct.tmul_smul (R := A) (R' := A) a (1 : B) m).symm
      -- The source generators `1 ⊗ a • m` are exactly the pure tensors with image coefficient.
      rw [hcoef]
      exact hgen
    · simpa using (show (0 : TensorProduct A B M) ∈ L from Submodule.zero_mem L)
    · intro b₁ b₂ _ _ hb₁ hb₂
      simpa [TensorProduct.add_tmul] using add_mem hb₁ hb₂
    · intro c b _ hb
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using (Submodule.smul_mem L c hb)
  apply le_antisymm
  · change L ≤ (J.map (algebraMap A B)) • (⊤ : _root_.Submodule B (TensorProduct A B M))
    rw [hL]
    refine Submodule.span_le.2 ?_
    rintro z ⟨x, hx, rfl⟩
    -- Reduce a source element `x ∈ J • ⊤` to pure tensor generators in the target ideal-smul.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m hm
      have ha' : algebraMap A B a ∈ J.map (algebraMap A B) := Ideal.mem_map_of_mem _ ha
      simpa [TensorProduct.tmul_smul] using
        (Submodule.smul_mem_smul ha'
          (show TensorProduct.tmul A (1 : B) m ∈
              (⊤ : _root_.Submodule B (TensorProduct A B M)) by simp))
    · intro x y hx hy
      simpa [TensorProduct.tmul_add] using add_mem hx hy
  · change (J.map (algebraMap A B)) • (⊤ : _root_.Submodule B (TensorProduct A B M)) ≤ L
    intro z hz
    -- Reduce a target ideal-smul element to pure tensors, then absorb the coefficient into `L`.
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro b hb t ht
      clear ht
      induction t using TensorProduct.induction_on with
      | zero =>
          simpa using (show (0 : TensorProduct A B M) ∈ L from Submodule.zero_mem L)
      | tmul b' m =>
          have hmul : b * b' ∈ J.map (algebraMap A B) := by
            exact Ideal.mul_mem_right b' _ hb
          simpa [L, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
            (htmul_of_mem_map (b * b') hmul m)
      | add t₁ t₂ ht₁ ht₂ =>
          simpa [smul_add] using add_mem ht₁ ht₂
    · intro x y hx hy
      exact add_mem hx hy

end Submodule

/- Domain-style sampling:
- primary domain: Artin-Rees bounds for linear maps under flat scalar extension;
- sampled declarations: `LinearMap.IsArtinReesBound`,
  `LinearMap.isArtinReesBound_of_preimage_pow_smul_eq`, `LinearMap.baseChange`,
  and `Module.Flat.lTensor_exact`;
- core/canonical owner: `LinearMap.IsArtinReesBound`;
- source-facing content: the Stacks lemma that the same Artin-Rees constant survives flat base
  change;
- bridge/view target here: a base-change theorem for the owner-level predicate, not a parallel
  stronger reformulation in terms of preimage equalities. -/

-- Proof sketch: tensor the exact sequence computing the Artin-Rees quotient by `B`, use flatness
-- to preserve the relevant intersections and kernels, rewrite `I.map (algebraMap A B) ^ n` as the
-- base change of `I ^ n`, and identify the image term with the corresponding image for
-- `f.baseChange B`.
/-- Lemma 15.4.3: if `c` is an Artin-Rees bound for `f` with respect to `I`, then after flat base
change along `A → B` the same `c` is an Artin-Rees bound for `f.baseChange B` with respect to
`I.map (algebraMap A B)`. -/
@[stacks 07VG]
theorem IsArtinReesBound.baseChange {f : M →ₗ[A] N} {I : Ideal A} {c : ℕ}
    (hc : f.IsArtinReesBound I c) :
    (f.baseChange B).IsArtinReesBound (I.map (algebraMap A B)) c := by
  -- Route correction: the base-changed inclusion `P.baseChange B ≤ Q.baseChange B` is now
  -- available, so the theorem now reduces to deterministic rewrites of the tensorized
  -- intersection and ideal-power terms.
  intro n hn
  have hbase :
      ((LinearMap.range f ⊓ I ^ n • (⊤ : _root_.Submodule A N)).baseChange B :
          _root_.Submodule B (TensorProduct A B N)) ≤
        (Submodule.map f (I ^ (n - c) • (⊤ : _root_.Submodule A M))).baseChange B :=
    submodule_baseChange_mono (B := B) (hc n hn)
  -- Tensor the Artin-Rees inclusion once, then rewrite both tensorized terms into owner shape.
  rw [LinearMap.Submodule.inf_baseChange_eq_of_flat (B := B) (P := LinearMap.range f)
        (Q := I ^ n • (⊤ : _root_.Submodule A N)),
    _root_.Submodule.baseChange,
    range_subtype_baseChange_eq_range_baseChange (B := B) (f := f),
    LinearMap.Submodule.smul_top_baseChange_eq (B := B) (M := N) (J := I ^ n),
    submodule_map_baseChange_eq (B := B) (f := f)
      (P := I ^ (n - c) • (⊤ : _root_.Submodule A M)),
    LinearMap.Submodule.smul_top_baseChange_eq (B := B) (M := M) (J := I ^ (n - c))] at hbase
  simpa [Ideal.map_pow] using hbase

end LinearMap

end
