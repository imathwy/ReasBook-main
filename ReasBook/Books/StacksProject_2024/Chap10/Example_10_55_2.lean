import stacks_project.Chap10.Lemma_10_55_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable (k : Type u) [Field k]

/- Domain-style sampling for Example 10.55.2:
- primary domain: the comparison between `K₀(k)` of finite projective `k`-modules and `K'_0(k)`
  of finite `k`-modules, identified with `ℤ` by rank/length;
- sampled owner declarations:
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length`,
  `projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply`,
  `finiteGrothendieckGroup_lengthEquiv`,
  `finiteGrothendieckGroup_lengthEquiv_apply`,
  `projectiveGrothendieckGroup_rankMap`;
- best owner abstraction:
  the canonical owner data is the comparison square from Lemma 10.55.9 together with the chapter's
  length equivalence `finiteGrothendieckGroup_lengthEquiv`; this file is a field-specific
  `bridge/view`, not a new owner;
- primitive vs. derived:
  primitive data remains the comparison map `K₀(k) → K'_0(k)` and the rank/length homomorphisms;
  the field statement is the derived specialization where `length_k(k) = 1`;
- source/core/bridge triage:
  `source-facing`: Example 10.55.2 identifying the canonical comparison with the dimension map;
  `core/canonical`: Lemma 10.55.9 and `finiteGrothendieckGroup_lengthEquiv`;
  `bridge/view`: the field specialization below.
-/
/-- Helper for Example 10.55.2: over a field, the free rank-one module `k` has length `1`. -/
private theorem field_self_length_toNat_int_eq_one :
    ((Module.length k k).toNat : ℤ) = 1 := by
  -- Convert the module length of `k` into its finite dimension over itself.
  simpa [Module.finrank_self] using
    congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_eq_finrank k k)

/-- Over a field `k`, the canonical comparison map `K₀(k) → K'_0(k)` commutes with the rank and
length identifications with `ℤ`. -/
theorem field_projectiveGrothendieckGroup_comparison_commutes_with_rank :
    (finiteGrothendieckGroup_lengthEquiv k).toAddMonoidHom.comp
        (ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k)) =
      projectiveGrothendieckGroup_rankMap k := by
  apply AddMonoidHom.ext
  intro x
  -- Evaluate Lemma 10.55.9 on `x` and identify the length equivalence with the length map.
  -- Over a field, the ring-length factor from the local Artinian comparison square is `1`.
  simpa [finiteGrothendieckGroup_lengthEquiv_apply, field_self_length_toNat_int_eq_one, one_mul] using
    projectiveGrothendieckGroup_comparison_commutes_with_rank_and_length_apply k x

/-- Example 10.55.2: if `R = k` is a field, then the canonical map `K₀(k) → K'_0(k)` is the
identification obtained by the dimension function, which over a field is also the length function.
Equivalently, the comparison map is the canonical passage through `ℤ`. -/
theorem field_projectiveGrothendieckGroup_to_finiteGrothendieckGroup_eq :
    ModulePropertyK0.map k (finiteProjectiveModuleProperty_le_isFG k) =
      (finiteGrothendieckGroup_lengthEquiv k).symm.toAddMonoidHom.comp
        (projectiveGrothendieckGroup_rankMap k) := by
  apply AddMonoidHom.ext
  intro x
  -- Apply the length equivalence to reduce the comparison map to the commutative square above.
  apply (finiteGrothendieckGroup_lengthEquiv k).injective
  -- After composing with the equivalence, both sides are exactly the rank map.
  simpa [AddMonoidHom.comp_apply] using
    DFunLike.congr_fun (field_projectiveGrothendieckGroup_comparison_commutes_with_rank k) x
