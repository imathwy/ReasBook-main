import stacks_project.Chap10.Lemma_10_72_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]

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
    1 ≤ moduleDepth R (M →ₗ[R] N) := sorry

-- Proof sketch: use the same short exact sequence
-- `0 → Hom_R(M, N) → N^n → N' → 0`. Part `(1)` gives `moduleDepth R N' ≥ 1` when
-- `moduleDepth R N ≥ 2`, while `moduleDepth R N^n ≥ 2`. Then apply the canonical Chapter 10 owner
-- theorem `CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min` to recover
-- `moduleDepth R Hom_R(M, N) ≥ 2`.
/-- Lemma 15.23.10 (2): if `N` has depth at least `2`, then `Hom_R(M, N)` has depth at least `2`.
-/
theorem moduleDepth_linearMap_ge_two
    (hN : 2 ≤ moduleDepth R N) :
    2 ≤ moduleDepth R (M →ₗ[R] N) := sorry

end
