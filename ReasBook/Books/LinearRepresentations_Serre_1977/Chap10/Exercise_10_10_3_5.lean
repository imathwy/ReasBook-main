import LinearRepresentations_Serre_1977.Chap10.Exercise_10_10_3_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for this item:
* primary domain: ordinary character theory for finite groups, with tensor characters reduced
  modulo a prime ideal and evaluated at the canonical `p'`-component `pRegularComponent p x`;
* relevant owner declarations inspected in this domain:
  `pRegularComponent`,
  `characterRingScalarExtension`,
  `integerValued_tensorCharacter_modEq_pRegularComponent`,
  `character_value_congruent_mod_ideal`;
* best owner abstraction: the source-facing exercise already lives on the chapter owner theorems
  for tensor characters `χ : A ⊗R(G)` and their quotient values modulo an ideal, so this item file
  should reuse those owners directly rather than maintain a parallel local theorem/helper layer.

Primitive data vs. derived API:
* primitive data: the prime ideal `𝔭`, the tensor character `χ : A ⊗R(G)`, its `A`-valued
  realization `f`, the element `x`, and the explicit counterexample witness data in the chapter
  file;
* derived API: quotient-equality reformulations, realized-span bridge lemmas, and auxiliary
  quartic-root witness helpers. Those are not new source-facing owners here and should not remain
  as a duplicate public layer in this item file.

Source/core/bridge triage:
* source-facing: the two exercise statements, namely the congruence modulo `𝔭` and the existence
  of a counterexample to the stronger modulus `(p)A`;
* core/canonical: the chapter owner theorems
  `character_value_congruent_mod_ideal` and
  `exists_tensorCharacter_character_value_mod_pIdeal_ne`;
* bridge/view: the deleted local quotient-equality and realized-span wrapper lemmas were only
  bridge/view API around those owners, not independent mathematical content.

This refine pass therefore targets the `core/canonical` layer: the item is best expressed as a
direct recall of the already-owned chapter declarations. -/

/- Exercise 10-10.3-5 (1) is already owned by the chapter theorem
`character_value_congruent_mod_ideal`. The item contributes no new owner beyond recalling that
canonical source-facing statement. -/
recall character_value_congruent_mod_ideal

/- Exercise 10-10.3-5 (2) is already owned by the chapter theorem
`exists_tensorCharacter_character_value_mod_pIdeal_ne`, which gives the explicit witness-data
counterexample to the stronger modulus `(p)A`. -/
recall exists_tensorCharacter_character_value_mod_pIdeal_ne
