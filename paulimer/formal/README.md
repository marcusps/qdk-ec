# paulimer formal verification

Lean 4 proofs for Paulimer's phase-aware Pauli algebra and the minimal
symplectic-transvection decomposition used by
`paulimer::clifford_to_transvections_minimal`.

`PaulimerFormal.Pauli` defines storage-independent Paulis in Paulimer's `xz`
phase convention, `i^p X^x Z^z`. It proves the group laws, xz/xyz phase
conversion, the Y-count/Y-weight identity, commutation and anticommutation
criteria, the phase-only center, the self-inverse criterion corresponding to
Hermiticity, unique zero-`xyz`-phase normalization, conjugation signs, and the
order-four bound. Its one-qubit interpretation uses Physlib's concrete Pauli
matrices and is proved multiplicative by `oneQubitMatrix_mul`;
`oneQubitMatrixHom` packages that result as a monoid homomorphism. The
symbolic X, Y, and Z generators are also proved equal to Physlib's
corresponding matrices.

These Pauli results verify the canonical mathematics, not yet Paulimer's
dense or sparse Rust representations. Their refinement to executable packed
models and compiled Rust remains separate work. The concrete one-qubit bridge
does not yet connect the symbolic Hermiticity or complex-conjugation
definitions to matrix conjugate transpose or entrywise conjugation.

The theorem concerns the Clifford's binary symplectic action. Pauli-image signs
and global phase are outside its scope. It proves the action-level
specification underlying the Rust algorithm, not the compiled Rust or Python
bindings.

The input type `SymplecticAction m` carries a proof of symplecticity. Applying
these results to a Rust input requires a valid Clifford tableau; the Rust
decomposition functions do not themselves call `is_valid`.

See the [proof strategy and module guide](../docs/lean-transvection-minimality-proof.md),
including its [Rust contract correspondence](../docs/lean-transvection-minimality-proof.md#rust-contract-correspondence)
and per-commit review of the updated #118/#119 implementation.

The main results are:

- `CorePresentation.exists_factorization_iff_isTriangularizable`
- `CorePresentation.exists_minimal_factorization`
- `exists_residue_fix_of_not_triangularizable`
- `minimalDecomposition_spec`

They prove replay correctness, strict minimality, the universal `r`/`r+1`
range, the exact length-`r` criterion, existence of a nonzero rank-preserving
residue fix in every finite dimension, and totality of the separate finite
factorization reference search. They do **not** prove that Rust's enumeration,
row reduction, congruence-triangularization search, fix-vector enumeration,
memoization, or recursion is sound, complete, or panic-free. Rust implements a
different algorithm from Lean's reference search.

Implementation-facing matrix lemmas make the correspondence explicit:

- `residueRank_inv` and `residueRank_add_finrank_fixedSpace` justify the
  inverse/preimage-matrix rank and fixed-space dimension used by the tests.
- `exists_residue_coefficient_of_basis` applies to any faithful residue basis,
  not just Lean's noncomputably chosen one.
- `CorePresentation.core_eq_of_row_reduction` identifies Rust's formula
  `V Rᵀ`, where `V = R F̂`, with the formal core `D⁻ᵀ`.
- `CorePresentation.factorization_of_triangularizer` proves that the rows of
  `Q V` replay in their returned order when `Q` is a valid triangularizer.
- `CorePresentation.isTriangularizable_iff_canonical` connects a supplied
  faithful basis to the canonical core used by the one-fix theorem.

These lemmas assume the stated matrix invariants; they do not verify Rust's
row reducer or triangularizer. The use of positive phase normalization in the
Rust transvection pipeline, the greedy algorithm and its `4m + 2` guard,
Python GIL behavior, and resource bounds remain outside the formalization.

`PaulimerFormal.BinarBridge` imports the sibling `BinarFormal` project and
records the shared `X`-then-`Z` coordinate convention. Its main refinement
theorems show that Binar's verified packed operations decode to Paulimer's
matrix semantics:

- `decodeActionMatrix_transpose`
- `decodePhaseVector_mulVec`
- `decodePhaseVector_rightMultiply`

This is a semantic bridge to Binar's executable Lean model. It does not by
itself prove that the compiled Rust packed representation matches that model.

The project pins Lean **4.34.0**, mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and Physlib
`d410e856abdd7c4c747332da2533c1596327a473`. The local BinarFormal dependency
uses the same Lean and mathlib pins:

```bash
lake build
```

On a fresh checkout, `lake exe cache get` downloads the pinned mathlib cache.
