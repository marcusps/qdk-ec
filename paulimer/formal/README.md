# paulimer formal verification

Lean 4 proofs for the minimal symplectic-transvection decomposition used by
`paulimer::clifford_to_transvections_minimal`.

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
row reducer or triangularizer. Positive Hermitian normalization, the greedy
algorithm and its `4m + 2` guard, Python GIL behavior, and resource bounds
remain outside the formalization.

The project pins Lean **4.32.2** and mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`:

```bash
lake build
```

On a fresh checkout, `lake exe cache get` downloads the pinned mathlib cache.
