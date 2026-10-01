# paulimer formal verification

Lean 4 proofs for the minimal symplectic-transvection decomposition used by
`paulimer::clifford_to_transvections_minimal`.

The theorem concerns the Clifford's binary symplectic action. Pauli-image signs
and global phase are outside its scope. It proves the action-level
specification underlying the Rust algorithm, not the compiled Rust or Python
bindings.

See the [proof strategy and module guide](../docs/lean-transvection-minimality-proof.md).

The main results are:

- `CorePresentation.exists_factorization_iff_isTriangularizable`
- `CorePresentation.exists_minimal_factorization`
- `exists_residue_fix_of_not_triangularizable`
- `minimalDecomposition_spec`

They prove replay correctness, strict minimality, the universal `r`/`r+1`
range, the exact length-`r` criterion, and totality of the residue fix search.

```bash
lake exe cache get
lake build
```
