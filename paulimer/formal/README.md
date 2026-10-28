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
dense or sparse compiled Rust representations. `PauliRepresentations` adds
executable Lean models for both storage strategies: dense coordinates reuse
BinarFormal's verified packed XOR and dot product, while sparse coordinates
use finite supports, symmetric difference, and intersection parity. Direct
refinement theorems cover packed and sparse multiplication and inversion,
phase updates, packed support queries, sparse weights, order-two testing,
packed offset assignment, and sparse-to-sparse injective remapping.
Support-covered condense/remap semantic models additionally round-trip and
preserve multiplication and inversion. Condensing explicitly requires every
nonidentity coordinate to occur in the ordered support map.

Constructors, dense/sparse or projective conversions, sparse offset assignment,
support-covered condensing, and dense-to-sparse remapping are executable
semantic specifications implemented by decode and repack, rather than proofs
of the corresponding Rust loops. The models store phases in `ZMod 4`, matching
every exposed mathematical observation in Rust. Separate `ZMod 256` lemmas
verify wrapping addition, negation, and Rust's exact
`4 - (raw % 4)` complex-conjugation update after reduction modulo four. These
results do not verify compiled Rust memory or trait implementations. The
concrete one-qubit bridge does not yet connect symbolic Hermiticity or
complex conjugation to matrix conjugate transpose or entrywise conjugation.

`PaulimerFormal.PauliAlgorithms` verifies the fixed-width mathematical core of
the standalone Pauli algorithms. Its packed X-then-Z matrix encoding decodes to
the canonical projective rows. The RREF rank profile is completed by standard
X/Z generators at the non-pivot columns; the result preserves the input prefix,
always spans the full projective space, and, for independent input, is an
independent list of length `2m`. A packed rank check succeeds exactly for
projectively independent input, giving a total model of Rust's independence
assertion. Packed commutation parity, indexed commuting and anticommuting
queries, the pairwise commutation check, Pauli-exponent updates, and root-X/Y/Z
updates all refine their canonical phase-aware semantics.

These fixed-width results correspond to Rust when the supplied
`qubit_count` is `m` and every input support index is below `m`. Lean's types
exclude Rust calls with an undersized runtime count, including their possible
indexing panic, coordinate aliasing, or truncation behavior. The formal
generated-group equality check exhaustively enumerates the binary row span and
is proved sound and complete. It is a reference specification, not a proof of
Rust's implementation, which instead compares the leading rows of two
echelonized matrices and first derives a runtime qubit count. Proving that
comparator requires a canonical-RREF uniqueness theorem not currently supplied
by BinarFormal. The formal `exponentAction` names Rust's branchwise update;
interpreting it as quarter-turn conjugation for suitably normalized Hermitian
generators remains a separate matrix-level obligation.

`PaulimerFormal.PauliGroup` verifies phase-aware subgroup standardization. Each
row of BinarFormal's invertible RREF transform is interpreted as the ordered
product of the indicated input Paulis. Pivot rows retain the verified binary
row space, while zero rows are proved to be scalar relations. The phase-parity
proof uses BinarFormal's inverse transform to show that an odd scalar is
generated exactly when a zero-row relation has odd phase.

The `-I` criterion is also exact: it is generated exactly when there is a
phase-two relation, an odd relation, a non-order-two pivot product, or an
anticommuting pivot pair. This proves the zero-row phase modulus and semantic
`[0]`, `[0, 2]`, or `[0, 1, 2, 3]` phase classification. It matches Rust's
`phases()` for groups constructed with `PauliGroup::new`, or with
`PauliGroup::with_promise` when the optional commutation promise is truthful.
Rust does not validate that promise, so a false promise can make `phases()`,
`contains`, and `log2_size` disagree with the represented subgroup.

The normalized pivot products and the scalar relation generator actually
retained by Rust are then proved to generate exactly the original phase-aware
subgroup. A redundant `-I` relation is omitted when a normalized pivot square
or commutator already generates it:

- `relationPhaseModulus_eq_one_iff`
- `standardPhaseRepresentatives_eq_phaseRepresentatives`
- `two_mem_scalarPhases_iff_standard_trigger`
- `standardPauliGroup_eq_generatedPauliGroup`
- `standardBinaryRank_eq_finrank_projectiveSpan`
- `standardLog2Size_eq_semantic_ranks`

The formal standard group omits Rust's identity-only sentinels for empty output,
including empty input and nonempty all-identity input, because they do not
change the generated subgroup. The current results verify standardization,
scalar phases, binary rank, and the structural rank sum used by `log2_size`
under the truthful-promise condition above. Executable membership,
factorization, and element-enumeration refinements remain separate obligations.

The minimality theorem concerns the Clifford's binary symplectic action.
`TransvectionSigns` additionally proves PR #217's final Pauli correction:
equal binary preimages with self-inverse rows become exactly equal signed
tableaux after the phase-mismatch correction, which is positive Hermitian.
`TransvectionImplementation` verifies a typed executable candidate checker,
minimality of accepted bordered candidates after a correct congruence-search
rejection, and the retained fallback's factor order and minimality.

These are conditional refinement contracts, not proofs of the complete Rust
search or Python bindings. In particular, binary replay and Hermiticity of
the rebuilt tableau remain inputs to the sign theorem. Global Clifford
phase is not represented. See the
[pinned PR #217 review and audit record](../docs/lean-transvection-minimality-proof.md#pr-217-refinement-review).

`Triangularization` and `SpanEnumeration` cover the first two units of the
congruence-search refinement: the exact ordered pivot-deletion/XOR complement,
its span and dimension decrease, the half-matrix alternating guard, and the
little-endian span iterator. The iterator step preserves its running XOR
vector; its finite trace enumerates exactly `2^n - 1` distinct nonzero span
vectors for an independent `n`-vector family, including `n = 0`.
Four principal targets passed action-speaks source-mode audits (entries 80-83).

`TriangularSearch` adds the uncached first-success recursive search, with
soundness, complete failure characterization, and structural termination.
Its matrix wrapper returns an invertible `Q` with unit lower-triangular
`Q E Q^T`; rejection of a faithful core is equivalent to the existing
`CorePresentation.IsTriangularizable` predicate being false. Four further
action-speaks audits passed (entries 84-87). Memoization and complement
deduplication remain unfinished; this is not verification of compiled Rust. See the
[milestone record](../docs/lean-transvection-minimality-proof.md#pr-217-triangularizer-milestone).

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
row reducer or triangularizer. Positive phase normalization is covered by the
canonical Pauli model and the final-correction contract. A complete refinement
of the Rust rotation pipeline, the greedy algorithm and its `4m + 2` guard,
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
