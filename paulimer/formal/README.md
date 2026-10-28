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

`PauliExponent` now proves that this branchwise update, for a self-inverse
exponent, is a phase-preserving Pauli-group automorphism. The inverse uses
the negative exponent; self-inversion is preserved, and the projective
action is exactly the binary transvection. Audit 105 verified the combined
contract, including the Hermitian precondition. This is an algebraic bridge;
the concrete unitary-matrix interpretation remains open. The signed-tableau
interpretation is established below.

`Clifford` defines phase-preserving Pauli automorphisms as a subgroup of
Mathlib's `MulAut`. It derives their symplectic binary actions, signed
image/preimage inverses, and Hermiticity preservation. Composition satisfies
`F_(A B) = F_B F_A` in row-vector conventions, so left composition by a
quarter-turn gives the greedy update `F T_v`. The lifted Pauli-exponent
automorphism projects to that transvection. Audits 106-107 passed.
Constructing the automorphism from validated rows is covered below;
binary identity is not identified with signed identity.

`CliffordTableau` proves that its executable validity checker accepts exactly
Hermitian rows with canonical commutation, equivalently Hermitian rows with
a symplectic preimage matrix. The upper-triangle conditions in #217's
`is_valid_clifford` are equivalent to this full-pair condition. Preimages
of semantic Clifford actions are valid and their matrix is exactly the
inverse binary action. Audits 108-109 passed. These results do not
verify compiled Rust or its storage layout.

`CliffordRealization` constructs a phase-preserving automorphism for every
valid signed tableau. Reversed quarter-turn products realize the minimal
binary decomposition of its inverse preimage matrix; left Pauli conjugation
then implements the existing final sign correction exactly. Thus binary
replay and Hermiticity are derived rather than assumed for this construction.
Audits 111-112 passed. All 24 signed one-qubit tableaux were reconstructed
in bounded execution batches. Concrete unitary realization remains open.
Minimality counts binary transvections, not the separate final
Pauli correction.

`CliffordUniqueness` proves that valid signed tableaux extend uniquely to
phase-preserving Pauli automorphisms, using Mathlib's equalizer subgroup
and a generalized version of the existing Pauli-group span witness proof.
The resulting equivalence upgrades signed row reconstruction to full action
equality. `signedDecomposition_spec` proves exact reconstruction of every
semantic Clifford by shortest nonzero binary transvections, lifted to
positive-Hermitian quarter-turns, and the final positive-Hermitian Pauli
correction. Audits 113-114 passed. This closes the mathematical signed
bridge for #119/#217, not compiled Rust, concrete unitary global phase, or
the separate finite classification claims in #118.

`TwoQubitEnumeration` lists every element of `Sp(4,2)` exactly once and
proves its cardinality is 720. Four-bit frames decode bijectively to
binary matrices; their six pairing conditions are equivalent to
symplecticity. The count uses ordinary kernel reduction, with a structural
duplicate-freedom proof. Audit 115 passed. Exception counts and greedy
optimality require separate proofs, not enumeration alone.

`TwoQubitAction` proves exact four-bit matrix action and transvection
updates, providing a small executable representation for the remaining
finite checks. Its hyperbolicity test is equivalent to vanishing pairing
with every vector's image; kernel reduction counts exactly 15 nonidentity
hyperbolic actions. Audit 116 passed.

`TwoQubitRank` identifies the executable fixed-code count with the
cardinality of the mathematical fixed space, giving exact residue rank.
Kernel reduction proves rank distribution `[1, 15, 100, 300, 304]` and
exactly 90 nonhyperbolic rank-three actions whose every rank-lowering
transvection leaves a hyperbolic rank-two action. The obstruction count
is split into sixteen first-row batches. Audit 117 passed. Exact
minimal lengths and greedy optimality are established below.

`TwoQubitGreedy` proves that four-bit ordered selection and bounded
execution return exactly the general `GreedyDecomposition` output.
Ten fuel always suffices for symplectic frames, with nonzero factors,
exact replay, and length at most nine. Fuel exhaustion is explicit,
not an empty-factor fallback. Audit 118 passed. Execution also compared
all 720 outputs against the general implementation and checked replay.

`TwoQubitMinimality` proves greedy optimality for every two-qubit
symplectic action, against arbitrary-length transvection words.
The 720-entry `TwoQubitDistances` certificate is checked against exact
greedy execution, and all 11,520 transvection neighbors satisfy the
length inequality. Reverse word induction turns this local inequality
into a lower bound for every factorization. Audit 119 passed. The
certificate is verified data, not an assumption about the greedy code.

`TwoQubitClassification` proves exactly 210 nonhyperbolic actions have
minimum length rank plus one, and all 90 rank-three obstructions have
minimum length four. Its shortest-length distribution for lengths zero
through five is `[1, 15, 85, 225, 274, 120]`. Audit 120 passed, including
the rank-count proofs now using direct kernel reduction. Together these
modules close the 720/210/90 counts and two-qubit greedy optimality claims
from #118; higher-qubit counterexamples and growing excess are separate.

`GreedyCounterexample` proves exact nonminimality at three qubits.
In `X0,X1,X2,Z0,Z1,Z2` bit order, centers `[9, 61, 43]` reproduce the
action, whereas the general greedy output is exactly `[22, 52, 34, 31]`.
Audit 121 passed. The proof follows all four actual selection/update
steps; it does not depend on a search oracle.

`GreedyBlocks` constructs arbitrary disjoint copies using Mathlib's
block-diagonal ring homomorphism, matrix reindexing, and single-coordinate
monoid homomorphisms. It proves that `k` copies have an explicit
`3k`-factor decomposition, including `k = 0`. Audit 122 passed.
`GreedyBlockSelection` and `GreedyBlockLength` prove the actual greedy
length is exactly `4k`: selection respects the global ordered basis,
each step advances one unfinished block, and the sum of remaining
local steps decreases by one. Thus greedy exceeds every shortest
decomposition by at least `k`, for arbitrary `k`. Audit 123 passed.
The `3k` competitor is not claimed to be shortest.

`SymplecticPadding` and `GreedyPadding` extend the witness by any number
of identity qubits. For every dimension at least three, the embedded
three-factor word replays the padded action, whereas the actual greedy
algorithm takes four steps. The proof preserves the initial X-generator
prefix, hyperbolicity at fallback, and each update. Audit 124 passed;
execution checks also reproduced the result on three through five qubits.

`HyperbolicMinimality.minimum_spec` proves the remaining general
rank-plus-one claim from #118: every nonidentity hyperbolic action has
exact minimum length `residueRank + 1`. Hyperbolicity makes the residue
form alternating, so no positive-dimensional faithful core can acquire
a unit diagonal by congruence. The existing general upper bound attains
the required extra factor. Audit 125 passed.

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
factorization, and element enumeration are covered below.

`standardization_spec` combines the nine previously blocked standardization
audit targets without changing their proofs or statements. Source-bundle
action-speaks audit **126** passed all checks, replaying 1271 declarations
with only `propext`, `Classical.choice`, and `Quot.sound`. This closes the
old audit blocker; the memory limits and kernel checks were unchanged.
The complete 14-source bundle, with the finite 1,000,000-heartbeat prefix,
has SHA256
`897611e1e20522726804196aaf8c19b3ea58b6e1c1ed200e0ec45d2079552a07`;
all constituent hashes match.

`PauliGroupCardinality.generatedPauliGroup_card` proves the actual
phase-aware subgroup has cardinality `2 ^ standardLog2Size`, including
empty input and zero qubits. Its binary-projective map is surjective
onto the verified projective span; its kernel is equivalent to the
scalar phase subgroup. Mathlib's kernel/index and finite-vector-space
cardinality theorems then give the result. Audit **127** passed all
checks, replaying 1278 declarations with standard axioms only.
The complete 15-source bundle, with the finite 1,000,000-heartbeat prefix,
has SHA256
`8c28224ac0756d229ca9bed14fb6c5033f5e34db2b99903a6adb47503dbd4ee4`;
all constituent hashes match.

`PauliGroupMembership` implements a fixed-width executable membership
and indexed-factorization reference: Binar's verified transpose solver
selects original generators, their ordered phase-aware product determines
the residual scalar, and a computable phase classification accepts it
exactly when allowed. `membership_spec` proves success iff subgroup
membership and exact phase-aware replay of every returned factorization.
It does not certify Rust's sparse-support handling or a false commutation
promise. Exhaustive execution covered all 16 one-qubit targets for six
generator lists (empty, X, duplicate X, scalar i, X/Z, and the full Pauli
group), plus all four zero-qubit scalar targets for empty input.

Audit **128** passed all checks, replaying 1290 declarations with standard
axioms only. The complete 15-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`2538591acbb8e17bd267774f5eee2f686fbb87d7eece7050bfa0c879075cadc5`;
all constituent hashes match.

`PauliGroupDecisions` proves that the executable pairwise generator
commutation check accepts exactly abelian generated subgroups. Its
stabilizer decision accepts exactly abelian subgroups excluding `-I`,
and every member of an accepted group is proved Hermitian. This is the
group-theoretic stabilizer criterion, not a separately verified
common-eigenspace construction. Computed commutation is used, not an
unchecked promise. Execution checked both decisions on the six
one-qubit generator lists above.

Audit **129** passed all checks, replaying 1300 declarations with standard
axioms only. The complete 16-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`7cd546b2cc563e5fe951fccf76eb9d06922467c3ed2bce2f11f6c0eb0d149f08`;
all constituent hashes match.

`PauliGroupEnumeration` computes normalized pivot products, enumerates
their binary subsets, and combines each with the allowed scalar phases.
`enumeration_spec` proves exact subgroup coverage, no duplicates, and
length equal to the actual subgroup cardinality. Empty input and zero
qubits are included. Enumeration order is not asserted to match Rust's
`itertools::powerset` order. Execution checked exact membership and
duplicate freedom for the six one-qubit examples above and the
zero-qubit empty group.

Audit **130** passed all checks, replaying 1663 declarations with standard
axioms only. The complete 29-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`1424d4b3f562d358924afe985c39788664f7c4869793fe7c4a6e82d14d73dfed`;
all constituent hashes match.

`PauliIntersectionCounterexample` proves that independently phase-filtering
the projective basis `XX, ZZ` is incomplete: the groups generated by
`XX, ZZ` and `-XX, -ZZ` share `-YY`, but that filter returns only identity.
Its finite membership predicate is proved equivalent to actual subgroup
membership. The omission was also reproduced in Rust before repair.

The repaired Rust intersection retains the first rejected basis vector and
pairs subsequent rejected vectors with it. `PauliIntersection.pair_rejected`
proves that such pairs always admit a common phase in arbitrary dimension.
Compatibility is exactly membership of the phase difference in the sum of
the two scalar-phase subgroups. The proof covers both sign and imaginary-phase
mismatches. This lemma alone does not establish traversal completeness;
the following modules supply that refinement, still without verifying compiled Rust.
Rust regression tests check the original counterexample, imaginary phases,
three rejected generators, and all 8192 pairs of phase assignments for two
three-generator bases, alongside an exact-set intersection property.

Audits **131–132** passed all checks with standard axioms only. Each complete
16-source bundle has a finite 1,000,000-heartbeat prefix and verified
constituent hashes:

| Audit | Target | Replayed declarations | Bundle SHA256 |
|---|---|---:|---|
| 131 | `PauliIntersectionCounterexample.counterexample` | 1310 | `ed31a3e5fb304e4507d6193af28251208dfaf3b5e40872b69630129a300094cb` |
| 132 | `PauliIntersection.pair_rejected` | 1297 | `90159c754f8d44457d57da792ceb4d47ca621a103a10e2f5a23a5ed0209488f5` |

`PauliIntersectionBasis` adds `PauliIntersection.basis_spec`, closing
mathematical completeness of this basis repair. For any spanning
family of the common projective row space, retain compatible rows and add
one rejected anchor to every rejected row. The corrected rows span exactly
the projective image of the actual subgroup intersection. Any common phase
lifts, together with the common scalar subgroup, generate exactly that
intersection. Both the no-rejection case and the anchored case are covered,
including empty families. Independence and a particular choice of common
phase are unnecessary. The anchor's corrected row is zero and can be
omitted once the scalar subgroup is included.

This is a mathematical construction with an assumed correct projective
spanning family, rather than an execution-refinement proof for the ordered
one-pass Rust loop. Audit **133** verified the combined construction,
replaying 1309 declarations with standard axioms only. Its complete
17-source bundle, with the finite 1,000,000-heartbeat prefix, has SHA256
`0f22e9af37cab4643b2020225c4dc08d42c0fbdf5818d8661135bf69c6aec8ca`;
all constituent hashes match.

`PauliIntersectionSelection` verifies executable ordered common-phase lookup
and rejected-anchor discovery using the packed membership algorithm.
Lookup tries the Rust `xz` phases `0, 1, 2, 3`; it succeeds exactly when a
common representative exists and returns an actual member of both groups
with the requested projective row. Anchor discovery returns a rejected input
or certifies that every input is compatible. `pairedVariant_exists` proves
that lookup cannot fail on the product of two rejected rows drawn from the
common projective space. Execution checked six cases, including the original
counterexample, its repaired product, identical groups, and zero qubits.
The following modules verify traversal and discharge projective-basis extraction.

Audit **134** passed all checks, replaying 1323 declarations with standard
axioms only. Its complete 18-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`2e4c628d347a7f1d5f5ee82f465f6a7f638fc18875861c140d142d0cd9bc2ef4`;
all constituent hashes match.

`PauliIntersectionLoop` adds `PauliIntersection.traversal_spec`, verifying
the ordered one-pass traversal and the actual enumeration of common
scalar generators. The first rejected vector becomes the anchor without
being emitted; later rejected vectors are paired with it. Missing paired
phases are explicit failures in the executable model, proved unreachable
under `ValidBasis`. That precondition requires the supplied rows to span the
common projective space, without requiring independence. The traversal
succeeds, and every returned list generates exactly the subgroup intersection.
Eleven executable cases cover phase selection, both basis orders of the
counterexample, all-compatible inputs, imaginary-phase cancellation, and
zero-qubit scalar groups. Basis extraction is connected below; support
compaction and compiled-code correspondence are not included.

Audits **135–136** reached the triviality probe's heartbeat limit on the
existential formulation, not a failed kernel proof. Audit **137** passed
all checks on the equivalent nonfailure-and-universal-result contract,
with unchanged finite budgets and no disabled checks. It replayed 1352
declarations with standard axioms only. The complete 19-source bundle has SHA256
`019fb0a378c0411752b82c1fab7cee00192b1105a5a6239074cd7a50fe066d84`;
all constituent hashes match.

`IntersectionKernel.kernel_spec` verifies the first extraction prerequisite:
the trailing rows of Binar's echelon transform, from rank to the last row,
are an executable, independent basis of the input matrix's left kernel.
This matches the dependency-row selection in Rust's row-space intersection.
The result includes arbitrary rectangular matrices, empty matrices, and
full row rank. The next modules connect stacking, alpha projection, the
product with the first input, and final pivot extraction to `ValidBasis`.
Audit **138** passed all checks, replaying 1421 declarations with standard
axioms only. Its complete 23-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`d77de84087a411867f4b17200a0f62f0997cbb6c4a117605710ac4b36be14598`;
all constituent hashes match.

`IntersectionExtraction.extraction_spec` proves that stacking the inputs,
projecting the transform's dependency rows onto the first coefficient block,
applying M4RI multiplication, and extracting the final echelon pivot rows
produces an independent basis of the intersection of the two row spaces.
It covers arbitrary rectangular matrices, dependent rows, zero dimensions,
and full rank.

`PauliGroupIntersection` converts those rows to zero-xz-phase Paulis and proves
`projectiveBasis_valid`. Its `PauliIntersection.full_intersection_spec` then
proves that the complete executable fixed-width algorithm cannot fail and
returns generators of exactly the phase-aware subgroup intersection, without
assuming a correct input basis. It does not model Rust's sparse support
discovery, comparison-based early exits, final canonicalization, or compiled
execution.

The initial algorithm passed audit **139**, but its function-backed packed
transpose repeatedly recomputed rows and blocks during execution. Binar's
`PackedMatrix.materialize_eq` proves that storing rows changes no values;
transpose storage now evaluates each output word once, and M4RI materializes
the transposed rows. The existing dimension-general refinement theorems
remain checked. Extraction also materializes its alpha and product rows.
The complete 3130-job project build and all eleven persistent execution
cases pass, including the original phase-cancellation counterexample,
dependent and disjoint inputs, both empty-input orders, zero-qubit scalars,
noncommuting groups, and odd-width rectangular extraction:

```bash
cd paulimer/formal
lake --offline env lean --run tests/Intersection.lean
```

Audit **140** reverified the final materialized implementation with every
check enabled, replaying 1702 declarations with standard axioms only.
Its complete 31-source bundle, with the finite 1,000,000-heartbeat prefix,
has SHA256
`620af9b6a97a1842975a100214dc47700476c321ab65a54e90c64e8ca3408f4d`;
all constituent hashes match. Audit 139 is the earlier, unmaterialized
snapshot, not the receipt for the current source.

`PauliGroupOrder.operations_spec` proves that concatenating generator lists
generates the subgroup supremum and verifies Rust's exact partial-comparison
branches. Phase-count/binary-rank pairs are compared with the joined group's
pair: `Equal` means semantic subgroup equality, `Less` and `Greater` mean
strict inclusion in the corresponding direction, and `None` means neither
group includes the other. The proof uses the actual subgroup cardinality,
not the insufficient assumption that equal ranks alone imply equal groups.

The same contract verifies intersection including the comparison-driven
early returns. Nineteen persistent execution cases now cover both full and
early-exit intersection, all four comparison outcomes, redundant generators,
incomparable equal-rank groups, crossed scalar/binary ranks, and scalar
inclusion caused by a commutator. This does not yet verify Rust's separate
`PartialEq` implementation, which compares canonical generator lists.
Sparse support discovery and compiled execution also remain outside the model.

Audit **141** passed every check, replaying 1734 declarations with standard
axioms only. Its complete 33-source bundle, with the finite
1,000,000-heartbeat prefix, has SHA256
`dde40d34a470417f195934a8dc647a21b15f145e2e5d0caab356d7ec783a2798`;
all constituent hashes match. The full 3131-job project build passed.

The minimality theorem concerns the Clifford's binary symplectic action.
`TransvectionSigns` additionally proves PR #217's final Pauli correction:
equal binary preimages with self-inverse rows become exactly equal signed
tableaux after the phase-mismatch correction, which is positive Hermitian.
`TransvectionImplementation` verifies a typed executable candidate checker,
minimality of accepted bordered candidates after a correct congruence-search
rejection, and the retained fallback's factor order and minimality.

These are conditional refinement contracts, not proofs of the complete Rust
search or Python bindings. Binary replay and Hermiticity are inputs to the
standalone sign theorem; `CliffordTableau.signedDecomposition_spec` now
derives them for the complete semantic construction. Global Clifford
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
action-speaks audits passed (entries 84-87).

`TriangularMemo` proves that certified failure caching and complement
deduplication preserve the exact optional ordered result of the uncached
search. `TriangularKeys` supplies collision-safe flattened Boolean keys using
Binar's verified echelon reduction, including zero ambient width. Its concrete
memoized solver inherits the complete core criterion. Four principal audits
passed (entries 88 and 92-94); the concrete audits use a recorded finite
command budget of 1,000,000 heartbeats, with every audit check enabled.
Shared packing helpers now live in `PackedEncoding` and Binar's `Packed`,
without changed names or algorithms. The correspondence with Rust's separate
key reducer remains an obligation; this is not verification of compiled Rust. See the
[milestone record](../docs/lean-transvection-minimality-proof.md#pr-217-triangularizer-milestone).

`ResidueExtraction` computes the residue basis, rank, retained row transform,
and `V R^T` core using Binar. It proves independence, full residue span,
`R F̂ = V`, and existence of a faithful presentation of the computed core.
The executable rank branch replays its input with a shortest rank-length
factorization, or rejects exactly when the canonical core is not
triangularizable. Action-speaks entries 95-97 verified these results.
Noncomputable witnesses occur only in specifications, not the executable
data. Rust's separate augmented reducer correspondence remains unproved.

`ResidueFixSearch` proves complete exhaustive fix search and implements the
recursive fallback, terminating by whether the rank branch succeeds rather
than by residue rank. Its total solver and checked-candidate variant return
globally shortest factorizations; all returned centers are nonzero.
The combined contract passed action-speaks (entry 99). Concrete SWAP fallback
execution remains unverified within the monitored three-minute interpreter
check; this is separate from its dimension-general kernel proof.

`CliffordFixedSpace` computes Binar's kernel basis of `(I + F)^T` and
reindexes it into positive Hermitian Paulis. The generators are independent,
span exactly `Fix(F)`, and number `2m - residueRank(F)`. The combined theorem
passed action-speaks (entry 100). This is the projective fixed space, not
the exact signed centralizer. After packed-transpose materialization, the
previously blocked execution checks pass for the empty action, one-qubit
identity, X-root, and Z-root. The persistent check verifies dimension,
positive-Hermitian generators, and their fixed-vector equations:
`lake --offline env lean --run tests/FixedSpace.lean`.

`GreedyReduction` proves the two rank transitions underlying PR #118's
greedy loop. For `v = x + xF` with `pairing(x, xF) = 1`, the update `F T_v`
adds exactly one fixed-space dimension and drops residue rank by one. If
every `pairing(x, xF)` is zero, any residue update preserves the fixed space
and rank, and a nonzero residue makes the updated action nonhyperbolic.
The combined contract passed action-speaks (entry 101).

`GreedySearch` proves complete ordered selection, including equivalence to
the singleton loop followed by the lexicographic pair loop and its XOR
cross-pairing test. It returns no vector exactly for identity; every selected
vector has nonzero residue and meets one of the proved reduction conditions.
Audits 102-103 passed. Execution covers the empty case, all six one-qubit
actions, a pair-only choice, and SWAP's hyperbolic fallback.

`GreedyDecomposition` implements the full terminating greedy loop on
vector-backed valid action matrices. Its state conversion preserves the
matrix, and its public equations append each chosen residue after the
recursive result. The output replays the binary action, has between
`residueRank(F)` and `4m + 1` factors, and consists of nonidentity positive
Hermitian Paulis. Audit 104 passed. Full execution covers empty input, all
six one-qubit actions, and three-factor SWAP, including factor phases.
This is not a minimality claim for greedy decomposition or a verification
of signed tableaux or compiled Rust.

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
