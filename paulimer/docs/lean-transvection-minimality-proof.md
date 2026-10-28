# Lean proof of minimal transvection decomposition

The Lean development in [`../formal/`](../formal/) proves the minimal number of
symplectic transvections needed to represent the binary symplectic action of a
Clifford operation. The result holds in every finite dimension; finite
enumeration is used only for the reference search, not for the mathematical
proof.

The minimality theorem concerns binary symplectic actions. The
[PR #217 refinement review](#pr-217-refinement-review) also proves the final
signed-preimage correction under explicit binary-replay and Hermiticity
contracts. Python binding behavior and performance optimizations remain
outside the formalization.

## Relationship to the published proof

The reassessment of
[arXiv:2102.11380](https://arxiv.org/abs/2102.11380) separates the paper's
existence theorem from its construction. Theorem 1's product identity,
Theorem 2's treatment of non-hyperbolic involutions, and Theorem 3's conclusion
that every binary symplectic map is a product of transvections are correct.
The gap is the construction inside Theorem 3: it assumes that every
non-hyperbolic map has a residue core that is triangularizable by congruence
and therefore has a length-$r$ factorization.

That implication is false over $F_2$. Callan's class-A exceptions include
non-hyperbolic maps whose minimum is $r+1$. A smallest example acts on two
qubits and is the product

$$
T_{X_0}T_{X_1}T_{X_0X_1}T_{Z_0}.
$$

It has residue rank three and minimum length four. The accompanying Rust
regression checks that minimum against the complete two-qubit breadth-first
search; a separate ignored test exhausts all three-qubit symplectic actions.
Callan identifies these residue-three exceptions in dimension four in Section
2.4 and classifies the binary exceptions in Theorem 5.1.

The notation does not hide a convention mismatch. The paper writes its
faithful residue reduction as

$$
R\widehat F R^T=\operatorname{diag}(E,0),
$$

whereas Lean writes $\widehat F=V^TDV$ and defines its core as $D^{-T}$.
Comparing the two presentations gives $D=E^{-T}$, so Lean's core is exactly
the paper's $E$. Transposing the action convention therefore cannot rescue the
failed implication. Likewise, hyperbolicity is equivalent to the residue
matrix being alternating, meaning symmetric with zero diagonal; zero diagonal
alone is insufficient.

Lean repairs rather than formalizes the incomplete construction. It proves
that length $r$ is equivalent to congruence triangularizability of the full
nonsymmetric core, then supplies the bordered construction proving length
$r+1$ in every remaining case. Lean therefore proves the fallback sufficient.
Callan's class-A examples, confirmed by the Rust two-qubit breadth-first
search rather than by Lean, show that it is needed: replacing it with the
paper's non-hyperbolic criterion would reject valid inputs. This is not a proof
of Rust's backtracking implementation.

## Statement and scope

The phase space for an `m`-qubit action is

$$
V = F_2^{2m},
$$

represented by row vectors whose coordinates are indexed by the `X` and `Z`
halves. The standard symplectic form is the matrix $\Omega$, and the
transvection centered at $v$ is

$$
T_v = I + \Omega v^T v.
$$

For a symplectic action $F$, define its residue matrix, residue space, and
residue rank by

$$
\widehat F = \Omega(I+F), \qquad
\operatorname{Res}(F) = \operatorname{rowspan}(I+F), \qquad
r = \dim\operatorname{Res}(F).
$$

Let $\ell(F)$ be the shortest length of a list of transvections whose ordered
product is $F$. In a faithful residue basis, write

$$
\widehat F = V^T D V
$$

with $D$ invertible, and define the residue core $E=D^{-T}$. Different
faithful residue bases give cores related by congruence, so the
criterion below and the value of $\ell(F)$ do not depend on this choice. Lean
proves

$$
\ell(F) =
\begin{cases}
r, & \text{if some }Q\in\operatorname{GL}(r,F_2)
       \text{ makes }QEQ^T\text{ unit lower triangular},\\
r+1, & \text{otherwise}.
\end{cases}
$$

In the second case it also proves that there is a nonzero
$w\in\operatorname{Res}(F)$ such that $FT_w$ has the same residue rank and a
triangularizable core. Thus one additional residue transvection always reduces
the problem to the length-$r$ case.

The theorem concerns the binary symplectic action. Pauli-image signs and global
Clifford phase are outside this representation and therefore outside the
statement.

## Proof strategy

### 1. Establish the binary symplectic model

`Symplectic.lean` defines $F_2$ as `ZMod 2`, the phase space, the standard
symplectic form, row action, transvections, fixed and residue spaces, and
residue rank. It proves that each transvection is symplectic and involutive and
that the residue matrix determines the action. The implementation-facing
lemmas `residueRank_add_finrank_fixedSpace` and `residueRank_inv` also prove
$r+\dim\operatorname{Fix}(F)=2m$ and $r(F^{-1})=r(F)$.

The central identity extracted from symplecticity is

$$
\widehat F+\widehat F^T
  = \widehat F^T\Omega\widehat F.
$$

This identity later determines the symmetric part of the residue core and is
what connects core congruence to the pairings between transvection centers.

### 2. Express an ordered product as a matrix factorization

`Product.lean` fixes the same order convention as the Rust implementation: a
list `[u, v]` denotes $T_uT_v$, so a row vector encounters $T_u$ first.

For centers $c_0,\ldots,c_{k-1}$, let $C$ be the matrix with those centers as
rows. The file defines an invertible path matrix $B(C)$ that records the
pairings accumulated while the centers are replayed. Induction over the list
proves

$$
\widehat{T_{c_0}\cdots T_{c_{k-1}}}
  = C^T B(C) C.
$$

The rows of $I+T_{c_0}\cdots T_{c_{k-1}}$ lie in the span of the centers.
Consequently,

$$
\operatorname{rank}(I+F)\leq k
$$

for every length-$k$ factorization of $F$. This is the universal lower bound
$r\leq\ell(F)$. When equality holds, the centers are linearly independent and
form a basis of the residue space.

### 3. Reduce the length-$r$ question to the residue core

`Minimality.lean` packages a faithful residue presentation as a residue basis
$V$, an invertible coefficient matrix $D$, and the equality
$\widehat F=V^TDV$. Its core is $E=D^{-T}$.

Suppose first that $F$ has a factorization with exactly $r$ centers. The lower
bound is tight, so those centers are another residue basis and can be written
as $C=QV$ for an invertible change of basis $Q$. Comparing the two
factorizations of $\widehat F$ and cancelling the independent basis gives

$$
D = Q^T B(C)Q.
$$

The path matrix is inverse to a unit upper triangular matrix built directly
from the center pairings. Inverting and transposing the preceding identity
therefore shows that $QEQ^T$ is unit lower triangular.

Conversely, assume $QEQ^T$ is unit lower triangular and set $C=QV$. The
symplectic residue identity determines

$$
QEQ^T+(QEQ^T)^T = C\Omega C^T.
$$

A unit lower triangular matrix is uniquely determined by this sum: its
diagonal is fixed to one and its lower entries are the corresponding
off-diagonal entries of the sum. Hence $QEQ^T$ equals the transpose of the
upper pairing matrix of $C$. Reversing the matrix argument recovers
$D=Q^TB(C)Q$, and the ordered-product formula proves that the transvections
centered at the rows of $C$ multiply to $F$.

The constructive direction is exposed as
`CorePresentation.factorization_of_triangularizer`: its output is specifically
the ordered rows of $QV$, not merely some length-$r$ factorization. Together
the two directions prove
`CorePresentation.exists_factorization_iff_isTriangularizable`.
`CorePresentation.isTriangularizable_iff_canonical` makes the independence of
the chosen faithful residue basis explicit.

### 4. Construct a factorization with at most $r+1$ centers

It remains to prove an upper bound without assuming that the core is
triangularizable. Regard the invertible core $E$ as the nondegenerate bilinear
form

$$
\beta(x,y)=xEy^T
$$

on $F_2^r$. The proof constructs $r+1$ vectors $q_i$ and coefficients $z_i$
such that

$$
L_{ij}=\beta(q_i,q_j)+z_i z_j
$$

is unit lower triangular, while

$$
\sum_i z_iq_i=0,\qquad \sum_i z_i^2=1,
\qquad \operatorname{span}\{q_i\}=F_2^r.
$$

In matrix form these are the conditions in
`IsBorderedTriangularization`. The rank-one border $zz^T$ compensates for
using one more center than the core dimension. `BorderedFactorization.lean`
shows algebraically that these conditions imply the coefficient identity
needed by the ordered-product formula, and therefore produce a factorization
of $F$.

`Bilinear.lean` and `UpperBound.lean` construct the bordered family by strong
induction on $r`.

If $\beta$ is alternating, the proof builds a symplectic simplex: $r+1$
vectors that span the space, sum to zero, and pair to one whenever they are
distinct. A nondegenerate alternating form has even dimension, so the simplex
has odd cardinality and taking every $z_i=1$ also gives
$\sum_i z_i^2=1$. With that choice, $L$ is the identity. The simplex itself
is constructed recursively by splitting off a hyperbolic pair and using its
orthogonal complement.

If $\beta$ is not alternating, choose an anisotropic vector $q$ with
$\beta(q,q)=1$. Its line has a right-orthogonal complement of dimension
$r-1$, and the restricted form remains nondegenerate. Apply the induction
hypothesis in that complement, prepend $q$, and prepend a zero to the relation
coefficients. Orthogonality gives the required zeros above the new diagonal,
and the line together with its complement spans the original space.

The resulting theorem,
`CorePresentation.exists_succ_factorization`, gives a length-$r+1$
factorization for every symplectic action.

### 5. Deduce strict minimality

The lower bound, exact length-$r$ criterion, and universal upper bound leave
only two possibilities.

If the core is triangularizable, the criterion supplies a length-$r$
factorization and the rank bound proves it minimal. If the core is not
triangularizable, the criterion rules out length $r$, while the bordered
construction supplies length $r+1$. The rank bound rules out every shorter
length. This is formalized by
`CorePresentation.exists_minimal_factorization`.

### 6. Derive the one-fix theorem

The bordered construction is strengthened so that its final relation
coefficient is one. The relation then places the final bordered vector in the
span of the first $r$ vectors. Since all $r+1$ vectors span an $r$-dimensional
space, the first $r$ are a basis. After mapping through the faithful residue
basis, this gives a factorization

$$
F=T_{c_0}\cdots T_{c_{r-1}}T_w
$$

whose first $r$ centers are independent.

Multiplying by $T_w$ on the right cancels the last factor because
$T_w^2=I$. The remaining independent $r$ centers show that $FT_w$ still has
residue rank $r$. A length-$r+1$ factorization spans the residue space, so
$w\in\operatorname{Res}(F)$. If $w=0$, the first $r$ factors would already
factorize $F$, contradicting non-triangularizability. Finally, the exact
criterion applied to the remaining length-$r$ factorization shows that the
core of $FT_w$ is triangularizable.

This is `exists_residue_fix_of_not_triangularizable`, the theorem behind the
exhaustive residue-vector fallback in the Rust implementation.

### 7. Verify a reference search

`Algorithm.lean` explicitly enumerates all binary phase vectors and all
fixed-length center families. It first searches length $r$ and, if that fails,
searches length $r+1$. Completeness of the enumeration, the universal upper
bound, and the lower-bound argument prove that the search returns a
factorization, that replay gives the target action, and that no shorter list
can do so.

`minimalDecompositionAtRank?` is executable when supplied a computed rank.
The convenience wrapper `minimalDecomposition?` is noncomputable only because
mathlib's matrix rank is noncomputable. This search is a simple specification,
not a performance implementation of paulimer's row-reduction code. The supplied
rank must equal `residueRank`; the theorem does not certify an arbitrary
caller-supplied rank or require the reference search to choose Rust's list.

## Proof elements by module

| Module | Main proof elements |
|---|---|
| `Symplectic.lean` | Binary phase space, symplectic form and action, transvections, residue matrix/space/rank, rank-nullity and inverse-rank bridges, symplectic residue identities |
| `Product.lean` | Ordered replay, path and pairing matrices, product identity, center-span containment, residue-rank lower bound |
| `Minimality.lean` | Arbitrary faithful residue bases, row-reduced-core bridge, concrete triangularizer output, basis-independent exact length-$r$ criterion |
| `Bilinear.lean` | Nondegenerate alternating forms, orthogonal splitting, recursive symplectic simplices |
| `BorderedFactorization.lean` | Bordered triangularization conditions and conversion of a bordered witness into a factorization |
| `UpperBound.lean` | Recursive bordered construction, $r+1$ upper bound, strict minimality, one-fix theorem |
| `Algorithm.lean` | Complete finite enumeration and the proved reference decomposition search |

The main public theorems are:

- `CorePresentation.exists_factorization_iff_isTriangularizable`
- `CorePresentation.exists_minimal_factorization`
- `exists_residue_fix_of_not_triangularizable`
- `minimalDecomposition_spec`

## Rust contract correspondence

This section records the historical #119 review. The
[PR #217 review below](#pr-217-refinement-review) updates the source snapshot,
bordered acceptance path, and signed return contract.

This correspondence review uses the implementation merged locally at
`94bdf9e`, from #119 head `2d1acf5` containing #118 head `336e2c1`. The links
below identify source-level obligations, not a Lean translation of Rust:
[`transvection.rs`](../src/clifford/transvection.rs),
[`clifford_impl.rs`](../src/clifford/clifford_impl.rs),
[`generic_algos.rs`](../src/clifford/generic_algos.rs), and the
[`Python binding`](../bindings/python/src/py_clifford.rs).

### Input, action, and factor order

The formal input is `SymplecticAction m`, not an arbitrary binary matrix.
Rust requires a valid Clifford as reported by `is_valid`, but neither
decomposition calls that validator. Its checks include both canonical
commutation relations and Hermitian tableau generators; Lean models only the
former. Invalid positive-qubit `CliffordUnitary::zero` tableaux are outside the
contract. Zero qubits and the identity action are included and need no factors.

`action_matrix` obtains **images** of `X₀, …, Xₘ₋₁, Z₀, …, Zₘ₋₁` as rows.
Its first and second column halves correspond to Lean's `Sum.inl` and
`Sum.inr` coordinates. `transvection_matrix` is exactly
$I+\Omega v^Tv$, and `rowAction_transvection` states its action.
In contrast, public `Clifford::symplectic_matrix()` returns **preimages**:
for a valid input it represents $F^{-1}$. Equality tests on those matrices
still test equality of actions; `residueRank_inv` justifies their use for the
independent rank calculation. Substituting the preimage matrix for
`action_matrix` without changing the rest of the algorithm would not be the
same convention.

Left-multiplying the **unitary** by the Pauli exponential updates its
**image row matrix** by right multiplication, $F\mapsto FT_v$. Thus replaying
`[u, v]` on the identity gives $T_uT_v$, as in
`replay_eq_rowAction_product`. The greedy algorithm records reductions
$FT_{v_1}\cdots T_{v_k}=I$ and reverses that list when returning it. The exact
algorithm instead returns the rows of $QV$ directly. Its fallback updates
$G=FT_w$ and returns the recursive list followed by $w$; the product is
$GT_w=F$ by `productTransvections_append` and `transvection_squared`.

### Residue core and complete search

`residue_matrix` swaps the row halves of $I+F$, giving exactly Lean's
$\widehat F=\Omega(I+F)$. `row_reduce_with_transform` pivots only in the
original columns of the augmented matrix $[\widehat F\mid I]$ and keeps its
$r$ nonzero rows. Its intended postconditions are an independent residue basis
$V$, a rectangular $r\times2m$ transform $R$, and $V=R\widehat F$.
`residue_core` computes $E_{\mathrm{Rust}}=VR^T$.

The formal bridge takes those mathematical postconditions as hypotheses:
`exists_residue_coefficient_of_basis` supplies an invertible $D$ for any such
faithful basis, with $\widehat F=V^TDV$.
`CorePresentation.core_eq_of_row_reduction` then proves

$$
E_{\mathrm{Rust}}=VR^T=D^{-T}=E_{\mathrm{Lean}}.
$$

This is not merely agreement up to an unspecified transpose. Cancelling the
independent rows of $V$ in $R\widehat F=V$ gives $RV^TD=I$; transposing
$RV^T=D^{-1}$ gives the stated equality. The row reducer's preservation,
independence, spanning, and rank postconditions remain Rust verification
obligations, not assumptions proved about its machine execution.

`congruence_triangularize` searches for an invertible $Q$ with $QEQ^T$
unit **lower** triangular. Its pivot satisfies $\beta(p,p)=1$, and the
recursive subspace is the **right**-orthogonal complement
$\{y:\beta(p,y)=0\}$, giving zeros above the diagonal. It explores all nonzero
span vectors, deduplicates equal complements, and memoizes failed subspaces
by reduced-row-echelon keys. The [executable Lean model](#pr-217-triangularizer-milestone)
now covers this search and safe pruning using Binar-backed keys; correspondence
with Rust's separate key reducer remains unproved. Conditional on a valid returned $Q$,
`CorePresentation.factorization_of_triangularizer` proves replay of the actual
row formula $QV$; the residue-rank lower bound makes its length $r$ minimal.
Proving that Rust's success and failure results decide the predicate exactly
still requires connecting that implementation to the verified model.

In particular, entering the fallback is justified only if a Rust `Err`
implies that the current core has no triangularizer. With that completeness
obligation, `CorePresentation.core_eq_of_row_reduction` and
`CorePresentation.isTriangularizable_iff_canonical` transfer the failed
computed-core search to the canonical core used by the one-fix theorem. A
false `Err` need not panic: at larger ranks it could find a fix and return a
valid but non-minimal list.

On failure, `find_fix_vector` lazily enumerates all nonzero binary coordinate
combinations of $V$; `SpanVectors` does not limit the rank to a machine-word
bit count. It accepts precisely a nonzero $w$ for which $FT_w$ retains rank
$r$ and its recomputed core triangularizes. The dimension-general
`exists_residue_fix_of_not_triangularizable` gives such a witness.
`CorePresentation.isTriangularizable_iff_canonical` connects the cores of any
faithful computed bases to the canonical ones in that theorem. Therefore an
exhaustive, correct implementation of this predicate succeeds, and its
recursive call reaches the length-$r$ branch, costing just one extra factor.
`CorePresentation.isTriangularizable_of_factorization_length_eq` and
`residueRank_le_length_of_factorization` then show that the resulting
length-$r+1$ list is minimal.
This mathematical existence result is stronger than checking three qubits,
but does **not** establish Rust enumeration completeness or panic-freedom.

### Fixed space, representatives, and runtime

`clifford_centralizer` uses the rows of $I+F$, not $\widehat F$, and calls
`kernel_basis_matrix` on its transpose to obtain the **left** null space.
This matches `fixedSpace` and `mem_fixedSpace_iff`.
`residueRank_add_finrank_fixedSpace` proves its intended dimension
$2m-r$. Whether the returned generators really form an independent basis is
a separate property of the Rust kernel routine.

The projection from a `SparsePauli` to `PhaseVector` forgets its phase and keeps
its `x`/`z` bits. `assign_positive_hermitian_phase` leaves those bits untouched
and assigns the xz exponent `y_weight() % 4`. Since the xyz exponent is the
xz exponent minus the Y weight modulo four, the result has xyz exponent zero,
the positive Hermitian representative. Setting the **xz** exponent to zero
instead would be anti-Hermitian at odd Y weight. The fixes therefore matter
for valid Pauli exponentials and replayed tableaux even though they do not
change the binary action or any factor count. Lean neither represents these
phases nor proves this Rust normalization. Its name `PhaseVector` denotes
binary coordinates, not a Pauli phase.

The minimal API promises the fewest factors for the **binary action**, not a
sign-exact tableau decomposition, a global-phase reconstruction, a unique
list, or a polynomial-time algorithm. Zero centers are allowed in Lean's
general lists, but $T_0=I$ cannot occur in a shortest list: deleting it would
give a shorter factorization. The exact Rust path likewise uses independent
rows of $QV$ and explicitly rejects a zero fix.

The greedy reduction and its release-mode `4m + 2` assertion are not the
reference algorithm and have no termination proof here. The exact Rust path
also retains a panic when no fix is found. Resource exhaustion, integer
sizes, recursion, and the exponential time/memoization costs are outside
the mathematical totality statement. Python's minimal method clones the
input before `py.detach` runs the same Rust search, then wraps the output
Paulis. GIL release, interruption/cancellation behavior, and wrapper execution
have no formal counterpart.

### PR update ledger

| Commit | Effect on the formal contract |
|---|---|
| `3407d77` | Normalizes greedy factors and centralizer generators to positive Hermitian Paulis. Binary vectors are unchanged; the additional representative/valid-tableau promise is tested in Rust/Python, not proved by Lean. |
| `6388dd4` | Changes the greedy termination guard from `debug_assert!` to `assert!`. Release-mode failure behavior changes, not the exact minimum theorem; neither the greedy bound nor invalid-input behavior is formalized. |
| `e2a4b0a` | Corrects greedy-versus-minimal, hyperbolicity, and phase documentation. The existing Lean full-core criterion already agrees; it never used zero diagonal or non-hyperbolicity as a sufficient length-$r$ test. |
| `336e2c1` | Makes rank/fixed-space tests independent of the centralizer's output count and checks Rust generator independence. The new rank-nullity and inverse-rank lemmas expose the intended mathematical correspondence; they do not verify the kernel implementation. |
| `50d8ee7` | Applies Hermitian normalization to the minimal output and clarifies valid inputs, panic, and exponential-search claims. The vector algorithm is unchanged. The weaker implementation-level fix-search wording does not weaken Lean's all-dimensional existence theorem. |
| `8c227d2` | Moves the minimal Rust search onto a cloned input inside `py.detach`. This preserves the intended action-level target; scheduling and GIL behavior remain outside Lean. |
| `2d1acf5` | Adds exhaustive one-/two-/three-qubit action tests and updates explanatory material. This strengthens finite implementation evidence, not the dimension-general proof or its assumptions. |

The merge also brings stricter Hermitian checks in `is_valid_clifford`,
phase/root-Y and parser/permutation fixes, bit-support iteration changes,
and dependency version updates from main. These affect implementation
validity, construction, or execution, but do not change the symplectic input
type, the residue formulas, or the theorem's minimum-length criterion.

The current [`Rust tests`](../tests/transvection_test.rs) compare shortest
lengths against an independent BFS on all 6 one-qubit and 720 two-qubit
actions, and check returned replay, tableau validity, and positive Hermitian
phases. The ignored three-qubit test visits all 1,451,520 actions and checks
minimum lengths and Hermiticity; it does **not** replay each returned
decomposition or check its positive xyz phase. Its census derives rank from
the centralizer length, unlike the independent rank helper in the other
tests. Property tests and [`Python tests`](../bindings/python/tests/transvection_test.py)
add replay, fixed-space, representative, and GIL checks. None of these tests
is a Lean/Rust extraction or refinement proof, and the three-qubit test does
not run in the default suite.

## PR #217 refinement review

Reviewed source: [#217](https://github.com/microsoft/qdk-ec/pull/217), head
[`2ce895eda84473762d7db36bf6c3561460992858`](https://github.com/microsoft/qdk-ec/commit/2ce895eda84473762d7db36bf6c3561460992858),
with reported base `50f3bff4e5923ffad9382d49d3b9d4f522a4b09a`.
The review used an isolated checkout of that exact head, not the older Rust
implementation on this proof branch. It does not cover later PR revisions.

The principal source is
[`transvection_exact.rs`](https://github.com/microsoft/qdk-ec/blob/2ce895eda84473762d7db36bf6c3561460992858/paulimer/src/clifford/transvection_exact.rs).
No mathematical defect was found in its new checked-candidate or final-sign
paths under the contracts below. This is a conditional mathematical
refinement review, **not end-to-end verification of the Rust solver**.

### New checked contracts

| Source path | Lean result | Preconditions and conclusion |
| --- | --- | --- |
| `final_pauli_correction`, lines 125-149 | `TransvectionSigns.finalPauliCorrection_spec` | Equal binary preimage rows and self-inverse rows in both tableaux imply exact equality of every corrected signed row. The correction has zero xyz phase and is self-inverse. |
| `verifies_bordered_decomposition`, lines 633-652 | `TransvectionRefinement.checkCandidate_iff` and `checked_candidate_spec` | The typed Boolean checker accepts exactly nonzero, rank-plus-one lists with correct ordered replay. Given a faithful core and a correct rejection of triangularizability, every accepted list is shortest. |
| `BorderedFamily::validate` and the `QV` lift, starting at lines 514 and 616 | `TransvectionRefinement.bordered_family_spec` | The existing `IsBorderedTriangularization` postconditions imply that the lifted rows replay the target. On the rejected-core branch, their rank-plus-one length is minimal. |
| `verified_decomposition_or_search`, starting at line 654 | `TransvectionRefinement.retained_fallback_spec` | A rank-length factorization of `F T_w`, followed by `w`, replays `F` in the returned order and is shortest on the rejected-core branch. |

The sources are
[`TransvectionSigns.lean`](../formal/PaulimerFormal/TransvectionSigns.lean) and
[`TransvectionImplementation.lean`](../formal/PaulimerFormal/TransvectionImplementation.lean).
They reuse the phase-aware Pauli algebra and the existing residue-core,
bordered-factorization, and minimum-length theorems. No new axiom is introduced.

The candidate checker is executable over fixed-width mathematical vectors.
Its types replace the Rust vector-length checks; it does not model malformed
`Vec<bool>` inputs or prove the packed matrix routines. In particular,
`bordered_family_spec` consumes the validator's algebraic postconditions,
not an assumption that the recursive construction always succeeds.

### Why the sign correction is sufficient

The algorithm compares **preimages** of the standard generators.
Different X-preimage phases set a Z correction bit; different Z-preimage
phases set an X bit. This agrees with `left_mul_pauli`'s support loops and
`clifford_left_mul_eq_x`/`clifford_left_mul_eq_z`: those helpers add two to
the opposite preimage's phase, without changing its binary coordinates.
Testing commutation against the current preimage instead of the standard
generator would implement a different multiplication convention.

For equal binary coordinates, self-inverse Paulis have equal doubled xz
phases. Their phases are therefore either equal or differ by two modulo
four. The exact phase-inequality test selects precisely the rows that need
negation. This includes odd Y weight: the proof does not assume that
Hermitian Paulis have even **xz** phase. Rust's `xz_phase_exponent()` reduces
its raw byte modulo four, and tableau equality also compares phases modulo
four, matching the formal model.

The result holds for any qubit count, including zero, and for any correctly
replayed rotation list, whether constructed or found by the fallback.
It proves equality of the stored signed tableau, not global unitary phase.
The final Pauli is not included in the unsigned minimum rotation count.

### Remaining implementation obligations

The initial congruence search must be sound **and complete**. A false rejection
can allow a valid rank-plus-one candidate even when rank factors suffice;
the final replay check alone cannot establish minimality. The
[Lean search](#uncached-recursive-search-and-core-bridge) now proves
this property, and the [memoized model](#memoization-and-collision-safe-keys)
preserves its exact result.

The other explicit obligations are correspondence of `row_reduce_with_transform`
with the [verified Binar-backed extraction](#executable-residue-extraction);
correspondence of Rust's separate key reducer
with collision-safe keys; and the
connection from valid Rust tableaux and quarter-turn updates to the binary
action. The sign proof assumes equal binary **preimages**, whereas candidate
validation compares **image** action matrices. Transferring between them
requires the valid-tableau inverse-action contract.

The recursive `bordered_family` and `symplectic_simplex` implementations are
not proved to produce valid witnesses on every input. Their checked success
path is covered; failures retain the original search. The dimension-general
Lean residue-fix existence theorem closes the abstract existence question,
but does not by itself prove that Rust's retained search finds that witness
or cannot panic.

`clifford_fixed_space` is the renamed projective fixed-space API. The earlier
rank-nullity theorem still applies. It is not an exact signed centralizer,
and its packed kernel-basis implementation remains a refinement obligation.
Greedy termination, Python/GIL behavior, and runtime/resource bounds are
unchanged exclusions.

### Independent audit

The new modules build with the pinned Lean 4.34.0 project. The principal
targets are audited individually with action-speaks and
`require_nontrivial=true`.

The project-mode signed audit was stopped at the watchdog's private-memory
ceiling without a verdict. The supported **source mode** instead audits the
complete local dependency closure: source bodies are concatenated in import
order with only import lines removed; action-speaks supplies its pinned
Mathlib, Physlib, and Cslib environment. No declarations, hypotheses, or
audit checks are omitted. This is a source-snapshot audit plus a separate
project build, not a successful project-environment replay audit.

| Target | Project ledger entry | Result |
| --- | --- | --- |
| `TransvectionSigns.finalPauliCorrection_spec` | 76 | Verified |
| `TransvectionRefinement.checked_candidate_spec` | 77 | Verified |
| `TransvectionRefinement.bordered_family_spec` | 78 | Verified |
| `TransvectionRefinement.retained_fallback_spec` | 79 | Verified |

Each successful result checks elaboration, kernel replay, audit integrity,
trusted axioms, absence of proof holes, statement integrity, non-vacuity,
and hypothesis use. The axiom set is exactly `propext`, `Classical.choice`,
and `Quot.sound`.

The signed bundle contains `Symplectic`, `Pauli`, and `TransvectionSigns`,
and has SHA256
`f3956bb62936704da5ae409624d165bdcd47856906edd28b864b6b85c483e43e`.
The unsigned bundle contains `Symplectic`, `Bilinear`, `Product`, `Minimality`,
`BorderedFactorization`, `UpperBound`, and `TransvectionImplementation`,
and has SHA256
`5833ebd299e6fbfafdf5f5bcb3b3d4d4f1173f323bfc1869294cea9834ca2d8f`.
Full source snapshots and results are retained in the local project ledger;
per-file hash manifests and watchdog logs are retained with the session
artifacts.

### Implementation checks

On the pinned PR checkout, with Rust 1.96.0, two build jobs, a writable
session-local Cargo cache, and the generated Cargo lockfile:

```bash
cargo test --locked --offline --profile ci-test -p paulimer --all-features \
  --lib transvection_exact -- --test-threads=2
cargo test --locked --offline --profile ci-test -p paulimer --all-features \
  --test transvection_test -- --test-threads=2
```

The focused unit run passed 20 tests; the public integration run passed 25.
Coverage includes malformed candidates, forced fallback, all one-/two-qubit
signed tableaux, the independent minimum-length oracle, and seeded larger
bordered examples. The two exhaustive three-qubit tests remained ignored.
These are implementation regressions, not a replacement for the stated
refinement obligations. Existing Binar PyO3 deprecation warnings were not
changed. Python tests and the full workspace Rust suite were not run.

## PR #217 triangularizer milestone

**Executable Lean milestone complete:** the complement, enumeration, recursive
search, cache/deduplication safety, collision-safe keys, and
core-triangularizability bridge are implemented and independently audited.
This is not a checked translation of Rust's separate reducer or solver.
The source pin remains `2ce895eda84473762d7db36bf6c3561460992858`.

### Complement and alternating guard

[`Triangularization.lean`](../formal/PaulimerFormal/Triangularization.lean)
models the right-orthogonal complement with coupling `y ↦ form pick y`.
It removes the chosen coupling-one row and adds that row to every other
coupling-one row, preserving their order. `exists_coupling_pivot` shows that
a nonisotropic pick in the supplied span guarantees such a row exists.
`complement_spec` proves that independent input gives independent output
spanning exactly the intersection with the coupling kernel, with dimension
decreased by one. It applies to any coupling-one pivot; choosing Rust's
first such row does not require a stronger mathematical assumption.

`alternatingCheck_iff` proves the exact half-matrix check equivalent to
vanishing self-pairing on the entire span. This includes the cross-pair
symmetry comparisons, not just zero diagonal entries. It needs neither
independence nor nondegeneracy nor symmetry of the original form.

### Exact binary enumeration

[`SpanEnumeration.lean`](../formal/PaulimerFormal/SpanEnumeration.lean)
models `SpanVectors::next`, not the older factorization reference search:

- `nextBits` carries from the lowest coefficient index upward, without a
  machine-word dimension bound.
- `advance` performs the same successive vector XORs. `advance_spec`
  proves that a current vector equal to the decoded coefficients remains
  equal to the decoded next coefficients, or returns `none` on overflow.
- `binaryStates` is a finite trace starting at all-false coefficients;
  `CounterTrace` checks every successor transition and the final overflow.
- `spanEnumeration_spec` proves that removing the initial state and decoding
  yields exactly `2^n - 1` distinct vectors, with membership equivalent to
  being nonzero and in the original independent family's span.

Both the carry recursion and the trace construction are structurally
terminating. The results are dimension-general and include empty input.
The checked two-bit example records the order `00, 10, 01, 11`.

The trace is materialized only as a semantic description; it does not model
Rust's lazy allocation behavior. `none` represents terminal exhaustion,
rather than exposing the mutable `exhausted` flag. Fixed-length function
types exclude malformed runtime vector lengths. These are checked executable
Lean models with explicit source correspondence, not a checked translation
of Rust.

### Audit record and next obligations

All four targets passed action-speaks with `require_nontrivial=true`, using
the same complete-source-closure method described above:

| Target in `PaulimerFormal.Triangularization` | Project ledger entry | Result |
| --- | --- | --- |
| `complement_spec` | 80 | Verified |
| `alternatingCheck_iff` | 81 | Verified |
| `advance_spec` | 82 | Verified |
| `spanEnumeration_spec` | 83 | Verified |

Each audit replayed all 161 declarations in the bundle. All applicable
checks passed, no warnings were reported, and the axiom set was exactly
`propext`, `Classical.choice`, and `Quot.sound`. The unchanged dependency
closure contains `Symplectic`, `Bilinear`, `Triangularization`, and
`SpanEnumeration`, with bundle SHA256
`67a632720036595e5849158a0775669348a92abdd93d7520d3fc4f55288aab16`.
The manifests and audit hashes were checked against the current source files.
The full pinned Lean project build passed (3088 jobs). No Rust code changed;
the earlier pinned PR regression results were not rerun for these Lean-only
additions.

### Uncached recursive search and core bridge

[`TriangularSearch.lean`](../formal/PaulimerFormal/TriangularSearch.lean)
implements `search` using the verified span iterator and complement routine.
It accepts empty input before checking the alternating guard, skips
isotropic candidates, selects the first coupling-one pivot with `List.find?`,
and returns the first successful recursive branch with `List.findSome?`.
The basis length decreases at every recursive call; Lean checks structural
termination without a fuel assumption or a partial-function escape.

`IsTriangularBasis` states independence, equality of the spanned subspace,
and a unit lower-triangular Gram matrix in the returned order. The
`triangularBasis_cons` and `triangularBasis_tail` lemmas justify prepending a
nonisotropic pick and restricting a solution to its right-orthogonal tail.
`search_sound` proves this specification for every successful result from
independent input. `search_none_iff` proves complete failure: an existing
triangular basis supplies an enumerated first vector and a valid tail in
the exact computed complement, so neither the guard nor exhaustion can
incorrectly reject it.

`congruenceTriangularize` starts from the standard basis of a square matrix
`E`. `gram_eq_congruence` fixes the orientation as `Q E Q^T`.
`congruenceTriangularize_sound` proves that the returned `Q` is invertible
and its congruence is unit lower triangular.
`congruenceTriangularize_none_iff` characterizes failure for any square `E`,
without requiring invertibility as an input hypothesis.
`core_search_none_iff` specializes this to the existing
`CorePresentation.IsTriangularizable` criterion, discharging the correct
rejection premise for this executable Lean search model.

Kernel-backed examples cover empty input, identity, alternating rejection,
a nonsymmetric zero-diagonal guard, and genuine backtracking. In the last
example, `E = [[1,0,0],[0,0,1],[0,1,0]]`: the first candidate's recursive
branch fails, but the complete search returns rows `110, 101, 111`.
The dimension-general theorems do not depend on these finite examples.

| Target in `PaulimerFormal.Triangularization` | Project ledger entry | Result |
| --- | --- | --- |
| `search_sound` | 84 | Verified |
| `search_none_iff` | 85 | Verified |
| `congruenceTriangularize_sound` | 86 | Verified |
| `core_search_none_iff` | 87 | Verified |

All four action-speaks source-mode audits used `require_nontrivial=true`.
Each replayed all 317 declarations in its complete dependency closure,
with all applicable checks passing, no warnings, and exactly the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. The bundle includes
`Symplectic`, `Bilinear`, `Triangularization`, `SpanEnumeration`, `Product`,
`Minimality`, and `TriangularSearch`; its SHA256 is
`c15353d35e2dbb989f269389076bff1660c4656546562cfc83fd97aa71073a94`.
Source and audit hashes were checked against the current files. The full
Lean project build passed (3089 jobs). No Rust code changed.

### Memoization and collision-safe keys

[`TriangularMemo.lean`](../formal/PaulimerFormal/TriangularMemo.lean) adds a
failure cache and a local set of previously failed complement keys. Equal
keys must imply equal spans, including across different family lengths;
the converse is unnecessary. Cache certificates refer to one fixed bilinear
form and independent input families. `memoSearch_spec` proves exact equality
with the uncached optional ordered result and preservation of cache soundness.
The local key is recorded after recursive failure; Rust records it before
recursion, but successful recursion returns immediately, making the timing
difference unobservable. List-backed sets model membership, not hash-table costs.

[`TriangularKeys.lean`](../formal/PaulimerFormal/TriangularKeys.lean) packs
rows, reuses Binar's echelon reduction, removes zero rows, and flattens their
logical bits. Span preservation and injective flattening at positive width
prove collision safety. At width zero every span is zero, so the empty key
is safe even for different row counts. No canonical-RREF uniqueness theorem
is assumed. `memoizedTriangularize_eq` preserves the exact uncached answer;
`memoized_core_none_iff` transfers the complete rejection criterion.

| Target in `PaulimerFormal.Triangularization` | Project ledger entry | Result |
| --- | --- | --- |
| `memoSearch_spec` | 88 | Verified |
| `subspaceKey_noFalseCollisions` | 92 | Verified |
| `memoizedTriangularize_eq` | 93 | Verified |
| `memoized_core_none_iff` | 94 | Verified |

Every applicable action-speaks check passed with `require_nontrivial=true`
and only `propext`, `Classical.choice`, and `Quot.sound`. The generic audit
replayed 338 declarations, bundle SHA256
`767f64dfc2e38751e64272da7f493851825b87413e06d0db8786587409f24fc6`.
The concrete audits replayed 548 declarations, bundle SHA256
`7e7f8f68993c869cd8bb405481027b8c022598a880af7141b1501e83c3c2ffbe`.
They include the complete local dependency bodies with import lines removed
and a recorded `set_option maxHeartbeats 1000000` prefix. The default
200,000-heartbeat batch failed during the hypothesis-use check, after
successful replay, axiom, shape, and non-vacuity records. No verifier code or
audit check was changed; the finite command budget resolves that failure.

Shared packing definitions were moved, without changing their names or
proofs, into `PackedEncoding` and Binar's `Packed` module. This removes
unrelated Pauli and solver modules from the keys' import closure.
The source hashes match the audited snapshots. Both full project builds
passed (3092 Paulimer jobs; 2468 Binar jobs). Executed checks cover genuine
memoized backtracking, failure-cache reuse, flattened bit order, and zero
width. No Rust code changed.

The separate Rust reducer's byte-for-byte correspondence is not established.
Materialized lists model lazy traversal order, not allocation behavior.
The signed tableau bridge remains a separate work unit.

### Executable residue extraction

[`ResidueExtraction.lean`](../formal/PaulimerFormal/ResidueExtraction.lean)
packs `omega * (I + F)` in the existing X-then-Z index order. It retains Binar's
pivot rows and the matching rows of its accumulated transform. The computed
basis is independent and spans the full residue space, its pivot count equals
the residue rank, and its retained transform satisfies `R F̂ = V`.
`core_spec` supplies a faithful `CorePresentation` whose basis is exactly the
computed basis and whose core is the computed product `V R^T`.
The presentation's existential coefficient is a specification witness only:
the basis, rank, transform, core, and search are all executable.

`rankDecomposition` applies the memoized triangularizer to that computed core
and returns the rows of `Q V`. Every returned list replays the action, has
exactly residue-rank length, and is no longer than any other factorization.
Rejection is equivalent to non-triangularizability of the canonical core.
This connects the executable rank branch to the hypotheses of the
all-dimensional residue-fix existence theorem.

| Target in `PaulimerFormal.ResidueExtraction` | Project ledger entry | Result |
| --- | --- | --- |
| `core_spec` | 95 | Verified |
| `rankDecomposition_some_spec` | 96 | Verified |
| `rankDecomposition_none_iff` | 97 | Verified |

All three source-mode audits replayed 1412 declarations with every applicable
check passing and only the three standard axioms. The complete local-source
bundle, with the same finite 1,000,000-heartbeat prefix, has SHA256
`5144eccf4ecb2ed21a9940b249cb93c4d34934c5d4a36ffbe39d0f102860f773`.
Source hashes match that snapshot. The full Lean project build passed
(3093 jobs). Executed checks cover empty input, all six one-qubit binary
symplectic actions, retained transforms, factor replay, and SWAP's rejection
by the rank branch.

The pinned Rust helper performs elimination on an augmented matrix; the Lean
model reuses Binar's verified transform-producing reduction. Their required
algebraic contract is proved for the executable model, not a byte-for-byte
translation of that separate Rust loop. No Rust source changed.

### Complete executable residue-fix fallback

[`ResidueFixSearch.lean`](../formal/PaulimerFormal/ResidueFixSearch.lean)
enumerates the computed residue basis using the verified little-endian span
iterator. `spanVectors_lift` proves exact equality with enumerating standard
coordinates first and then lifting them, including order. `acceptsFix_iff`
characterizes the actual nonzero, equal-rank, and successful-core checks.
`findFix_sound` proves the returned vector satisfies those conditions;
`findFix_complete` proves a rejected canonical core cannot exhaust the search.

`minimalDecomposition` is executable recursion on valid symplectic actions,
not a noncomputable choice of a factorization. Its termination measure is
zero when the rank branch succeeds and one otherwise.
`fix_enters_rank_branch` proves strict decrease on the sole recursive call,
even though residue rank is preserved. The recursively returned factors are
followed by the fix, in the order required to replay the original action.
The impossible no-fix branch is eliminated by the completeness proof.

`checkedDecomposition` tests the rank branch first, then validates a supplied
candidate, otherwise uses the complete fallback. Its theorem quantifies over
every candidate, including absent, wrong-length, zero-containing, and
incorrect-replay candidates; it does not assume the bordered construction
succeeds. Both solvers replay the input with globally shortest
factorizations. `shortest_nonzero` excludes identity factors from any
shortest factorization, and hence from the checked solver's result.

The combined `PaulimerFormal.ResidueFixSearch.fullSearch_spec` passed
action-speaks as project ledger entry **99**, with
`require_nontrivial=true`, all applicable checks passing, and only the three
standard axioms. Kernel replay checked all 1465 declarations in the complete
source closure. Its snapshot, with the finite 1,000,000-heartbeat prefix, has
SHA256
`8918b11ba2c31998ae041a43c27514bb59a0ac1f7611521edaf30eb563a8b62b`.
The source hashes match the snapshot and the full Lean build passed
(3094 jobs). An earlier source audit rejected an ambiguous unqualified
`rank`; explicit qualification resolved it without changing the claim.

**Runtime boundary:** empty and one-qubit execution cases completed, but a
single literal, kernel-certified SWAP fallback did not finish within a
monitored 180-second Lean-interpreter run. It was stopped with no surviving
children. No successful runtime result is claimed for that fallback or the
remaining candidate regression batch. Those execution/fixture checks remain
outstanding; they do not substitute for or invalidate the independently
replayed dimension-general termination and correctness proofs. Runtime cost,
Rust reducer correspondence, and the signed tableau bridge are not proved by
this milestone.

## PR #118 projective fixed-space extraction

[`CliffordFixedSpace.lean`](../formal/PaulimerFormal/CliffordFixedSpace.lean)
computes `I + F` in X-then-Z order, calls Binar's verified packed transpose
and kernel-basis algorithms, and converts the rows to canonical positive
Hermitian Paulis. The kernel-to-row-action bridge proves these rows span
exactly `Fix(F)`. They are independent and number `2m - residueRank(F)`.
Every returned Pauli has zero xyz phase, is self-inverse, and has fixed
projective coordinates. These claims hold for the matrix kernel independently
of the later valid-tableau interpretation.

`PaulimerFormal.CliffordFixedSpace.fixedSpace_spec` passed action-speaks as
project ledger entry **100**, with all applicable checks passing and only
`propext`, `Classical.choice`, and `Quot.sound`. The complete local-source
snapshot, with the finite 1,000,000-heartbeat prefix, has SHA256
`f0c018d12338cf5d701d5763846921c09bc10eab38d224dd8fb74544ce910526`.
Kernel replay checked 982 declarations, the source hashes match, and the full
project build passed (3095 jobs).

The empty runtime case passed; the nonempty one-qubit identity regression
did not finish within its monitored 120-second interpreter check. Remaining
runtime cases are not reported as passing. The verified packed transpose
model reconstructs output bits through its full tile kernel, so its execution
cost must not be confused with Rust's mutable packed implementation.
No timing bound is proved. Exact signed commutation is deliberately not
claimed: Clifford X projectively fixes Z while conjugating it to -Z.

## PR #118 greedy rank transitions

[`GreedyReduction.lean`](../formal/PaulimerFormal/GreedyReduction.lean)
proves the dimension-general steps for the row-action update `F T_v`, with
`v = x + xF`. When `pairing(x, xF) = 1`, its fixed space is exactly
`Fix(F) + span{x}`, with `x` outside the original fixed space. Therefore
the residue rank drops by exactly one.

The hyperbolic condition is defined explicitly as
`pairing(x, xF) = 0` for every vector `x`, and is proved equivalent to
alternation of the image-pairing bilinear form. In this case every residue
update preserves the fixed space and residue rank. If the residue is
nonzero, symplectic nondegeneracy supplies a vector that pairs to one with
it; polarization shows this vector is self-anticommuting for the updated
action. Thus the update leaves the hyperbolic case.

`PaulimerFormal.GreedyReduction.reduction_spec` passed action-speaks as
project ledger entry **101**, replaying 134 declarations with all applicable
checks passing and only `propext`, `Classical.choice`, and `Quot.sound`.
The full local-source bundle, including the finite 1,000,000-heartbeat
prefix, has SHA256
`931bd3a5e57b1231572ed4d25ea5d14e3c62bd214626e2a78727a325165d7076`.
Its source hashes match the checked files, and the full project build
passed (3096 jobs). These are symbolic step theorems, not execution tests
or a completed proof of Rust's ordered greedy loop.

## PR #118 ordered greedy selection

[`GreedySearch.lean`](../formal/PaulimerFormal/GreedySearch.lean)
enumerates the standard X-then-Z vectors followed by lexicographically
ordered pair sums. It proves equality with the two-stage loop: first search
singletons, then search `first < second` using the cross-pairing sum.
The sum-equals-one predicate is exactly the XOR of the two anticommutation
bits. Full-vector self-pairing reduces to this test after all singleton
tests fail.

Reusing the alternating-span theorem proves that active search fails
exactly for hyperbolic actions. The first moved standard-vector fallback
then makes next-vector selection return `none` exactly for the identity
matrix. Every returned vector has nonzero residue and is either
self-anticommuting or comes from a hyperbolic action. These selection
claims hold even for unchecked matrices; the rank-transition theorems
separately require symplecticity.

Action-speaks verified `selection_spec` and `findActive_eq_ordered_loops`
as entries **102-103**, replaying 582 declarations each with all applicable
checks passing and only the standard three axioms. Their complete local
source bundle, with the finite 1,000,000-heartbeat prefix, has SHA256
`7cda99a016cf7726de3b83cd737337b6e9d92ea18326f6a673994ecc4a065825`.
All source hashes match; the full build passed (3097 jobs). Monitored
execution passed the empty case, all six one-qubit symplectic actions, a
two-qubit pair-only selection, and the SWAP hyperbolic fallback. These are
next-step checks, not complete greedy-loop or minimal SWAP execution checks.

## PR #118 complete greedy model

[`GreedyDecomposition.lean`](../formal/PaulimerFormal/GreedyDecomposition.lean)
connects the verified selection and rank transitions to a terminating
executable loop. The well-founded potential is twice the residue rank plus
one for a hyperbolic action. Active choices lower the rank by one; hyperbolic
choices preserve rank but remove that extra one. Every selected step
strictly decreases the potential.

The public recursion equations return the recursive factors followed by
the current residue, reversing the reduction sequence. Involutivity of each
transvection then proves exact binary replay. The returned positive
Hermitian Paulis have nonzero projective vectors and zero xyz phase.
Their count lies between the residue rank and `4m + 1`, which is stronger
than the implementation's `4m + 2` guard. No greedy minimality theorem is
asserted.

The executable state stores a fixed-size vector of fixed-size row vectors,
together with its symplecticity proof. `action_store` proves that materializing
an action preserves its matrix exactly. The initial function-valued loop
exceeded a monitored 120-second SWAP run; materializing back into a function
also stalled, while retaining explicit vector-backed state completed.
With that representation, full execution passed empty input, all six
one-qubit actions, and three-factor SWAP, checking replay, nonzero factors,
zero xyz phase, self-inversion, and the Y-count xz phase. This does not close
the separate minimal-search SWAP or nonempty fixed-space runtime gaps.

Action-speaks verified `PaulimerFormal.GreedyDecomposition.full_spec` as
entry **104**, replaying 897 declarations with all applicable checks passing
and only `propext`, `Classical.choice`, and `Quot.sound`. The full build
passed (3098 jobs). The complete local-source snapshot, with the finite
1,000,000-heartbeat prefix, has SHA256
`977c2ed2b1d927b27c26356f20f5b871ff4a37b1d0e9fdccf5ebd216c8347239`;
all constituent source hashes match.

The remaining implementation bridge must derive the binary action from a
valid signed tableau and identify physical left Pauli-exponential updates
with these row-action updates. The exact finite counts and greedy optimality
claims for all 720 two-qubit actions remain separate enumeration obligations.
Neither signed replay nor verification of compiled Rust follows from this
milestone.

## Phase-aware Pauli-exponent automorphisms

[`PauliExponent.lean`](../formal/PaulimerFormal/PauliExponent.lean)
proves that the existing branchwise `Pauli.exponentAction` is a
multiplicative bijection for every self-inverse Pauli exponent. The inverse
uses its negative, scalar phases are fixed pointwise, and self-inverse
inputs remain self-inverse. `exponentEquiv` packages the action as a
Mathlib multiplicative equivalence. Its projective action is precisely
`x -> x T_v`, including zero centers and arbitrary input phases.

The proof separates the four commutation cases and uses the canonical
Pauli commutation and conjugation theorems; it does not assume the desired
automorphism law. The Hermitian exponent condition is important: the
non-Hermitian exponent `iX` gives a concrete multiplicativity failure on
`Z * Z`. Monitored execution checked all eight signed Hermitian one-qubit
exponents on all 16 Paulis, including 2048 products, inverse identities,
scalar phases and binary projection, and retained that counterexample.

`PaulimerFormal.Pauli.exponent_spec` passed action-speaks as entry **105**,
replaying 1117 declarations. Every applicable check passed, including
hypothesis-use checking, with only `propext`, `Classical.choice`, and
`Quot.sound`. The complete source snapshot, with the finite
1,000,000-heartbeat prefix, has SHA256
`ae1b74b62810ac49dca03e01248024156c9af785ac70d8537a4876ef3f7f2d82`.
Its constituent hashes match the checked files; the full build passed
(3099 jobs).

This establishes phase-aware algebraic semantics for the update. It does
not yet prove the concrete matrix formula for quarter-turn conjugation or
the valid-tableau extension and image/preimage conventions required by
the remaining signed decomposition bridge.

## Clifford actions and binary projection

[`Clifford.lean`](../formal/PaulimerFormal/Clifford.lean) defines a
`CliffordAction` as a Pauli-group automorphism fixing every scalar phase.
This is a subgroup of Mathlib's `MulAut`, not an assumed binary matrix
decorated with phases. Phase preservation makes its projective action
independent of the chosen Pauli representative. Multiplicativity induces
an F2-linear map; preservation of commutation then proves the extracted
matrix is symplectic.

Signed images and preimages are inverse, their binary actions are the
extracted matrix and its symplectic inverse, and self-inverse rows remain
self-inverse. Automorphism multiplication is function composition.
Consequently row-vector matrices satisfy `F_(A B) = F_B F_A`. The
Pauli-exponent automorphism lifts to this subgroup and has binary action
`T_v`; left composition therefore produces `F T_v`, as used by the
verified greedy reduction.

Action-speaks verified `CliffordAction.projection_spec` and
`CliffordAction.binaryAction_quarterTurn` as entries **106-107**. Each
replayed 1158 declarations with all applicable checks passing and only
`propext`, `Classical.choice`, and `Quot.sound`. Their complete local-source
bundle, with the finite 1,000,000-heartbeat prefix, has SHA256
`63485469edf95059535e7b6af891017e5901e2405b2165ce12a3c082b0aa92d8`.
All constituent hashes match, and the full build passed (3100 jobs).

Execution checked seven actions on all 16 one-qubit Paulis, signed
image/preimage round trips, both binary inverse products, and a
noncommuting composition-order sentinel. It also checked a double
X-quarter-turn whose binary action is identity but which sends Z to -Z.
Thus no argument identifies equal binary actions with equal signed
actions. Valid-tableau extension, runtime layout correspondence, and
concrete unitary realization remain distinct obligations.

## Signed tableau validity

[`CliffordTableau.lean`](../formal/PaulimerFormal/CliffordTableau.lean)
defines positive standard X/Z generators and signed preimage rows. Its
computable `validCheck` accepts exactly self-inverse rows with canonical
pairwise commutation. This is also equivalent to self-inverse rows whose
binary row matrix is symplectic.

`upperValid_iff` proves equivalence with the per-qubit and upper-triangle
conditions inspected in #217's `generic_algos.rs:89-112` at
`2ce895eda84473762d7db36bf6c3561460992858`: Hermitian X/Z rows, an
anticommuting pair at each qubit, and commuting XX/XZ/ZX/ZZ pairs between
distinct qubits. Symmetry and vanishing self-pairings recover the omitted
half and diagonal. This proves the mathematical acceptance criterion,
not Rust control flow, memory safety, or trait implementations.

Every phase-preserving Pauli automorphism yields a valid preimage tableau,
and `preimageMatrix_preimages` identifies its matrix with the inverse
binary action. Constructing an automorphism from arbitrary valid rows,
proving its uniqueness, and discharging the signed decomposition bridge
remain subsequent obligations.

Action-speaks verified `CliffordTableau.tableau_spec` and
`CliffordTableau.preimages_spec` as entries **108-109**. Each replayed
1196 declarations with all applicable checks passing and only `propext`,
`Classical.choice`, and `Quot.sound`. The complete local-source bundle,
including the finite 1,000,000-heartbeat prefix, has SHA256
`3f0c4a8883cb16b91501feaffadb7d00ca1ff7838f0bda2d7a21bd6f23514ab1`.
Every constituent hash matches the audited source; the full build passed
(3101 jobs).

Five kernel-checked examples cover empty and standard tableaux, negative
Hermitian rows, zero rows, and non-Hermitian rows. Bounded execution also
compared the full checker with a literal ordered-loop reference on all
256 one-qubit row pairs, accepting 24, and checked a two-qubit identity,
cross-pair rejection, and three signed action-generated tableaux with
their inverse matrices. This execution count is not a separate Lean
enumeration-completeness theorem.

## Verification boundary

The unsigned minimality proof uses Mathlib; the signed refinement imports the
existing Pauli model, which also has Physlib bridges. Both use the pinned
formal-project dependencies. There is no admitted theorem or project-defined axiom. The
main declarations depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.

The Lean model proves the mathematical result for the symplectic action and a
complete reference search. The optimized Rust implementation is not extracted
from Lean. The matrix bridges above prove consequences of explicit algebraic
invariants; source inspection and regression tests, not Lean, connect the Rust
operations to those invariants. In particular, the one-fix existence theorem
must not be reported as a proof that compiled Rust/Python always terminates
without panic.

To check the formal development:

```bash
cd paulimer/formal
lake build
```

The pins are Lean `4.34.0` and mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. On a fresh checkout,
`lake exe cache get` downloads the matching mathlib cache.
