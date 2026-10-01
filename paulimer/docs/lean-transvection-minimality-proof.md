# Lean proof of minimal transvection decomposition

The Lean development in [`../formal/`](../formal/) proves the minimal number of
symplectic transvections needed to represent the binary symplectic action of a
Clifford operation. The result holds in every finite dimension; finite
enumeration is used only for the reference search, not for the mathematical
proof.

The formalization concerns binary symplectic actions. The Rust API's choice of
Hermitian Pauli representatives, Python binding behavior, and performance
optimizations are outside its scope.

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
by reduced-row-echelon keys. Those implementation details are not modeled in
Lean. Conditional on a valid returned $Q$,
`CorePresentation.factorization_of_triangularizer` proves replay of the actual
row formula $QV$; the residue-rank lower bound makes its length $r$ minimal.
Proving that Rust's success and failure results decide the predicate exactly
would require verifying this backtracking and memoization.

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

## Verification boundary

The proof is mathlib-only and uses the pinned Lean and mathlib versions in the
formal project. It contains no admitted theorem or project-defined axiom. The
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

The pins are Lean `4.32.2` and mathlib
`905b95818eb32af7874a58b427f50c1711a5e96c`. On a fresh checkout,
`lake exe cache get` downloads the matching mathlib cache.
