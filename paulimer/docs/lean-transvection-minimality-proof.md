# Lean proof of minimal transvection decomposition

The Lean development in [`../formal/`](../formal/) proves the minimal number of
symplectic transvections needed to represent the binary symplectic action of a
Clifford operation. The result holds in every finite dimension; finite
enumeration is used only for the reference search, not for the mathematical
proof.

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
search. Callan identifies these residue-three exceptions in dimension four in
Section 2.4 and classifies the binary exceptions in Theorem 5.1.

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
$r+1$ in every remaining case. This also proves that paulimer's complete
triangularizer search and residue-fix fallback are necessary; replacing them
with the paper's non-hyperbolic branch would reject valid inputs. A separate
Claude Opus 4.8 adversarial review independently reached the same assessment:
the proof step has a real gap, the existence conclusion remains true, and no
action convention removes the class-A counterexample.

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

with $D$ invertible, and define the residue core $E=D^{-T}$. Lean proves

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
that the residue matrix determines the action.

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

This proves
`CorePresentation.exists_factorization_iff_isTriangularizable`.

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
distinct. Taking every $z_i=1$ makes $L$ the identity. The simplex itself is
constructed recursively by splitting off a hyperbolic pair and using its
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
not a performance implementation of paulimer's row-reduction code.

## Proof elements by module

| Module | Main proof elements |
|---|---|
| `Symplectic.lean` | Binary phase space, symplectic form and action, transvections, residue matrix/space/rank, symplectic residue identities |
| `Product.lean` | Ordered replay, path and pairing matrices, product identity, center-span containment, residue-rank lower bound |
| `Minimality.lean` | Faithful core presentations, canonical residue basis, core identities, exact length-$r$ criterion |
| `Bilinear.lean` | Nondegenerate alternating forms, orthogonal splitting, recursive symplectic simplices |
| `BorderedFactorization.lean` | Bordered triangularization conditions and conversion of a bordered witness into a factorization |
| `UpperBound.lean` | Recursive bordered construction, $r+1$ upper bound, strict minimality, one-fix theorem |
| `Algorithm.lean` | Complete finite enumeration and the proved reference decomposition search |

The main public theorems are:

- `CorePresentation.exists_factorization_iff_isTriangularizable`
- `CorePresentation.exists_minimal_factorization`
- `exists_residue_fix_of_not_triangularizable`
- `minimalDecomposition_spec`

## Verification boundary

The proof is mathlib-only and uses the pinned Lean and mathlib versions in the
formal project. It contains no admitted theorem or project-defined axiom. The
main declarations depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms.

The Lean model proves the mathematical result for the symplectic action and a
complete reference search. The optimized Rust implementation is not extracted
from Lean; its matrix representation and replay convention are connected to
the model by matching definitions and regression tests.

To check the formal development:

```bash
cd paulimer/formal
lake exe cache get
lake build
```
