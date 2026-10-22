# Correctness of the modeled `binar` algorithms

## Claim and trust boundary

**Top-level claim.** The executable Lean models of the included packed `binar`
algorithms refine Mathlib vectors and matrices over
$\mathbb F_2=\mathrm{ZMod}(2)$. Each cited theorem is checked by the Lean kernel:
after decoding packed inputs and outputs, the modeled operation has exactly its
stated mathematical meaning.

This is not an automatic Rust-to-Lean translation, nor a kernel-checked theorem
about compiled Rust. The correspondence between each Rust routine and its
executable Lean model is established by source review. In particular, the proof
does not establish allocation, raw-pointer, aliasing, alignment, FFI,
serialization, panic, or performance safety. Those concerns, and the validity of
arbitrary externally constructed padding bits, remain outside the semantic model.
All modeled algorithms are ordinary executable definitions over `BitVec`, lists,
and finite matrices; the formal development contains no `noncomputable`
declarations.

## Packed representation and decoding

Write $\beta:\{\mathsf{false},\mathsf{true}\}\to\mathbb F_2$ for
$\beta(\mathsf{false})=0$ and $\beta(\mathsf{true})=1$. A Rust `Word` has
$64$ bits, a `BitBlock` has eight words, and hence one block has $512$ bits.
For a logical length $n$, define

$$
\operatorname{blocks}(n)=
\left\lfloor\frac n{512}\right\rfloor+
\begin{cases}
0,&n\bmod 512=0,\\
1,&n\bmod 512\ne0,
\end{cases}
\qquad
C(n)=512\,\operatorname{blocks}(n).
$$

These are Lean's `blockCount` and `capacity`; `le_capacity` proves
$n\le C(n)$. They correspond to Rust's `Word`,
`BIT_BLOCK_WORD_COUNT`, and `BitBlock` in
`binar/src/bit/bitblock.rs`, and `block_count` plus
`AlignedBitVec::{zeros,capacity}` in `binar/src/vec/aligned_vec.rs`.
At packed offset $i=512q+64a+r$, block $q$, word $a\in\{0,\ldots,7\}$,
and least-significant-bit index $r\in\{0,\ldots,63\}$ determine the stored
bit; this is the indexing implemented by `BitwiseViaStd::index`,
`BitwiseForSlice::index`, and `BitAccessor` in the corresponding Rust bitwise
modules.

A Lean `PackedVec n` contains a `BitVec (C n)` and the invariant that every
stored bit with index at least $n$ is zero. Its decoding is

$$
\llbracket v\rrbracket_i=\beta(v_i),\qquad i\in\{0,\ldots,n-1\}.
$$

A `PackedMatrix m n` is $m$ independently padded rows, and

$$
\llbracket M\rrbracket_{ij}=\llbracket M.\mathrm{rows}_i\rrbracket_j.
$$

These are exactly `PackedVec.decode` and `PackedMatrix.decode` in
`binar/formal/BinarFormal/Packed.lean`. On the Rust side, `BitVec` records the
logical length while `AlignedBitVec` owns the rounded storage
(`binar/src/vec/bitvec.rs` and `binar/src/vec/aligned_vec.rs`);
`AlignedBitMatrix::rowstride_of` and `column_count` provide the analogous
per-row distinction in `binar/src/matrix/aligned_bitmatrix.rs`.

Henceforth all vector and matrix arithmetic is over $\mathbb F_2$.
For a matrix $X$, $X^{\mathsf T}$ denotes transpose,
$I_d$ the $d\times d$ identity, $\operatorname{rank}(X)$ Mathlib's matrix
rank, $\ker(X)$ the kernel of its matrix-vector map, and $|p|$ the length of
a pivot list $p$. Equality of decodings is also equality of packed logical
values: `PackedVec.ext_of_decode` proves injectivity of vector decoding.

## Kernel-checked lemma chain

### 1. Packed bit algebra

Reading after an in-range write returns the written bit and every other bit is
unchanged (`PackedVec.get_set_self`, `PackedVec.get_set_ne`); therefore setting
decodes to functional update (`PackedVec.decode_set`). Boolean XOR and AND
become addition and multiplication in $\mathbb F_2$
(`Bool.toF2_xor`, `Bool.toF2_and`), so packed XOR decodes to vector addition
(`PackedVec.decode_xor`). Zero padding removes all rounded-capacity terms:
packed parity is the sum of decoded coordinates
(`PackedVec.parity_eq_sum_decode`), and parity of packed AND is Mathlib's dot
product (`PackedVec.dot_eq_dotProduct`). Row XOR likewise decodes to row
addition (`PackedMatrix.decode_xorRow`). These results cover
`Bitwise::{index,parity}`, `BitwiseMut::assign_index`,
`BitwisePair::dot`, and `BitwisePairMut::bitxor_assign` in
`binar/src/bit/bitwise.rs`, as implemented through
`bitwise_via_std.rs`, `bitwise_for_slice.rs`, and
`bitwise_truncated.rs`.

This is the base refinement layer for every later proof. In particular, the
parity and dot-product theorems quantify only over the $n$ logical
coordinates even though the executable operation scans whole words and
blocks: the proofs explicitly show that every term from $n$ through $C(n)-1$
is zero. Matrix row operations therefore inherit ordinary addition in
$\mathbb F_2$ without exposing block boundaries.

### 2. Transpose kernels and tiled transpose

For a $64\times64$ tile, the six mask-and-swap stages satisfy

$$
\operatorname{transpose64x64}(X)_{ij}=X_{ji},
$$

by `Transpose.swapBlocks_getLsbD` and
`Transpose.transpose64x64_getLsbD`, corresponding to
`swap_blocks_64` and `transpose_64x64_inplace` in
`binar/src/matrix/transpose_kernel.rs`. For the M4RI extraction kernel,
`Transpose.transpose8x64_getLsbD` proves that output bit
$8j+r$ of output word $b$ is input bit $8b+j$ of input row $r$; thus each
output byte is exactly one $8$-bit column pattern. This corresponds to
`delta_swap` and `transpose_8x64` in the same Rust file.

The proof of the $64\times64$ result is compositional rather than a
truth-table assertion: `Transpose.swapBlocks_getLsbD` identifies the source
coordinate of one mask stage, and the six source-coordinate maps are proved
to compose to $(i,j)\mapsto(j,i)$. Likewise, the three delta swaps of the
$8\times8$ lane kernel are reduced to an explicit coordinate permutation
before `Transpose.transpose8x64_getLsbD` connects that permutation to the
packed bytes.

`Transpose.readTile_getLsbD` then connects tiles to packed rows, including
partial tiles by zero extension. `PackedMatrix.transpose_get` proves
entrywise swapping, and `PackedMatrix.decode_transpose` concludes

$$
\llbracket M.\operatorname{transpose}\rrbracket
=\llbracket M\rrbracket^{\mathsf T}
$$

for every shape, including zero dimensions and partial final tiles. The
corresponding Rust routine is `AlignedBitMatrix::transposed` and its
`read_64x64_tile*`/`write_64x64_tile*` helpers in
`binar/src/matrix/aligned_bitmatrix.rs`.

### 3. M4RI multiplication

Let $\operatorname{bit}_i(x)$ denote the $i$th least-significant binary digit
of $x$. For rows $r_0,\ldots,r_{b-1}$ and a $b$-bit pattern $x$, the
completed Gray table entry decodes to

$$
\sum_{i=0}^{b-1}\beta(\operatorname{bit}_i(x))\,
\llbracket r_i\rrbracket .
$$

The one-bit Gray transition is proved by
`M4RI.grayCode_succ_diff_eq_two_pow_changedBit`; the construction invariant
and completed-table result are `M4RI.tableStep_grayCode` and
`M4RI.decode_grayTable`. They correspond to
`RowStripeTable::populate` in `binar/src/matrix/m4ri.rs`.
`M4RI.extractPattern_testBit` proves that every extracted pattern bit is the
requested entry of the left matrix, matching `StripeColumnExtractor`.
`M4RI.decode_stripeFold` proves that XOR-folding bounded chunks equals the
partial $\mathbb F_2$ dot product, and `M4RI.decode_innerStripe` instantiates
that fact for the eight-bit tables. Finally,
`PackedMatrix.decode_m4riMul` proves, for an $m\times k$ packed matrix $L$
and a $k\times n$ packed matrix $R$,

$$
\llbracket L.\operatorname{m4riMul}(R)\rrbracket
=\llbracket L\rrbracket\llbracket R\rrbracket .
$$

This corresponds to `multiply_stripes` and `mul` in
`binar/src/matrix/m4ri.rs`.
Composing this theorem with transpose gives
`PackedMatrix.decode_mulTranspose`, namely
$\llbracket L.\operatorname{mulTranspose}(Q)\rrbracket
=\llbracket L\rrbracket\llbracket Q\rrbracket^{\mathsf T}$, corresponding to
`AlignedBitMatrix::mul_transpose` and `BitMatrix::mul_transpose` in
`binar/src/matrix/aligned_bitmatrix.rs` and
`binar/src/matrix/bitmatrix.rs`.

`M4RI.decode_grayTable` proves all table indices, not only those seen
at a particular Gray-code step: `M4RI.grayCode_invGray` supplies a preimage,
and `M4RI.tableStep_decode_stable` proves later writes do not alter an
existing entry. `M4RI.extractPattern_testBit` then identifies the lookup
index bit-for-bit, while `M4RI.decode_stripeFold` partitions the complete
inner dimension into disjoint consecutive windows. Thus no algebraic term is
lost at an eight-bit or $32$-bit boundary, including a short final stripe.

Two control-flow differences are deliberate extensional correspondences.
Rust caches each `transpose_8x64` result for $64$ consecutive output rows,
whereas Lean's `extractPattern` recomputes the same pure value. Rust also has separate inner-
and super-stripe loops, whereas Lean reuses one `stripeFold` with chunk sizes
$8$ and $32$. Reuse versus recomputation and the unified folds do not change
the pure lookup values or accumulated XOR result. The Lean results are kernel-checked by
`M4RI.extractPattern_testBit` and `M4RI.decode_stripeFold`; their equivalence
to the Rust caching and loop organization is reviewed source correspondence,
not a theorem extracted from Rust.

### 4. Pivots, reduction, RREF, and rank

Let $A=\llbracket M\rrbracket$, let
`S = EchelonForm.new M`, and define
$R=\llbracket S.\mathrm{matrix}\rrbracket$,
$T=\llbracket S.\mathrm{transform}\rrbracket$, and
$U=\llbracket S.\mathrm{transformInvT}\rrbracket$.
At the algorithm's distinct-row call sites, decoded row swaps and row XORs
are invertible elementary row operations
(`Echelon.decode_swapRows`,
`Echelon.decode_xorRow_eq_transvection_mul`). The maintained invariant
`EchelonForm.new_invariant` yields

$$
TA=R,\qquad TU^{\mathsf T}=I_m
$$

through `EchelonForm.new_transform_mul_eq` and
`EchelonForm.new_transform_mul_inv`. The pivot columns are strictly
increasing and in range, each pivot column is a unit column at its pivot row,
and every later row is zero (`EchelonForm.new_isRREF`). Thus the result
satisfies the formalization's RREF contract; canonical uniqueness is not
needed. Invertibility of the row operations gives equality of row spaces
(`EchelonForm.new_rowSpace_eq`), while
`EchelonForm.new_pivots_length_eq_rank` proves

$$
|S.\mathrm{pivots}|=\operatorname{rank}(A),
$$

where $\operatorname{rank}$ is Mathlib's matrix rank.
`PackedMatrix.rank_eq_decode_rank` gives the transform-free public statement.
The corresponding Rust symbols are `pivot_of`, `reduce_with_transforms`,
`xor_if_column_with_transforms`, `EchelonForm::new`,
`AlignedBitMatrix::echelonize`, and `AlignedBitMatrix::rank` in
`binar/src/matrix/aligned_bitmatrix.rs`, wrapped by the same public operations
in `binar/src/matrix/bitmatrix.rs`.

The invariant is strong enough to justify both the algorithm and the rank
statement. `Echelon.pivotOf_success` certifies every accepted pivot bit, while
`Echelon.pivotOf_lt_zero` certifies the skipped columns on the remaining
rows. `Echelon.applyPivot_invariant` shows that swapping the chosen row into
position and reducing every other row preserves $TA=R$ and
$TU^{\mathsf T}=I_m$, preserves all old unit pivot columns, and creates one
new unit pivot column. At termination,
`EchelonForm.new_rows_zero` proves all rows after the pivots are zero.
For rank, the pivot columns restrict the first $|p|$ rows to an identity
submatrix, proving independence, while the zero trailing rows prove those
rows span the row space; `EchelonForm.new_pivots_length_eq_rank` combines
these bounds with row-space preservation.

There is one further reviewed source correspondence. Rust's transform-free
`reduce()` begins XOR at the pivot's $512$-bit block
(`ReductionData::for_pivot`), while Lean's transform-free result projects the
full-row reducer of `EchelonForm.new`. At the moment a pivot is selected, all
earlier blocks of its pivot row are zero; XORs skipped by Rust therefore add
only zero blocks and cannot affect the output. This is a reviewed
source-to-model correspondence, not a kernel theorem about Rust.

### 5. Solving and transpose-solving

`PackedMatrix.decode_mulVec` and `PackedMatrix.decode_rightMultiply` connect
Rust's matrix-vector product and `AlignedBitMatrix::right_multiply` to
Mathlib's column and row products. For $b=\llbracket\mathrm{target}\rrbracket$,
`EchelonForm.solve_eq_some_iff` proves that Rust-modeled `solve` returns
`some x` exactly when

$$
A\llbracket x\rrbracket=b
$$

and every non-pivot coordinate of $x$ is zero. Thus the returned solution is
the canonical solution with all free variables zero, not merely an arbitrary
solution. `EchelonForm.solve_eq_none_iff` proves that `none` is returned
exactly when no solution exists. These correspond to
`solve_rref_system` and `EchelonForm::solve` in
`binar/src/matrix/aligned_bitmatrix.rs`.

The checked loop invariant behind this statement is
`Solve.solveRrefFold_spec`: processed pivot rows have zero residual, each
solution pivot coordinate equals the corresponding transformed target bit,
and every non-pivot coordinate remains zero. The RREF unit-column property
makes a cancellation affect exactly its intended pivot row. Consequently the
final residual is zero precisely when rows of the RREF-level target with index
at least $|p|$ vanish. `Solve.solveRrefSystem_eq_some_iff` gives the RREF-level
soundness/completeness and free-zero characterization, while
`Solve.solveRrefSystem_eq_none_iff` strengthens failure of the canonical
construction to nonexistence of any solution. The transform identities lift
both results to the original matrix in `EchelonForm.solve_eq_some_iff` and
`EchelonForm.solve_eq_none_iff`.

For the transpose system, `Solve.transposeSolveRrefSystem_eq_some_iff` proves
that the RREF-level solution $y$ satisfies
$R^{\mathsf T}\llbracket y\rrbracket=b$ and has
$y_r=0$ for every $r\ge |S.\mathrm{pivots}|$.
`EchelonForm.transposeSolve_eq_some_iff` proves that the public result $x$
satisfies $A^{\mathsf T}\llbracket x\rrbracket=b$ and is exactly
`S.transform.rightMultiply(y)` for such a canonical $y$; equivalently,

$$
\llbracket x\rrbracket_j=\sum_i \llbracket y\rrbracket_iT_{ij}.
$$

`Solve.transposeSolveRrefSystem_eq_none_iff` and
`EchelonForm.transposeSolve_eq_none_iff` prove `none` exactly when the
respective RREF and original transpose systems are unsatisfiable. These correspond to
`transpose_solve_rref_system` and `EchelonForm::transpose_solve` in the same
Rust file.

On the transpose side, `Solve.transposeSolveRrefFold_spec` maintains the
decoded equation “residual plus $R^{\mathsf T}$ times the partial solution
equals the target.” `Solve.transposeMulVec_apply_pivot` shows that evaluation
at pivot column $p_k$ reads exactly coefficient $y_k$, and
`Solve.transpose_mulVec_eq_of_agree_lt` shows coefficients after $|p|$ cannot
matter because the corresponding RREF rows are zero. These facts establish
both the canonical tail-zero result and completeness with respect to
arbitrary solutions.

### 6. Kernel, inverse, and affine maps

For an $m\times n$ packed matrix $M$, set $A=\llbracket M\rrbracket$ and
$K=\llbracket M.\operatorname{kernelBasis}\rrbracket$. The rows of $K$ are
indexed by the non-pivot columns. Every row belongs to
$\ker(A)$ (`Solve.kernelBasis_mem_ker`), the rows are linearly independent
(`Solve.kernelBasis_linearIndependent`), and their span is exactly
$\ker(A)$ (`Solve.kernelBasis_span_eq_ker`). Moreover,
`Solve.finrank_ker_mulVecLin_eq_freeColumns_length` and
`Solve.kernelBasis_rows_length_eq` prove that the row count is the nullity
$n-\operatorname{rank}(A)$, while
`Solve.decode_mul_kernelBasis_decode_transpose_eq_zero` gives

$$
AK^{\mathsf T}=0.
$$

These theorems correspond to `kernel_basis_matrix`, `complement`, and public
`BitMatrix::kernel` in `binar/src/matrix/aligned_bitmatrix.rs` and
`binar/src/matrix/bitmatrix.rs`.

The basis proof follows the executable row construction. For each free column
$c$, `Solve.get_kernelVec_self` sets coordinate $c$ to one,
`Solve.get_kernelVec_pivot` copies the required RREF coefficients into pivot
coordinates, and `Solve.get_kernelVec_free_ne` makes every other free
coordinate zero. The driving coordinates therefore isolate coefficients in
any linear relation, proving independence. Membership plus the matching
rank-nullity dimension then upgrades containment of spans to equality in
`Solve.kernelBasis_span_eq_ker`.

If $M$ is $n\times n$ and has packed rank $n$, let
$X=\llbracket M.\operatorname{inverted}\rrbracket$ denote Lean's modeled
inverse, namely the accumulated transform. `Solve.inverted_mul_left` and
`Solve.inverted_mul_right` prove both

$$
XA=I_n,
\qquad
AX=I_n.
$$

This corresponds to `AlignedBitMatrix::inverted` and `BitMatrix::inverted`;
the Rust full-rank assertion is represented in Lean by an explicit hypothesis.
The intermediate theorem `Solve.echelonized_eq_one_of_full_rank` proves that
an $n\times n$ RREF with $n$ pivots is $I_n$; substituting this into
$TA=R$ gives the left inverse, and square-matrix invertibility gives the right
inverse.

Finally, let the inner affine map be $g(x)=Cx+d$ and the outer map be
$f(y)=Ay+b$. `AffineMap.decode_apply` proves packed application computes its
decoded affine function. Rust's `outer.dot(inner)` has the orientation
$f\circ g$, and its fields are

$$
AC,\qquad Ad+b,
$$

so $(f\circ g)(x)=A(Cx+d)+b$.
`AffineMap.decode_compose` proves this formula, and
`AffineMap.apply_compose` proves equality of the executable packed
applications. The corresponding Rust symbols are `AffineMap::apply` and
`AffineMap::dot` in `binar/src/affine_map.rs`.

## Covered-behavior theorem

**Theorem.** Under the reviewed Rust-to-model correspondence and the stated
trust boundary, decoding commutes with packed set/XOR/parity/dot, transpose,
matrix-vector products, M4RI multiplication, solving, kernel construction,
full-rank inversion, and affine composition; echelonization returns an RREF
$R=TA$ with $TU^{\mathsf T}=I$, preserves row space, and reports Mathlib rank;
ordinary solve returns the canonical nonpivot-zero solution, transpose solve
returns the transform of its canonical tail-zero RREF solution, and either
returns `none` exactly on unsatisfiable systems; kernel rows form a basis with
$AK^{\mathsf T}=0$; and a full-rank square inverse is two-sided. These clauses
are precisely the refinement theorems cited above.
