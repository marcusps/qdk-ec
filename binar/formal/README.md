# `binar` formal verification

Lean 4 proofs that executable models of `binar`'s packed GF(2) algorithms
refine Mathlib matrices over `ZMod 2`.

The proof covers packed bit operations, transpose kernels, M4RI
multiplication, reduced row echelon form and transforms, linear-system
solving, rank, kernel, inverse, and affine composition. It does not verify Rust
allocation, alignment, raw-pointer aliasing, serialization, FFI, or automatic
translation from the Rust source.

## Correspondence

`decode` is the refinement boundary: packed vectors decode to `Fin n -> ZMod 2`
and packed matrices decode to `Matrix (Fin m) (Fin n) (ZMod 2)`.

| Rust implementation | Executable Lean model | Refinement theorem |
|---|---|---|
| `BitBlock`, `AlignedBitVec`, bit access/XOR | `PackedVec`, `get`, `set`, `xor` | `PackedVec.decode_set`, `PackedVec.decode_xor` |
| `Bitwise::parity`, `BitwisePair::dot` | `PackedVec.parity`, `PackedVec.dot` | `PackedVec.parity_eq_sum_decode`, `PackedVec.dot_eq_dotProduct` |
| `transpose_64x64_inplace` | `Transpose.transpose64x64` | `Transpose.transpose64x64_getLsbD` |
| `transpose_8x64` | `Transpose.transpose8x64` | `Transpose.transpose8x64_getLsbD` |
| `AlignedBitMatrix::transposed` | `PackedMatrix.transpose` | `PackedMatrix.decode_transpose` |
| `m4ri::RowStripeTable::populate` | `M4RI.grayTable` | `M4RI.decode_grayTable` |
| `m4ri::StripeColumnExtractor` | `M4RI.extractPattern` | `M4RI.extractPattern_testBit` |
| `m4ri::mul` | `PackedMatrix.m4riMul` | `PackedMatrix.decode_m4riMul` |
| `pivot_of`, reduction, `EchelonForm::new` | `Echelon.pivotOf`, `reduceWithTransforms`, `EchelonForm.new` | `EchelonForm.new_transform_mul_eq`, `EchelonForm.new_transform_mul_inv`, `EchelonForm.new_isRREF` |
| `echelonize`, `rank` | `Echelon.echelonize`, `PackedMatrix.rank` | `Echelon.echelonize_rowSpace_eq`, `PackedMatrix.rank_eq_decode_rank` |
| matrix-vector and row-vector products | `PackedMatrix.mulVec`, `rightMultiply` | `PackedMatrix.decode_mulVec`, `PackedMatrix.decode_rightMultiply` |
| `solve_rref_system`, `EchelonForm::solve` | `Solve.solveRrefSystem`, `EchelonForm.solve` | `Solve.solveRrefSystem_eq_some_iff`, `EchelonForm.solve_eq_some_iff`, `EchelonForm.solve_eq_none_iff` |
| `transpose_solve_rref_system`, `transpose_solve` | `Solve.transposeSolveRrefSystem`, `EchelonForm.transposeSolve` | `Solve.transposeSolveRrefSystem_eq_some_iff`, `EchelonForm.transposeSolve_eq_some_iff`, `EchelonForm.transposeSolve_eq_none_iff` |
| `kernel_basis_matrix` | `PackedMatrix.kernelBasis` | `Solve.kernelBasis_linearIndependent`, `Solve.kernelBasis_span_eq_ker`, `Solve.decode_mul_kernelBasis_decode_transpose_eq_zero` |
| `inverted` | `PackedMatrix.inverted` | `Solve.inverted_mul_left`, `Solve.inverted_mul_right` |
| `mul_transpose` | `PackedMatrix.mulTranspose` | `PackedMatrix.decode_mulTranspose` |
| `AffineMap::apply`, `AffineMap::dot` | `AffineMap.apply`, `AffineMap.compose` | `AffineMap.decode_apply`, `AffineMap.decode_compose`, `AffineMap.apply_compose` |

The table is a reviewed source-to-model correspondence, not a theorem that
extracts Lean from Rust. Random constructors, sparse `IndexSet`, serialization,
parsing/formatting, resizing, direct sums/general row stacking,
`tiny_matrix`, full-rank-basis completion, Python bindings, panic behavior, and
performance bounds are outside the current scope.

Row-space intersection is verified downstream in
[`PaulimerFormal.IntersectionExtraction`](../../paulimer/formal/PaulimerFormal/IntersectionExtraction.lean),
reusing Binar's transform, M4RI, and echelon theorems. Its extracted rows are
independent and span exactly the intersection, including rectangular and empty
inputs. Binar's row materialization is proved equal to the original matrix;
transpose blocks and M4RI's transposed rows are evaluated once rather than
recomputed on every bit access. Paulimer audit 140 replays these dependencies
as part of the complete phase-aware intersection proof.

Local builds use the repository-local Lean installation:

```bash
repo_root="$(git rev-parse --show-toplevel)"
export ELAN_HOME="$repo_root/.lean-local/elan"
export MATHLIB_CACHE_DIR="$repo_root/.lean-local/cache/mathlib"
cd "$repo_root/binar/formal"
"$HOME/.local/bin/lake" exe cache get
"$HOME/.local/bin/lake" build
```
