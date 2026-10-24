"""Deterministic unsigned synthesis and signed decomposition benchmarks."""

from typing import ClassVar

from paulimer import CliffordUnitary, SparsePauli, UnitaryOpcode


class TransvectionDecomposition:
    params: ClassVar[list[int]] = [1, 2, 4]
    param_names: ClassVar[list[str]] = ["qubit_count"]

    def setup(self, qubit_count):
        self.clifford = CliffordUnitary.identity(qubit_count)
        for qubit in range(qubit_count):
            self.clifford.left_mul(UnitaryOpcode.Hadamard, [qubit])
            self.clifford.left_mul(UnitaryOpcode.SqrtZ, [qubit])
        for qubit in range(qubit_count - 1):
            self.clifford.left_mul(UnitaryOpcode.ControlledX, [qubit, qubit + 1])
        self.clifford.left_mul_pauli(SparsePauli("Y0"))
        factors, correction = self.clifford.to_transvections_minimal()
        rebuilt = CliffordUnitary.identity(qubit_count)
        for pauli in factors:
            rebuilt.left_mul_pauli_exp(pauli)
        rebuilt.left_mul_pauli(correction)
        assert rebuilt == self.clifford

    def time_greedy_unsigned(self, qubit_count):
        self.clifford.to_transvections()

    def time_minimal_with_final_pauli(self, qubit_count):
        self.clifford.to_transvections_minimal()

    def track_minimal_unsigned_rotation_count(self, qubit_count):
        factors, _correction = self.clifford.to_transvections_minimal()
        return len(factors)
