#!/usr/bin/env python3
"""Independent finite-dimensional F2 diagnostic, not a substitute for Lean.

For each total degree d, constructs the matrix of (a,b) -> Xa+Yb on
R(-1)^2, computes its kernel by binary elimination, computes X*K_(d-1)
+ Y*K_(d-1), and reports the dimension of the quotient. No expected
syzygy parametrization is used to construct either subspace.
"""
import json


def eliminate(columns):
    pivots = {}
    relations = []
    for index, column in enumerate(columns):
        value, combination = column, 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (value, combination)
                break
            row, mask = pivots[pivot]
            value ^= row
            combination ^= mask
        else:
            relations.append(combination)
    return len(pivots), relations


def shift_pair(vector, old_width, x_power):
    answer = 0
    new_width = old_width + 1
    for coordinate in range(2):
        for i in range(old_width):
            if vector & (1 << (coordinate * old_width + i)):
                answer ^= 1 << (coordinate * new_width + i + x_power)
    return answer


def apply(columns, vector):
    result = 0
    for i, column in enumerate(columns):
        if vector & (1 << i):
            result ^= column
    return result


def main():
    kernels, results = {}, []
    for degree in range(13):
        width = degree  # dim R_(d-1), including width=0 when d=0
        columns = [1 << (i + 1) for i in range(width)]
        columns += [1 << i for i in range(width)]
        rank, kernel = eliminate(columns)
        kernels[degree] = kernel
        assert all(apply(columns, v) == 0 for v in kernel)
        generators = []
        if degree >= 1:
            for v in kernels[degree - 1]:
                generators.extend(shift_pair(v, degree - 1, dx) for dx in (0, 1))
        assert all(apply(columns, v) == 0 for v in generators)
        product_dimension, _ = eliminate(generators)
        quotient_dimension = len(kernel) - product_dimension
        assert len(kernel) == 2 * width - rank
        assert quotient_dimension == (1 if degree == 2 else 0)
        results.append({
            "degree": degree,
            "presentation_dimension": 2 * width,
            "augmentation_rank": rank,
            "kernel_dimension": len(kernel),
            "maximal_ideal_times_kernel_dimension": product_dimension,
            "quotient_dimension": quotient_dimension,
        })
    print(json.dumps({"status": "PASS", "method": "independent binary matrix elimination",
                      "scope": "degrees 0 through 12 only; not a universal proof",
                      "graded_pieces": results}, indent=2))


if __name__ == "__main__":
    main()
