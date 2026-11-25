"""Pure-stdlib exact-Q Koszul complex, max-degree filtration, and Multicolor Permutation Wordle
arithmetic engine for Paper 31 (Lawren Smithline, arXiv:2611.33113, Nov 24, 2026).

ZERO floating-point arithmetic anywhere.
Author: Lluis Eriksson
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

Monom = Tuple[int, ...]
MPolyQ = Dict[Monom, Fraction]


def fmt_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


# =============================================================================
# 1. Exact Multivariate Polynomials Q[x_1, ..., x_N] & Generators Q(k, N)
# =============================================================================

def mp_add(a: MPolyQ, b: MPolyQ) -> MPolyQ:
    out = dict(a)
    for m, c in b.items():
        nv = out.get(m, Fraction(0)) + c
        if nv == 0:
            out.pop(m, None)
        else:
            out[m] = nv
    return out


def mp_mul(a: MPolyQ, b: MPolyQ) -> MPolyQ:
    out: MPolyQ = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(e1 + e2 for e1, e2 in zip(m1, m2))
            nv = out.get(m, Fraction(0)) + c1 * c2
            if nv == 0:
                out.pop(m, None)
            else:
                out[m] = nv
    return out


def mp_scale(c: Fraction, a: MPolyQ) -> MPolyQ:
    if c == 0:
        return {}
    return {m: c * v for m, v in a.items()}


def build_generator_Q(N: int, sk: int, ck: Fraction) -> MPolyQ:
    """Q(k, N) = prod_{i=0}^{N-1} (x_i^{s_k} - c_k) in Q[x_0, ..., x_{N-1}]."""
    p: MPolyQ = {tuple([0] * N): Fraction(1)}
    for i in range(N):
        e_hi = [0] * N
        e_hi[i] = sk
        e_lo = [0] * N
        fac: MPolyQ = {tuple(e_hi): Fraction(1), tuple(e_lo): -ck}
        p = mp_mul(p, fac)
    return p


# =============================================================================
# 2. Exact Filtered Koszul Complex K(N, M, b) Over Q (Definitions 2.4-2.10)
# =============================================================================

def is_gap_free(b: Sequence[int]) -> bool:
    """A multidegree b in Z^N is gap-free iff its distinct coordinates form consecutive integers."""
    uniq = sorted(set(b))
    return all(uniq[i + 1] == uniq[i] + 1 for i in range(len(uniq) - 1))


def filtered_basis_Fhb(
    N: int, M: int, s_vec: Sequence[int], b: Sequence[int], h: int
) -> List[Tuple[Tuple[int, ...], Monom]]:
    """Return exact ordered basis of F_h^b(N, M) as list of (subset_T, monom_exp).
    Each basis element is x^monom * e(T) with |T| = h and monom[j] + sum_{k in T} s_k <= b[j]."""
    basis: List[Tuple[Tuple[int, ...], Monom]] = []
    for T in itertools.combinations(range(M), h):
        deg_T = sum(s_vec[k] for k in T)
        caps = [b[j] - deg_T for j in range(N)]
        if any(c < 0 for c in caps):
            continue
        for mon in itertools.product(*(range(c + 1) for c in caps)):
            basis.append((T, mon))
    return basis


def koszul_differential_matrix_q(
    N: int, M: int, s_vec: Sequence[int], c_vec: Sequence[Fraction], b: Sequence[int], h: int
) -> Tuple[List[List[Fraction]], int, int]:
    """Build exact matrix of delta_h : F_h^b(N, M) -> F_{h-1}^b(N, M) over Q.
    Returns (matrix rows x cols, rows=dim F_{h-1}^b, cols=dim F_h^b)."""
    dom = filtered_basis_Fhb(N, M, s_vec, b, h)
    cod = filtered_basis_Fhb(N, M, s_vec, b, h - 1)
    cod_idx = {item: idx for idx, item in enumerate(cod)}
    Qs = [build_generator_Q(N, s_vec[k], c_vec[k]) for k in range(M)]
    rows = len(cod)
    cols = len(dom)
    mat = [[Fraction(0)] * cols for _ in range(rows)]

    for col_j, (T, mon) in enumerate(dom):
        for pos, k in enumerate(T):
            sign = Fraction(-1 if (pos % 2 == 1) else 1)
            T_minus = T[:pos] + T[pos + 1 :]
            for q_mon, q_coeff in Qs[k].items():
                out_mon = tuple(m1 + m2 for m1, m2 in zip(mon, q_mon))
                row_i = cod_idx[(T_minus, out_mon)]
                mat[row_i][col_j] += sign * q_coeff
    return mat, rows, cols


def exact_rank_q(mat: List[List[Fraction]]) -> int:
    """Exact matrix rank over Q via Gaussian elimination (zero floats)."""
    if not mat or not mat[0]:
        return 0
    rows = len(mat)
    cols = len(mat[0])
    A = [row[:] for row in mat]
    rank = 0
    for c in range(cols):
        piv = None
        for r in range(rank, rows):
            if A[r][c] != 0:
                piv = r
                break
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        pv = A[rank][c]
        for j in range(c, cols):
            A[rank][j] /= pv
        for r in range(rows):
            if r != rank and A[r][c] != 0:
                fac = A[r][c]
                for j in range(c, cols):
                    A[r][j] -= fac * A[rank][j]
        rank += 1
        if rank == rows:
            break
    return rank


def matmul_is_zero_q(A: List[List[Fraction]], B: List[List[Fraction]]) -> bool:
    """Verify A @ B == 0 identically over exact Q."""
    if not A or not B or not B[0]:
        return True
    rows_a = len(A)
    inner = len(A[0])
    cols_b = len(B[0])
    for i in range(rows_a):
        row_a = A[i]
        for j in range(cols_b):
            s = Fraction(0)
            for k in range(inner):
                if row_a[k] != 0 and B[k][j] != 0:
                    s += row_a[k] * B[k][j]
            if s != 0:
                return False
    return True


def alternating_koszul_dim(N: int, M: int, s_vec: Sequence[int], b: Sequence[int]) -> int:
    """Exact alternating Euler characteristic sum_{T subset [M]} (-1)^|T| prod_{j=1}^N max(0, b_j + 1 - deg T)."""
    total = 0
    for h in range(M + 1):
        sign = -1 if (h % 2 == 1) else 1
        for T in itertools.combinations(range(M), h):
            deg_T = sum(s_vec[k] for k in T)
            prod = 1
            for j in range(N):
                fac = b[j] + 1 - deg_T
                if fac <= 0:
                    prod = 0
                    break
                prod *= fac
            total += sign * prod
    return total


# =============================================================================
# 3. Eulerian Polynomials & Multicolor Permutation Wordle Generating Function
# =============================================================================

def eulerian_poly_z(n: int) -> List[int]:
    """Exact Eulerian polynomial A_n(u) = sum_{r=0}^{n-1} A(n, r) u^r."""
    if n == 0:
        return [1]
    prev = [1]
    for m in range(2, n + 1):
        cur = [0] * m
        for r in range(m):
            a = (r + 1) * (prev[r] if r < len(prev) else 0)
            b = (m - r) * (prev[r - 1] if r > 0 else 0)
            cur[r] = a + b
        prev = cur
    return prev


def poly_mul_z(a: Sequence[int], b: Sequence[int]) -> List[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def multicolor_wordle_gf_z(s_vec: Sequence[int]) -> List[int]:
    """Theorem 6.1 generating function W_s(u) = A_n(u) * prod_{k=1}^n (1 + u + ... + u^{s_k - 1})."""
    n = len(s_vec)
    p = eulerian_poly_z(n)
    for sk in s_vec:
        p = poly_mul_z(p, [1] * sk)
    return p


def rational_zero_set_VJn(s_vec: Sequence[int], v_vec: Sequence[Fraction]) -> List[Tuple[Fraction, ...]]:
    """Exact rational zero set V(J_n) subset Q^n when every s_k in {1, 2} (so x^{s_k} - v_k^{s_k} splits over Q!).
    Contains exactly n! * prod(s_k) distinct points."""
    n = len(s_vec)
    roots_by_k: List[List[Fraction]] = []
    for sk, vk in zip(s_vec, v_vec):
        if sk == 1:
            roots_by_k.append([vk])
        elif sk == 2:
            roots_by_k.append([vk, -vk])
        else:
            raise ValueError("Rational zero set requires s_k in {1, 2}")
    pts: List[Tuple[Fraction, ...]] = []
    for perm in itertools.permutations(range(n)):
        for chosen in itertools.product(*(roots_by_k[k] for k in perm)):
            pts.append(chosen)
    return pts
