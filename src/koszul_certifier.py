"""Pure-stdlib zero-float verifier for KOSZUL-WORDLE-CERT-1.0 certificates.
Supports four exact-Q verification modes aligned with Lawren Smithline
(arXiv:2611.33113, Nov 24, 2026) "The Max-Degree Filtration, Koszul Complexes,
and Dimension Counts for Multicolor Permutation Wordle":
  1. koszul_filtered_exactness_exact   (Thm 5.1: exact Q matrices delta_h, delta^2=0, exactness at every h>=1, Euler char match)
  2. multicolor_wordle_dim_count_exact (Thm 6.1 & Conj 4.5: alternating Koszul sum == cumulative A_n(u)*prod(1+..+u^{s_k-1}))
  3. gap_free_strictness_failure_exact (App A Remark A.1: non-gap-free Z in J cap R_N(b) with dual witness w^T delta_1=0, w^T Z!=0)
  4. zero_set_eval_rank_exact          (Sec 6.1: exact rational evaluation matrix rank of R_n(d) on V(J_n) == quotient dimension)

Author: Lluis Eriksson
"""
from __future__ import annotations

import itertools
import math
import re
from fractions import Fraction
from typing import Any, Dict, List, Tuple

from src.koszul_exact import (
    MPolyQ,
    alternating_koszul_dim,
    build_generator_Q,
    exact_rank_q,
    filtered_basis_Fhb,
    is_gap_free,
    koszul_differential_matrix_q,
    matmul_is_zero_q,
    mp_add,
    mp_mul,
    multicolor_wordle_gf_z,
    rational_zero_set_VJn,
)

SCHEMA_VERSION = "KOSZUL-WORDLE-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A-?[1-9][0-9]*/[1-9][0-9]*\Z")


class KoszulWordleCertificateError(ValueError):
    """Raised whenever any KOSZUL-WORDLE-CERT-1.0 verification check fails."""


def _assert_strict_json_types(obj: Any, path: str = "root") -> None:
    t = type(obj)
    if t is int or t is str or obj is None:
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise KoszulWordleCertificateError(f"Non-str dict key at {path}: {type(k).__name__}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    raise KoszulWordleCertificateError(f"Forbidden type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise KoszulWordleCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        return Fraction(val, 1)
    if type(val) is str:
        if _CANON_INT_RE.match(val):
            return Fraction(int(val), 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if den < 2:
                raise KoszulWordleCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise KoszulWordleCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise KoszulWordleCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise KoszulWordleCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_mpoly(raw: Any, N: int, name: str) -> MPolyQ:
    if type(raw) is not list or len(raw) > 256:
        raise KoszulWordleCertificateError(f"{name} must be list of [exp_list, coeff] pairs")
    out: MPolyQ = {}
    for i, item in enumerate(raw):
        if type(item) is not list or len(item) != 2:
            raise KoszulWordleCertificateError(f"{name}[{i}] must be [exp_list, coeff]")
        exp_raw, c_raw = item
        if type(exp_raw) is not list or len(exp_raw) != N:
            raise KoszulWordleCertificateError(f"{name}[{i}].exp must have length {N}")
        mon = tuple(_parse_int(e, f"{name}[{i}].exp[{j}]") for j, e in enumerate(exp_raw))
        if any(e < 0 for e in mon):
            raise KoszulWordleCertificateError(f"{name}[{i}] has negative exponent")
        c = _parse_rat(c_raw, f"{name}[{i}].coeff")
        if c == 0 or mon in out:
            raise KoszulWordleCertificateError(f"{name}[{i}] zero coeff or duplicate monomial")
        out[mon] = c
    return out


def _verify_mode1_koszul_exactness(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "N", "M", "s_vec", "v_vec", "multidegree_b",
        "claimed_grade_dims", "claimed_diff_ranks", "claimed_quotient_dim",
    }
    if set(cert.keys()) != req:
        raise KoszulWordleCertificateError(f"Mode 1 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    N = _parse_int(cert["N"], "N")
    M = _parse_int(cert["M"], "M")
    if not (1 <= M <= N <= 4):
        raise KoszulWordleCertificateError("Require 1 <= M <= N <= 4")
    s_raw = cert["s_vec"]
    v_raw = cert["v_vec"]
    b_raw = cert["multidegree_b"]
    if type(s_raw) is not list or len(s_raw) != M or type(v_raw) is not list or len(v_raw) != M or type(b_raw) is not list or len(b_raw) != N:
        raise KoszulWordleCertificateError("s_vec, v_vec, or multidegree_b length mismatch")
    s_vec = [_parse_int(v, f"s[{i}]") for i, v in enumerate(s_raw)]
    v_vec = [_parse_rat(v, f"v[{i}]") for i, v in enumerate(v_raw)]
    b = [_parse_int(v, f"b[{i}]") for i, v in enumerate(b_raw)]
    if any(s < 1 or s > 4 for s in s_vec):
        raise KoszulWordleCertificateError("s_vec entries must lie in [1, 4]")
    if any(v <= 0 for v in v_vec) or len(set(v_vec)) != M:
        raise KoszulWordleCertificateError("v_vec must be M distinct positive rationals")
    if not is_gap_free(b):
        raise KoszulWordleCertificateError(f"multidegree_b={b} is NOT gap-free (Theorem 5.1 hypothesis)")

    c_vec = [v_vec[k] ** s_vec[k] for k in range(M)]
    grade_dims = [len(filtered_basis_Fhb(N, M, s_vec, b, h)) for h in range(M + 1)]
    if max(grade_dims) > 256:
        raise KoszulWordleCertificateError("Filtered Koszul grade dimension exceeds audit cap 256")

    mats: List[List[List[Fraction]]] = []
    ranks: List[int] = []
    for h in range(1, M + 1):
        mat, _, _ = koszul_differential_matrix_q(N, M, s_vec, c_vec, b, h)
        mats.append(mat)
        ranks.append(exact_rank_q(mat))

    # 1. Verify chain complex identity delta_h o delta_{h+1} == 0 for all h >= 1
    for idx in range(len(mats) - 1):
        if not matmul_is_zero_q(mats[idx], mats[idx + 1]):
            raise KoszulWordleCertificateError(f"Chain complex identity delta_{idx+1} o delta_{idx+2} != 0")

    # 2. Verify exactness at EVERY grade h >= 1: rank(delta_h) + rank(delta_{h+1}) == dim F_h^b
    for h in range(1, M + 1):
        r_out = ranks[h - 1]
        r_in = ranks[h] if h < M else 0
        if r_out + r_in != grade_dims[h]:
            raise KoszulWordleCertificateError(
                f"Koszul complex NOT exact at grade {h}: rank_out={r_out} + rank_in={r_in} != dim={grade_dims[h]}"
            )

    quot_dim = grade_dims[0] - ranks[0]
    alt_dim = alternating_koszul_dim(N, M, s_vec, b)
    if quot_dim != alt_dim:
        raise KoszulWordleCertificateError(f"Quotient dim {quot_dim} != alternating Euler char {alt_dim}")

    cgd_raw = cert["claimed_grade_dims"]
    cdr_raw = cert["claimed_diff_ranks"]
    if type(cgd_raw) is not list or [_parse_int(v, "gd") for v in cgd_raw] != grade_dims:
        raise KoszulWordleCertificateError(f"claimed_grade_dims mismatch: exact={grade_dims}")
    if type(cdr_raw) is not list or [_parse_int(v, "dr") for v in cdr_raw] != ranks:
        raise KoszulWordleCertificateError(f"claimed_diff_ranks mismatch: exact={ranks}")
    if _parse_int(cert["claimed_quotient_dim"], "claimed_quotient_dim") != quot_dim:
        raise KoszulWordleCertificateError(f"claimed_quotient_dim mismatch: exact={quot_dim}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "N": N,
        "M": M,
        "b": b,
        "grade_dims": grade_dims,
        "quotient_dim": quot_dim,
    }


def _verify_mode2_multicolor_dim(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "s_vec", "max_d",
        "claimed_gf_coeffs", "claimed_cumul_dims",
        "claimed_sat_deg", "claimed_total_colored_perms",
    }
    if set(cert.keys()) != req:
        raise KoszulWordleCertificateError(f"Mode 2 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    s_raw = cert["s_vec"]
    if type(s_raw) is not list or not (1 <= len(s_raw) <= 6):
        raise KoszulWordleCertificateError("s_vec must have length in [1, 6]")
    s_vec = [_parse_int(v, f"s[{i}]") for i, v in enumerate(s_raw)]
    if any(s < 1 or s > 8 for s in s_vec):
        raise KoszulWordleCertificateError("s_vec entries must lie in [1, 8]")
    n = len(s_vec)
    sat_deg = sum(s_vec) - 1
    max_d = _parse_int(cert["max_d"], "max_d")
    if max_d < sat_deg or max_d > sat_deg + 4:
        raise KoszulWordleCertificateError(f"Require sat_deg={sat_deg} <= max_d <= sat_deg+4")

    gf = multicolor_wordle_gf_z(s_vec)
    total_perms = math.factorial(n)
    for sk in s_vec:
        total_perms *= sk
    if sum(gf) != total_perms or len(gf) - 1 != sat_deg:
        raise KoszulWordleCertificateError("Internal Theorem 6.1 GF degree/value check failed")

    # Cross-check EVERY d in 0..max_d: alternating Koszul sum == cumulative GF sum!
    cumul = []
    running = 0
    for d in range(max_d + 1):
        if d < len(gf):
            running += gf[d]
        alt = alternating_koszul_dim(n, n, s_vec, [d] * n)
        if alt != running:
            raise KoszulWordleCertificateError(f"Theorem 6.1 mismatch at d={d}: alt={alt} != cumul={running}")
        cumul.append(alt)

    cgf_raw = cert["claimed_gf_coeffs"]
    ccd_raw = cert["claimed_cumul_dims"]
    if type(cgf_raw) is not list or [_parse_int(v, "gf") for v in cgf_raw] != gf:
        raise KoszulWordleCertificateError(f"claimed_gf_coeffs mismatch: exact={gf}")
    if type(ccd_raw) is not list or [_parse_int(v, "cd") for v in ccd_raw] != cumul:
        raise KoszulWordleCertificateError(f"claimed_cumul_dims mismatch: exact={cumul}")
    if _parse_int(cert["claimed_sat_deg"], "claimed_sat_deg") != sat_deg:
        raise KoszulWordleCertificateError(f"claimed_sat_deg mismatch: exact={sat_deg}")
    if _parse_int(cert["claimed_total_colored_perms"], "claimed_total_colored_perms") != total_perms:
        raise KoszulWordleCertificateError(f"claimed_total_colored_perms mismatch: exact={total_perms}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "s_vec": s_vec,
        "sat_deg": sat_deg,
        "total_colored_perms": total_perms,
    }


def _verify_mode3_strictness_failure(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "N", "M", "s_vec", "v_vec", "multidegree_b",
        "ideal_multipliers_A", "witness_Z", "dual_functional_w",
    }
    if set(cert.keys()) != req:
        raise KoszulWordleCertificateError(f"Mode 3 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    N = _parse_int(cert["N"], "N")
    M = _parse_int(cert["M"], "M")
    if not (2 <= M <= N <= 3):
        raise KoszulWordleCertificateError("Require 2 <= M <= N <= 3")
    s_raw, v_raw, b_raw = cert["s_vec"], cert["v_vec"], cert["multidegree_b"]
    if type(s_raw) is not list or len(s_raw) != M or type(v_raw) is not list or len(v_raw) != M or type(b_raw) is not list or len(b_raw) != N:
        raise KoszulWordleCertificateError("s_vec, v_vec, or multidegree_b length mismatch")
    s_vec = [_parse_int(v, f"s[{i}]") for i, v in enumerate(s_raw)]
    v_vec = [_parse_rat(v, f"v[{i}]") for i, v in enumerate(v_raw)]
    b = [_parse_int(v, f"b[{i}]") for i, v in enumerate(b_raw)]
    if any(s < 1 or s > 3 for s in s_vec) or any(v <= 0 for v in v_vec) or len(set(v_vec)) != M:
        raise KoszulWordleCertificateError("Invalid s_vec or v_vec")
    if is_gap_free(b):
        raise KoszulWordleCertificateError(f"multidegree_b={b} IS gap-free; counterexample requires a non-gap-free multidegree!")

    c_vec = [v_vec[k] ** s_vec[k] for k in range(M)]
    Qs = [build_generator_Q(N, s_vec[k], c_vec[k]) for k in range(M)]

    A_raw = cert["ideal_multipliers_A"]
    if type(A_raw) is not list or len(A_raw) != M:
        raise KoszulWordleCertificateError("ideal_multipliers_A must have length M")
    Z_from_ideal: MPolyQ = {}
    for k in range(M):
        Ak = _parse_mpoly(A_raw[k], N, f"A[{k}]")
        Z_from_ideal = mp_add(Z_from_ideal, mp_mul(Ak, Qs[k]))
    Z_claimed = _parse_mpoly(cert["witness_Z"], N, "witness_Z")
    if not Z_claimed or Z_from_ideal != Z_claimed:
        raise KoszulWordleCertificateError("witness_Z must be non-zero and equal sum_k A_k * Q_k")

    # Verify Z lies in R_N(b) (every monomial exponent <= b)
    for mon in Z_claimed:
        if any(mon[j] > b[j] for j in range(N)):
            raise KoszulWordleCertificateError(f"witness_Z monomial {mon} exceeds multidegree_b={b}")

    # Build delta_1 : F_1^b(N, M) -> F_0^b(N, M) = R_N(b) and verify Farkas dual functional w:
    #   w^T delta_1 == 0  AND  w^T Z != 0  ==>  Z NOT in im(delta_1)  ==>  Strictness S(N, M, b) FAILS!
    basis0 = filtered_basis_Fhb(N, M, s_vec, b, 0)
    idx0 = {mon: i for i, (_, mon) in enumerate(basis0)}
    mat1, rows, cols = koszul_differential_matrix_q(N, M, s_vec, c_vec, b, 1)
    w_raw = cert["dual_functional_w"]
    if type(w_raw) is not list or len(w_raw) != rows:
        raise KoszulWordleCertificateError(f"dual_functional_w must have length {rows}")
    w = [_parse_rat(v, f"w[{i}]") for i, v in enumerate(w_raw)]

    for col_j in range(cols):
        dot = sum(w[i] * mat1[i][col_j] for i in range(rows))
        if dot != 0:
            raise KoszulWordleCertificateError(f"Dual functional fails w^T delta_1 == 0 at col {col_j}: {dot}")

    w_dot_Z = sum(w[idx0[mon]] * coeff for mon, coeff in Z_claimed.items())
    if w_dot_Z == 0:
        raise KoszulWordleCertificateError("Dual functional fails w^T Z != 0")

    return {
        "verified": True,
        "mode": cert["mode"],
        "N": N,
        "M": M,
        "b": b,
        "dim_R_b": rows,
        "dim_F1_b": cols,
        "w_dot_Z": str(w_dot_Z),
    }


def _verify_mode4_zero_set_eval_rank(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "s_vec", "v_vec", "max_degree_d",
        "claimed_num_points", "claimed_eval_rank",
    }
    if set(cert.keys()) != req:
        raise KoszulWordleCertificateError(f"Mode 4 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    s_raw = cert["s_vec"]
    v_raw = cert["v_vec"]
    if type(s_raw) is not list or not (1 <= len(s_raw) <= 3) or type(v_raw) is not list or len(v_raw) != len(s_raw):
        raise KoszulWordleCertificateError("Require 1 <= n <= 3 with len(s_vec) == len(v_vec)")
    s_vec = [_parse_int(v, f"s[{i}]") for i, v in enumerate(s_raw)]
    v_vec = [_parse_rat(v, f"v[{i}]") for i, v in enumerate(v_raw)]
    if any(s not in (1, 2) for s in s_vec):
        raise KoszulWordleCertificateError("Mode 4 rational V(J_n) requires s_k in {1, 2}")
    if any(v <= 0 for v in v_vec) or len(set(v_vec)) != len(s_vec):
        raise KoszulWordleCertificateError("v_vec must be distinct positive rationals")
    d = _parse_int(cert["max_degree_d"], "max_degree_d")
    if not (0 <= d <= 6):
        raise KoszulWordleCertificateError("Require 0 <= max_degree_d <= 6")

    n = len(s_vec)
    pts = rational_zero_set_VJn(s_vec, v_vec)
    monoms = list(itertools.product(range(d + 1), repeat=n))
    eval_mat = [
        [math.prod(pt[j] ** mon[j] for j in range(n)) for mon in monoms]
        for pt in pts
    ]
    rk = exact_rank_q(eval_mat)
    koszul_dim = alternating_koszul_dim(n, n, s_vec, [d] * n)
    if rk != koszul_dim:
        raise KoszulWordleCertificateError(f"Eval rank {rk} != Koszul quotient dim {koszul_dim}")
    if _parse_int(cert["claimed_num_points"], "claimed_num_points") != len(pts):
        raise KoszulWordleCertificateError(f"claimed_num_points mismatch: exact={len(pts)}")
    if _parse_int(cert["claimed_eval_rank"], "claimed_eval_rank") != rk:
        raise KoszulWordleCertificateError(f"claimed_eval_rank mismatch: exact={rk}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "s_vec": s_vec,
        "d": d,
        "num_points": len(pts),
        "eval_rank": rk,
    }


def verify_koszul_wordle_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise KoszulWordleCertificateError("Certificate root must be a dict")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise KoszulWordleCertificateError(f"Invalid schema: {cert.get('schema')!r}")
    name = cert.get("name")
    if type(name) is not str or not name.strip():
        raise KoszulWordleCertificateError(f"Certificate name must be non-empty str, got {name!r}")
    mode = cert.get("mode")
    if mode == "koszul_filtered_exactness_exact":
        return _verify_mode1_koszul_exactness(cert)
    if mode == "multicolor_wordle_dim_count_exact":
        return _verify_mode2_multicolor_dim(cert)
    if mode == "gap_free_strictness_failure_exact":
        return _verify_mode3_strictness_failure(cert)
    if mode == "zero_set_eval_rank_exact":
        return _verify_mode4_zero_set_eval_rank(cert)
    raise KoszulWordleCertificateError(f"Unknown mode: {mode!r}")
