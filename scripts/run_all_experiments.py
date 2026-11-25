"""Generate all 16 canonical KOSZUL-WORDLE-CERT-1.0 certificates and 4 experiment JSONs for Paper 31.
ZERO floating-point arithmetic in any certificate generation or verification.
Author: Lluis Eriksson
"""
from __future__ import annotations

import itertools
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.koszul_certifier import verify_koszul_wordle_certificate_exact
from src.koszul_exact import (
    MPolyQ,
    alternating_koszul_dim,
    build_generator_Q,
    exact_rank_q,
    filtered_basis_Fhb,
    fmt_rat,
    koszul_differential_matrix_q,
    mp_add,
    mp_mul,
    multicolor_wordle_gf_z,
    rational_zero_set_VJn,
)

RESULTS = ROOT / "results"
CERT_DIR = RESULTS / "certificates"
CERT_DIR.mkdir(parents=True, exist_ok=True)


def _emit_cert(filename: str, cert: Dict[str, Any]) -> Dict[str, Any]:
    path = CERT_DIR / filename
    path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    t0 = time.perf_counter()
    res = verify_koszul_wordle_certificate_exact(cert)
    dt_ms = round((time.perf_counter() - t0) * 1000.0, 3)
    return {"file": filename, "mode": cert["mode"], "verify_ms": dt_ms, "summary": res}


def _mp_to_json(p: MPolyQ) -> List[Any]:
    return [[list(m), fmt_rat(c)] for m, c in sorted(p.items()) if c != 0]


def _find_farkas_dual_w(mat: List[List[Fraction]], z_vec: List[Fraction]) -> List[Fraction]:
    """Compute exact rational w in ker(mat^T) such that w^T z_vec != 0 (zero floats)."""
    rows = len(mat)
    cols = len(mat[0]) if mat else 0
    if cols == 0:
        # Any vector with w^T z_vec != 0 works
        for i, v in enumerate(z_vec):
            if v != 0:
                w = [Fraction(0)] * rows
                w[i] = Fraction(1)
                return w
        raise RuntimeError("z_vec is zero")
    # Build transpose M = mat^T (cols x rows), find RREF nullspace basis
    A = [[mat[r][c] for r in range(rows)] for c in range(cols)]
    piv_cols: List[int] = []
    r_idx = 0
    for c in range(rows):
        piv = None
        for r in range(r_idx, cols):
            if A[r][c] != 0:
                piv = r
                break
        if piv is None:
            continue
        A[r_idx], A[piv] = A[piv], A[r_idx]
        pv = A[r_idx][c]
        for j in range(c, rows):
            A[r_idx][j] /= pv
        for r in range(cols):
            if r != r_idx and A[r][c] != 0:
                fac = A[r][c]
                for j in range(c, rows):
                    A[r][j] -= fac * A[r_idx][j]
        piv_cols.append(c)
        r_idx += 1
        if r_idx == cols:
            break
    piv_set = set(piv_cols)
    free_cols = [c for c in range(rows) if c not in piv_set]
    for fc in free_cols:
        w = [Fraction(0)] * rows
        w[fc] = Fraction(1)
        for pr, pc in enumerate(piv_cols):
            w[pc] = -A[pr][fc]
        if sum(w[i] * z_vec[i] for i in range(rows)) != 0:
            return w
    raise RuntimeError("z_vec lies in im(mat); no Farkas dual exists")


def main() -> None:
    atlas_rows: List[Dict[str, Any]] = []

    # =========================================================================
    # MODE 1: 4 Filtered Koszul Complex Exactness Certificates (Theorem 5.1)
    # =========================================================================
    m1_specs = [
        ("koszul_exact_n3_m3_s111.cert.json", "mode1_koszul_n3_m3_s111", 3, 3, [1, 1, 1], [1, 2, 3], [2, 2, 2]),
        ("koszul_exact_n2_m2_s32.cert.json", "mode1_koszul_n2_m2_s32", 2, 2, [3, 2], [1, 2], [4, 4]),
        ("koszul_exact_n3_m2_gapfree.cert.json", "mode1_koszul_n3_m2_gapfree", 3, 2, [2, 1], [1, 2], [2, 3, 2]),
        ("koszul_exact_n2_m2_s22_gapfree.cert.json", "mode1_koszul_n2_m2_s22_gf", 2, 2, [2, 2], [1, 3], [3, 4]),
    ]
    for fname, cname, N, M, s_vec, v_ints, b in m1_specs:
        v_vec = [Fraction(v, 1) for v in v_ints]
        c_vec = [v_vec[k] ** s_vec[k] for k in range(M)]
        gdims = [len(filtered_basis_Fhb(N, M, s_vec, b, h)) for h in range(M + 1)]
        ranks = [exact_rank_q(koszul_differential_matrix_q(N, M, s_vec, c_vec, b, h)[0]) for h in range(1, M + 1)]
        qdim = gdims[0] - ranks[0]
        atlas_rows.append(_emit_cert(fname, {
            "schema": "KOSZUL-WORDLE-CERT-1.0",
            "mode": "koszul_filtered_exactness_exact",
            "name": cname,
            "N": N,
            "M": M,
            "s_vec": s_vec,
            "v_vec": [fmt_rat(v) for v in v_vec],
            "multidegree_b": b,
            "claimed_grade_dims": gdims,
            "claimed_diff_ranks": ranks,
            "claimed_quotient_dim": qdim,
        }))

    # =========================================================================
    # MODE 2: 4 Multicolor Permutation Wordle Dimension Certificates (Thm 6.1)
    # =========================================================================
    m2_specs = [
        ("wordle_dim_n3_s111.cert.json", "mode2_wordle_n3_s111", [1, 1, 1], 4),
        ("wordle_dim_n2_s32.cert.json", "mode2_wordle_n2_s32", [3, 2], 6),
        ("wordle_dim_n4_s1111.cert.json", "mode2_wordle_n4_s1111", [1, 1, 1, 1], 5),
        ("wordle_dim_n3_s223.cert.json", "mode2_wordle_n3_s223", [2, 2, 3], 8),
    ]
    for fname, cname, s_vec, max_d in m2_specs:
        n = len(s_vec)
        gf = multicolor_wordle_gf_z(s_vec)
        sat_deg = sum(s_vec) - 1
        tot = math.factorial(n)
        for sk in s_vec:
            tot *= sk
        cumul = [alternating_koszul_dim(n, n, s_vec, [d] * n) for d in range(max_d + 1)]
        atlas_rows.append(_emit_cert(fname, {
            "schema": "KOSZUL-WORDLE-CERT-1.0",
            "mode": "multicolor_wordle_dim_count_exact",
            "name": cname,
            "s_vec": s_vec,
            "max_d": max_d,
            "claimed_gf_coeffs": gf,
            "claimed_cumul_dims": cumul,
            "claimed_sat_deg": sat_deg,
            "claimed_total_colored_perms": tot,
        }))

    # =========================================================================
    # MODE 3: 4 Appendix A Remark A.1 Non-Gap-Free Strictness Failure Certificates
    # =========================================================================
    def _make_remark_a1_cert(
        fname: str, cname: str, N: int, M: int, s_vec: List[int], v_ints: List[int],
        b: List[int], As: List[MPolyQ]
    ) -> Dict[str, Any]:
        v_vec = [Fraction(v, 1) for v in v_ints]
        c_vec = [v_vec[k] ** s_vec[k] for k in range(M)]
        Qs = [build_generator_Q(N, s_vec[k], c_vec[k]) for k in range(M)]
        Z: MPolyQ = {}
        for k in range(M):
            Z = mp_add(Z, mp_mul(As[k], Qs[k]))
        basis0 = filtered_basis_Fhb(N, M, s_vec, b, 0)
        idx0 = {mon: i for i, (_, mon) in enumerate(basis0)}
        z_vec = [Fraction(0)] * len(basis0)
        for mon, coeff in Z.items():
            z_vec[idx0[mon]] = coeff
        mat1, _, _ = koszul_differential_matrix_q(N, M, s_vec, c_vec, b, 1)
        w = _find_farkas_dual_w(mat1, z_vec)
        return _emit_cert(fname, {
            "schema": "KOSZUL-WORDLE-CERT-1.0",
            "mode": "gap_free_strictness_failure_exact",
            "name": cname,
            "N": N,
            "M": M,
            "s_vec": s_vec,
            "v_vec": [fmt_rat(v) for v in v_vec],
            "multidegree_b": b,
            "ideal_multipliers_A": [_mp_to_json(Ak) for Ak in As],
            "witness_Z": _mp_to_json(Z),
            "dual_functional_w": [fmt_rat(val) for val in w],
        })

    # 3a. Remark A.1 (s=(1,1), b=(0,2)): A1 = (x2 - c2), A2 = -(x2 - c1)
    atlas_rows.append(_make_remark_a1_cert(
        "fail_remarkA1_s11_b02.cert.json", "mode3_remarkA1_s11_b02",
        2, 2, [1, 1], [1, 2], [0, 2],
        [{(0, 1): Fraction(1), (0, 0): Fraction(-2)}, {(0, 1): Fraction(-1), (0, 0): Fraction(1)}],
    ))
    # 3b. Remark A.1 symmetric (s=(1,1), b=(2,0)): A1 = (x1 - c2), A2 = -(x1 - c1)
    atlas_rows.append(_make_remark_a1_cert(
        "fail_remarkA1_s11_b20.cert.json", "mode3_remarkA1_s11_b20",
        2, 2, [1, 1], [1, 3], [2, 0],
        [{(1, 0): Fraction(1), (0, 0): Fraction(-3)}, {(1, 0): Fraction(-1), (0, 0): Fraction(1)}],
    ))
    # 3c. Remark A.1 (s=(2,2), b=(2,4)): A1 = x1*(x2^2 - c2), A2 = -x1*(x2^2 - c1) (c1=1, c2=4)
    atlas_rows.append(_make_remark_a1_cert(
        "fail_remarkA1_s22_b24.cert.json", "mode3_remarkA1_s22_b24",
        2, 2, [2, 2], [1, 2], [2, 4],
        [{(1, 2): Fraction(1), (1, 0): Fraction(-4)}, {(1, 2): Fraction(-1), (1, 0): Fraction(1)}],
    ))
    # 3d. 3-variable non-gap-free (N=3, M=2, s=(1,1), b=(0,2,2)):
    #     A1 = (x2 - c2)*(x3 - c2), A2 = -(x2 - c1)*(x3 - c1) -> x1 cancels!
    #     Wait: Q1=(x1-1)(x2-1)(x3-1), Q2=(x1-2)(x2-2)(x3-2) => A1=(x2-2)(x3-2), A2=-(x2-1)(x3-1) =>
    #     A1*Q1 + A2*Q2 = ((x1-1)-(x1-2))*(x2-1)(x2-2)(x3-1)(x3-2) = (x2-1)(x2-2)(x3-1)(x3-2) in R_3(0,2,2)!
    A1_3d = mp_mul({(0, 1, 0): Fraction(1), (0, 0, 0): Fraction(-2)}, {(0, 0, 1): Fraction(1), (0, 0, 0): Fraction(-2)})
    A2_3d = mp_mul({(0, 1, 0): Fraction(-1), (0, 0, 0): Fraction(1)}, {(0, 0, 1): Fraction(1), (0, 0, 0): Fraction(-1)})
    atlas_rows.append(_make_remark_a1_cert(
        "fail_remarkA1_n3_b022.cert.json", "mode3_remarkA1_n3_b022",
        3, 2, [1, 1], [1, 2], [0, 2, 2],
        [A1_3d, A2_3d],
    ))

    # =========================================================================
    # MODE 4: 4 Exact Rational Zero-Set Evaluation-Rank Certificates (Sec 6.1)
    # =========================================================================
    m4_specs = [
        ("eval_rank_n3_s111_d1.cert.json", "mode4_eval_n3_s111_d1", [1, 1, 1], [1, 2, 3], 1),
        ("eval_rank_n2_s22_d2.cert.json", "mode4_eval_n2_s22_d2", [2, 2], [1, 2], 2),
        ("eval_rank_n3_s212_d2.cert.json", "mode4_eval_n3_s212_d2", [2, 1, 2], [1, 2, 3], 2),
        ("eval_rank_n3_s222_d3.cert.json", "mode4_eval_n3_s222_d3", [2, 2, 2], [1, 2, 3], 3),
    ]
    for fname, cname, s_vec, v_ints, d in m4_specs:
        n = len(s_vec)
        v_vec = [Fraction(v, 1) for v in v_ints]
        pts = rational_zero_set_VJn(s_vec, v_vec)
        rk = alternating_koszul_dim(n, n, s_vec, [d] * n)
        atlas_rows.append(_emit_cert(fname, {
            "schema": "KOSZUL-WORDLE-CERT-1.0",
            "mode": "zero_set_eval_rank_exact",
            "name": cname,
            "s_vec": s_vec,
            "v_vec": [fmt_rat(v) for v in v_vec],
            "max_degree_d": d,
            "claimed_num_points": len(pts),
            "claimed_eval_rank": rk,
        }))

    (RESULTS / "exp1_certified_atlas.json").write_text(
        json.dumps({"experiment": "exp1_certified_atlas", "count": len(atlas_rows), "rows": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 2: Multicolor Wordle Cumulative Dimension Curves (d = 0..7)
    # =========================================================================
    exp2_curves = {}
    for label, s_vec in [
        ("n3_s111", [1, 1, 1]),
        ("n2_s32", [3, 2]),
        ("n4_s1111", [1, 1, 1, 1]),
        ("n3_s212", [2, 1, 2]),
        ("n3_s222", [2, 2, 2]),
    ]:
        n = len(s_vec)
        exp2_curves[label] = {
            "s_vec": s_vec,
            "sat_deg": sum(s_vec) - 1,
            "dims": [alternating_koszul_dim(n, n, s_vec, [d] * n) for d in range(8)],
        }
    (RESULTS / "exp2_wordle_dim_curves.json").write_text(
        json.dumps({"experiment": "exp2_wordle_dim_curves", "curves": exp2_curves}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 3: Exact Koszul Exactness vs. Gap-Free Failure Grid on N=M=2, s=(1,1)
    # =========================================================================
    # For b = (b1, b2) in [0..3]^2, compare dim R_2(b) - rank(delta_1) vs alternating_koszul_dim!
    # Wait: exactness holds everywhere in M=2 for s=(1,1) EXCEPT strictness fails when |b1 - b2| >= 2!
    # We measure BOTH actual eval rank on V(J_2) (exact dim R_2(b) / (J_2 cap R_2(b))) vs. Koszul formula!
    v2 = [Fraction(1), Fraction(2)]
    c2 = [Fraction(1), Fraction(2)]
    pts2 = rational_zero_set_VJn([1, 1], v2)
    exp3_rows = []
    for b1 in range(4):
        for b2 in range(4):
            b = [b1, b2]
            monoms = [(i, j) for i in range(b1 + 1) for j in range(b2 + 1)]
            emat = [[(p[0] ** m[0]) * (p[1] ** m[1]) for m in monoms] for p in pts2]
            true_quot_dim = exact_rank_q(emat)
            mat1, r0, _ = koszul_differential_matrix_q(2, 2, [1, 1], c2, b, 1)
            koszul_im_quot = r0 - exact_rank_q(mat1)
            gf = abs(b1 - b2) <= 1
            exp3_rows.append({
                "b": b,
                "gap_free": gf,
                "true_quotient_dim": true_quot_dim,
                "koszul_delta1_quot_dim": koszul_im_quot,
                "strictness_defect": koszul_im_quot - true_quot_dim,
            })
    (RESULTS / "exp3_gap_free_strictness_grid.json").write_text(
        json.dumps({"experiment": "exp3_gap_free_strictness_grid", "rows": exp3_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 4: Exact Rational Eval Rank Sweep Across d = 0..4 for n=3, s=(2,1,2)
    # =========================================================================
    pts3 = rational_zero_set_VJn([2, 1, 2], [Fraction(1), Fraction(2), Fraction(3)])
    exp4_rows = []
    for d in range(5):
        monoms = list(itertools.product(range(d + 1), repeat=3))
        emat = [[math.prod(p[j] ** m[j] for j in range(3)) for m in monoms] for p in pts3]
        rk = exact_rank_q(emat)
        kd = alternating_koszul_dim(3, 3, [2, 1, 2], [d, d, d])
        exp4_rows.append({"d": d, "ambient_dim": len(monoms), "eval_rank": rk, "koszul_dim": kd, "match": rk == kd})
    (RESULTS / "exp4_eval_rank_sweep.json").write_text(
        json.dumps({"experiment": "exp4_eval_rank_sweep", "num_points": len(pts3), "rows": exp4_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"[PASS] Generated & verified {len(atlas_rows)}/16 exact-Q certificates and 4 experiment JSONs.")
    for r in atlas_rows:
        print(f"  {r['file']:44s} {r['verify_ms']:6.3f} ms  {r['summary']}")


if __name__ == "__main__":
    main()
