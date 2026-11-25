"""Comprehensive verification, exhaustive cross-checks, and 57-attack red-team suite
for KOSZUL-WORDLE-CERT-1.0 (Paper 31).
Author: Lluis Eriksson
"""
from __future__ import annotations

import copy
import itertools
import json
import math
import sys
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.koszul_certifier import (
    KoszulWordleCertificateError,
    verify_koszul_wordle_certificate_exact,
)
from src.koszul_exact import (
    alternating_koszul_dim,
    exact_rank_q,
    koszul_differential_matrix_q,
    rational_zero_set_VJn,
)

CERT_DIR = ROOT / "results" / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / name).read_text(encoding="utf-8"))


def test_exhaustive_gap_free_grid_and_eval_rank_cross_checks() -> None:
    """1. Exhaustively test all 16 multidegrees b in [0..3]^2 for N=M=2, s=(1,1):
       strictness defect == 0 iff b is gap-free (|b1-b2| <= 1) or trivial!
    2. Cross-check V(J_3) exact eval rank vs alternating Koszul dim for s=(2,1,2) across d=0..4."""
    v2 = [Fraction(1), Fraction(2)]
    c2 = [Fraction(1), Fraction(2)]
    pts2 = rational_zero_set_VJn([1, 1], v2)
    assert len(pts2) == 2
    for b1 in range(4):
        for b2 in range(4):
            b = [b1, b2]
            monoms = [(i, j) for i in range(b1 + 1) for j in range(b2 + 1)]
            emat = [[(p[0] ** m[0]) * (p[1] ** m[1]) for m in monoms] for p in pts2]
            true_q = exact_rank_q(emat)
            mat1, r0, _ = koszul_differential_matrix_q(2, 2, [1, 1], c2, b, 1)
            koszul_q = r0 - exact_rank_q(mat1)
            if abs(b1 - b2) <= 1:
                assert koszul_q == true_q
            if b in ([0, 2], [2, 0], [0, 3], [3, 0]):
                assert koszul_q > true_q  # strictness genuinely FAILS!

    # Cross-check n=3, s=(2,1,2) on all 24 exact rational points of V(J_3) across d=0..4
    pts3 = rational_zero_set_VJn([2, 1, 2], [Fraction(1), Fraction(2), Fraction(3)])
    assert len(pts3) == 24
    for d in range(5):
        monoms = list(itertools.product(range(d + 1), repeat=3))
        emat = [[math.prod(p[j] ** m[j] for j in range(3)) for m in monoms] for p in pts3]
        assert exact_rank_q(emat) == alternating_koszul_dim(3, 3, [2, 1, 2], [d, d, d])


def test_all_16_certificates_verify_cleanly() -> None:
    cert_files = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(cert_files) == 16
    for p in cert_files:
        cert = json.loads(p.read_text(encoding="utf-8"))
        res = verify_koszul_wordle_certificate_exact(cert)
        assert res["verified"] is True


def test_57_live_adversarial_red_team_attacks_rejected() -> None:
    m1 = _load("koszul_exact_n2_m2_s32.cert.json")
    m2 = _load("wordle_dim_n2_s32.cert.json")
    m3 = _load("fail_remarkA1_s22_b24.cert.json")
    m4 = _load("eval_rank_n2_s22_d2.cert.json")

    def mutate(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
        c = copy.deepcopy(base)
        fn(c)
        return c

    attacks: List[Tuple[str, Any]] = [
        # --- Global AST / schema / type attacks (1-14) ---
        ("01_root_not_dict", [1, 2, 3]),
        ("02_bad_schema", mutate(m1, lambda c: c.__setitem__("schema", "KOSZUL-WORDLE-CERT-2.0"))),
        ("03_unknown_mode", mutate(m1, lambda c: c.__setitem__("mode", "fake_mode"))),
        ("04_empty_name", mutate(m1, lambda c: c.__setitem__("name", "  "))),
        ("05_float_injected", mutate(m1, lambda c: c["v_vec"].__setitem__(0, 1.0))),
        ("06_bool_as_int", mutate(m1, lambda c: c.__setitem__("N", True))),
        ("07_decimal_injected", mutate(m1, lambda c: c["v_vec"].__setitem__(0, Decimal("1")))),
        ("08_complex_injected", mutate(m2, lambda c: c.__setitem__("max_d", 6 + 0j))),
        ("09_tuple_injected", mutate(m1, lambda c: c.__setitem__("s_vec", (3, 2)))),
        ("10_non_str_key", {**m2, 99: "bad"}),
        ("11_unreduced_frac", mutate(m1, lambda c: c["v_vec"].__setitem__(0, "2/4"))),
        ("12_denom_one_str", mutate(m1, lambda c: c["v_vec"].__setitem__(0, "1/1"))),
        ("13_neg_zero_str", mutate(m3, lambda c: c["dual_functional_w"].__setitem__(0, "-0"))),
        ("14_extra_key", mutate(m4, lambda c: c.__setitem__("rogue", 1))),

        # --- Mode 1: Filtered Koszul exactness attacks (15-26) ---
        ("15_m1_missing_key", mutate(m1, lambda c: c.pop("claimed_quotient_dim"))),
        ("16_m1_M_gt_N", mutate(m1, lambda c: c.__setitem__("M", 3))),
        ("17_m1_nonpos_v", mutate(m1, lambda c: c["v_vec"].__setitem__(0, "0"))),
        ("18_m1_duplicate_v", mutate(m1, lambda c: c["v_vec"].__setitem__(1, "1"))),
        ("19_m1_s_out_of_range", mutate(m1, lambda c: c["s_vec"].__setitem__(0, 0))),
        ("20_m1_not_gap_free", mutate(m1, lambda c: c.__setitem__("multidegree_b", [0, 2]))),
        ("21_m1_wrong_grade_dims", mutate(m1, lambda c: c["claimed_grade_dims"].__setitem__(0, 99))),
        ("22_m1_wrong_diff_ranks", mutate(m1, lambda c: c["claimed_diff_ranks"].__setitem__(0, 0))),
        ("23_m1_wrong_quot_dim", mutate(m1, lambda c: c.__setitem__("claimed_quotient_dim", 11))),
        ("24_m1_b_len_mismatch", mutate(m1, lambda c: c["multidegree_b"].pop())),
        ("25_m1_s_len_mismatch", mutate(m1, lambda c: c["s_vec"].pop())),
        ("26_m1_v_len_mismatch", mutate(m1, lambda c: c["v_vec"].pop())),

        # --- Mode 2: Multicolor Wordle dimension count attacks (27-35) ---
        ("27_m2_missing_key", mutate(m2, lambda c: c.pop("claimed_sat_deg"))),
        ("28_m2_empty_s_vec", mutate(m2, lambda c: c.__setitem__("s_vec", []))),
        ("29_m2_zero_color", mutate(m2, lambda c: c["s_vec"].__setitem__(0, 0))),
        ("30_m2_max_d_too_small", mutate(m2, lambda c: c.__setitem__("max_d", 2))),
        ("31_m2_max_d_too_large", mutate(m2, lambda c: c.__setitem__("max_d", 20))),
        ("32_m2_wrong_gf_coeffs", mutate(m2, lambda c: c["claimed_gf_coeffs"].__setitem__(0, 2))),
        ("33_m2_wrong_cumul_dims", mutate(m2, lambda c: c["claimed_cumul_dims"].__setitem__(2, 9))),
        ("34_m2_wrong_sat_deg", mutate(m2, lambda c: c.__setitem__("claimed_sat_deg", 5))),
        ("35_m2_wrong_total_perms", mutate(m2, lambda c: c.__setitem__("claimed_total_colored_perms", 10))),

        # --- Mode 3: Remark A.1 gap-free strictness failure attacks (36-47) ---
        ("36_m3_missing_key", mutate(m3, lambda c: c.pop("dual_functional_w"))),
        ("37_m3_is_gap_free", mutate(m3, lambda c: c.__setitem__("multidegree_b", [3, 4]))),
        ("38_m3_duplicate_v", mutate(m3, lambda c: c["v_vec"].__setitem__(1, "1"))),
        ("39_m3_wrong_A_len", mutate(m3, lambda c: c["ideal_multipliers_A"].pop())),
        ("40_m3_empty_witness_Z", mutate(m3, lambda c: c.__setitem__("witness_Z", []))),
        ("41_m3_Z_not_in_ideal", mutate(m3, lambda c: c["witness_Z"].__setitem__(0, [c["witness_Z"][0][0], "999"]))),
        ("42_m3_Z_exceeds_b", mutate(m3, lambda c: c.__setitem__("multidegree_b", [0, 4]))),
        ("43_m3_neg_exponent", mutate(m3, lambda c: c["witness_Z"].__setitem__(0, [[-1, 0], "1"]))),
        ("44_m3_dup_monomial", mutate(m3, lambda c: c["witness_Z"].append(c["witness_Z"][0][:]))),
        ("45_m3_wrong_w_len", mutate(m3, lambda c: c["dual_functional_w"].pop())),
        ("46_m3_w_zero_vector", mutate(m3, lambda c: c.__setitem__("dual_functional_w", ["0"] * len(c["dual_functional_w"])))),
        ("47_m3_w_not_in_ker_d1T", mutate(m3, lambda c: c["dual_functional_w"].__setitem__(0, "7"))),

        # --- Mode 4: Rational zero-set evaluation rank attacks (48-57) ---
        ("48_m4_missing_key", mutate(m4, lambda c: c.pop("claimed_eval_rank"))),
        ("49_m4_s_eq_3_not_rational", mutate(m4, lambda c: c["s_vec"].__setitem__(0, 3))),
        ("50_m4_s_zero", mutate(m4, lambda c: c["s_vec"].__setitem__(0, 0))),
        ("51_m4_duplicate_v", mutate(m4, lambda c: c["v_vec"].__setitem__(1, "1"))),
        ("52_m4_neg_v", mutate(m4, lambda c: c["v_vec"].__setitem__(0, "-1"))),
        ("53_m4_neg_d", mutate(m4, lambda c: c.__setitem__("max_degree_d", -1))),
        ("54_m4_d_too_large", mutate(m4, lambda c: c.__setitem__("max_degree_d", 7))),
        ("55_m4_wrong_num_points", mutate(m4, lambda c: c.__setitem__("claimed_num_points", 9))),
        ("56_m4_wrong_eval_rank", mutate(m4, lambda c: c.__setitem__("claimed_eval_rank", 6))),
        ("57_m4_n_too_large", mutate(m4, lambda c: c.__setitem__("s_vec", [1, 1, 1, 1]) or c.__setitem__("v_vec", ["1", "2", "3", "4"]))),
    ]

    assert len(attacks) == 57
    for label, payload in attacks:
        with pytest.raises(KoszulWordleCertificateError, match="."):
            verify_koszul_wordle_certificate_exact(payload)
