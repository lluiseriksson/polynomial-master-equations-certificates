"""Generate all 16 canonical POLY-MASTER-CERT-1.0 certificates and 4 exact-Q studies
for Paper 44 (Miku Ishizaki & Jaeha Lee, arXiv:2611.33027, Nov 24, 2026).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.master_certifier import SCHEMA_VERSION, verify_poly_master_certificate_exact
from src.master_exact import (
    build_companion_matrix_eq29,
    compute_ivp_derivatives_eq24,
    format_rat,
    gcd_int,
    isqrt_exact,
    mat_add,
    mat_eye,
    mat_mul,
    mat_scale,
    mat_zero,
    two_qubit_V3_polys_eq64,
    two_qubit_polys_P_Q_eq61_64,
)

CERT_DIR = ROOT / "certificates"
DATA_DIR = ROOT / "data"


def _fmt_mat(M: Sequence[Sequence[Fraction]]) -> List[List[str]]:
    return [[format_rat(v) for v in row] for row in M]


def _fmt_mpoly(P: Sequence[Sequence[Sequence[Fraction]]]) -> List[List[List[str]]]:
    return [_fmt_mat(Pk) for Pk in P]


def _make_mode1(
    cid: str,
    P: List[List[List[Fraction]]],
    Q: List[List[List[Fraction]]],
) -> Dict[str, Any]:
    d = len(P[0])
    n = len(P) - 1
    derivs = compute_ivp_derivatives_eq24(P, Q)
    Theta = build_companion_matrix_eq29(P)
    tr_th = sum((Theta[i][i] for i in range(n * d)), Fraction(0, 1))
    last_sum = mat_zero(d, d)
    for k in range(n):
        last_sum = mat_add(last_sum, mat_mul(mat_scale(Fraction(-1, 1), P[k]), derivs[k]))
    return {
        "schema": SCHEMA_VERSION,
        "mode": "matrix_poly_laplace_ivp_cert",
        "cert_id": cid,
        "block_dim_d": d,
        "order_n": n,
        "P_coeffs": _fmt_mpoly(P),
        "Q_coeffs": _fmt_mpoly(Q),
        "claimed_initial_derivs": [_fmt_mat(M) for M in derivs],
        "claimed_companion_trace": format_rat(tr_th),
        "claimed_companion_last_row_block_sum": _fmt_mat(last_sum),
        "claimed_ode_residual_zero_at_t0": True,
    }


def _make_mode2(
    cid: str,
    wS: Fraction,
    wE: Fraction,
    J: Fraction,
    sub: str,
    regime: str,
    R: List[List[List[Fraction]]],
    Pt: List[List[List[Fraction]]],
    Qt: List[List[List[Fraction]]],
) -> Dict[str, Any]:
    return {
        "schema": SCHEMA_VERSION,
        "mode": "two_qubit_critical_factorization_cert",
        "cert_id": cid,
        "omega_S": format_rat(wS),
        "omega_E": format_rat(wE),
        "coupling_J": format_rat(J),
        "subspace": sub,
        "regime_label": regime,
        "R_factor_coeffs": _fmt_mpoly(R),
        "P_tilde_coeffs": _fmt_mpoly(Pt),
        "Q_tilde_coeffs": _fmt_mpoly(Qt),
        "claimed_order_before": len(R) - 1 + len(Pt) - 1,
        "claimed_order_after": len(Pt) - 1,
        "claimed_factorization_exact": True,
    }


def _make_mode3(
    cid: str,
    wS2: Fraction,
    wE2: Fraction,
    wSE: Fraction,
    J2: Fraction,
) -> Dict[str, Any]:
    Dp = J2 + wS2 + wE2 + Fraction(2, 1) * wSE
    Dm = J2 + wS2 + wE2 - Fraction(2, 1) * wSE
    sum_cos_sq = J2 / Dp + J2 / Dm
    nec = abs(wS2 - wE2) <= J2
    on_crit = abs(wS2 - wE2) == J2
    ratio_sq = Dm / Dp
    rn, rd = ratio_sq.numerator, ratio_sq.denominator
    sn, sd = isqrt_exact(rn), isqrt_exact(rd)
    is_rat = (sn * sn == rn) and (sd * sd == rd)
    if is_rat:
        g = gcd_int(sn, sd)
        qm, qp = sn // g, sd // g
        if on_crit:
            tier = "periodic_and_singular" if (qm % 2 == 1 and qp % 2 == 1) else "periodic_and_nonsingular"
        elif nec:
            tier = "interior_periodic"
        else:
            tier = "nonsingular_periodic"
    else:
        qm, qp = 0, 0
        if on_crit:
            tier = "nonperiodic_and_nonsingular"
        elif nec:
            tier = "interior_quasiperiodic"
        else:
            tier = "nonsingular_nonperiodic"
    return {
        "schema": SCHEMA_VERSION,
        "mode": "singularity_periodicity_hierarchy_cert",
        "cert_id": cid,
        "omega_S_sq": format_rat(wS2),
        "omega_E_sq": format_rat(wE2),
        "omega_SE_prod": format_rat(wSE),
        "coupling_J_sq": format_rat(J2),
        "claimed_sum_cos_sq": format_rat(sum_cos_sq),
        "claimed_necessary_singularity_holds": nec,
        "claimed_on_critical_boundary": on_crit,
        "claimed_ratio_omega_sq": format_rat(ratio_sq),
        "claimed_ratio_is_rational": is_rat,
        "claimed_ratio_q_minus": qm,
        "claimed_ratio_q_plus": qp,
        "claimed_tier": tier,
    }


def _make_mode4(cid: str, g0: Fraction, lam: Fraction) -> Dict[str, Any]:
    four_e2 = lam * (lam - Fraction(2, 1) * g0)
    u_c = [lam * g0 / Fraction(2, 1), lam, Fraction(1, 1)]
    v_c = [
        Fraction(2, 1) * lam * lam * g0,
        Fraction(2, 1) * lam * lam + Fraction(2, 1) * lam * g0,
        Fraction(3, 1) * lam,
        Fraction(1, 1),
    ]
    qu_c = [lam, Fraction(1, 1)]
    qv_c = [Fraction(2, 1) * lam * lam + lam * g0, Fraction(3, 1) * lam, Fraction(1, 1)]
    if four_e2 < 0:
        regime, ep = "nonmarkovian_singular_oscillatory", False
    elif four_e2 == 0:
        regime, ep = "critical_exceptional_point", True
    else:
        regime, ep = "overdamped_nonsingular", False
    return {
        "schema": SCHEMA_VERSION,
        "mode": "jaynes_cummings_exceptional_point_cert",
        "cert_id": cid,
        "gamma_0": format_rat(g0),
        "lambda_bw": format_rat(lam),
        "claimed_four_eps_sq": format_rat(four_e2),
        "claimed_u_poly_coeffs": [format_rat(c) for c in u_c],
        "claimed_v_poly_coeffs": [format_rat(c) for c in v_c],
        "claimed_q_u_coeffs": [format_rat(c) for c in qu_c],
        "claimed_q_v_coeffs": [format_rat(c) for c in qv_c],
        "claimed_regime": regime,
        "claimed_jordan_order3_nilpotent": ep,
    }


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    z0, one = Fraction(0, 1), Fraction(1, 1)
    certs: List[Dict[str, Any]] = []

    # --- Mode 1: 4 Sec. III IVP + Companion Matrix certificates ---
    # 1.1: Two-qubit V12 block at (wS=5, wE=4, J=3) (order 4, 2x2 matrices, Eq. 74 exact derivatives!)
    P12_a, Q12_a = two_qubit_polys_P_Q_eq61_64(Fraction(5, 1), Fraction(4, 1), Fraction(3, 1))
    certs.append(_make_mode1("m1_ivp_twoqubit_V12_5_4_3", P12_a, Q12_a))

    # 1.2: Two-qubit V3 block at (wS=5, wE=4, J=3) (order 5, 1x1, Eq. 77 exact derivatives!)
    P3_a, Q3_a = two_qubit_V3_polys_eq64(Fraction(5, 1), Fraction(4, 1), Fraction(3, 1))
    certs.append(_make_mode1("m1_ivp_twoqubit_V3_5_4_3", P3_a, Q3_a))

    # 1.3: Two-qubit V12 order-3 minimal form Eq. (63) at (wS=2, wE=1, J=3/2)!
    wS, wE, J = Fraction(2, 1), Fraction(1, 1), Fraction(3, 2)
    P12_o3 = [
        [[z0, -wS * wE * wE], [wS * wE * wE, z0]],
        [[wE * wE, z0], [z0, J * J + wE * wE]],
        [[z0, -wS], [wS, z0]],
        mat_eye(2),
    ]
    Q12_o3 = [
        [[wE * wE, z0], [z0, wE * wE]],
        mat_zero(2, 2),
        mat_eye(2),
    ]
    certs.append(_make_mode1("m1_ivp_twoqubit_V12_order3_eq63", P12_o3, Q12_o3))

    # 1.4: Jaynes-Cummings V3 cubic ODE (order 3, 1x1) at exceptional point lam=4, g0=2
    P_jc = [[[Fraction(64, 1)]], [[Fraction(48, 1)]], [[Fraction(12, 1)]], [[one]]]
    Q_jc = [[[Fraction(40, 1)]], [[Fraction(12, 1)]], [[one]]]
    certs.append(_make_mode1("m1_ivp_jc_order3_ep", P_jc, Q_jc))

    # --- Mode 2: 4 Sec. IV.F Two-Qubit Critical-Parameter Factorizations ---
    # 2.1: Trivial interaction J=0 on V12 (order 4 -> 1, Liouville-von Neumann reduction Eq. 83-85!)
    # P12(x) = (x^2+wS^2)(x^2+wE^2) I_2, Q12(x) = [[x(x^2+wE^2), -wS(x^2+wE^2)], [wS(x^2+wE^2), x(x^2+wE^2)]]
    # R12(x) = [[x(x^2+wE^2), -wS(x^2+wE^2)], [wS(x^2+wE^2), x(x^2+wE^2)]], P_tilde = [[x, wS], [-wS, x]], Q_tilde = I_2!
    # Wait: check sign! R12(x) * [[x, wS], [-wS, x]] = [[(x^2+wS^2)(x^2+wE^2), 0], [0, (x^2+wS^2)(x^2+wE^2)]] = P12!
    # And R12(x) * I_2 = Q12! YES!!
    wS_21, wE_21 = Fraction(3, 1), Fraction(2, 1)
    R_21 = [
        [[z0, -wS_21 * wE_21 * wE_21], [wS_21 * wE_21 * wE_21, z0]],
        [[wE_21 * wE_21, z0], [z0, wE_21 * wE_21]],
        [[z0, -wS_21], [wS_21, z0]],
        mat_eye(2),
    ]
    Pt_21 = [[[z0, wS_21], [-wS_21, z0]], mat_eye(2)]
    Qt_21 = [mat_eye(2)]
    certs.append(_make_mode2("m2_crit_J0_V12_lvn_order4_to_1", wS_21, wE_21, z0, "V12", "trivial_interaction_J0", R_21, Pt_21, Qt_21))

    # 2.2: Trivial interaction J=0 on V3 (order 5 -> 1, Eq. 86-88! R_3(x) = (x^2 + omega_+^2)(x^2 + omega_-^2) where omega_pm = wS +- wE)
    wp_22 = wS_21 + wE_21  # 5
    wm_22 = wS_21 - wE_21  # 1
    R_22 = [
        [[wp_22 * wp_22 * wm_22 * wm_22]],
        [[z0]],
        [[wp_22 * wp_22 + wm_22 * wm_22]],
        [[z0]],
        [[one]],
    ]
    Pt_22 = [[[z0]], [[one]]]
    Qt_22 = [[[one]]]
    certs.append(_make_mode2("m2_crit_J0_V3_order5_to_1", wS_21, wE_21, z0, "V3", "trivial_interaction_J0_V3", R_22, Pt_22, Qt_22))

    # 2.3: Non-trivial J=2, wS=3, wE=0 on V3 (order 5 -> 3, Eq. 96-97!)
    # P3(x) = x(x^2 + J^2 + wS^2)^2, Q3(x) = (x^2 + wS^2)(x^2 + J^2 + wS^2)
    # R(x) = x^2 + J^2 + wS^2, P_tilde(x) = x(x^2 + J^2 + wS^2), Q_tilde(x) = x^2 + wS^2!
    wS_23, J_23 = Fraction(3, 1), Fraction(2, 1)
    c23 = J_23 * J_23 + wS_23 * wS_23  # 13
    R_23 = [[[c23]], [[z0]], [[one]]]
    Pt_23 = [[[z0]], [[c23]], [[z0]], [[one]]]
    Qt_23 = [[[wS_23 * wS_23]], [[z0]], [[one]]]
    certs.append(_make_mode2("m2_crit_wE0_V3_order5_to_3", wS_23, z0, J_23, "V3", "non_trivial_wE0", R_23, Pt_23, Qt_23))

    # 2.4: Non-trivial J=3, wS=0, wE=0 on V3 (order 5 -> 2, Eq. 104-105!)
    # P3(x) = x(x^2 + J^2)^2, Q3(x) = x^2(x^2 + J^2)
    # R(x) = x(x^2 + J^2), P_tilde(x) = x^2 + J^2, Q_tilde(x) = x!
    J_24 = Fraction(3, 1)
    R_24 = [[[z0]], [[J_24 * J_24]], [[z0]], [[one]]]
    Pt_24 = [[[J_24 * J_24]], [[z0]], [[one]]]
    Qt_24 = [[[z0]], [[one]]]
    certs.append(_make_mode2("m2_crit_wS0_wE0_V3_order5_to_2", z0, z0, J_24, "V3", "harmonic_wS0_wE0", R_24, Pt_24, Qt_24))

    # --- Mode 3: 4 Sec. IV.G-I Singularity & Periodicity 3-Tier Hierarchy Certificates ---
    # 3.1: Fig. 3(a) Periodic & Singular: (wS, wE, J) = (5, 4, 3) -> Omega_-/Omega_+ = 1/3 (odd/odd)
    certs.append(_make_mode3("m3_tier1_periodic_singular_5_4_3", Fraction(25, 1), Fraction(16, 1), Fraction(20, 1), Fraction(9, 1)))
    # 3.2: Fig. 3(b) Periodic & Non-Singular: (wS, wE, J) = (5, 3, 4) -> Omega_-/Omega_+ = 1/2 (odd/even)
    certs.append(_make_mode3("m3_tier2_periodic_nonsing_5_3_4", Fraction(25, 1), Fraction(9, 1), Fraction(15, 1), Fraction(16, 1)))
    # 3.3: Fig. 3(c) Non-Periodic & Non-Singular on critical boundary: wS=2*sqrt(2) -> wS^2=8, wE^2=4, wSE=4*sqrt(2)??
    # Wait: wSE must be rational in our schema! Use exact rational triple on critical boundary with IRRATIONAL Omega_-/Omega_+:
    # e.g. wS=13, wE=12, J=5 -> |169-144|=25=J^2! D_- = 25 + 1 = 26, D_+ = 25 + 625 = 650, ratio = 26/650 = 1/25 = (1/5)^2 (odd/odd!).
    # How about wS=5, wE=1? No, |25-1|=24 not square. How about Pythagorean triple where D_-/D_+ is NOT a square!
    # Try (wS, wE, J) = (17, 15, 8): |289-225|=64=8^2! D_- = 64+4=68, D_+ = 64+1024=1088, ratio = 68/1088 = 1/16 = (1/4)^2 (rational).
    # Wait: on |wS^2 - wE^2| = J^2 with rational wS, wE, J:
    # D_- = J^2 + (wS - wE)^2 = (wS - wE)(wS + wE + wS - wE) = 2*wS*(wS - wE)!
    # D_+ = J^2 + (wS + wE)^2 = 2*wS*(wS + wE)!
    # So D_-/D_+ = (wS - wE) / (wS + wE)!! WHOA!! WHAT AN INSANE ALGEBRAIC GEM!!
    # So choosing (wS, wE, J) = (10, 8, 6)? D_-/D_+ = 2/18 = 1/9 (square).
    # Choose (wS, wE, J) = (13, 5, 12): |169-25|=144=12^2, D_-/D_+ = 8/18 = 4/9 (square).
    # Wait: for ANY primitive Pythagorean triple wS = m^2+n^2, wE = m^2-n^2, J = 2mn: (wS-wE)/(wS+wE) = n^2/m^2 (ALWAYS a square!).
    # Whereas if wE = 2mn, J = m^2-n^2: (wS-wE)/(wS+wE) = (m-n)^2/(m+n)^2 (ALSO a square!!).
    # Wait — what if wS^2, wE^2, wSE, J^2 are rational via wS = sqrt(p), wE = sqrt(q) with sqrt(pq) rational?
    # Take wS^2 = 5/2? No, take wS = 3*sqrt(2), wE = 2*sqrt(2), J^2 = |18 - 8| = 10 -> wSE = 12 (RATIONAL!)
    # Check: wS^2 = 18, wE^2 = 8, wSE = 12 (wSE^2 = 144 = 18*8 EXACT!), J^2 = 10 (|18-8|=10 ON CRITICAL BOUNDARY!).
    # Then D_- = 10 + 18 + 8 - 24 = 12, D_+ = 10 + 18 + 8 + 24 = 60, ratio = 12/60 = 1/5 -> IRRATIONAL sqrt(1/5)!!
    # OH!! PURE GENIUS!! ZERO FLOATS, 100% EXACT RATIONALS, ON CRITICAL BOUNDARY, PROVABLY IRRATIONAL!
    certs.append(_make_mode3("m3_tier3_nonperiodic_nonsing_crit_irr", Fraction(18, 1), Fraction(8, 1), Fraction(12, 1), Fraction(10, 1)))
    # 3.4: Strictly Non-Singular exterior domain |wS^2 - wE^2| > J^2: (wS, wE, J) = (6, 2, 3) -> |36-4|=32 > 9, sum_cos_sq < 1!
    certs.append(_make_mode3("m3_exterior_nonsingular_6_2_3", Fraction(36, 1), Fraction(4, 1), Fraction(12, 1), Fraction(9, 1)))

    # --- Mode 4: 4 Sec. V Jaynes-Cummings & Exceptional-Point Jordan Certificates ---
    certs.append(_make_mode4("m4_jc_nonmarkovian_singular_g4_l2", Fraction(4, 1), Fraction(2, 1)))
    certs.append(_make_mode4("m4_jc_exceptional_point_g2_l4", Fraction(2, 1), Fraction(4, 1)))
    certs.append(_make_mode4("m4_jc_exceptional_point_g3_2_l3", Fraction(3, 2), Fraction(3, 1)))
    certs.append(_make_mode4("m4_jc_overdamped_nonsing_g1_l6", Fraction(1, 1), Fraction(6, 1)))

    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        t0 = time.perf_counter()
        summary = verify_poly_master_certificate_exact(cert)
        ms = round((time.perf_counter() - t0) * 1000.0, 3)
        replay_rows.append({"cert_id": cert["cert_id"], "mode": cert["mode"], "verify_ms": ms, "summary": summary})

    (DATA_DIR / "certificate_replay_summary.json").write_text(
        json.dumps({"count": len(replay_rows), "certificates": replay_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Experiment 1: Two-qubit necessary singularity criterion sum_cos_sq vs |wS^2 - wE^2|/J^2 (fixed wE=3, J=4, sweep wS)
    exp1_rows = []
    for wS_num in range(0, 17):
        wS_q = Fraction(wS_num, 2)
        wE_q, J_q = Fraction(3, 1), Fraction(4, 1)
        Dp = J_q * J_q + (wS_q + wE_q) ** 2
        Dm = J_q * J_q + (wS_q - wE_q) ** 2
        scs = J_q * J_q / Dp + J_q * J_q / Dm
        gap_ratio = abs(wS_q * wS_q - wE_q * wE_q) / (J_q * J_q)
        exp1_rows.append({
            "omega_S": round(wS_q.numerator / wS_q.denominator, 3),
            "sum_cos_sq": round(scs.numerator / scs.denominator, 6),
            "gap_ratio": round(gap_ratio.numerator / gap_ratio.denominator, 6),
            "possibly_singular": scs >= Fraction(1, 1),
        })
    (DATA_DIR / "exp1_twoqubit_singularity_scan.json").write_text(
        json.dumps({"rows": exp1_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Experiment 2: Critical-parameter ODE order drop across all 4 Mode 2 regimes
    exp2_rows = [
        {"label": "J=0\n(V12 LvN)", "before": 4, "after": 1},
        {"label": "J=0\n(V3)", "before": 5, "after": 1},
        {"label": "wE=0\n(V3)", "before": 5, "after": 3},
        {"label": "wS=wE=0\n(V3)", "before": 5, "after": 2},
    ]
    (DATA_DIR / "exp2_critical_order_reduction.json").write_text(
        json.dumps({"rows": exp2_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Experiment 3: Jaynes-Cummings 4*eps^2 = lam*(lam - 2*g0) across lam/g0 ratio (g0 = 2)
    exp3_rows = []
    for lam_num in range(1, 17):
        lam_q = Fraction(lam_num, 2)
        g0_q = Fraction(2, 1)
        fe2 = lam_q * (lam_q - Fraction(2, 1) * g0_q)
        exp3_rows.append({
            "lambda_over_g0": round((lam_q / g0_q).numerator / (lam_q / g0_q).denominator, 3),
            "four_eps_sq": round(fe2.numerator / fe2.denominator, 6),
            "regime": "singular" if fe2 < 0 else ("EP" if fe2 == 0 else "overdamped"),
        })
    (DATA_DIR / "exp3_jc_exceptional_point_scan.json").write_text(
        json.dumps({"rows": exp3_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Experiment 4: 3-tier hierarchy summary on critical boundary |wS^2 - wE^2| = J^2
    exp4_rows = [
        r["summary"] | {"cert_id": r["cert_id"], "verify_ms": r["verify_ms"]}
        for r in replay_rows
        if r["mode"] == "singularity_periodicity_hierarchy_cert"
    ]
    (DATA_DIR / "exp4_singularity_hierarchy_summary.json").write_text(
        json.dumps({"rows": exp4_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Generated {len(replay_rows)} canonical {SCHEMA_VERSION} certificates and 4 experiment JSONs.")
    for r in replay_rows:
        print(f"  {r['cert_id']:40s} {r['verify_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    main()
