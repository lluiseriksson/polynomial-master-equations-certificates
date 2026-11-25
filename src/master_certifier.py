"""Zero-floating-point exact-Q certificate verifier: POLY-MASTER-CERT-1.0.
Audits all four algebraic, critical-factorization, singularity-hierarchy, and exceptional-point
pillars of Miku Ishizaki & Jaeha Lee (arXiv:2611.33027, Nov 24, 2026)
"Polynomial Master Equations of Open Quantum Systems and an Analysis on the Critical Solutions":
  - Mode 1: matrix_poly_laplace_ivp_cert (Sec. III Eqs. 24-29 IVP derivatives & companion matrix Theta)
  - Mode 2: two_qubit_critical_factorization_cert (Sec. IV.C & IV.F exact P = R*P_tilde, Q = R*Q_tilde)
  - Mode 3: singularity_periodicity_hierarchy_cert (Sec. IV.G-I Eqs. 108-119 3-tier hierarchy)
  - Mode 4: jaynes_cummings_exceptional_point_cert (Sec. V Eqs. 126-151 similarity, u/v polys & Jordan EP)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import re
from fractions import Fraction
from typing import Any, Dict, List, Set

from src.master_exact import (
    build_companion_matrix_eq29,
    compute_ivp_derivatives_eq24,
    format_rat,
    gcd_int,
    isqrt_exact,
    mat_add,
    mat_eye,
    mat_mul,
    mat_poly_mul,
    mat_scale,
    mat_zero,
    two_qubit_V3_polys_eq64,
    two_qubit_polys_P_Q_eq61_64,
)

SCHEMA_VERSION = "POLY-MASTER-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A-?[1-9][0-9]*/[1-9][0-9]*\Z")
MAX_RAT_STR_LEN = 1024
MAX_INT_BITS = 2048
MAX_ID_LEN = 128
MAX_JSON_DEPTH = 32


class PolyMasterCertificateError(ValueError):
    """Raised whenever a POLY-MASTER-CERT-1.0 certificate fails any invariant."""


def _assert_strict_json_types(obj: Any, path: str = "$", depth: int = 0) -> None:
    if depth > MAX_JSON_DEPTH:
        raise PolyMasterCertificateError(f"JSON nesting depth > {MAX_JSON_DEPTH} at {path}")
    t = type(obj)
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise PolyMasterCertificateError(f"Integer bit-length > {MAX_INT_BITS} at {path}")
        return
    if t is str or t is bool:
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]", depth + 1)
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise PolyMasterCertificateError(f"Non-string dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}", depth + 1)
        return
    raise PolyMasterCertificateError(f"Forbidden JSON type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise PolyMasterCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    if val.bit_length() > MAX_INT_BITS:
        raise PolyMasterCertificateError(f"{name} integer too large")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        if val.bit_length() > MAX_INT_BITS:
            raise PolyMasterCertificateError(f"{name} integer too large")
        return Fraction(val, 1)
    if type(val) is str:
        if len(val) > MAX_RAT_STR_LEN:
            raise PolyMasterCertificateError(f"{name} rational string too long")
        if _CANON_INT_RE.match(val):
            iv = int(val)
            if iv.bit_length() > MAX_INT_BITS:
                raise PolyMasterCertificateError(f"{name} integer bit-length > {MAX_INT_BITS}")
            return Fraction(iv, 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if num.bit_length() > MAX_INT_BITS or den.bit_length() > MAX_INT_BITS:
                raise PolyMasterCertificateError(f"{name} rational bit-length > {MAX_INT_BITS}")
            if den < 2:
                raise PolyMasterCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise PolyMasterCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise PolyMasterCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise PolyMasterCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_exact_keys(cert: Dict[str, Any], req: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != req:
        raise PolyMasterCertificateError(f"{mode} key mismatch: {sorted(keys ^ req)}")


def _parse_mat(raw: Any, rows: int, cols: int, name: str) -> List[List[Fraction]]:
    if type(raw) is not list or len(raw) != rows:
        raise PolyMasterCertificateError(f"{name} row count != {rows}")
    out: List[List[Fraction]] = []
    for r in range(rows):
        if type(raw[r]) is not list or len(raw[r]) != cols:
            raise PolyMasterCertificateError(f"{name}[{r}] col count != {cols}")
        out.append([_parse_rat(raw[r][c], f"{name}[{r}][{c}]") for c in range(cols)])
    return out


def _parse_mat_poly(raw: Any, deg: int, d: int, name: str) -> List[List[List[Fraction]]]:
    if type(raw) is not list or len(raw) != deg + 1:
        raise PolyMasterCertificateError(f"{name} must have {deg + 1} coefficient matrices")
    return [_parse_mat(raw[k], d, d, f"{name}[{k}]") for k in range(deg + 1)]


# =============================================================================
# Mode 1: Section III Eqs. (24)-(29) Matrix-Polynomial IVP & Companion Matrix
# =============================================================================


def _verify_mode1_ivp_companion(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "block_dim_d",
        "order_n",
        "P_coeffs",
        "Q_coeffs",
        "claimed_initial_derivs",
        "claimed_companion_trace",
        "claimed_companion_last_row_block_sum",
        "claimed_ode_residual_zero_at_t0",
    }
    _parse_exact_keys(cert, req, "Mode 1")
    d = _parse_int(cert["block_dim_d"], "block_dim_d")
    n = _parse_int(cert["order_n"], "order_n")
    if not (1 <= d <= 4 and 1 <= n <= 6):
        raise PolyMasterCertificateError("Require 1 <= d <= 4 and 1 <= n <= 6")

    P = _parse_mat_poly(cert["P_coeffs"], n, d, "P_coeffs")
    Q = _parse_mat_poly(cert["Q_coeffs"], n - 1, d, "Q_coeffs")
    if P[n] != mat_eye(d):
        raise PolyMasterCertificateError("P(x) must be monic (P_n == I_d)")
    if Q[n - 1] != mat_eye(d):
        raise PolyMasterCertificateError("Q(x) must be monic of order n - 1 (Q_{n-1} == I_d)")

    derivs = compute_ivp_derivatives_eq24(P, Q)
    Theta = build_companion_matrix_eq29(P)

    # Verify E(0) == I_d (exact dynamical map normalization at t = 0)
    if derivs[0] != mat_eye(d):
        raise PolyMasterCertificateError("E(0) != I_d for monic P, Q pair")

    # Verify companion matrix Theta trace == -Tr(P_{n-1}) and ODE relation at t=0:
    # E^{(n)}(0) = -sum_{k=0}^{n-1} P_k E^{(k)}(0) equals companion action on F(0)!
    N = n * d
    tr_theta = sum((Theta[i][i] for i in range(N)), Fraction(0, 1))
    last_row_sum = mat_zero(d, d)
    for k in range(n):
        last_row_sum = mat_add(last_row_sum, mat_mul(mat_scale(Fraction(-1, 1), P[k]), derivs[k]))
    # Check companion matrix times stacked F(0) matches shifted derivatives
    F0 = mat_zero(N, d)
    for k in range(n):
        for r in range(d):
            for c in range(d):
                F0[k * d + r][c] = derivs[k][r][c]
    dF0 = mat_mul(Theta, F0)
    for k in range(n - 1):
        blk = [[dF0[k * d + r][c] for c in range(d)] for r in range(d)]
        if blk != derivs[k + 1]:
            raise PolyMasterCertificateError(f"Companion shift failed at block {k}")
    last_blk = [[dF0[(n - 1) * d + r][c] for c in range(d)] for r in range(d)]
    if last_blk != last_row_sum:
        raise PolyMasterCertificateError("Companion last block residual mismatch")

    raw_d = cert["claimed_initial_derivs"]
    if type(raw_d) is not list or len(raw_d) != n:
        raise PolyMasterCertificateError("claimed_initial_derivs length != n")
    parsed_d = [_parse_mat(raw_d[k], d, d, f"derivs[{k}]") for k in range(n)]
    if parsed_d != derivs:
        raise PolyMasterCertificateError("claimed_initial_derivs mismatch")
    if _parse_rat(cert["claimed_companion_trace"], "claimed_companion_trace") != tr_theta:
        raise PolyMasterCertificateError("claimed_companion_trace mismatch")
    if _parse_mat(cert["claimed_companion_last_row_block_sum"], d, d, "last_row_sum") != last_row_sum:
        raise PolyMasterCertificateError("claimed_companion_last_row_block_sum mismatch")
    if cert["claimed_ode_residual_zero_at_t0"] is not True:
        raise PolyMasterCertificateError("claimed_ode_residual_zero_at_t0 must be true")

    return {
        "verified": True,
        "mode": cert["mode"],
        "d": d,
        "n": n,
        "companion_trace": format_rat(tr_theta),
    }


# =============================================================================
# Mode 2: Section IV.C & IV.F Two-Qubit Exact Critical-Parameter Factorization
# =============================================================================


def _verify_mode2_two_qubit_factorization(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "omega_S",
        "omega_E",
        "coupling_J",
        "subspace",
        "regime_label",
        "R_factor_coeffs",
        "P_tilde_coeffs",
        "Q_tilde_coeffs",
        "claimed_order_before",
        "claimed_order_after",
        "claimed_factorization_exact",
    }
    _parse_exact_keys(cert, req, "Mode 2")
    wS = _parse_rat(cert["omega_S"], "omega_S")
    wE = _parse_rat(cert["omega_E"], "omega_E")
    J = _parse_rat(cert["coupling_J"], "coupling_J")
    sub = cert["subspace"]
    if sub not in ("V12", "V3"):
        raise PolyMasterCertificateError("subspace must be 'V12' or 'V3'")
    reg = cert["regime_label"]
    if type(reg) is not str or not (1 <= len(reg) <= MAX_ID_LEN):
        raise PolyMasterCertificateError("regime_label invalid")

    if sub == "V12":
        d = 2
        P_full, Q_full = two_qubit_polys_P_Q_eq61_64(wS, wE, J)
    else:
        d = 1
        P_full, Q_full = two_qubit_V3_polys_eq64(wS, wE, J)

    ord_before = len(P_full) - 1
    raw_R = cert["R_factor_coeffs"]
    raw_Pt = cert["P_tilde_coeffs"]
    raw_Qt = cert["Q_tilde_coeffs"]
    if type(raw_R) is not list or type(raw_Pt) is not list or type(raw_Qt) is not list:
        raise PolyMasterCertificateError("Factor polynomial lists required")
    deg_R = len(raw_R) - 1
    deg_Pt = len(raw_Pt) - 1
    deg_Qt = len(raw_Qt) - 1
    if deg_R < 1 or deg_Pt < 1 or deg_Qt != deg_Pt - 1 or deg_R + deg_Pt != ord_before:
        raise PolyMasterCertificateError(
            f"Invalid non-trivial order reduction degrees: deg_R={deg_R}, deg_Pt={deg_Pt}, deg_Qt={deg_Qt}"
        )

    R_poly = _parse_mat_poly(raw_R, deg_R, d, "R_factor_coeffs")
    Pt_poly = _parse_mat_poly(raw_Pt, deg_Pt, d, "P_tilde_coeffs")
    Qt_poly = _parse_mat_poly(raw_Qt, deg_Qt, d, "Q_tilde_coeffs")

    # Enforce monic leading coefficients for R, P_tilde, Q_tilde (Eq. 21)
    I_d = mat_eye(d)
    if R_poly[-1] != I_d or Pt_poly[-1] != I_d or Qt_poly[-1] != I_d:
        raise PolyMasterCertificateError("R, P_tilde, and Q_tilde must be monic (Eq. 21)")

    # Verify exact polynomial matrix factorization P(x) = R(x) P_tilde(x) AND Q(x) = R(x) Q_tilde(x)!
    if mat_poly_mul(R_poly, Pt_poly) != P_full:
        raise PolyMasterCertificateError("Exact factorization P(x) == R(x) * P_tilde(x) failed")
    if mat_poly_mul(R_poly, Qt_poly) != Q_full:
        raise PolyMasterCertificateError("Exact factorization Q(x) == R(x) * Q_tilde(x) failed")

    if _parse_int(cert["claimed_order_before"], "claimed_order_before") != ord_before:
        raise PolyMasterCertificateError("claimed_order_before mismatch")
    if _parse_int(cert["claimed_order_after"], "claimed_order_after") != deg_Pt:
        raise PolyMasterCertificateError("claimed_order_after mismatch")
    if cert["claimed_factorization_exact"] is not True:
        raise PolyMasterCertificateError("claimed_factorization_exact must be true")

    return {
        "verified": True,
        "mode": cert["mode"],
        "subspace": sub,
        "order_before": ord_before,
        "order_after": deg_Pt,
    }


# =============================================================================
# Mode 3: Section IV.G-I Singularity & Periodicity 3-Tier Hierarchy Audit
# =============================================================================


def _verify_mode3_singularity_hierarchy(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "omega_S_sq",
        "omega_E_sq",
        "omega_SE_prod",
        "coupling_J_sq",
        "claimed_sum_cos_sq",
        "claimed_necessary_singularity_holds",
        "claimed_on_critical_boundary",
        "claimed_ratio_omega_sq",
        "claimed_ratio_is_rational",
        "claimed_ratio_q_minus",
        "claimed_ratio_q_plus",
        "claimed_tier",
    }
    _parse_exact_keys(cert, req, "Mode 3")
    wS2 = _parse_rat(cert["omega_S_sq"], "omega_S_sq")
    wE2 = _parse_rat(cert["omega_E_sq"], "omega_E_sq")
    wSE = _parse_rat(cert["omega_SE_prod"], "omega_SE_prod")
    J2 = _parse_rat(cert["coupling_J_sq"], "coupling_J_sq")
    if wS2 < 0 or wE2 < 0 or J2 <= 0:
        raise PolyMasterCertificateError("Require omega_S_sq >= 0, omega_E_sq >= 0, coupling_J_sq > 0")
    if wSE * wSE != wS2 * wE2:
        raise PolyMasterCertificateError("Consistency failed: omega_SE_prod^2 != omega_S_sq * omega_E_sq")
    if wSE < 0:
        raise PolyMasterCertificateError("Require non-negative omega_SE_prod (wS, wE >= 0)")

    # Exact D_+ = 4*Omega_+^2 = J^2 + wS^2 + wE^2 + 2*wS*wE, D_- = 4*Omega_-^2 = J^2 + wS^2 + wE^2 - 2*wS*wE
    Dp = J2 + wS2 + wE2 + Fraction(2, 1) * wSE
    Dm = J2 + wS2 + wE2 - Fraction(2, 1) * wSE
    if Dp <= 0 or Dm <= 0:
        raise PolyMasterCertificateError("Require non-vanishing singular values Omega_pm > 0")

    # Exact sum cos^2 theta_+ + cos^2 theta_- = J^2/Dp + J^2/Dm
    sum_cos_sq = J2 / Dp + J2 / Dm
    nec_holds = abs(wS2 - wE2) <= J2
    if nec_holds != (sum_cos_sq >= Fraction(1, 1)):
        raise PolyMasterCertificateError("Internal Eq. (111) equivalence mismatch")
    on_crit = abs(wS2 - wE2) == J2

    ratio_sq = Dm / Dp  # = (Omega_- / Omega_+)^2 in Q_{>0}
    rn, rd = ratio_sq.numerator, ratio_sq.denominator
    sn, sd = isqrt_exact(rn), isqrt_exact(rd)
    is_rat = (sn * sn == rn) and (sd * sd == rd)

    if is_rat:
        g = gcd_int(sn, sd)
        qm, qp = sn // g, sd // g
        if on_crit:
            if (qm % 2 == 1) and (qp % 2 == 1):
                tier = "periodic_and_singular"
            else:
                tier = "periodic_and_nonsingular"
        elif nec_holds:
            tier = "interior_periodic"
        else:
            tier = "nonsingular_periodic"
    else:
        qm, qp = 0, 0
        if on_crit:
            tier = "nonperiodic_and_nonsingular"
        elif nec_holds:
            tier = "interior_quasiperiodic"
        else:
            tier = "nonsingular_nonperiodic"

    if _parse_rat(cert["claimed_sum_cos_sq"], "claimed_sum_cos_sq") != sum_cos_sq:
        raise PolyMasterCertificateError("claimed_sum_cos_sq mismatch")
    if cert["claimed_necessary_singularity_holds"] is not nec_holds:
        raise PolyMasterCertificateError("claimed_necessary_singularity_holds mismatch")
    if cert["claimed_on_critical_boundary"] is not on_crit:
        raise PolyMasterCertificateError("claimed_on_critical_boundary mismatch")
    if _parse_rat(cert["claimed_ratio_omega_sq"], "claimed_ratio_omega_sq") != ratio_sq:
        raise PolyMasterCertificateError("claimed_ratio_omega_sq mismatch")
    if cert["claimed_ratio_is_rational"] is not is_rat:
        raise PolyMasterCertificateError("claimed_ratio_is_rational mismatch")
    if _parse_int(cert["claimed_ratio_q_minus"], "claimed_ratio_q_minus") != qm:
        raise PolyMasterCertificateError("claimed_ratio_q_minus mismatch")
    if _parse_int(cert["claimed_ratio_q_plus"], "claimed_ratio_q_plus") != qp:
        raise PolyMasterCertificateError("claimed_ratio_q_plus mismatch")
    if cert["claimed_tier"] != tier:
        raise PolyMasterCertificateError(f"claimed_tier {cert['claimed_tier']!r} != {tier!r}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "sum_cos_sq": format_rat(sum_cos_sq),
        "ratio_sq": format_rat(ratio_sq),
        "tier": tier,
    }


# =============================================================================
# Mode 4: Section V Multi-Mode Jaynes-Cummings & Exceptional-Point Jordan Audit
# =============================================================================


def _verify_mode4_jaynes_cummings(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "gamma_0",
        "lambda_bw",
        "claimed_four_eps_sq",
        "claimed_u_poly_coeffs",
        "claimed_v_poly_coeffs",
        "claimed_q_u_coeffs",
        "claimed_q_v_coeffs",
        "claimed_regime",
        "claimed_jordan_order3_nilpotent",
    }
    _parse_exact_keys(cert, req, "Mode 4")
    g0 = _parse_rat(cert["gamma_0"], "gamma_0")
    lam = _parse_rat(cert["lambda_bw"], "lambda_bw")
    if g0 <= 0 or lam <= 0:
        raise PolyMasterCertificateError("Require positive gamma_0 > 0 and lambda_bw > 0")

    # Exact 4*eps^2 = lam * (lam - 2*g0)
    four_e2 = lam * (lam - Fraction(2, 1) * g0)

    # Eq. (135): u(s) = (s + lam/2)^2 - eps^2 = s^2 + lam*s + (lam*g0)/2
    u_coeffs = [lam * g0 / Fraction(2, 1), lam, Fraction(1, 1)]
    # v(s) = (s + lam) * ((s + lam)^2 - 4*eps^2) = (s + lam) * (s^2 + 2*lam*s + 2*lam*g0)
    #      = s^3 + 3*lam*s^2 + (2*lam^2 + 2*lam*g0)*s + 2*lam^2*g0
    v_coeffs = [
        Fraction(2, 1) * lam * lam * g0,
        Fraction(2, 1) * lam * lam + Fraction(2, 1) * lam * g0,
        Fraction(3, 1) * lam,
        Fraction(1, 1),
    ]
    # Eq. (136)-(137): q_u(s) = s + lam, q_v(s) = s^2 + 3*lam*s + (2*lam^2 + lam*g0)
    qu_coeffs = [lam, Fraction(1, 1)]
    qv_coeffs = [Fraction(2, 1) * lam * lam + lam * g0, Fraction(3, 1) * lam, Fraction(1, 1)]

    # Verify IVP derivative normalization E_u(0)=1, E_u'(0)=0 and E_v(0)=1, E_v'(0)=0 via exact Eq. (24)!
    Pu_m = [[[c]] for c in u_coeffs]
    Qu_m = [[[c]] for c in qu_coeffs]
    du = compute_ivp_derivatives_eq24(Pu_m, Qu_m)
    if du[0][0][0] != Fraction(1, 1) or du[1][0][0] != Fraction(0, 1):
        raise PolyMasterCertificateError("JC u(s) IVP condition f(0)=1, f'(0)=0 failed")

    Pv_m = [[[c]] for c in v_coeffs]
    Qv_m = [[[c]] for c in qv_coeffs]
    dv = compute_ivp_derivatives_eq24(Pv_m, Qv_m)
    if dv[0][0][0] != Fraction(1, 1) or dv[1][0][0] != Fraction(0, 1):
        raise PolyMasterCertificateError("JC v(s) IVP condition f^2(0)=1, (f^2)'(0)=0 failed")

    # Classify regime and verify companion matrix nilpotency at exceptional point (eps^2 == 0)
    if four_e2 < 0:
        regime = "nonmarkovian_singular_oscillatory"
        is_ep_nilp = False
    elif four_e2 == 0:
        regime = "critical_exceptional_point"
        # Build 3x3 companion matrix Theta_v and check (Theta_v + lam*I)^3 == 0 and (Theta_v + lam*I)^2 != 0!
        Theta_v = build_companion_matrix_eq29(Pv_m)
        shifted = mat_add(Theta_v, mat_scale(lam, mat_eye(3)))
        sh2 = mat_mul(shifted, shifted)
        sh3 = mat_mul(sh2, shifted)
        if sh2 == mat_zero(3, 3) or sh3 != mat_zero(3, 3):
            raise PolyMasterCertificateError("Exceptional-point order-3 Jordan nilpotency failed")
        is_ep_nilp = True
    else:
        regime = "overdamped_nonsingular"
        is_ep_nilp = False

    if _parse_rat(cert["claimed_four_eps_sq"], "claimed_four_eps_sq") != four_e2:
        raise PolyMasterCertificateError("claimed_four_eps_sq mismatch")
    for field, expected in [
        ("claimed_u_poly_coeffs", u_coeffs),
        ("claimed_v_poly_coeffs", v_coeffs),
        ("claimed_q_u_coeffs", qu_coeffs),
        ("claimed_q_v_coeffs", qv_coeffs),
    ]:
        raw = cert[field]
        if type(raw) is not list or len(raw) != len(expected) or [_parse_rat(v, field) for v in raw] != expected:
            raise PolyMasterCertificateError(f"{field} mismatch")
    if cert["claimed_regime"] != regime:
        raise PolyMasterCertificateError(f"claimed_regime {cert['claimed_regime']!r} != {regime!r}")
    if cert["claimed_jordan_order3_nilpotent"] is not is_ep_nilp:
        raise PolyMasterCertificateError("claimed_jordan_order3_nilpotent mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "four_eps_sq": format_rat(four_e2),
        "regime": regime,
        "ep_jordan3": is_ep_nilp,
    }


def verify_poly_master_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Top-level zero-float entry point for POLY-MASTER-CERT-1.0."""
    if type(cert) is not dict:
        raise PolyMasterCertificateError("Certificate root must be a JSON object")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise PolyMasterCertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not (1 <= len(cid) <= MAX_ID_LEN):
        raise PolyMasterCertificateError(f"cert_id must be string of length in [1, {MAX_ID_LEN}]")
    mode = cert.get("mode")
    if mode == "matrix_poly_laplace_ivp_cert":
        return _verify_mode1_ivp_companion(cert)
    if mode == "two_qubit_critical_factorization_cert":
        return _verify_mode2_two_qubit_factorization(cert)
    if mode == "singularity_periodicity_hierarchy_cert":
        return _verify_mode3_singularity_hierarchy(cert)
    if mode == "jaynes_cummings_exceptional_point_cert":
        return _verify_mode4_jaynes_cummings(cert)
    raise PolyMasterCertificateError(f"Unknown verification mode: {mode!r}")
