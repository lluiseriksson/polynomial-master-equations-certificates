"""Comprehensive pytest & 60-attack live adversarial red-team suite for Paper 44:
POLY-MASTER-CERT-1.0 (Ishizaki & Lee, arXiv:2611.33027).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.master_certifier import PolyMasterCertificateError, verify_poly_master_certificate_exact

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    paths = sorted(CERT_DIR.glob("*.json"))
    assert len(paths) == 16, f"Expected 16 certificates, found {len(paths)}"
    for p in paths:
        res = verify_poly_master_certificate_exact(json.loads(p.read_text(encoding="utf-8")))
        assert res["verified"] is True


def _mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_60_adversarial_attacks() -> List[Tuple[str, Any]]:
    m1 = _load("m1_ivp_twoqubit_V12_5_4_3")
    m2 = _load("m2_crit_J0_V12_lvn_order4_to_1")
    m3 = _load("m3_tier1_periodic_singular_5_4_3")
    m4 = _load("m4_jc_exceptional_point_g2_l4")

    attacks: List[Tuple[str, Any]] = [
        # --- Global Schema / Type / Rational / Depth Hardening (12 attacks) ---
        ("g01_non_dict_root", [1, 2, 3]),
        ("g02_wrong_schema", _mut(m1, lambda c: c.__setitem__("schema", "POLY-MASTER-CERT-2.0"))),
        ("g03_empty_cert_id", _mut(m1, lambda c: c.__setitem__("cert_id", ""))),
        ("g04_unknown_mode", _mut(m1, lambda c: c.__setitem__("mode", "bogus"))),
        ("g05_float_leak", _mut(m4, lambda c: c.__setitem__("gamma_0", 2.0))),
        ("g06_none_injection", _mut(m1, lambda c: c.__setitem__("order_n", None))),
        ("g07_bool_as_int", _mut(m1, lambda c: c.__setitem__("block_dim_d", True))),
        ("g08_unreduced_fraction", _mut(m4, lambda c: c.__setitem__("gamma_0", "4/2"))),
        ("g09_den_one_fraction", _mut(m4, lambda c: c.__setitem__("gamma_0", "2/1"))),
        ("g10_trailing_newline_rat", _mut(m4, lambda c: c.__setitem__("gamma_0", "2\n"))),
        ("g11_oversized_rat_str", _mut(m4, lambda c: c.__setitem__("gamma_0", "1/" + "9" * 1200))),
        ("g12_json_depth_dos", _mut(m1, lambda c: c.__setitem__("P_coeffs", eval("[" * 40 + "0" + "]" * 40)))),
        # --- Mode 1: Sec. III Matrix-Polynomial IVP & Companion Matrix (12 attacks) ---
        ("m1_01_extra_key", _mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("m1_02_non_monic_P", _mut(m1, lambda c: c["P_coeffs"][-1][0].__setitem__(0, "2"))),
        ("m1_03_non_monic_Q", _mut(m1, lambda c: c["Q_coeffs"][-1][0].__setitem__(0, "2"))),
        ("m1_04_wrong_P_len", _mut(m1, lambda c: c["P_coeffs"].pop())),
        ("m1_05_wrong_Q_len", _mut(m1, lambda c: c["Q_coeffs"].pop())),
        ("m1_06_bad_dim_zero", _mut(m1, lambda c: c.__setitem__("block_dim_d", 0))),
        ("m1_07_bad_order_seven", _mut(m1, lambda c: c.__setitem__("order_n", 7))),
        ("m1_08_wrong_init_deriv", _mut(m1, lambda c: c["claimed_initial_derivs"][1][0].__setitem__(1, "0"))),
        ("m1_09_wrong_derivs_len", _mut(m1, lambda c: c["claimed_initial_derivs"].pop())),
        ("m1_10_wrong_comp_trace", _mut(m1, lambda c: c.__setitem__("claimed_companion_trace", "1"))),
        ("m1_11_wrong_last_row_sum", _mut(m1, lambda c: c["claimed_companion_last_row_block_sum"][0].__setitem__(0, "0"))),
        ("m1_12_ode_res_false", _mut(m1, lambda c: c.__setitem__("claimed_ode_residual_zero_at_t0", False))),
        # --- Mode 2: Sec. IV.F Two-Qubit Critical Factorization (12 attacks) ---
        ("m2_01_extra_key", _mut(m2, lambda c: c.__setitem__("extra", 1))),
        ("m2_02_bad_subspace", _mut(m2, lambda c: c.__setitem__("subspace", "V0"))),
        ("m2_03_empty_regime", _mut(m2, lambda c: c.__setitem__("regime_label", ""))),
        ("m2_04_non_monic_R", _mut(m2, lambda c: c["R_factor_coeffs"][-1][0].__setitem__(0, "2"))),
        ("m2_05_non_monic_Ptilde", _mut(m2, lambda c: c["P_tilde_coeffs"][-1][0].__setitem__(0, "2"))),
        ("m2_06_wrong_P_product", _mut(m2, lambda c: c["P_tilde_coeffs"][0][0].__setitem__(1, "0"))),
        ("m2_07_wrong_Q_product", _mut(m2, lambda c: c["R_factor_coeffs"][0][0].__setitem__(1, "0"))),
        ("m2_08_nonzero_J_breaks_J0", _mut(m2, lambda c: c.__setitem__("coupling_J", "1"))),
        ("m2_09_trivial_deg_R_zero", _mut(m2, lambda c: c.__setitem__("R_factor_coeffs", [[["1", "0"], ["0", "1"]]]))),
        ("m2_10_wrong_order_before", _mut(m2, lambda c: c.__setitem__("claimed_order_before", 3))),
        ("m2_11_wrong_order_after", _mut(m2, lambda c: c.__setitem__("claimed_order_after", 2))),
        ("m2_12_factor_exact_false", _mut(m2, lambda c: c.__setitem__("claimed_factorization_exact", False))),
        # --- Mode 3: Sec. IV.G-I Singularity & Periodicity Hierarchy (12 attacks) ---
        ("m3_01_extra_key", _mut(m3, lambda c: c.__setitem__("extra", 1))),
        ("m3_02_zero_J_sq", _mut(m3, lambda c: c.__setitem__("coupling_J_sq", "0"))),
        ("m3_03_neg_wS_sq", _mut(m3, lambda c: c.__setitem__("omega_S_sq", "-1"))),
        ("m3_04_inconsistent_wSE", _mut(m3, lambda c: c.__setitem__("omega_SE_prod", "19"))),
        ("m3_05_neg_wSE", _mut(m3, lambda c: c.__setitem__("omega_SE_prod", "-20"))),
        ("m3_06_wrong_sum_cos_sq", _mut(m3, lambda c: c.__setitem__("claimed_sum_cos_sq", "2"))),
        ("m3_07_wrong_nec_flag", _mut(m3, lambda c: c.__setitem__("claimed_necessary_singularity_holds", False))),
        ("m3_08_wrong_crit_flag", _mut(m3, lambda c: c.__setitem__("claimed_on_critical_boundary", False))),
        ("m3_09_wrong_ratio_sq", _mut(m3, lambda c: c.__setitem__("claimed_ratio_omega_sq", "1/4"))),
        ("m3_10_wrong_is_rat", _mut(m3, lambda c: c.__setitem__("claimed_ratio_is_rational", False))),
        ("m3_11_wrong_q_plus", _mut(m3, lambda c: c.__setitem__("claimed_ratio_q_plus", 2))),
        ("m3_12_wrong_tier", _mut(m3, lambda c: c.__setitem__("claimed_tier", "periodic_and_nonsingular"))),
        # --- Mode 4: Sec. V Jaynes-Cummings & Exceptional Point (12 attacks) ---
        ("m4_01_extra_key", _mut(m4, lambda c: c.__setitem__("extra", 1))),
        ("m4_02_zero_gamma0", _mut(m4, lambda c: c.__setitem__("gamma_0", "0"))),
        ("m4_03_neg_lambda", _mut(m4, lambda c: c.__setitem__("lambda_bw", "-4"))),
        ("m4_04_wrong_four_eps_sq", _mut(m4, lambda c: c.__setitem__("claimed_four_eps_sq", "1"))),
        ("m4_05_wrong_u_poly", _mut(m4, lambda c: c["claimed_u_poly_coeffs"].__setitem__(0, "1"))),
        ("m4_06_wrong_u_len", _mut(m4, lambda c: c["claimed_u_poly_coeffs"].pop())),
        ("m4_07_wrong_v_poly", _mut(m4, lambda c: c["claimed_v_poly_coeffs"].__setitem__(0, "1"))),
        ("m4_08_wrong_qu_poly", _mut(m4, lambda c: c["claimed_q_u_coeffs"].__setitem__(0, "1"))),
        ("m4_09_wrong_qv_poly", _mut(m4, lambda c: c["claimed_q_v_coeffs"].__setitem__(0, "1"))),
        ("m4_10_wrong_regime", _mut(m4, lambda c: c.__setitem__("claimed_regime", "overdamped_nonsingular"))),
        ("m4_11_wrong_jordan_flag", _mut(m4, lambda c: c.__setitem__("claimed_jordan_order3_nilpotent", False))),
        ("m4_12_huge_int_bitlen", _mut(m4, lambda c: c.__setitem__("gamma_0", 1 << 3000))),
    ]
    assert len(attacks) == 60
    return attacks


def test_60_live_adversarial_attacks_rejected() -> None:
    attacks = build_60_adversarial_attacks()
    rejected = 0
    for name, payload in attacks:
        try:
            verify_poly_master_certificate_exact(payload)
        except PolyMasterCertificateError:
            rejected += 1
        else:
            raise AssertionError(f"Adversarial attack {name!r} was NOT rejected!")
    assert rejected == 60


def test_exact_no_float_source_audit() -> None:
    for rel in ["src/master_exact.py", "src/master_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        assert "float(" not in src, f"float() found in {rel}"
        assert "math." not in src, f"math. found in {rel}"
        assert "numpy" not in src, f"numpy found in {rel}"
