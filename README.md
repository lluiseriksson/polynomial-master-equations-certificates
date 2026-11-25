# Certified Verification of Polynomial Master Equations and Critical Solutions in Open Quantum Systems

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact-$\mathbb{Q}$ certificate audit (`POLY-MASTER-CERT-1.0`) for **Miku Ishizaki & Jaeha Lee** ([arXiv:2611.33027](https://arxiv.org/abs/2611.33027), Nov 24, 2026), *"Polynomial Master Equations of Open Quantum Systems and an Analysis on the Critical Solutions"*.

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/PolyMasterEq.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`3` `none`, `1` `[propext]`, `14` `[propext, Quot.sound]`) |
| **Exact-$\mathbb{Q}$ Verifier** (`src/master_certifier.py`) | Zero `float()`, `math`, or `numpy`; 4-mode `POLY-MASTER-CERT-1.0` | **16 / 16 PASS** (`0.046–0.648 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 60 live forged payloads (12 global + 12/mode) | **60 / 60 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **41 / 41 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`POLY-MASTER-CERT-1.0`)

1. **`matrix_poly_laplace_ivp_cert` (Mode 1 — Section III):** Verifies monic matrix-polynomial pairs $(P(x), Q(x))$, independently computes the block upper-triangular inverse $\tilde{P} = \sum_{k=0}^{n-1} (-T)^k$ and exact initial derivatives $E^{(k)}(0)$ (Eqs. 24–26), checks $E(0) = I_d$, and certifies exact Frobenius companion matrix $\Theta$ action (Eq. 29).
2. **`two_qubit_critical_factorization_cert` (Mode 2 — Section IV.C & IV.F):** Constructs exact two-qubit block polynomials $(P_{12}, Q_{12})$ and $(P_3, Q_3)$ over $\mathbb{Q}$ and verifies exact monic polynomial matrix factorizations $P(x) = R(x)\tilde{P}(x)$ and $Q(x) = R(x)\tilde{Q}(x)$ across all four critical order-reduction regimes ($4 \to 1$ Liouville–von Neumann, $5 \to 1$, $5 \to 3$, $5 \to 2$).
3. **`singularity_periodicity_hierarchy_cert` (Mode 3 — Section IV.G–I):** Certifies the necessary singularity criterion $\sum_\pm \cos^2 \theta_\pm \ge 1 \iff |\omega_S^2 - \omega_E^2| \le J^2$ and classifies the 3-tier critical-boundary hierarchy via exact integer square-root rationality and odd/even parity tests (Tier 1 Periodic & Singular `(5,4,3)`, Tier 2 Periodic & Non-Singular `(5,3,4)`, Tier 3 Non-Periodic & Non-Singular irrational boundary `r^2 = 1/5`, and Exterior Non-Singular).
4. **`jaynes_cummings_exceptional_point_cert` (Mode 4 — Section V):** Verifies exact rational Jaynes–Cummings polynomials $u(s), v(s), q_u(s), q_v(s)$, checks exact IVP conditions $f(0) = 1, f'(0) = 0$, classifies the three regimes ($\lambda < 2\gamma_0$ non-Markovian singular, $\lambda = 2\gamma_0$ critical exceptional point, $\lambda > 2\gamma_0$ overdamped), and directly verifies order-3 Jordan nilpotency $(\Theta_v + \lambda I)^3 = 0, (\Theta_v + \lambda I)^2 \ne 0$ at the exceptional point!

---

## Quick Reproduction

```bash
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

---

## Licenses & Transparency Disclosure

- **Code, Lean proofs, certificates, and scripts:** [MIT License](LICENSE).
- **Manuscript (`paper/main.tex`, `paper/main.pdf`) and figures:** CC-BY-4.0.
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact-$\mathbb{Q}$ certificates, and adversarial tests were independently compiled and machine-verified locally.
