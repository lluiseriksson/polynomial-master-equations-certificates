"""Zero-floating-point exact-Q primitives for Paper 44:
Miku Ishizaki & Jaeha Lee (arXiv:2611.33027, Nov 24, 2026)
"Polynomial Master Equations of Open Quantum Systems and an Analysis on the Critical Solutions".

Strict rule: zero floating-point arithmetic — Python fractions.Fraction only.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


def format_rat(q: Fraction) -> str:
    """Canonical reduced rational string ('n' if den == 1 else 'n/d')."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


# --- Exact Rational Matrix & Polynomial Algebra over Q ---

def mat_zero(n: int, m: int) -> List[List[Fraction]]:
    z = Fraction(0, 1)
    return [[z for _ in range(m)] for _ in range(n)]


def mat_eye(n: int) -> List[List[Fraction]]:
    M = mat_zero(n, n)
    for i in range(n):
        M[i][i] = Fraction(1, 1)
    return M


def mat_add(A: Sequence[Sequence[Fraction]], B: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mat_scale(c: Fraction, A: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    return [[c * a for a in row] for row in A]


def mat_mul(A: Sequence[Sequence[Fraction]], B: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    n, k, m = len(A), len(B), len(B[0])
    out = mat_zero(n, m)
    for i in range(n):
        for t in range(k):
            ait = A[i][t]
            if ait == 0:
                continue
            for j in range(m):
                out[i][j] += ait * B[t][j]
    return out


def mat_poly_eval_scalar(
    coeffs: Sequence[Sequence[Sequence[Fraction]]],
    x: Fraction,
) -> List[List[Fraction]]:
    """Evaluate matrix polynomial P(x) = sum_{k=0}^n P_k x^k at rational scalar x."""
    d = len(coeffs[0])
    acc = mat_zero(d, d)
    xp = Fraction(1, 1)
    for Pk in coeffs:
        acc = mat_add(acc, mat_scale(xp, Pk))
        xp *= x
    return acc


def mat_poly_mul(
    A: Sequence[Sequence[Sequence[Fraction]]],
    B: Sequence[Sequence[Sequence[Fraction]]],
) -> List[List[List[Fraction]]]:
    """Exact product of two matrix polynomials over Q[x]: (A*B)_m = sum_{i+j=m} A_i B_j."""
    d = len(A[0])
    deg_a = len(A) - 1
    deg_b = len(B) - 1
    out = [mat_zero(d, d) for _ in range(deg_a + deg_b + 1)]
    for i, Ai in enumerate(A):
        for j, Bj in enumerate(B):
            out[i + j] = mat_add(out[i + j], mat_mul(Ai, Bj))
    return out


def compute_ivp_derivatives_eq24(
    P_coeffs: Sequence[Sequence[Sequence[Fraction]]],
    Q_coeffs: Sequence[Sequence[Sequence[Fraction]]],
) -> List[List[List[Fraction]]]:
    """Exact Section III.B Eqs. (24)-(26) initial derivatives E^{(k)}(0) for k = 0..n-1:
    P(x) = sum_{k=0}^n P_k x^k (monic: P_n = I_d), Q(x) = sum_{j=0}^{n-1} Q_j x^j.
    Block matrix T_{ij} = P_{n+i-j} for 1 <= i < j <= n (0-indexed: T[i][j] = P_{n+i-j} for i < j).
    P_tilde = sum_{r=0}^{n-1} (-T)^r = (I + T)^{-1}.
    E^{(k)}(0) = sum_{j=1}^n P_tilde[n-1-k][j-1] Q_{j-1}.
    """
    n = len(P_coeffs) - 1
    d = len(P_coeffs[0])
    assert len(Q_coeffs) == n
    # Build block strictly upper triangular matrix T of size (n*d) x (n*d)
    N = n * d
    T = mat_zero(N, N)
    for i in range(n):
        for j in range(i + 1, n):
            idx = n + i - j  # in 1..n-1
            blk = P_coeffs[idx]
            for r in range(d):
                for c in range(d):
                    T[i * d + r][j * d + c] = blk[r][c]

    # P_tilde = sum_{k=0}^{n-1} (-T)^k
    neg_T = mat_scale(Fraction(-1, 1), T)
    P_tilde = mat_eye(N)
    cur = mat_eye(N)
    for _ in range(1, n):
        cur = mat_mul(cur, neg_T)
        P_tilde = mat_add(P_tilde, cur)

    # E^{(k)}(0) = sum_{j=0}^{n-1} P_tilde_block[n - 1 - k][j] @ Q_coeffs[j]
    derivs: List[List[List[Fraction]]] = []
    for k in range(n):
        row_blk = n - 1 - k
        acc = mat_zero(d, d)
        for j in range(n):
            blk = [
                [P_tilde[row_blk * d + r][j * d + c] for c in range(d)]
                for r in range(d)
            ]
            acc = mat_add(acc, mat_mul(blk, Q_coeffs[j]))
        derivs.append(acc)
    return derivs


def build_companion_matrix_eq29(
    P_coeffs: Sequence[Sequence[Sequence[Fraction]]],
) -> List[List[Fraction]]:
    """Exact Section III.C Eq. (29) Frobenius companion matrix Theta of monic P(x)."""
    n = len(P_coeffs) - 1
    d = len(P_coeffs[0])
    N = n * d
    Theta = mat_zero(N, N)
    for i in range(n - 1):
        for r in range(d):
            Theta[i * d + r][(i + 1) * d + r] = Fraction(1, 1)
    for j in range(n):
        neg_Pj = mat_scale(Fraction(-1, 1), P_coeffs[j])
        for r in range(d):
            for c in range(d):
                Theta[(n - 1) * d + r][j * d + c] = neg_Pj[r][c]
    return Theta


def two_qubit_polys_P_Q_eq61_64(
    wS: Fraction, wE: Fraction, J: Fraction
) -> Tuple[List[List[List[Fraction]]], List[List[List[Fraction]]]]:
    """Exact Section IV.C Eqs. (61)-(64) 4x4 block-diagonal monic matrix polynomials:
      V_0:  P_0(x) = x, Q_0(x) = 1
      V_12: P_12(x) = (x^2 + zeta_-^2)(x^2 + zeta_+^2) I_2, Q_12(x) (Eq. 62, degree 3)
            Note: zeta_-^2 + zeta_+^2 = J^2 + wS^2 + wE^2,
                  zeta_-^2 * zeta_+^2 = wS^2 * wE^2? Wait — check exact algebra!
      Let's compute zeta_pm^2 = (Omega_+ +- Omega_-)^2 = Omega_+^2 + Omega_-^2 +- 2 Omega_+ Omega_-!
      Wait: 4*Omega_pm^2 = J^2 + (wS +- wE)^2.
      So Omega_+^2 + Omega_-^2 = (J^2 + wS^2 + wE^2) / 2.
      And zeta_+^2 + zeta_-^2 = 2*(Omega_+^2 + Omega_-^2) = J^2 + wS^2 + wE^2!
      And zeta_+^2 * zeta_-^2 = (Omega_+^2 - Omega_-^2)^2 = (wS * wE)^2 = wS^2 * wE^2!
      YES!! Purely rational in (wS, wE, J) with ZERO square roots!
      V_3:  P_3(x) = x(x^2 + 4*Omega_+^2)(x^2 + 4*Omega_-^2) (degree 5),
            Q_3(x) = (x^2 + eta_-^2)(x^2 + eta_+^2) (degree 4)!
            Note: 4*Omega_+^2 + 4*Omega_-^2 = 2*(J^2 + wS^2 + wE^2),
                  (4*Omega_+^2)*(4*Omega_-^2) = (J^2 + wS^2 + wE^2)^2 - 4*wS^2*wE^2,
                  eta_+^2 + eta_-^2 = J^2 + 2*(wS^2 + wE^2),
                  eta_+^2 * eta_-^2 = J^2*(wS^2 + wE^2) + (wS^2 - wE^2)^2!
    Returns (P_12_coeffs, Q_12_coeffs) for V_12, and separately scalar poly helper below.
    """
    z0 = Fraction(0, 1)
    one = Fraction(1, 1)
    j2, s2, e2 = J * J, wS * wS, wE * wE

    # V_12: P_12(x) = (x^4 + (j2 + s2 + e2) x^2 + s2*e2) I_2
    c2_12 = j2 + s2 + e2
    c0_12 = s2 * e2
    P12 = [
        [[c0_12, z0], [z0, c0_12]],
        mat_zero(2, 2),
        [[c2_12, z0], [z0, c2_12]],
        mat_zero(2, 2),
        mat_eye(2),
    ]
    # Q_12(x) from Eq. (62):
    #   Q12[0,0] = x(x^2 + j2 + e2) = (j2+e2) x + x^3
    #   Q12[0,1] = -wS(x^2 + e2)  [wait: check sign! (LE)^{-1} has +wS at (1,2) and -wS at (2,1),
    #              so b12 = -wS(s^2+e2)/denom and b21 = +wS(s^2+e2)/denom in Eq. (55)!
    #              Wait: Eq. (62) has +wS at (1,2) vs Eq. (55) has -wS at (1,2) — let's verify against Eq. (74):
    #              E^{(1)}_{12}(0) = [[0, -wS], [wS, 0]] = Q_{12,2}! Since P_12 is even (P_3 = 0),
    #              E^{(1)}_{12}(0) = Q_{12, 2}! So Q12[0,1] = -wS(x^2 + e2), Q12[1,0] = +wS(x^2 + e2)!]
    Q12 = [
        [[z0, -wS * e2], [wS * e2, z0]],
        [[j2 + e2, z0], [z0, e2]],
        [[z0, -wS], [wS, z0]],
        [[one, z0], [z0, one]],
    ]
    return P12, Q12


def two_qubit_V3_polys_eq64(
    wS: Fraction, wE: Fraction, J: Fraction
) -> Tuple[List[List[List[Fraction]]], List[List[List[Fraction]]]]:
    """Exact 1x1 matrix polynomials P_3(x) (deg 5) and Q_3(x) (deg 4) from Eq. (64)."""
    z0 = Fraction(0, 1)
    one = Fraction(1, 1)
    j2, s2, e2 = J * J, wS * wS, wE * wE
    sig = j2 + s2 + e2
    p3_1 = sig * sig - Fraction(4, 1) * s2 * e2
    p3_3 = Fraction(2, 1) * sig
    P3 = [[[z0]], [[p3_1]], [[z0]], [[p3_3]], [[z0]], [[one]]]

    q3_0 = j2 * (s2 + e2) + (s2 - e2) * (s2 - e2)
    q3_2 = j2 + Fraction(2, 1) * (s2 + e2)
    Q3 = [[[q3_0]], [[z0]], [[q3_2]], [[z0]], [[one]]]
    return P3, Q3


def isqrt_exact(n: int) -> int:
    """Exact integer floor sqrt without floating-point arithmetic."""
    if n < 0:
        raise ValueError("negative")
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y


def gcd_int(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a
