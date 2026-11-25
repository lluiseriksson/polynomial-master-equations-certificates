/-
  Paper 44: Zero-Dependency Constructive Lean 4.35.0 Kernel for
  Miku Ishizaki & Jaeha Lee (arXiv:2611.33027, Nov 24, 2026):
  "Polynomial Master Equations of Open Quantum Systems and an Analysis on the Critical Solutions"

  Author: Lluis Eriksson
  License: MIT
  Axiom budget: ZERO sorry, ZERO warnings, ZERO Classical.choice, ZERO Lean.ofReduceBool.
-/

namespace PolyMasterEq

/-- Decidable integer absolute value without `Classical.choice`. -/
def iabs (x : Int) : Int :=
  if x < 0 then -x else x

/-- Theorem 1 (Section IV.B Singular-Value Squared Sum & Difference Identities):
    For `4*Ω_+^2 = J^2 + (ωS + ωE)^2` and `4*Ω_-^2 = J^2 + (ωS - ωE)^2`,
    `4*Ω_+^2 + 4*Ω_-^2 = 2*(J^2 + ωS^2 + ωE^2)` and
    `4*Ω_+^2 - 4*Ω_-^2 = 4*(ωS * ωE)`! -/
theorem two_qubit_omega_sq_sum_and_diff (J wS wE : Int) :
    ((J * J + (wS + wE) * (wS + wE)) + (J * J + (wS - wE) * (wS - wE)) =
      2 * (J * J + wS * wS + wE * wE)) ∧
    ((J * J + (wS + wE) * (wS + wE)) - (J * J + (wS - wE) * (wS - wE)) =
      4 * (wS * wE)) := by
  have h1 : (wS + wE) * (wS + wE) = wS * wS + 2 * (wS * wE) + wE * wE := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm wE wS]; omega
  have h2 : (wS - wE) * (wS - wE) = wS * wS - 2 * (wS * wE) + wE * wE := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm wE wS]; omega
  constructor <;> omega

/-- Theorem 2 (Section IV.B Eq. 45–46 Product `4*Ω_+^2 * 4*Ω_-^2` Expansion):
    `(J^2 + (wS + wE)^2) * (J^2 + (wS - wE)^2) = (J^2 + wS^2 + wE^2)^2 - 4*(wS^2 * wE^2)`. -/
theorem two_qubit_omega_sq_product (J wS wE : Int) :
    (J * J + (wS + wE) * (wS + wE)) * (J * J + (wS - wE) * (wS - wE)) =
      (J * J + wS * wS + wE * wE) * (J * J + wS * wS + wE * wE) -
      (2 * (wS * wE)) * (2 * (wS * wE)) := by
  have h1 : (wS + wE) * (wS + wE) = (wS * wS + wE * wE) + 2 * (wS * wE) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm wE wS]; omega
  have h2 : (wS - wE) * (wS - wE) = (wS * wS + wE * wE) - 2 * (wS * wE) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm wE wS]; omega
  have hdiff : ∀ A B : Int, (A + B) * (A - B) = A * A - B * B := by
    intro A B
    rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm B A]; omega
  have ha : J * J + (wS + wE) * (wS + wE) = (J * J + wS * wS + wE * wE) + 2 * (wS * wE) := by omega
  have hb : J * J + (wS - wE) * (wS - wE) = (J * J + wS * wS + wE * wE) - 2 * (wS * wE) := by omega
  rw [ha, hb, hdiff]

/-- Helper algebraic identity `(a + b)^2 = a^2 + 2ab + b^2`. -/
private theorem sq_add_int (a b : Int) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]; omega

/-- Helper algebraic identity for Vieta expansion in Theorem 3. -/
private theorem eta_vieta_helper (j2 s2 e2 : Int) :
    (j2 + 2 * (s2 + e2)) * (j2 + 2 * (s2 + e2)) - (j2 * j2 + 16 * (s2 * e2)) =
      4 * (j2 * (s2 + e2) + (s2 - e2) * (s2 - e2)) := by
  have hsq1 : (j2 + 2 * (s2 + e2)) * (j2 + 2 * (s2 + e2)) =
      j2 * j2 + 4 * (j2 * (s2 + e2)) + 4 * ((s2 + e2) * (s2 + e2)) := by
    rw [sq_add_int j2 (2 * (s2 + e2))]
    have ha1 : j2 * (2 * (s2 + e2)) = 2 * (j2 * (s2 + e2)) := by
      rw [← Int.mul_assoc, Int.mul_comm j2 2, Int.mul_assoc]
    have ha2 : (2 * (s2 + e2)) * (2 * (s2 + e2)) = 4 * ((s2 + e2) * (s2 + e2)) := by
      calc (2 * (s2 + e2)) * (2 * (s2 + e2))
          = 2 * ((s2 + e2) * (2 * (s2 + e2))) := Int.mul_assoc _ _ _
        _ = 2 * (2 * ((s2 + e2) * (s2 + e2))) := by
              rw [← Int.mul_assoc (s2 + e2) 2, Int.mul_comm (s2 + e2) 2, Int.mul_assoc]
        _ = (2 * 2) * ((s2 + e2) * (s2 + e2)) := (Int.mul_assoc _ _ _).symm
        _ = 4 * ((s2 + e2) * (s2 + e2)) := rfl
    omega
  have hsq2 : (s2 + e2) * (s2 + e2) - (s2 - e2) * (s2 - e2) = 4 * (s2 * e2) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm e2 s2]
    omega
  omega

/-- Theorem 3 (Section IV.C Eq. 49 Spectral Identity `η_+^2 + η_-^2` and `η_+^2 * η_-^2`):
    For `A = J^2 + 2*(wS^2 + wE^2)` and `R^2 = J^4 + 16*(wS^2 * wE^2)`,
    `(A + R) + (A - R) = 2*A` and `(A + R)*(A - R) = 4*(J^2*(wS^2 + wE^2) + (wS^2 - wE^2)^2)`! -/
theorem two_qubit_eta_vieta_identities (J wS wE R : Int)
    (hR : R * R = J * J * (J * J) + 16 * ((wS * wS) * (wE * wE))) :
    let A := J * J + 2 * (wS * wS + wE * wE)
    ((A + R) + (A - R) = 2 * A) ∧
    ((A + R) * (A - R) =
      4 * (J * J * (wS * wS + wE * wE) + (wS * wS - wE * wE) * (wS * wS - wE * wE))) := by
  dsimp only
  constructor
  · omega
  · have hdiff : (J * J + 2 * (wS * wS + wE * wE) + R) * (J * J + 2 * (wS * wS + wE * wE) - R) =
        (J * J + 2 * (wS * wS + wE * wE)) * (J * J + 2 * (wS * wS + wE * wE)) - R * R := by
      rw [Int.add_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm R]; omega
    rw [hdiff, hR]
    exact eta_vieta_helper (J * J) (wS * wS) (wE * wE)

/-- Theorem 4 (Section IV.C Eq. 51 Residue Weights `p_+ + p_- = 1`):
    Cleared by `2 * R`: `(R + J^2) + (R - J^2) = 2 * R`. -/
theorem two_qubit_residue_weights_sum_one (R J2 : Int) :
    (R + J2) + (R - J2) = 2 * R := by
  omega

/-- Exact degree of a non-empty univariate integer polynomial represented in ascending powers. -/
def polyDeg (p : List Int) : Nat :=
  p.length - 1

/-- Multiply polynomial `p` by scalar `c`. -/
def polyScale (c : Int) : List Int → List Int
  | [] => []
  | a :: as => (c * a) :: polyScale c as

/-- Add two univariate integer polynomials in ascending powers. -/
def polyAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: polyAdd as bs

/-- Exact univariate polynomial multiplication over `Int[x]`. -/
def polyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, q => polyAdd (polyScale a q) (0 :: polyMul as q)

/-- Exact 4×4 matrix multiplication over `Int`. -/
def mat4Mul (A B : Fin 4 → Fin 4 → Int) : Fin 4 → Fin 4 → Int :=
  fun i j => A i ⟨0, by decide⟩ * B ⟨0, by decide⟩ j + A i ⟨1, by decide⟩ * B ⟨1, by decide⟩ j +
             A i ⟨2, by decide⟩ * B ⟨2, by decide⟩ j + A i ⟨3, by decide⟩ * B ⟨3, by decide⟩ j

/-- 4×4 identity matrix over `Int`. -/
def mat4Id (i j : Fin 4) : Int :=
  if i.val == j.val then 1 else 0

/-- Section V.C Eq. (126) global similarity involution `T`. -/
def jcSimT (i j : Fin 4) : Int :=
  match i.val, j.val with
  | 0, 0 => -1
  | 1, 1 => 1
  | 2, 2 => 1
  | 3, 0 => 1
  | 3, 3 => 1
  | _, _ => 0

/-- Section V.B Eq. (123) Jaynes–Cummings dynamical map `E_ε(t)` parameterized by `f = f_ε(t)`. -/
def jcDynE (f : Int) (i j : Fin 4) : Int :=
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 1 => f
  | 2, 2 => f
  | 3, 0 => f * f - 1
  | 3, 3 => f * f
  | _, _ => 0

/-- Diagonal 4×4 matrix `diag(d0, d1, d2, d3)`. -/
def jcDiag4 (d0 d1 d2 d3 : Int) (i j : Fin 4) : Int :=
  match i.val, j.val with
  | 0, 0 => d0
  | 1, 1 => d1
  | 2, 2 => d2
  | 3, 3 => d3
  | _, _ => 0

/-- Exact 3×3 matrix multiplication over `Int`. -/
def mat3Mul (A B : Fin 3 → Fin 3 → Int) : Fin 3 → Fin 3 → Int :=
  fun i j => A i ⟨0, by decide⟩ * B ⟨0, by decide⟩ j + A i ⟨1, by decide⟩ * B ⟨1, by decide⟩ j +
             A i ⟨2, by decide⟩ * B ⟨2, by decide⟩ j

/-- Shifted 3×3 companion matrix `Θ_v + λ I_3` for `v(s) = (s + λ)^3 = s^3 + 3λ s^2 + 3λ^2 s + λ^3`
    at the Jaynes–Cummings exceptional point `λ = 2γ_0`. -/
def jcShiftedCompanionEP (lam : Int) (i j : Fin 3) : Int :=
  match i.val, j.val with
  | 0, 0 => lam
  | 0, 1 => 1
  | 1, 1 => lam
  | 1, 2 => 1
  | 2, 0 => -(lam * lam * lam)
  | 2, 1 => -(3 * (lam * lam))
  | 2, 2 => -(2 * lam)
  | _, _ => 0

/-- Theorem 5 (Section IV.C Eq. 61–64 Exact Monic Matrix-Polynomial Degree Budget):
    Constructs the actual `List Int` polynomials `P_0, Q_0, P_{12}, Q_{12}, P_3, Q_3`
    for arbitrary `(J, wS, wE)` and certifies `polyDeg P_i = polyDeg Q_i + 1` on every block! -/
theorem two_qubit_poly_order_budget (J wS wE : Int) :
    let j2 := J * J
    let s2 := wS * wS
    let e2 := wE * wE
    let sig := j2 + s2 + e2
    let P0 : List Int := [0, 1]
    let Q0 : List Int := [1]
    let P12 : List Int := [s2 * e2, 0, sig, 0, 1]
    let Q12 : List Int := [0, j2 + e2, 0, 1]
    let P3 : List Int := [0, sig * sig - 4 * (s2 * e2), 0, 2 * sig, 0, 1]
    let Q3 : List Int := [j2 * (s2 + e2) + (s2 - e2) * (s2 - e2), 0, j2 + 2 * (s2 + e2), 0, 1]
    polyDeg P0 = polyDeg Q0 + 1 ∧
    polyDeg P12 = polyDeg Q12 + 1 ∧
    polyDeg P3 = polyDeg Q3 + 1 ∧
    polyDeg P0 = 1 ∧ polyDeg P12 = 4 ∧ polyDeg P3 = 5 := by
  dsimp only [polyDeg, List.length]
  decide

/-- Helper algebraic identity for Theorem 6 singularity criterion. -/
private theorem singularity_helper (j2 s2 e2 : Int) :
    j2 * (2 * (j2 + s2 + e2)) - ((j2 + s2 + e2) * (j2 + s2 + e2) - 4 * (s2 * e2)) =
      j2 * j2 - (s2 - e2) * (s2 - e2) := by
  have h1 : j2 * (2 * (j2 + s2 + e2)) = 2 * (j2 * j2) + 2 * (j2 * (s2 + e2)) := by
    have hsplit : j2 + s2 + e2 = j2 + (s2 + e2) := by omega
    rw [hsplit, ← Int.mul_assoc, Int.mul_comm j2 2, Int.mul_assoc, Int.mul_add]
    omega
  have h2 : (j2 + s2 + e2) * (j2 + s2 + e2) =
      j2 * j2 + 2 * (j2 * (s2 + e2)) + (s2 + e2) * (s2 + e2) := by
    have hsplit : j2 + s2 + e2 = j2 + (s2 + e2) := by omega
    rw [hsplit, sq_add_int j2 (s2 + e2)]
  have h3 : (s2 + e2) * (s2 + e2) - 4 * (s2 * e2) = (s2 - e2) * (s2 - e2) := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm e2 s2]
    omega
  omega

/-- Theorem 6 (Section IV.G Eq. 111 Exact Necessary Singularity Criterion `∑ cos^2 θ_± ≥ 1 ↔ |ωS^2 - ωE^2| ≤ J^2`):
    Cleared by `D_+ * D_- > 0` where `D_± = J^2 + (ωS ± ωE)^2` and `cos^2 θ_± = J^2 / D_±`:
    `J^2 * (D_+ + D_-) - D_+ * D_- = J^4 - (ωS^2 - ωE^2)^2`! -/
theorem two_qubit_singularity_criterion_exact (J wS wE : Int) :
    let Dp := J * J + (wS + wE) * (wS + wE)
    let Dm := J * J + (wS - wE) * (wS - wE)
    J * J * (Dp + Dm) - Dp * Dm = (J * J) * (J * J) - (wS * wS - wE * wE) * (wS * wS - wE * wE) := by
  dsimp only
  have hsum := (two_qubit_omega_sq_sum_and_diff J wS wE).1
  have hprod := two_qubit_omega_sq_product J wS wE
  rw [hsum, hprod]
  have h4se : (2 * (wS * wE)) * (2 * (wS * wE)) = 4 * ((wS * wS) * (wE * wE)) := by
    have hsq : (wS * wE) * (wS * wE) = (wS * wS) * (wE * wE) := by
      calc (wS * wE) * (wS * wE) = wS * (wE * (wS * wE)) := Int.mul_assoc _ _ _
        _ = wS * ((wE * wS) * wE) := by rw [← Int.mul_assoc wE wS wE]
        _ = wS * ((wS * wE) * wE) := by rw [Int.mul_comm wE wS]
        _ = (wS * wS) * (wE * wE) := by simp only [Int.mul_assoc]
    calc (2 * (wS * wE)) * (2 * (wS * wE))
        = 2 * ((wS * wE) * (2 * (wS * wE))) := Int.mul_assoc _ _ _
      _ = 2 * (2 * ((wS * wE) * (wS * wE))) := by
            rw [← Int.mul_assoc (wS * wE) 2, Int.mul_comm (wS * wE) 2, Int.mul_assoc]
      _ = (2 * 2) * ((wS * wE) * (wS * wE)) := (Int.mul_assoc _ _ _).symm
      _ = 4 * ((wS * wS) * (wE * wE)) := by rw [hsq]; rfl
  rw [h4se]
  exact singularity_helper (J * J) (wS * wS) (wE * wE)

/-- Theorem 7 (Section IV.H Eq. 112 Critical Boundary `|ωS^2 - ωE^2| = J^2` Gives Exact Equality `∑ cos^2 θ_± = 1`):
    Direct corollary of Theorem 6 when `(ωS^2 - ωE^2)^2 = J^4`. -/
theorem two_qubit_critical_boundary_sum_one (J wS wE : Int)
    (hcrit : (wS * wS - wE * wE) * (wS * wS - wE * wE) = (J * J) * (J * J)) :
    let Dp := J * J + (wS + wE) * (wS + wE)
    let Dm := J * J + (wS - wE) * (wS - wE)
    J * J * (Dp + Dm) = Dp * Dm := by
  have hid := two_qubit_singularity_criterion_exact J wS wE
  dsimp only at hid ⊢
  omega

/-- Theorem 8 (Section IV.H–I Fig. 3(a) Exact Periodic & Singular Witness `(ωS, ωE, J) = (5, 4, 3)`):
    Certifies `|5^2 - 4^2| = 9 = 3^2`, `4*Ω_-^2 = 10`, `4*Ω_+^2 = 90`, so `Ω_- / Ω_+ = 1/3` (odd/odd!). -/
theorem fig3a_periodic_singular_5_4_3 :
    (5 * 5 - 4 * 4 = 3 * 3) ∧
    (3 * 3 + (5 - 4) * (5 - 4) = 10) ∧
    (3 * 3 + (5 + 4) * (5 + 4) = 90) ∧
    (90 = 9 * 10) ∧
    (1 % 2 = 1) ∧ (3 % 2 = 1) := by
  decide

/-- Theorem 9 (Section IV.H–I Fig. 3(b) Exact Periodic & Non-Singular Witness `(ωS, ωE, J) = (5, 3, 4)`):
    Certifies `|5^2 - 3^2| = 16 = 4^2`, `4*Ω_-^2 = 20`, `4*Ω_+^2 = 80`, so `Ω_- / Ω_+ = 1/2` (odd/even: periodic, NOT singular!). -/
theorem fig3b_periodic_nonsingular_5_3_4 :
    (5 * 5 - 3 * 3 = 4 * 4) ∧
    (4 * 4 + (5 - 3) * (5 - 3) = 20) ∧
    (4 * 4 + (5 + 3) * (5 + 3) = 80) ∧
    (80 = 4 * 20) ∧
    (1 % 2 = 1) ∧ (2 % 2 = 0) := by
  decide

/-- Theorem 10 (Section IV.H Eq. 114 Parity Obstruction for Even/Odd Periodicity):
    If `q_minus` is odd and `q_plus = 2 * k` is even, there is NO pair of integers
    `(n_minus, n_plus)` with `(2*n_minus + 1) * (2*k) = (2*n_plus + 1) * q_minus`! -/
theorem odd_even_ratio_never_singular (k qm nm np : Int) (hqm : qm % 2 = 1) :
    (2 * nm + 1) * (2 * k) ≠ (2 * np + 1) * qm := by
  intro heq
  have hlhs : ((2 * nm + 1) * (2 * k)) % 2 = 0 := by
    rw [Int.mul_emod, Int.mul_emod 2 k]
    have h2 : (2 : Int) % 2 = 0 := by decide
    rw [h2, Int.zero_mul, Int.zero_emod, Int.mul_zero]
    rfl
  have hrhs : ((2 * np + 1) * qm) % 2 = 1 := by
    have h1 : (2 * np + 1) % 2 = 1 := by omega
    rw [Int.mul_emod, h1, hqm]
    decide
  omega

/-- Theorem 11 (Section IV.F Eq. 81 Critical Factor `ζ_- = 0 ↔ ωS * ωE = 0`):
    Since `4*Ω_+^2 - 4*Ω_-^2 = 4*(ωS * ωE)`, `4*Ω_+^2 = 4*Ω_-^2` holds iff `ωS * ωE = 0`! -/
theorem critical_zeta_minus_zero_iff (J wS wE : Int) :
    (J * J + (wS + wE) * (wS + wE) = J * J + (wS - wE) * (wS - wE)) ↔ wS * wE = 0 := by
  have hdiff := (two_qubit_omega_sq_sum_and_diff J wS wE).2
  constructor
  · intro heq; omega
  · intro h0; omega

/-- Theorem 12 (Section IV.F Eq. 86–88 Trivial Interaction `J = 0` Exact Polynomial Ring Factorization):
    In `Int[x]`, `R_3(x) = (x^2 + ω_+^2)(x^2 + ω_-^2)` satisfies `polyMul R_3 [0, 1] = P_3|_{J=0}`
    and `polyMul R_3 [1] = Q_3|_{J=0}`, with strict order drop `polyDeg P_3 = 5 → polyDeg [0, 1] = 1`! -/
theorem trivial_interaction_order_drop (wp wm : Int) :
    let a := wp * wp
    let b := wm * wm
    let R3 : List Int := [a * b, 0, a + b, 0, 1]
    let P3_J0 : List Int := [0, a * b, 0, a + b, 0, 1]
    polyMul R3 [0, 1] = P3_J0 ∧
    polyMul R3 [1] = R3 ∧
    polyDeg P3_J0 = 5 ∧ polyDeg [0, 1] = 1 := by
  dsimp only [polyMul, polyAdd, polyScale, polyDeg, List.length]
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [Int.mul_zero, Int.mul_one, Int.add_zero]
  · simp only [Int.mul_one, Int.add_zero]

/-- Helper: prove a property for all `i : Fin 4` by exhaustive case split in core Lean 4. -/
private theorem fin4_forall {P : Fin 4 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩)
    (h2 : P ⟨2, by decide⟩) (h3 : P ⟨3, by decide⟩) : ∀ i : Fin 4, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

/-- Helper: prove a property for all `i : Fin 3` by exhaustive case split in core Lean 4. -/
private theorem fin3_forall {P : Fin 3 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩) (h2 : P ⟨2, by decide⟩) : ∀ i : Fin 3, P i
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2

/-- Theorem 13 (Section V.C Eq. 126–127 Full 4×4 Jaynes–Cummings Involution & Diagonalization):
    Proves entrywise across all 16 entries `(i, j : Fin 4)` that `T^2 = I_4` AND
    `T * E_ε(f) * T = diag(1, f, f, f^2)` universally for every `f : Int`! -/
theorem jc_similarity_involution_and_diag (f : Int) :
    (∀ i j : Fin 4, mat4Mul jcSimT jcSimT i j = mat4Id i j) ∧
    (∀ i j : Fin 4, mat4Mul (mat4Mul jcSimT (jcDynE f)) jcSimT i j = jcDiag4 1 f f (f * f) i j) := by
  constructor
  · apply fin4_forall <;> apply fin4_forall <;> decide
  · apply fin4_forall <;> apply fin4_forall <;>
    simp only [mat4Mul, jcSimT, jcDynE, jcDiag4,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one,
               Int.add_zero, Int.zero_add, Int.mul_neg, Int.neg_neg] <;>
    omega

/-- Theorem 14 (Section V.D Eq. 135 Jaynes–Cummings Polynomial Expansion `u(s)`):
    For `4*ε^2 = λ*(λ - 2*γ0)`, expanding `4*u(s) = (2s + λ)^2 - 4ε^2` gives
    `4*(s^2) + 4*(λ*s) + 2*(λ*γ0)`, independent of `√(λ(λ - 2γ0))`! -/
theorem jc_poly_u_rational_expansion (s lam g0 e2 : Int) (he2 : 4 * e2 = lam * (lam - 2 * g0)) :
    (2 * s + lam) * (2 * s + lam) - 4 * e2 = 4 * (s * s) + 4 * (lam * s) + 2 * (lam * g0) := by
  rw [he2]
  have h1 : (2 * s + lam) * (2 * s + lam) = 4 * (s * s) + 4 * (lam * s) + lam * lam := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add]
    have c1 : (2 * s) * (2 * s) = 4 * (s * s) := by
      calc (2 * s) * (2 * s) = 2 * (s * (2 * s)) := Int.mul_assoc _ _ _
        _ = 2 * (2 * (s * s)) := by rw [← Int.mul_assoc s 2 s, Int.mul_comm s 2, Int.mul_assoc]
        _ = (2 * 2) * (s * s) := (Int.mul_assoc _ _ _).symm
        _ = 4 * (s * s) := rfl
    have c2 : (2 * s) * lam = 2 * (lam * s) := by
      rw [Int.mul_assoc, Int.mul_comm s lam]
    have c3 : lam * (2 * s) = 2 * (lam * s) := by
      rw [← Int.mul_assoc, Int.mul_comm lam 2, Int.mul_assoc]
    omega
  have h2 : lam * (lam - 2 * g0) = lam * lam - 2 * (lam * g0) := by
    rw [Int.mul_sub, ← Int.mul_assoc lam 2 g0, Int.mul_comm lam 2, Int.mul_assoc]
  omega

/-- Theorem 15 (Section V.D Eq. 135–137 Jaynes–Cummings Cubic `v(s)` & `Q_3(s)` Rationality):
    `(-3λ)^2 - λ(λ - 4γ0) = 4*(2*(λ^2) + λ*γ0)` (exact Vieta discriminant for `κ_±`). -/
theorem jc_poly_Q3_vieta_exact (lam g0 : Int) :
    (-3 * lam) * (-3 * lam) - lam * (lam - 4 * g0) = 4 * (2 * (lam * lam) + lam * g0) := by
  have h1 : (-3 * lam) * (-3 * lam) = 9 * (lam * lam) := by
    calc (-3 * lam) * (-3 * lam) = (-3) * (lam * ((-3) * lam)) := Int.mul_assoc _ _ _
      _ = (-3) * (((-3) * lam) * lam) := by rw [Int.mul_comm lam ((-3) * lam)]
      _ = ((-3) * (-3)) * (lam * lam) := by simp only [Int.mul_assoc]
      _ = 9 * (lam * lam) := rfl
  have h2 : lam * (lam - 4 * g0) = lam * lam - 4 * (lam * g0) := by
    rw [Int.mul_sub, ← Int.mul_assoc lam 4 g0, Int.mul_comm lam 4, Int.mul_assoc]
  omega

/-- Theorem 16 (Section V.E Eq. 139–140 Exceptional-Point Coalescence `λ = 2γ0 ↔ ε^2 = 0`):
    For `λ > 0`, `λ * (λ - 2 * γ0) = 0 ↔ λ = 2 * γ0`, coalescing poles into multiplicity 2 and 3! -/
theorem jc_exceptional_point_iff (lam g0 : Int) (hlam : 0 < lam) :
    lam * (lam - 2 * g0) = 0 ↔ lam = 2 * g0 := by
  constructor
  · intro h0
    have hcases := Int.mul_eq_zero.mp h0
    cases hcases with
    | inl hl => omega
    | inr hd => omega
  · intro heq
    rw [heq]
    have hz : 2 * g0 - 2 * g0 = 0 := by omega
    rw [hz, Int.mul_zero]

/-- Theorem 17 (Section V.C Eq. 129 Non-Markovian Singularity Regime `λ < 2γ0 ↔ ε^2 < 0`):
    For `λ > 0`, `λ * (λ - 2 * γ0) < 0 ↔ λ < 2 * γ0` (purely imaginary `ε = iν`, infinitely many singularities). -/
theorem jc_nonmarkovian_singularity_regime (lam g0 : Int) (hlam : 0 < lam) :
    lam * (lam - 2 * g0) < 0 ↔ lam < 2 * g0 := by
  constructor
  · intro hlt
    by_cases hge : 2 * g0 ≤ lam
    · have hnn : 0 ≤ lam * (lam - 2 * g0) := Int.mul_nonneg (by omega) (by omega)
      omega
    · omega
  · intro hlt
    have hpos : 0 < lam * (2 * g0 - lam) := Int.mul_pos hlam (by omega)
    have hflip : lam * (lam - 2 * g0) = -(lam * (2 * g0 - lam)) := by
      have : lam - 2 * g0 = -(2 * g0 - lam) := by omega
      rw [this, Int.mul_neg]
    omega

/-- Congruence for left factor of `mat3Mul` without unfolding nested multiplications. -/
private theorem mat3Mul_congr_left (A B C : Fin 3 → Fin 3 → Int)
    (h : ∀ i j, A i j = B i j) (i j : Fin 3) :
    mat3Mul A C i j = mat3Mul B C i j := by
  unfold mat3Mul
  rw [h i ⟨0, by decide⟩, h i ⟨1, by decide⟩, h i ⟨2, by decide⟩]

/-- Exact rank-1 closed form of `(Θ_v + λ I_3)^2 = [1, -λ, λ^2]^T [λ^2, 2λ, 1]`. -/
def jcN2Rank1 (lam : Int) (i j : Fin 3) : Int :=
  match i.val, j.val with
  | 0, 0 => lam * lam
  | 0, 1 => 2 * lam
  | 0, 2 => 1
  | 1, 0 => -(lam * lam * lam)
  | 1, 1 => -(2 * (lam * lam))
  | 1, 2 => -lam
  | 2, 0 => lam * lam * lam * lam
  | 2, 1 => 2 * (lam * lam * lam)
  | 2, 2 => lam * lam
  | _, _ => 0

/-- Theorem 18 (Section V.F Full 3×3 Exceptional-Point Companion Matrix Nilpotency):
    For EVERY `lam : Int`, the actual shifted 3×3 companion matrix `N = Θ_v + lam * I_3` of
    `v(s) = (s + lam)^3` satisfies `(N^2)_{0,2} = 1` (so `N^2 ≠ 0`) AND `∀ i j : Fin 3, (N^3)_{i,j} = 0`! -/
theorem jc_exceptional_point_jordan3_nilpotent (lam : Int) :
    let N := jcShiftedCompanionEP lam
    let N2 := mat3Mul N N
    let N3 := mat3Mul N2 N
    N2 0 2 = 1 ∧ (∀ i j : Fin 3, N3 i j = 0) := by
  dsimp only
  have h1 : lam * (lam * lam) = lam * lam * lam := (Int.mul_assoc lam lam lam).symm
  have h2 : lam * (2 * lam) = 2 * (lam * lam) := by
    rw [← Int.mul_assoc, Int.mul_comm lam 2, Int.mul_assoc]
  have h2a : (2 * lam) * lam = 2 * (lam * lam) := Int.mul_assoc 2 lam lam
  have h3a : (lam * lam) * (2 * lam) = 2 * (lam * lam * lam) := by
    rw [Int.mul_comm (lam * lam) (2 * lam), Int.mul_assoc 2 lam (lam * lam), h1]
  have h4 : (2 * lam) * (2 * lam) = 4 * (lam * lam) := by
    calc (2 * lam) * (2 * lam) = 2 * (lam * (2 * lam)) := Int.mul_assoc _ _ _
      _ = 2 * (2 * (lam * lam)) := by rw [h2]
      _ = (2 * 2) * (lam * lam) := (Int.mul_assoc _ _ _).symm
      _ = 4 * (lam * lam) := rfl
  have h5 : (2 * lam) * (3 * (lam * lam)) = 6 * (lam * lam * lam) := by
    calc (2 * lam) * (3 * (lam * lam)) = 2 * (lam * (3 * (lam * lam))) := Int.mul_assoc _ _ _
      _ = 2 * (3 * (lam * lam * lam)) := by
            rw [← Int.mul_assoc lam 3, Int.mul_comm lam 3, Int.mul_assoc, Int.mul_assoc, h1]
      _ = (2 * 3) * (lam * lam * lam) := (Int.mul_assoc _ _ _).symm
      _ = 6 * (lam * lam * lam) := rfl
  have h6 : (3 * (lam * lam)) * lam = 3 * (lam * lam * lam) := Int.mul_assoc 3 (lam * lam) lam
  have h6a : lam * (3 * (lam * lam)) = 3 * (lam * lam * lam) := by
    rw [← Int.mul_assoc lam 3, Int.mul_comm lam 3, Int.mul_assoc, Int.mul_assoc, h1]
  have h7a : lam * (lam * lam * lam) = lam * lam * lam * lam := by
    rw [← Int.mul_assoc lam (lam * lam) lam, h1]
  have h7 : (2 * lam) * (lam * lam * lam) = 2 * (lam * lam * lam * lam) := by
    rw [Int.mul_assoc 2 lam (lam * lam * lam), h7a]
  have h8 : (lam * lam) * (lam * lam) = lam * lam * lam * lam := (Int.mul_assoc (lam * lam) lam lam).symm
  have h9 : (lam * lam) * (3 * (lam * lam)) = 3 * (lam * lam * lam * lam) := by
    rw [← Int.mul_assoc (lam * lam) 3, Int.mul_comm (lam * lam) 3, Int.mul_assoc, h8]
  have h10 : (lam * lam) * (lam * lam * lam) = lam * lam * lam * lam * lam := by
    rw [← Int.mul_assoc (lam * lam) (lam * lam) lam, h8]
  have h11 : (2 * (lam * lam * lam)) * lam = 2 * (lam * lam * lam * lam) := Int.mul_assoc 2 (lam * lam * lam) lam
  have h14 : (2 * (lam * lam)) * lam = 2 * (lam * lam * lam) := Int.mul_assoc 2 (lam * lam) lam
  have hN2 : ∀ i j : Fin 3,
      mat3Mul (jcShiftedCompanionEP lam) (jcShiftedCompanionEP lam) i j = jcN2Rank1 lam i j := by
    apply fin3_forall <;> apply fin3_forall <;>
    dsimp [mat3Mul, jcShiftedCompanionEP, jcN2Rank1] <;>
    simp only [Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.add_zero, Int.zero_add,
               Int.neg_mul, Int.mul_neg, Int.neg_neg] <;>
    omega
  constructor
  · rw [hN2 0 2]; rfl
  · intro i j
    rw [mat3Mul_congr_left _ _ _ hN2 i j]
    revert j; revert i
    apply fin3_forall <;> apply fin3_forall <;>
    dsimp [mat3Mul, jcShiftedCompanionEP, jcN2Rank1] <;>
    simp only [Int.mul_zero, Int.one_mul, Int.mul_one, Int.add_zero, Int.zero_add,
               Int.neg_mul, Int.mul_neg, Int.neg_neg] <;>
    omega

end PolyMasterEq
