import Mathlib

open scoped BigOperators
open Filter Topology

-- ==== BODY START ====

namespace GoldbachB1B1Scale

noncomputable section

/-- U cutoff: ⌊n^(1/16)⌋₊ (frozen). -/
def b1B1_cutoffU (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊

/-- B₁ cutoff: ⌊n^(1/4)⌋₊ (frozen low divisor band). -/
def b1B1_B1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- Q₁ cutoff: ⌊n^(1/3)⌋₊ (frozen wide-arc conductor bound). -/
def b1B1_Q1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

/-- H cutoff: 256 · Q₁ · (log₂(n+2))² (frozen). -/
def b1B1_H (n : ℕ) : ℕ :=
  256 * b1B1_Q1 n * (Nat.log 2 (n + 2)) ^ 2

/-- M_low envelope: ⌊n^(2/5)⌋₊ (wave-step envelope, blueprint §2.6.5). -/
def b1B1_stepLow (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊

/-- R cutoff: ⌊n^(1/12)⌋₊ (small-conductor cutoff, blueprint §2.6.5). -/
def b1B1_cutoffR (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 12 : ℝ)⌋₊

/-- Grid-neighbourhood radius 1/(8 M²). -/
def b1B1_radiusLow (M : ℕ) : ℝ := 1 / (8 * (M : ℝ) ^ 2)

/-- Half-floor lower bound (port of B1B4 L5805). -/
theorem b1B1_floor_half_le {x : ℝ} (xLower : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases small : x ≤ 2
  · have floorLower : (1 : ℝ) ≤ ⌊x⌋₊ := by
      exact_mod_cast (Nat.le_floor (n := 1) (by simpa using xLower))
    linarith only [small, floorLower]
  · have floorBound := Nat.lt_floor_add_one x
    linarith only [floorBound, lt_of_not_ge small]

/-- Upper floor bound for M_low. -/
theorem b1B1_stepLow_le_power (n : ℕ) :
    (b1B1_stepLow n : ℝ) ≤ (n : ℝ) ^ (2 / 5 : ℝ) :=
  Nat.floor_le (by positivity)

/-- Half-floor lower bound for M_low. -/
theorem b1B1_stepLow_ge_half {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 / 5 : ℝ) / 2 ≤ b1B1_stepLow n :=
  b1B1_floor_half_le (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

/-- B₁ band is bounded by the M_low envelope: 1/4 ≤ 2/5. -/
theorem b1B1_B1_le_stepLow {n : ℕ} (hn : 1 ≤ n) :
    b1B1_B1 n ≤ b1B1_stepLow n :=
  Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))

/-- Conductor bound Q₁ is bounded by the M_low envelope: 1/3 ≤ 2/5. -/
theorem b1B1_Q1_le_stepLow {n : ℕ} (hn : 1 ≤ n) :
    b1B1_Q1 n ≤ b1B1_stepLow n :=
  Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))

/-- Radius is positive. -/
theorem b1B1_radiusLow_pos {M : ℕ} (hM : 0 < M) : 0 < b1B1_radiusLow M := by
  unfold b1B1_radiusLow
  positivity

/-- Radius bounded by the centre-separation scale 1/(4qr) (port of B1B4 L621). -/
theorem b1B1_radiusLow_le_product {M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (qM : q ≤ M) (rM : r ≤ M) :
    b1B1_radiusLow M ≤ 1 / (4 * (q : ℝ) * (r : ℝ)) := by
  have productBound : (q : ℝ) * r ≤ (M : ℝ) ^ 2 := by
    norm_cast
    rw [pow_two]
    exact Nat.mul_le_mul qM rM
  unfold b1B1_radiusLow
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [productBound, show 0 ≤ (M : ℝ) ^ 2 by positivity]

/-- Radius ≤ 1/2 for M ≥ 1. -/
theorem b1B1_radiusLow_le_half {M : ℕ} (hM : 1 ≤ M) :
    b1B1_radiusLow M ≤ 1 / 2 := by
  unfold b1B1_radiusLow
  have hDen : 8 * (M : ℝ) ^ 2 ≥ 2 := by
    have hM' : (M : ℝ) ≥ 1 := by exact_mod_cast hM
    nlinarith
  exact one_div_le_one_div_of_le (by positivity) hDen

/-- log₂(n+2) ≤ 4 log n (port of B1B4 `log2_le_four_log`, L5824). -/
theorem b1B1_log2_le_four_log {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith)
      (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have hLogNonneg : (0 : ℝ) ≤ (Nat.log 2 (n + 2) : ℝ) := by positivity
  have multiplied := mul_le_mul_of_nonneg_left h2 hLogNonneg
  linarith only [logarithm, divided, multiplied]

/-- M_low ≤ n (for later `M ≤ n` constraints). -/
theorem b1B1_stepLow_le_n {n : ℕ} (hn : 1 ≤ n) : b1B1_stepLow n ≤ n :=
  Nat.floor_le_of_le
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

/-- Cover inequality: R · n · radius(M_low) ≤ H.
    Exponent ledger (blueprint §5-A):
      LHS ≤ n^(1/12) · n · 1/(2 n^(4/5)) = (1/2) n^(17/60),
      H   ≥ 128 n^(1/3); 1/3 − 17/60 = 1/20, and n^(1/20) ≥ 1. -/
theorem b1B1_cover {n : ℕ} (hn : 2 ≤ n) :
    (b1B1_cutoffR n : ℝ) * (n : ℝ) * b1B1_radiusLow (b1B1_stepLow n) ≤
      (b1B1_H n : ℝ) := by
  have nReal : (1 : ℝ) ≤ n := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have nPositive : 0 < n := by omega
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have hR : (b1B1_cutoffR n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) :=
    Nat.floor_le (by positivity)
  have hStep : (n : ℝ) ^ (2 / 5 : ℝ) / 2 ≤ (b1B1_stepLow n : ℝ) :=
    b1B1_stepLow_ge_half (by linarith)
  have hQ1 : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ b1B1_Q1 n :=
    b1B1_floor_half_le (Real.one_le_rpow nReal (by norm_num))
  have hLogN : 0 < Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
  have hLog : 1 ≤ (Nat.log 2 (n + 2) : ℝ) := by
    have h1 : 1 ≤ Nat.log 2 (n + 2) := hLogN
    exact_mod_cast h1
  have hM2 : (b1B1_stepLow n : ℝ) ^ 2 ≥ (n : ℝ) ^ (4 / 5 : ℝ) / 4 := by
    have hsq : ((n : ℝ) ^ (2 / 5 : ℝ) / 2) ^ 2 = (n : ℝ) ^ (4 / 5 : ℝ) / 4 := by
      have hmul : ((n : ℝ) ^ (2 / 5 : ℝ) / 2) ^ 2 =
          (n : ℝ) ^ (2 / 5 : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) / 4 := by ring
      rw [hmul, ← Real.rpow_add nRealPositive]
      ring
    have hstep2 : ((n : ℝ) ^ (2 / 5 : ℝ) / 2) ^ 2 ≤ (b1B1_stepLow n : ℝ) ^ 2 := by
      gcongr
    rw [hsq] at hstep2
    exact hstep2
  have hRadius : b1B1_radiusLow (b1B1_stepLow n) ≤
      1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ)) := by
    unfold b1B1_radiusLow
    have hDen : 8 * (b1B1_stepLow n : ℝ) ^ 2 ≥ 2 * (n : ℝ) ^ (4 / 5 : ℝ) := by
      linarith
    exact one_div_le_one_div_of_le (by positivity) hDen
  have hH : (b1B1_H n : ℝ) ≥ 128 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    unfold b1B1_H
    push_cast
    have hLog2 : 1 ≤ (Nat.log 2 (n + 2) : ℝ) ^ 2 := one_le_pow₀ hLog
    nlinarith [hQ1, hLog2]
  have hMPos : 0 < b1B1_stepLow n := by
    have h1 : 1 ≤ b1B1_stepLow n :=
      Nat.le_floor (Real.one_le_rpow nReal (by norm_num))
    omega
  have hRadPos : 0 ≤ b1B1_radiusLow (b1B1_stepLow n) :=
    (b1B1_radiusLow_pos hMPos).le
  have hFirst : (b1B1_cutoffR n : ℝ) * (n : ℝ) * b1B1_radiusLow (b1B1_stepLow n) ≤
      (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) := by
    have h1 : (b1B1_cutoffR n : ℝ) * (n : ℝ) ≤
        (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hR nRealPositive.le
    have h2 : b1B1_radiusLow (b1B1_stepLow n) ≤
        1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ)) := hRadius
    have hLeftNonneg : 0 ≤ (b1B1_cutoffR n : ℝ) * (n : ℝ) := by positivity
    have hRightNonneg : 0 ≤ 1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ)) := by positivity
    have h3 : (b1B1_cutoffR n : ℝ) * (n : ℝ) * b1B1_radiusLow (b1B1_stepLow n) ≤
        (b1B1_cutoffR n : ℝ) * (n : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hLeftNonneg
    have h4 : (b1B1_cutoffR n : ℝ) * (n : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) ≤
        (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) :=
      mul_le_mul_of_nonneg_right h1 hRightNonneg
    exact h3.trans h4
  calc
    (b1B1_cutoffR n : ℝ) * (n : ℝ) * b1B1_radiusLow (b1B1_stepLow n)
      ≤ (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) := hFirst
    _ = (1 / 2 : ℝ) * (n : ℝ) ^ (17 / 60 : ℝ) := by
      have step1 : (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) =
          (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      have exp1 : (n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) ^ (1 : ℝ) =
          (n : ℝ) ^ (13 / 12 : ℝ) := by
        rw [← Real.rpow_add nRealPositive]; norm_num
      have exp2 : (n : ℝ) ^ (13 / 12 : ℝ) / (n : ℝ) ^ (4 / 5 : ℝ) =
          (n : ℝ) ^ (17 / 60 : ℝ) := by
        rw [← Real.rpow_sub nRealPositive]; norm_num
      have ringEq : (n : ℝ) ^ (13 / 12 : ℝ) * (1 / (2 * (n : ℝ) ^ (4 / 5 : ℝ))) =
          (1 / 2 : ℝ) * ((n : ℝ) ^ (13 / 12 : ℝ) / (n : ℝ) ^ (4 / 5 : ℝ)) := by ring
      rw [step1, exp1, ringEq, exp2]
    _ ≤ 128 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hGap : (n : ℝ) ^ (1 / 20 : ℝ) ≥ 1 :=
        Real.one_le_rpow nReal (by norm_num)
      have split : 128 * (n : ℝ) ^ (1 / 3 : ℝ) =
          128 * (n : ℝ) ^ (17 / 60 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) := by
        have hmul : (n : ℝ) ^ (17 / 60 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) =
            (n : ℝ) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_add nRealPositive]; norm_num
        calc
          128 * (n : ℝ) ^ (1 / 3 : ℝ)
            = 128 * ((n : ℝ) ^ (17 / 60 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ)) := by rw [hmul]
          _ = 128 * (n : ℝ) ^ (17 / 60 : ℝ) * (n : ℝ) ^ (1 / 20 : ℝ) := by ring
      rw [split]
      have hCoef : (1 / 2 : ℝ) ≤ 128 * (n : ℝ) ^ (1 / 20 : ℝ) := by linarith [hGap]
      have hMul : (n : ℝ) ^ (17 / 60 : ℝ) * (1 / 2 : ℝ) ≤
          (n : ℝ) ^ (17 / 60 : ℝ) * (128 * (n : ℝ) ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left hCoef (by positivity : 0 ≤ (n : ℝ) ^ (17 / 60 : ℝ))
      linarith
    _ ≤ (b1B1_H n : ℝ) := hH

/-- Small-width condition: 4 · H · M_low ≤ n eventually.
    Exponent ledger: 4HM ≤ 16384 n^(11/15) log² n, and
    log² n / n^(4/15) → 0 (1 − 11/15 = 4/15). -/
theorem b1B1_small_width :
    ∀ᶠ n : ℕ in Filter.atTop,
      4 * (b1B1_H n : ℝ) * (b1B1_stepLow n : ℝ) ≤ n := by
  have limit : Tendsto (fun n : ℕ =>
      (Real.log n) ^ 2 / (n : ℝ) ^ (4 / 15 : ℝ)) Filter.atTop (𝓝 0) := by
    have asymptotic :=
      (isLittleO_log_rpow_rpow_atTop (2 : ℕ)
        (show (0 : ℝ) < 4 / 15 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Function.comp_def] using
      asymptotic.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2,
    limit.eventually_lt_const (show (0 : ℝ) < 1 / 16384 by norm_num)] with n hn small
  have nPositive : 0 < n := by omega
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have q1Upper : (b1B1_Q1 n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (by positivity)
  have stepUpper : (b1B1_stepLow n : ℝ) ≤ (n : ℝ) ^ (2 / 5 : ℝ) :=
    b1B1_stepLow_le_power n
  have logUpper : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n :=
    b1B1_log2_le_four_log hn
  have asReal : 4 * (b1B1_H n : ℝ) * (b1B1_stepLow n : ℝ) ≤ n := by
    calc
      _ = 1024 * (b1B1_Q1 n : ℝ) * (Nat.log 2 (n + 2) : ℝ) ^ 2 *
            (b1B1_stepLow n : ℝ) := by
        unfold b1B1_H
        push_cast
        ring
      _ ≤ 1024 * (n : ℝ) ^ (1 / 3 : ℝ) * (4 * Real.log n) ^ 2 *
            (n : ℝ) ^ (2 / 5 : ℝ) := by gcongr
      _ = (n : ℝ) ^ (11 / 15 : ℝ) * (16384 * (Real.log n) ^ 2) := by
        have exponent : (n : ℝ) ^ (11 / 15 : ℝ) =
            (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (2 / 5 : ℝ) := by
          rw [← Real.rpow_add nRealPositive]; norm_num
        rw [exponent]
        ring
      _ ≤ n := by
        have absorbed :=
          (div_lt_iff₀ (show 0 < (n : ℝ) ^ (4 / 15 : ℝ) by positivity)).mp small
        have hAbs : 16384 * (Real.log n) ^ 2 ≤ (n : ℝ) ^ (4 / 15 : ℝ) := by
          linarith [absorbed]
        have h : (n : ℝ) ^ (11 / 15 : ℝ) * (16384 * (Real.log n) ^ 2) ≤
            (n : ℝ) ^ (11 / 15 : ℝ) * (n : ℝ) ^ (4 / 15 : ℝ) :=
          mul_le_mul_of_nonneg_left hAbs (by positivity)
        rw [← Real.rpow_add nRealPositive] at h
        norm_num at h
        exact h
  exact_mod_cast asReal

end

end GoldbachB1B1Scale
