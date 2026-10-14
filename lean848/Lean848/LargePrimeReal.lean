import Lean848.LargePrime

/-!
# The large-prime lemma (Lemma 6 of the paper), real form

For `1 ≤ w ≤ N` and real `V ≥ 1`:
  #{z ∈ [1,N] : ∃ prime p > V, p^2 ∣ wz+1} ≤ λ(w)·((N^2+1)/V^2 + 2(N+1)/V + 1).

Deduced from the integer form `large_prime_count` via `Σ_{m=1}^{K} m^{-1/2} ≤ 2√K`
and `Nat.sqrt n ≤ √n`.
-/

namespace Erdos848

open Finset

/-- `Σ_{m=1}^{K} 1/√m ≤ 2√K`. -/
theorem sum_inv_sqrt_le (K : ℕ) : ∑ m ∈ Icc 1 K, 1 / Real.sqrt m ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hs : 0 < Real.sqrt ((K + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hs2 : Real.sqrt ((K + 1 : ℕ) : ℝ) ^ 2 = K + 1 := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have ht0 : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
    have ht2 : Real.sqrt (K : ℝ) ^ 2 = K := Real.sq_sqrt (by positivity)
    -- 1/s ≤ 2(s - t), since 2s² - 2st ≥ 2s² - (s² + t²) = 1
    have key : 1 / Real.sqrt ((K + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((K + 1 : ℕ) : ℝ) - 2 * Real.sqrt (K : ℝ) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((K + 1 : ℕ) : ℝ) - Real.sqrt (K : ℝ))]
    linarith

open Classical in
/-- **Large-prime lemma** (real form, as stated in the paper). -/
theorem large_prime_count_real (w N : ℕ) [NeZero w] (hwN : w ≤ N) (V : ℝ) (hV : 1 ≤ V) :
    (((Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1)).card : ℝ) ≤
      lam w * (((N : ℝ) ^ 2 + 1) / V ^ 2 + 2 * ((N : ℝ) + 1) / V + 1) := by
  have hw : 0 < w := Nat.pos_of_ne_zero (NeZero.ne w)
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hV0 : (0 : ℝ) < V := by linarith
  set V0 := ⌊V⌋₊ with hV0def
  -- the filter with real `V` equals the filter with `V0 = ⌊V⌋`
  have hfilt : (Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1) =
      (Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V0 < p ∧ p ^ 2 ∣ w * z + 1) := by
    ext z
    simp only [mem_filter, hV0def, Nat.floor_lt hV0.le]
  rw [hfilt]
  set X : ℕ := w * N + 1 with hX
  set K := X / (V0 + 1) ^ 2 with hK
  have hXR : (X : ℝ) = w * N + 1 := by rw [hX]; push_cast; ring
  have hXpos : (0 : ℝ) < X := by rw [hXR]; positivity
  have hVlt : V < (V0 : ℝ) + 1 := Nat.lt_floor_add_one V
  -- K ≤ X / V^2
  have hKle : (K : ℝ) ≤ X / V ^ 2 := by
    calc (K : ℝ) ≤ (X : ℝ) / ((V0 + 1) ^ 2 : ℕ) := Nat.cast_div_le
      _ ≤ X / V ^ 2 := by
        push_cast
        apply div_le_div_of_nonneg_left hXpos.le (by positivity)
        nlinarith
  have hint := large_prime_count w N V0
  have hintR : (((Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V0 < p ∧ p ^ 2 ∣ w * z + 1)).card : ℝ)
      ≤ ∑ m ∈ Icc 1 K, (lam w : ℝ) * ((Nat.sqrt (X / m) / w : ℕ) + 1) := by
    exact_mod_cast hint
  -- bound each summand
  have hterm : ∀ m ∈ Icc 1 K, (lam w : ℝ) * ((Nat.sqrt (X / m) / w : ℕ) + 1) ≤
      lam w * (Real.sqrt X / w * (1 / Real.sqrt m) + 1) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.1 hm).1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((Nat.sqrt (X / m) / w : ℕ) : ℝ) ≤ (Nat.sqrt (X / m) : ℝ) / w := Nat.cast_div_le
    have h2 : (Nat.sqrt (X / m) : ℝ) ≤ Real.sqrt X / Real.sqrt m := by
      calc (Nat.sqrt (X / m) : ℝ) ≤ Real.sqrt ((X / m : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
        _ ≤ Real.sqrt ((X : ℝ) / m) := Real.sqrt_le_sqrt Nat.cast_div_le
        _ = Real.sqrt X / Real.sqrt m := Real.sqrt_div' _ (by positivity)
    have h3 : (Nat.sqrt (X / m) : ℝ) / w ≤ Real.sqrt X / w * (1 / Real.sqrt m) := by
      rw [div_le_iff₀ (by positivity)]
      calc (Nat.sqrt (X / m) : ℝ) ≤ Real.sqrt X / Real.sqrt m := h2
        _ = Real.sqrt X / w * (1 / Real.sqrt m) * w := by field_simp
    linarith
  have hsum := sum_le_sum hterm
  have hR : ∑ m ∈ Icc 1 K, (lam w : ℝ) * (Real.sqrt X / w * (1 / Real.sqrt m) + 1) =
      lam w * (Real.sqrt X / w * ∑ m ∈ Icc 1 K, 1 / Real.sqrt m + K) := by
    rw [← mul_sum, sum_add_distrib, ← mul_sum]; simp
  rw [hR] at hsum
  -- √X · 2√K / w ≤ 2(N+1)/V
  have hsK : Real.sqrt K ≤ Real.sqrt X / V := by
    calc Real.sqrt K ≤ Real.sqrt (X / V ^ 2) := Real.sqrt_le_sqrt hKle
      _ = Real.sqrt X / V := by rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hV0.le]
  have hsX : Real.sqrt (X : ℝ) * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
  have hB : Real.sqrt X / w * ∑ m ∈ Icc 1 K, 1 / Real.sqrt m ≤ 2 * ((N : ℝ) + 1) / V := by
    calc Real.sqrt X / w * ∑ m ∈ Icc 1 K, 1 / Real.sqrt m
        ≤ Real.sqrt X / w * (2 * (Real.sqrt X / V)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [sum_inv_sqrt_le K]
      _ = 2 * (Real.sqrt X * Real.sqrt X) / w / V := by ring
      _ = 2 * (X / w) / V := by rw [hsX]; ring
      _ ≤ 2 * ((N : ℝ) + 1) / V := by
          apply div_le_div_of_nonneg_right _ hV0.le
          rw [hXR, add_div, mul_div_cancel_left₀ _ (by positivity)]
          have : (1 : ℝ) / w ≤ 1 := by rw [div_le_one (by positivity)]; exact hwR
          linarith
  have hA : (K : ℝ) ≤ ((N : ℝ) ^ 2 + 1) / V ^ 2 := by
    refine le_trans hKle (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hXR]
    have : (w : ℝ) ≤ N := by exact_mod_cast hwN
    nlinarith
  have hlam : (0 : ℝ) ≤ lam w := by positivity
  calc _ ≤ _ := hintR
    _ ≤ _ := hsum
    _ ≤ lam w * (((N : ℝ) ^ 2 + 1) / V ^ 2 + 2 * ((N : ℝ) + 1) / V + 1) := by
        apply mul_le_mul_of_nonneg_left _ hlam
        linarith

end Erdos848
