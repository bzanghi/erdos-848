import Mathlib

/-!
# The negative Pell count (used in Lemma 8 of the paper)

For `k ≥ 2`, the positive `x ≤ N` with `x^2 - k y^2 = -1` for some `y` number at most
  `1/2 + log(2N+1) / (2 log(1+√2))`.

The proof is elementary and does not use the structure theory of units: if `x < x'` are two
solutions, `η = x + y√k`, `η' = x' + y'√k`, then `η' = (a + b√k) η` with integers
`a = k y y' - x x' ≥ 3`, `b = x' y - x y' ≥ 1`, `a^2 - k b^2 = 1`, so `η'/η ≥ 3 + 2√2 = (1+√2)^2`
(`a = 2` would force `k = 3`, impossible mod 3). Also `1 + √2 ≤ η ≤ 2x+1`.
-/

namespace Erdos848

open Finset

/-- `η(x) = x + √(x^2+1)`; for a solution of `x^2 + 1 = k y^2` this is `x + y√k`. -/
noncomputable def pellEta (x : ℕ) : ℝ := x + Real.sqrt ((x : ℝ) ^ 2 + 1)

theorem pellEta_eq (k x y : ℕ) (h : x ^ 2 + 1 = k * y ^ 2) :
    pellEta x = x + y * Real.sqrt k := by
  have : ((x : ℝ) ^ 2 + 1) = (y : ℝ) ^ 2 * k := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h; push_cast at this; linarith
  rw [pellEta, this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Consecutive solutions grow by a factor of at least `(1+√2)^2 = 3 + 2√2`. -/
theorem pell_ratio (k x y x' y' : ℕ) (hk : 2 ≤ k) (h : x ^ 2 + 1 = k * y ^ 2)
    (h' : x' ^ 2 + 1 = k * y' ^ 2) (hlt : x < x') :
    (1 + Real.sqrt 2) ^ 2 * pellEta x ≤ pellEta x' := by
  -- integer arithmetic
  have hZ : (x : ℤ) ^ 2 + 1 = k * y ^ 2 := by exact_mod_cast h
  have hZ' : (x' : ℤ) ^ 2 + 1 = k * y' ^ 2 := by exact_mod_cast h'
  have hkZ : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hy'0 : (0 : ℤ) ≤ y' := by positivity
  have hltZ : (x : ℤ) < x' := by exact_mod_cast hlt
  have hyy : (y : ℤ) < y' := by
    apply lt_of_pow_lt_pow_left₀ 2 hy'0
    have : (k : ℤ) * y ^ 2 < k * y' ^ 2 := by nlinarith
    nlinarith
  set a : ℤ := k * y * y' - x * x' with ha
  set b : ℤ := x' * y - x * y' with hb
  have hnorm : a ^ 2 - k * b ^ 2 = 1 := by
    rw [ha, hb]
    linear_combination (-(k * (y' : ℤ) ^ 2 - x' ^ 2)) * hZ - hZ'
  have hbpos : 0 < b := by
    have hsq : ((x : ℤ) * y') ^ 2 < (x' * y) ^ 2 := by
      have e1 : ((x : ℤ) * y') ^ 2 = k * y ^ 2 * y' ^ 2 - y' ^ 2 := by
        linear_combination (y' : ℤ) ^ 2 * hZ
      have e2 : ((x' : ℤ) * y) ^ 2 = k * y ^ 2 * y' ^ 2 - y ^ 2 := by
        linear_combination (y : ℤ) ^ 2 * hZ'
      rw [e1, e2]; nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [hb]; linarith
  have hapos : 0 < a := by
    have hsq : ((x : ℤ) * x') ^ 2 < (k * y * y') ^ 2 := by
      have e : ((k : ℤ) * y * y') ^ 2 = (x ^ 2 + 1) * (x' ^ 2 + 1) := by
        rw [hZ, hZ']; ring
      rw [e]; nlinarith [sq_nonneg ((x : ℤ)), sq_nonneg ((x' : ℤ))]
    have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
    rw [ha]; linarith
  have hkb : 8 ≤ (k : ℤ) * b ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hb1 : b = 1 := by
      by_contra hne
      have : 2 ≤ b := by omega
      nlinarith
    rw [hb1] at hcon hnorm
    -- a^2 = k + 1 with 3 ≤ k + 1 ≤ 8, so a = 2 and k = 3 (a = 3 gives k = 8, excluded)
    have ha3 : a ≤ 2 := by nlinarith
    have ha2 : a = 2 := by
      rcases (show a = 1 ∨ a = 2 by omega) with h1 | h1 <;> rw [h1] at hnorm
      · nlinarith
      · exact h1
    rw [ha2] at hnorm
    have hk3 : k = 3 := by
      have : (k : ℤ) = 3 := by linarith
      exact_mod_cast this
    rw [hk3] at h
    have hmod : (x ^ 2 + 1) % 3 = 0 := by rw [h]; simp
    rw [Nat.add_mod, Nat.pow_mod] at hmod
    have := Nat.mod_lt x (by norm_num : 3 > 0)
    interval_cases (x % 3) <;> simp at hmod
  -- real arithmetic
  have hkR : (0 : ℝ) ≤ k := by positivity
  have hsk : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hkR
  have hfac : pellEta x' = ((a : ℝ) + b * Real.sqrt k) * pellEta x := by
    rw [pellEta_eq k x y h, pellEta_eq k x' y' h', ha, hb]
    push_cast
    have hZR : (x : ℝ) ^ 2 + 1 = k * y ^ 2 := by exact_mod_cast h
    linear_combination ((y' : ℝ) * Real.sqrt k + x') * hZR +
      ((x : ℝ) * y * y' - y ^ 2 * x') * hsk
  have hbR : (8 : ℝ) ≤ (k : ℝ) * (b : ℝ) ^ 2 := by exact_mod_cast hkb
  have haR : (9 : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : (a : ℝ) ^ 2 - k * (b : ℝ) ^ 2 = 1 := by exact_mod_cast hnorm
    linarith
  have ha3R : (3 : ℝ) ≤ a := by
    have : (0 : ℝ) < a := by exact_mod_cast hapos
    nlinarith
  have hbsk : 2 * Real.sqrt 2 ≤ b * Real.sqrt k := by
    have hb0 : (0 : ℝ) ≤ b := by exact_mod_cast hbpos.le
    have e1 : (b : ℝ) * Real.sqrt k = Real.sqrt (k * b ^ 2) := by
      rw [Real.sqrt_mul hkR, Real.sqrt_sq hb0, mul_comm]
    have e2 : 2 * Real.sqrt 2 = Real.sqrt 8 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [e1, e2]; exact Real.sqrt_le_sqrt hbR
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have heta0 : 0 ≤ pellEta x := by unfold pellEta; positivity
  rw [hfac]
  apply mul_le_mul_of_nonneg_right _ heta0
  nlinarith

/-- `1 + √2 ≤ η(x) ≤ 2x + 1` for a positive solution. -/
theorem pellEta_bounds (k x y : ℕ) (hk : 2 ≤ k) (h : x ^ 2 + 1 = k * y ^ 2) (hx : 1 ≤ x) :
    1 + Real.sqrt 2 ≤ pellEta x ∧ pellEta x ≤ 2 * x + 1 := by
  constructor
  · rw [pellEta_eq k x y h]
    have hy : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hk2 : Real.sqrt 2 ≤ Real.sqrt k := Real.sqrt_le_sqrt (by exact_mod_cast hk)
    nlinarith [Real.sqrt_nonneg (k : ℝ)]
  · unfold pellEta
    have : Real.sqrt ((x : ℝ) ^ 2 + 1) ≤ x + 1 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]
    linarith

open Classical in
/-- **Negative Pell count.** For `k ≥ 2`,
`#{x ∈ [1,N] : ∃ y, x^2 + 1 = k y^2} ≤ 1/2 + log(2N+1)/(2 log(1+√2))`. -/
theorem pell_neg_count (k N : ℕ) (hk : 2 ≤ k) :
    (((Icc 1 N).filter (fun x => ∃ y : ℕ, x ^ 2 + 1 = k * y ^ 2)).card : ℝ) ≤
      1 / 2 + Real.log (2 * N + 1) / (2 * Real.log (1 + Real.sqrt 2)) := by
  set X := (Icc 1 N).filter (fun x => ∃ y : ℕ, x ^ 2 + 1 = k * y ^ 2) with hX
  set c := 2 * Real.log (1 + Real.sqrt 2) with hc
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlog1 : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hcpos : 0 < c := by rw [hc]; linarith
  set L := Real.log (2 * N + 1) / c with hL
  rcases X.eq_empty_or_nonempty with hE | hne
  · rw [hE, card_empty, Nat.cast_zero]
    have : 0 ≤ L := div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
      hcpos.le
    linarith
  -- t(x) = log η(x) / c, so 1/2 ≤ t ≤ L and t(x') ≥ t(x) + 1 for x < x' in X
  set t : ℕ → ℝ := fun x => Real.log (pellEta x) / c with ht
  have hmem : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N ∧ ∃ y : ℕ, x ^ 2 + 1 = k * y ^ 2 := by
    intro x hx
    simp only [hX, mem_filter, mem_Icc] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have hlo : ∀ x ∈ X, 1 / 2 ≤ t x := by
    intro x hx
    obtain ⟨h1, -, y, hy⟩ := hmem x hx
    have hb := (pellEta_bounds k x y hk hy h1).1
    simp only [ht]
    rw [le_div_iff₀ hcpos, hc]
    have := Real.log_le_log (by positivity) hb
    linarith
  have hhi : ∀ x ∈ X, t x ≤ L := by
    intro x hx
    obtain ⟨h1, hN, y, hy⟩ := hmem x hx
    have hb := pellEta_bounds k x y hk hy h1
    simp only [ht, hL]
    apply div_le_div_of_nonneg_right _ hcpos.le
    apply Real.log_le_log (by linarith [hb.1])
    have : (x : ℝ) ≤ N := by exact_mod_cast hN
    linarith [hb.2]
  have hgap : ∀ x ∈ X, ∀ x' ∈ X, x < x' → t x + 1 ≤ t x' := by
    intro x hx x' hx' hlt
    obtain ⟨h1, -, y, hy⟩ := hmem x hx
    obtain ⟨-, -, y', hy'⟩ := hmem x' hx'
    have hr := pell_ratio k x y x' y' hk hy hy' hlt
    have hpos : 0 < pellEta x := by linarith [(pellEta_bounds k x y hk hy h1).1]
    have hl := Real.log_le_log (by positivity) hr
    rw [Real.log_mul (by positivity) hpos.ne', Real.log_pow] at hl
    simp only [ht]
    rw [div_add_one hcpos.ne', div_le_div_iff_of_pos_right hcpos, hc]
    push_cast at hl
    linarith
  -- floor(t - 1/2) is injective on X with values in [0, floor(L - 1/2)]
  obtain ⟨x0, hx0⟩ := hne
  have hL2 : 0 ≤ L - 1 / 2 := by linarith [hlo x0 hx0, hhi x0 hx0]
  have hcard : X.card ≤ ⌊L - 1 / 2⌋₊ + 1 := by
    calc X.card ≤ (range (⌊L - 1 / 2⌋₊ + 1)).card := by
          refine card_le_card_of_injOn (fun x => ⌊t x - 1 / 2⌋₊) ?_ ?_
          · intro x hx
            simp only [coe_range, Set.mem_Iio]
            exact Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [hhi x hx]))
          · have key : ∀ x ∈ X, ∀ x' ∈ X, x < x' → ⌊t x - 1 / 2⌋₊ ≠ ⌊t x' - 1 / 2⌋₊ := by
              intro x hx x' hx' hlt heq
              have h0 : 0 ≤ t x - 1 / 2 := by linarith [hlo x hx]
              have hle : ⌊t x - 1 / 2⌋₊ + 1 ≤ ⌊t x' - 1 / 2⌋₊ := by
                apply Nat.le_floor
                push_cast
                linarith [Nat.floor_le h0, hgap x hx x' hx' hlt]
              omega
            intro x hx x' hx' heq
            rcases lt_trichotomy x x' with h | h | h
            · exact absurd heq (key x hx x' hx' h)
            · exact h
            · exact absurd heq.symm (key x' hx' x hx h)
      _ = ⌊L - 1 / 2⌋₊ + 1 := card_range _
  have hfl := Nat.floor_le hL2
  have : (X.card : ℝ) ≤ (⌊L - 1 / 2⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  linarith

end Erdos848
