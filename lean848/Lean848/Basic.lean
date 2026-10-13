import Mathlib

/-!
# Erdős Problem #848 — formalised lemmas (phase 1)

Lemmas from Sections 2 and 5 of `paper/erdos848.pdf`:
* the witness facts mod 25 and mod 4 (Lemma 3 of the paper);
* the arithmetic of `n^2+1` (no factor 4, no factor `p ≡ 3 mod 4`, `25 ∣ n^2+1 ↔ n ≡ ±7 mod 25`);
* the residue class `7 mod 25` is admissible;
* the counting core of the large-prime lemma: for fixed `m`, the solutions of `m*u^2 ≡ 1 (mod w)` are at most
  as numerous as the square roots of unity mod `w`.
-/

namespace Erdos848

/-! ## Witness facts -/

/-- If `z ≡ 7 (mod 25)` then `25 ∣ wz+1` iff `w ≡ 7 (mod 25)`. -/
theorem dvd25_of_P7 (w z : ℕ) (hz : z % 25 = 7) : 25 ∣ w * z + 1 ↔ w % 25 = 7 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hz]
  have h := Nat.mod_lt w (by norm_num : 25 > 0)
  interval_cases (w % 25) <;> simp

/-- If `z ≡ 18 (mod 25)` then `25 ∣ wz+1` iff `w ≡ 18 (mod 25)`. -/
theorem dvd25_of_P18 (w z : ℕ) (hz : z % 25 = 18) : 25 ∣ w * z + 1 ↔ w % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hz]
  have h := Nat.mod_lt w (by norm_num : 25 > 0)
  interval_cases (w % 25) <;> simp

/-- If `h ≡ ±7 (mod 25)` and `r ≢ ±7 (mod 25)` then `25 ∤ hr+1`. -/
theorem not_dvd25_PR (h r : ℕ) (hh : h % 25 = 7 ∨ h % 25 = 18) (hr : r % 25 ≠ 7 ∧ r % 25 ≠ 18) :
    ¬ 25 ∣ h * r + 1 := by
  rcases hh with hh | hh
  · rw [Nat.mul_comm]; exact fun hd => hr.1 ((dvd25_of_P7 r h hh).1 hd)
  · rw [Nat.mul_comm]; exact fun hd => hr.2 ((dvd25_of_P18 r h hh).1 hd)

/-- `4 ∣ wz+1` iff `(w mod 4)(z mod 4) ≡ 3 (mod 4)`. -/
theorem dvd4_iff (w z : ℕ) : 4 ∣ w * z + 1 ↔ (w % 4) * (z % 4) % 4 = 3 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  have hw := Nat.mod_lt w (by norm_num : 4 > 0)
  have hz := Nat.mod_lt z (by norm_num : 4 > 0)
  interval_cases (w % 4) <;> interval_cases (z % 4) <;> simp

/-! ## Arithmetic of `n^2+1` -/

theorem not_four_dvd_sq_add_one (n : ℕ) : ¬ 4 ∣ n ^ 2 + 1 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
  have h := Nat.mod_lt n (by norm_num : 4 > 0)
  interval_cases (n % 4) <;> simp

theorem dvd25_sq_add_one_iff (n : ℕ) : 25 ∣ n ^ 2 + 1 ↔ n % 25 = 7 ∨ n % 25 = 18 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
  have h := Nat.mod_lt n (by norm_num : 25 > 0)
  interval_cases (n % 25) <;> simp

/-- A prime `p ≡ 3 (mod 4)` never divides `n^2+1`. -/
theorem prime_three_mod_four_not_dvd (p n : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) : ¬ p ∣ n ^ 2 + 1 := by
  have := Fact.mk hp
  intro hd
  have h0 : ((n : ZMod p)) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hd
    push_cast at this; exact this
  have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination (-1 : ZMod p) * h0⟩
  exact (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq h3

/-! ## The residue class `7 mod 25` is admissible -/

theorem P7_admissible (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 7) : ¬ Squarefree (a * b + 1) := by
  have h25 : 25 ∣ a * b + 1 := (dvd25_of_P7 a b hb).2 ha
  intro hsq
  have : (5 : ℕ) * 5 ∣ a * b + 1 := by simpa using h25
  have hu := hsq 5 this
  simp at hu

/-! ## Counting core of the large-prime lemma (Lemma 6 of the paper)

For fixed `m`, the residues `u (mod w)` with `m*u^2 = 1` are at most as many as the square roots of unity:
if `u₀` is one solution then `u ↦ u * u₀⁻¹` is an injection into `{s : s^2 = 1}`. -/

theorem card_solutions_le_card_sqrt_one (w : ℕ) [NeZero w] (m : ZMod w) :
    (Finset.univ.filter (fun u : ZMod w => m * u ^ 2 = 1)).card ≤
    (Finset.univ.filter (fun s : ZMod w => s ^ 2 = 1)).card := by
  by_cases hex : ∃ u₀ : ZMod w, m * u₀ ^ 2 = 1
  · obtain ⟨u₀, hu₀⟩ := hex
    -- u₀ is a unit, with inverse m * u₀
    have hinv : u₀ * (m * u₀) = 1 := by linear_combination hu₀
    refine Finset.card_le_card_of_injOn (fun u => u * (m * u₀)) ?_ ?_
    · intro u hu
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      calc (u * (m * u₀)) ^ 2 = (m * u ^ 2) * (m * u₀ ^ 2) := by ring
        _ = 1 := by rw [hu, hu₀, one_mul]
    · intro x _ y _ hxy
      simp only at hxy
      calc x = x * (m * u₀) * u₀ := by linear_combination (-x) * hinv
        _ = y * (m * u₀) * u₀ := by rw [hxy]
        _ = y := by linear_combination y * hinv
  · push Not at hex
    have : (Finset.univ.filter (fun u : ZMod w => m * u ^ 2 = 1)) = ∅ := by
      ext u; simp [hex u]
    rw [this]; simp

end Erdos848
