import Lean848.LargePrime

/-!
# Inclusion–exclusion with bounded error (core of Lemma 7 of the paper)

Let `Z = {z ∈ [1,N] : z ≡ c (mod q)}` and let `S` be a finite family of residue conditions
`z ≡ r i (mod d i)`, with the `d i` pairwise coprime and coprime to `q`. Then
  #{z ∈ Z : z ≡ r i (mod d i) for some i ∈ S} ≤ N/q · (1 − Π_{i∈S} (1 − 1/d i)) + (2^{|S|} − 1).
In fact the count is within `2^{|S|} − 1` of the density term (`ie_count_abs`).
The specialisation to prime squares `d p = p^2` is `ie_prime_squares`.
-/

namespace Erdos848

open Finset

/-- A residue class mod `q` has at least `⌊N/q⌋` members in `[1,N]`. -/
theorem card_class_ge (N q c : ℕ) (hq : 0 < q) :
    N / q ≤ ((Icc 1 N).filter (fun z => z ≡ c [MOD q])).card := by
  set r := if c % q = 0 then q else c % q with hr
  have hr1 : 1 ≤ r := by rw [hr]; split_ifs <;> omega
  have hrq : r ≤ q := by
    rw [hr]; split_ifs
    · exact le_rfl
    · exact (Nat.mod_lt c hq).le
  have hrc : r % q = c % q := by
    rw [hr]; split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt (Nat.mod_lt c hq) ▸ Nat.mod_mod c q
  calc N / q = (range (N / q)).card := (card_range _).symm
    _ ≤ _ := by
      refine card_le_card_of_injOn (fun k => k * q + r) ?_ ?_
      · intro k hk
        simp only [coe_range, Set.mem_Iio] at hk
        simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq]
        have h1 : (k + 1) * q ≤ N / q * q := Nat.mul_le_mul_right q hk
        have h2 : N / q * q ≤ N := Nat.div_mul_le_self N q
        refine ⟨⟨by omega, by nlinarith⟩, ?_⟩
        show (k * q + r) % q = c % q
        rw [Nat.mul_comm, Nat.mul_add_mod, hrc]
      · intro a _ b _ hab
        simp only at hab
        exact Nat.eq_of_mul_eq_mul_right hq (by omega)

/-- A residue class mod `q` has at most `⌊N/q⌋ + 1` members in `[1,N]`. -/
theorem card_class_le (N q c : ℕ) :
    ((Icc 1 N).filter (fun z => z ≡ c [MOD q])).card ≤ N / q + 1 :=
  card_residue_le q N (c % q)

/-- The count of a residue class mod `q` in `[1,N]` is within `1` of `N/q`. -/
theorem card_class_abs (N q c : ℕ) (hq : 0 < q) :
    |(((Icc 1 N).filter (fun z => z ≡ c [MOD q])).card : ℝ) - N / q| ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo := card_class_ge N q c hq
  have hhi := card_class_le N q c
  have hdm : ((N / q : ℕ) : ℝ) * q + ((N % q : ℕ) : ℝ) = N := by
    exact_mod_cast (Nat.div_add_mod' N q)
  have hmod : ((N % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt N hq
  have hmod0 : (0 : ℝ) ≤ ((N % q : ℕ) : ℝ) := by positivity
  have hfl : (N : ℝ) / q - 1 < ((N / q : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hqR]; nlinarith
  have hfu : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have hloR : ((N / q : ℕ) : ℝ) ≤ (((Icc 1 N).filter (fun z => z ≡ c [MOD q])).card : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (((Icc 1 N).filter (fun z => z ≡ c [MOD q])).card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhi
  rw [abs_le]; constructor <;> linarith

/-- Chinese remainder: `z ≡ CRT(c, b) (mod q·d) ↔ z ≡ c (mod q) ∧ z ≡ b (mod d)`. -/
theorem crt_iff {q d : ℕ} (h : Nat.Coprime q d) (c b z : ℕ) :
    z ≡ (Nat.chineseRemainder h c b : ℕ) [MOD q * d] ↔ z ≡ c [MOD q] ∧ z ≡ b [MOD d] := by
  constructor
  · intro hz
    exact ⟨(hz.of_mul_right d).trans (Nat.chineseRemainder h c b).2.1,
      (hz.of_mul_left q).trans (Nat.chineseRemainder h c b).2.2⟩
  · rintro ⟨h1, h2⟩
    exact Nat.chineseRemainder_modEq_unique h h1 h2

private theorem split_iff (a b c e : Prop) :
    (a ∧ b ∧ (c ∨ e)) ↔ (a ∧ b ∧ e) ∨ (a ∧ b ∧ c) ∧ ¬(a ∧ (b ∧ c) ∧ e) := by
  tauto

/-- **Inclusion–exclusion with bounded error** (two-sided form). -/
theorem ie_count_abs {ι : Type*} [DecidableEq ι] (N : ℕ) (d r : ι → ℕ) (S : Finset ι) :
    (∀ i ∈ S, 0 < d i) → (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (d i) (d j)) →
    ∀ q c : ℕ, 0 < q → (∀ i ∈ S, Nat.Coprime q (d i)) →
    |(((Icc 1 N).filter (fun z => z ≡ c [MOD q] ∧ ∃ i ∈ S, z ≡ r i [MOD d i])).card : ℝ)
        - N / q * (1 - ∏ i ∈ S, (1 - 1 / (d i : ℝ)))| ≤ 2 ^ S.card - 1 := by
  induction S using Finset.induction_on with
  | empty => intro _ _ q c _ _; simp
  | insert j S hj ih =>
    intro hd hpw q c hq hcop
    have hdS : ∀ i ∈ S, 0 < d i := fun i hi => hd i (mem_insert_of_mem hi)
    have hpwS : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → Nat.Coprime (d i) (d k) :=
      fun i hi k hk => hpw i (mem_insert_of_mem hi) k (mem_insert_of_mem hk)
    have hdj : 0 < d j := hd j (mem_insert_self j S)
    have hqj : Nat.Coprime q (d j) := hcop j (mem_insert_self j S)
    set c' : ℕ := (Nat.chineseRemainder hqj c (r j) : ℕ) with hc'
    have hcop' : ∀ i ∈ S, Nat.Coprime (q * d j) (d i) := by
      intro i hi
      have hij : i ≠ j := fun h => hj (h ▸ hi)
      exact Nat.Coprime.mul_left (hcop i (mem_insert_of_mem hi))
        (hpw j (mem_insert_self j S) i (mem_insert_of_mem hi) hij.symm)
    have ih1 := ih hdS hpwS q c hq (fun i hi => hcop i (mem_insert_of_mem hi))
    have ih2 := ih hdS hpwS (q * d j) c' (Nat.mul_pos hq hdj) hcop'
    have hcl := card_class_abs N (q * d j) c' (Nat.mul_pos hq hdj)
    set F := (Icc 1 N).filter (fun z => z ≡ c [MOD q] ∧ ∃ i ∈ S, z ≡ r i [MOD d i]) with hF
    set A := (Icc 1 N).filter (fun z => z ≡ c' [MOD q * d j]) with hA
    set B := (Icc 1 N).filter (fun z => z ≡ c' [MOD q * d j] ∧ ∃ i ∈ S, z ≡ r i [MOD d i])
      with hB
    have hsplit : (Icc 1 N).filter
        (fun z => z ≡ c [MOD q] ∧ ∃ i ∈ insert j S, z ≡ r i [MOD d i]) = F ∪ (A \ B) := by
      ext z
      simp only [hF, hA, hB, mem_filter, mem_union, mem_sdiff, exists_mem_insert, hc',
        crt_iff hqj]
      exact split_iff _ _ _ _
    have hdisj : Disjoint F (A \ B) := by
      rw [disjoint_left]
      intro z hzF hz
      simp only [hF, hA, hB, mem_filter, mem_sdiff, hc', crt_iff hqj] at hzF hz
      exact hz.2 ⟨hzF.1, ⟨hzF.2.1, hz.1.2.2⟩, hzF.2.2⟩
    have hBA : B ⊆ A := by
      intro z hz
      simp only [hA, hB, mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.1⟩
    have hcard : ((F ∪ (A \ B)).card : ℝ) = F.card + A.card - B.card := by
      rw [card_union_of_disjoint hdisj]
      have := card_sdiff_add_card_eq_card hBA
      have : ((A \ B).card : ℝ) + B.card = A.card := by exact_mod_cast this
      push_cast; linarith
    rw [hsplit, hcard, prod_insert hj, card_insert_of_notMem hj]
    set P := ∏ i ∈ S, (1 - 1 / (d i : ℝ))
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hdR : (0 : ℝ) < d j := by exact_mod_cast hdj
    have hiden : (N : ℝ) / q * (1 - (1 - 1 / (d j : ℝ)) * P) =
        N / q * (1 - P) + N / ((q * d j : ℕ) : ℝ) - N / ((q * d j : ℕ) : ℝ) * (1 - P) := by
      push_cast; field_simp; ring
    rw [hiden, pow_succ]
    rw [abs_le] at ih1 ih2 hcl ⊢
    constructor <;> linarith [ih1.1, ih1.2, ih2.1, ih2.2, hcl.1, hcl.2]

/-- **Inclusion–exclusion with bounded error** (the upper bound used in Lemma 7). -/
theorem ie_count_le {ι : Type*} [DecidableEq ι] (N : ℕ) (d r : ι → ℕ) (S : Finset ι)
    (hd : ∀ i ∈ S, 0 < d i) (hpw : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (d i) (d j))
    (q c : ℕ) (hq : 0 < q) (hcop : ∀ i ∈ S, Nat.Coprime q (d i)) :
    (((Icc 1 N).filter (fun z => z ≡ c [MOD q] ∧ ∃ i ∈ S, z ≡ r i [MOD d i])).card : ℝ)
      ≤ N / q * (1 - ∏ i ∈ S, (1 - 1 / (d i : ℝ))) + (2 ^ S.card - 1) := by
  have := ie_count_abs N d r S hd hpw q c hq hcop
  rw [abs_le] at this; linarith [this.2]

/-- **Lemma 7 core, prime-square form.** For a set `S` of primes, each coprime to `q`, and
residues `r p`: `#{z ∈ [1,N] : z ≡ c (q), ∃ p ∈ S, z ≡ r p (p^2)} ≤
N/q·(1 − Π_{p∈S}(1 − 1/p^2)) + (2^{|S|} − 1)`. -/
theorem ie_prime_squares (N q c : ℕ) (hq : 0 < q) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hcop : ∀ p ∈ S, Nat.Coprime q p) (r : ℕ → ℕ) :
    (((Icc 1 N).filter (fun z => z ≡ c [MOD q] ∧ ∃ p ∈ S, z ≡ r p [MOD p ^ 2])).card : ℝ)
      ≤ N / q * (1 - ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)) + (2 ^ S.card - 1) := by
  have h := ie_count_le N (fun p => p ^ 2) r S
    (fun p hp => pow_pos (hS p hp).pos 2)
    (fun p hp p' hp' hne => Nat.Coprime.pow 2 2 ((Nat.coprime_primes (hS p hp) (hS p' hp')).2 hne))
    q c hq (fun p hp => Nat.Coprime.pow_right 2 (hcop p hp))
  simpa using h

end Erdos848
