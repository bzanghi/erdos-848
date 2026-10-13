import Lean848.Basic

/-!
# The large-prime lemma (Lemma 6 of the paper), integer form

For `w ≥ 1`, `N`, `V`:
  #{z ∈ [1,N] : ∃ prime p > V, p^2 ∣ wz+1}
    ≤ Σ_{m=1}^{K} λ(w) · (⌊√((wN+1)/m)⌋ / w + 1),   K = (wN+1)/(V+1)^2,
where λ(w) = #{s ∈ ZMod w : s^2 = 1}.  (The paper then uses Σ_{m≤K} m^{-1/2} ≤ 2√K.)
-/

namespace Erdos848

open Finset

/-- Integers in `[1,U]` with a prescribed residue mod `w` number at most `U/w + 1`. -/
theorem card_residue_le (w U r : ℕ) :
    ((Icc 1 U).filter (fun u => u % w = r)).card ≤ U / w + 1 := by
  calc ((Icc 1 U).filter (fun u => u % w = r)).card
      ≤ (range (U / w + 1)).card := by
        refine card_le_card_of_injOn (fun u => u / w) ?_ ?_
        · intro u hu
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at hu
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hu.1.2)
        · intro a ha b hb hab
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
          simp only at hab
          rw [← Nat.div_add_mod a w, ← Nat.div_add_mod b w, hab, ha.2, hb.2]
    _ = U / w + 1 := card_range _

/-- Integers in `[1,U]` whose residue mod `w` lies in a set `R` number at most `|R|·(U/w+1)`. -/
theorem card_residues_le (w U : ℕ) (R : Finset ℕ) :
    ((Icc 1 U).filter (fun u => u % w ∈ R)).card ≤ R.card * (U / w + 1) := by
  calc ((Icc 1 U).filter (fun u => u % w ∈ R)).card
      = (R.biUnion (fun r => (Icc 1 U).filter (fun u => u % w = r))).card := by
        congr 1; ext u; simp [and_comm]
    _ ≤ ∑ r ∈ R, ((Icc 1 U).filter (fun u => u % w = r)).card := card_biUnion_le
    _ ≤ ∑ _r ∈ R, (U / w + 1) := sum_le_sum (fun r _ => card_residue_le w U r)
    _ = R.card * (U / w + 1) := by rw [sum_const, smul_eq_mul]

/-- `λ(w)`: the number of square roots of unity modulo `w`. -/
noncomputable def lam (w : ℕ) [NeZero w] : ℕ :=
  (univ.filter (fun s : ZMod w => s ^ 2 = 1)).card

/-- For fixed `m`, `#{u ∈ [1,U] : m u^2 ≡ 1 (mod w)} ≤ λ(w)·(U/w+1)`. -/
theorem card_sol_le (w U m : ℕ) [NeZero w] :
    ((Icc 1 U).filter (fun u : ℕ => ((m : ZMod w) * (u : ZMod w) ^ 2 = 1))).card
      ≤ lam w * (U / w + 1) := by
  have hw : 0 < w := Nat.pos_of_ne_zero (NeZero.ne w)
  set R : Finset ℕ := (range w).filter (fun r : ℕ => (m : ZMod w) * (r : ZMod w) ^ 2 = 1) with hR
  have hsub : (Icc 1 U).filter (fun u : ℕ => ((m : ZMod w) * (u : ZMod w) ^ 2 = 1)) ⊆
      (Icc 1 U).filter (fun u => u % w ∈ R) := by
    intro u hu
    simp only [mem_filter] at hu ⊢
    refine ⟨hu.1, ?_⟩
    simp only [hR, mem_filter, mem_range]
    refine ⟨Nat.mod_lt u hw, ?_⟩
    rw [ZMod.natCast_mod]; exact hu.2
  have hRcard : R.card ≤ lam w := by
    calc R.card ≤ (univ.filter (fun u : ZMod w => (m : ZMod w) * u ^ 2 = 1)).card := by
          refine card_le_card_of_injOn (fun r => (r : ZMod w)) ?_ ?_
          · intro r hr
            simp only [hR, coe_filter, mem_range, Set.mem_ofPred_eq] at hr
            simp [hr.2]
          · intro a ha b hb hab
            simp only [hR, coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
            simp only at hab
            have := (ZMod.natCast_eq_natCast_iff' a b w).1 hab
            rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at this
      _ ≤ lam w := card_solutions_le_card_sqrt_one w (m : ZMod w)
  calc _ ≤ ((Icc 1 U).filter (fun u => u % w ∈ R)).card := card_le_card hsub
    _ ≤ R.card * (U / w + 1) := card_residues_le w U R
    _ ≤ lam w * (U / w + 1) := Nat.mul_le_mul_right _ hRcard

open Classical in
/-- **Large-prime lemma** (integer form). -/
theorem large_prime_count (w N V : ℕ) [NeZero w] :
    ((Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1)).card ≤
      ∑ m ∈ Icc 1 ((w * N + 1) / (V + 1) ^ 2), lam w * (Nat.sqrt ((w * N + 1) / m) / w + 1) := by
  set K := (w * N + 1) / (V + 1) ^ 2
  set T := (Icc 1 K).sigma (fun m => (Icc 1 (Nat.sqrt ((w * N + 1) / m))).filter
      (fun u : ℕ => ((m : ZMod w) * (u : ZMod w) ^ 2 = 1))) with hT
  have hTcard : T.card ≤ ∑ m ∈ Icc 1 K, lam w * (Nat.sqrt ((w * N + 1) / m) / w + 1) := by
    rw [hT, card_sigma]
    exact sum_le_sum (fun m _ => card_sol_le w _ m)
  refine le_trans ?_ hTcard
  let S := (Icc 1 N).filter (fun z => ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1)
  let pz : ℕ → ℕ := fun z =>
    if h : ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1 then h.choose else 0
  have pz_spec : ∀ z ∈ S, (pz z).Prime ∧ V < pz z ∧ pz z ^ 2 ∣ w * z + 1 := by
    intro z hz
    have h : ∃ p : ℕ, p.Prime ∧ V < p ∧ p ^ 2 ∣ w * z + 1 := (mem_filter.1 hz).2
    simp only [pz, dif_pos h]; exact h.choose_spec
  refine card_le_card_of_injOn (fun z => (⟨(w * z + 1) / pz z ^ 2, pz z⟩ : (_ : ℕ) × ℕ)) ?_ ?_
  · intro z hz
    have hzS : z ∈ S := hz
    obtain ⟨hp, hV, hdvd⟩ := pz_spec z hzS
    have hzN : z ≤ N := (mem_Icc.1 (mem_filter.1 hzS).1).2
    set p := pz z
    set m := (w * z + 1) / p ^ 2 with hm
    have hmul : m * p ^ 2 = w * z + 1 := Nat.div_mul_cancel hdvd
    have hmpos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, zero_mul] at hmul; omega
      · exact h0
    have hwzN : w * z + 1 ≤ w * N + 1 := by
      have := Nat.mul_le_mul_left w hzN; omega
    have hK : m ≤ K := by
      apply (Nat.le_div_iff_mul_le (pow_pos (Nat.succ_pos V) 2)).2
      calc m * (V + 1) ^ 2 ≤ m * p ^ 2 := Nat.mul_le_mul_left m (Nat.pow_le_pow_left hV 2)
        _ = w * z + 1 := hmul
        _ ≤ w * N + 1 := hwzN
    have hsq : p ≤ Nat.sqrt ((w * N + 1) / m) := by
      apply Nat.le_sqrt.2
      apply (Nat.le_div_iff_mul_le hmpos).2
      calc p * p * m = m * p ^ 2 := by ring
        _ = w * z + 1 := hmul
        _ ≤ w * N + 1 := hwzN
    have hmod : ((m : ZMod w) * (p : ZMod w) ^ 2 = 1) := by
      have : ((m * p ^ 2 : ℕ) : ZMod w) = ((w * z + 1 : ℕ) : ZMod w) := by rw [hmul]
      push_cast at this
      rw [this, ZMod.natCast_self, zero_mul, zero_add]
    show (⟨m, p⟩ : (_ : ℕ) × ℕ) ∈ (T : Set ((_ : ℕ) × ℕ))
    rw [mem_coe, hT, mem_sigma, mem_filter, mem_Icc, mem_Icc]
    exact ⟨⟨hmpos, hK⟩, ⟨hp.one_lt.le, hsq⟩, hmod⟩
  · intro x hx y hy hxy
    have hxy' : (w * x + 1) / pz x ^ 2 = (w * y + 1) / pz y ^ 2 ∧ pz x = pz y := by
      simp only [Sigma.mk.injEq] at hxy
      exact ⟨hxy.1, eq_of_heq hxy.2⟩
    obtain ⟨-, -, hdx⟩ := pz_spec x hx
    obtain ⟨-, -, hdy⟩ := pz_spec y hy
    have ex : (w * x + 1) / pz x ^ 2 * pz x ^ 2 = w * x + 1 := Nat.div_mul_cancel hdx
    have ey : (w * y + 1) / pz y ^ 2 * pz y ^ 2 = w * y + 1 := Nat.div_mul_cancel hdy
    have h3 : w * x + 1 = w * y + 1 := by rw [← ex, ← ey, hxy'.1, hxy'.2]
    have hw : 0 < w := Nat.pos_of_ne_zero (NeZero.ne w)
    exact Nat.eq_of_mul_eq_mul_left hw (by omega)

end Erdos848
