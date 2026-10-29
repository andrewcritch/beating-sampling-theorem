import BstLean.Part56MomProg_CostDefs

/-! The arithmetic bound `costAll ≤ onceCost56`. -/

namespace BstLean.Part56.MomProg

lemma fpow (a b : ℕ) : a ^ b ≤ (a + b).factorial := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [zero_pow hb.ne']; exact Nat.zero_le _
  · have h := Nat.factorial_mul_pow_le_factorial (m := a - 1) (n := b)
    rw [Nat.sub_add_cancel ha] at h
    calc a ^ b ≤ (a - 1).factorial * a ^ b := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
      _ ≤ (a - 1 + b).factorial := h
      _ ≤ (a + b).factorial := Nat.factorial_le (by omega)

lemma fmul (a b : ℕ) : a.factorial * b.factorial ≤ (a + b).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a b)

lemma lin {P : ℕ} (hP : 2 ≤ P) (x : ℕ) : x ≤ P ^ x :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hP x)

lemma ppow {P : ℕ} (hP : 2 ≤ P) {i j : ℕ} (h : i ≤ j) : P ^ i ≤ P ^ j :=
  Nat.pow_le_pow_right (by omega) h

lemma one_le_pow' {P : ℕ} (hP : 2 ≤ P) (j : ℕ) : 1 ≤ P ^ j := Nat.one_le_pow _ _ (by omega)

lemma le_mul_left' {a b c : ℕ} (h : a ≤ c) (hb : 1 ≤ b) : a ≤ b * c :=
  h.trans (Nat.le_mul_of_pos_left _ hb)

section stages

variable (n d k K N M Kc m : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hk : 1 ≤ k) (hm : d * k = m)
  (hN : N ≤ (n + 2) ^ (2 * m)) (hM : M ≤ (n + 2) ^ (2 * m))
  (hKc : Kc ≤ (k + 1) ^ 2 * (d + 1) ^ k)

include hn hd hk hm

lemma basic_facts : 1 ≤ m ∧ d ≤ m ∧ k ≤ m := by
  subst hm
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_mul_of_pos_right _ hk,
    Nat.le_mul_of_pos_left _ hd⟩

include hM in
lemma stageA : costA n d M ≤ (n + 2) ^ (3 * m + 4) := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  unfold costA
  have t1 : 4 * (n + 1) ^ 2 ≤ (n + 2) ^ (3 * m + 3) := by
    calc 4 * (n + 1) ^ 2 ≤ (n + 2) * (n + 2) ^ 2 := by gcongr <;> omega
      _ = (n + 2) ^ 3 := by ring
      _ ≤ _ := ppow hP (by omega)
  have t2 : 3 * (d + 1) * M ≤ (n + 2) ^ (3 * m + 3) := by
    calc 3 * (d + 1) * M ≤ (n + 2) * (n + 2) ^ (m + 1) * (n + 2) ^ (2 * m) := by
          gcongr
          · omega
          · exact (lin hP _).trans (ppow hP (by omega))
      _ = (n + 2) ^ (3 * m + 2) := by ring
      _ ≤ _ := ppow hP (by omega)
  calc _ ≤ 2 * (n + 2) ^ (3 * m + 3) := by omega
    _ ≤ (n + 2) * (n + 2) ^ (3 * m + 3) := by gcongr
    _ = _ := by ring

include hN hM in
lemma stageB : costB d N M ≤ (n + 2) ^ (8 * m + 1) * m.factorial := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  unfold costB mulCN
  calc M * (d * (N * (2 * N ^ 2))) ≤ (n + 2) ^ (2 * m) * (m.factorial *
        ((n + 2) ^ (2 * m) * ((n + 2) * ((n + 2) ^ (2 * m)) ^ 2))) := by
        gcongr
        exact hdm.trans (Nat.self_le_factorial _)
    _ = _ := by ring

include hN hM in
lemma stageC : costC d N M ≤ (n + 2) ^ (8 * m + 3) * (m + 1).factorial := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  have hf : d + 1 ≤ (m + 1).factorial := (by omega : d + 1 ≤ m + 1).trans (Nat.self_le_factorial _)
  have hf1 : 1 ≤ (m + 1).factorial := Nat.factorial_pos _
  have hq := one_le_pow' hP (2 * m)
  unfold costC mulCN
  have t1 : 4 * (d + 1) * (N * M) ≤ (n + 2) ^ (8 * m + 2) * (m + 1).factorial := by
    calc 4 * (d + 1) * (N * M) ≤ (n + 2) * (m + 1).factorial *
          ((n + 2) ^ (2 * m) * (n + 2) ^ (2 * m)) := by gcongr; omega
      _ = (n + 2) ^ (4 * m + 1) * (m + 1).factorial := by ring
      _ ≤ _ := Nat.mul_le_mul (ppow hP (by omega)) (by first | exact le_rfl | exact hF1)
  have hMd : M + d + 1 ≤ (n + 2) ^ (2 * m + 1) * (m + 1).factorial := by
    have a1 : M ≤ (n + 2) ^ (2 * m) * (m + 1).factorial :=
      hM.trans (Nat.le_mul_of_pos_right _ hf1)
    have a2 : d + 1 ≤ (n + 2) ^ (2 * m) * (m + 1).factorial := le_mul_left' hf hq
    calc M + d + 1 ≤ 2 * ((n + 2) ^ (2 * m) * (m + 1).factorial) := by omega
      _ ≤ (n + 2) * ((n + 2) ^ (2 * m) * (m + 1).factorial) := by gcongr
      _ = _ := by ring
  have t2 : (M + d + 1) * (N * (2 * N ^ 2)) ≤ (n + 2) ^ (8 * m + 2) * (m + 1).factorial := by
    calc (M + d + 1) * (N * (2 * N ^ 2)) ≤ ((n + 2) ^ (2 * m + 1) * (m + 1).factorial) *
          ((n + 2) ^ (2 * m) * ((n + 2) * ((n + 2) ^ (2 * m)) ^ 2)) := by gcongr
      _ = _ := by ring
  have t3 : N * (4 * d + 4) ≤ (n + 2) ^ (8 * m + 2) * (m + 1).factorial := by
    calc N * (4 * d + 4) ≤ (n + 2) ^ (2 * m) * ((n + 2) * (m + 1).factorial) := by
          gcongr
          calc 4 * d + 4 = 4 * (d + 1) := by ring
            _ ≤ _ := by gcongr; omega
      _ = (n + 2) ^ (2 * m + 1) * (m + 1).factorial := by ring
      _ ≤ _ := Nat.mul_le_mul (ppow hP (by omega)) (by first | exact le_rfl | exact hF1)
  calc _ ≤ 3 * ((n + 2) ^ (8 * m + 2) * (m + 1).factorial) := by omega
    _ ≤ (n + 2) * ((n + 2) ^ (8 * m + 2) * (m + 1).factorial) := by gcongr; omega
    _ = _ := by ring

include hKc in
lemma Kc_le : Kc ≤ (k + 3).factorial * (n + 2) ^ m := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  refine hKc.trans ?_
  have hd2 : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
  refine Nat.mul_le_mul (fpow _ _) ?_
  calc (d + 1) ^ k ≤ (2 ^ d) ^ k := Nat.pow_le_pow_left hd2 k
      _ = 2 ^ m := by rw [← pow_mul, hm]
      _ ≤ _ := Nat.pow_le_pow_left hP m

include hN hKc in
lemma stageD : costD k N Kc ≤ (n + 2) ^ (8 * m + 2) * (k + 3).factorial := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  have hK := Kc_le n d k Kc m hn hd hk hm hKc
  unfold costD mulCN
  have h2k : 2 * k ≤ (n + 2) ^ (m + 1) := by
    calc 2 * k ≤ (n + 2) * (n + 2) ^ k := by gcongr; exact lin hP k
      _ = (n + 2) ^ (k + 1) := by ring
      _ ≤ _ := ppow hP (by omega)
  calc Kc * (2 * k * (N * (2 * N ^ 2))) ≤ ((k + 3).factorial * (n + 2) ^ m) *
        ((n + 2) ^ (m + 1) * ((n + 2) ^ (2 * m) * ((n + 2) * ((n + 2) ^ (2 * m)) ^ 2))) := by
        gcongr
    _ = _ := by ring

include hN in
lemma stageE : costE n d k K N ≤ (K + 2) ^ 2 * (n + 2) ^ (4 * m + 6) * (4 * m).factorial := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  unfold costE
  have e2 : 2 * d * k = 2 * m := by rw [← hm]; ring
  have e8 : 8 * d * k = 8 * m := by rw [← hm]; ring
  rw [e2, e8]
  set X := (K + 2) ^ 2 * (n + 2) ^ (2 * m + 5) * (4 * m).factorial with hX
  have hK1 : 1 ≤ (K + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hF1 : 1 ≤ (4 * m).factorial := Nat.factorial_pos _
  have hp1 := one_le_pow' hP (2 * m + 5)
  have hpm : (n + 2) ^ (2 * m) ≤ (n + 2) ^ (2 * m + 5) := ppow hP (by omega)
  have hDD : (2 * m) ^ (2 * m) ≤ (4 * m).factorial := by
    have := fpow (2 * m) (2 * m); rwa [show 2 * m + 2 * m = 4 * m by ring] at this
  have a1 : (2 * m) ^ (2 * m) ≤ X := by
    rw [hX]
    calc (2 * m) ^ (2 * m) ≤ 1 * 1 * (4 * m).factorial := by simpa using hDD
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hK1 hp1) le_rfl
  have a2 : (n + 2 * m) ^ (2 * m) ≤ X := by
    rw [hX]
    calc (n + 2 * m) ^ (2 * m) ≤ ((n + 2) * (2 * m)) ^ (2 * m) :=
          Nat.pow_le_pow_left (by nlinarith) _
      _ = (n + 2) ^ (2 * m) * (2 * m) ^ (2 * m) := by rw [mul_pow]
      _ ≤ 1 * (n + 2) ^ (2 * m + 5) * (4 * m).factorial := by
          rw [one_mul]; exact Nat.mul_le_mul hpm hDD
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hK1 le_rfl) le_rfl
  have a3 : 2 ≤ X := by
    rw [hX]
    calc 2 ≤ 1 * (n + 2) ^ (2 * m + 5) * 1 := by
          simpa using (le_trans hP (Nat.le_self_pow (by omega) _))
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hK1 le_rfl) hF1
  have a4 : K * (n + 6 * K + 8 * m + 10) ≤ X := by
    have hs : n + 8 * m + 16 ≤ (n + 2) ^ (m + 5) := by
      have b1 : 8 * (m + 2) ≤ (n + 2) ^ 2 * (n + 2) ^ (m + 2) :=
        Nat.mul_le_mul (by nlinarith) (lin hP _)
      have b2 : (n + 2) ^ 2 * (n + 2) ^ (m + 2) = (n + 2) ^ (m + 4) := by ring
      have b3 : (n + 2) ^ (m + 5) = (n + 2) * (n + 2) ^ (m + 4) := by ring
      have b4 := one_le_pow' hP (m + 4)
      rw [b3]; nlinarith
    calc K * (n + 6 * K + 8 * m + 10) ≤ (K + 2) ^ 2 * (n + 8 * m + 16) := by
          nlinarith [Nat.zero_le (K * K * n), Nat.zero_le (K * K * m), Nat.zero_le (K * n),
            Nat.zero_le (K * m), Nat.zero_le (K * K)]
      _ ≤ (K + 2) ^ 2 * (n + 2) ^ (2 * m + 5) * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul_left _ (hs.trans (ppow hP (by omega)))
      _ ≤ _ := Nat.mul_le_mul le_rfl hF1
  calc N * ((2 * m) ^ (2 * m) + (n + 2 * m) ^ (2 * m) + 2 + K * (n + 6 * K + 8 * m + 10))
      ≤ (n + 2) ^ (2 * m) * ((n + 2) * X) := by
        refine Nat.mul_le_mul hN ?_
        calc _ ≤ 4 * X := by omega
          _ ≤ (n + 2) * X := by gcongr; omega
    _ = _ := by rw [hX]; ring

include hN hKc in
lemma stageF : costF n d k N Kc ≤ (n + 2) ^ (3 * m + 5) * (3 * k + 3).factorial := by
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm
  have hP : 2 ≤ n + 2 := by omega
  have hK := Kc_le n d k Kc m hn hd hk hm hKc
  unfold costF
  set Y := (n + 2) ^ (2 * m + 3) * (2 * k).factorial with hY
  have hF1 : 1 ≤ (2 * k).factorial := Nat.factorial_pos _
  have hkk : k.factorial ≤ (2 * k).factorial := Nat.factorial_le (by omega)
  have hk2 : k.factorial ^ 2 ≤ (2 * k).factorial := by
    have := fmul k k; rw [sq]; rwa [show k + k = 2 * k by ring] at this
  have a1 : 2 * N ≤ Y := by
    rw [hY]
    calc 2 * N ≤ (n + 2) * (n + 2) ^ (2 * m) * 1 := by rw [mul_one]; exact Nat.mul_le_mul hP hN
      _ = (n + 2) ^ (2 * m + 1) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (ppow hP (by omega)) (by first | exact le_rfl | exact hF1)
  have a2 : k.factorial ≤ Y := le_mul_left' hkk (one_le_pow' hP _)
  have a3 : 2 ^ k * k.factorial ^ 2 ≤ Y := by
    rw [hY]; exact Nat.mul_le_mul ((Nat.pow_le_pow_left hP k).trans (ppow hP (by omega))) hk2
  have a4 : n * (n + 1) ^ d ≤ Y := by
    rw [hY]
    calc n * (n + 1) ^ d ≤ (n + 2) * (n + 2) ^ d * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      _ = (n + 2) ^ (d + 1) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (ppow hP (by omega)) (by first | exact le_rfl | exact hF1)
  have a5 : 2 * k + 10 ≤ Y := by
    rw [hY]
    calc 2 * k + 10 ≤ (n + 2) ^ 2 * (n + 2) ^ (k + 1) * 1 := by
          rw [mul_one]
          have := lin hP (k + 1)
          have : 16 ≤ (n + 2) ^ 2 := by nlinarith
          nlinarith
      _ = (n + 2) ^ (k + 3) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (ppow hP (by omega)) (by first | exact le_rfl | exact hF1)
  calc Kc * (2 * N + k.factorial + 2 ^ k * k.factorial ^ 2 + n * (n + 1) ^ d + 2 * k + 10)
      ≤ ((k + 3).factorial * (n + 2) ^ m) * ((n + 2) ^ 2 * Y) := by
        refine Nat.mul_le_mul hK ?_
        have : 16 ≤ (n + 2) ^ 2 := by nlinarith
        calc _ ≤ 5 * Y := by omega
          _ ≤ (n + 2) ^ 2 * Y := by gcongr; omega
    _ = (n + 2) ^ (3 * m + 5) * ((k + 3).factorial * (2 * k).factorial) := by rw [hY]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ ((fmul _ _).trans (Nat.factorial_le (by omega)))

end stages

theorem costAll_le_nat (n d k K N M Kc : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hN : N ≤ (n + 1) ^ (2 * d * k)) (hM : M ≤ (n + 1) ^ d)
    (hKc : Kc ≤ (k + 1) ^ 2 * (d + 1) ^ k) :
    costAll n d k K N M Kc ≤
      (K + 2) ^ 2 * (n + 2) ^ (8 * d * k + 8) * (8 * d * k + 8).factorial := by
  set m := d * k with hm
  obtain ⟨h1, hdm, hkm⟩ := basic_facts n d k m hn hd hk hm.symm
  have hP : 2 ≤ n + 2 := by omega
  have e2 : 2 * d * k = 2 * m := by rw [hm]; ring
  have e8 : 8 * d * k = 8 * m := by rw [hm]; ring
  rw [e8]
  rw [e2] at hN
  have hN' : N ≤ (n + 2) ^ (2 * m) := hN.trans (Nat.pow_le_pow_left (by omega) _)
  have hM' : M ≤ (n + 2) ^ (2 * m) :=
    hM.trans ((Nat.pow_le_pow_left (by omega) _).trans (ppow hP (by omega)))
  set U := (K + 2) ^ 2 * (n + 2) ^ (8 * m + 7) * (8 * m + 7).factorial with hU
  have hK1 : 1 ≤ (K + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have toU : ∀ j a x, x ≤ (K + 2) ^ 2 * (n + 2) ^ j * a.factorial → j ≤ 8 * m + 7 →
      a ≤ 8 * m + 7 → x ≤ U := by
    intro j a x hx hj ha
    refine hx.trans ?_
    rw [hU]; exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (ppow hP hj)) (Nat.factorial_le ha)
  have toU' : ∀ j a x, x ≤ (n + 2) ^ j * a.factorial → j ≤ 8 * m + 7 →
      a ≤ 8 * m + 7 → x ≤ U := by
    intro j a x hx hj ha
    refine toU j a x (hx.trans ?_) hj ha
    rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have hA := toU' (3 * m + 4) 0 _ (by simpa using stageA n d k M m hn hd hk hm.symm hM')
    (by omega) (by omega)
  have hB := toU' _ _ _ (stageB n d k N M m hn hd hk hm.symm hN' hM') (by omega) (by omega)
  have hC := toU' _ _ _ (stageC n d k N M m hn hd hk hm.symm hN' hM') (by omega) (by omega)
  have hD := toU' _ _ _ (stageD n d k N Kc m hn hd hk hm.symm hN' hKc) (by omega) (by omega)
  have hE := toU _ _ _ (stageE n d k K N m hn hd hk hm.symm hN') (by omega) (by omega)
  have hF := toU' _ _ _ (stageF n d k N Kc m hn hd hk hm.symm hN' hKc) (by omega) (by omega)
  unfold costAll
  calc _ ≤ 6 * U := by omega
    _ ≤ (n + 2) * (8 * m + 8) * U := by gcongr; nlinarith
    _ = _ := by
        rw [show 8 * m + 8 = (8 * m + 7) + 1 by ring, Nat.factorial_succ, hU]; ring

theorem costAll_le (n d k K N M Kc : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hN : N ≤ (n + 1) ^ (2 * d * k)) (hM : M ≤ (n + 1) ^ d)
    (hKc : Kc ≤ (k + 1) ^ 2 * (d + 1) ^ k) :
    (costAll n d k K N M Kc : ℝ) ≤ onceCost56 n d k K := by
  have h := costAll_le_nat n d k K N M Kc hn hd hk hN hM hKc
  unfold onceCost56
  exact_mod_cast h

end BstLean.Part56.MomProg
