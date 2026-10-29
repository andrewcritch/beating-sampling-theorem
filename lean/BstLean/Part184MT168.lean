import BstLean.Part184MT167

/-!
# Part 184 (file `MT168`): the T168 link (Lemma LJ numerics) at the moment order `⌊log₂ n⌋/2` (`≥ 7`): `m^{1/(64q)} ≤ 1.0508`, `128q ≤ 0.0513n`, `X2 ≤ 2.252`, `Cg ≤ 10.81`, `Z ≤ 0.16543`, `K² ≤ 5` (value `≈ 4.964`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 184 `L` chain (floor 17 750) for every `n ≥ 17 500` (statistics cap `n ≤ 17 750`),
namespaces `….J175` / `BstLean.Part184.M`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.M

-- ===== from Part168Num.lean =====
section SPart168Num
open BstLean.Part168
open Real
open BstLean.Part130
open BstLean.Part167
variable {n : ℕ}
lemma q_ge (hn : 17500 ≤ n) : 14 ≤ qn n := by
  unfold qn
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- `128q ≤ 0.035n` for `q = ⌊log₂ n⌋`, every `n ≥ 45 000` (Part 168's `q_lin`, `4096q ≤ n`, needs
`n ≥ 61 440` when `q = 15`). -/
lemma q_lin45 (hn : 17500 ≤ n) : (128 : ℝ) * qn n ≤ 1025 / 10000 * n := by
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases h14 : qn n ≤ 14
  · have : ((qn n : ℕ) : ℝ) ≤ 14 := by exact_mod_cast h14
    linarith
  by_cases h15 : qn n ≤ 15
  · have hq : qn n = 15 := by omega
    have h2 := pow_q_le (n := n) (by omega)
    rw [hq] at h2
    have h3 : (32768 : ℝ) ≤ n := by exact_mod_cast (show 32768 ≤ n by simpa using h2)
    have : ((qn n : ℕ) : ℝ) = 15 := by exact_mod_cast hq
    rw [this]; linarith
  · obtain ⟨k, hk⟩ : ∃ k, qn n = 16 + k := ⟨qn n - 16, by omega⟩
    have h1 := lin_le_pow k
    have h2 := pow_q_le (n := n) (by omega)
    rw [hk] at h2
    have h3 : 4096 * qn n ≤ n := by rw [hk]; omega
    have h4 : ((4096 * qn n : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
    push_cast at h4
    linarith

/-- `128·⌊q/2⌋ ≤ 0.0505n` for `q = ⌊log₂ n⌋`, every `n ≥ 17 750`. -/
lemma qh_lin (hn : 17500 ≤ n) : (128 : ℝ) * (qn n / 2 : ℕ) ≤ 513 / 10000 * n := by
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 2 * (qn n / 2) ≤ qn n := Nat.mul_div_le (qn n) 2
  have hh' : ((2 * (qn n / 2) : ℕ) : ℝ) ≤ qn n := by exact_mod_cast hh
  push_cast at hh'
  by_cases h15 : qn n ≤ 15
  · have h7 : qn n / 2 ≤ 7 := by omega
    have : ((qn n / 2 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast h7
    linarith
  · obtain ⟨k, hk⟩ : ∃ k, qn n = 16 + k := ⟨qn n - 16, by omega⟩
    have h1 := lin_le_pow k
    have h2 := pow_q_le (n := n) (by omega)
    rw [hk] at h2
    have h3 : 4096 * qn n ≤ n := by rw [hk]; omega
    have h4 : ((4096 * qn n : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
    push_cast at h4
    linarith

lemma qh_ge (hn : 17500 ≤ n) : 7 ≤ qn n / 2 := by
  have := q_ge hn; omega

/-- **`m^{1/(64⌊q/2⌋)} ≤ 1.0508`** (`m < 2^{2q+2} ≤ 2^{4⌊q/2⌋+4}`, `⌊q/2⌋ ≥ 7`). -/
lemma rpow_m_le (hn : 17500 ≤ n) :
    ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * ((qn n / 2 : ℕ) : ℝ))) ≤ 10508 / 10000 := by
  set q := qn n / 2 with hq
  have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast qh_ge hn
  have hq0 : (0 : ℝ) < q := by linarith
  have hm : ((mA n : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((4 * q + 4 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h := lt_pow_q n
    have hle : qn n + 1 ≤ 2 * q + 2 := by omega
    have h2 : mA n ≤ 2 ^ (4 * q + 4) := by
      unfold mA
      calc n ^ 2 ≤ (2 ^ (qn n + 1)) ^ 2 := Nat.pow_le_pow_left h.le 2
        _ ≤ (2 ^ (2 * q + 2)) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hle) 2
        _ = 2 ^ (4 * q + 4) := by rw [← pow_mul]; ring_nf
    exact_mod_cast h2
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hm
    (by positivity : (0 : ℝ) ≤ 1 / (64 * (q : ℝ)))
  rw [← Real.rpow_mul (by norm_num)] at h1
  refine h1.trans ?_
  have hexp : ((4 * q + 4 : ℕ) : ℝ) * (1 / (64 * (q : ℝ))) ≤ 1 / 14 := by
    push_cast
    rw [show (4 * (q : ℝ) + 4) * (1 / (64 * (q : ℝ))) = (4 * q + 4) / (64 * q) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans ?_
  have h14 : (2 : ℝ) ≤ (10508 / 10000) ^ (14 : ℕ) := by norm_num
  calc (2 : ℝ) ^ ((1 : ℝ) / 14) ≤ ((10508 / 10000 : ℝ) ^ (14 : ℕ)) ^ ((1 : ℝ) / 14) :=
        Real.rpow_le_rpow (by norm_num) h14 (by norm_num)
    _ = 10508 / 10000 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

lemma two_rpow_64b : (2 : ℝ) ^ ((1 : ℝ) / 64) ≤ 10109 / 10000 := by
  have hb : (2 : ℝ) ≤ (10109 / 10000) ^ (64 : ℕ) := by norm_num
  have h := Real.rpow_le_rpow (by norm_num) hb (by norm_num : (0 : ℝ) ≤ 1 / 64)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  norm_num at h
  exact h

/-- **`X2 ≤ 2.196`** for `q = ⌊log₂ n⌋`. -/
theorem X2_num (hn : 17500 ≤ n) : X2q n (qn n / 2) ≤ 22520 / 10000 := by
  set q := qn n / 2 with hq
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [show n - 1 - 1 = n - 2 by omega]; push_cast [show 2 ≤ n by omega]; ring
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hqn : (128 : ℝ) * q ≤ 513 / 10000 * n := qh_lin hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR := rpow_m_le hn
  have hR0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) := Real.rpow_nonneg (by positivity) _
  -- the four factors
  have f1 : (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤ 10074 / 10000 := by
    rw [hd, div_le_iff₀ (by linarith)]; linarith
  have f1' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) := by
    rw [hd]; apply div_nonneg <;> linarith
  have f3 : (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) ≤ 2 * (10513 / 10000) := by
    rw [hd, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have f3' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) := by
    rw [hd]; apply mul_nonneg <;> [nlinarith; positivity]
  have f4 : 2 / ((mA n : ℕ) : ℝ) * BL (mA n) ≤ 10116 / 10000 := by
    unfold BL
    rw [hmR]
    set N : ℝ := (n : ℝ) with hN
    have hN0 : 0 < N := by linarith
    have hsq : √(N ^ 2 / 2 + 128) ≤ N := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h64 := two_rpow_64b
    have h640 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 64) := by positivity
    have e : 2 / N ^ 2 * ((2 : ℝ) ^ ((1 : ℝ) / 64) * (N ^ 2 / 2 + 256) + 8 * √(N ^ 2 / 2 + 128)) =
        (2 : ℝ) ^ ((1 : ℝ) / 64) * (1 + 512 / N ^ 2) + 16 * √(N ^ 2 / 2 + 128) / N ^ 2 := by
      field_simp; ring
    rw [e]
    have hA : (2 : ℝ) ^ ((1 : ℝ) / 64) * (1 + 512 / N ^ 2) ≤ 10109 / 10000 * (1 + 512 / N ^ 2) :=
      mul_le_mul_of_nonneg_right h64 (by positivity)
    have hB : 512 / N ^ 2 ≤ 17 / 10000000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hsq2 : √(N ^ 2 / 2 + 128) ≤ 71 / 100 * N := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hC : 16 * √(N ^ 2 / 2 + 128) / N ^ 2 ≤ 65 / 100000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have f4' : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * BL (mA n) := by
    unfold BL; positivity
  have e : X2q n q = ((((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) *
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) *
      ((((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ))) *
      (2 / ((mA n : ℕ) : ℝ) * BL (mA n)) := by
    unfold X2q; ring
  rw [e]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul f1 hR hR0 (by norm_num)) f3 f3'
    (by norm_num)) f4 f4' (by norm_num)) (by norm_num)

/-- `Cg ≤ 10.85` (Part 168's `Cg_le` has `11.1`): `E|g|¹²⁸ ≤ 6.9¹²⁸` and `π < 3.1416`. -/
lemma Cg_le45 : Cg ≤ 1081 / 100 := by
  unfold Cg
  have hg : BstLean.Part162.gmom 128 ≤ (6881 / 1000 : ℝ) ^ (128 : ℕ) := by
    rw [show (128 : ℕ) = 2 * 64 from rfl, BstLean.Part162.gmom_even]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
  have h1 := Real.rpow_le_rpow (BstLean.Part162.gmom_nonneg 128) hg
    (by norm_num : (0 : ℝ) ≤ 1 / 128)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h1
  norm_num at h1
  have hpi := Real.pi_lt_d4
  have h0 : 0 ≤ BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) :=
    Real.rpow_nonneg (BstLean.Part162.gmom_nonneg 128) _
  have h7 : BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ 6881 / 1000 := by simpa using h1
  calc π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ (31416 / 10000) / 2 * (6881 / 1000) :=
        mul_le_mul (by linarith) h7 h0 (by norm_num)
    _ ≤ 1081 / 100 := by norm_num

/-- **`Cg·√t_A·Zop ≤ 0.1`.** -/
theorem Z_num (hn : 17500 ≤ n) : Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n ≤ 16543 / 100000 := by
  have hnR : (17500 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  unfold Zop
  rw [hmR, Real.sqrt_sq (by linarith)]
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set G := BstLean.Part152.gaussMomConst 64
  have hG := G64_le
  have hG0 : 0 ≤ G := BstLean.Part152.gaussMomConst_nonneg 64
  have hs : √N ≤ N / (13228 / 100) := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ √N := Real.sqrt_nonneg _
  have hC := Cg_le45
  have hC0 := Cg_pos
  set T := Cg * √(2 / N ^ 2) * (√(2 / N) * (N + √N + G)) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hT2 : T ^ 2 = Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2 := by
    rw [hT, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hS : N + √N + G ≤ 10122 / 10000 * N := by linarith
  have hS0 : 0 ≤ N + √N + G := by positivity
  have hb : T ^ 2 ≤ 27366 / 1000000 := by
    rw [hT2]
    have h1 : Cg ^ 2 ≤ (1081 / 100) ^ 2 := pow_le_pow_left₀ hC0.le hC 2
    have h2 : (N + √N + G) ^ 2 ≤ (10122 / 10000 * N) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    have e : (1081 / 100) ^ 2 * (2 / N ^ 2) * (2 / N) * (10122 / 10000 * N) ^ 2 =
        (1081 / 100) ^ 2 * 4 * (10122 / 10000) ^ 2 / N := by
      field_simp; ring
    calc Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2
        ≤ (1081 / 100) ^ 2 * (2 / N ^ 2) * (2 / N) * (10122 / 10000 * N) ^ 2 := by gcongr
      _ = (1081 / 100) ^ 2 * 4 * (10122 / 10000) ^ 2 / N := e
      _ ≤ 27366 / 1000000 := by rw [div_le_iff₀ hN0]; nlinarith
  nlinarith

/-- **The numerics of Lemma LJ**: `K2XY n X2 Y2 ≤ 4.7` for every `n ≥ 45 000`, with
`X2 = X2q n ⌊log₂ n⌋` and `Y2 = Y2n n`. -/
theorem K2_num (hn : 17500 ≤ n) : K2XY n (X2q n (qn n / 2)) (Y2n n) ≤ 5 := by
  unfold K2XY
  have hX := X2_num hn
  have hY := Y_num' (n := n) (by omega)
  have hZ := Z_num hn
  have hX0 : 0 ≤ X2q n (qn n / 2) := by
    unfold X2q
    have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
    have : 0 ≤ BL (mA n) := by unfold BL; positivity
    have : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * ((qn n / 2 : ℕ) : ℝ))) := Real.rpow_nonneg (by positivity) _
    apply mul_nonneg; apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
    · apply div_nonneg <;> linarith
    · apply mul_nonneg this; positivity
    · positivity
    · positivity
    · assumption
  have hY0 : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * Y2n n := by
    have := Y2n_pos (n := n) (by omega); positivity
  have hZ0 : 0 ≤ Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n := by
    have := Cg_pos; have := Zop_pos (n := n) (by omega); positivity
  have hs : √(X2q n (qn n / 2) + 2 / ((mA n : ℕ) : ℝ) * Y2n n) ≤ 206253 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs0 := Real.sqrt_nonneg (X2q n (qn n / 2) + 2 / ((mA n : ℕ) : ℝ) * Y2n n)
  nlinarith

end SPart168Num

-- ===== from Part168End.lean =====
section SPart168End
open BstLean.Part168
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part167
variable {n : ℕ}
lemma X2q_pos (hn : 17500 ≤ n) : 0 < X2q n (qn n / 2) := by
  unfold X2q
  have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have hB : 0 < BL (mA n) := by unfold BL; positivity
  have hR : 0 < ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * ((qn n / 2 : ℕ) : ℝ))) := Real.rpow_pos_of_pos hm0 _
  have h1 : 0 < (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) :=
    div_pos (by linarith) (by linarith)
  have h2 : 0 < ((n - 1 - 1 : ℕ) : ℝ) + 128 * ((qn n / 2 : ℕ) : ℝ) := by positivity
  positivity

/-- **Lemma LJ is proved** (paper `t7:p07:LJ` at `ℓ = 128`, `K² ≤ 4.7`), every `n ≥ 45 000`. -/
theorem LJ_proved (hn : 17500 ≤ n) : JM_hyp n (5) :=
  JM_mono (by unfold K2XY; positivity) (K2_num hn)
    (JM_of_XY (by omega) (X2q_pos hn) (Y2n_pos (by omega))
      (XY_of_X hn (X_hyp_proved (by omega) (by have := qh_ge hn; omega))))

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Proposition LG fully proved** (every `n ≥ 45 000`, floor
`d_low = 0.22005`, room `roomK ≥ 0.001892`). Remaining: `BIAS_hyp` on the good set, and the
charge of the caller's event `E_A` within `roomK`. -/
theorem classifier_paper_LG22k (hHQ : BstLean.Part184.M.HQG n) (hn : 17500 ≤ n)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomK + BstLean.Part181.roomX + BstLean.Part184.M.roomL)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (4138 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_X22k hHQ hn (X2q_pos hn) (X_hyp_proved (by omega) (by have := qh_ge hn; omega))
    (K2_num hn) fT wT hf hw t hEA hA hroom hB

end SPart168End

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.J175.M

