import BstLean.Part181T167

/-!
# Part 181 (file `T168`): the T168 link of the chain at `n ≥ 22 000`
(namespace `BstLean.Part179.N30.N27.N26.N25.N24.N23`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of file `Part180T168` (the chain at `n ≥ 24 000`) with `24 000 ↦ 22 000`, in the
sub-namespace `N23` of `BstLean.Part179.N30.N27.N26.N25.N24` (its names shadow those of the
parents; the split data `dP`, `KR`, `dStar`, `fb_of_SEn` are `N30`'s: `sd = 0.452`, `η = 1/50`).
Upstream: `BstLean.Part179.N30.N27.N26.N24.N23.N22.classifier_paper_JM22H` (file `Part180TopJb`): `K² ≤ 5`,
bias root `0.00523`, room `roomK = roomC − 10⁻⁴ ≥ 0.002892`.
Changed constants: `128q ≤ 0.07792n`; `X2 ≤ 2.2446` (factors `1.0057·1.0235·2·1.07792·1.0115`, `f4` with `1/2000`); `Z ≤ 0.1446` (`√N ≤ N/151`); `√(X2 + Y) ≤ 2.061`, so `K² ≈ 4.865 ≤ 5`; `LJ_proved : JM_hyp n 5`.
Every `classifier_paper_*` theorem here takes `hHQ : BstLean.Part181.HQF_stmt` (passed to the top).
The docstrings of the copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22

-- ===== from Part168Num.lean =====
section SPart168Num
open BstLean.Part168
open Real
open BstLean.Part130
open BstLean.Part167
variable {n : ℕ}
lemma q_ge (hn : 22000 ≤ n) : 14 ≤ qn n := by
  unfold qn
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- `128q ≤ 0.035n` for `q = ⌊log₂ n⌋`, every `n ≥ 45 000` (Part 168's `q_lin`, `4096q ≤ n`, needs
`n ≥ 61 440` when `q = 15`). -/
lemma q_lin45 (hn : 22000 ≤ n) : (128 : ℝ) * qn n ≤ 8146 / 100000 * n := by
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
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

/-- **`m^{1/(64q)} ≤ 1.034`.** -/
lemma rpow_m_le (hn : 22000 ≤ n) :
    ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) ≤ 10235 / 10000 := by
  set q := qn n with hq
  have hq16 : (14 : ℝ) ≤ q := by exact_mod_cast q_ge hn
  have hq0 : (0 : ℝ) < q := by linarith
  have hm : ((mA n : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * q + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h := lt_pow_q n
    have h2 : mA n ≤ 2 ^ (2 * q + 2) := by
      unfold mA
      rw [show 2 * q + 2 = (q + 1) * 2 by ring, pow_mul]
      exact Nat.pow_le_pow_left h.le 2
    exact_mod_cast h2
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hm
    (by positivity : (0 : ℝ) ≤ 1 / (64 * (q : ℝ)))
  rw [← Real.rpow_mul (by norm_num)] at h1
  refine h1.trans ?_
  have hexp : ((2 * q + 2 : ℕ) : ℝ) * (1 / (64 * (q : ℝ))) ≤ 15 / 448 := by
    push_cast
    rw [show (2 * (q : ℝ) + 2) * (1 / (64 * (q : ℝ))) = (2 * q + 2) / (64 * q) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans ?_
  have h64 : (442 / 100 : ℝ) ≤ (10235 / 10000) ^ (64 : ℕ) := by norm_num
  have h30 : (2 : ℝ) ^ (15 : ℕ) ≤ (10235 / 10000) ^ (448 : ℕ) := by
    rw [show (448 : ℕ) = 64 * 7 by norm_num, pow_mul]
    calc (2 : ℝ) ^ (15 : ℕ) ≤ (442 / 100) ^ (7 : ℕ) := by norm_num
      _ ≤ ((10235 / 10000) ^ (64 : ℕ)) ^ (7 : ℕ) := pow_le_pow_left₀ (by norm_num) h64 7
  calc (2 : ℝ) ^ ((15 : ℝ) / 448) = ((2 : ℝ) ^ (15 : ℕ)) ^ ((1 : ℝ) / 448) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ ((10235 / 10000 : ℝ) ^ (448 : ℕ)) ^ ((1 : ℝ) / 448) :=
        Real.rpow_le_rpow (by positivity) h30 (by norm_num)
    _ = 10235 / 10000 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

lemma two_rpow_64b : (2 : ℝ) ^ ((1 : ℝ) / 64) ≤ 10109 / 10000 := by
  have hb : (2 : ℝ) ≤ (10109 / 10000) ^ (64 : ℕ) := by norm_num
  have h := Real.rpow_le_rpow (by norm_num) hb (by norm_num : (0 : ℝ) ≤ 1 / 64)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  norm_num at h
  exact h

/-- **`X2 ≤ 2.196`** for `q = ⌊log₂ n⌋`. -/
theorem X2_num (hn : 22000 ≤ n) : X2q n (qn n) ≤ 22525 / 10000 := by
  set q := qn n with hq
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [show n - 1 - 1 = n - 2 by omega]; push_cast [show 2 ≤ n by omega]; ring
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hqn : (128 : ℝ) * q ≤ 8146 / 100000 * n := q_lin45 hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR := rpow_m_le hn
  have hR0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) := Real.rpow_nonneg (by positivity) _
  -- the four factors
  have f1 : (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤ 10059 / 10000 := by
    rw [hd, div_le_iff₀ (by linarith)]; linarith
  have f1' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) := by
    rw [hd]; apply div_nonneg <;> linarith
  have f3 : (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) ≤ 2 * (108146 / 100000) := by
    rw [hd, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have f3' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) := by
    rw [hd]; apply mul_nonneg <;> [nlinarith; positivity]
  have f4 : 2 / ((mA n : ℕ) : ℝ) * BL (mA n) ≤ 10115 / 10000 := by
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
    have hB : 512 / N ^ 2 ≤ 11 / 10000000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hsq2 : √(N ^ 2 / 2 + 128) ≤ 71 / 100 * N := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hC : 16 * √(N ^ 2 / 2 + 128) / N ^ 2 ≤ 52 / 100000 := by
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
lemma Cg_le45 : Cg ≤ 1085 / 100 := by
  unfold Cg
  have hg : BstLean.Part162.gmom 128 ≤ (69 / 10 : ℝ) ^ (128 : ℕ) := by
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
  have h7 : BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ 69 / 10 := by simpa using h1
  calc π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ (31416 / 10000) / 2 * (69 / 10) :=
        mul_le_mul (by linarith) h7 h0 (by norm_num)
    _ ≤ 1085 / 100 := by norm_num

/-- **`Cg·√t_A·Zop ≤ 0.1`.** -/
theorem Z_num (hn : 22000 ≤ n) : Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n ≤ 1479 / 10000 := by
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  unfold Zop
  rw [hmR, Real.sqrt_sq (by linarith)]
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set G := BstLean.Part152.gaussMomConst 64
  have hG := G64_le
  have hG0 : 0 ≤ G := BstLean.Part152.gaussMomConst_nonneg 64
  have hs : √N ≤ N / 148 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ √N := Real.sqrt_nonneg _
  have hC := Cg_le45
  have hC0 := Cg_pos
  set T := Cg * √(2 / N ^ 2) * (√(2 / N) * (N + √N + G)) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hT2 : T ^ 2 = Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2 := by
    rw [hT, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hS : N + √N + G ≤ 10106 / 10000 * N := by linarith
  have hS0 : 0 ≤ N + √N + G := by positivity
  have hb : T ^ 2 ≤ 21861 / 1000000 := by
    rw [hT2]
    have h1 : Cg ^ 2 ≤ (1085 / 100) ^ 2 := pow_le_pow_left₀ hC0.le hC 2
    have h2 : (N + √N + G) ^ 2 ≤ (10106 / 10000 * N) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    have e : (1085 / 100) ^ 2 * (2 / N ^ 2) * (2 / N) * (10106 / 10000 * N) ^ 2 =
        (1085 / 100) ^ 2 * 4 * (10106 / 10000) ^ 2 / N := by
      field_simp; ring
    calc Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2
        ≤ (1085 / 100) ^ 2 * (2 / N ^ 2) * (2 / N) * (10106 / 10000 * N) ^ 2 := by gcongr
      _ = (1085 / 100) ^ 2 * 4 * (10106 / 10000) ^ 2 / N := e
      _ ≤ 21861 / 1000000 := by rw [div_le_iff₀ hN0]; nlinarith
  nlinarith

/-- **The numerics of Lemma LJ**: `K2XY n X2 Y2 ≤ 4.7` for every `n ≥ 45 000`, with
`X2 = X2q n ⌊log₂ n⌋` and `Y2 = Y2n n`. -/
theorem K2_num (hn : 22000 ≤ n) : K2XY n (X2q n (qn n)) (Y2n n) ≤ 5 := by
  unfold K2XY
  have hX := X2_num hn
  have hY := Y_num' (n := n) (by omega)
  have hZ := Z_num hn
  have hX0 : 0 ≤ X2q n (qn n) := by
    unfold X2q
    have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
    have : 0 ≤ BL (mA n) := by unfold BL; positivity
    have : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) := Real.rpow_nonneg (by positivity) _
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
  have hs : √(X2q n (qn n) + 2 / ((mA n : ℕ) : ℝ) * Y2n n) ≤ 2063 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs0 := Real.sqrt_nonneg (X2q n (qn n) + 2 / ((mA n : ℕ) : ℝ) * Y2n n)
  nlinarith

end SPart168Num

-- ===== from Part168End.lean =====
section SPart168End
open BstLean.Part168
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part167
variable {n : ℕ}
lemma X2q_pos (hn : 22000 ≤ n) : 0 < X2q n (qn n) := by
  unfold X2q
  have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have hB : 0 < BL (mA n) := by unfold BL; positivity
  have hR : 0 < ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) := Real.rpow_pos_of_pos hm0 _
  have h1 : 0 < (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) :=
    div_pos (by linarith) (by linarith)
  have h2 : 0 < ((n - 1 - 1 : ℕ) : ℝ) + 128 * (qn n : ℝ) := by positivity
  positivity

/-- **Lemma LJ is proved** (paper `t7:p07:LJ` at `ℓ = 128`, `K² ≤ 4.7`), every `n ≥ 45 000`. -/
theorem LJ_proved (hn : 22000 ≤ n) : JM_hyp n (5) :=
  JM_mono (by unfold K2XY; positivity) (K2_num hn)
    (JM_of_XY (by omega) (X2q_pos hn) (Y2n_pos (by omega))
      (XY_of_X hn (X_hyp_proved (by omega) (by have := q_ge hn; omega))))

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Proposition LG fully proved** (every `n ≥ 45 000`, floor
`d_low = 0.22005`, room `roomK ≥ 0.001792`). Remaining: `BIAS_hyp` on the good set, and the
charge of the caller's event `E_A` within `roomK`. -/
theorem classifier_paper_LG22k (hHQ : BstLean.Part181.HQF_stmt) (hn : 22000 ≤ n)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomK + BstLean.Part181.roomX)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (5154 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_X22k hHQ hn (X2q_pos hn) (X_hyp_proved (by omega) (by have := q_ge hn; omega))
    (K2_num hn) fT wT hf hw t hEA hA hroom hB

end SPart168End

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22

