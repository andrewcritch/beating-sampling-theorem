import BstLean.Part89QDefs2
import BstLean.Part89Aux
import BstLean.Part89Arith

/-!
# Part 89, arithmetic at `d_f = 2`: the threshold `NQ d = 110000 (d+1)² (d+1)!`

* `NQ_ge`, `NQ_2`, `NQ_3`, `NQ_4`: values.
* `arithQ`: the numeric conditions `NumQ` and the bound `gQ(d+1) + 100/n + 20808/N_W ≤ 1/100`
  for `n = m + 1 ≥ NQ d`.
* `costQ`: the strict cost clause for `n ≥ NQ d`, `n ≥ 40 B`.
-/

namespace BstLean.Part89

open BstLean.Part86
open BstLean.Part88 (SE)
open BstLean.Part36 (DD)
open BstLean.Part41 (Mono Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part80 (e80 K80_le)

theorem NQ_ge (d : ℕ) : 110000 ≤ NQ d := by
  unfold NQ
  have h1 : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (d + 1).factorial := Nat.factorial_pos _
  calc 110000 = 110000 * 1 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

theorem NQ_2 : NQ 2 = 5940000 := by
  unfold NQ; norm_num [Nat.factorial]

theorem NQ_3 : NQ 3 = 42240000 := by
  unfold NQ; norm_num [Nat.factorial]

theorem NQ_4 : NQ 4 = 330000000 := by
  unfold NQ; norm_num [Nat.factorial]

private lemma factQ_ge6 (d : ℕ) (hd : 2 ≤ d) : 6 ≤ (d + 1).factorial := by
  calc 6 = (3 : ℕ).factorial := by decide
    _ ≤ (d + 1).factorial := Nat.factorial_le (by omega)

private lemma NQ_facts (d : ℕ) (hd : 2 ≤ d) :
    5940000 ≤ NQ d ∧ 110000 * (d + 1) ^ 2 ≤ NQ d ∧ d + 1 ≤ NQ d := by
  have h6 := factQ_ge6 d hd
  have h9 : 9 ≤ (d + 1) ^ 2 := by nlinarith
  have hA : 110000 * (d + 1) ^ 2 ≤ NQ d := by
    unfold NQ
    calc 110000 * (d + 1) ^ 2 = 110000 * (d + 1) ^ 2 * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  refine ⟨?_, hA, ?_⟩
  · unfold NQ
    calc 5940000 = 110000 * 9 * 6 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h9) h6
  · have : d + 1 ≤ (d + 1) ^ 2 := by nlinarith
    omega

/-- The window constants at `k = 2`. -/
private lemma coreQ (t L c a τ : ℝ) (ha : a = (1 + 2 * t) ^ (2 * 2) - 1)
    (hτ : τ = t * (1 + 2 * t) ^ 2)
    (ht0 : 0 ≤ t) (ht : t ≤ 11 / 100000) (hL0 : 0 ≤ L) (hL : L ≤ 2 / 1000000) (hc : 0 ≤ c) :
    0 ≤ (1 + 1 / 50) * c * (1 + (a + τ + τ ^ 2)) ^ 2 +
        (1 + 1 / (1 / 50)) * (a + τ * (1 + τ) + L * (2 + (a + τ + τ ^ 2))) ^ 2 ∧
    (1 + 1 / 50) * c * (1 + (a + τ + τ ^ 2)) ^ 2 +
        (1 + 1 / (1 / 50)) * (a + τ * (1 + τ) + L * (2 + (a + τ + τ ^ 2))) ^ 2 ≤
      10221 / 10000 * c + 8283 * t ^ 2 + 409 * L ^ 2 := by
  set u : ℝ := 1 + 2 * t with hu
  have hu1 : 1 ≤ u := by linarith
  have hu2 : u ≤ 100022 / 100000 := by linarith
  have husq : u ^ 2 ≤ 100045 / 100000 := by nlinarith
  have husq1 : 1 ≤ u ^ 2 := by nlinarith
  have haeq : a = 2 * t * ((u + 1) * (u ^ 2 + 1)) := by rw [ha, hu]; ring
  have hprod : (u + 1) * (u ^ 2 + 1) ≤ 40014 / 10000 := by
    have := mul_le_mul (by linarith : u + 1 ≤ 200022 / 100000)
      (by linarith : u ^ 2 + 1 ≤ 200045 / 100000) (by linarith) (by norm_num)
    linarith
  have hprod0 : 0 ≤ (u + 1) * (u ^ 2 + 1) := by positivity
  have ha0 : 0 ≤ a := by rw [haeq]; positivity
  have hale : a ≤ 80028 / 10000 * t := by
    rw [haeq]
    have := mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 2 * t)
    linarith
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hτle : τ ≤ 100045 / 100000 * t := by
    rw [hτ]
    have := mul_le_mul_of_nonneg_left husq ht0
    linarith
  have hτs : τ ≤ 12 / 100000 := by linarith
  have hτ2 : τ ^ 2 ≤ 12 / 100000 * τ := by nlinarith
  have hτ20 : 0 ≤ τ ^ 2 := sq_nonneg _
  set e1 : ℝ := a + τ + τ ^ 2 with he1
  have he10 : 0 ≤ e1 := by linarith
  have he1le : e1 ≤ 9004 / 1000 * t := by linarith
  have he1s : e1 ≤ 1 / 1000 := by linarith
  set e2 : ℝ := a + τ * (1 + τ) + L * (2 + e1) with he2
  have he20 : 0 ≤ e2 := by
    have : 0 ≤ L * (2 + e1) := mul_nonneg hL0 (by linarith)
    have : τ * (1 + τ) = τ + τ ^ 2 := by ring
    linarith
  have he2le : e2 ≤ 9004 / 1000 * t + 2001 / 1000 * L := by
    have h1 : L * (2 + e1) ≤ L * (2001 / 1000) := mul_le_mul_of_nonneg_left (by linarith) hL0
    have : τ * (1 + τ) = τ + τ ^ 2 := by ring
    linarith
  have he2sq : e2 ^ 2 ≤ 1624 / 10 * t ^ 2 + 801 / 100 * L ^ 2 := by
    have h1 : e2 ^ 2 ≤ (9004 / 1000 * t + 2001 / 1000 * L) ^ 2 :=
      pow_le_pow_left₀ he20 he2le 2
    have h2 : (9004 / 1000 * t + 2001 / 1000 * L) ^ 2 =
        2 * (9004 / 1000) ^ 2 * t ^ 2 + 2 * (2001 / 1000) ^ 2 * L ^ 2 -
          (9004 / 1000 * t - 2001 / 1000 * L) ^ 2 := by ring
    have h3 := sq_nonneg (9004 / 1000 * t - 2001 / 1000 * L)
    have h4 := sq_nonneg t
    have h5 := sq_nonneg L
    rw [h2] at h1
    generalize (9004 / 1000 * t - 2001 / 1000 * L) ^ 2 = Z at h1 h3
    linarith
  have hsq1 : (1 + e1) ^ 2 ≤ 1002001 / 1000000 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + e1)
      (by linarith : 1 + e1 ≤ 1001 / 1000) 2
    norm_num at this ⊢; linarith
  have hsq0 : 0 ≤ (1 + e1) ^ 2 := sq_nonneg _
  have hc1 : c * (1 + e1) ^ 2 ≤ c * (1002001 / 1000000) := mul_le_mul_of_nonneg_left hsq1 hc
  have hc0 : 0 ≤ c * (1 + e1) ^ 2 := mul_nonneg hc hsq0
  have he2sq0 : 0 ≤ e2 ^ 2 := sq_nonneg _
  have e51 : (1 + 1 / (1 / 50) : ℝ) = 51 := by norm_num
  rw [e51]
  have e3 : (1 + 1 / 50 : ℝ) * c * (1 + e1) ^ 2 = 51 / 50 * (c * (1 + e1) ^ 2) := by ring
  rw [e3]
  generalize c * (1 + e1) ^ 2 = P at hc1 hc0
  generalize e2 ^ 2 = R at he2sq he2sq0
  have ht2n := sq_nonneg t
  have hL2n := sq_nonneg L
  constructor
  · linarith
  · linarith

private lemma cVW_leQ (t L c : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 11 / 100000) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 / 1000000) (hc : 0 ≤ c) :
    0 ≤ cVW 2 t L c (1 / 50) ∧
      cVW 2 t L c (1 / 50) ≤ 10221 / 10000 * c + 8283 * t ^ 2 + 409 * L ^ 2 := by
  unfold cVW e2S e1S a1S tauS
  simp only [Nat.cast_ofNat]
  exact coreQ t L c _ _ rfl rfl ht0 ht hL0 hL hc

private lemma XQ_leQ (d : ℕ) (hd : 2 ≤ d) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 10000000) :
    0 ≤ XQ (1 / 2) 6 8 (kapQ d β * ((d : ℝ) + 1)) d (49 / 100) ∧
      XQ (1 / 2) 6 8 (kapQ d β * ((d : ℝ) + 1)) d (49 / 100) ≤ 9483 / 100 * ((d : ℝ) + 1) ^ 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set D : ℝ := (d : ℝ) + 1 with hD
  have hdD : (d : ℝ) = D - 1 := by rw [hD]; ring
  have hD3 : 3 ≤ D := by linarith
  have hκ0 : 0 ≤ kapQ d β := by
    unfold kapQ
    exact div_nonneg (by nlinarith) (by linarith)
  have hκ : kapQ d β ≤ 161601 / 10000 * D := by
    unfold kapQ
    rw [← hD, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ D) hβ0,
      mul_nonneg (by linarith : (0 : ℝ) ≤ D) (sub_nonneg.mpr hβ)]
  have hκD0 : 0 ≤ kapQ d β * D := mul_nonneg hκ0 (by linarith)
  have hκD : kapQ d β * D ≤ 161601 / 10000 * D ^ 2 := by
    have := mul_le_mul_of_nonneg_right hκ (by linarith : (0 : ℝ) ≤ D)
    nlinarith
  have hq : 0 ≤ (2 * D - 3) * (D - 3) := mul_nonneg (by linarith) (by linarith)
  have hD9 : 9 ≤ D ^ 2 := by nlinarith
  unfold XQ c0q
  rw [hdD]
  generalize kapQ d β * D = y at hκD0 hκD
  constructor
  · have : 0 ≤ (1 + 1 / 8 : ℝ) * ((2 + 1 / 2) * (1 + 1 / 6) * y +
        ((1 + 1 / (1 / 2)) * (4184 / 1000 * (8 * (1733 / 1000))) + 8) * (D - 1) / 2) /
        (2 * (49 / 100)) := by
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg (by norm_num)
      nlinarith
    linarith
  · have hq' : 0 ≤ 2 * D ^ 2 - 9 * D + 9 := by nlinarith
    have e : (1 + 8 : ℝ) * (2 + 1 / 2) * (1 + 6) + (1 + 1 / 8) * ((2 + 1 / 2) * (1 + 1 / 6) * y +
        ((1 + 1 / (1 / 2)) * (4184 / 1000 * (8 * (1733 / 1000))) + 8) * (D - 1) / 2) /
        (2 * (49 / 100)) =
        315 / 2 + 1875 / 560 * y + 2559669300 / 24500000 * (D - 1) := by
      ring
    rw [e]
    linarith

private lemma var_leQ (S W N L ν : ℝ) (hS : S ≤ 233 / 100) (hW : 0 ≤ W) (hN : 0 < N)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 / 1000000) (hν : ν ≤ 106 / 100000) :
    S * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) / ((1 - (1 / 8) ^ 2) * (1 - ν)) ≤
      3226 / 1000 * W := by
  have h1 : (0 : ℝ) < 1 - L := by linarith
  have h2 : (0 : ℝ) < 1 - ν := by linarith
  have hp : (999996 : ℝ) / 1000000 ≤ (1 - L) ^ 2 := by nlinarith [sq_nonneg L]
  have hpq : (999996 : ℝ) / 1000000 * (99894 / 100000) ≤ (1 - L) ^ 2 * (1 - ν) :=
    mul_le_mul hp (by linarith) (by norm_num) (sq_nonneg _)
  have hden : (0 : ℝ) < (1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 8) ^ 2) * (1 - ν)) := by
    positivity
  have e : S * (N * W) / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * N) / ((1 - (1 / 8) ^ 2) * (1 - ν)) =
      S * W / ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 8) ^ 2) * (1 - ν))) := by
    field_simp
  rw [e, div_le_iff₀ hden]
  have hSW : S * W ≤ 233 / 100 * W := mul_le_mul_of_nonneg_right hS hW
  have hk : (233 : ℝ) / 100 ≤
      3226 / 1000 * ((1 - 1 / 7) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 8) ^ 2) * (1 - ν))) := by
    have : (1 - 1 / 7 : ℝ) ^ 2 * (1 - L) ^ 2 * ((1 - (1 / 8) ^ 2) * (1 - ν)) =
        (36 / 49 * (63 / 64)) * ((1 - L) ^ 2 * (1 - ν)) := by ring
    rw [this]; linarith
  have := mul_le_mul_of_nonneg_right hk hW
  linarith

private lemma tS_leQ (n : ℕ) (hn : 5940000 ≤ n) :
    0 ≤ tS n (1 / (4 * (n : ℝ))) ∧ tS n (1 / (4 * (n : ℝ))) ≤ 11 / 100000 ∧
      tS n (1 / (4 * (n : ℝ))) ^ 2 * n ≤ 626 / 10000 := by
  have hN : (5940000 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = N := Real.sq_sqrt hN0.le
  have h4 : (0 : ℝ) < 4 * N - 1 := by linarith
  have e : tS n (1 / (4 * N)) = s / (4 * N - 1) := by
    unfold tS
    have hb : 1 - 1 / (4 * N) = (4 * N - 1) / (4 * N) := by field_simp
    rw [← hNdef, ← hs, hb]
    field_simp
  rw [e]
  set T : ℝ := s / (4 * N - 1) with hT
  have hT0 : 0 ≤ T := div_nonneg hs0 h4.le
  have hTm : T * (4 * N - 1) = s := by rw [hT]; field_simp
  have hT2 : T ^ 2 * (4 * N - 1) ^ 2 = N := by rw [← mul_pow, hTm, hs2]
  have hq : N ^ 2 * (10000 / 626) ≤ (4 * N - 1) ^ 2 := by nlinarith
  have hTN : T ^ 2 * N ≤ 626 / 10000 := by
    have h1 : T ^ 2 * (N ^ 2 * (10000 / 626)) ≤ N :=
      (mul_le_mul_of_nonneg_left hq (sq_nonneg T)).trans hT2.le
    have h2 : T ^ 2 * N * N ≤ 626 / 10000 * N := by nlinarith
    exact le_of_mul_le_mul_right h2 hN0
  refine ⟨hT0, ?_, hTN⟩
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (11 / 100000 : ℝ) ^ 2 < T ^ 2 := by nlinarith
  have h2 : T ^ 2 * 5940000 ≤ T ^ 2 * N := mul_le_mul_of_nonneg_left hN (sq_nonneg T)
  nlinarith

set_option maxHeartbeats 800000 in
theorem arithQ (d m : ℕ) (hd : 2 ≤ d) (hn : NQ d ≤ m + 1) :
    NumQ m d (1 / 2) 6 8 (1 / 50) (1 / 100) (1 / 7) (1 / (4 * ((m + 1 : ℕ) : ℝ))) (1 / 8) ∧
    gQ m d (1 / 2) 6 8 (1 / 50) (1 / 100) (1 / 7) (1 / (4 * ((m + 1 : ℕ) : ℝ))) (1 / 8)
        ((d : ℝ) + 1) + 100 / ((m + 1 : ℕ) : ℝ) + 20808 / DWr (m + 1) (JR (m + 1) d) ≤ 1 / 100 := by
  obtain ⟨hq6, hqD, hqd⟩ := NQ_facts d hd
  have hn6 : 5940000 ≤ m + 1 := hq6.trans hn
  have hdn : d ≤ m + 1 := by omega
  have h100 : 100 ≤ m + 1 := by omega
  have hNW := DWr_ge_cube (m + 1) d hd hdn h100
  obtain ⟨ht0, ht1, ht2⟩ := tS_leQ (m + 1) hn6
  unfold gQ semiBound89
  have hNr : (5940000 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn6
  have hmN : (m : ℝ) = ((m + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have hNX : 110000 * ((d : ℝ) + 1) ^ 2 * ((d + 1).factorial : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : ((NQ d : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hn
    refine le_trans (le_of_eq ?_) this
    simp only [NQ]; push_cast; ring
  have hF6 : (6 : ℝ) ≤ ((d + 1).factorial : ℝ) := by exact_mod_cast factQ_ge6 d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hCL : CLs d = 101 / 100 * ((d + 1).factorial : ℝ) := rfl
  have h5000 : 5000 ≤ m := by omega
  clear hq6 hqD hqd hn6 hn
  rw [hCL, hmN]
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hNdef
  set F : ℝ := ((d + 1).factorial : ℝ) with hFdef
  set D : ℝ := (d : ℝ) + 1 with hDdef
  set NW : ℝ := DWr (m + 1) (JR (m + 1) d) with hNWdef
  set β : ℝ := 1 / (4 * N) with hβdef
  set t : ℝ := tS (m + 1) β with htdef
  set L : ℝ := 101 / 100 * F / (N - 1) with hLdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have hD3 : (3 : ℝ) ≤ D := by linarith
  have hD9 : (9 : ℝ) ≤ D ^ 2 := by nlinarith
  have hL0 : 0 ≤ L := div_nonneg (by linarith) hN1.le
  have hLM : L * (N - 1) = 101 / 100 * F := by rw [hLdef]; field_simp
  have hDF : 9 * F ≤ D ^ 2 * F := mul_le_mul_of_nonneg_right hD9 (by linarith)
  -- L ≤ 1.0203e-6
  have hL1 : L ≤ 10203 / 10000000000 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : L * (990000 * F - 1) ≤ L * (N - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hL0
    nlinarith [mul_nonneg (sub_nonneg.mpr hF6) (by linarith : (0 : ℝ) ≤ 990000 * L - 101 / 100)]
  have hL2 : L ≤ 2 / 1000000 := by linarith
  -- L D² ≤ 9.182e-6
  have hLD : L * D ^ 2 ≤ 9182 / 1000000000 := by
    have h1 : L * (110000 * D ^ 2 * F) ≤ L * N := mul_le_mul_of_nonneg_left hNX hL0
    have h2 : (L * D ^ 2) * F ≤ 9182 / 1000000000 * F := by nlinarith
    exact le_of_mul_le_mul_right h2 (by linarith)
  have hLD0 : 0 ≤ L * D ^ 2 := mul_nonneg hL0 (by positivity)
  have hLsq : L ^ 2 ≤ 2 / 1000000 * L := by nlinarith
  -- β
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  have hβN : β * N = 1 / 4 := by rw [hβdef]; field_simp
  have hβs : β ≤ 1 / 10000000 := by
    have : β * 5940000 ≤ β * N := mul_le_mul_of_nonneg_left hNr hβ0.le
    linarith
  -- N_W
  have hN3 : N * (5940000 : ℝ) ^ 2 ≤ N ^ 3 := by
    have : (5940000 : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by norm_num) hNr 2
    nlinarith
  have hNW0 : 0 < NW := by linarith [pow_pos hN0 3]
  have hNWs : 20808 / NW ≤ 1 / 1000000 := by
    rw [div_le_iff₀ hNW0]; nlinarith
  -- ν
  have hsq : (99 / 100 * (1 / 8) * β) ^ 2 * N ^ 2 = (99 / 3200) ^ 2 := by
    have : (99 / 100 * (1 / 8) * β) ^ 2 * N ^ 2 = (99 / 3200) ^ 2 * (4 * (β * N)) ^ 2 := by ring
    rw [this, hβN]; norm_num
  have hXpos : (1894 : ℝ) ≤ NW * (99 / 100 * (1 / 8) * β) ^ 2 := by
    have h1 : N ^ 3 / 3 * (99 / 100 * (1 / 8) * β) ^ 2 ≤ NW * (99 / 100 * (1 / 8) * β) ^ 2 :=
      mul_le_mul_of_nonneg_right hNW (sq_nonneg _)
    have h2 : N ^ 3 / 3 * (99 / 100 * (1 / 8) * β) ^ 2 = N / 3 * (99 / 3200) ^ 2 := by
      rw [← hsq]; ring
    rw [h2] at h1
    nlinarith
  have hν : 2 / (NW * (99 / 100 * (1 / 8) * β) ^ 2) ≤ 106 / 100000 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  -- SE
  have hS : SE (2 * 2) β (1 / 8) ≤ 233 / 100 := by
    have h := SE_two_k_le 2 le_rfl β hβ0.le (by linarith)
    have h8 : (1 : ℝ) / (4 * ((2 : ℕ) : ℝ)) = 1 / 8 := by norm_num
    rw [h8] at h
    push_cast at h
    linarith
  -- X and cV0
  obtain ⟨hX0, hX⟩ := XQ_leQ d hd β hβ0.le hβs
  rw [← hDdef] at hX0 hX
  have hfr0 : 0 ≤ 2 * L / (1 - L) := div_nonneg (by linarith) (by linarith)
  have hfr : 2 * L / (1 - L) ≤ 200001 / 100000 * L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hc0 : 0 ≤ cV0Q d L (1 / 2) 6 8 β D := by
    unfold cV0Q; exact mul_nonneg hfr0 hX0
  have hc : cV0Q d L (1 / 2) 6 8 β D ≤ 18967 / 100 * (L * D ^ 2) := by
    unfold cV0Q
    have := mul_le_mul hfr hX hX0 (by linarith : (0 : ℝ) ≤ 200001 / 100000 * L)
    nlinarith
  obtain ⟨hW0, hW⟩ := cVW_leQ t L (cV0Q d L (1 / 2) 6 8 β D) ht0 ht1 hL0 hL2 hc0
  have hV := var_leQ (SE (2 * 2) β (1 / 8))
    (cVW 2 t L (cV0Q d L (1 / 2) 6 8 β D) (1 / 50)) N L
    (2 / (NW * (99 / 100 * (1 / 8) * β) ^ 2)) hS hW0 hN0 hL0 hL2 hν
  have htN : t ^ 2 ≤ 626 / 10000 * (1 / N) := by
    rw [mul_one_div, le_div_iff₀ hN0]; exact ht2
  have hinv : 1 / N ≤ 1 / 5940000 := one_div_le_one_div_of_le (by norm_num) hNr
  have hinv0 : 0 ≤ 1 / N := by positivity
  have hE : 5 / 2 * (((2 : ℕ) : ℝ) + 1) ^ 2 * (N * L + 2) / (1 / 100 * N) =
      2250 * L + 4500 * (1 / N) := by
    push_cast; field_simp; ring
  have h100N : 100 / N = 100 * (1 / N) := by ring
  refine ⟨⟨h100, h5000, hdn, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_, hβ0, by linarith, by norm_num, by norm_num,
    by nlinarith, by linarith⟩, ?_⟩
  · rw [hCL, hmN]; linarith
  · rw [hCL, hmN]; linarith
  · rw [hE, h100N]
    linarith

private lemma card_monoQ (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => Nat.multichoose n i) (d + 1)]
  rw [Nat.sum_range_multichoose, ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma pow_le_fact_chooseQ (n k : ℕ) : (n + 1) ^ k ≤ k.factorial * (n + k).choose k := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (n + 1) k

/-- The cost clause from the three size conditions (the proof of `cost89`). -/
private lemma costGen (d k n B : ℕ) (hd1 : 1 ≤ d) (hkd : k ≤ d)
    (hbig : 8 * ((k + 2) ^ 3 * (d + 1) ^ k * k.factorial) ≤ n)
    (hd3 : 3 * (d + 1) ≤ n) (h4000 : 4000 ≤ n) (hB : 40 * B ≤ n)
    (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d k) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  set C : ℕ := (n + d).choose d with hC
  have hNN : NN n d = (C : ℝ) := by unfold NN; rw [card_monoQ]
  have hPn : Pn n d = (n : ℝ) * C := by unfold Pn; rw [BstLean.Part36.DD_eq]
  have hCn : n + 1 ≤ C := BstLean.Part74.choose_ge74 n d hd1
  have hpow : (n + 1) ^ k ≤ k.factorial * C := by
    refine (pow_le_fact_chooseQ n k).trans (Nat.mul_le_mul_left _ ?_)
    rw [hC, ← Nat.choose_symm_add (a := n) (b := k), ← Nat.choose_symm_add (a := n) (b := d)]
    exact Nat.choose_le_choose n (by omega)
  have hK := K80_le n
  have hbase : 91 / 100 * Pn n d / (1 / 2) ^ 2 ≤ baseline n d (1 / 2) := le_max_right _ _
  have hcl : (pgc : ℝ) ≤ 2 * Pn n d + ((d : ℝ) + 1) * NN n d +
      4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k := by
    refine hpg.trans (le_of_eq ?_); unfold costLine56; rfl
  rw [hPn] at hbase hcl
  rw [hNN] at hcl
  set N : ℝ := (n : ℝ)
  set Cr : ℝ := (C : ℝ)
  have hN0 : (4000 : ℝ) ≤ N := by
    show (4000 : ℝ) ≤ (n : ℝ)
    exact_mod_cast h4000
  have hCr : N + 1 ≤ Cr := by
    show (n : ℝ) + 1 ≤ (C : ℝ)
    exact_mod_cast hCn
  have hBr : 40 * (B : ℝ) ≤ N := by
    show 40 * (B : ℝ) ≤ (n : ℝ)
    exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hd3r : 3 * ((d : ℝ) + 1) ≤ N := by
    show 3 * ((d : ℝ) + 1) ≤ (n : ℝ)
    exact_mod_cast hd3
  have hT : 4 * ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (N + 1) ^ k ≤ N * Cr / 2 := by
    have h1 : ((n : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * Cr := by
      show ((n : ℝ) + 1) ^ k ≤ (k.factorial : ℝ) * (C : ℝ)
      exact_mod_cast hpow
    have h2 : 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) ≤ N := by
      show 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) ≤ (n : ℝ)
      exact_mod_cast hbig
    have h0 : (0 : ℝ) ≤ ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k := by positivity
    have h3 : ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (N + 1) ^ k ≤
        ((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * ((k.factorial : ℝ) * Cr) :=
      mul_le_mul_of_nonneg_left h1 h0
    have hCr0 : (0 : ℝ) ≤ Cr := by linarith
    have h4 : 8 * (((k : ℝ) + 2) ^ 3 * ((d : ℝ) + 1) ^ k * (k.factorial : ℝ)) * Cr ≤ N * Cr :=
      mul_le_mul_of_nonneg_right h2 hCr0
    nlinarith
  have hD : ((d : ℝ) + 1) * Cr ≤ N * Cr / 3 := by
    have hCr0 : (0 : ℝ) ≤ Cr := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hd3r hCr0]
  have hM : (B : ℝ) * (N + (KRK 1 n e80 : ℝ) + 1) ≤ N * Cr / 2 := by
    have h1 : (B : ℝ) * (N + (KRK 1 n e80 : ℝ) + 1) ≤ B * (17 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) hB0
    have h2 : (B : ℝ) * 34 ≤ Cr := by linarith
    have h3 : (B : ℝ) * 34 * N ≤ Cr * N := mul_le_mul_of_nonneg_right h2 (by linarith)
    nlinarith
  have hpos : 0 < N * Cr := by nlinarith
  have e : 91 / 100 * (N * Cr) / (1 / 2) ^ 2 = 364 / 100 * (N * Cr) := by norm_num; ring
  rw [e] at hbase
  linarith

theorem costQ (d n B : ℕ) (hd : 2 ≤ d) (hn : NQ d ≤ n) (hB : 40 * B ≤ n) (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ (B : ℝ) * ((n : ℝ) + (KRK 1 n e80 : ℝ) + 1))
    (hpg : (pgc : ℝ) ≤ costLine56 n d 2) :
    (pmc : ℝ) + pgc < baseline n d (1 / 2) := by
  obtain ⟨hq6, hqD, hqd⟩ := NQ_facts d hd
  have hbig : 8 * ((2 + 2) ^ 3 * (d + 1) ^ 2 * (2 : ℕ).factorial) ≤ n := by
    have : 8 * ((2 + 2) ^ 3 * (d + 1) ^ 2 * (2 : ℕ).factorial) = 1024 * (d + 1) ^ 2 := by
      norm_num [Nat.factorial]; ring
    rw [this]
    have : 1024 * (d + 1) ^ 2 ≤ 110000 * (d + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
    omega
  have hsq : d + 1 ≤ (d + 1) ^ 2 := by nlinarith
  exact costGen d 2 n B (by omega) hd hbig (by omega) (by omega) hB pmc pgc hpm hpg

end BstLean.Part89

#print axioms BstLean.Part89.arithQ
#print axioms BstLean.Part89.costQ
#print axioms BstLean.Part89.NQ_ge
#print axioms BstLean.Part89.NQ_2
#print axioms BstLean.Part89.NQ_3
#print axioms BstLean.Part89.NQ_4
