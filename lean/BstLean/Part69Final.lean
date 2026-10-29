import BstLean.Part69Weights
import BstLean.Part69Prog
import BstLean.Part64Final
import BstLean.Part66T1Ord

/-!
# Part 69: Theorem 1 at `d_M = d_f = 2` without amortization

* `eval69`: the line program `pg` of Part 56, fed the outputs of the single-use moment program
  `pm1` (`momProg69_exists_nat`), returns `gLineW (surrRK n K t v)`, the function that Part 56's
  accuracy theorem controls. Only the keys with `2l ≤ i` matter (`weights69`).
* `part69_single`: the statement of `part56_general` at `k = d = 2`, with the counter clause
  replaced by `cost(pm1) + cost(pg) < baseline n 2 ε`. The accuracy threshold is Part 64's.
* `part69_single_cert`: the same at `C = 1`, `ε = 1/2` for every `n ≥ 10^86` (Part 66's ordered
  certificate `part66T1O_22`).
-/

namespace BstLean.Part69

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount Pn NN)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56

variable {n : ℕ}

/-- The weaker specification of a moment program: exact surrogate weights at the keys `2l ≤ i`. -/
def MomSpecUsed69 (pm : Prog (InM56 n) (KeyRK 2 2)) (K : ℕ) : Prop :=
  ∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → UnitV v → ∀ κ : KeyRK 2 2, 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) →
    pm.eval (inRK t v) κ = wRK (surrRK n K t v) 2 v κ

/-- **Evaluation under the weaker specification.** -/
theorem eval69 (pm : Prog (InM56 n) (KeyRK 2 2)) (pg : Prog (In56 n 2 2) Unit) (K : ℕ)
    (hpm : MomSpecUsed69 pm K) (hpg : GSpec56 pg) (t : ℝ) (v : Fin n → ℝ) (ht : 0 ≤ t)
    (hv : UnitV v) (f0 : ℝ) (T : Tens n) (hT : TSymm 2 T) (M : CoefIdxD n 2 → ℝ) :
    pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () = gLineW (surrRK n K t v) 2 f0 T v M := by
  rw [hpg f0 T M v _ hT]
  unfold gLineW gW
  apply Finset.sum_congr rfl
  intro κ _
  split_ifs with h
  · rw [hpm t v ht hv κ h]
  · rfl

/-- The single-use moment program of `Part69Prog` meets the weaker specification. -/
theorem momProg69_used (n K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (InM56 n) (KeyRK 2 2), heavyCount pm = 0 ∧ MomSpecUsed69 pm K ∧
      pm.cost ≤ 11 * n + 23 * K + 194 := by
  obtain ⟨pm, h0, hev, hc⟩ := momProg69_exists_nat n K
  exact ⟨pm, h0, fun t v ht hv κ hκ => (hev t v κ).trans (weights69 hn K t ht v hv κ hκ), hc⟩

/-! ## Cost -/

theorem ceil_le69 (x : ℝ) : (⌈x⌉₊ : ℝ) ≤ max x 0 + 1 := by
  rcases le_or_gt x 0 with h | h
  · rw [Nat.ceil_eq_zero.mpr h]; simp only [Nat.cast_zero]; linarith [le_max_right x 0]
  · have := Nat.ceil_lt_add_one h.le
    rw [max_eq_left h.le]; linarith

theorem sqrt_le69 (y B : ℝ) (hy : y ≤ B) (hB : 0 ≤ B) : Real.sqrt y ≤ B + 1 := by
  rcases le_or_gt y 0 with h | h
  · rw [Real.sqrt_eq_zero'.mpr h]; linarith
  · have h1 := Real.sq_sqrt h.le
    have h2 := Real.sqrt_nonneg y
    nlinarith [sq_nonneg (Real.sqrt y - 1)]

/-- `K = Kof43 A e ≤ (1 + 2|L|)|A| + |L|/3 + L²/9 + 2`, `L = Leta e`. -/
theorem K_le69 (A e : ℝ) :
    (BstLean.Part43.Kof43 A e : ℝ) ≤
      (1 + 2 * |BstLean.Part43.Leta e|) * |A| + |BstLean.Part43.Leta e| / 3 +
        BstLean.Part43.Leta e ^ 2 / 9 + 2 := by
  unfold BstLean.Part43.Kof43 BstLean.Part43.ustar
  set L := BstLean.Part43.Leta e
  have hs := sqrt_le69 (L ^ 2 / 9 + 2 * A * L) (L ^ 2 / 9 + 2 * |A| * |L|)
    (by
      have : A * L ≤ |A| * |L| := by rw [← abs_mul]; exact le_abs_self _
      linarith)
    (by positivity)
  have hc := ceil_le69 (A + (L / 3 + Real.sqrt (L ^ 2 / 9 + 2 * A * L)))
  have hA := le_abs_self A
  have hL := le_abs_self L
  have hAL := mul_nonneg (abs_nonneg A) (abs_nonneg L)
  have hsq := Real.sqrt_nonneg (L ^ 2 / 9 + 2 * A * L)
  refine hc.trans ?_
  rcases le_total (A + (L / 3 + Real.sqrt (L ^ 2 / 9 + 2 * A * L))) 0 with h | h
  · rw [max_eq_right h]; nlinarith [abs_nonneg A, abs_nonneg L, sq_nonneg L]
  · rw [max_eq_left h]; nlinarith [abs_nonneg A, abs_nonneg L]

theorem Pn2_69 (n : ℕ) : Pn n 2 = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := DD2_69

/-- For every `α, β`, the single-use cost `11 n + 23 (α n + β) + 194` is below `c · P` for large `n`. -/
theorem cost_small69 (α β c : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 < c) :
    ∃ n1 : ℕ, ∀ n : ℕ, n1 ≤ n →
      11 * (n : ℝ) + 23 * (α * n + β) + 194 ≤ c * Pn n 2 := by
  set X := 11 + 23 * α + 23 * β + 194
  refine ⟨⌈2 * X / c⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (⌈2 * X / c⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hX : 2 * X / c ≤ n := (Nat.le_ceil _).trans (by linarith)
  have hX' : 2 * X ≤ c * n := by rw [div_le_iff₀ hc] at hX; linarith
  have h1 : (1 : ℝ) ≤ n := le_trans (by linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * X / c⌉₊]) hn1
  rw [Pn2_69]
  have hXn : 11 * (n : ℝ) + 23 * (α * n + β) + 194 ≤ X * n := by
    simp only [X]; nlinarith
  have : X * n ≤ c * ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) := by
    have hX0 : 0 ≤ X := by simp only [X]; positivity
    nlinarith [mul_le_mul_of_nonneg_right hX' (by positivity : (0 : ℝ) ≤ (n : ℝ) * n)]
  linarith

/-! ## The headline -/

/-- **Theorem 1 at `d_M = d_f = 2` without amortization.** For `0 < ε_lo ≤ ε_hi`,
`ε_hi² < 91/200` and every `C`, there are `η > 0` and `n₀ ≥ 100` such that for every `n ≥ n₀` a
moment program `pm` (constants `0`, `1`; reads `t`, `v`; cost `≤ 11 n + 23 K + 194`; exact surrogate
weights at every key that `pg` reads) and the line program `pg` of Part 56 satisfy, for every unit
`v`, `t ∈ [0, C n]`, `ε ∈ [ε_lo, ε_hi]` and admissible `f` of degree 2: the failure probability over
`M` uniform on the coefficient sphere is `≤ 1/100`, and `cost(pm) + cost(pg) < baseline n 2 ε`. -/
theorem part69_single (C εlo εhi : ℝ) (hlo : 0 < εlo) (hlh : εlo ≤ εhi) (hhi : εhi ^ 2 < 91 / 200) :
    ∃ (η : ℝ) (n0 : ℕ), 0 < η ∧ 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK 2 2)) (pg : Prog (In56 n 2 2) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed69 pm (KRK C n η) ∧ GSpec56 pg ∧
        (pm.cost : ℝ) ≤ 11 * n + 23 * (KRK C n η) + 194 ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm 2 T → 0 < frob (T 2) →
          stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) 2 f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) 2 f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          (pm.cost : ℝ) + pg.cost < baseline n 2 ε := by
  have hfail := BstLean.Part64.part64_fail 2 2 le_rfl le_rfl C εlo εhi hlo
  set η := eRK 2 (BstLean.Part64.s64 2) εlo
  have hεhi : 0 < εhi := lt_of_lt_of_le hlo hlh
  obtain ⟨nc, hc⟩ := costLine56_lt 2 2 (by norm_num) le_rfl εhi hεhi hhi
  have hν := nuRK_pos εhi hhi
  set L := BstLean.Part43.Leta η
  obtain ⟨n1, h1⟩ := cost_small69 ((1 + 2 * |L|) * |C|) (|L| / 3 + L ^ 2 / 9 + 2)
    (nuRK εhi * (91 / 100) / εhi ^ 2) (by positivity) (by positivity) (by positivity)
  have hη0 : 0 < η := by
    simp only [η]; unfold eRK etaRK BstLean.Part43.xi43
    have := BstLean.Part64.tsb64_pos 2
    unfold BstLean.Part64.s64; positivity
  refine ⟨η, max (max (BstLean.Part64.NF56 2 2 C εlo) nc) (max n1 100), hη0, le_max_of_le_right
    (le_max_right _ _), fun n hn => ?_⟩
  have hnf : BstLean.Part64.NF56 2 2 C εlo ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn100 : 100 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n 2 2 (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := momProg69_used n (KRK C n η) (by omega)
  have hpmc' : (pm.cost : ℝ) ≤ 11 * n + 23 * (KRK C n η) + 194 := by exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc', fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have heval : ∀ M : CoefIdxD n 2 → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK C n η) t v) 2 f0 T v M :=
      fun M => eval69 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [heval]
    exact hfail n hnf v hv t ht0 ht ε hε1 hε2 f0 T hT hTk
  · have hK : (KRK C n η : ℝ) ≤ (1 + 2 * |L|) * |C| * n + (|L| / 3 + L ^ 2 / 9 + 2) := by
      have := K_le69 (C * n) η
      rw [abs_mul, Nat.abs_cast] at this
      unfold KRK; linarith
    have hm := h1 n hn1
    have hP : 0 < Pn n 2 := by rw [Pn2_69]; positivity
    have hε : 0 < ε := lt_of_lt_of_le hlo hε1
    have hbase : 91 / 100 * Pn n 2 / εhi ^ 2 ≤ baseline n 2 ε := by
      unfold baseline
      refine le_trans ?_ (le_max_right _ _)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ hε.le hε2 2
    have hcl := hc n hnc
    have : (pm.cost : ℝ) ≤ nuRK εhi * (91 / 100) / εhi ^ 2 * Pn n 2 := by
      calc (pm.cost : ℝ) ≤ 11 * n + 23 * (KRK C n η) + 194 := hpmc'
        _ ≤ 11 * (n : ℝ) + 23 * ((1 + 2 * |L|) * |C| * n + (|L| / 3 + L ^ 2 / 9 + 2)) + 194 := by
          linarith
        _ ≤ _ := hm
    have e : nuRK εhi * (91 / 100) / εhi ^ 2 * Pn n 2 + (1 - nuRK εhi) * (91 / 100) * Pn n 2 /
        εhi ^ 2 = 91 / 100 * Pn n 2 / εhi ^ 2 := by field_simp; ring
    linarith

/-! ## The certificate at `C = 1`, `ε = 1/2` -/

/-- The surrogate order of Part 66's certificate. -/
noncomputable def eC69 : ℝ := eRK 2 (BstLean.Part66.tO (2 * 2) (1 / 200) / 4) (1 / 2)

theorem Leta_le69 : |BstLean.Part43.Leta eC69| ≤ 10 ^ 23 := by
  set s := BstLean.Part66.tO (2 * 2) (1 / 200) / 4 with hs
  have hs40 : (10 : ℝ) ^ (-40 : ℤ) ≤ s := by
    rw [hs, show 2 * 2 = 4 by rfl, BstLean.Part66.tO_4]; norm_num
  have hsq : (10 : ℝ) ^ (-20 : ℤ) ≤ Real.sqrt s := by
    rw [show (10 : ℝ) ^ (-40 : ℤ) = ((10 : ℝ) ^ (-20 : ℤ)) ^ 2 by norm_num] at hs40
    calc (10 : ℝ) ^ (-20 : ℤ) = Real.sqrt (((10 : ℝ) ^ (-20 : ℤ)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs40
  set η := BstLean.Part43.etaQ eC69
  have hη : η = min (Real.sqrt s / 600) (1 / 2) := by
    simp only [η, BstLean.Part43.etaQ, eC69, eRK, etaRK, BstLean.Part43.xi43, ← hs]
    congr 1; field_simp; norm_num
  have hηlo : (10 : ℝ) ^ (-20 : ℤ) / 600 ≤ η := by
    rw [hη]; exact le_min (div_le_div_of_nonneg_right hsq (by norm_num)) (by norm_num)
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hηlo
  have hL0 : 0 ≤ BstLean.Part43.Leta eC69 := by
    unfold BstLean.Part43.Leta
    apply Real.log_nonneg
    rw [le_div_iff₀ hη0]; linarith
  rw [abs_of_nonneg hL0]
  unfold BstLean.Part43.Leta
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [add_div, div_self hη0.ne', add_sub_cancel_right, div_le_iff₀ hη0]
  calc (1 : ℝ) = 10 ^ 23 * (10 ^ (-20 : ℤ) / 600) * (600 / 1000) := by norm_num
    _ ≤ 10 ^ 23 * η * 1 := by gcongr <;> norm_num
    _ = 10 ^ 23 * η := by ring

theorem NN2_69 (n : ℕ) (hn : 1 ≤ n) : NN n 2 = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  have h := Pn_eq56 n 2
  rw [Pn2_69] at h
  have : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp at h ⊢
  nlinarith [h]

/-- **Theorem 1 at `d_M = d_f = 2`, `C = 1`, `ε = 1/2`, without amortization, for every
`n ≥ 10^86`.** -/
theorem part69_single_cert : ∀ n : ℕ, 10 ^ 86 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 2 2)) (pg : Prog (In56 n 2 2) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed69 pm (KRK 1 n eC69) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ 11 * n + 23 * (KRK 1 n eC69) + 194 ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 2 T → 0 < frob (T 2) →
        stdGauss (CoefIdxD n 2) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 2 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 2 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 2 ε := by
  intro n hn
  have hn' : (10 : ℝ) ^ 86 ≤ n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  obtain ⟨pm0, pg0, -, -, hpm0s, hpg0s, -, hall⟩ := BstLean.Part66.part66T1O_22 n hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n 2 2 (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := momProg69_used n (KRK 1 n eC69) hn2
  have hpmc' : (pm.cost : ℝ) ≤ 11 * n + 23 * (KRK 1 n eC69) + 194 := by exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc', fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have h := (hall v hv t ht0 ht ε hε1 hε2 f0 T hT hTk).1
    have e0 : ∀ M : CoefIdxD n 2 → ℝ,
        pg0.eval (inp56 f0 T M v (pm0.eval (inRK t v))) () =
          gLineW (surrRK n (KRK 1 n eC69) t v) 2 f0 T v M :=
      fun M => eval56 pm0 pg0 _ hpm0s hpg0s t v ht0 hv f0 T hT M
    have e1 : ∀ M : CoefIdxD n 2 → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK 1 n eC69) t v) 2 f0 T v M :=
      fun M => eval69 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [e0] at h
    simp only [e1]
    exact h
  · have hε : ε = 1 / 2 := le_antisymm hε2 hε1
    subst hε
    have hK : (KRK 1 n eC69 : ℝ) ≤ (1 + 2 * 10 ^ 23) * n + (10 ^ 23 / 3 + (10 ^ 23) ^ 2 / 9 + 2) := by
      have h := K_le69 (1 * n) eC69
      have hL := Leta_le69
      have hL2 : BstLean.Part43.Leta eC69 ^ 2 ≤ (10 ^ 23) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hL 2
      rw [one_mul, Nat.abs_cast] at h
      have h3 : (1 + 2 * |BstLean.Part43.Leta eC69|) * (n : ℝ) ≤ (1 + 2 * 10 ^ 23) * n :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
      unfold KRK
      rw [one_mul]
      linarith
    have hbase : 91 / 100 * Pn n 2 / (1 / 2) ^ 2 ≤ baseline n 2 (1 / 2) := le_max_right _ _
    have hcl : (pg.cost : ℝ) ≤ 2 * Pn n 2 + 3 * NN n 2 + 2304 * ((n : ℝ) + 1) ^ 2 := by
      refine hpgc.trans (le_of_eq ?_)
      unfold costLine56; norm_num
    rw [Pn2_69] at hbase hcl
    rw [NN2_69 n (by omega)] at hcl
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := le_trans (by norm_num) hn'
    set N := (n : ℝ)
    have hsq : (10 : ℝ) ^ 86 * N ≤ N * N := mul_le_mul_of_nonneg_right hn' hn0
    have hcube : (10 : ℝ) ^ 86 * (N * N) ≤ N * N * N := by
      calc (10 : ℝ) ^ 86 * (N * N) ≤ N * (N * N) := mul_le_mul_of_nonneg_right hn' (by positivity)
        _ = N * N * N := by ring
    have hN2 : (10 : ℝ) ^ 86 ≤ N * N := le_trans hn' (le_mul_of_one_le_right hn0 hn1)
    have hlhs : (11 * N + 23 * ((1 + 2 * 10 ^ 23) * N + (10 ^ 23 / 3 + (10 ^ 23) ^ 2 / 9 + 2)) + 194)
        + (2 * (N * (N + 1) * (N + 2) / 2) + 3 * ((N + 1) * (N + 2) / 2) + 2304 * (N + 1) ^ 2)
        ≤ N * (N + 1) * (N + 2) + 10 ^ 4 * (N * N) := by
      ring_nf; ring_nf at hsq hN2; linarith
    have hrhs : N * (N + 1) * (N + 2) + 10 ^ 4 * (N * N) <
        91 / 100 * (N * (N + 1) * (N + 2) / 2) / (1 / 2) ^ 2 := by
      ring_nf; ring_nf at hcube hN2 hsq; linarith
    linarith

end BstLean.Part69

#print axioms BstLean.Part69.part69_single
#print axioms BstLean.Part69.part69_single_cert
