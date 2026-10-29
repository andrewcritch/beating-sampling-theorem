import BstLean.Part69Final
import BstLean.Part66T1Ord

/-!
# Part 74: Theorem 1 at `d_M = d_f = 3` without amortization, from a moment-program hypothesis

* `MomSpecUsed74`: the weaker specification of a moment program at general `(k, d)`: exact surrogate
  weights at the keys `2l ≤ i` (the keys that `pg` reads).
* `eval74`: the general-degree version of `Part69.eval69`.
* `ProgHyp33 A`: a single-use moment program at `(3,3)` of cost `≤ A (n + K + 1)` exists.
* `part74_single_33_of`: from `ProgHyp33 A`, `A ≤ 10^40`: Theorem 1 at `(3,3)`, `C = 1`, `ε = 1/2`,
  failure `1/100`, for every `n ≥ 10^125`, with `cost(pm) + cost(pg) < baseline n 3 ε` (no counter).
  Accuracy from `Part66.part66T1O_33`.
-/

namespace BstLean.Part74

open MeasureTheory BstLean.Cost
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount Pn NN)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part56

variable {n : ℕ}

/-- The weaker specification of a moment program: exact surrogate weights at the keys `2l ≤ i`. -/
def MomSpecUsed74 {k d : ℕ} (pm : Prog (InM56 n) (KeyRK k d)) (K : ℕ) : Prop :=
  ∀ (t : ℝ) (v : Fin n → ℝ), 0 ≤ t → UnitV v → ∀ κ : KeyRK k d, 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ) →
    pm.eval (inRK t v) κ = wRK (surrRK n K t v) d v κ

/-- **Evaluation under the weaker specification**, at every degree pair. -/
theorem eval74 {k d : ℕ} (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit) (K : ℕ)
    (hpm : MomSpecUsed74 pm K) (hpg : GSpec56 pg) (t : ℝ) (v : Fin n → ℝ) (ht : 0 ≤ t)
    (hv : UnitV v) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (M : CoefIdxD n d → ℝ) :
    pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () = gLineW (surrRK n K t v) k f0 T v M := by
  rw [hpg f0 T M v _ hT]
  unfold gLineW gW
  apply Finset.sum_congr rfl
  intro κ _
  split_ifs with h
  · rw [hpm t v ht hv κ h]
  · rfl

/-- The hypothesis: a single-use moment program at `(3,3)` of cost `≤ A (n + K + 1)`. -/
def ProgHyp33 (A : ℕ) : Prop :=
  ∀ n K : ℕ, 2 ≤ n → ∃ pm : Prog (InM56 n) (KeyRK 3 3), heavyCount pm = 0 ∧
    MomSpecUsed74 pm K ∧ pm.cost ≤ A * (n + K + 1)

/-- The surrogate parameter of Part 66's ordered certificate at `(3,3)`. -/
noncomputable def eC74_33 : ℝ := eRK 3 (BstLean.Part66.tO (2 * 3) (1 / 200) / 4) (1 / 2)

theorem Leta_le74_33 : |BstLean.Part43.Leta eC74_33| ≤ 10 ^ 31 := by
  set s := BstLean.Part66.tO (2 * 3) (1 / 200) / 4 with hs
  have hs54 : (10 : ℝ) ^ (-54 : ℤ) ≤ s := by
    rw [hs, show 2 * 3 = 6 by rfl, BstLean.Part66.tO_6]; norm_num
  have hsq : (10 : ℝ) ^ (-27 : ℤ) ≤ Real.sqrt s := by
    rw [show (10 : ℝ) ^ (-54 : ℤ) = ((10 : ℝ) ^ (-27 : ℤ)) ^ 2 by norm_num] at hs54
    calc (10 : ℝ) ^ (-27 : ℤ) = Real.sqrt (((10 : ℝ) ^ (-27 : ℤ)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs54
  set η := BstLean.Part43.etaQ eC74_33
  have hη : η = min (Real.sqrt s / 800) (1 / 2) := by
    simp only [η, BstLean.Part43.etaQ, eC74_33, eRK, etaRK, BstLean.Part43.xi43, ← hs]
    congr 1; field_simp; norm_num
  have hηlo : (10 : ℝ) ^ (-27 : ℤ) / 800 ≤ η := by
    rw [hη]; exact le_min (div_le_div_of_nonneg_right hsq (by norm_num)) (by norm_num)
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hηlo
  have hL0 : 0 ≤ BstLean.Part43.Leta eC74_33 := by
    unfold BstLean.Part43.Leta
    apply Real.log_nonneg
    rw [le_div_iff₀ hη0]; linarith
  rw [abs_of_nonneg hL0]
  unfold BstLean.Part43.Leta
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [add_div, div_self hη0.ne', add_sub_cancel_right, div_le_iff₀ hη0]
  calc (1 : ℝ) = 10 ^ 31 * (10 ^ (-27 : ℤ) / 800) * (800 / 10000) := by norm_num
    _ ≤ 10 ^ 31 * η * 1 := by gcongr <;> norm_num
    _ = 10 ^ 31 * η := by ring

/-- `K = KRK 1 n eC74_33 ≤ (1 + 2·10^31) n + 10^63`. -/
theorem K_le74_33 (n : ℕ) : (KRK 1 n eC74_33 : ℝ) ≤ (1 + 2 * 10 ^ 31) * n + 10 ^ 63 := by
  have h := BstLean.Part69.K_le69 (1 * n) eC74_33
  have hL := Leta_le74_33
  have hL2 : BstLean.Part43.Leta eC74_33 ^ 2 ≤ (10 ^ 31) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hL 2
  rw [one_mul, Nat.abs_cast] at h
  have h3 : (1 + 2 * |BstLean.Part43.Leta eC74_33|) * (n : ℝ) ≤ (1 + 2 * 10 ^ 31) * n :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  unfold KRK
  rw [one_mul]
  have : (10 : ℝ) ^ 31 / 3 + (10 ^ 31) ^ 2 / 9 + 2 ≤ 10 ^ 63 := by norm_num
  linarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- **Theorem 1 at `d_M = d_f = 3`, `C = 1`, `ε = 1/2`, without amortization, for every
`n ≥ 10^125`**, from a single-use moment program of cost `≤ A (n + K + 1)`, `A ≤ 10^40`. -/
theorem part74_single_33_of (A : ℕ) (hA : A ≤ 10 ^ 40) (h : ProgHyp33 A) :
    ∀ n : ℕ, 10 ^ 125 ≤ n →
    ∃ (pm : Prog (InM56 n) (KeyRK 3 3)) (pg : Prog (In56 n 3 3) Unit),
      heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpecUsed74 pm (KRK 1 n eC74_33) ∧ GSpec56 pg ∧
      (pm.cost : ℝ) ≤ A * ((n : ℝ) + (KRK 1 n eC74_33 : ℝ) + 1) ∧
      ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ 1 * n →
      ∀ ε : ℝ, 1 / 2 ≤ ε → ε ≤ 1 / 2 →
      ∀ (f0 : ℝ) (T : Tens n), TSymm 3 T → 0 < frob (T 3) →
        stdGauss (CoefIdxD n 3) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) 3 f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) 3 f0 T (unitOfD Z) -
              pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) ∧
        (pm.cost : ℝ) + pg.cost < baseline n 3 ε := by
  intro n hn
  have hn' : (10 : ℝ) ^ 125 ≤ n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn
  obtain ⟨pm0, pg0, -, -, hpm0s, hpg0s, -, hall⟩ := BstLean.Part66.part66T1O_33 n hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n 3 3 (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := h n (KRK 1 n eC74_33) hn2
  have hpmc' : (pm.cost : ℝ) ≤ A * ((n : ℝ) + (KRK 1 n eC74_33 : ℝ) + 1) := by
    exact_mod_cast hpmc
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc',
    fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have h := (hall v hv t ht0 ht ε hε1 hε2 f0 T hT hTk).1
    have e0 : ∀ M : CoefIdxD n 3 → ℝ,
        pg0.eval (inp56 f0 T M v (pm0.eval (inRK t v))) () =
          gLineW (surrRK n (KRK 1 n eC74_33) t v) 3 f0 T v M :=
      fun M => eval56 pm0 pg0 _ hpm0s hpg0s t v ht0 hv f0 T hT M
    have e1 : ∀ M : CoefIdxD n 3 → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK 1 n eC74_33) t v) 3 f0 T v M :=
      fun M => eval74 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [e0] at h
    simp only [e1]
    exact h
  · have hε : ε = 1 / 2 := le_antisymm hε2 hε1
    subst hε
    have hK := K_le74_33 n
    have hbase : 91 / 100 * Pn n 3 / (1 / 2) ^ 2 ≤ baseline n 3 (1 / 2) := le_max_right _ _
    have hcl : (pg.cost : ℝ) ≤ 2 * Pn n 3 + 4 * NN n 3 + 32000 * ((n : ℝ) + 1) ^ 3 := by
      refine hpgc.trans (le_of_eq ?_)
      unfold costLine56; norm_num
    have hPN := Pn_eq56 n 3
    have hNN := NN_ge56 n 3 (by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := le_trans (by norm_num) hn'
    set N := (n : ℝ)
    set P := Pn n 3
    set Q := NN n 3
    have hQ : N ^ 3 / 6 ≤ Q := by
      have : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [this] at hNN; exact hNN
    have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
    -- `4 Q ≤ P/100`
    have h4Q : 400 * Q ≤ P := by
      rw [hPN]; exact mul_le_mul_of_nonneg_right (le_trans (by norm_num) hn') hQ0
    have hP4 : N ^ 4 / 6 ≤ P := by
      rw [hPN]
      calc N ^ 4 / 6 = N * (N ^ 3 / 6) := by ring
        _ ≤ N * Q := mul_le_mul_of_nonneg_left hQ hn0
    -- the moment program
    have hA' : (A : ℝ) ≤ 10 ^ 40 := by exact_mod_cast hA
    have hm : (pm.cost : ℝ) ≤ 10 ^ 40 * ((2 + 2 * 10 ^ 31) * N + (10 ^ 63 + 1)) := by
      refine hpmc'.trans ?_
      calc (A : ℝ) * (N + (KRK 1 n eC74_33 : ℝ) + 1)
          ≤ 10 ^ 40 * (N + (KRK 1 n eC74_33 : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hA'
              (by have := Nat.cast_nonneg (α := ℝ) (KRK 1 n eC74_33); linarith)
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            linarith
    have hsq : (10 : ℝ) ^ 125 * N ≤ N ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hn' hn0
    have hm2 : (pm.cost : ℝ) ≤ N ^ 2 := by
      refine hm.trans ?_
      have e0 : (10 : ℝ) ^ 40 * ((2 + 2 * 10 ^ 31) * N + (10 ^ 63 + 1)) =
          (10 ^ 40 * (2 + 2 * 10 ^ 31)) * N + 10 ^ 40 * (10 ^ 63 + 1) := by ring
      have e1 : ((10 : ℝ) ^ 40 * (2 + 2 * 10 ^ 31)) * N ≤ 10 ^ 124 * N :=
        mul_le_mul_of_nonneg_right (by norm_num) hn0
      have e3 : (10 : ℝ) ^ 40 * (10 ^ 63 + 1) ≤ 10 ^ 124 * N := by
        calc (10 : ℝ) ^ 40 * (10 ^ 63 + 1) ≤ 10 ^ 124 * 1 := by norm_num
          _ ≤ 10 ^ 124 * N := mul_le_mul_of_nonneg_left hn1 (by norm_num)
      have e4 : (10 : ℝ) ^ 125 * N = 10 * (10 ^ 124 * N) := by ring
      have e5 : (0 : ℝ) ≤ 10 ^ 124 * N := by positivity
      rw [e0]
      linarith
    have hN3 : 0 ≤ N ^ 3 := by positivity
    have hcub : 32000 * (N + 1) ^ 3 ≤ 256000 * N ^ 3 := by
      have h2 : (N + 1) ^ 3 ≤ (2 * N) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      have h3 : (2 * N) ^ 3 = 8 * N ^ 3 := by ring
      linarith
    have h34 : (10 : ℝ) ^ 125 * N ^ 3 ≤ N ^ 4 := by
      calc (10 : ℝ) ^ 125 * N ^ 3 ≤ N * N ^ 3 := mul_le_mul_of_nonneg_right hn' (by positivity)
        _ = N ^ 4 := by ring
    have h23 : N ^ 2 ≤ N ^ 3 := by
      calc N ^ 2 = 1 * N ^ 2 := by ring
        _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hn1 (by positivity)
        _ = N ^ 3 := by ring
    have hgap : N ^ 2 + 256000 * N ^ 3 < N ^ 4 / 6 := by
      have h1 : (256001 : ℝ) * N ^ 3 ≤ 10 ^ 124 * N ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) hN3
      have e : (10 : ℝ) ^ 125 * N ^ 3 = 10 * (10 ^ 124 * N ^ 3) := by ring
      have hpos : 0 < N ^ 3 := by positivity
      have h0 : (0 : ℝ) < 10 ^ 124 * N ^ 3 := by positivity
      linarith
    have hb : 91 / 100 * P / (1 / 2) ^ 2 = 364 / 100 * P := by ring
    rw [hb] at hbase
    linarith

end BstLean.Part74

#print axioms BstLean.Part74.eval74
#print axioms BstLean.Part74.part74_single_33_of
