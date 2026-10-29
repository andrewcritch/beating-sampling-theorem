import BstLean.Part185D6
import BstLean.Part182TImono

/-!
# Part 185 (file `D7`): Lemma TI with the two-sided E block for every `n ≥ 17 000`

No proof is left open; no `native_decide` or `axiom` is used.

* `d5_cell_0` … `d5_cell_3`, **`d7_E`**: the E-block conditions of `d4_num` on the window
  `0.370 ≤ c ≤ 0.655` with `k_E = 0.642` (cells cut at `0.5`, `0.6`, `0.64`).
* **`d7_num`**: `d4_num n 0.370 0.655 0.642 0.0284 0.185 (283/10⁶) 46 (1/8) (1/100) (2·10⁻¹⁹)`.
* **`d7_lam`**: `ta_lam 0.642 0.0284 0.185 ≤ 0.645` (value `≈ 0.6438`).
* **`TI_two_17000`**: `TI_hyp n 0.370 0.655 0.645 10⁻¹⁸` for every `n ≥ 17 000`.
-/

namespace BstLean.Part185

open BstLean.Part182 BstLean.Part130 Real

/-- The two-sided E-block conditions of `d4_num` at one `c` (`τ = 46`, `η = 283/10⁶`, `δ = 1/8`,
`ε = 1/100`, `c₊ = 0.655`, `k_E = 0.642`). -/
def d6_Econd (n : ℕ) (c : ℝ) : Prop :=
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 283 / 1000000) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 283 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 283 / 1000000)) (√(2 * 46)) (1 / 8) (1 / 100) ∧
    (2 * (BstLean.Part184.gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) *
      exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 283 / 1000000) * (1 / 8) ^ 2 / 4)) ≤
        2 / 10 ^ 19 ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 283 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 283 / 1000000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 283 / 1000000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot (655 / 1000) / 2 + 283 / 1000000)) 46 ^ 2)
      (e4_b n 2 46) (1 / 8) (1 / 100) ≤ n * (321 / 500)

lemma d5_cell_0 {n : ℕ} (hn : 17000 ≤ n) {c : ℝ} (h0 : (37 / 100 : ℝ) ≤ c) (h1 : c ≤ (1 / 2 : ℝ)) :
    d6_Econd n c :=
  d5_cell hn (ca := (37 / 100 : ℝ)) (cb := (1 / 2 : ℝ)) (Sc := (433013 / 500000 : ℝ)) (Sd := (929031 / 1000000 : ℝ)) (KU := (19033 / 31250 : ℝ)) (KL := (525351 / 1000000 : ℝ)) (C1 := (61389 / 100000 : ℝ)) (C1l := (104133 / 200000 : ℝ)) (kU := (710809 / 1000000 : ℝ)) (kL := (337067 / 500000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (a2 := (843431 / 1000000 : ℝ)) (al := (1000283 / 1000000 : ℝ)) (am := (426759 / 500000 : ℝ)) (r0 := (153541 / 200000 : ℝ)) (S0 := (429807 / 500000 : ℝ)) (b0 := (751431 / 1000000 : ℝ)) (l0 := (202393 / 200000 : ℝ)) (m0 := (2163 / 2500 : ℝ)) (p0 := (1533949 / 1000000 : ℝ)) (t0 := (1085373 / 500000 : ℝ)) (kE := (321 / 500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num [d5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma d5_cell_1 {n : ℕ} (hn : 17000 ≤ n) {c : ℝ} (h0 : (1 / 2 : ℝ) ≤ c) (h1 : c ≤ (3 / 5 : ℝ)) :
    d6_Econd n c :=
  d5_cell hn (ca := (1 / 2 : ℝ)) (cb := (3 / 5 : ℝ)) (Sc := (4 / 5 : ℝ)) (Sd := (34641 / 40000 : ℝ)) (KU := (169441 / 250000 : ℝ)) (KL := (60893 / 100000 : ℝ)) (C1 := (170677 / 250000 : ℝ)) (C1l := (604111 / 1000000 : ℝ)) (kU := (23123 / 31250 : ℝ)) (kL := (705911 / 1000000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (a2 := (34421 / 40000 : ℝ)) (al := (1000283 / 1000000 : ℝ)) (am := (426759 / 500000 : ℝ)) (r0 := (392803 / 500000 : ℝ)) (S0 := (219177 / 250000 : ℝ)) (b0 := (384491 / 500000 : ℝ)) (l0 := (202393 / 200000 : ℝ)) (m0 := (2163 / 2500 : ℝ)) (p0 := (1533949 / 1000000 : ℝ)) (t0 := (1085373 / 500000 : ℝ)) (kE := (321 / 500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num [d5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma d5_cell_2 {n : ℕ} (hn : 17000 ≤ n) {c : ℝ} (h0 : (3 / 5 : ℝ) ≤ c) (h1 : c ≤ (16 / 25 : ℝ)) :
    d6_Econd n c :=
  d5_cell hn (ca := (3 / 5 : ℝ)) (cb := (16 / 25 : ℝ)) (Sc := (6147 / 8000 : ℝ)) (Sd := (4 / 5 : ℝ)) (KU := (706399 / 1000000 : ℝ)) (KL := (169307 / 250000 : ℝ)) (C1 := (177847 / 250000 : ℝ)) (C1l := (6723 / 10000 : ℝ)) (kU := (376413 / 500000 : ℝ)) (kL := (733399 / 1000000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (a2 := (433991 / 500000 : ℝ)) (al := (1000283 / 1000000 : ℝ)) (am := (426759 / 500000 : ℝ)) (r0 := (800767 / 1000000 : ℝ)) (S0 := (176833 / 200000 : ℝ)) (b0 := (783917 / 1000000 : ℝ)) (l0 := (202393 / 200000 : ℝ)) (m0 := (2163 / 2500 : ℝ)) (p0 := (1533949 / 1000000 : ℝ)) (t0 := (1085373 / 500000 : ℝ)) (kE := (321 / 500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num [d5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma d5_cell_3 {n : ℕ} (hn : 17000 ≤ n) {c : ℝ} (h0 : (16 / 25 : ℝ) ≤ c) (h1 : c ≤ (131 / 200 : ℝ)) :
    d6_Econd n c :=
  d5_cell hn (ca := (16 / 25 : ℝ)) (cb := (131 / 200 : ℝ)) (Sc := (755629 / 1000000 : ℝ)) (Sd := (384187 / 500000 : ℝ)) (KU := (179329 / 250000 : ℝ)) (KL := (705501 / 1000000 : ℝ)) (C1 := (722323 / 1000000 : ℝ)) (C1l := (43783 / 62500 : ℝ)) (kU := (757877 / 1000000 : ℝ)) (kL := (2981 / 4000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (a2 := (870887 / 1000000 : ℝ)) (al := (1000283 / 1000000 : ℝ)) (am := (426759 / 500000 : ℝ)) (r0 := (50451 / 62500 : ℝ)) (S0 := (88707 / 100000 : ℝ)) (b0 := (790273 / 1000000 : ℝ)) (l0 := (202393 / 200000 : ℝ)) (m0 := (2163 / 2500 : ℝ)) (p0 := (1533949 / 1000000 : ℝ)) (t0 := (1085373 / 500000 : ℝ)) (kE := (321 / 500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [d5P7]) (by norm_num [d5P5]) (by norm_num [d5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- The E-block conditions on the whole window `[0.370, 0.655]`. -/
theorem d7_E {n : ℕ} (hn : 17000 ≤ n) {c : ℝ} (h0 : (370 / 1000 : ℝ) ≤ c) (h1 : c ≤ 655 / 1000) :
    d6_Econd n c := by
  replace h0 : (37 / 100 : ℝ) ≤ c := by linarith
  replace h1 : c ≤ (131 / 200 : ℝ) := by linarith
  by_cases hc0 : c ≤ (1 / 2 : ℝ)
  · exact d5_cell_0 hn h0 hc0
  have hl1 : (1 / 2 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (3 / 5 : ℝ)
  · exact d5_cell_1 hn hl1 hc1
  have hl2 : (3 / 5 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (16 / 25 : ℝ)
  · exact d5_cell_2 hn hl2 hc2
  have hl3 : (16 / 25 : ℝ) ≤ c := (not_le.mp hc2).le
  exact d5_cell_3 hn hl3 h1

/-- `46 ≤ 2η²m` for `η = 283/10⁶`, `n ≥ 17 000`. -/
lemma d7_eta {n : ℕ} (hn : 17000 ≤ n) : (46 : ℝ) ≤ 2 * (283 / 1000000) ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (17000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [d5_M]
  have : (17000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  nlinarith

/-- **All numeric hypotheses of `d4_num`** at `n ≥ 17 000`. -/
theorem d7_num {n : ℕ} (hn : 17000 ≤ n) :
    d4_num n (370 / 1000) (655 / 1000) (321 / 500) (284 / 10000) (185 / 1000) (283 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, DT.fsn_am hn, fun c h0 h1 => ?_⟩
  · have h := DT.fsn_ko hn; rwa [DT.fsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := DT.fsn_S hn h0 h1
    rw [DT.fsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := d7_E hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

/-- `ta_lam 0.642 0.0284 0.185 ≤ 0.645`. -/
theorem d7_lam : ta_lam (321 / 500) (284 / 10000) (185 / 1000) ≤ 645 / 1000 := by
  unfold ta_lam
  have h : √(((321 / 500 - 185 / 1000 : ℝ) / 2) ^ 2 + (284 / 10000) ^ 2) ≤ 2303 / 10000 :=
    DT.fsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Lemma TI with the two-sided (ε-net) E block, every `n ≥ 17 000`**:
`TI_hyp n 0.370 0.655 0.645 10⁻¹⁸`. -/
theorem TI_two_17000 : ∀ n : ℕ, 17000 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (645 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono d7_lam le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (d7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (d7_num hn)

end BstLean.Part185

open BstLean.Part185 in
#print axioms d7_num
open BstLean.Part185 in
#print axioms TI_two_17000
