import BstLean.Part187T6
import BstLean.Part182TImono

/-!
# Part 186 (file `T7`): Lemma TI with the two-sided E block for every `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used. A copy of Part 185's file `D7` at the
floor `16 250` (`√n ≥ 127`, `η = 296/10⁶`, net term with `K_lo ≥ 0.336m`), with the window top
`c₊` as a parameter of the E-block conditions (`t7_Econd`).

* `t7_E_w`, **`t7_num_w`**: `d4_num n 0.370 0.655 0.6440 0.0291 0.186 (296/10⁶) 46 (1/8) (1/100) (2·10⁻¹⁹)`.
* `t7_lam_w`: `ta_lam 0.6440 0.0291 0.186 ≤ 0.6460` (value `≈ 0.64584`).
* **`TI_two_16250`**: `TI_hyp n 0.370 0.655 0.647 10⁻¹⁸` for every `n ≥ 16 250`; the sharper
  `TI_two_16250s` has `λ = 0.6460`.
-/

namespace BstLean.Part187

open BstLean.Part182 BstLean.Part130 Real
open BstLean.Part185 BstLean.Part187.T

/-- The two-sided E-block conditions of `d4_num` at one `c` (`τ = 46`, `η = 296/10⁶`, `δ = 1/8`,
`ε = 1/100`, window top `c₊`, constant `k_E`). -/
def t7_Econd (n : ℕ) (cp kE c : ℝ) : Prop :=
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 296 / 1000000) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 296 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 296 / 1000000)) (√(2 * 46)) (1 / 8) (1 / 100) ∧
    (2 * (BstLean.Part184.gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) *
      exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 296 / 1000000) * (1 / 8) ^ 2 / 4)) ≤
        2 / 10 ^ 19 ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 296 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 296 / 1000000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 296 / 1000000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + 296 / 1000000)) 46 ^ 2)
      (e4_b n 2 46) (1 / 8) (1 / 100) ≤ n * kE

/-- `46 ≤ 2η²m` for `η = 296/10⁶`, `n ≥ 16 250`. -/
lemma t7_eta {n : ℕ} (hn : 16250 ≤ n) : (46 : ℝ) ≤ 2 * (296 / 1000000) ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  rw [t5_M]
  have : (16250 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  nlinarith

lemma t7c_w_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (37 / 100 : ℝ) ≤ c) (h1 : c ≤ (1 / 2 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (37 / 100 : ℝ)) (cb := (1 / 2 : ℝ)) (Sc := (433013 / 500000 : ℝ)) (Sd := (929031 / 1000000 : ℝ)) (KU := (19033 / 31250 : ℝ)) (KL := (525351 / 1000000 : ℝ)) (C1 := (614113 / 1000000 : ℝ)) (C1l := (520449 / 1000000 : ℝ)) (kU := (710899 / 1000000 : ℝ)) (kL := (337027 / 500000 : ℝ)) (a2 := (1687 / 2000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (853533 / 1000000 : ℝ)) (r0 := (153529 / 200000 : ℝ)) (S0 := (860083 / 1000000 : ℝ)) (b0 := (751367 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (86551 / 100000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (1 / 2 : ℝ) ≤ c) (h1 : c ≤ (3 / 5 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (1 / 2 : ℝ)) (cb := (3 / 5 : ℝ)) (Sc := (4 / 5 : ℝ)) (Sd := (34641 / 40000 : ℝ)) (KU := (169441 / 250000 : ℝ)) (KL := (60893 / 100000 : ℝ)) (C1 := (85367 / 125000 : ℝ)) (C1l := (603889 / 1000000 : ℝ)) (kU := (185009 / 250000 : ℝ)) (kL := (22057 / 31250 : ℝ)) (a2 := (430299 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (853533 / 1000000 : ℝ)) (r0 := (785543 / 1000000 : ℝ)) (S0 := (877181 / 1000000 : ℝ)) (b0 := (153783 / 200000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (86551 / 100000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (3 / 5 : ℝ) ≤ c) (h1 : c ≤ (16 / 25 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (3 / 5 : ℝ)) (cb := (16 / 25 : ℝ)) (Sc := (6147 / 8000 : ℝ)) (Sd := (4 / 5 : ℝ)) (KU := (706399 / 1000000 : ℝ)) (KL := (169307 / 250000 : ℝ)) (C1 := (711619 / 1000000 : ℝ)) (C1l := (672073 / 1000000 : ℝ)) (kU := (188233 / 250000 : ℝ)) (kL := (146661 / 200000 : ℝ)) (a2 := (434029 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (853533 / 1000000 : ℝ)) (r0 := (400351 / 500000 : ℝ)) (S0 := (884641 / 1000000 : ℝ)) (b0 := (97981 / 125000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (86551 / 100000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (16 / 25 : ℝ) ≤ c) (h1 : c ≤ (131 / 200 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (16 / 25 : ℝ)) (cb := (131 / 200 : ℝ)) (Sc := (755629 / 1000000 : ℝ)) (Sd := (384187 / 500000 : ℝ)) (KU := (179329 / 250000 : ℝ)) (KL := (705501 / 1000000 : ℝ)) (C1 := (361277 / 500000 : ℝ)) (C1l := (700299 / 1000000 : ℝ)) (kU := (23687 / 31250 : ℝ)) (kL := (745153 / 1000000 : ℝ)) (a2 := (870963 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (853533 / 1000000 : ℝ)) (r0 := (807149 / 1000000 : ℝ)) (S0 := (443773 / 500000 : ℝ)) (b0 := (395101 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (86551 / 100000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.37, 0.655]` (`k_E = 0.644`). -/
theorem t7_E_w {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (370 / 1000 : ℝ) ≤ c) (h1 : c ≤ (655 / 1000 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c := by
  replace h0 : (37 / 100 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (131 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (1 / 2 : ℝ)
  · exact t7c_w_0 hn h0 hc0
  have hl1 : (1 / 2 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (3 / 5 : ℝ)
  · exact t7c_w_1 hn hl1 hc1
  have hl2 : (3 / 5 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (16 / 25 : ℝ)
  · exact t7c_w_2 hn hl2 hc2
  have hl3 : (16 / 25 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_w_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.37, 0.655]`, `n ≥ 16 250`. -/
theorem t7_num_w {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (370 / 1000) (655 / 1000) (161 / 250) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_w hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_w : ta_lam (161 / 250) (291 / 10000) (186 / 1000) ≤ 323 / 500 := by
  unfold ta_lam
  have h : √(((161 / 250 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 230843 / 1000000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Lemma TI, two-sided E block, every `n ≥ 16 250`**: `TI_hyp n 0.370 0.655 0.6460 10⁻¹⁸`. -/
theorem TI_two_16250s : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (323 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_w le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_w hn)

/-- **Lemma TI, two-sided E block, every `n ≥ 16 250`**: `TI_hyp n 0.370 0.655 0.647 10⁻¹⁸`. -/
theorem TI_two_16250 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18) :=
  fun n hn => TI_hyp_mono (by norm_num) le_rfl (TI_two_16250s n hn)

end BstLean.Part187

#print axioms BstLean.Part187.t7_num_w
#print axioms BstLean.Part187.TI_two_16250s
#print axioms BstLean.Part187.TI_two_16250
