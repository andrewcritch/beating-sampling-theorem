import BstLean.Part186T6
import BstLean.Part182TImono

/-!
# Part 186 (file `T7`): Lemma TI with the two-sided E block for every `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used. A copy of Part 185's file `D7` at the
floor `16 384` (`√n ≥ 128`, `η = 293/10⁶`, net term with `K_lo ≥ 0.336m`), with the window top
`c₊` as a parameter of the E-block conditions (`t7_Econd`).

* `t7_E_w`, **`t7_num_w`**: `d4_num n 0.370 0.655 0.6435 0.0288 0.186 (293/10⁶) 46 (1/8) (1/100) (2·10⁻¹⁹)`.
* `t7_lam_w`: `ta_lam 0.6435 0.0288 0.186 ≤ 0.6455` (value `≈ 0.64531`).
* **`TI_two_16384`**: `TI_hyp n 0.370 0.655 0.647 10⁻¹⁸` for every `n ≥ 16 384`; the sharper
  `TI_two_16384s` has `λ = 0.6455`.
-/

namespace BstLean.Part186

open BstLean.Part182 BstLean.Part130 Real
open BstLean.Part185 BstLean.Part186.T

/-- The two-sided E-block conditions of `d4_num` at one `c` (`τ = 46`, `η = 293/10⁶`, `δ = 1/8`,
`ε = 1/100`, window top `c₊`, constant `k_E`). -/
def t7_Econd (n : ℕ) (cp kE c : ℝ) : Prop :=
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000)) (√(2 * 46)) (1 / 8) (1 / 100) ∧
    (2 * (BstLean.Part184.gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) *
      exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) * (1 / 8) ^ 2 / 4)) ≤
        2 / 10 ^ 19 ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 293 / 1000000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + 293 / 1000000)) 46 ^ 2)
      (e4_b n 2 46) (1 / 8) (1 / 100) ≤ n * kE

/-- `46 ≤ 2η²m` for `η = 293/10⁶`, `n ≥ 16 384`. -/
lemma t7_eta {n : ℕ} (hn : 16384 ≤ n) : (46 : ℝ) ≤ 2 * (293 / 1000000) ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  rw [t5_M]
  have : (16384 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  nlinarith

lemma t7c_w_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (37 / 100 : ℝ) ≤ c) (h1 : c ≤ (1 / 2 : ℝ)) :
    t7_Econd n (655 / 1000) (1287 / 2000) c :=
  t5_cell hn (ca := (37 / 100 : ℝ)) (cb := (1 / 2 : ℝ)) (Sc := (433013 / 500000 : ℝ)) (Sd := (929031 / 1000000 : ℝ)) (KU := (19033 / 31250 : ℝ)) (KL := (525351 / 1000000 : ℝ)) (C1 := (76759 / 125000 : ℝ)) (C1l := (520489 / 1000000 : ℝ)) (kU := (710883 / 1000000 : ℝ)) (kL := (674069 / 1000000 : ℝ)) (a2 := (843487 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (85353 / 100000 : ℝ)) (r0 := (767657 / 1000000 : ℝ)) (S0 := (42997 / 50000 : ℝ)) (b0 := (751381 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (865407 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (1287 / 2000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (1 / 2 : ℝ) ≤ c) (h1 : c ≤ (3 / 5 : ℝ)) :
    t7_Econd n (655 / 1000) (1287 / 2000) c :=
  t5_cell hn (ca := (1 / 2 : ℝ)) (cb := (3 / 5 : ℝ)) (Sc := (4 / 5 : ℝ)) (Sd := (34641 / 40000 : ℝ)) (KU := (169441 / 250000 : ℝ)) (KL := (60893 / 100000 : ℝ)) (C1 := (341447 / 500000 : ℝ)) (C1l := (60393 / 100000 : ℝ)) (kU := (370009 / 500000 : ℝ)) (kL := (8823 / 12500 : ℝ)) (a2 := (107573 / 125000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (85353 / 100000 : ℝ)) (r0 := (157111 / 200000 : ℝ)) (S0 := (877037 / 1000000 : ℝ)) (b0 := (768929 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (865407 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (1287 / 2000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (3 / 5 : ℝ) ≤ c) (h1 : c ≤ (16 / 25 : ℝ)) :
    t7_Econd n (655 / 1000) (1287 / 2000) c :=
  t5_cell hn (ca := (3 / 5 : ℝ)) (cb := (16 / 25 : ℝ)) (Sc := (6147 / 8000 : ℝ)) (Sd := (4 / 5 : ℝ)) (KU := (706399 / 1000000 : ℝ)) (KL := (169307 / 250000 : ℝ)) (C1 := (88947 / 125000 : ℝ)) (C1l := (134423 / 200000 : ℝ)) (kU := (47057 / 62500 : ℝ)) (kL := (366661 / 500000 : ℝ)) (a2 := (868043 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (85353 / 100000 : ℝ)) (r0 := (400357 / 500000 : ℝ)) (S0 := (55281 / 62500 : ℝ)) (b0 := (783861 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (865407 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (1287 / 2000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (16 / 25 : ℝ) ≤ c) (h1 : c ≤ (131 / 200 : ℝ)) :
    t7_Econd n (655 / 1000) (1287 / 2000) c :=
  t5_cell hn (ca := (16 / 25 : ℝ)) (cb := (131 / 200 : ℝ)) (Sc := (755629 / 1000000 : ℝ)) (Sd := (384187 / 500000 : ℝ)) (KU := (179329 / 250000 : ℝ)) (KL := (705501 / 1000000 : ℝ)) (C1 := (722511 / 1000000 : ℝ)) (C1l := (700341 / 1000000 : ℝ)) (kU := (189491 / 250000 : ℝ)) (kL := (74517 / 100000 : ℝ)) (a2 := (217737 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (85353 / 100000 : ℝ)) (r0 := (403581 / 500000 : ℝ)) (S0 := (887401 / 1000000 : ℝ)) (b0 := (98777 / 125000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (865407 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (1287 / 2000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.37, 0.655]` (`k_E = 0.6435`). -/
theorem t7_E_w {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (370 / 1000 : ℝ) ≤ c) (h1 : c ≤ (655 / 1000 : ℝ)) :
    t7_Econd n (655 / 1000) (1287 / 2000) c := by
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

/-- **All numeric hypotheses of `d4_num`** on `[0.37, 0.655]`, `n ≥ 16 384`. -/
theorem t7_num_w {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (370 / 1000) (655 / 1000) (1287 / 2000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_w hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_w : ta_lam (1287 / 2000) (288 / 10000) (186 / 1000) ≤ 1291 / 2000 := by
  unfold ta_lam
  have h : √(((1287 / 2000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 230557 / 1000000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Lemma TI, two-sided E block, every `n ≥ 16 384`**: `TI_hyp n 0.370 0.655 0.6455 10⁻¹⁸`. -/
theorem TI_two_16384s : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (1291 / 2000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_w le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_w hn)

/-- **Lemma TI, two-sided E block, every `n ≥ 16 384`**: `TI_hyp n 0.370 0.655 0.647 10⁻¹⁸`. -/
theorem TI_two_16384 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18) :=
  fun n hn => TI_hyp_mono (by norm_num) le_rfl (TI_two_16384s n hn)

end BstLean.Part186

#print axioms BstLean.Part186.t7_num_w
#print axioms BstLean.Part186.TI_two_16384s
#print axioms BstLean.Part186.TI_two_16384
