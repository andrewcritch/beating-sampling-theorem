import BstLean.Part188All
import BstLean.Part190T6
import BstLean.Part182TImono



namespace BstLean.Part190
open BstLean.Part188
open BstLean.Part187

open BstLean.Part182 BstLean.Part130 Real
open BstLean.Part185 BstLean.Part190.T


def t7_Econd (n : ℕ) (cp kE c : ℝ) : Prop :=
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 297 / 1000000) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 297 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 297 / 1000000)) (√(2 * 46)) (1 / 8) (1 / 100) ∧
    (2 * (BstLean.Part184.gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) *
      exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 297 / 1000000) * (1 / 8) ^ 2 / 4)) ≤
        2 / 10 ^ 19 ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 297 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 297 / 1000000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 297 / 1000000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + 297 / 1000000)) 46 ^ 2)
      (e4_b n 2 46) (1 / 8) (1 / 100) ≤ n * kE


lemma t7_eta {n : ℕ} (hn : 16200 ≤ n) : (46 : ℝ) ≤ 2 * (297 / 1000000) ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  rw [t5_M]
  have : (16200 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  nlinarith

lemma t7c_w_0 {n : ℕ} (hn : 16200 ≤ n) {c : ℝ} (h0 : (37 / 100 : ℝ) ≤ c) (h1 : c ≤ (1 / 2 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (37 / 100 : ℝ)) (cb := (1 / 2 : ℝ)) (Sc := (433013 / 500000 : ℝ)) (Sd := (929031 / 1000000 : ℝ)) (KU := (19033 / 31250 : ℝ)) (KL := (525351 / 1000000 : ℝ)) (C1 := (614129 / 1000000 : ℝ)) (C1l := (260217 / 500000 : ℝ)) (kU := (355453 / 500000 : ℝ)) (kL := (10532 / 15625 : ℝ)) (a2 := (168701 / 200000 : ℝ)) (al := (1000297 / 1000000 : ℝ)) (am := (426767 / 500000 : ℝ)) (r0 := (19191 / 25000 : ℝ)) (S0 := (860091 / 1000000 : ℝ)) (b0 := (375681 / 500000 : ℝ)) (l0 := (506137 / 500000 : ℝ)) (m0 := (865511 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (1087409 / 500000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_1 {n : ℕ} (hn : 16200 ≤ n) {c : ℝ} (h0 : (1 / 2 : ℝ) ≤ c) (h1 : c ≤ (3 / 5 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (1 / 2 : ℝ)) (cb := (3 / 5 : ℝ)) (Sc := (4 / 5 : ℝ)) (Sd := (34641 / 40000 : ℝ)) (KU := (169441 / 250000 : ℝ)) (KL := (60893 / 100000 : ℝ)) (C1 := (85369 / 125000 : ℝ)) (C1l := (603873 / 1000000 : ℝ)) (kU := (740043 / 1000000 : ℝ)) (kL := (352909 / 500000 : ℝ)) (a2 := (860603 / 1000000 : ℝ)) (al := (1000297 / 1000000 : ℝ)) (am := (426767 / 500000 : ℝ)) (r0 := (392769 / 500000 : ℝ)) (S0 := (877189 / 1000000 : ℝ)) (b0 := (76891 / 100000 : ℝ)) (l0 := (506137 / 500000 : ℝ)) (m0 := (865511 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (1087409 / 500000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_2 {n : ℕ} (hn : 16200 ≤ n) {c : ℝ} (h0 : (3 / 5 : ℝ) ≤ c) (h1 : c ≤ (16 / 25 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (3 / 5 : ℝ)) (cb := (16 / 25 : ℝ)) (Sc := (6147 / 8000 : ℝ)) (Sd := (4 / 5 : ℝ)) (KU := (706399 / 1000000 : ℝ)) (KL := (169307 / 250000 : ℝ)) (C1 := (142327 / 200000 : ℝ)) (C1l := (672057 / 1000000 : ℝ)) (kU := (752939 / 1000000 : ℝ)) (kL := (366649 / 500000 : ℝ)) (a2 := (868063 / 1000000 : ℝ)) (al := (1000297 / 1000000 : ℝ)) (am := (426767 / 500000 : ℝ)) (r0 := (800697 / 1000000 : ℝ)) (S0 := (884649 / 1000000 : ℝ)) (b0 := (783843 / 1000000 : ℝ)) (l0 := (506137 / 500000 : ℝ)) (m0 := (865511 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (1087409 / 500000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_w_3 {n : ℕ} (hn : 16200 ≤ n) {c : ℝ} (h0 : (16 / 25 : ℝ) ≤ c) (h1 : c ≤ (131 / 200 : ℝ)) :
    t7_Econd n (655 / 1000) (161 / 250) c :=
  t5_cell hn (ca := (16 / 25 : ℝ)) (cb := (131 / 200 : ℝ)) (Sc := (755629 / 1000000 : ℝ)) (Sd := (384187 / 500000 : ℝ)) (KU := (179329 / 250000 : ℝ)) (KL := (705501 / 1000000 : ℝ)) (C1 := (72257 / 100000 : ℝ)) (C1l := (700283 / 1000000 : ℝ)) (kU := (94749 / 125000 : ℝ)) (kL := (372573 / 500000 : ℝ)) (a2 := (870969 / 1000000 : ℝ)) (al := (1000297 / 1000000 : ℝ)) (am := (426767 / 500000 : ℝ)) (r0 := (100893 / 125000 : ℝ)) (S0 := (177511 / 200000 : ℝ)) (b0 := (790197 / 1000000 : ℝ)) (l0 := (506137 / 500000 : ℝ)) (m0 := (865511 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (1087409 / 500000 : ℝ)) (cp := (655 / 1000 : ℝ)) (k655 := (363963 / 500000 : ℝ)) (kE := (161 / 250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


theorem t7_E_w {n : ℕ} (hn : 16200 ≤ n) {c : ℝ} (h0 : (370 / 1000 : ℝ) ≤ c) (h1 : c ≤ (655 / 1000 : ℝ)) :
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


theorem t7_num_w {n : ℕ} (hn : 16200 ≤ n) :
    d4_num n (370 / 1000) (655 / 1000) (161 / 250) (291 / 10000) (186 / 1000) (297 / 1000000) 46
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


theorem TI_two_16200s : ∀ n : ℕ, 16200 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (323 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_w le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_w hn)


theorem TI_two_16200 : ∀ n : ℕ, 16200 ≤ n →
    BstLean.Part182.TI_hyp n (370 / 1000) (655 / 1000) (647 / 1000) (1 / 10 ^ 18) :=
  fun n hn => TI_hyp_mono (by norm_num) le_rfl (TI_two_16200s n hn)

end BstLean.Part190

#print axioms BstLean.Part190.t7_num_w
#print axioms BstLean.Part190.TI_two_16200s
#print axioms BstLean.Part190.TI_two_16200
