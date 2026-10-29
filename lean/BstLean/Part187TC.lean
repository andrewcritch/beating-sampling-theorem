import BstLean.Part187T7

/-!
# Part 186 (file `TC`): Lemma TI on the narrow windows of the core set `Γ(3.75, 7, 3.75)` (windows of `Part187GeoC`), `n ≥ 16 250`

No proof is left open; no `native_decide` or `axiom` is used. Same numerics as file `T7`
(`η = 296/10⁶`, `δ = 1/8`, `ε = 1/100`, `τ = 46`, `k_o = 0.0291`, `k_s = 0.186`), with the window
top `c₊` in `L₁₁` and four E cells per window (cuts at `c₊ − 0.08`, `c₊ − 0.03`, `c₊ − 0.01`).

* `TI_core_16250_0`: window `[0.463, 0.615]`, `k_E = 0.6211` (cells max `0.62102`), `λ₁ = 0.624` (`ta_lam ≈ 0.62304`).
* `TI_core_16250_1`: window `[0.453, 0.605]`, `k_E = 0.6157` (cells max `0.61563`), `λ₁ = 0.618` (`ta_lam ≈ 0.61766`).
* `TI_core_16250_2`: window `[0.443, 0.595]`, `k_E = 0.6104` (cells max `0.61032`), `λ₁ = 0.613` (`ta_lam ≈ 0.61239`).
* `TI_core_16250_3`: window `[0.433, 0.585]`, `k_E = 0.6052` (cells max `0.60510`), `λ₁ = 0.608` (`ta_lam ≈ 0.60721`).
* `TI_core_16250_4`: window `[0.423, 0.575]`, `k_E = 0.6001` (cells max `0.59997`), `λ₁ = 0.603` (`ta_lam ≈ 0.60213`).
* `TI_core_16250_5`: window `[0.413, 0.565]`, `k_E = 0.595` (cells max `0.59492`), `λ₁ = 0.598` (`ta_lam ≈ 0.59706`).
* `TI_core_16250_6`: window `[0.405, 0.555]`, `k_E = 0.59` (cells max `0.58994`), `λ₁ = 0.593` (`ta_lam ≈ 0.59209`).
-/

namespace BstLean.Part187

open BstLean.Part182 BstLean.Part130 Real
open BstLean.Part185 BstLean.Part187.T


lemma t7c_c0_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (463 / 1000 : ℝ) ≤ c) (h1 : c ≤ (107 / 200 : ℝ)) :
    t7_Econd n (615 / 1000) (6211 / 10000) c :=
  t5_cell hn (ca := (463 / 1000 : ℝ)) (cb := (107 / 200 : ℝ)) (Sc := (844853 / 1000000 : ℝ)) (Sd := (443179 / 500000 : ℝ)) (KU := (316327 / 500000 : ℝ)) (KL := (116909 / 200000 : ℝ)) (C1 := (637751 / 1000000 : ℝ)) (C1l := (72443 / 125000 : ℝ)) (kU := (720649 / 1000000 : ℝ)) (kL := (696361 / 1000000 : ℝ)) (a2 := (42463 / 50000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (421857 / 500000 : ℝ)) (r0 := (156051 / 200000 : ℝ)) (S0 := (865843 / 1000000 : ℝ)) (b0 := (381897 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (855691 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (615 / 1000 : ℝ)) (k655 := (711261 / 1000000 : ℝ)) (kE := (6211 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (107 / 200 : ℝ) ≤ c) (h1 : c ≤ (117 / 200 : ℝ)) :
    t7_Econd n (615 / 1000) (6211 / 10000) c :=
  t5_cell hn (ca := (107 / 200 : ℝ)) (cb := (117 / 200 : ℝ)) (Sc := (405517 / 500000 : ℝ)) (Sd := (211213 / 250000 : ℝ)) (KU := (667201 / 1000000 : ℝ)) (KL := (316219 / 500000 : ℝ)) (C1 := (134471 / 200000 : ℝ)) (C1l := (313679 / 500000 : ℝ)) (kU := (3677 / 5000 : ℝ)) (kL := (715113 / 1000000 : ℝ)) (a2 := (8579 / 10000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (421857 / 500000 : ℝ)) (r0 := (790699 / 1000000 : ℝ)) (S0 := (874483 / 1000000 : ℝ)) (b0 := (774047 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (855691 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (615 / 1000 : ℝ)) (k655 := (711261 / 1000000 : ℝ)) (kE := (6211 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (117 / 200 : ℝ) ≤ c) (h1 : c ≤ (121 / 200 : ℝ)) :
    t7_Econd n (615 / 1000) (6211 / 10000) c :=
  t5_cell hn (ca := (117 / 200 : ℝ)) (cb := (121 / 200 : ℝ)) (Sc := (398113 / 500000 : ℝ)) (Sd := (811033 / 1000000 : ℝ)) (KU := (340653 / 500000 : ℝ)) (KL := (666763 / 1000000 : ℝ)) (C1 := (171621 / 250000 : ℝ)) (C1l := (5293 / 8000 : ℝ)) (kU := (148321 / 200000 : ℝ)) (kL := (728993 / 1000000 : ℝ)) (a2 := (861509 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (421857 / 500000 : ℝ)) (r0 := (399171 / 500000 : ℝ)) (S0 := (219523 / 250000 : ℝ)) (b0 := (781577 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (855691 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (615 / 1000 : ℝ)) (k655 := (711261 / 1000000 : ℝ)) (kE := (6211 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (121 / 200 : ℝ) ≤ c) (h1 : c ≤ (123 / 200 : ℝ)) :
    t7_Econd n (615 / 1000) (6211 / 10000) c :=
  t5_cell hn (ca := (121 / 200 : ℝ)) (cb := (123 / 200 : ℝ)) (Sc := (49283 / 62500 : ℝ)) (Sd := (31849 / 40000 : ℝ)) (KU := (344211 / 500000 : ℝ)) (KL := (680733 / 1000000 : ℝ)) (C1 := (173403 / 250000 : ℝ)) (C1l := (168893 / 250000 : ℝ)) (kU := (372389 / 500000 : ℝ)) (kL := (367379 / 500000 : ℝ)) (a2 := (863349 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (421857 / 500000 : ℝ)) (r0 := (160299 / 200000 : ℝ)) (S0 := (219983 / 250000 : ℝ)) (b0 := (19617 / 25000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (855691 / 1000000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (615 / 1000 : ℝ)) (k655 := (711261 / 1000000 : ℝ)) (kE := (6211 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.463, 0.615]` (`k_E = 0.6211`). -/
theorem t7_E_c0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (463 / 1000 : ℝ) ≤ c) (h1 : c ≤ (615 / 1000 : ℝ)) :
    t7_Econd n (615 / 1000) (6211 / 10000) c := by
  replace h0 : (463 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (123 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (107 / 200 : ℝ)
  · exact t7c_c0_0 hn h0 hc0
  have hl1 : (107 / 200 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (117 / 200 : ℝ)
  · exact t7c_c0_1 hn hl1 hc1
  have hl2 : (117 / 200 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (121 / 200 : ℝ)
  · exact t7c_c0_2 hn hl2 hc2
  have hl3 : (121 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c0_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.463, 0.615]`, `n ≥ 16 250`. -/
theorem t7_num_c0 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (463 / 1000) (615 / 1000) (6211 / 10000) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c0 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c0 : ta_lam (6211 / 10000) (291 / 10000) (186 / 1000) ≤ 78 / 125 := by
  unfold ta_lam
  have h : √(((6211 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 219489 / 1000000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 0**: `TI_hyp n 0.463 0.615 0.624 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_0 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (463 / 1000) (615 / 1000) (78 / 125) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c0 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c0 hn)

lemma t7c_c1_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (453 / 1000 : ℝ) ≤ c) (h1 : c ≤ (21 / 40 : ℝ)) :
    t7_Econd n (605 / 1000) (6157 / 10000) c :=
  t5_cell hn (ca := (453 / 1000 : ℝ)) (cb := (21 / 40 : ℝ)) (Sc := (851103 / 1000000 : ℝ)) (Sd := (89151 / 100000 : ℝ)) (KU := (625863 / 1000000 : ℝ)) (KL := (144509 / 250000 : ℝ)) (C1 := (157737 / 250000 : ℝ)) (C1l := (286523 / 500000 : ℝ)) (kU := (717817 / 1000000 : ℝ)) (kL := (86733 / 125000 : ℝ)) (a2 := (847591 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (841307 / 1000000 : ℝ)) (r0 := (778853 / 1000000 : ℝ)) (S0 := (432087 / 500000 : ℝ)) (b0 := (381211 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (213321 / 250000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (605 / 1000 : ℝ)) (k655 := (141441 / 200000 : ℝ)) (kE := (6157 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (21 / 40 : ℝ) ≤ c) (h1 : c ≤ (23 / 40 : ℝ)) :
    t7_Econd n (605 / 1000) (6157 / 10000) c :=
  t5_cell hn (ca := (21 / 40 : ℝ)) (cb := (23 / 40 : ℝ)) (Sc := (409077 / 500000 : ℝ)) (Sd := (425551 / 500000 : ℝ)) (KU := (660211 / 1000000 : ℝ)) (KL := (312839 / 500000 : ℝ)) (C1 := (332677 / 500000 : ℝ)) (C1l := (620609 / 1000000 : ℝ)) (kU := (366183 / 500000 : ℝ)) (kL := (89053 / 125000 : ℝ)) (a2 := (85613 / 100000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (841307 / 1000000 : ℝ)) (r0 := (78921 / 100000 : ℝ)) (S0 := (872713 / 1000000 : ℝ)) (b0 := (77259 / 100000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (213321 / 250000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (605 / 1000 : ℝ)) (k655 := (141441 / 200000 : ℝ)) (kE := (6157 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (23 / 40 : ℝ) ≤ c) (h1 : c ≤ (119 / 200 : ℝ)) :
    t7_Econd n (605 / 1000) (6157 / 10000) c :=
  t5_cell hn (ca := (23 / 40 : ℝ)) (cb := (119 / 200 : ℝ)) (Sc := (401863 / 500000 : ℝ)) (Sd := (818153 / 1000000 : ℝ)) (KU := (674233 / 1000000 : ℝ)) (KL := (659829 / 1000000 : ℝ)) (C1 := (679399 / 1000000 : ℝ)) (C1l := (654703 / 1000000 : ℝ)) (kU := (738479 / 1000000 : ℝ)) (kL := (726157 / 1000000 : ℝ)) (a2 := (859693 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (841307 / 1000000 : ℝ)) (r0 := (398393 / 500000 : ℝ)) (S0 := (219069 / 250000 : ℝ)) (b0 := (156011 / 200000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (213321 / 250000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (605 / 1000 : ℝ)) (k655 := (141441 / 200000 : ℝ)) (kE := (6157 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (119 / 200 : ℝ) ≤ c) (h1 : c ≤ (121 / 200 : ℝ)) :
    t7_Econd n (605 / 1000) (6157 / 10000) c :=
  t5_cell hn (ca := (119 / 200 : ℝ)) (cb := (121 / 200 : ℝ)) (Sc := (398113 / 500000 : ℝ)) (Sd := (32149 / 40000 : ℝ)) (KU := (340653 / 500000 : ℝ)) (KL := (673731 / 1000000 : ℝ)) (C1 := (171621 / 250000 : ℝ)) (C1l := (334291 / 500000 : ℝ)) (kU := (148321 / 200000 : ℝ)) (kL := (36593 / 50000 : ℝ)) (a2 := (861509 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (841307 / 1000000 : ℝ)) (r0 := (99989 / 125000 : ℝ)) (S0 := (219523 / 250000 : ℝ)) (b0 := (783131 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (213321 / 250000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (605 / 1000 : ℝ)) (k655 := (141441 / 200000 : ℝ)) (kE := (6157 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.453, 0.605]` (`k_E = 0.6157`). -/
theorem t7_E_c1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (453 / 1000 : ℝ) ≤ c) (h1 : c ≤ (605 / 1000 : ℝ)) :
    t7_Econd n (605 / 1000) (6157 / 10000) c := by
  replace h0 : (453 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (121 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (21 / 40 : ℝ)
  · exact t7c_c1_0 hn h0 hc0
  have hl1 : (21 / 40 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (23 / 40 : ℝ)
  · exact t7c_c1_1 hn hl1 hc1
  have hl2 : (23 / 40 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (119 / 200 : ℝ)
  · exact t7c_c1_2 hn hl2 hc2
  have hl3 : (119 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c1_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.453, 0.605]`, `n ≥ 16 250`. -/
theorem t7_num_c1 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (453 / 1000) (605 / 1000) (6157 / 10000) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c1 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c1 : ta_lam (6157 / 10000) (291 / 10000) (186 / 1000) ≤ 309 / 500 := by
  unfold ta_lam
  have h : √(((6157 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 216813 / 1000000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 1**: `TI_hyp n 0.453 0.605 0.618 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_1 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (453 / 1000) (605 / 1000) (309 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c1 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c1 hn)

lemma t7c_c2_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (443 / 1000 : ℝ) ≤ c) (h1 : c ≤ (103 / 200 : ℝ)) :
    t7_Econd n (595 / 1000) (763 / 1250) c :=
  t5_cell hn (ca := (443 / 1000 : ℝ)) (cb := (103 / 200 : ℝ)) (Sc := (857191 / 1000000 : ℝ)) (Sd := (896521 / 1000000 : ℝ)) (KU := (77389 / 125000 : ℝ)) (KL := (571563 / 1000000 : ℝ)) (C1 := (312093 / 500000 : ℝ)) (C1l := (70823 / 125000 : ℝ)) (kU := (44689 / 62500 : ℝ)) (kL := (10803 / 15625 : ℝ)) (a2 := (845941 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (419459 / 500000 : ℝ)) (r0 := (777463 / 1000000 : ℝ)) (S0 := (215631 / 250000 : ℝ)) (b0 := (761063 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (170179 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (595 / 1000 : ℝ)) (k655 := (703191 / 1000000 : ℝ)) (kE := (763 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (103 / 200 : ℝ) ≤ c) (h1 : c ≤ (113 / 200 : ℝ)) :
    t7_Econd n (595 / 1000) (763 / 1250) c :=
  t5_cell hn (ca := (103 / 200 : ℝ)) (cb := (113 / 200 : ℝ)) (Sc := (825091 / 1000000 : ℝ)) (Sd := (85719 / 100000 : ℝ)) (KU := (653261 / 1000000 : ℝ)) (KL := (77369 / 125000 : ℝ)) (C1 := (82299 / 125000 : ℝ)) (C1l := (306947 / 500000 : ℝ)) (kU := (1167 / 1600 : ℝ)) (kL := (709763 / 1000000 : ℝ)) (a2 := (427191 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (419459 / 500000 : ℝ)) (r0 := (787733 / 1000000 : ℝ)) (S0 := (174193 / 200000 : ℝ)) (b0 := (385573 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (170179 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (595 / 1000 : ℝ)) (k655 := (703191 / 1000000 : ℝ)) (kE := (763 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (113 / 200 : ℝ) ≤ c) (h1 : c ≤ (117 / 200 : ℝ)) :
    t7_Econd n (595 / 1000) (763 / 1250) c :=
  t5_cell hn (ca := (113 / 200 : ℝ)) (cb := (117 / 200 : ℝ)) (Sc := (405517 / 500000 : ℝ)) (Sd := (82509 / 100000 : ℝ)) (KU := (667201 / 1000000 : ℝ)) (KL := (652929 / 1000000 : ℝ)) (C1 := (134471 / 200000 : ℝ)) (C1l := (323907 / 500000 : ℝ)) (kU := (3677 / 5000 : ℝ)) (kL := (90419 / 125000 : ℝ)) (a2 := (8579 / 10000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (419459 / 500000 : ℝ)) (r0 := (159049 / 200000 : ℝ)) (S0 := (874483 / 1000000 : ℝ)) (b0 := (778547 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (170179 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (595 / 1000 : ℝ)) (k655 := (703191 / 1000000 : ℝ)) (kE := (763 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (117 / 200 : ℝ) ≤ c) (h1 : c ≤ (119 / 200 : ℝ)) :
    t7_Econd n (595 / 1000) (763 / 1250) c :=
  t5_cell hn (ca := (117 / 200 : ℝ)) (cb := (119 / 200 : ℝ)) (Sc := (401863 / 500000 : ℝ)) (Sd := (811033 / 1000000 : ℝ)) (KU := (674233 / 1000000 : ℝ)) (KL := (666763 / 1000000 : ℝ)) (C1 := (679399 / 1000000 : ℝ)) (C1l := (5293 / 8000 : ℝ)) (kU := (738479 / 1000000 : ℝ)) (kL := (728993 / 1000000 : ℝ)) (a2 := (859693 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (419459 / 500000 : ℝ)) (r0 := (399171 / 500000 : ℝ)) (S0 := (219069 / 250000 : ℝ)) (b0 := (156319 / 200000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (170179 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (595 / 1000 : ℝ)) (k655 := (703191 / 1000000 : ℝ)) (kE := (763 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.443, 0.595]` (`k_E = 0.6104`). -/
theorem t7_E_c2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (443 / 1000 : ℝ) ≤ c) (h1 : c ≤ (595 / 1000 : ℝ)) :
    t7_Econd n (595 / 1000) (763 / 1250) c := by
  replace h0 : (443 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (119 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (103 / 200 : ℝ)
  · exact t7c_c2_0 hn h0 hc0
  have hl1 : (103 / 200 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (113 / 200 : ℝ)
  · exact t7c_c2_1 hn hl1 hc1
  have hl2 : (113 / 200 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (117 / 200 : ℝ)
  · exact t7c_c2_2 hn hl2 hc2
  have hl3 : (117 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c2_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.443, 0.595]`, `n ≥ 16 250`. -/
theorem t7_num_c2 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (443 / 1000) (595 / 1000) (763 / 1250) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c2 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c2 : ta_lam (763 / 1250) (291 / 10000) (186 / 1000) ≤ 613 / 1000 := by
  unfold ta_lam
  have h : √(((763 / 1250 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 53547 / 250000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 2**: `TI_hyp n 0.443 0.595 0.613 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_2 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (443 / 1000) (595 / 1000) (613 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c2 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c2 hn)

lemma t7c_c3_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (433 / 1000 : ℝ) ≤ c) (h1 : c ≤ (101 / 200 : ℝ)) :
    t7_Econd n (585 / 1000) (1513 / 2500) c :=
  t5_cell hn (ca := (433 / 1000 : ℝ)) (cb := (101 / 200 : ℝ)) (Sc := (10789 / 12500 : ℝ)) (Sd := (901393 / 1000000 : ℝ)) (KU := (306199 / 500000 : ℝ)) (KL := (141281 / 250000 : ℝ)) (C1 := (617461 / 1000000 : ℝ)) (C1l := (140039 / 250000 : ℝ)) (kU := (142453 / 200000 : ℝ)) (kL := (43059 / 62500 : ℝ)) (a2 := (844309 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (167309 / 200000 : ℝ)) (r0 := (155217 / 200000 : ℝ)) (S0 := (215223 / 250000 : ℝ)) (b0 := (151943 / 200000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (424261 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (585 / 1000 : ℝ)) (k655 := (139843 / 200000 : ℝ)) (kE := (1513 / 2500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (101 / 200 : ℝ) ≤ c) (h1 : c ≤ (111 / 200 : ℝ)) :
    t7_Econd n (585 / 1000) (1513 / 2500) c :=
  t5_cell hn (ca := (101 / 200 : ℝ)) (cb := (111 / 200 : ℝ)) (Sc := (831851 / 1000000 : ℝ)) (Sd := (863119 / 1000000 : ℝ)) (KU := (40397 / 62500 : ℝ)) (KL := (306131 / 500000 : ℝ)) (C1 := (40717 / 62500 : ℝ)) (C1l := (121443 / 200000 : ℝ)) (kU := (363213 / 500000 : ℝ)) (kL := (70713 / 100000 : ℝ)) (a2 := (426327 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (167309 / 200000 : ℝ)) (r0 := (78627 / 100000 : ℝ)) (S0 := (869237 / 1000000 : ℝ)) (b0 := (384857 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (424261 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (585 / 1000 : ℝ)) (k655 := (139843 / 200000 : ℝ)) (kE := (1513 / 2500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (111 / 200 : ℝ) ≤ c) (h1 : c ≤ (23 / 40 : ℝ)) :
    t7_Econd n (585 / 1000) (1513 / 2500) c :=
  t5_cell hn (ca := (111 / 200 : ℝ)) (cb := (23 / 40 : ℝ)) (Sc := (409077 / 500000 : ℝ)) (Sd := (16637 / 20000 : ℝ)) (KU := (660211 / 1000000 : ℝ)) (KL := (40379 / 62500 : ℝ)) (C1 := (332677 / 500000 : ℝ)) (C1l := (640961 / 1000000 : ℝ)) (kU := (366183 / 500000 : ℝ)) (kL := (11259 / 15625 : ℝ)) (a2 := (85613 / 100000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (167309 / 200000 : ℝ)) (r0 := (198429 / 250000 : ℝ)) (S0 := (872713 / 1000000 : ℝ)) (b0 := (777051 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (424261 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (585 / 1000 : ℝ)) (k655 := (139843 / 200000 : ℝ)) (kE := (1513 / 2500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (23 / 40 : ℝ) ≤ c) (h1 : c ≤ (117 / 200 : ℝ)) :
    t7_Econd n (585 / 1000) (1513 / 2500) c :=
  t5_cell hn (ca := (23 / 40 : ℝ)) (cb := (117 / 200 : ℝ)) (Sc := (405517 / 500000 : ℝ)) (Sd := (818153 / 1000000 : ℝ)) (KU := (667201 / 1000000 : ℝ)) (KL := (659829 / 1000000 : ℝ)) (C1 := (134471 / 200000 : ℝ)) (C1l := (654703 / 1000000 : ℝ)) (kU := (3677 / 5000 : ℝ)) (kL := (726157 / 1000000 : ℝ)) (a2 := (8579 / 10000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (167309 / 200000 : ℝ)) (r0 := (398393 / 500000 : ℝ)) (S0 := (874483 / 1000000 : ℝ)) (b0 := (780073 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (424261 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (585 / 1000 : ℝ)) (k655 := (139843 / 200000 : ℝ)) (kE := (1513 / 2500 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.433, 0.585]` (`k_E = 0.6052`). -/
theorem t7_E_c3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (433 / 1000 : ℝ) ≤ c) (h1 : c ≤ (585 / 1000 : ℝ)) :
    t7_Econd n (585 / 1000) (1513 / 2500) c := by
  replace h0 : (433 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (117 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (101 / 200 : ℝ)
  · exact t7c_c3_0 hn h0 hc0
  have hl1 : (101 / 200 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (111 / 200 : ℝ)
  · exact t7c_c3_1 hn hl1 hc1
  have hl2 : (111 / 200 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (23 / 40 : ℝ)
  · exact t7c_c3_2 hn hl2 hc2
  have hl3 : (23 / 40 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c3_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.433, 0.585]`, `n ≥ 16 250`. -/
theorem t7_num_c3 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (433 / 1000) (585 / 1000) (1513 / 2500) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c3 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c3 : ta_lam (1513 / 2500) (291 / 10000) (186 / 1000) ≤ 76 / 125 := by
  unfold ta_lam
  have h : √(((1513 / 2500 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 52903 / 250000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 3**: `TI_hyp n 0.433 0.585 0.608 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_3 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (433 / 1000) (585 / 1000) (76 / 125) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c3 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c3 hn)

lemma t7c_c4_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (423 / 1000 : ℝ) ≤ c) (h1 : c ≤ (99 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (6001 / 10000) c :=
  t5_cell hn (ca := (423 / 1000 : ℝ)) (cb := (99 / 200 : ℝ)) (Sc := (868893 / 1000000 : ℝ)) (Sd := (906129 / 1000000 : ℝ)) (KU := (605723 / 1000000 : ℝ)) (KL := (558719 / 1000000 : ℝ)) (C1 := (24431 / 40000 : ℝ)) (C1l := (553761 / 1000000 : ℝ)) (kU := (354771 / 500000 : ℝ)) (kL := (686519 / 1000000 : ℝ)) (a2 := (168539 / 200000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (208547 / 250000 : ℝ)) (r0 := (193679 / 250000 : ℝ)) (S0 := (429639 / 500000 : ℝ)) (b0 := (94797 / 125000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (169233 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (6001 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (99 / 200 : ℝ) ≤ c) (h1 : c ≤ (109 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (6001 / 10000) c :=
  t5_cell hn (ca := (99 / 200 : ℝ)) (cb := (109 / 200 : ℝ)) (Sc := (838437 / 1000000 : ℝ)) (Sd := (217223 / 250000 : ℝ)) (KU := (639483 / 1000000 : ℝ)) (KL := (302803 / 500000 : ℝ)) (C1 := (644591 / 1000000 : ℝ)) (C1l := (60057 / 100000 : ℝ)) (kU := (723517 / 1000000 : ℝ)) (kL := (176131 / 250000 : ℝ)) (a2 := (425473 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (208547 / 250000 : ℝ)) (r0 := (392409 / 500000 : ℝ)) (S0 := (867529 / 1000000 : ℝ)) (b0 := (384147 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (169233 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (6001 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (109 / 200 : ℝ) ≤ c) (h1 : c ≤ (113 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (6001 / 10000) c :=
  t5_cell hn (ca := (109 / 200 : ℝ)) (cb := (113 / 200 : ℝ)) (Sc := (825091 / 1000000 : ℝ)) (Sd := (209609 / 250000 : ℝ)) (KU := (653261 / 1000000 : ℝ)) (KL := (319617 / 500000 : ℝ)) (C1 := (82299 / 125000 : ℝ)) (C1l := (317071 / 500000 : ℝ)) (kU := (1167 / 1600 : ℝ)) (kL := (71783 / 100000 : ℝ)) (a2 := (427191 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (208547 / 250000 : ℝ)) (r0 := (792201 / 1000000 : ℝ)) (S0 := (174193 / 200000 : ℝ)) (b0 := (775569 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (169233 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (6001 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (113 / 200 : ℝ) ≤ c) (h1 : c ≤ (23 / 40 : ℝ)) :
    t7_Econd n (575 / 1000) (6001 / 10000) c :=
  t5_cell hn (ca := (113 / 200 : ℝ)) (cb := (23 / 40 : ℝ)) (Sc := (409077 / 500000 : ℝ)) (Sd := (82509 / 100000 : ℝ)) (KU := (660211 / 1000000 : ℝ)) (KL := (652929 / 1000000 : ℝ)) (C1 := (332677 / 500000 : ℝ)) (C1l := (323907 / 500000 : ℝ)) (kU := (366183 / 500000 : ℝ)) (kL := (90419 / 125000 : ℝ)) (a2 := (85613 / 100000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (208547 / 250000 : ℝ)) (r0 := (159049 / 200000 : ℝ)) (S0 := (872713 / 1000000 : ℝ)) (b0 := (155713 / 200000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (169233 / 200000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (6001 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.423, 0.575]` (`k_E = 0.6001`). -/
theorem t7_E_c4 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (423 / 1000 : ℝ) ≤ c) (h1 : c ≤ (575 / 1000 : ℝ)) :
    t7_Econd n (575 / 1000) (6001 / 10000) c := by
  replace h0 : (423 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (23 / 40 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (99 / 200 : ℝ)
  · exact t7c_c4_0 hn h0 hc0
  have hl1 : (99 / 200 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (109 / 200 : ℝ)
  · exact t7c_c4_1 hn hl1 hc1
  have hl2 : (109 / 200 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (113 / 200 : ℝ)
  · exact t7c_c4_2 hn hl2 hc2
  have hl3 : (113 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c4_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.423, 0.575]`, `n ≥ 16 250`. -/
theorem t7_num_c4 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (423 / 1000) (575 / 1000) (6001 / 10000) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c4 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c4 : ta_lam (6001 / 10000) (291 / 10000) (186 / 1000) ≤ 603 / 1000 := by
  unfold ta_lam
  have h : √(((6001 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 104543 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 4**: `TI_hyp n 0.423 0.575 0.603 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_4 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (423 / 1000) (575 / 1000) (603 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c4 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c4 hn)

lemma t7c_c5_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (413 / 1000 : ℝ) ≤ c) (h1 : c ≤ (97 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (119 / 200) c :=
  t5_cell hn (ca := (413 / 1000 : ℝ)) (cb := (97 / 200 : ℝ)) (Sc := (174903 / 200000 : ℝ)) (Sd := (910731 / 1000000 : ℝ)) (KU := (119817 / 200000 : ℝ)) (KL := (11047 / 20000 : ℝ)) (C1 := (4833 / 8000 : ℝ)) (C1l := (547403 / 1000000 : ℝ)) (kU := (706853 / 1000000 : ℝ)) (kL := (684119 / 1000000 : ℝ)) (a2 := (420549 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (166369 / 200000 : ℝ)) (r0 := (9667 / 12500 : ℝ)) (S0 := (857681 / 1000000 : ℝ)) (b0 := (757049 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (421911 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (119 / 200 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (97 / 200 : ℝ) ≤ c) (h1 : c ≤ (107 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (119 / 200) c :=
  t5_cell hn (ca := (97 / 200 : ℝ)) (cb := (107 / 200 : ℝ)) (Sc := (844853 / 1000000 : ℝ)) (Sd := (437257 / 500000 : ℝ)) (KU := (316327 / 500000 : ℝ)) (KL := (299493 / 500000 : ℝ)) (C1 := (637751 / 1000000 : ℝ)) (C1l := (593961 / 1000000 : ℝ)) (kU := (720649 / 1000000 : ℝ)) (kL := (140389 / 200000 : ℝ)) (a2 := (42463 / 50000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (166369 / 200000 : ℝ)) (r0 := (783379 / 1000000 : ℝ)) (S0 := (865843 / 1000000 : ℝ)) (b0 := (383443 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (421911 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (119 / 200 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (107 / 200 : ℝ) ≤ c) (h1 : c ≤ (111 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (119 / 200) c :=
  t5_cell hn (ca := (107 / 200 : ℝ)) (cb := (111 / 200 : ℝ)) (Sc := (831851 / 1000000 : ℝ)) (Sd := (211213 / 250000 : ℝ)) (KU := (40397 / 62500 : ℝ)) (KL := (316219 / 500000 : ℝ)) (C1 := (40717 / 62500 : ℝ)) (C1l := (313679 / 500000 : ℝ)) (kU := (363213 / 500000 : ℝ)) (kL := (715113 / 1000000 : ℝ)) (a2 := (426327 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (166369 / 200000 : ℝ)) (r0 := (790699 / 1000000 : ℝ)) (S0 := (869237 / 1000000 : ℝ)) (b0 := (774099 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (421911 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (119 / 200 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (111 / 200 : ℝ) ≤ c) (h1 : c ≤ (113 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (119 / 200) c :=
  t5_cell hn (ca := (111 / 200 : ℝ)) (cb := (113 / 200 : ℝ)) (Sc := (825091 / 1000000 : ℝ)) (Sd := (16637 / 20000 : ℝ)) (KU := (653261 / 1000000 : ℝ)) (KL := (40379 / 62500 : ℝ)) (C1 := (82299 / 125000 : ℝ)) (C1l := (640961 / 1000000 : ℝ)) (kU := (1167 / 1600 : ℝ)) (kL := (11259 / 15625 : ℝ)) (a2 := (427191 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (166369 / 200000 : ℝ)) (r0 := (198429 / 250000 : ℝ)) (S0 := (174193 / 200000 : ℝ)) (b0 := (777069 / 1000000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (421911 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (119 / 200 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.413, 0.565]` (`k_E = 0.595`). -/
theorem t7_E_c5 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (413 / 1000 : ℝ) ≤ c) (h1 : c ≤ (565 / 1000 : ℝ)) :
    t7_Econd n (565 / 1000) (119 / 200) c := by
  replace h0 : (413 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (113 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (97 / 200 : ℝ)
  · exact t7c_c5_0 hn h0 hc0
  have hl1 : (97 / 200 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (107 / 200 : ℝ)
  · exact t7c_c5_1 hn hl1 hc1
  have hl2 : (107 / 200 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (111 / 200 : ℝ)
  · exact t7c_c5_2 hn hl2 hc2
  have hl3 : (111 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c5_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.413, 0.565]`, `n ≥ 16 250`. -/
theorem t7_num_c5 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (413 / 1000) (565 / 1000) (119 / 200) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c5 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c5 : ta_lam (119 / 200) (291 / 10000) (186 / 1000) ≤ 299 / 500 := by
  unfold ta_lam
  have h : √(((119 / 200 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 103281 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 5**: `TI_hyp n 0.413 0.565 0.598 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_5 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (413 / 1000) (565 / 1000) (299 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c5 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c5 hn)

lemma t7c_c6_0 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (81 / 200 : ℝ) ≤ c) (h1 : c ≤ (19 / 40 : ℝ)) :
    t7_Econd n (555 / 1000) (59 / 100) c :=
  t5_cell hn (ca := (81 / 200 : ℝ)) (cb := (19 / 40 : ℝ)) (Sc := (439993 / 500000 : ℝ)) (Sd := (228579 / 250000 : ℝ)) (KU := (118497 / 200000 : ℝ)) (KL := (547279 / 1000000 : ℝ)) (C1 := (298757 / 500000 : ℝ)) (C1l := (542341 / 1000000 : ℝ)) (kU := (176049 / 250000 : ℝ)) (kL := (136443 / 200000 : ℝ)) (a2 := (839517 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (829517 / 1000000 : ℝ)) (r0 := (386141 / 500000 : ℝ)) (S0 := (8561 / 10000 : ℝ)) (b0 := (377999 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (420747 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (555 / 1000 : ℝ)) (k655 := (137501 / 200000 : ℝ)) (kE := (59 / 100 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_1 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (19 / 40 : ℝ) ≤ c) (h1 : c ≤ (21 / 40 : ℝ)) :
    t7_Econd n (555 / 1000) (59 / 100) c :=
  t5_cell hn (ca := (19 / 40 : ℝ)) (cb := (21 / 40 : ℝ)) (Sc := (851103 / 1000000 : ℝ)) (Sd := (175997 / 200000 : ℝ)) (KU := (625863 / 1000000 : ℝ)) (KL := (592401 / 1000000 : ℝ)) (C1 := (157737 / 250000 : ℝ)) (C1l := (587387 / 1000000 : ℝ)) (kU := (717817 / 1000000 : ℝ)) (kL := (699391 / 1000000 : ℝ)) (a2 := (847591 / 1000000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (829517 / 1000000 : ℝ)) (r0 := (12218 / 15625 : ℝ)) (S0 := (432087 / 500000 : ℝ)) (b0 := (76549 / 100000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (420747 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (555 / 1000 : ℝ)) (k655 := (137501 / 200000 : ℝ)) (kE := (59 / 100 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_2 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (21 / 40 : ℝ) ≤ c) (h1 : c ≤ (109 / 200 : ℝ)) :
    t7_Econd n (555 / 1000) (59 / 100) c :=
  t5_cell hn (ca := (21 / 40 : ℝ)) (cb := (109 / 200 : ℝ)) (Sc := (838437 / 1000000 : ℝ)) (Sd := (425551 / 500000 : ℝ)) (KU := (639483 / 1000000 : ℝ)) (KL := (312839 / 500000 : ℝ)) (C1 := (644591 / 1000000 : ℝ)) (C1l := (620609 / 1000000 : ℝ)) (kU := (723517 / 1000000 : ℝ)) (kL := (89053 / 125000 : ℝ)) (a2 := (425473 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (829517 / 1000000 : ℝ)) (r0 := (78921 / 100000 : ℝ)) (S0 := (867529 / 1000000 : ℝ)) (b0 := (386321 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (420747 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (555 / 1000 : ℝ)) (k655 := (137501 / 200000 : ℝ)) (kE := (59 / 100 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_3 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (109 / 200 : ℝ) ≤ c) (h1 : c ≤ (111 / 200 : ℝ)) :
    t7_Econd n (555 / 1000) (59 / 100) c :=
  t5_cell hn (ca := (109 / 200 : ℝ)) (cb := (111 / 200 : ℝ)) (Sc := (831851 / 1000000 : ℝ)) (Sd := (209609 / 250000 : ℝ)) (KU := (40397 / 62500 : ℝ)) (KL := (319617 / 500000 : ℝ)) (C1 := (40717 / 62500 : ℝ)) (C1l := (317071 / 500000 : ℝ)) (kU := (363213 / 500000 : ℝ)) (kL := (71783 / 100000 : ℝ)) (a2 := (426327 / 500000 : ℝ)) (al := (125037 / 125000 : ℝ)) (am := (829517 / 1000000 : ℝ)) (r0 := (792201 / 1000000 : ℝ)) (S0 := (869237 / 1000000 : ℝ)) (b0 := (387793 / 500000 : ℝ)) (l0 := (1012273 / 1000000 : ℝ)) (m0 := (420747 / 500000 : ℝ)) (p0 := (1536777 / 1000000 : ℝ)) (t0 := (2174813 / 1000000 : ℝ)) (cp := (555 / 1000 : ℝ)) (k655 := (137501 / 200000 : ℝ)) (kE := (59 / 100 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.405, 0.555]` (`k_E = 0.59`). -/
theorem t7_E_c6 {n : ℕ} (hn : 16250 ≤ n) {c : ℝ} (h0 : (405 / 1000 : ℝ) ≤ c) (h1 : c ≤ (555 / 1000 : ℝ)) :
    t7_Econd n (555 / 1000) (59 / 100) c := by
  replace h0 : (81 / 200 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (111 / 200 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (19 / 40 : ℝ)
  · exact t7c_c6_0 hn h0 hc0
  have hl1 : (19 / 40 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (21 / 40 : ℝ)
  · exact t7c_c6_1 hn hl1 hc1
  have hl2 : (21 / 40 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (109 / 200 : ℝ)
  · exact t7c_c6_2 hn hl2 hc2
  have hl3 : (109 / 200 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c6_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.405, 0.555]`, `n ≥ 16 250`. -/
theorem t7_num_c6 {n : ℕ} (hn : 16250 ≤ n) :
    d4_num n (405 / 1000) (555 / 1000) (59 / 100) (291 / 10000) (186 / 1000) (296 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c6 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c6 : ta_lam (59 / 100) (291 / 10000) (186 / 1000) ≤ 593 / 1000 := by
  unfold ta_lam
  have h : √(((59 / 100 - 186 / 1000 : ℝ) / 2) ^ 2 + (291 / 10000) ^ 2) ≤ 204087 / 1000000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 6**: `TI_hyp n 0.405 0.555 0.593 10⁻¹⁸`, every `n ≥ 16 250`. -/
theorem TI_core_16250_6 : ∀ n : ℕ, 16250 ≤ n →
    BstLean.Part182.TI_hyp n (405 / 1000) (555 / 1000) (593 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c6 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c6 hn)

end BstLean.Part187

#print axioms BstLean.Part187.TI_core_16250_0
#print axioms BstLean.Part187.TI_core_16250_1
#print axioms BstLean.Part187.TI_core_16250_2
#print axioms BstLean.Part187.TI_core_16250_3
#print axioms BstLean.Part187.TI_core_16250_4
#print axioms BstLean.Part187.TI_core_16250_5
#print axioms BstLean.Part187.TI_core_16250_6
