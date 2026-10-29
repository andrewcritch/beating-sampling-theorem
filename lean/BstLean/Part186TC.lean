import BstLean.Part186T7

/-!
# Part 186 (file `TC`): Lemma TI on the narrow windows of the core set `Γ(3.75, 7, 3.75)` (windows of `Part186GeoC`), `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used. Same numerics as file `T7`
(`η = 293/10⁶`, `δ = 1/8`, `ε = 1/100`, `τ = 46`, `k_o = 0.0288`, `k_s = 0.186`), with the window
top `c₊` in `L₁₁` and four E cells per window (cuts at `c₊ − 0.08`, `c₊ − 0.03`, `c₊ − 0.01`).

* `TI_core_16384_0`: window `[0.463, 0.614]`, `k_E = 0.6199` (cells max `0.61984`), `λ₁ = 0.622` (`ta_lam ≈ 0.62180`).
* `TI_core_16384_1`: window `[0.453, 0.604]`, `k_E = 0.6146` (cells max `0.61446`), `λ₁ = 0.617` (`ta_lam ≈ 0.61653`).
* `TI_core_16384_2`: window `[0.443, 0.594]`, `k_E = 0.6093` (cells max `0.60916`), `λ₁ = 0.612` (`ta_lam ≈ 0.61125`).
* `TI_core_16384_3`: window `[0.433, 0.584]`, `k_E = 0.6041` (cells max `0.60395`), `λ₁ = 0.607` (`ta_lam ≈ 0.60607`).
* `TI_core_16384_4`: window `[0.423, 0.575]`, `k_E = 0.5994` (cells max `0.59934`), `λ₁ = 0.602` (`ta_lam ≈ 0.60140`).
* `TI_core_16384_5`: window `[0.413, 0.565]`, `k_E = 0.5944` (cells max `0.59429`), `λ₁ = 0.597` (`ta_lam ≈ 0.59642`).
* `TI_core_16384_6`: window `[0.405, 0.554]`, `k_E = 0.5889` (cells max `0.58882`), `λ₁ = 0.591` (`ta_lam ≈ 0.59095`).
-/

namespace BstLean.Part186

open BstLean.Part182 BstLean.Part130 Real
open BstLean.Part185 BstLean.Part186.T


lemma t7c_c0_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (463 / 1000 : ℝ) ≤ c) (h1 : c ≤ (267 / 500 : ℝ)) :
    t7_Econd n (614 / 1000) (6199 / 10000) c :=
  t5_cell hn (ca := (463 / 1000 : ℝ)) (cb := (267 / 500 : ℝ)) (Sc := (169097 / 200000 : ℝ)) (Sd := (443179 / 500000 : ℝ)) (KU := (631973 / 1000000 : ℝ)) (KL := (116909 / 200000 : ℝ)) (C1 := (637027 / 1000000 : ℝ)) (C1l := (115917 / 200000 : ℝ)) (kU := (360173 / 500000 : ℝ)) (kL := (696377 / 1000000 : ℝ)) (a2 := (424539 / 500000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (843469 / 1000000 : ℝ)) (r0 := (780267 / 1000000 : ℝ)) (S0 := (865531 / 1000000 : ℝ)) (b0 := (763809 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (427673 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (614 / 1000 : ℝ)) (k655 := (710853 / 1000000 : ℝ)) (kE := (6199 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (267 / 500 : ℝ) ≤ c) (h1 : c ≤ (73 / 125 : ℝ)) :
    t7_Econd n (614 / 1000) (6199 / 10000) c :=
  t5_cell hn (ca := (267 / 500 : ℝ)) (cb := (73 / 125 : ℝ)) (Sc := (405877 / 500000 : ℝ)) (Sd := (211371 / 250000 : ℝ)) (KU := (1333 / 2000 : ℝ)) (KL := (631761 / 1000000 : ℝ)) (C1 := (671611 / 1000000 : ℝ)) (C1l := (626723 / 1000000 : ℝ)) (kU := (183769 / 250000 : ℝ)) (kL := (714859 / 1000000 : ℝ)) (a2 := (214427 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (843469 / 1000000 : ℝ)) (r0 := (395281 / 500000 : ℝ)) (S0 := (874161 / 1000000 : ℝ)) (b0 := (386957 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (427673 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (614 / 1000 : ℝ)) (k655 := (710853 / 1000000 : ℝ)) (kE := (6199 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (73 / 125 : ℝ) ≤ c) (h1 : c ≤ (151 / 250 : ℝ)) :
    t7_Econd n (614 / 1000) (6199 / 10000) c :=
  t5_cell hn (ca := (73 / 125 : ℝ)) (cb := (151 / 250 : ℝ)) (Sc := (159397 / 200000 : ℝ)) (Sd := (811753 / 1000000 : ℝ)) (KU := (680597 / 1000000 : ℝ)) (KL := (166517 / 250000 : ℝ)) (C1 := (685731 / 1000000 : ℝ)) (C1l := (660973 / 1000000 : ℝ)) (kU := (741271 / 1000000 : ℝ)) (kL := (29149 / 40000 : ℝ)) (a2 := (13458 / 15625 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (843469 / 1000000 : ℝ)) (r0 := (399099 / 500000 : ℝ)) (S0 := (175553 / 200000 : ℝ)) (b0 := (390719 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (427673 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (614 / 1000 : ℝ)) (k655 := (710853 / 1000000 : ℝ)) (kE := (6199 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c0_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (151 / 250 : ℝ) ≤ c) (h1 : c ≤ (307 / 500 : ℝ)) :
    t7_Econd n (614 / 1000) (6199 / 10000) c :=
  t5_cell hn (ca := (151 / 250 : ℝ)) (cb := (307 / 500 : ℝ)) (Sc := (789307 / 1000000 : ℝ)) (Sd := (99623 / 125000 : ℝ)) (KU := (687709 / 1000000 : ℝ)) (KL := (21251 / 31250 : ℝ)) (C1 := (138571 / 200000 : ℝ)) (C1l := (337457 / 500000 : ℝ)) (kU := (18611 / 25000 : ℝ)) (kL := (183621 / 250000 : ℝ)) (a2 := (863149 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (843469 / 1000000 : ℝ)) (r0 := (801349 / 1000000 : ℝ)) (S0 := (439801 / 500000 : ℝ)) (b0 := (784539 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (427673 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (614 / 1000 : ℝ)) (k655 := (710853 / 1000000 : ℝ)) (kE := (6199 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.463, 0.614]` (`k_E = 0.6199`). -/
theorem t7_E_c0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (463 / 1000 : ℝ) ≤ c) (h1 : c ≤ (614 / 1000 : ℝ)) :
    t7_Econd n (614 / 1000) (6199 / 10000) c := by
  replace h0 : (463 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (307 / 500 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (267 / 500 : ℝ)
  · exact t7c_c0_0 hn h0 hc0
  have hl1 : (267 / 500 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (73 / 125 : ℝ)
  · exact t7c_c0_1 hn hl1 hc1
  have hl2 : (73 / 125 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (151 / 250 : ℝ)
  · exact t7c_c0_2 hn hl2 hc2
  have hl3 : (151 / 250 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c0_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.463, 0.614]`, `n ≥ 16 384`. -/
theorem t7_num_c0 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (463 / 1000) (614 / 1000) (6199 / 10000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c0 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c0 : ta_lam (6199 / 10000) (288 / 10000) (186 / 1000) ≤ 311 / 500 := by
  unfold ta_lam
  have h : √(((6199 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 43771 / 200000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 0**: `TI_hyp n 0.463 0.614 0.622 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_0 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (463 / 1000) (614 / 1000) (311 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c0 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c0 hn)

lemma t7c_c1_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (453 / 1000 : ℝ) ≤ c) (h1 : c ≤ (131 / 250 : ℝ)) :
    t7_Econd n (604 / 1000) (3073 / 5000) c :=
  t5_cell hn (ca := (453 / 1000 : ℝ)) (cb := (131 / 250 : ℝ)) (Sc := (851719 / 1000000 : ℝ)) (Sd := (89151 / 100000 : ℝ)) (KU := (312593 / 500000 : ℝ)) (KL := (144509 / 250000 : ℝ)) (C1 := (157557 / 250000 : ℝ)) (C1l := (573087 / 1000000 : ℝ)) (kU := (717519 / 1000000 : ℝ)) (kL := (17347 / 25000 : ℝ)) (a2 := (847411 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (105133 / 125000 : ℝ)) (r0 := (389433 / 500000 : ℝ)) (S0 := (107983 / 125000 : ℝ)) (b0 := (381219 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (852941 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (604 / 1000 : ℝ)) (k655 := (353401 / 500000 : ℝ)) (kE := (3073 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (131 / 250 : ℝ) ≤ c) (h1 : c ≤ (287 / 500 : ℝ)) :
    t7_Econd n (604 / 1000) (3073 / 5000) c :=
  t5_cell hn (ca := (131 / 250 : ℝ)) (cb := (287 / 500 : ℝ)) (Sc := (102357 / 125000 : ℝ)) (Sd := (425859 / 500000 : ℝ)) (KU := (329757 / 500000 : ℝ)) (KL := (156251 / 250000 : ℝ)) (C1 := (664613 / 1000000 : ℝ)) (C1l := (619977 / 1000000 : ℝ)) (kU := (366023 / 500000 : ℝ)) (kL := (712173 / 1000000 : ℝ)) (a2 := (42797 / 50000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (105133 / 125000 : ℝ)) (r0 := (394537 / 500000 : ℝ)) (S0 := (872393 / 1000000 : ℝ)) (b0 := (772459 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (852941 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (604 / 1000 : ℝ)) (k655 := (353401 / 500000 : ℝ)) (kE := (3073 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (287 / 500 : ℝ) ≤ c) (h1 : c ≤ (297 / 500 : ℝ)) :
    t7_Econd n (604 / 1000) (3073 / 5000) c :=
  t5_cell hn (ca := (287 / 500 : ℝ)) (cb := (297 / 500 : ℝ)) (Sc := (402233 / 500000 : ℝ)) (Sd := (163771 / 200000 : ℝ)) (KU := (84191 / 125000 : ℝ)) (KL := (659137 / 1000000 : ℝ)) (C1 := (678651 / 1000000 : ℝ)) (C1l := (327027 / 500000 : ℝ)) (kU := (738151 / 1000000 : ℝ)) (kL := (181473 / 250000 : ℝ)) (a2 := (859499 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (105133 / 125000 : ℝ)) (r0 := (199161 / 250000 : ℝ)) (S0 := (54747 / 62500 : ℝ)) (b0 := (389959 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (852941 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (604 / 1000 : ℝ)) (k655 := (353401 / 500000 : ℝ)) (kE := (3073 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c1_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (297 / 500 : ℝ) ≤ c) (h1 : c ≤ (151 / 250 : ℝ)) :
    t7_Econd n (604 / 1000) (3073 / 5000) c :=
  t5_cell hn (ca := (297 / 500 : ℝ)) (cb := (151 / 250 : ℝ)) (Sc := (159397 / 200000 : ℝ)) (Sd := (160893 / 200000 : ℝ)) (KU := (680597 / 1000000 : ℝ)) (KL := (673033 / 1000000 : ℝ)) (C1 := (685731 / 1000000 : ℝ)) (C1l := (667927 / 1000000 : ℝ)) (kU := (741271 / 1000000 : ℝ)) (kL := (731589 / 1000000 : ℝ)) (a2 := (13458 / 15625 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (105133 / 125000 : ℝ)) (r0 := (799767 / 1000000 : ℝ)) (S0 := (175553 / 200000 : ℝ)) (b0 := (782991 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (852941 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (604 / 1000 : ℝ)) (k655 := (353401 / 500000 : ℝ)) (kE := (3073 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.453, 0.604]` (`k_E = 0.6146`). -/
theorem t7_E_c1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (453 / 1000 : ℝ) ≤ c) (h1 : c ≤ (604 / 1000 : ℝ)) :
    t7_Econd n (604 / 1000) (3073 / 5000) c := by
  replace h0 : (453 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (151 / 250 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (131 / 250 : ℝ)
  · exact t7c_c1_0 hn h0 hc0
  have hl1 : (131 / 250 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (287 / 500 : ℝ)
  · exact t7c_c1_1 hn hl1 hc1
  have hl2 : (287 / 500 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (297 / 500 : ℝ)
  · exact t7c_c1_2 hn hl2 hc2
  have hl3 : (297 / 500 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c1_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.453, 0.604]`, `n ≥ 16 384`. -/
theorem t7_num_c1 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (453 / 1000) (604 / 1000) (3073 / 5000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c1 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c1 : ta_lam (3073 / 5000) (288 / 10000) (186 / 1000) ≤ 617 / 1000 := by
  unfold ta_lam
  have h : √(((3073 / 5000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 54057 / 250000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 1**: `TI_hyp n 0.453 0.604 0.617 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_1 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (453 / 1000) (604 / 1000) (617 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c1 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c1 hn)

lemma t7c_c2_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (443 / 1000 : ℝ) ≤ c) (h1 : c ≤ (257 / 500 : ℝ)) :
    t7_Econd n (594 / 1000) (6093 / 10000) c :=
  t5_cell hn (ca := (443 / 1000 : ℝ)) (cb := (257 / 500 : ℝ)) (Sc := (857791 / 1000000 : ℝ)) (Sd := (896521 / 1000000 : ℝ)) (KU := (618439 / 1000000 : ℝ)) (KL := (571563 / 1000000 : ℝ)) (C1 := (62347 / 100000 : ℝ)) (C1l := (4533 / 8000 : ℝ)) (kU := (714729 / 1000000 : ℝ)) (kL := (43213 / 62500 : ℝ)) (a2 := (845763 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (209669 / 250000 : ℝ)) (r0 := (194369 / 250000 : ℝ)) (S0 := (107777 / 125000 : ℝ)) (b0 := (761079 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (850553 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (594 / 1000 : ℝ)) (k655 := (702791 / 1000000 : ℝ)) (kE := (6093 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (257 / 500 : ℝ) ≤ c) (h1 : c ≤ (141 / 250 : ℝ)) :
    t7_Econd n (594 / 1000) (6093 / 10000) c :=
  t5_cell hn (ca := (257 / 500 : ℝ)) (cb := (141 / 250 : ℝ)) (Sc := (33031 / 40000 : ℝ)) (Sd := (85779 / 100000 : ℝ)) (KU := (81571 / 125000 : ℝ)) (KL := (309141 / 500000 : ℝ)) (C1 := (82207 / 125000 : ℝ)) (C1l := (306633 / 500000 : ℝ)) (kU := (36453 / 50000 : ℝ)) (kL := (141903 / 200000 : ℝ)) (a2 := (427097 / 500000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (209669 / 250000 : ℝ)) (r0 := (787599 / 1000000 : ℝ)) (S0 := (870647 / 1000000 : ℝ)) (b0 := (96377 / 125000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (850553 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (594 / 1000 : ℝ)) (k655 := (702791 / 1000000 : ℝ)) (kE := (6093 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (141 / 250 : ℝ) ≤ c) (h1 : c ≤ (73 / 125 : ℝ)) :
    t7_Econd n (594 / 1000) (6093 / 10000) c :=
  t5_cell hn (ca := (141 / 250 : ℝ)) (cb := (73 / 125 : ℝ)) (Sc := (405877 / 500000 : ℝ)) (Sd := (412887 / 500000 : ℝ)) (KU := (1333 / 2000 : ℝ)) (KL := (652241 / 1000000 : ℝ)) (C1 := (671611 / 1000000 : ℝ)) (C1l := (647169 / 1000000 : ℝ)) (kU := (183769 / 250000 : ℝ)) (kL := (72309 / 100000 : ℝ)) (a2 := (214427 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (209669 / 250000 : ℝ)) (r0 := (24847 / 31250 : ℝ)) (S0 := (874161 / 1000000 : ℝ)) (b0 := (778411 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (850553 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (594 / 1000 : ℝ)) (k655 := (702791 / 1000000 : ℝ)) (kE := (6093 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c2_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (73 / 125 : ℝ) ≤ c) (h1 : c ≤ (297 / 500 : ℝ)) :
    t7_Econd n (594 / 1000) (6093 / 10000) c :=
  t5_cell hn (ca := (73 / 125 : ℝ)) (cb := (297 / 500 : ℝ)) (Sc := (402233 / 500000 : ℝ)) (Sd := (811753 / 1000000 : ℝ)) (KU := (84191 / 125000 : ℝ)) (KL := (166517 / 250000 : ℝ)) (C1 := (678651 / 1000000 : ℝ)) (C1l := (660973 / 1000000 : ℝ)) (kU := (738151 / 1000000 : ℝ)) (kL := (29149 / 40000 : ℝ)) (a2 := (859499 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (209669 / 250000 : ℝ)) (r0 := (399099 / 500000 : ℝ)) (S0 := (54747 / 62500 : ℝ)) (b0 := (48841 / 62500 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (850553 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (594 / 1000 : ℝ)) (k655 := (702791 / 1000000 : ℝ)) (kE := (6093 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.443, 0.594]` (`k_E = 0.6093`). -/
theorem t7_E_c2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (443 / 1000 : ℝ) ≤ c) (h1 : c ≤ (594 / 1000 : ℝ)) :
    t7_Econd n (594 / 1000) (6093 / 10000) c := by
  replace h0 : (443 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (297 / 500 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (257 / 500 : ℝ)
  · exact t7c_c2_0 hn h0 hc0
  have hl1 : (257 / 500 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (141 / 250 : ℝ)
  · exact t7c_c2_1 hn hl1 hc1
  have hl2 : (141 / 250 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (73 / 125 : ℝ)
  · exact t7c_c2_2 hn hl2 hc2
  have hl3 : (73 / 125 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c2_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.443, 0.594]`, `n ≥ 16 384`. -/
theorem t7_num_c2 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (443 / 1000) (594 / 1000) (6093 / 10000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c2 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c2 : ta_lam (6093 / 10000) (288 / 10000) (186 / 1000) ≤ 153 / 250 := by
  unfold ta_lam
  have h : √(((6093 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 106801 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 2**: `TI_hyp n 0.443 0.594 0.612 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_2 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (443 / 1000) (594 / 1000) (153 / 250) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c2 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c2 hn)

lemma t7c_c3_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (433 / 1000 : ℝ) ≤ c) (h1 : c ≤ (63 / 125 : ℝ)) :
    t7_Econd n (584 / 1000) (6041 / 10000) c :=
  t5_cell hn (ca := (433 / 1000 : ℝ)) (cb := (63 / 125 : ℝ)) (Sc := (107963 / 125000 : ℝ)) (Sd := (901393 / 1000000 : ℝ)) (KU := (611729 / 1000000 : ℝ)) (KL := (141281 / 250000 : ℝ)) (C1 := (616749 / 1000000 : ℝ)) (C1l := (140049 / 250000 : ℝ)) (kU := (28479 / 40000 : ℝ)) (kL := (688959 / 1000000 : ℝ)) (a2 := (422067 / 500000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (167261 / 200000 : ℝ)) (r0 := (24253 / 31250 : ℝ)) (S0 := (860587 / 1000000 : ℝ)) (b0 := (759729 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (424091 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (584 / 1000 : ℝ)) (k655 := (698819 / 1000000 : ℝ)) (kE := (6041 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (63 / 125 : ℝ) ≤ c) (h1 : c ≤ (277 / 500 : ℝ)) :
    t7_Econd n (584 / 1000) (6041 / 10000) c :=
  t5_cell hn (ca := (63 / 125 : ℝ)) (cb := (277 / 500 : ℝ)) (Sc := (832517 / 1000000 : ℝ)) (Sd := (863703 / 1000000 : ℝ)) (KU := (645663 / 1000000 : ℝ)) (KL := (122319 / 200000 : ℝ)) (C1 := (650739 / 1000000 : ℝ)) (C1l := (606591 / 1000000 : ℝ)) (kU := (145223 / 200000 : ℝ)) (kL := (141377 / 200000 : ℝ)) (a2 := (213117 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (167261 / 200000 : ℝ)) (r0 := (786137 / 1000000 : ℝ)) (S0 := (868921 / 1000000 : ℝ)) (b0 := (384793 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (424091 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (584 / 1000 : ℝ)) (k655 := (698819 / 1000000 : ℝ)) (kE := (6041 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (277 / 500 : ℝ) ≤ c) (h1 : c ≤ (287 / 500 : ℝ)) :
    t7_Econd n (584 / 1000) (6041 / 10000) c :=
  t5_cell hn (ca := (277 / 500 : ℝ)) (cb := (287 / 500 : ℝ)) (Sc := (102357 / 125000 : ℝ)) (Sd := (208129 / 250000 : ℝ)) (KU := (329757 / 500000 : ℝ)) (KL := (645379 / 1000000 : ℝ)) (C1 := (664613 / 1000000 : ℝ)) (C1l := (640319 / 1000000 : ℝ)) (kU := (366023 / 500000 : ℝ)) (kL := (720317 / 1000000 : ℝ)) (a2 := (42797 / 50000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (167261 / 200000 : ℝ)) (r0 := (793577 / 1000000 : ℝ)) (S0 := (872393 / 1000000 : ℝ)) (b0 := (776917 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (424091 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (584 / 1000 : ℝ)) (k655 := (698819 / 1000000 : ℝ)) (kE := (6041 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c3_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (287 / 500 : ℝ) ≤ c) (h1 : c ≤ (73 / 125 : ℝ)) :
    t7_Econd n (584 / 1000) (6041 / 10000) c :=
  t5_cell hn (ca := (287 / 500 : ℝ)) (cb := (73 / 125 : ℝ)) (Sc := (405877 / 500000 : ℝ)) (Sd := (163771 / 200000 : ℝ)) (KU := (1333 / 2000 : ℝ)) (KL := (659137 / 1000000 : ℝ)) (C1 := (671611 / 1000000 : ℝ)) (C1l := (327027 / 500000 : ℝ)) (kU := (183769 / 250000 : ℝ)) (kL := (181473 / 250000 : ℝ)) (a2 := (214427 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (167261 / 200000 : ℝ)) (r0 := (199161 / 250000 : ℝ)) (S0 := (874161 / 1000000 : ℝ)) (b0 := (155987 / 200000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (424091 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (584 / 1000 : ℝ)) (k655 := (698819 / 1000000 : ℝ)) (kE := (6041 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.433, 0.584]` (`k_E = 0.6041`). -/
theorem t7_E_c3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (433 / 1000 : ℝ) ≤ c) (h1 : c ≤ (584 / 1000 : ℝ)) :
    t7_Econd n (584 / 1000) (6041 / 10000) c := by
  replace h0 : (433 / 1000 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (73 / 125 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (63 / 125 : ℝ)
  · exact t7c_c3_0 hn h0 hc0
  have hl1 : (63 / 125 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (277 / 500 : ℝ)
  · exact t7c_c3_1 hn hl1 hc1
  have hl2 : (277 / 500 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (287 / 500 : ℝ)
  · exact t7c_c3_2 hn hl2 hc2
  have hl3 : (287 / 500 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c3_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.433, 0.584]`, `n ≥ 16 384`. -/
theorem t7_num_c3 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (433 / 1000) (584 / 1000) (6041 / 10000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c3 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c3 : ta_lam (6041 / 10000) (288 / 10000) (186 / 1000) ≤ 607 / 1000 := by
  unfold ta_lam
  have h : √(((6041 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 105513 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 3**: `TI_hyp n 0.433 0.584 0.607 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_3 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (433 / 1000) (584 / 1000) (607 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c3 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c3 hn)

lemma t7c_c4_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (423 / 1000 : ℝ) ≤ c) (h1 : c ≤ (99 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (2997 / 5000) c :=
  t5_cell hn (ca := (423 / 1000 : ℝ)) (cb := (99 / 200 : ℝ)) (Sc := (868893 / 1000000 : ℝ)) (Sd := (906129 / 1000000 : ℝ)) (KU := (605723 / 1000000 : ℝ)) (KL := (558719 / 1000000 : ℝ)) (C1 := (610733 / 1000000 : ℝ)) (C1l := (276901 / 500000 : ℝ)) (kU := (28381 / 40000 : ℝ)) (kL := (137307 / 200000 : ℝ)) (a2 := (842681 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (104273 / 125000 : ℝ)) (r0 := (774729 / 1000000 : ℝ)) (S0 := (429567 / 500000 : ℝ)) (b0 := (75839 / 100000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (846061 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (2997 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (99 / 200 : ℝ) ≤ c) (h1 : c ≤ (109 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (2997 / 5000) c :=
  t5_cell hn (ca := (99 / 200 : ℝ)) (cb := (109 / 200 : ℝ)) (Sc := (838437 / 1000000 : ℝ)) (Sd := (217223 / 250000 : ℝ)) (KU := (639483 / 1000000 : ℝ)) (KL := (302803 / 500000 : ℝ)) (C1 := (644549 / 1000000 : ℝ)) (C1l := (600611 / 1000000 : ℝ)) (kU := (1447 / 2000 : ℝ)) (kL := (35227 / 50000 : ℝ)) (a2 := (850933 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (104273 / 125000 : ℝ)) (r0 := (784831 / 1000000 : ℝ)) (S0 := (433693 / 500000 : ℝ)) (b0 := (192077 / 250000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (846061 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (2997 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (109 / 200 : ℝ) ≤ c) (h1 : c ≤ (113 / 200 : ℝ)) :
    t7_Econd n (575 / 1000) (2997 / 5000) c :=
  t5_cell hn (ca := (109 / 200 : ℝ)) (cb := (113 / 200 : ℝ)) (Sc := (825091 / 1000000 : ℝ)) (Sd := (209609 / 250000 : ℝ)) (KU := (653261 / 1000000 : ℝ)) (KL := (319617 / 500000 : ℝ)) (C1 := (13167 / 20000 : ℝ)) (C1l := (79273 / 125000 : ℝ)) (kU := (729357 / 1000000 : ℝ)) (kL := (717847 / 1000000 : ℝ)) (a2 := (26699 / 31250 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (104273 / 125000 : ℝ)) (r0 := (396107 / 500000 : ℝ)) (S0 := (870821 / 1000000 : ℝ)) (b0 := (775583 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (846061 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (2997 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c4_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (113 / 200 : ℝ) ≤ c) (h1 : c ≤ (23 / 40 : ℝ)) :
    t7_Econd n (575 / 1000) (2997 / 5000) c :=
  t5_cell hn (ca := (113 / 200 : ℝ)) (cb := (23 / 40 : ℝ)) (Sc := (409077 / 500000 : ℝ)) (Sd := (82509 / 100000 : ℝ)) (KU := (660211 / 1000000 : ℝ)) (KL := (652929 / 1000000 : ℝ)) (C1 := (20791 / 31250 : ℝ)) (C1l := (40491 / 62500 : ℝ)) (kU := (183087 / 250000 : ℝ)) (kL := (723369 / 1000000 : ℝ)) (a2 := (214029 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (104273 / 125000 : ℝ)) (r0 := (795257 / 1000000 : ℝ)) (S0 := (872569 / 1000000 : ℝ)) (b0 := (389289 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (846061 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (575 / 1000 : ℝ)) (k655 := (173819 / 250000 : ℝ)) (kE := (2997 / 5000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.423, 0.575]` (`k_E = 0.5994`). -/
theorem t7_E_c4 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (423 / 1000 : ℝ) ≤ c) (h1 : c ≤ (575 / 1000 : ℝ)) :
    t7_Econd n (575 / 1000) (2997 / 5000) c := by
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

/-- **All numeric hypotheses of `d4_num`** on `[0.423, 0.575]`, `n ≥ 16 384`. -/
theorem t7_num_c4 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (423 / 1000) (575 / 1000) (2997 / 5000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c4 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c4 : ta_lam (2997 / 5000) (288 / 10000) (186 / 1000) ≤ 301 / 500 := by
  unfold ta_lam
  have h : √(((2997 / 5000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 104349 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 4**: `TI_hyp n 0.423 0.575 0.602 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_4 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (423 / 1000) (575 / 1000) (301 / 500) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c4 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c4 hn)

lemma t7c_c5_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (413 / 1000 : ℝ) ≤ c) (h1 : c ≤ (97 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (743 / 1250) c :=
  t5_cell hn (ca := (413 / 1000 : ℝ)) (cb := (97 / 200 : ℝ)) (Sc := (174903 / 200000 : ℝ)) (Sd := (910731 / 1000000 : ℝ)) (KU := (119817 / 200000 : ℝ)) (KL := (11047 / 20000 : ℝ)) (C1 := (151021 / 250000 : ℝ)) (C1l := (547443 / 1000000 : ℝ)) (kU := (176709 / 250000 : ℝ)) (kL := (342067 / 500000 : ℝ)) (a2 := (210271 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (415921 / 500000 : ℝ)) (r0 := (193343 / 250000 : ℝ)) (S0 := (857537 / 1000000 : ℝ)) (b0 := (378531 / 500000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (843719 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (743 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (97 / 200 : ℝ) ≤ c) (h1 : c ≤ (107 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (743 / 1250) c :=
  t5_cell hn (ca := (97 / 200 : ℝ)) (cb := (107 / 200 : ℝ)) (Sc := (844853 / 1000000 : ℝ)) (Sd := (437257 / 500000 : ℝ)) (KU := (316327 / 500000 : ℝ)) (KL := (299493 / 500000 : ℝ)) (C1 := (637709 / 1000000 : ℝ)) (C1l := (297001 / 500000 : ℝ)) (kU := (720631 / 1000000 : ℝ)) (kL := (701961 / 1000000 : ℝ)) (a2 := (169849 / 200000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (415921 / 500000 : ℝ)) (r0 := (24481 / 31250 : ℝ)) (S0 := (432849 / 500000 : ℝ)) (b0 := (766901 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (843719 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (743 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (107 / 200 : ℝ) ≤ c) (h1 : c ≤ (111 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (743 / 1250) c :=
  t5_cell hn (ca := (107 / 200 : ℝ)) (cb := (111 / 200 : ℝ)) (Sc := (831851 / 1000000 : ℝ)) (Sd := (211213 / 250000 : ℝ)) (KU := (40397 / 62500 : ℝ)) (KL := (316219 / 500000 : ℝ)) (C1 := (65143 / 100000 : ℝ)) (C1l := (627399 / 1000000 : ℝ)) (kU := (90801 / 125000 : ℝ)) (kL := (715129 / 1000000 : ℝ)) (a2 := (5329 / 6250 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (415921 / 500000 : ℝ)) (r0 := (790711 / 1000000 : ℝ)) (S0 := (869093 / 1000000 : ℝ)) (b0 := (24191 / 31250 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (843719 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (743 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c5_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (111 / 200 : ℝ) ≤ c) (h1 : c ≤ (113 / 200 : ℝ)) :
    t7_Econd n (565 / 1000) (743 / 1250) c :=
  t5_cell hn (ca := (111 / 200 : ℝ)) (cb := (113 / 200 : ℝ)) (Sc := (825091 / 1000000 : ℝ)) (Sd := (16637 / 20000 : ℝ)) (KU := (653261 / 1000000 : ℝ)) (KL := (40379 / 62500 : ℝ)) (C1 := (13167 / 20000 : ℝ)) (C1l := (320501 / 500000 : ℝ)) (kU := (729357 / 1000000 : ℝ)) (kL := (720593 / 1000000 : ℝ)) (a2 := (26699 / 31250 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (415921 / 500000 : ℝ)) (r0 := (793729 / 1000000 : ℝ)) (S0 := (870821 / 1000000 : ℝ)) (b0 := (777083 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (843719 / 1000000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (565 / 1000 : ℝ)) (k655 := (345687 / 500000 : ℝ)) (kE := (743 / 1250 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.413, 0.565]` (`k_E = 0.5944`). -/
theorem t7_E_c5 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (413 / 1000 : ℝ) ≤ c) (h1 : c ≤ (565 / 1000 : ℝ)) :
    t7_Econd n (565 / 1000) (743 / 1250) c := by
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

/-- **All numeric hypotheses of `d4_num`** on `[0.413, 0.565]`, `n ≥ 16 384`. -/
theorem t7_num_c5 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (413 / 1000) (565 / 1000) (743 / 1250) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c5 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c5 : ta_lam (743 / 1250) (288 / 10000) (186 / 1000) ≤ 597 / 1000 := by
  unfold ta_lam
  have h : √(((743 / 1250 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 103111 / 500000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 5**: `TI_hyp n 0.413 0.565 0.597 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_5 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (413 / 1000) (565 / 1000) (597 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c5 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c5 hn)

lemma t7c_c6_0 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (81 / 200 : ℝ) ≤ c) (h1 : c ≤ (237 / 500 : ℝ)) :
    t7_Econd n (554 / 1000) (5889 / 10000) c :=
  t5_cell hn (ca := (81 / 200 : ℝ)) (cb := (237 / 500 : ℝ)) (Sc := (35221 / 40000 : ℝ)) (Sd := (228579 / 250000 : ℝ)) (KU := (591827 / 1000000 : ℝ)) (KL := (547279 / 1000000 : ℝ)) (C1 := (298407 / 500000 : ℝ)) (C1l := (542381 / 1000000 : ℝ)) (kU := (175979 / 250000 : ℝ)) (kL := (68223 / 100000 : ℝ)) (a2 := (839347 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (829281 / 1000000 : ℝ)) (r0 := (386147 / 500000 : ℝ)) (S0 := (4279 / 5000 : ℝ)) (b0 := (756013 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (420579 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (554 / 1000 : ℝ)) (k655 := (8589 / 12500 : ℝ)) (kE := (5889 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_1 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (237 / 500 : ℝ) ≤ c) (h1 : c ≤ (131 / 250 : ℝ)) :
    t7_Econd n (554 / 1000) (5889 / 10000) c :=
  t5_cell hn (ca := (237 / 500 : ℝ)) (cb := (131 / 250 : ℝ)) (Sc := (851719 / 1000000 : ℝ)) (Sd := (220131 / 250000 : ℝ)) (KU := (312593 / 500000 : ℝ)) (KL := (9246 / 15625 : ℝ)) (C1 := (157557 / 250000 : ℝ)) (C1l := (146693 / 250000 : ℝ)) (kU := (717519 / 1000000 : ℝ)) (kL := (699153 / 1000000 : ℝ)) (a2 := (847411 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (829281 / 1000000 : ℝ)) (r0 := (390911 / 500000 : ℝ)) (S0 := (107983 / 125000 : ℝ)) (b0 := (153073 / 200000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (420579 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (554 / 1000 : ℝ)) (k655 := (8589 / 12500 : ℝ)) (kE := (5889 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_2 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (131 / 250 : ℝ) ≤ c) (h1 : c ≤ (68 / 125 : ℝ)) :
    t7_Econd n (554 / 1000) (5889 / 10000) c :=
  t5_cell hn (ca := (131 / 250 : ℝ)) (cb := (68 / 125 : ℝ)) (Sc := (419543 / 500000 : ℝ)) (Sd := (425859 / 500000 : ℝ)) (KU := (319399 / 500000 : ℝ)) (KL := (156251 / 250000 : ℝ)) (C1 := (643863 / 1000000 : ℝ)) (C1l := (619977 / 1000000 : ℝ)) (kU := (723211 / 1000000 : ℝ)) (kL := (712173 / 1000000 : ℝ)) (a2 := (850763 / 1000000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (829281 / 1000000 : ℝ)) (r0 := (394537 / 500000 : ℝ)) (S0 := (54201 / 62500 : ℝ)) (b0 := (772511 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (420579 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (554 / 1000 : ℝ)) (k655 := (8589 / 12500 : ℝ)) (kE := (5889 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma t7c_c6_3 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (68 / 125 : ℝ) ≤ c) (h1 : c ≤ (277 / 500 : ℝ)) :
    t7_Econd n (554 / 1000) (5889 / 10000) c :=
  t5_cell hn (ca := (68 / 125 : ℝ)) (cb := (277 / 500 : ℝ)) (Sc := (832517 / 1000000 : ℝ)) (Sd := (167817 / 200000 : ℝ)) (KU := (645663 / 1000000 : ℝ)) (KL := (638553 / 1000000 : ℝ)) (C1 := (650739 / 1000000 : ℝ)) (C1l := (19797 / 31250 : ℝ)) (kU := (145223 / 200000 : ℝ)) (kL := (358787 / 500000 : ℝ)) (a2 := (213117 / 250000 : ℝ)) (al := (1000293 / 1000000 : ℝ)) (am := (829281 / 1000000 : ℝ)) (r0 := (792063 / 1000000 : ℝ)) (S0 := (868921 / 1000000 : ℝ)) (b0 := (775453 / 1000000 : ℝ)) (l0 := (101217 / 100000 : ℝ)) (m0 := (420579 / 500000 : ℝ)) (p0 := (76791 / 50000 : ℝ)) (t0 := (2173447 / 1000000 : ℝ)) (cp := (554 / 1000 : ℝ)) (k655 := (8589 / 12500 : ℝ)) (kE := (5889 / 10000 : ℝ)) h0 h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [t5P7]) (by norm_num [t5P5]) (by norm_num) (by norm_num) (by norm_num [t5P7])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The E-block conditions on the window `[0.405, 0.554]` (`k_E = 0.5889`). -/
theorem t7_E_c6 {n : ℕ} (hn : 16384 ≤ n) {c : ℝ} (h0 : (405 / 1000 : ℝ) ≤ c) (h1 : c ≤ (554 / 1000 : ℝ)) :
    t7_Econd n (554 / 1000) (5889 / 10000) c := by
  replace h0 : (81 / 200 : ℝ) ≤ c := by norm_num at h0 ⊢; linarith
  replace h1 : c ≤ (277 / 500 : ℝ) := by norm_num at h1 ⊢; linarith
  by_cases hc0 : c ≤ (237 / 500 : ℝ)
  · exact t7c_c6_0 hn h0 hc0
  have hl1 : (237 / 500 : ℝ) ≤ c := (not_le.mp hc0).le
  by_cases hc1 : c ≤ (131 / 250 : ℝ)
  · exact t7c_c6_1 hn hl1 hc1
  have hl2 : (131 / 250 : ℝ) ≤ c := (not_le.mp hc1).le
  by_cases hc2 : c ≤ (68 / 125 : ℝ)
  · exact t7c_c6_2 hn hl2 hc2
  have hl3 : (68 / 125 : ℝ) ≤ c := (not_le.mp hc2).le
  exact t7c_c6_3 hn hl3 h1

/-- **All numeric hypotheses of `d4_num`** on `[0.405, 0.554]`, `n ≥ 16 384`. -/
theorem t7_num_c6 {n : ℕ} (hn : 16384 ≤ n) :
    d4_num n (405 / 1000) (554 / 1000) (5889 / 10000) (288 / 10000) (186 / 1000) (293 / 1000000) 46
      (1 / 8) (1 / 100) (2 / 10 ^ 19) := by
  refine ⟨?_, TT.tsn_am hn, fun c h0 h1 => ?_⟩
  · have h := TT.tsn_ko hn; rwa [TT.tsnEta_eq] at h
  · obtain ⟨hdm, h6, hc1, hr1, hpos, hks⟩ := TT.tsn_S hn (c := c) (by norm_num at h0 ⊢; linarith) (by norm_num at h1 ⊢; linarith)
    rw [TT.tsnEta_eq] at hks
    obtain ⟨e1, e2, e3, e4, e5⟩ := t7_E_c6 hn h0 h1
    exact ⟨hdm, h6, hc1, hr1, hpos, e1, e2, e3, e4, e5, hks⟩

theorem t7_lam_c6 : ta_lam (5889 / 10000) (288 / 10000) (186 / 1000) ≤ 591 / 1000 := by
  unfold ta_lam
  have h : √(((5889 / 10000 - 186 / 1000 : ℝ) / 2) ^ 2 + (288 / 10000) ^ 2) ≤ 407 / 2000 :=
    TT.tsn_sqrt_le (by norm_num) (by norm_num)
  linarith

/-- **Core-window Lemma TI 6**: `TI_hyp n 0.405 0.554 0.591 10⁻¹⁸`, every `n ≥ 16 384`. -/
theorem TI_core_16384_6 : ∀ n : ℕ, 16384 ≤ n →
    BstLean.Part182.TI_hyp n (405 / 1000) (554 / 1000) (591 / 1000) (1 / 10 ^ 18) := by
  intro n hn
  refine TI_hyp_mono t7_lam_c6 le_rfl ?_
  exact d4_TI46 (by omega) (by norm_num) (by norm_num) (by norm_num) (t7_eta hn) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (t7_num_c6 hn)

end BstLean.Part186

#print axioms BstLean.Part186.TI_core_16384_0
#print axioms BstLean.Part186.TI_core_16384_1
#print axioms BstLean.Part186.TI_core_16384_2
#print axioms BstLean.Part186.TI_core_16384_3
#print axioms BstLean.Part186.TI_core_16384_4
#print axioms BstLean.Part186.TI_core_16384_5
#print axioms BstLean.Part186.TI_core_16384_6
