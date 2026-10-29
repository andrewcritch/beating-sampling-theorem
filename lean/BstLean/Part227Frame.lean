import BstLean.Part227Centre

/-! Part 227: the parameterized computed-centre frame at base dimension n. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part137 BstLean.Part140 BstLean.Part157 BstLean.Part159

noncomputable def frameFormula (n : ℕ) (sp p₂ Xc dT eB r0 k0 k6 ε₁ ε₂ s : ℝ) : ℝ :=
  (3017 / 20000 + (138 / 1000) / (2 * (n : ℝ)) +
    (k0 / sp + (1 / 1000) * (17321 / 20000) + (2 / 5) * k6) +
      centreDistance n Xc) / s + centreFluctuation n dT / ε₂ ^ 2 +
        (2235 / 100) * r0 / ((n : ℝ) * p₂ * ε₁ ^ 2)

/-- The certificate contains scalar guards, not a frame or moment premise. -/
structure FrameCertificate (n : ℕ) (sp p₂ Xc dT eB : ℝ) where
  r0 : ℝ
  k0 : ℝ
  k6 : ℝ
  ε₁ : ℝ
  ε₂ : ℝ
  s : ℝ
  r0_nonneg : 0 ≤ r0
  radius : 1 ≤ r0 ^ 2 * (n : ℝ) ^ 3
  k0_nonneg : 0 ≤ k0
  kernel : (2235 / 100) * r0 ≤ k0 ^ 2
  k6_nonneg : 0 ≤ k6
  sixth : 15 / (8 * (n : ℝ)) ≤ k6 ^ 2
  ε₁_pos : 0 < ε₁
  ε₂_pos : 0 < ε₂
  s_pos : 0 < s
  norm_lower : 0 ≤ kap1 (2 * n) - eB
  norm_separation : √(perturbation n) < √(kap1 (2 * n) - eB)
  denominator : s ≤ 1 - ε₁ - (4938 / 10000 + ε₂) ^ 2 / centreLower n eB

noncomputable def frameValue {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) : ℝ :=
  frameFormula n sp p₂ Xc dT eB c.r0 c.k0 c.k6 c.ε₁ c.ε₂ c.s

/-- The hidden event supplies every analytic premise of frameB_num. -/
theorem computed_frame {n : ℕ} (hn : 4096 ≤ n) {sp p₂ Xc dT eB : ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 ≤ dT) (hdT : dT ≤ 1 / 400000)
    (c : FrameCertificate n sp p₂ Xc dT eB)
    {θ : WHid n} (hθ : θ ∈ hidden n sp p₂ Xc dT eB) (w : Fin (mW n) → ℝ) :
    (∫ u, (∑ j, eDir (bWp θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n)) ≤
      frameValue c / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hS := hθ.1.1.2
  have hA := hθ.1.2
  have hB := hθ.2
  have hp := hidden_subset_GPap hsp hp₂ hXc hdT hθ
  have hξ := mean_distance hn hθ.1.1.1.1.2 hS hA
  have hX := scalar_fluctuation hn hdT0 hθ.1.1.1.2 hp.1.1.1.1 hS hA
  have hβ := (computed_norm_window hn hB hS hA c.norm_lower c.norm_separation.le).1
  have hβpos : 0 < centreLower n eB := by
    unfold centreLower
    exact sq_pos_of_pos (sub_pos.mpr c.norm_separation)
  have hβb : (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * centreLower n eB ≤ normSq (bWp θ) := by
    have h := mul_le_mul_of_nonneg_left hβ
      (show (0 : ℝ) ≤ (mW n : ℝ) / (2 * (n : ℝ)) by positivity)
    change (mW n : ℝ) / (2 * (n : ℝ)) * centreLower n eB ≤ _ at h
    have he : (mW n : ℝ) / (2 * (n : ℝ)) *
        ((n : ℝ) * (2 / (mW n : ℝ) * normSq (bWp θ))) = normSq (bWp θ) := by field_simp
    rw [he] at h
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  obtain ⟨hk1, hk2⟩ := BstLean.Part140.kap1_window hn
  have hsle : c.s ≤ 1 - c.ε₁ - (kap1 (2 * n) + c.ε₂) ^ 2 / centreLower n eB := by
    have hk : (kap1 (2 * n) + c.ε₂) ^ 2 ≤ (4938 / 10000 + c.ε₂) ^ 2 :=
      pow_le_pow_left₀ (by linarith [c.ε₂_pos]) (by linarith) 2
    have h := div_le_div_of_nonneg_right hk hβpos.le
    linarith [c.denominator]
  obtain ⟨bq, hb0, hb1, hmodel⟩ := kk_three
  exact frameB_num (n := n) (n0 := n) hn le_rfl (b := bq)
    (c2 := 138 / 1000) (η := 1 / 1000) (K₃ := 2 / 5)
    (r0 := c.r0) (k0 := c.k0) (k6 := c.k6) (sp := sp) (p₂ := p₂)
    (ε₁ := c.ε₁) (ε₂ := c.ε₂) (s := c.s)
    (D0 := c.k0 / sp + (1 / 1000) * (17321 / 20000) + (2 / 5) * c.k6)
    (C := frameValue c) (ξ₀ := centreDistance n Xc) (a := kap1 (2 * n))
    (dT := centreFluctuation n dT) (β := centreLower n eB)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    c.r0_nonneg c.radius c.k0_nonneg c.kernel c.k6_nonneg c.sixth
    (by linarith) (by linarith) c.ε₁_pos c.ε₂_pos rfl
    (sq_nonneg _) (by linarith) hβpos c.s_pos hsle
    (by dsimp [frameValue, frameFormula]; norm_num)
    hθ.1.1.1.1.1 hξ hX hβb w

/-- The retained frame keeps the actual computed centre of the design. -/
theorem retained_frame {n : ℕ} (hn : 4096 ≤ n) (D : Centres n) (hD : D.bW = bWp)
    {sp p₂ Xc dT eB : ℝ} (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 ≤ dT) (hdT : dT ≤ 1 / 400000)
    (c : FrameCertificate n sp p₂ Xc dT eB) {E : Set (Ret n)}
    (hE : E ⊆ Hof (hidden n sp p₂ Xc dT eB)) :
    FRAME_W_hyp D (frameValue c / (n : ℝ)) E := by
  apply frame_of_hid D (G := hidden n sp p₂ Xc dT eB) _ hE
  intro θ hθ w
  rw [hD]
  exact computed_frame hn hsp hp₂ hXc hdT0 hdT c hθ w

end BstLean.Part227
#print axioms BstLean.Part227.computed_frame
#print axioms BstLean.Part227.retained_frame
