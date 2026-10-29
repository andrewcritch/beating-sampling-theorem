import BstLean.Part236Regularization
import BstLean.Part227Frame

/-! RF re-instantiates the computed-centre frame on the fixed base event. -/
namespace BstLean.Part236
open MeasureTheory Real Set
open BstLean.Part29 (uniformSphere)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 BstLean.Part137 BstLean.Part140 BstLean.Part157 BstLean.Part159
open BstLean.Part227

noncomputable def coeffK {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (e : ℝ) : ℝ := (1 + e) * c.k0 / c.s
noncomputable def coeffD {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (e : ℝ) : ℝ :=
  (1 + e) * (2235 / 100) * c.r0 / ((n : ℝ) * c.ε₁ ^ 2)
noncomputable def frameBase {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (e d : ℝ) : ℝ :=
  (3017 / 20000 + (138 / 1000) / (2 * (n : ℝ)) +
    (1 / 1000) * (17321 / 20000) + (2 / 5) * c.k6 + centreDistance n Xc) / c.s +
    centreFluctuation n dT / c.ε₂ ^ 2 + coeffK c e * √d + coeffD c e * d
noncomputable def frameError {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (e : ℝ) (θ : WHid n) : ℝ :=
  coeffK c e * √(yK θ) + coeffD c e * yD θ

lemma coeffK_nonneg {n : ℕ} {sp p₂ Xc dT eB e : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (he : 0 < e) : 0 ≤ coeffK c e := by
  exact div_nonneg (mul_nonneg (by linarith) c.k0_nonneg) c.s_pos.le

lemma coeffD_nonneg {n : ℕ} {sp p₂ Xc dT eB e : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (he : 0 < e) : 0 ≤ coeffD c e := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by norm_num)) c.r0_nonneg)
    (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg c.ε₁))

theorem regular_formula_bound {n : ℕ} (hn : 4096 ≤ n) {sp p₂ Xc dT eB e d : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (he : 0 < e) (hd : 0 < d) (θ : WHid n) :
    frameFormula n (regularSp e d (yK θ)) (regularP e d (yD θ))
      Xc dT eB c.r0 c.k0 c.k6 c.ε₁ c.ε₂ c.s ≤ frameBase c e d + frameError c e θ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk : 0 ≤ coeffK c e := coeffK_nonneg c he
  have hD : 0 ≤ coeffD c e := coeffD_nonneg c he
  have hkb := mul_le_mul_of_nonneg_left (sqrt_max_le (yK_nonneg θ) hd.le) hk
  have hdb := mul_le_mul_of_nonneg_left (max_le_add (yD_nonneg θ) hd.le) hD
  have hEq : frameFormula n (regularSp e d (yK θ)) (regularP e d (yD θ))
      Xc dT eB c.r0 c.k0 c.k6 c.ε₁ c.ε₂ c.s =
      (3017 / 20000 + (138 / 1000) / (2 * (n : ℝ)) +
        (1 / 1000) * (17321 / 20000) + (2 / 5) * c.k6 + centreDistance n Xc) / c.s +
        centreFluctuation n dT / c.ε₂ ^ 2 +
        coeffK c e * √(max (yK θ) d) + coeffD c e * max (yD θ) d := by
    unfold frameFormula
    rw [show c.k0 / regularSp e d (yK θ) = c.k0 * (1 / regularSp e d (yK θ)) by ring,
      regularSp_price]
    rw [show (2235 / 100) * c.r0 / ((n : ℝ) * regularP e d (yD θ) * c.ε₁ ^ 2) =
      ((2235 / 100) * c.r0 / ((n : ℝ) * c.ε₁ ^ 2)) * (1 / regularP e d (yD θ)) by ring,
      regularP_price]
    unfold coeffK coeffD
    ring
  rw [hEq]
  unfold frameBase frameError
  linarith

/-- The fixed base event supplies centre premises; random thresholds supply only goodHid. -/
theorem pointwise_frame {n : ℕ} (hn : 4096 ≤ n) {Xc dT eB e d : ℝ}
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 ≤ dT) (hdT : dT ≤ 1 / 400000)
    (c : FrameCertificate n (4 / 100) (4 / 10000) Xc dT eB)
    (he : 0 < e) (hd : 0 < d) {θ : WHid n}
    (hθ : θ ∈ hidden n (4 / 100) (4 / 10000) Xc dT eB) (w : Fin (mW n) → ℝ) :
    (∫ u, (∑ j, eDir (bWp θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n)) ≤
      (frameBase c e d + frameError c e θ) / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hS := hθ.1.1.2
  have hA := hθ.1.2
  have hB := hθ.2
  have hp := hidden_subset_GPap (le_refl _) (le_refl _) hXc hdT hθ
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
    have heq : (mW n : ℝ) / (2 * (n : ℝ)) *
        ((n : ℝ) * (2 / (mW n : ℝ) * normSq (bWp θ))) = normSq (bWp θ) := by field_simp
    rw [heq] at h
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  obtain ⟨hk1, hk2⟩ := BstLean.Part140.kap1_window hn
  have hsle : c.s ≤ 1 - c.ε₁ - (kap1 (2 * n) + c.ε₂) ^ 2 / centreLower n eB := by
    have hk : (kap1 (2 * n) + c.ε₂) ^ 2 ≤ (4938 / 10000 + c.ε₂) ^ 2 :=
      pow_le_pow_left₀ (by linarith [c.ε₂_pos]) (by linarith) 2
    have h := div_le_div_of_nonneg_right hk hβpos.le
    linarith [c.denominator]
  obtain ⟨bq, hb0, hb1, hmodel⟩ := kk_three
  apply frameB_num (n := n) (n0 := n) hn le_rfl (b := bq)
    (c2 := 138 / 1000) (η := 1 / 1000) (K₃ := 2 / 5)
    (r0 := c.r0) (k0 := c.k0) (k6 := c.k6)
    (sp := regularSp e d (yK θ)) (p₂ := regularP e d (yD θ))
    (ε₁ := c.ε₁) (ε₂ := c.ε₂) (s := c.s)
    (D0 := c.k0 / regularSp e d (yK θ) + (1 / 1000) * (17321 / 20000) + (2 / 5) * c.k6)
    (ξ₀ := centreDistance n Xc) (a := kap1 (2 * n))
    (dT := centreFluctuation n dT) (β := centreLower n eB)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    c.r0_nonneg c.radius c.k0_nonneg c.kernel c.k6_nonneg c.sixth
    (regularSp_pos he hd) (regularP_pos he hd) c.ε₁_pos c.ε₂_pos rfl
    (sq_nonneg _) (by linarith) hβpos c.s_pos hsle
    _ (regular_goodHid hn he hd θ) hξ hX hβb w
  exact regular_formula_bound hn c he hd θ
end BstLean.Part236
