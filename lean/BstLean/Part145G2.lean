import BstLean.Part145G1

/-!
# Part 145 (abstract good hidden event), file 2: the Part 141 lemmas

`goodAG G`, `goodWAG G`, `errSAG G k`: `goodA n`, `goodWA n`, `errSA k n` of Part 141 with an
abstract good hidden event `G` in the place of `goodHat n`. This file makes again the lemmas of
`Part141Tau`, `Part141Err`, `Part141Final`, `Part141Sample` and `Part141Prog` that read the
event. **`badAG_prob_gen`**, **`zeroPtAG_null`**. The proofs are those of the sources.
Do not use `sorry`, `native_decide` or `axiom`.
-/

-- ===== from Part141Tau =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part138 BstLean.Part140

/-- The good hidden event of the arithmetic centre for an abstract good hidden event `G`:
`G`, and `t|b̃ − b̂|² ≤ γ/10⁶`. -/
def goodAG {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) : Set (HidParam (2 * n) (mW n)) :=
  G ∩ {θ | Part141.dA n θ ≤ 2 / ((2 * n : ℕ) : ℝ) / 1000000}

lemma goodAG_meas {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) : MeasurableSet (goodAG G) :=
  (hG.meas).inter (measurableSet_le (measurable_dA hn) measurable_const)

/-- `Pr(goodAG n fails) ≤ p + 68·10⁶/(qA n)²` if `Pr(G fails) ≤ p`. -/
theorem goodAG_prob_gen {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hn : 4096 ≤ n) {p : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (hidGauss (2 * n) (mW n)).real (goodAG G)ᶜ ≤ p + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  set P := hidGauss (2 * n) (mW n) with hP
  obtain ⟨hi, hb⟩ := centreArith141 hn
  set x₀ : ℝ := 2 / ((2 * n : ℕ) : ℝ) / 1000000 with hx₀
  have hx₀0 : 0 < x₀ := by rw [hx₀]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := Part141.dA n)
    (Filter.Eventually.of_forall (dA_nonneg n)) hi x₀
  have h2 : P.real {θ | x₀ ≤ Part141.dA n θ} ≤ 68000000 / (qA n : ℝ) ^ 2 := by
    have h3 : x₀ * P.real {θ | x₀ ≤ Part141.dA n θ} ≤ 2 / ((2 * n : ℕ) : ℝ) * (68 / (qA n : ℝ) ^ 2)
        :=
      hmk.trans hb
    have e : 2 / ((2 * n : ℕ) : ℝ) * (68 / (qA n : ℝ) ^ 2) =
        x₀ * (68000000 / (qA n : ℝ) ^ 2) := by
      rw [hx₀]; field_simp; ring
    rw [e] at h3
    exact le_of_mul_le_mul_left h3 hx₀0
  have hsub : (goodAG G)ᶜ ⊆ Gᶜ ∪ {θ | x₀ ≤ Part141.dA n θ} := by
    intro θ hθ
    by_cases hg : θ ∈ G
    · right
      by_contra hc
      exact hθ ⟨hg, (le_of_lt (not_le.mp hc) : Part141.dA n θ ≤ x₀)⟩
    · exact Or.inl hg
  calc P.real (goodAG G)ᶜ ≤ P.real (Gᶜ ∪ {θ | x₀ ≤ Part141.dA n θ}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real Gᶜ + P.real {θ | x₀ ≤ Part141.dA n θ} := measureReal_union_le _ _
    _ ≤ _ := add_le_add h1 h2

section good

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodAG G)

include hG hn hθ

/-- On `goodAG n`, with `γ = 2/N`: `τ̂₀² ≥ 0.46·γ`, `τ̃₀² ≥ 0.458·γ` and
`(τ̃₀² − τ̂₀²)² ≤ γ²·(42·t|b̃ − b̂|²/γ + 3/(qA n)²)`. -/
theorem scalarAG :
    2 / ((2 * n : ℕ) : ℝ) * (46 / 100) ≤ tauHat (2 * n) (mW n) θ ^ 2 ∧
    2 / ((2 * n : ℕ) : ℝ) * (458 / 1000) ≤ tauA n θ ^ 2 ∧
    (tauA n θ ^ 2 - tauHat (2 * n) (mW n) θ ^ 2) ^ 2 ≤
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 *
        (42 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 3 * (1 / (qA n : ℝ)) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγd, hNcast, div_le_one (by positivity)]
    linarith
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have hqR : (40960000 : ℝ) ≤ qA n := by rw [qA_cast]; linarith
  obtain ⟨hB1, hB2⟩ := BhG_hat hG hθ.1
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  have hdle : Part141.dA n θ ≤ γ / 1000000 := hθ.2
  have hd0 := dA_nonneg n θ
  set B : ℝ := Bh (2 * n) (mW n) θ with hBd
  set B' : ℝ := 2 / (mW n : ℝ) * normSq (bA n θ) with hB'd
  set c : ℝ := c1Hat (2 * n) with hcd
  set c' : ℝ := ((c1A n : ℚ) : ℝ) with hc'd
  have hB'0 : 0 ≤ B' := mul_nonneg (by positivity) (normSq_nonneg _)
  -- the squares of the two scalars
  have eT : tauHat (2 * n) (mW n) θ ^ 2 = B * relu (B * c - 1) := by
    rw [← tauOf_bhat]
    unfold tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
    rfl
  have eT' : tauA n θ ^ 2 = B' * relu (B' * c' - 1) := by
    unfold tauA tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
  -- normalized units
  have hκ : γ * c = 1 / kap1 (2 * n) ^ 2 := by
    rw [hcd]
    unfold c1Hat
    rw [← hγd]
    field_simp
  have hksq1 : (49372 / 100000 : ℝ) ^ 2 ≤ kap1 (2 * n) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hk1 2
  have hksq2 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hk2 2
  have hkpos : (0 : ℝ) < kap1 (2 * n) ^ 2 := by nlinarith
  have hκ1 : 4101 / 1000 ≤ γ * c := by
    rw [hκ, le_div_iff₀ hkpos]
    nlinarith
  have hκ2 : γ * c ≤ 41025 / 10000 := by
    rw [hκ, div_le_iff₀ hkpos]
    nlinarith
  have hcerr : |γ * c' - γ * c| ≤ 1 / (qA n : ℝ) * (γ * c) := by
    rw [← mul_sub, abs_mul, abs_of_pos hγ]
    have h1 := c1A_err hn1
    have h2 : γ * |c' - c| ≤ 1 * (1 / (qA n : ℝ)) :=
      mul_le_mul hγ1 h1 (abs_nonneg _) (by norm_num)
    have h3 : (1 : ℝ) / (qA n : ℝ) * 1 ≤ 1 / (qA n : ℝ) * (γ * c) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hdiff : (B' - B) ^ 2 ≤ 2 * Part141.dA n θ * (B' + B) := by
    have h := normSq_diff_sq (bA n θ) (bhat θ)
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (2 / (mW n : ℝ)) ^ 2)
    have e1 : (B' - B) ^ 2 = (2 / (mW n : ℝ)) ^ 2 * (normSq (bA n θ) - normSq (bhat θ)) ^ 2 := by
      rw [hB'd, hBd]; unfold Bh; ring
    have e2 : 2 * Part141.dA n θ * (B' + B) = (2 / (mW n : ℝ)) ^ 2 *
        (2 * normSq (bA n θ - bhat θ) * (normSq (bA n θ) + normSq (bhat θ))) := by
      rw [hB'd, hBd]; unfold Bh Part141.dA; ring
    rw [e1, e2]
    exact h2
  have hN := tauN (β := B / γ) (β' := B' / γ) (κ := γ * c) (κ' := γ * c') (ξ := Part141.dA n θ / γ)
    (e := 1 / (qA n : ℝ))
    (by rw [le_div_iff₀ hγ]; linarith) (by rw [div_le_iff₀ hγ]; linarith) (by positivity)
    (by positivity) (by rw [div_le_iff₀ hγ]; linarith)
    (by
      have e1 : (B' / γ - B / γ) ^ 2 = (B' - B) ^ 2 / γ ^ 2 := by field_simp
      have e2 : 2 * (Part141.dA n θ / γ) * (B' / γ + B / γ) = 2 * Part141.dA n θ * (B' + B) / γ ^ 2
          := by
        field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hdiff (by positivity))
    hκ1 hκ2 hcerr (by positivity)
    (by rw [div_le_div_iff₀ hq' (by norm_num)]; linarith)
  have eN : B / γ * (γ * c) = B * c := by field_simp
  have eN' : B' / γ * (γ * c') = B' * c' := by field_simp
  rw [eN, eN'] at hN
  obtain ⟨hN1, hN2, hN3⟩ := hN
  rw [eT, eT']
  have ea : B * relu (B * c - 1) = γ * (B / γ * relu (B * c - 1)) := by field_simp
  have eb : B' * relu (B' * c' - 1) = γ * (B' / γ * relu (B' * c' - 1)) := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [ea]; exact mul_le_mul_of_nonneg_left hN1 hγ.le
  · rw [eb]; exact mul_le_mul_of_nonneg_left hN2 hγ.le
  · rw [ea, eb, ← mul_sub, mul_pow]
    exact mul_le_mul_of_nonneg_left hN3 (by positivity)

lemma tauAG_pos : 0 < tauA n θ := by
  have h := (scalarAG hG hn hθ).2.1
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have h0 : 0 ≤ tauA n θ := by unfold tauA tauOf; exact Real.sqrt_nonneg _
  have hsq : 0 < tauA n θ ^ 2 := by nlinarith
  exact lt_of_le_of_ne h0 (fun h => by rw [← h] at hsq; norm_num at hsq)

/-- **The Hellinger price of the arithmetic centre and scalar.** On `goodAG n`:
`8·hellG n τ̃₀ τ̂₀ + 2n·t|b̃ − b̂|²/τ̃₀² ≤ n·(404·t|b̃ − b̂|²/γ + 29/(qA n)²)`. -/
theorem KAG_le :
    8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ) +
        2 * (n : ℝ) * Part141.dA n θ / tauA n θ ^ 2 ≤
      (n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  obtain ⟨h1, h2, h3⟩ := scalarAG hG hn hθ
  rw [← hγd] at h1 h2 h3
  have ha := tauAG_pos hG hn hθ
  have hb := tauHatG_pos hG hn hθ.1
  have hd0 := dA_nonneg n θ
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set T' : ℝ := a ^ 2 / γ with hT'
  set T : ℝ := b ^ 2 / γ with hT
  set ξ : ℝ := Part141.dA n θ / γ with hξ
  have hTl : 46 / 100 ≤ T := by rw [hT, le_div_iff₀ hγ]; linarith
  have hT'l : 458 / 1000 ≤ T' := by rw [hT', le_div_iff₀ hγ]; linarith
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hD : (T' - T) ^ 2 ≤ 42 * ξ + 3 * (1 / (qA n : ℝ)) ^ 2 := by
    have e : (T' - T) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 / γ ^ 2 := by rw [hT', hT]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hK := K_num hTl hT'l hξ0 hD
  have hH := hellG_le (n := n) (by omega) ha.le hb
  have hF := hell_frac ha.le hb
  have e1 : (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2 = (T' - T) ^ 2 / (T' + T) ^ 2 := by
    rw [hT', hT]; field_simp
  have e2 : 2 * (n : ℝ) * Part141.dA n θ / a ^ 2 = (n : ℝ) * (2 * ξ / T') := by
    rw [hT', hξ]; field_simp
  have hH2 : hellG n a b ≤ (n : ℝ) * ((T' - T) ^ 2 / (T' + T) ^ 2) := by
    rw [← e1]
    refine hH.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hF hnpos.le
  rw [e2]
  have := mul_le_mul_of_nonneg_left hK hnpos.le
  nlinarith

end good

end BstLean.Part145

-- ===== from Part141Err =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

section fixed

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodAG G)

include hG hn hθ

/-- For fixed `(M₁, M₂) ∈ goodAG n` and fixed `M₃`: the mean over `(A, F)` of `(g̃ − ĝ)²`. -/
lemma diffFixedMG (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal ((2 * (normSq (M₃.mulVec (bA n θ - bhat θ)) / tauA n θ ^ 2) +
      8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ)) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have ha := tauAG_pos hG hn hθ
  have hb := tauHatG_pos hG hn hθ.1
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set c : Fin n → ℝ := M₃.mulVec (bhat θ) with hc
  set c' : Fin n → ℝ := M₃.mulVec (bA n θ) with hc'
  have hcc : c' - c = M₃.mulVec (bA n θ - bhat θ) := by
    rw [hc, hc', Matrix.mulVec_sub]
  set w : ℝ := normSq (c' - c) / a ^ 2 with hw
  have hw0 : 0 ≤ w := div_nonneg (normSq_nonneg _) (sq_nonneg _)
  set H : ℝ := 4 * hellG n a b with hH
  have hH0 : 0 ≤ H := mul_nonneg (by norm_num) (hellG_nonneg _ _ _)
  set o1 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c' + a • γ with ho1
  set o2 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + a • γ with ho2
  set o3 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + b • γ with ho3
  have mo1 : Measurable o1 := measurable_const.add (measurable_const_smul a)
  have mo2 : Measurable o2 := measurable_const.add (measurable_const_smul a)
  have mo3 : Measurable o3 := measurable_const.add (measurable_const_smul b)
  set P := stdGauss (Fin n) with hP
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ≤
      ENNReal.ofReal w * (Lout P o1 p + Lout P o2 p) +
        ENNReal.ofReal H * (Lout P o2 p + Lout P o3 p) := by
    rintro ⟨A, F⟩
    have h := diff_pt hn1 c c' ha hb A F
    have i1 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c' a := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c a := integral_nonneg fun _ => sq_nonneg _
    have i3 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c b := integral_nonneg fun _ => sq_nonneg _
    rw [← sqInt_cheapIn hn1 c' a A F, ← sqInt_cheapIn hn1 c a A F, ← sqInt_cheapIn hn1 c b A F,
      ← ENNReal.ofReal_add i1 i2, ← ENNReal.ofReal_add i2 i3,
      ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
      ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg i1 i2))
        (mul_nonneg hH0 (add_nonneg i2 i3))]
    refine ENNReal.ofReal_le_ofReal ?_
    exact h
  refine (lintegral_mono key).trans (le_of_eq ?_)
  have m1 := measurable_Lout (mA := mA n) (mF := mF n) P mo1
  have m2 := measurable_Lout (mA := mA n) (mF := mF n) P mo2
  have m3 := measurable_Lout (mA := mA n) (mF := mF n) P mo3
  have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have m12 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o1 p + Lout P o2 p) := m1.add m2
  have m23 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o2 p + Lout P o3 p) := m2.add m3
  have hA : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o1 p + Lout P o2 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m1, lintegral_Lout P hn1 hmA hmF mo1,
      lintegral_Lout P hn1 hmA hmF mo2]
  have hB : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o2 p + Lout P o3 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m2, lintegral_Lout P hn1 hmA hmF mo2,
      lintegral_Lout P hn1 hmA hmF mo3]
  rw [lintegral_add_left (m12.const_mul (ENNReal.ofReal w)), lintegral_const_mul _ m12,
    lintegral_const_mul _ m23, hA, hB]
  rw [← ENNReal.ofReal_add h4 h4, ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
    ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg h4 h4))
      (mul_nonneg hH0 (add_nonneg h4 h4))]
  congr 1
  rw [hw, hH, hcc]
  ring

/-- **For fixed `(M₁, M₂) ∈ goodAG n`**: `E_{M₃} E_{A,F} (g̃ − ĝ)² ≤
`n·(404·t|b̃ − b̂|²/γ + 29/q²)·(4/n)`. -/
theorem diffFixedAG :
    ∫⁻ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
        ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
      ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
    ENNReal.ofReal ((n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) +
      29 * (1 / (qA n : ℝ)) ^ 2) * (4 / (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have ha := tauAG_pos hG hn hθ
  set a : ℝ := tauA n θ with had
  set Hh : ℝ := hellG n a (tauHat (2 * n) (mW n) θ) with hHh
  have hH0 : 0 ≤ Hh := hellG_nonneg _ _ _
  set d : Fin (mW n) → ℝ := bA n θ - bhat θ with hd
  obtain ⟨li, le⟩ := layer_sq (m := n) (k := mW n) (v := 2 / (mW n : ℝ)) (by positivity) d
  set f : Matrix (Fin n) (Fin (mW n)) ℝ → ℝ := fun M₃ =>
    (2 * (normSq (M₃.mulVec d) / a ^ 2) + 8 * Hh) * (4 / (n : ℝ)) with hf
  have hf0 : ∀ M₃, 0 ≤ f M₃ := fun M₃ => by
    have : 0 ≤ normSq (M₃.mulVec d) / a ^ 2 := div_nonneg (normSq_nonneg _) (sq_nonneg _)
    rw [hf]; positivity
  have hfi : Integrable f (gaussMat n (mW n) (2 / (mW n : ℝ))) := by
    rw [hf]
    exact ((((li.div_const _).const_mul 2).add (integrable_const _)).mul_const _)
  have hfint : ∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ)) =
      (8 * Hh + 2 * (n : ℝ) * Part141.dA n θ / a ^ 2) * (4 / (n : ℝ)) := by
    rw [hf, integral_mul_const, integral_add ((li.div_const _).const_mul 2)
      (integrable_const _), integral_const_mul, integral_div, le]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold Part141.dA
    rw [← hd]
    ring
  calc _ ≤ ∫⁻ M₃, ENNReal.ofReal (f M₃) ∂gaussMat n (mW n) (2 / (mW n : ℝ)) :=
        lintegral_mono fun M₃ => diffFixedMG hG hn hθ M₃
    _ = ENNReal.ofReal (∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)).symm
    _ ≤ _ := by
        rw [hfint]
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (KAG_le hG hn hθ) (by positivity)

end fixed

/-- The event `goodAG G` as an event of the whole World network. -/
def goodWAG {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) : Set (MlpParam (2 * n) (mW n) n) :=
  {W | (W.1, W.2.1) ∈ goodAG G}

lemma goodWAG_meas {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) : MeasurableSet (goodWAG G) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (goodAG_meas hG hn)

lemma goodWAG_sub {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) :
    goodWAG G ⊆ goodWHG G := fun _ hW => hW.1

/-- `1_good(W)·(g̃ − ĝ)²`, a function of `(W, A, F)`. -/
noncomputable def dGAG {n : ℕ} (G : Set (HidParam (2 * n) (mW n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWAG G).indicator (fun W => (gA W t.2.1 t.2.2 - gHat W t.2.1 t.2.2) ^ 2) t.1

/-- `1_good(W)·(g̃ − B)²`, a function of `(W, A, F)`. -/
noncomputable def errGAG {n : ℕ} (G : Set (HidParam (2 * n) (mW n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWAG G).indicator (fun W => (gA W t.2.1 t.2.2 - Part130.Bn W t.2.1 t.2.2) ^ 2) t.1

lemma dGAG_nonneg {n : ℕ} (G : Set (HidParam (2 * n) (mW n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ dGAG G t := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_dGAG {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) : Measurable (dGAG G) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : dGAG G = ({t | t.1 ∈ goodWAG G} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - gHat t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWAG G) (fun W p => (gA W p.1 p.2 - gHat W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (measurable_gHat hN)).pow_const 2).indicator
    (measurable_fst (goodWAG_meas hG hn))

lemma measurable_errGAG {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) : Measurable (errGAG G) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errGAG G = ({t | t.1 ∈ goodWAG G} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWAG G) (fun W p => (gA W p.1 p.2 - Part130.Bn W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodWAG_meas hG hn))

/-- **The distance of the two estimates, joint over `(W, A, F)`.** For `n ≥ 4096`:
`E_{W,A,F}[1_good(W)·(g̃ − ĝ)²] ≤ pertA n·(4/n)`. -/
theorem diffVecAG_lint {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 4096 ≤ n) :
    ∫⁻ t, ENNReal.ofReal (dGAG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (pertA n * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have mE := goodAG_meas hG (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (dGAG G t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_dGAG hG hn1)
  set Gf : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hGf
  have mGf : Measurable Gf := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, Gf W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mGf MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => Gf (MeasurableEquiv.prodAssoc a))
      (mGf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    (n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) *
      (4 / (n : ℝ)) with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have := dA_nonneg n θ
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    by_cases hθ : θ ∈ goodAG G
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWAG G := fun M₃ => hθ
      have hin : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Gf (θ.1, θ.2, M₃) =
          ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
            ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ∂PAF := by
        intro M₃
        refine lintegral_congr fun p => ?_
        simp only [hf, dGAG, Set.indicator_of_mem (hW M₃)]
      simp_rw [hin]
      exact diffFixedAG hG hn hθ
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWAG G := fun M₃ => hθ
      have hz : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Gf (θ.1, θ.2, M₃) = 0 := by
        intro M₃
        simp only [hGf, hf, dGAG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero,
          lintegral_zero]
      simp_rw [hz]
      simp
  obtain ⟨hdi, hdb⟩ := centreArith141 hn
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := by
    rw [hk]
    exact ((((hdi.div_const _).const_mul 404).add (integrable_const _)).const_mul _).mul_const _
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_mul_const, integral_const_mul,
          integral_add ((hdi.div_const _).const_mul 404) (integrable_const _),
          integral_const_mul, integral_div]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        have h1 : (∫ θ, Part141.dA n θ ∂hidGauss (2 * n) (mW n)) / (2 / ((2 * n : ℕ) : ℝ)) ≤
            68 / (qA n : ℝ) ^ 2 := by
          rw [div_le_iff₀ hγ]
          linarith
        have h2 : (n : ℝ) * (404 * ((∫ θ, Part141.dA n θ ∂hidGauss (2 * n) (mW n)) /
            (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) ≤ pertA n := by
          unfold pertA
          have e1 : 27501 * (n : ℝ) / (qA n : ℝ) ^ 2 =
              (n : ℝ) * (404 * (68 / (qA n : ℝ) ^ 2) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
            field_simp
            ring
          rw [e1]
          exact mul_le_mul_of_nonneg_left (by linarith) hnpos.le
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

end BstLean.Part145

-- ===== from Part141Final =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- The probability that `W` is not in the good hidden event, as an event of `(W, A, F)`, from a
bound for `G`. -/
lemma badAG_prob_gen {n : ℕ} (hn : 4096 ≤ n)
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    {p : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWAG G} ≤ p + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodWAG_meas hG (n := n) hn1
  have hmS := goodAG_meas hG (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWAG G} = (goodWAG G)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
  have e : (goodWAG G)ᶜ =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' (goodAG G)ᶜ := rfl
  have hmap : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) = hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    have h1 : (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) =
        Prod.map id Prod.fst := by
      funext W; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod]
    simp
  have hf : Measurable (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [e, ← map_measureReal_apply hf hmS.compl, hmap]
  exact goodAG_prob_gen hn h1

end BstLean.Part145

-- ===== from Part141Sample =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- `1_good(W)·(g̃_k − B)²`, a function of `((W, A, F), γ)`. -/
noncomputable def errSAG {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) (k : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : ℝ :=
  (goodWAG G).indicator (fun W => (gSampleA k W p.1.2.1 p.1.2.2 p.2 -
    Part130.Bn W p.1.2.1 p.1.2.2) ^ 2) p.1.1

lemma errSAG_nonneg {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) (k : ℕ)
    (p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) : 0 ≤ errSAG G k p :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errSAG {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) (k : ℕ) : Measurable (errSAG G k) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errSAG G k = ({p | p.1.1 ∈ goodWAG G} : Set ((MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ))).indicator
      (fun p => (gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2) := by
    funext p
    by_cases hp : p.1.1 ∈ goodWAG G
    · rw [Set.indicator_of_mem (show p ∈ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWAG G} from hp)]
      unfold errSAG
      rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWAG G} from hp)]
      unfold errSAG
      rw [Set.indicator_of_notMem hp]
  rw [e]
  exact (((measurable_gSampleA k).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).pow_const 2).indicator
    ((measurable_fst.comp measurable_fst) (goodWAG_meas hG hn))

end BstLean.Part145

-- ===== from Part141Prog =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- The event "`W` is good and a point is zero before the normalization" has probability `0`. -/
lemma zeroPtAG_null {n : ℕ} (hn : 4096 ≤ n)
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (k : ℕ) :
    ((mlpTriple 2 n).prod (gamK k n))
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} = 0 := by
  have hn1 : 1 ≤ n := by omega
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have mZ : MeasurableSet Z := by
    have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G} :=
      (measurable_fst.comp measurable_fst) (goodWAG_meas hG hn1)
    have m2 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} := by
      have e : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
          ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} =
          ⋃ i : Fin k, {p | normSq (preA p.1.1 (p.2 i)) = 0} := by
        ext p; simp
      rw [e]
      refine MeasurableSet.iUnion fun i => ?_
      have hm : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => normSq (preA p.1.1 (p.2 i))) :=
        measurable_normSq.comp (measurable_preA.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd)))
      exact hm (measurableSet_singleton 0)
    exact m1.inter m2
  rw [Measure.measure_prod_null mZ]
  refine Filter.Eventually.of_forall fun t => ?_
  change gamK k n (Prod.mk t ⁻¹' Z) = 0
  by_cases hg : t.1 ∈ goodWAG G
  · have hτ : tauWA t.1 ≠ 0 := (tauAG_pos hG hn hg).ne'
    refine measure_mono_null ?_ (preA_null hn1 k t.1 hτ)
    rintro γ ⟨-, h⟩
    exact h
  · have e : Prod.mk t ⁻¹' Z = ∅ := by
      ext γ
      simp only [Set.mem_preimage, hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact absurd h hg
    rw [e]
    simp

end BstLean.Part145

