import BstLean.Part278Assemble

/-!
# Part 278 (O3 + O4): the odd root is below `10⁻²⁰` (conditional on three retained-data bounds)

* `passF_le`: `|f̃_g| ≤ √(8O²Q + 16Q)/√n` from the operator bound `O` of `A₂` and `Q`.
* `num_core`: the scalar certificate.
* **`odd_root_lt`**: for odd `n ≥ 8001`, if `A₂` has operator bound `3` (`OpB (A2 c) 3`), if
  `Σ_i a_i(s_g)² ≤ 16 n³` at every node `s_g`, `e_b > 0` and `|c_A|² ≤ 2 e_b χ` with `0 ≤ χ ≤ n`
  (the field `hc` of `Part241.PassInputs`), then
  `|√q̃(statedDesign n) − √q̃(paperDesignP n)| ≤ 10⁻²⁰`.

The three bounds are hypotheses here. This part does not prove that the good set of the
chains implies them (see the report).
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part130 (relu normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde)
open BstLean.Part169 (A2 bR Jz OpB a1Bar e1Bar nodeS passF passW paperDesignP eR)
open BstLean.Part272 (vsig2G betaG fPassG statedDesign)

variable {n : ℕ}

/-- The zero moment vectors. -/
noncomputable def z0 : Ret n → ℝ → Fin (mA n) → ℝ := fun _ _ => 0

theorem fPassG_z0 (c : Ret n) (s : ℝ) : fPassG z0 z0 c s = 0 := by
  have hv : vsig2G (z0 (n := n)) z0 c s = 0 := by
    unfold vsig2G z0 normSq
    simp
  have hb : ∀ j, betaG (z0 (n := n)) z0 c s j = 0 := by
    intro j
    unfold betaG
    rw [hv, sqrt_zero]
    have : (A2 c).mulVec (z0 c s) j = 0 := by
      unfold z0; simp
    rw [this]
    simp only [zero_mul, add_zero, relu, max_self]
    exact BstLean.Part150.binMean_const _ 0
  unfold fPassG
  simp [hb]

theorem passF_le (hn : 8001 ≤ n) (hJ : 1 ≤ Jz n) (c : Ret n) {O Q : ℝ} (hO : OpB (A2 c) O)
    (g : ℕ) (hQ : ∑ i, aw c (nodeS c g) i ^ 2 ≤ Q) :
    |passF c g| ≤ √(8 * O ^ 2 * Q + 16 * Q) / √(n : ℝ) := by
  have h := fPassG_pert hJ z0 a1Bar z0 e1Bar c (nodeS c g) hO
  rw [fPassG_z0, sub_zero] at h
  have e1 : passF c g = fPassG a1Bar e1Bar c (nodeS c g) := rfl
  rw [e1]
  refine h.trans (div_le_div_of_nonneg_right (sqrt_le_sqrt ?_) (sqrt_nonneg _))
  have hm0 := mA_pos (n := n) (by omega)
  have hmm : (mA n : ℝ) * (mA n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0.ne'
  have hQg := hQ
  have hA : normSq (a1Bar c (nodeS c g) - z0 c (nodeS c g)) ≤ 4 * Q := by
    have : normSq (a1Bar c (nodeS c g) - z0 c (nodeS c g)) ≤ ∑ i, 4 * aw c (nodeS c g) i ^ 2 := by
      unfold normSq
      refine Finset.sum_le_sum fun i _ => ?_
      have hb := a1Bar_le (by omega) c (nodeS c g) i
      simp only [z0, Pi.sub_apply, Pi.zero_apply, sub_zero]
      rw [← sq_abs (a1Bar c (nodeS c g) i)]
      calc |a1Bar c (nodeS c g) i| ^ 2 ≤ (2 * aw c (nodeS c g) i) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = 4 * aw c (nodeS c g) i ^ 2 := by ring
    rw [← Finset.mul_sum] at this
    linarith
  have hv0 : vsig2G (z0 (n := n)) z0 c (nodeS c g) = 0 := by
    unfold vsig2G z0 normSq
    simp
  have hv : vsig2G a1Bar e1Bar c (nodeS c g) ≤ 2 / (mA n : ℝ) * (4 * Q) := by
    refine (vsig_le (a1Bar c (nodeS c g)) (e1Bar c (nodeS c g))).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : ∑ i, |e1Bar c (nodeS c g) i| ≤ ∑ i, 4 * aw c (nodeS c g) i ^ 2 :=
      Finset.sum_le_sum fun i _ => e1Bar_le (by omega) c (nodeS c g) i
    rw [← Finset.mul_sum] at this
    linarith
  rw [hv0, sub_zero, abs_of_nonneg (le_max_left _ _)]
  have hO2 : 0 ≤ O ^ 2 := sq_nonneg O
  have h1 := mul_le_mul_of_nonneg_left hA hO2
  have h2 := mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ) ≤ 2 * (mA n : ℝ))
  have e2 : 2 * (mA n : ℝ) * (2 / (mA n : ℝ) * (4 * Q)) = 16 * Q := by
    calc _ = 16 * Q * ((mA n : ℝ) * (mA n : ℝ)⁻¹) := by ring
      _ = _ := by rw [hmm, mul_one]
  rw [e2] at h2
  nlinarith

/-- The scalar certificate. -/
theorem num_core {nn e X Y F χ : ℝ} (hn : 1 ≤ nn) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hen : e * nn ^ 5 ≤ 1 / 10 ^ 90) (hX0 : 0 ≤ X) (hX2 : X ^ 2 ≤ 800 * e * nn ^ 3)
    (hY0 : 0 ≤ Y) (hY2 : Y ^ 2 ≤ 8896 * nn ^ 3) (hF0 : 0 ≤ F) (hF2 : F ^ 2 ≤ 1408 * nn ^ 2)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ nn) :
    5 * (X * Y / nn + X / √nn * (2 * F + X / √nn)) ≤ 1 / 2 ∧
    nn * (5 * (X * Y / nn + X / √nn * (2 * F + X / √nn))) ^ 2 + 5 / 2 * χ * X ^ 2 ≤
      1 / 10 ^ 40 := by
  have hn0 : 0 < nn := by linarith
  have hs2 : √nn ^ 2 = nn := sq_sqrt hn0.le
  have hn4 : e * nn ^ 4 ≤ 1 / 10 ^ 90 := by
    have h4 : nn ^ 4 ≤ nn ^ 5 := pow_le_pow_right₀ hn (by norm_num)
    have := mul_le_mul_of_nonneg_left h4 he0
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = X * Y / nn := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = X / √nn * (2 * F) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (X / √nn) ^ 2 := ⟨_, rfl⟩
  have hS : X * Y / nn + X / √nn * (2 * F + X / √nn) = a + b + c := by
    rw [ha, hb, hc]; ring
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (mul_nonneg hX0 hY0) hn0.le
  have hb0 : 0 ≤ b := by
    rw [hb]; exact mul_nonneg (div_nonneg hX0 (sqrt_nonneg _)) (mul_nonneg (by norm_num) hF0)
  have hc0 : 0 ≤ c := by rw [hc]; exact sq_nonneg _
  have hP : 0 ≤ 800 * e * nn ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) he0) (pow_nonneg hn0.le 3)
  have hXY : X ^ 2 * Y ^ 2 ≤ (800 * e * nn ^ 3) * (8896 * nn ^ 3) :=
    mul_le_mul hX2 hY2 (sq_nonneg _) hP
  have hXF : X ^ 2 * F ^ 2 ≤ (800 * e * nn ^ 3) * (1408 * nn ^ 2) :=
    mul_le_mul hX2 hF2 (sq_nonneg _) hP
  have hXX : X ^ 2 * X ^ 2 ≤ (800 * e * nn ^ 3) * (800 * e * nn ^ 3) :=
    mul_le_mul hX2 hX2 (sq_nonneg _) hP
  have hnn2 : 0 < nn ^ 2 := pow_pos hn0 2
  have ha2 : a ^ 2 ≤ 7116800 * (e * nn ^ 4) := by
    rw [ha, div_pow, mul_pow, div_le_iff₀ hnn2]
    have e1 : (800 * e * nn ^ 3) * (8896 * nn ^ 3) = 7116800 * (e * nn ^ 4) * nn ^ 2 := by ring
    linarith
  have hb2 : b ^ 2 ≤ 4505600 * (e * nn ^ 4) := by
    rw [hb, mul_pow, div_pow, hs2]
    rw [show (X ^ 2 / nn) * (2 * F) ^ 2 = 4 * (X ^ 2 * F ^ 2) / nn by ring,
      div_le_iff₀ hn0]
    have e1 : 4 * ((800 * e * nn ^ 3) * (1408 * nn ^ 2)) = 4505600 * (e * nn ^ 4) * nn := by ring
    linarith
  have hc2 : c ^ 2 ≤ 640000 * (e * nn ^ 4) := by
    rw [hc, div_pow, hs2, div_pow, div_le_iff₀ hnn2]
    have h1 : e * e ≤ e := by
      have := mul_le_mul_of_nonneg_left he1 he0
      linarith
    have h2 : 0 ≤ nn ^ 6 := pow_nonneg hn0.le 6
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    have e1 : (800 * e * nn ^ 3) * (800 * e * nn ^ 3) = 640000 * (e * e * nn ^ 6) := by ring
    have e2 : 640000 * (e * nn ^ 4) * nn ^ 2 = 640000 * (e * nn ^ 6) := by ring
    have e3 : (X ^ 2) ^ 2 = X ^ 2 * X ^ 2 := by ring
    rw [e3, e2]
    linarith
  have hsq3 : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hS2 : (a + b + c) ^ 2 ≤ 36787200 * (e * nn ^ 4) := by linarith
  have hS100 : (a + b + c) ^ 2 ≤ (1 / 10) ^ 2 := by
    have : 36787200 * (e * nn ^ 4) ≤ 36787200 * (1 / 10 ^ 90) :=
      mul_le_mul_of_nonneg_left hn4 (by norm_num)
    have h2 : (36787200 : ℝ) * (1 / 10 ^ 90) ≤ (1 / 10) ^ 2 := by norm_num
    linarith
  have hSle : a + b + c ≤ 1 / 10 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hS100
  rw [hS]
  refine ⟨by linarith, ?_⟩
  have h5 : nn * (5 * (a + b + c)) ^ 2 ≤ 25 * 36787200 * (e * nn ^ 5) := by
    have h := mul_le_mul_of_nonneg_left hS2 hn0.le
    have e1 : nn * (5 * (a + b + c)) ^ 2 = 25 * (nn * (a + b + c) ^ 2) := by ring
    have e2 : nn * (36787200 * (e * nn ^ 4)) = 36787200 * (e * nn ^ 5) := by ring
    rw [e1]
    linarith
  have h6 : 5 / 2 * χ * X ^ 2 ≤ 2000 * (e * nn ^ 4) := by
    have h := mul_le_mul hχ hX2 (sq_nonneg _) hn0.le
    have e1 : nn * (800 * e * nn ^ 3) = 800 * (e * nn ^ 4) := by ring
    have e2 : 5 / 2 * χ * X ^ 2 = 5 / 2 * (χ * X ^ 2) := by ring
    rw [e2]
    linarith
  have h7 : (25 * 36787200 : ℝ) * (1 / 10 ^ 90) + 2000 * (1 / 10 ^ 90) ≤ 1 / 10 ^ 40 := by
    norm_num
  have h8 := mul_le_mul_of_nonneg_left hen (by norm_num : (0:ℝ) ≤ 25 * 36787200)
  have h9 := mul_le_mul_of_nonneg_left hn4 (by norm_num : (0:ℝ) ≤ 2000)
  linarith

theorem epsO_le_one (hn : 1 ≤ n) : epsO n ≤ 1 := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have : (n:ℝ) ^ (-10:ℝ) ≤ 1 := by
    rw [rpow_neg_ten]; exact div_le_one_of_le₀ (one_le_pow₀ h1) (by positivity)
  unfold epsO
  nlinarith [rpow_nonneg (Nat.cast_nonneg n) (-10:ℝ)]

theorem epsO_n5 (hn : 1 ≤ n) : epsO n * (n : ℝ) ^ 5 ≤ 1 / 10 ^ 90 := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h5 : (1:ℝ) ≤ (n:ℝ) ^ 5 := one_le_pow₀ h1
  unfold epsO
  rw [rpow_neg_ten, show (1:ℝ) / 10 ^ 90 * (1 / (n:ℝ) ^ 10) * (n:ℝ) ^ 5 =
    1 / 10 ^ 90 * (1 / (n:ℝ) ^ 5) by field_simp]
  have : 1 / (n:ℝ) ^ 5 ≤ 1 := div_le_one_of_le₀ h5 (by positivity)
  nlinarith

/-- The three square roots of the certificate, at `O = 3`, `Q = 16n³`. -/
noncomputable def XX (n : ℕ) : ℝ :=
  √(2 * ((3:ℝ) ^ 2 * (epsO n ^ 2 * (16 * (n:ℝ) ^ 3))) +
    4 * (epsO n * (7 + epsO n) * (16 * (n:ℝ) ^ 3)))
noncomputable def YY (n : ℕ) : ℝ :=
  √(52 * ((3:ℝ) ^ 2 * (16 * (n:ℝ) ^ 3)) + 8 * ((8 + 3 * epsO n) * (16 * (n:ℝ) ^ 3)))
noncomputable def FF (n : ℕ) : ℝ :=
  √(8 * (3:ℝ) ^ 2 * (16 * (n:ℝ) ^ 3) + 16 * (16 * (n:ℝ) ^ 3)) / √(n : ℝ)

/-- **O3 + O4: the odd root is below `10⁻²⁰`** under three bounds on the retained data. -/
theorem odd_root_lt (hn : 8001 ≤ n) (ho : Odd n) (hJ : 1 ≤ Jz n) (t : ℝ) (c : Ret n)
    {χ : ℝ} (hO : OpB (A2 c) 3)
    (hQ : ∀ g, g ≤ BstLean.Part157.Js n - 1 → ∑ i, aw c (nodeS c g) i ^ 2 ≤ 16 * (n : ℝ) ^ 3)
    (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ) (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0:ℝ) < n := by linarith
  have he0 : 0 ≤ epsO n := by unfold epsO; positivity
  have he1 := epsO_le_one (n := n) (by omega)
  have hen := epsO_n5 (n := n) (by omega)
  have hn3 : (0:ℝ) ≤ (n:ℝ) ^ 3 := by positivity
  have hX2 : XX n ^ 2 ≤ 800 * epsO n * (n:ℝ) ^ 3 := by
    unfold XX
    rw [sq_sqrt (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 he0) hn3,
      mul_nonneg (mul_nonneg he0 he0) hn3, mul_nonneg he0 hn3]
  have hY2 : YY n ^ 2 ≤ 8896 * (n:ℝ) ^ 3 := by
    unfold YY
    rw [sq_sqrt (by positivity)]
    nlinarith [mul_nonneg he0 hn3, mul_le_mul_of_nonneg_right he1 hn3]
  have hF2 : FF n ^ 2 ≤ 1408 * (n:ℝ) ^ 2 := by
    unfold FF
    rw [div_pow, sq_sqrt (by positivity), sq_sqrt hn0.le, div_le_iff₀ hn0]
    nlinarith
  obtain ⟨hδ, hR⟩ := num_core (X := XX n) (Y := YY n) (F := FF n) hn1 he0 he1 hen
    (sqrt_nonneg _) hX2 (sqrt_nonneg _) hY2
    (div_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) hF2 hχ0 hχ
  have hFg : ∀ g, g ≤ BstLean.Part157.Js n - 1 → |passF c g| ≤ FF n :=
    fun g hg => passF_le hn hJ c hO g (hQ g hg)
  have h := odd_root_cond hn ho hJ t c hO hQ hFg hδ
  refine h.trans ?_
  have hsq : (1:ℝ) / 10 ^ 20 = √(1 / 10 ^ 40) := by
    rw [show (1:ℝ) / 10 ^ 40 = (1 / 10 ^ 20) ^ 2 by norm_num, sqrt_sq (by norm_num)]
  rw [hsq]
  apply sqrt_le_sqrt
  show (n:ℝ) * (5 * (XX n * YY n / (n:ℝ) + XX n / √(n:ℝ) * (2 * FF n + XX n / √(n:ℝ)))) ^ 2 +
      (XX n / √(n:ℝ) / √(normSq (bR c) / (n : ℝ))) ^ 2 * normSq c.2.1.2 /
        (2 * (2 / (n : ℝ) * (1 / 5))) ≤ 1 / 10 ^ 40
  have hb0 : 0 < normSq (bR c) / (n : ℝ) := he
  have eR_eq : eR c = normSq (bR c) / (n : ℝ) := rfl
  have hT : (XX n / √(n:ℝ) / √(normSq (bR c) / (n : ℝ))) ^ 2 * normSq c.2.1.2 /
      (2 * (2 / (n : ℝ) * (1 / 5))) ≤ 5 / 2 * χ * XX n ^ 2 := by
    rw [div_pow, div_pow, sq_sqrt hn0.le, sq_sqrt hb0.le, ← eR_eq]
    have hc' : normSq c.2.1.2 ≤ 2 * eR c * χ := by
      have : 2 / (n : ℝ) * eR c * n * χ = 2 * eR c * χ := by field_simp
      linarith
    have e1 : XX n ^ 2 / (n:ℝ) / eR c * normSq c.2.1.2 / (2 * (2 / (n : ℝ) * (1 / 5))) =
        5 / 4 * (XX n ^ 2 * normSq c.2.1.2) / eR c := by
      field_simp
      ring
    rw [e1, div_le_iff₀ he]
    have := mul_le_mul_of_nonneg_left hc' (sq_nonneg (XX n))
    nlinarith
  linarith

end BstLean.Part278
