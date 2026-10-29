import BstLean.Part186RA2
import BstLean.Part185All

/-!
# Part 186 (file `RA3`): the row-averaged bias moments at a node (paper Lemma `t7:p08:RA`)

No proof is left open; no `native_decide` or `axiom` is used.

* `node_biasF_RA`: `biasF⁸ ≤ n⁴(Σ_j q_F(R_j))⁴`, `q_F(R) = c₀ + c₁R + c₂R² ≥ P_F(ρ)²`;
* `node_biasW_RA`: `biasW⁸ ≤ (Σ_j q_W(R_j))⁸`, `q_W(R) ≥ P_W(ρ)`;
  (the radial factors `ρ ≤ (R + a²)/(2a)`, `a = 99/70`, and `ρ³ ≤ R²/4 + R`);
* `node_bulk16`: the nodes of the World window have `s² ≤ 1` for every `n ≥ 16 384`;
* **`biasMomF_RA_of_stat`**, **`biasMomW_RA_of_stat`**: the bias moments on the statistics event
  under the row-averaged numerical conditions.
-/

namespace BstLean.Part186.RA

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW hB tA aLat bOfY windowW mkR BiasMomF BiasMomW opSet)
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part137 (psiS)

variable {n : ℕ}

/-- The radial constant `a = 99/70 ≈ √2`. -/
noncomputable def aa : ℝ := 99 / 70

lemma rho_le {ρ : ℝ} : ρ ≤ (ρ ^ 2 + aa ^ 2) / (2 * aa) := by
  unfold aa; rw [le_div_iff₀ (by norm_num)]; nlinarith [sq_nonneg (ρ - 99 / 70)]

lemma rho3_le {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ * ρ ^ 2 ≤ (ρ ^ 2) ^ 2 / 4 + ρ ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (ρ / 2 - 1))]

/-- The location coefficients. -/
noncomputable def cF0 (A0 A1 _A2 : ℝ) : ℝ := A0 ^ 2 + aa * (A0 * A1)
noncomputable def cF1 (A0 A1 A2 : ℝ) : ℝ := A1 ^ 2 + A0 * A1 / aa + 2 * (A0 * A2) + 2 * (A1 * A2)
noncomputable def cF2 (_A0 A1 A2 : ℝ) : ℝ := A2 ^ 2 + A1 * A2 / 2

/-- The energy coefficients. -/
noncomputable def cW0 (A0 A1 _A2 : ℝ) : ℝ := A0 + A1 * aa / 2
noncomputable def cW1 (_A0 A1 A2 : ℝ) : ℝ := A1 / (2 * aa) + A2

lemma PF_sq_le {A0 A1 A2 ρ : ℝ} (h0 : 0 ≤ A0) (h1 : 0 ≤ A1) (h2 : 0 ≤ A2) (hρ : 0 ≤ ρ) :
    (A0 + A1 * ρ + A2 * ρ ^ 2) ^ 2 ≤ qp (cF0 A0 A1 A2) (cF1 A0 A1 A2) (cF2 A0 A1 A2) (ρ ^ 2) := by
  unfold qp cF0 cF1 cF2
  have r1 := rho_le (ρ := ρ)
  have r3 := rho3_le hρ
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have e1 : 2 * (A0 * A1) * ρ ≤ 2 * (A0 * A1) * ((ρ ^ 2 + aa ^ 2) / (2 * aa)) :=
    mul_le_mul_of_nonneg_left r1 (by positivity)
  have e2 : 2 * (A1 * A2) * (ρ * ρ ^ 2) ≤ 2 * (A1 * A2) * ((ρ ^ 2) ^ 2 / 4 + ρ ^ 2) :=
    mul_le_mul_of_nonneg_left r3 (by positivity)
  have e3 : 2 * (A0 * A1) * ((ρ ^ 2 + aa ^ 2) / (2 * aa)) =
      aa * (A0 * A1) + A0 * A1 / aa * ρ ^ 2 := by field_simp; ring
  nlinarith

lemma PW_le {A0 A1 A2 ρ : ℝ} (h1 : 0 ≤ A1) :
    A0 + A1 * ρ + A2 * ρ ^ 2 ≤ qp (cW0 A0 A1 A2) (cW1 A0 A1 A2) 0 (ρ ^ 2) := by
  unfold qp cW0 cW1
  have r1 := rho_le (ρ := ρ)
  have ha : (0 : ℝ) < aa := by unfold aa; norm_num
  have e1 : A1 * ρ ≤ A1 * ((ρ ^ 2 + aa ^ 2) / (2 * aa)) := mul_le_mul_of_nonneg_left r1 h1
  have e3 : A1 * ((ρ ^ 2 + aa ^ 2) / (2 * aa)) = A1 * aa / 2 + A1 / (2 * aa) * ρ ^ 2 := by
    field_simp; ring
  nlinarith

/-- **The location bias at a node, row-averaged form**: `biasF⁸ ≤ n⁴(Σ_j q_F(R_j))⁴`. -/
theorem node_biasF_RA (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm) :
    biasF c g ξ₁ ξ₂ ^ 8 ≤ (n : ℝ) ^ 4 * (∑ j, qp
      (cF0 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (cF1 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (cF2 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 4 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasF_rows hn c g hs h1]
  set b := bOfY c (M0 c g ξ₁ ξ₂ *ᵥ hB c)
  set x : Fin (mA n) → ℝ := fun j => ∫ v, psiS (√(wT c g v)) ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j)
      ∂stdGauss (Fin (n - 1)) - psiS √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hx
  set P : Fin (mA n) → ℝ := fun j => AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j + AF2 √Smin Dm * rhoJ ξ₁ ξ₂ j ^ 2 with hP
  have hxP : ∀ j, |x j| ≤ P j := by
    intro j
    have R := rowF (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    refine TF_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) hρ hC (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
        mul_le_mul_of_nonneg_right hsum hC
      unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hκ : |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ≤ √(n : ℝ) * √(∑ j, x j ^ 2) := by
    rw [abs_mul]
    have h1' := BstLean.Part130.abs_dot_le b x
    have h2 := BstLean.Part170.kappa_b_le n b
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * |∑ j, b j * x j|
        ≤ |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * (√(normSq b) * √(normSq x)) := by gcongr
      _ = (|(n : ℝ) / (√(n : ℝ) * √(normSq b))| * √(normSq b)) * √(normSq x) := by ring
      _ ≤ √(n : ℝ) * √(normSq x) := by gcongr
      _ = √(n : ℝ) * √(∑ j, x j ^ 2) := rfl
  have hS0 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have step1 : ((n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j) ^ 8 ≤
      (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
    rw [← Even.pow_abs (by decide)]
    calc |(n : ℝ) / (√(n : ℝ) * √(normSq b)) * ∑ j, b j * x j| ^ 8
        ≤ (√(n : ℝ) * √(∑ j, x j ^ 2)) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hκ _
      _ = ((√(n : ℝ)) ^ 2) ^ 4 * ((√(∑ j, x j ^ 2)) ^ 2) ^ 4 := by ring
      _ = (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt hS0]
  have step2 : ∑ j, x j ^ 2 ≤ ∑ j, qp
      (cF0 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (cF1 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (cF2 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm))
      (ξ₁ j ^ 2 + ξ₂ j ^ 2) := by
    gcongr with j
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hq := PF_sq_le hA0 hA1 hA2 hρ
    calc x j ^ 2 = |x j| ^ 2 := (sq_abs _).symm
      _ ≤ P j ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hxP j) 2
      _ ≤ _ := hq
      _ = _ := by rw [rhoJ_sq]
  calc _ ≤ (n : ℝ) ^ 4 * (∑ j, x j ^ 2) ^ 4 := step1
    _ ≤ _ := by gcongr

/-- **The energy bias at a node, row-averaged form**: `biasW⁸ ≤ (Σ_j q_W(R_j))⁸`. -/
theorem node_biasW_RA (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm) (ξ₁ ξ₂ : Fin (mA n) → ℝ)
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) :
    biasW c g ξ₁ ξ₂ ^ 8 ≤ (∑ j, qp
      (cW0 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
        (AW2 Dm Pm (√(tA n) * O)))
      (cW1 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
        (AW2 Dm Pm (√(tA n) * O))) 0 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 8 := by
  set s := nodeS c g
  have hv : 0 < vsig2 c s := hSm.trans_le H.hS1
  rw [biasW_rows hn c g hs h1]
  set y : Fin (mA n) → ℝ := fun j => ∫ v, BstLean.Part170.G2 (√(wT c g v))
      ((M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j) ∂stdGauss (Fin (n - 1)) -
        BstLean.Part170.G2 √(vsig2 c s) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j) with hy
  set Q : Fin (mA n) → ℝ := fun j => AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j +
      AW2 Dm Pm (√(tA n) * O) * rhoJ ξ₁ ξ₂ j ^ 2 with hQ
  have hyQ : ∀ j, |y j| ≤ Q j := by
    intro j
    have R := rowW (row_stat hn c g hs hO h1 hv ξ₁ ξ₂ j) ((M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j)
    have e : ∀ v, (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c s) j + ((M0 c g ξ₁ ξ₂ *ᵥ aLat c (nodeS c g) v) j -
        (M0 c g ξ₁ ξ₂ *ᵥ a1Bar c (nodeS c g)) j) = (M0 c g ξ₁ ξ₂ *ᵥ aLat c s v) j := fun v => by
      simp only [s]; ring
    simp only [e] at R
    refine R.trans ?_
    have hρ : 0 ≤ rhoJ ξ₁ ξ₂ j := Real.sqrt_nonneg _
    have hC : 0 ≤ √(tA n) * O := mul_nonneg (Real.sqrt_nonneg _) hO
    have hsum := abs_add_abs_le (ξ₁ j) (ξ₂ j)
    have hsum' : (|ξ₁ j| + |ξ₂ j|) * (√(tA n) * O) ≤ √2 * rhoJ ξ₁ ξ₂ j * (√(tA n) * O) :=
      mul_le_mul_of_nonneg_right hsum hC
    refine TW_le (Real.sqrt_pos.mpr hSm) (Real.sqrt_le_sqrt H.hS1) (Real.sqrt_le_sqrt H.hS2) hρ hC
      ?_ (by positivity) ?_
      (by have := vsig2_nonneg c s; have := tA_nonneg n; positivity) (by linarith [H.hS2])
      (mul_nonneg (by positivity) (DstN_nonneg c g)) ?_ (hUN_nonneg c g) H.hH (V2N_nonneg c g)
      H.hV (piN_nonneg c g) H.hP
    · have := abs_M0abar_le hn c g hs hO h1 ξ₁ ξ₂ j
      unfold rhoJ at *
      nlinarith
    · unfold rhoJ at *
      nlinarith
    · rw [rhoJ_sq]
      exact mul_le_mul_of_nonneg_left H.hD (by positivity)
  have hS : |∑ j, y j| ≤ ∑ j, |y j| := Finset.abs_sum_le_sum_abs _ _
  have hS2 : ∑ j, |y j| ≤ ∑ j, qp
      (cW0 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
        (AW2 Dm Pm (√(tA n) * O)))
      (cW1 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
        (AW2 Dm Pm (√(tA n) * O))) 0 (ξ₁ j ^ 2 + ξ₂ j ^ 2) := by
    gcongr with j
    have hq := PW_le (A0 := AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
      (A2 := AW2 Dm Pm (√(tA n) * O)) (ρ := rhoJ ξ₁ ξ₂ j) hA1
    refine ((hyQ j).trans hq).trans (le_of_eq ?_)
    rw [rhoJ_sq]
  calc (∑ j, y j) ^ 8 = |∑ j, y j| ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hS.trans hS2) 8

/-- **The location bias moments on the statistics event, row-averaged form.** -/
theorem biasMomF_RA_of_stat (hn : 1 ≤ n)
    (hbulk : ∀ wr : WRet n, windowW wr → ∀ (θ : AHid n) (g : ℕ), g < Js n →
      nodeS (mkR wr θ) g ^ 2 ≤ 1)
    {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm)
    {c0 c1 c2 : ℝ}
    (hc0 : cF0 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O))
      (AF2 √Smin Dm) = c0)
    (hc1 : cF1 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O))
      (AF2 √Smin Dm) = c1)
    (hc2 : cF2 (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O))
      (AF2 √Smin Dm) = c2)
    {ε t B : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (hB : (n : ℝ) ^ 4 * ((1 + ε) ^ 3 * (((mA n : ℕ) : ℝ) * (c0 + 2 * c1 + 8 * c2)) ^ 4 +
      (1 + 1 / ε) ^ 3 * (M8 (mA n) (c0 + c1 + c2) (c0 + 2 * c1 + 8 * c2) / (2 * t) + t / 2)) ≤
        B ^ 8) :
    BiasMomF O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  set c := mkR wr (A₁, 0)
  have hs := hbulk wr hw (A₁, 0) g hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  have hc0' : 0 ≤ c0 := by rw [← hc0]; unfold cF0 aa; positivity
  have hc1' : 0 ≤ c1 := by rw [← hc1]; unfold cF1 aa; positivity
  have hc2' : 0 ≤ c2 := by rw [← hc2]; unfold cF2; positivity
  have hbd := sum4_two (m := mA n) hc0' hc1' hc2' hε ht
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((n : ℝ) ^ 4) *
          ENNReal.ofReal ((∑ j, qp c0 c1 c2 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 4) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ?_
        rw [← ENNReal.ofReal_mul hn4]
        refine ENNReal.ofReal_le_ofReal ?_
        have := node_biasF_RA hn c g hs hO h1 hSm H ξ₁ ξ₂ hA0 hA1 hA2
        rwa [hc0, hc1, hc2] at this
    _ = ENNReal.ofReal ((n : ℝ) ^ 4) * ∫⁻ ξ₁, ∫⁻ ξ₂,
          ENNReal.ofReal ((∑ j, qp c0 c1 c2 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 4) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ 4) * ENNReal.ofReal ((1 + ε) ^ 3 *
          (((mA n : ℕ) : ℝ) * (c0 + 2 * c1 + 8 * c2)) ^ 4 +
          (1 + 1 / ε) ^ 3 * (M8 (mA n) (c0 + c1 + c2) (c0 + 2 * c1 + 8 * c2) / (2 * t) + t / 2)) := by
        gcongr
    _ ≤ ENNReal.ofReal (B ^ 8) := by
        rw [← ENNReal.ofReal_mul hn4]; exact ENNReal.ofReal_le_ofReal hB

/-- **The energy bias moments on the statistics event, row-averaged form.** -/
theorem biasMomW_RA_of_stat (hn : 1 ≤ n)
    (hbulk : ∀ wr : WRet n, windowW wr → ∀ (θ : AHid n) (g : ℕ), g < Js n →
      nodeS (mkR wr θ) g ^ 2 ≤ 1)
    {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AW2 Dm Pm (√(tA n) * O))
    {c0 c1 : ℝ}
    (hc0 : cW0 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
      (AW2 Dm Pm (√(tA n) * O)) = c0)
    (hc1 : cW1 (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
      (AW2 Dm Pm (√(tA n) * O)) = c1)
    {ε B : ℝ} (hε : 0 < ε)
    (hB : (1 + ε) ^ 7 * (((mA n : ℕ) : ℝ) * (c0 + 2 * c1 + 8 * 0)) ^ 8 +
      (1 + 1 / ε) ^ 7 * M8 (mA n) (c0 + c1 + 0) (c0 + 2 * c1 + 8 * 0) ≤ B ^ 8) :
    BiasMomW O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  set c := mkR wr (A₁, 0)
  have hs := hbulk wr hw (A₁, 0) g hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  have hc0' : 0 ≤ c0 := by rw [← hc0]; unfold cW0 aa; positivity
  have hc1' : 0 ≤ c1 := by rw [← hc1]; unfold cW1 aa; positivity
  have hbd := sum8_two (m := mA n) hc0' hc1' le_rfl hε
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((∑ j, qp c0 c1 0 (ξ₁ j ^ 2 + ξ₂ j ^ 2)) ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        have := node_biasW_RA hn c g hs hO h1 hSm H ξ₁ ξ₂ hA1
        rwa [hc0, hc1] at this
    _ ≤ _ := hbd
    _ ≤ ENNReal.ofReal (B ^ 8) := ENNReal.ofReal_le_ofReal hB

end BstLean.Part186.RA
