import BstLean.Part151JF4b
import BstLean.Part133L2

/-!
# Part 151: Lemma JF in the document's form, the `L⁴` bound and the one-factor charge

Role: `proofs/option-n/theorem5-08-F-rows.tex`, Lemma JF.
`t = 2/m`, `Q = jacFro F₁ F₂ y = ‖J_F(y)‖²_F`.

* `four_split`: `(a + b)⁴ ≤ (1 + s)³a⁴ + (1 + 1/s)³b⁴` for `s > 0`.
* **`lemmaJF4`** (the `L⁴` bound): for `n ≥ 4096`, `m ≥ 262144`, `y ≠ 0`:
  `E_{F₁,F₂} (t·Q − 2)⁴ ≤ (854/100)⁴/m²`.
* **`lemmaJF4_charge`** (the one-factor charge): for every probability measure `P` of inputs
  that does not depend on `F`: `Pr(Φ > 2(1 + δ)) ≤ (854/100)⁴/(16·δ⁴·m²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)

/-! ## Pointwise convexity and the numbers -/

lemma two_split {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + s) * a ^ 2 + (1 + 1 / s) * b ^ 2 := by
  have h : (1 + s) * a ^ 2 + (1 + 1 / s) * b ^ 2 - (a + b) ^ 2 = (s * a - b) ^ 2 / s := by
    field_simp; ring
  have : 0 ≤ (s * a - b) ^ 2 / s := by positivity
  linarith

/-- `(a + b)⁴ ≤ (1 + s)³a⁴ + (1 + 1/s)³b⁴` for `s > 0`. -/
lemma four_split {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    (a + b) ^ 4 ≤ (1 + s) ^ 3 * a ^ 4 + (1 + 1 / s) ^ 3 * b ^ 4 := by
  have h1 := two_split hs a b
  have h2 := two_split hs ((1 + s) * a ^ 2) ((1 + 1 / s) * b ^ 2)
  have h3 : ((a + b) ^ 2) ^ 2 ≤ ((1 + s) * a ^ 2 + (1 + 1 / s) * b ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  calc (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
    _ ≤ _ := h3
    _ ≤ (1 + s) * ((1 + s) * a ^ 2) ^ 2 + (1 + 1 / s) * ((1 + 1 / s) * b ^ 2) ^ 2 := h2
    _ = _ := by ring

/-- The numbers of the `L⁴` bound. -/
lemma num_L4 {n : ℕ} (hn : 4096 ≤ n) {M : ℝ} (hM : 262144 ≤ M) :
    (13 / 9 : ℝ) ^ 3 * (2 / M) ^ 4 *
        ((2 / M) ^ 4 * ((381 / 380) ^ 3 * M ^ 4) * (841 / 2 * M + 75 / 16 * M ^ 2)) +
      ((13 / 9) ^ 3 * (2 / M) ^ 4 * ((2 / M) ^ 4 * 381 ^ 3 * (841 / 2 * M + 75 / 16 * M ^ 2)) +
          (13 / 4) ^ 3 * (2 / M) ^ 4) *
        (M * (64 * rhoJ n + 8) + 3 * M ^ 2 * (1 + 4 / (n : ℝ)) ^ 2) ≤
      (854 / 100) ^ 4 / M ^ 2 := by
  have hN : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hM0 : 0 < M := by linarith
  have hN0 : (0 : ℝ) < n := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hρ : rhoJ n ≤ 1 + 36 / 4096 + 112 / 4096 ^ 2 + 48 / 4096 ^ 3 := by
    unfold rhoJ; gcongr
  have hρ0 : 0 ≤ rhoJ n := by unfold rhoJ; positivity
  have hx : 1 / M ≤ 1 / 262144 := one_div_le_one_div_of_le (by norm_num) hM
  have hx0 : 0 ≤ 1 / M := by positivity
  have hv : (1 + 4 / (n : ℝ)) ^ 2 ≤ (1 + 4 / 4096) ^ 2 := by gcongr
  have hA : 841 / 2 * (1 / M) + 75 / 16 ≤ 841 / 2 * (1 / 262144) + 75 / 16 := by gcongr
  have hR : 1 / M * (64 * rhoJ n + 8) + 3 * (1 + 4 / (n : ℝ)) ^ 2 ≤
      1 / 262144 * (64 * (1 + 36 / 4096 + 112 / 4096 ^ 2 + 48 / 4096 ^ 3) + 8) +
        3 * (1 + 4 / 4096) ^ 2 := by gcongr
  have hR0 : 0 ≤ 1 / M * (64 * rhoJ n + 8) + 3 * (1 + 4 / (n : ℝ)) ^ 2 := by positivity
  calc ((13 / 9 : ℝ) ^ 3 * (2 / M) ^ 4 *
        ((2 / M) ^ 4 * ((381 / 380) ^ 3 * M ^ 4) * (841 / 2 * M + 75 / 16 * M ^ 2)) +
      ((13 / 9) ^ 3 * (2 / M) ^ 4 * ((2 / M) ^ 4 * 381 ^ 3 * (841 / 2 * M + 75 / 16 * M ^ 2)) +
          (13 / 4) ^ 3 * (2 / M) ^ 4) *
        (M * (64 * rhoJ n + 8) + 3 * M ^ 2 * (1 + 4 / (n : ℝ)) ^ 2)) * M ^ 2
      = (13 / 9) ^ 3 * (381 / 380) ^ 3 * 256 * (841 / 2 * (1 / M) + 75 / 16) +
        ((13 / 9) ^ 3 * 381 ^ 3 * 256 * (1 / M) ^ 2 * (841 / 2 * (1 / M) + 75 / 16) +
          16 * (13 / 4) ^ 3) *
        (1 / M * (64 * rhoJ n + 8) + 3 * (1 + 4 / (n : ℝ)) ^ 2) := by
        field_simp; ring
    _ ≤ (13 / 9) ^ 3 * (381 / 380) ^ 3 * 256 * (841 / 2 * (1 / 262144) + 75 / 16) +
        ((13 / 9) ^ 3 * 381 ^ 3 * 256 * (1 / 262144) ^ 2 * (841 / 2 * (1 / 262144) + 75 / 16) +
          16 * (13 / 4) ^ 3) *
        (1 / 262144 * (64 * (1 + 36 / 4096 + 112 / 4096 ^ 2 + 48 / 4096 ^ 3) + 8) +
          3 * (1 + 4 / 4096) ^ 2) := by gcongr
    _ ≤ (854 / 100) ^ 4 := by norm_num

/-! ## The `L⁴` bound -/

section L4

variable {n m : ℕ}

/-- **Lemma JF, the `L⁴` bound.** For `n ≥ 4096`, `m ≥ 262144` and `y ≠ 0`
(`F₁ ∼ gaussMat m n (2/n)`, `F₂ ∼ gaussMat m m (2/m)`, `t = 2/m`):
`E (t·‖J_F(y)‖²_F − 2)⁴ ≤ (854/100)⁴/m²`. -/
theorem lemmaJF4 (hn : 4096 ≤ n) (hm : 262144 ≤ m) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∫⁻ θ, ENNReal.ofReal ((2 / (m : ℝ) * jacFro θ.1 θ.2 y - 2) ^ 4) ∂hidGauss n m ≤
      ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmeas : Measurable (fun θ : HidParam n m =>
      ENNReal.ofReal ((2 / (m : ℝ) * jacFro θ.1 θ.2 y - 2) ^ 4)) :=
    ENNReal.measurable_ofReal.comp
      ((((measurable_jacFro_param y).const_mul _).sub measurable_const).pow_const 4)
  unfold hidGauss
  rw [lintegral_prod _ hmeas.aemeasurable]
  set t : ℝ := 2 / (m : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  set K : ℝ := 841 / 2 * m + 75 / 16 * (m : ℝ) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c0 : ℝ := (13 / 9 : ℝ) ^ 3 * t ^ 4 * (t ^ 4 * ((381 / 380) ^ 3 * (m : ℝ) ^ 4) * K) with hc0
  set c1 : ℝ := (13 / 9 : ℝ) ^ 3 * t ^ 4 * (t ^ 4 * 381 ^ 3 * K) + (13 / 4) ^ 3 * t ^ 4 with hc1
  have c0n : 0 ≤ c0 := by positivity
  have c1n : 0 ≤ c1 := by positivity
  have inner : ∀ F₁ : Matrix (Fin m) (Fin n) ℝ,
      ∫⁻ F₂, ENNReal.ofReal ((t * jacFro F₁ F₂ y - 2) ^ 4) ∂gaussMat m m (2 / (m : ℝ)) ≤
        ENNReal.ofReal (c0 + c1 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4) := by
    intro F₁
    set Wd : ℝ := ∑ i, ∑ l, maskedF F₁ y i l ^ 2 with hWd
    have pt : ∀ F₂ : Matrix (Fin m) (Fin m) ℝ,
        ENNReal.ofReal ((t * jacFro F₁ F₂ y - 2) ^ 4) ≤
          ENNReal.ofReal ((13 / 9) ^ 3 * t ^ 4) * ENNReal.ofReal ((jacFro F₁ F₂ y - Wd) ^ 4) +
            ENNReal.ofReal ((13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4) := by
      intro F₂
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := four_split (s := 4 / 9) (by norm_num) (t * (jacFro F₁ F₂ y - Wd)) (t * (Wd - m))
      have e : t * (jacFro F₁ F₂ y - Wd) + t * (Wd - m) = t * jacFro F₁ F₂ y - 2 := by
        rw [ht]; field_simp; ring
      rw [e] at h
      refine h.trans (le_of_eq ?_)
      ring
    have hW := four_split (s := 1 / 380) (by norm_num) (m : ℝ) (Wd - m)
    have hW' : Wd ^ 4 ≤ (381 / 380) ^ 3 * (m : ℝ) ^ 4 + 381 ^ 3 * (Wd - m) ^ 4 := by
      have e : (m : ℝ) + (Wd - m) = Wd := by ring
      rw [e] at hW
      refine hW.trans (le_of_eq ?_)
      ring
    calc ∫⁻ F₂, ENNReal.ofReal ((t * jacFro F₁ F₂ y - 2) ^ 4) ∂gaussMat m m (2 / (m : ℝ))
        ≤ ∫⁻ F₂, (ENNReal.ofReal ((13 / 9) ^ 3 * t ^ 4) *
            ENNReal.ofReal ((jacFro F₁ F₂ y - Wd) ^ 4) +
            ENNReal.ofReal ((13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4)) ∂gaussMat m m (2 / (m : ℝ)) :=
          lintegral_mono pt
      _ = ENNReal.ofReal ((13 / 9) ^ 3 * t ^ 4) *
            ∫⁻ F₂, ENNReal.ofReal ((jacFro F₁ F₂ y - Wd) ^ 4) ∂gaussMat m m (2 / (m : ℝ)) +
            ENNReal.ofReal ((13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4) := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal ((13 / 9) ^ 3 * t ^ 4) *
            ENNReal.ofReal (t ^ 4 * Wd ^ 4 * K) +
            ENNReal.ofReal ((13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4) := by
          gcongr
          exact lemmaJF4_inner hn1 hm1 F₁ y
      _ ≤ ENNReal.ofReal (c0 + c1 * (Wd - m) ^ 4) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h3 := mul_le_mul_of_nonneg_left hW'
            (by positivity : 0 ≤ (13 / 9 : ℝ) ^ 3 * t ^ 4 * t ^ 4 * K)
          calc (13 / 9 : ℝ) ^ 3 * t ^ 4 * (t ^ 4 * Wd ^ 4 * K) +
                (13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4
              = (13 / 9 : ℝ) ^ 3 * t ^ 4 * t ^ 4 * K * Wd ^ 4 +
                (13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4 := by ring
            _ ≤ (13 / 9 : ℝ) ^ 3 * t ^ 4 * t ^ 4 * K *
                  ((381 / 380) ^ 3 * (m : ℝ) ^ 4 + 381 ^ 3 * (Wd - m) ^ 4) +
                (13 / 4) ^ 3 * t ^ 4 * (Wd - m) ^ 4 := by linarith
            _ = c0 + c1 * (Wd - m) ^ 4 := by rw [hc0, hc1]; ring
  have esplit : ∀ F₁ : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (c0 + c1 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4) =
        ENNReal.ofReal c0 +
          ENNReal.ofReal c1 * ENNReal.ofReal ((∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4) :=
    fun F₁ => by rw [ENNReal.ofReal_add c0n (by positivity), ENNReal.ofReal_mul c1n]
  calc ∫⁻ F₁, ∫⁻ F₂, ENNReal.ofReal ((t * jacFro F₁ F₂ y - 2) ^ 4)
        ∂gaussMat m m (2 / (m : ℝ)) ∂gaussMat m n (2 / (n : ℝ))
      ≤ ∫⁻ F₁, ENNReal.ofReal (c0 + c1 * (∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4)
          ∂gaussMat m n (2 / (n : ℝ)) := lintegral_mono inner
    _ = ENNReal.ofReal c0 + ENNReal.ofReal c1 *
          ∫⁻ F₁, ENNReal.ofReal ((∑ i, ∑ l, maskedF F₁ y i l ^ 2 - m) ^ 4)
            ∂gaussMat m n (2 / (n : ℝ)) := by
        simp_rw [esplit]
        rw [lintegral_add_left measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp
    _ ≤ ENNReal.ofReal c0 + ENNReal.ofReal c1 * ENNReal.ofReal
          (m * (64 * rhoJ n + 8) + 3 * (m : ℝ) ^ 2 * (1 + 4 / (n : ℝ)) ^ 2) := by
        gcongr
        exact lemmaJF4_W hn1 hy
    _ ≤ ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) := by
        have hρ0 : 0 ≤ rhoJ n := by unfold rhoJ; positivity
        rw [← ENNReal.ofReal_mul c1n, ← ENNReal.ofReal_add c0n (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hM : (262144 : ℝ) ≤ m := by exact_mod_cast hm
        exact num_L4 hn hM

end L4

/-! ## The one-factor charge -/

section charge

variable {Ω' : Type*} [MeasurableSpace Ω'] {n m : ℕ}

lemma jacFro_zero (F₁ : Matrix (Fin m) (Fin n) ℝ) (F₂ : Matrix (Fin m) (Fin m) ℝ) :
    jacFro F₁ F₂ (0 : Fin n → ℝ) = 0 := by
  rw [jacFro_rows]
  have h0 : reluV (F₁ *ᵥ (0 : Fin n → ℝ)) = 0 := by
    funext i
    simp [reluV, relu]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h0]
  simp

lemma jacFro_le (F₁ : Matrix (Fin m) (Fin n) ℝ) (F₂ : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin n → ℝ) : jacFro F₁ F₂ y ≤ ∑ j, normSq (rowOf j F₂) * frob F₁ := by
  have e : jacFro F₁ F₂ y = ∑ j, phiJ F₁ (rowOf j F₂) y := by
    rw [jacFro_rows]
    exact Finset.sum_congr rfl fun j _ => rfl
  rw [e]
  exact Finset.sum_le_sum fun j _ => (phiJ_le_quad F₁ _ y).trans (quad_le F₁ _ y)

variable (P : Measure Ω') [IsProbabilityMeasure P] {Yv : Ω' → Fin n → ℝ}

/-- **Lemma JF, the one-factor charge.** `P` is a distribution of inputs `y = Yv ω` that does
not depend on `F`; `Φ = E_y t_F·‖J_F(y)‖²_F`. For `n ≥ 4096`, `m ≥ 262144`, `δ > 0`:
`Pr_{F₁,F₂}(Φ > 2(1 + δ)) ≤ (854/100)⁴/(16·δ⁴·m²)`. -/
theorem lemmaJF4_charge (hn : 4096 ≤ n) (hm : 262144 ≤ m) (hY : Measurable Yv) {δ : ℝ}
    (hδ : 0 < δ) :
    (hidGauss n m).real {θ | 2 * (1 + δ) < PhiJ P Yv θ} ≤
      (854 / 100) ^ 4 / (16 * δ ^ 4 * (m : ℝ) ^ 2) := by
  have hm0 : (0 : ℝ) < m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  set t : ℝ := 2 / (m : ℝ) with ht
  have ht0 : 0 ≤ t := by positivity
  set g : HidParam n m × Ω' → ℝ := fun q => t * jacFro q.1.1 q.1.2 (Yv q.2) - 2 with hg
  have mg : Measurable g :=
    ((measurable_jacFro_joint.comp (measurable_fst.prodMk (hY.comp measurable_snd))).const_mul
      _).sub measurable_const
  set D : HidParam n m × Ω' → ℝ := fun q => max 0 (g q) with hD
  have mD : Measurable D := measurable_const.max mg
  have hD0 : ∀ q, 0 ≤ D q := fun q => le_max_left _ _
  have mD4 : Measurable (fun q : HidParam n m × Ω' => ENNReal.ofReal (D q ^ 4)) :=
    ENNReal.measurable_ofReal.comp (mD.pow_const 4)
  set H : HidParam n m → ℝ≥0∞ := fun θ => ∫⁻ ω, ENNReal.ofReal (D (θ, ω) ^ 4) ∂P with hH
  have mH : Measurable H := Measurable.lintegral_prod_right' mD4
  -- the total integral
  have hT : ∫⁻ θ, H θ ∂hidGauss n m ≤ ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) := by
    have sw : ∫⁻ θ, H θ ∂hidGauss n m =
        ∫⁻ ω, ∫⁻ θ, ENNReal.ofReal (D (θ, ω) ^ 4) ∂hidGauss n m ∂P :=
      lintegral_lintegral_swap (f := fun θ ω => ENNReal.ofReal (D (θ, ω) ^ 4))
        (by exact mD4.aemeasurable)
    rw [sw]
    calc ∫⁻ ω, ∫⁻ θ, ENNReal.ofReal (D (θ, ω) ^ 4) ∂hidGauss n m ∂P
        ≤ ∫⁻ _, ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hy : Yv ω = 0
          · have hz : ∀ θ : HidParam n m, D (θ, ω) = 0 := by
              intro θ
              change max 0 (t * jacFro θ.1 θ.2 (Yv ω) - 2) = 0
              rw [hy, jacFro_zero]
              norm_num
            simp [hz]
          · refine (lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ?_).trans
              (lemmaJF4 hn hm hy)
            change (max 0 (g (θ, ω))) ^ 4 ≤ (g (θ, ω)) ^ 4
            rcases le_total 0 (g (θ, ω)) with h | h
            · rw [max_eq_right h]
            · rw [max_eq_left h, zero_pow (by norm_num)]
              positivity
      _ = ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) := by simp
  -- the inclusion
  have hsub : {θ : HidParam n m | 2 * (1 + δ) < PhiJ P Yv θ} ⊆
      {θ | ENNReal.ofReal ((2 * δ) ^ 4) ≤ H θ} := by
    intro θ hθ
    simp only [mem_ofPred_eq] at hθ ⊢
    set Kθ : ℝ := ∑ j, normSq (rowOf j θ.2) * frob θ.1 with hKθ
    have hj0 : ∀ ω, 0 ≤ jacFro θ.1 θ.2 (Yv ω) := fun ω => jacFro_nonneg _ _ _
    have hjb : ∀ ω, jacFro θ.1 θ.2 (Yv ω) ≤ Kθ := fun ω => jacFro_le _ _ _
    have hK0 : 0 ≤ Kθ := (jacFro_nonneg θ.1 θ.2 (0 : Fin n → ℝ)).trans (jacFro_le _ _ _)
    have mgθ : Measurable (fun ω => g (θ, ω)) := mg.comp (measurable_const.prodMk measurable_id)
    have mDθ : Measurable (fun ω => D (θ, ω)) := mD.comp (measurable_const.prodMk measurable_id)
    have hgb : ∀ ω, |g (θ, ω)| ≤ t * Kθ + 2 := by
      intro ω
      have h1 : t * jacFro θ.1 θ.2 (Yv ω) ≤ t * Kθ := mul_le_mul_of_nonneg_left (hjb ω) ht0
      have h2 : 0 ≤ t * jacFro θ.1 θ.2 (Yv ω) := mul_nonneg ht0 (hj0 ω)
      change |t * jacFro θ.1 θ.2 (Yv ω) - 2| ≤ _
      rw [abs_le]
      constructor <;> linarith
    have hDb : ∀ ω, D (θ, ω) ≤ t * Kθ + 2 := by
      intro ω
      have hb : 0 ≤ t * Kθ + 2 := by positivity
      exact max_le hb ((le_abs_self _).trans (hgb ω))
    have ij : Integrable (fun ω => t * jacFro θ.1 θ.2 (Yv ω)) P := by
      have mj : Measurable (fun ω => t * jacFro θ.1 θ.2 (Yv ω)) :=
        (measurable_jacFro_joint.comp
          ((measurable_const (a := θ)).prodMk hY)).const_mul _
      refine Integrable.of_bound mj.aestronglyMeasurable (t * Kθ)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (hj0 ω))]
      exact mul_le_mul_of_nonneg_left (hjb ω) ht0
    have ig : Integrable (fun ω => g (θ, ω)) P := ij.sub (integrable_const 2)
    have iD : ∀ k : ℕ, Integrable (fun ω => D (θ, ω) ^ k) P := by
      intro k
      refine Integrable.of_bound (mDθ.pow_const k).aestronglyMeasurable ((t * Kθ + 2) ^ k)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hD0 _) k)]
      exact pow_le_pow_left₀ (hD0 _) (hDb ω) k
    have iD1 : Integrable (fun ω => D (θ, ω)) P := by simpa using iD 1
    have e1 : PhiJ P Yv θ - 2 = ∫ ω, g (θ, ω) ∂P := by
      change (∫ ω, t * jacFro θ.1 θ.2 (Yv ω) ∂P) - 2 = ∫ ω, (t * jacFro θ.1 θ.2 (Yv ω) - 2) ∂P
      rw [integral_sub ij (integrable_const 2)]
      simp
    have h1 : PhiJ P Yv θ - 2 ≤ ∫ ω, D (θ, ω) ∂P := by
      rw [e1]
      exact integral_mono ig iD1 fun ω => le_max_right _ _
    have h2 : (∫ ω, D (θ, ω) ∂P) ^ 2 ≤ ∫ ω, D (θ, ω) ^ 2 ∂P :=
      BstLean.Part133.sq_integral_le (iD 2)
    have i22 : Integrable (fun ω => (D (θ, ω) ^ 2) ^ 2) P := by
      have := iD 4
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      change D (θ, ω) ^ 4 = (D (θ, ω) ^ 2) ^ 2
      ring
    have h3 : (∫ ω, D (θ, ω) ^ 2 ∂P) ^ 2 ≤ ∫ ω, (D (θ, ω) ^ 2) ^ 2 ∂P :=
      BstLean.Part133.sq_integral_le (f := fun ω => D (θ, ω) ^ 2) i22
    have e4 : ∫ ω, (D (θ, ω) ^ 2) ^ 2 ∂P = ∫ ω, D (θ, ω) ^ 4 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        change (D (θ, ω) ^ 2) ^ 2 = D (θ, ω) ^ 4
        ring)
    have h4 : (2 * δ) ^ 4 ≤ ∫ ω, D (θ, ω) ^ 4 ∂P := by
      have a1 : 2 * δ ≤ ∫ ω, D (θ, ω) ∂P := by linarith
      have a2 : (2 * δ) ^ 2 ≤ ∫ ω, D (θ, ω) ^ 2 ∂P :=
        (pow_le_pow_left₀ (by positivity) a1 2).trans h2
      have a3 : ((2 * δ) ^ 2) ^ 2 ≤ (∫ ω, D (θ, ω) ^ 2 ∂P) ^ 2 :=
        pow_le_pow_left₀ (by positivity) a2 2
      calc (2 * δ) ^ 4 = ((2 * δ) ^ 2) ^ 2 := by ring
        _ ≤ _ := a3
        _ ≤ _ := h3
        _ = _ := e4
    change ENNReal.ofReal ((2 * δ) ^ 4) ≤ ∫⁻ ω, ENNReal.ofReal (D (θ, ω) ^ 4) ∂P
    rw [← ofReal_integral_eq_lintegral_ofReal (iD 4)
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hD0 _) 4)]
    exact ENNReal.ofReal_le_ofReal h4
  -- Markov
  have hε0 : ENNReal.ofReal ((2 * δ) ^ 4) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hM : (hidGauss n m) {θ | ENNReal.ofReal ((2 * δ) ^ 4) ≤ H θ} ≤
      ENNReal.ofReal ((854 / 100) ^ 4 / (m : ℝ) ^ 2) / ENNReal.ofReal ((2 * δ) ^ 4) :=
    (meas_ge_le_lintegral_div mH.aemeasurable hε0 ENNReal.ofReal_ne_top).trans
      (ENNReal.div_le_div_right hT _)
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((measure_mono hsub).trans (hM.trans (le_of_eq ?_)))
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp
  ring

end charge

end BstLean.Part151
