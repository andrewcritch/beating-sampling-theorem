import BstLean.Part150Bin2
import BstLean.Part150ThmNum

/-!
# Part 150, item 5: the arithmetic program with `J = n` atoms (the main form of the paper)

`Part150Arith` has the binomial part at first order in `α(J)` (`xiBin J`), which is small only
for `J = n²`. Here the binomial part is taken on the good event of `A₁`, at second order
(`Part150Bin2`): `xiBin2 n (2/5) (mA n) ≤ 10/n²`.

* `arith_bin2_part`, `arith_inner2`, **`arith_dispOK2`**: `E[1_good·|bTW − bMF|²] ≤ (m/n)·xiArith2`.
* `arithProg150_of`: the program bound for any displacement constant `ξ` of `bTW J`.
* **`arithProgN150`**: the program `fullProg150 k n n` (`J = n`), explicit terms.
* **`arithProgN150_16384`**: `≥ 7/10` for every `n ≥ 16 384`, `k ≥ 100n`;
  **`arithProgN150_99`**: `≥ 99/100` for every `n ≥ 400 000`, `k ≥ n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part139 (gamK)
open BstLean.Part141 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- The binomial part at second order, in mean over `(A₁, A₂)`, on the good event of `A₁`. -/
lemma arith_bin2_part {m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {k εD εQ σ : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hεD0 : 0 ≤ εD)
    (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ) (hcond : k * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hσ0 : 0 < σ) (hσ : σ ≤ (1 - εD) / 2 - 2 * LamN n εD εQ) :
    ∫⁻ θ : HidParam n m,
        ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
            Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
          (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
            (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ)))) θ.1 ∂hidGauss n m ≤
      ENNReal.ofReal (2 * ((m : ℝ) / n * xiBin2 J σ m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e0 : hidGauss n m = (gaussMat m n (2 / (n : ℝ))).prod (gaussMat m m (2 / (m : ℝ))) := rfl
  have key : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ,
      ∫⁻ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
              (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))) A₁ ∂gaussMat m m (2 / (m : ℝ)) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (PhiB J σ A₁ c τ) := by
    intro A₁
    by_cases hA : errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
        Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2
    · have e : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
              (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))) A₁ =
          ENNReal.ofReal 2 * ENNReal.ofReal
            (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ))) := by
        intro A₂
        rw [Set.indicator_of_mem (by exact hA), ENNReal.ofReal_mul (by norm_num)]
      simp_rw [e]
      have hlow := sO2_lower hn hm c hτ A₁ hk0 hk1 hεD0 hεD1 hεQ0 hcond hA.1 hA.2
      have hlow' : σ / (n : ℝ) ≤ sO2 A₁ c τ / rhoC c τ ^ 2 :=
        (div_le_div_of_nonneg_right hσ hnR.le).trans hlow
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (bin2_A2 hn hm hJ A₁ c hτ hσ0 hlow')
    · have e : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
              (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))) A₁ = 0 := by
        intro A₂
        rw [Set.indicator_of_notMem (by exact hA)]
      simp_rw [e]
      simp
  rw [e0]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_mono key).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (bin2_mean hn hm J c hτ hσ0)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]

/-- The mean over `(A₁, A₂)` of the displacement, for a fixed `W` (second-order form). -/
lemma arith_inner2 (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {εD εQ lam σ : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : 62714 / 100000 * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hlam : 0 < lam) (hσ0 : 0 < σ) (hσ : σ ≤ (1 - εD) / 2 - 2 * LamN n εD εQ)
    {J : ℕ} (hJ : 1 ≤ J) (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH (bTW J) x)) (W, θ)
        ∂hidGauss n (mA n) ≤
      (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin2 J σ (mA n))) +
          (ENNReal.ofReal (2 * CQn n εD εQ lam / ((mA n : ℝ) / n)) *
              ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) +
            (ENNReal.ofReal (2 * CEn n εD εQ / ((mA n : ℝ) / n)) *
                ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) +
              ENNReal.ofReal (2 * ((mA n : ℝ) / n * C0n n εD εQ lam))))) W := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  by_cases hW : W ∈ goodWAG G
  swap
  · have e : ∀ θ : HidParam n (mA n), (goodX1 G εD εQ).indicator
        (fun x => ENNReal.ofReal (dispH (bTW J) x)) (W, θ) = 0 := fun θ =>
      Set.indicator_of_notMem (fun h => hW h.1) _
    simp_rw [e]
    simp
  rw [Set.indicator_of_mem hW]
  obtain ⟨_, hτ, hq1, hq2, _, _⟩ := hwin (W.1, W.2.1) hW
  have hτ' : 0 < tauWA W := hτ
  have hkq0 : 0 ≤ kappa (qTh (W.1, W.2.1)) :=
    (kappa_mem (by linarith) (by linarith)).1
  have hkq1 : kappa (qTh (W.1, W.2.1)) ≤ 62714 / 100000 :=
    BstLean.Part135.kappa_le_of_le9 (a := 527 / 1000) (by linarith) hq2 (by norm_num)
      (by norm_num)
  have hcond' : kappa (qTh (W.1, W.2.1)) * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD) := by
    have h1 : 0 ≤ 1 - εD := by linarith
    have := mul_le_mul_of_nonneg_right hkq1 h1
    linarith
  have hb1 := arith_bin2_part (m := mA n) hn1 hmA hJ (cenA W) hτ' hkq0
    (hkq1.trans (by norm_num)) hεD0 hεD1 hεQ0 hcond' hσ0 hσ
  have hb2 := arith_norm_part (m := mA n) hn1 hmA (cenA W) hτ' hkq0
    (hkq1.trans (by norm_num)) hεD0 hεD1 hεQ0 hcond' hlam
  have mQ0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((kappa (qTh (W.1, W.2.1)), cenA W, tauWA W), A₁)) :=
      measurable_const.prodMk measurable_id
    have h2 := (measurable_Qk (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  have mD0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      errD1 (cenA W) (tauWA W) A₁) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((cenA W, tauWA W), A₁)) := measurable_const.prodMk measurable_id
    have h2 := (measurable_errD1 (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact h2
  have mQ : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)) :=
    ENNReal.measurable_ofReal.comp mQ0
  have mD : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)) := ENNReal.measurable_ofReal.comp mD0
  have eq1 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mQ
  have eq2 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mD
  rw [eq1, eq2]
  set S : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
    {A₁ | errD1 (cenA W) (tauWA W) A₁ ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧
      Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁ ≤ ((mA n : ℝ) / n * εQ) ^ 2} with hS
  have mS : MeasurableSet S :=
    (measurableSet_le mD0 measurable_const).inter (measurableSet_le mQ0 measurable_const)
  have h0 : Measurable (fun θ : HidParam n (mA n) => ((cenA W, tauWA W), θ)) :=
    measurable_const.prodMk measurable_id
  have mF : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (2 * normSq
      ((1 / rhoC (cenA W) (tauWA W)) •
        (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W))))) := by
    have h := (measurable_binDispX (n := n) (m := mA n) J).comp h0
    simp only [Function.comp_def] at h
    exact ENNReal.measurable_ofReal.comp (h.const_mul 2)
  have mg1 : Measurable (fun θ : HidParam n (mA n) => S.indicator
      (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC (cenA W) (tauWA W)) •
        (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W))))) θ.1) := by
    have e : (fun θ : HidParam n (mA n) => S.indicator
        (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC (cenA W) (tauWA W)) •
          (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W))))) θ.1) =
        (Prod.fst ⁻¹' S).indicator (fun θ : HidParam n (mA n) => ENNReal.ofReal (2 * normSq
          ((1 / rhoC (cenA W) (tauWA W)) •
            (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W))))) := by
      funext θ
      by_cases h : θ.1 ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show θ ∈ Prod.fst ⁻¹' S from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show θ ∉ Prod.fst ⁻¹' S from h)]
    rw [e]
    exact mF.indicator (measurable_fst mS)
  refine le_trans ?_ (add_le_add hb1 hb2)
  rw [← lintegral_add_left mg1]
  refine lintegral_mono fun θ => ?_
  by_cases hθ : θ.1 ∈ S
  · have h1 : (W, θ) ∈ goodX1 G εD εQ := ⟨hW, hθ.1, hθ.2⟩
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem hθ, Set.indicator_of_mem (by exact hθ)]
    have p1 := normSq_nonneg ((1 / rhoC (cenA W) (tauWA W)) •
      (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W)))
    have p2 := normSq_nonneg ((1 / rhoC (cenA W) (tauWA W)) • bO θ.1 θ.2 (cenA W) (tauWA W) -
      bMF (cenA W) (tauWA W) θ)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : bTW J (W, θ) - bMF (cenA W) (tauWA W) θ =
        (1 / rhoC (cenA W) (tauWA W)) •
          (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W)) +
        ((1 / rhoC (cenA W) (tauWA W)) • bO θ.1 θ.2 (cenA W) (tauWA W) -
          bMF (cenA W) (tauWA W) θ) := by
      unfold bTW
      rw [smul_sub]
      abel
    have := normSq_add_le2 ((1 / rhoC (cenA W) (tauWA W)) •
        (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W)))
      ((1 / rhoC (cenA W) (tauWA W)) • bO θ.1 θ.2 (cenA W) (tauWA W) - bMF (cenA W) (tauWA W) θ)
    unfold dispH
    rw [show bMF (cenA (W, θ).1) (tauWA (W, θ).1) (W, θ).2 = bMF (cenA W) (tauWA W) θ from rfl, e]
    exact this
  · have h1 : (W, θ) ∉ goodX1 G εD εQ := fun h => hθ ⟨h.2.1, h.2.2⟩
    rw [Set.indicator_of_notMem h1]
    exact bot_le

/-- The constant of the displacement of the arithmetic centre, second-order form. -/
noncomputable def xiArith2 (n J : ℕ) (εD εQ lam dQb σ : ℝ) : ℝ :=
  2 * xiBin2 J σ (mA n) +
    2 * (CQn n εD εQ lam * dQb ^ 2 + CEn n εD εQ * (5 / (mA n : ℝ)) + C0n n εD εQ lam)

/-- **The displacement of the arithmetic centre, second-order form**:
`E[1_good·|bTW − bMF|²] ≤ (m/n)·xiArith2`. -/
theorem arith_dispOK2 (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {εD εQ lam σ : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : 62714 / 100000 * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hlam : 0 < lam) (hσ0 : 0 < σ) (hσ : σ ≤ (1 - εD) / 2 - 2 * LamN n εD εQ)
    {J : ℕ} (hJ : 1 ≤ J) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q) :
    DispOK n G εD εQ (bTW J) (xiArith2 n J εD εQ lam dQb σ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hCQ := CQn_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have hCE := CEn_nonneg (n := n) hεD0 hεD1 hεQ0
  have hC0 := C0n_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have hxb := xiBin2_nonneg J hσ0 (mA n)
  have mGW := goodWAG0_meas hG hn1
  have mIQ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_qkW).lintegral_prod_right'
  have mID : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_d1W).lintegral_prod_right'
  unfold DispOK
  refine (lintegral_mono fun W =>
    arith_inner2 hn hwin hεD0 hεD1 hεQ0 hcond hlam hσ0 hσ hJ W).trans ?_
  have e : ∀ W : MlpParam (2 * n) (mW n) n, (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin2 J σ (mA n))) +
          (ENNReal.ofReal (2 * CQn n εD εQ lam / ((mA n : ℝ) / n)) *
              ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) +
            (ENNReal.ofReal (2 * CEn n εD εQ / ((mA n : ℝ) / n)) *
                ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) +
              ENNReal.ofReal (2 * ((mA n : ℝ) / n * C0n n εD εQ lam))))) W ≤
      ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin2 J σ (mA n))) +
        (ENNReal.ofReal (2 * CQn n εD εQ lam / ((mA n : ℝ) / n)) * (goodWAG G).indicator
            (fun W => ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) W +
          (ENNReal.ofReal (2 * CEn n εD εQ / ((mA n : ℝ) / n)) * (goodWAG G).indicator
              (fun W => ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) W +
            ENNReal.ofReal (2 * ((mA n : ℝ) / n * C0n n εD εQ lam)))) := by
    intro W
    by_cases hW : W ∈ goodWAG G
    · simp only [Set.indicator_of_mem hW]; exact le_rfl
    · simp only [Set.indicator_of_notMem hW]; exact bot_le
  refine (lintegral_mono e).trans ?_
  rw [lintegral_add_left measurable_const,
    lintegral_add_left ((mIQ.indicator mGW).const_mul _),
    lintegral_add_left ((mID.indicator mGW).const_mul _),
    lintegral_const_mul _ (mIQ.indicator mGW), lintegral_const_mul _ (mID.indicator mGW)]
  simp only [lintegral_const, measure_univ, mul_one]
  have h1 := qk_mean hn hG hwin hdQ hQ0
  have h2 := d1_mean hn1 hG (fun x hx => (hwin x hx).1)
  refine (add_le_add le_rfl (add_le_add (mul_le_mul' le_rfl h1)
    (add_le_add (mul_le_mul' le_rfl h2) le_rfl))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold xiArith2
  field_simp
  ring


/-- **The arithmetic program, for any displacement constant `ξ` of the centre `bTW J`.** -/
theorem arithProg150_of (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : DispOK n (Gwin n) (9 / 100) (1 / 10) (bTW J) ξ) {η₄ η₅ : ℝ}
    (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n + ξ * (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k) + 1 / (n : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
            Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hS := displaceSamp150 hn hk (measurable_bTW J) hξ0 hξ hη₄ hη₅
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have hbadW := badAG0_prob_gen hn hG hG1
  set μ' := (mlpTriple 2 n).prod (gamK k n) with hμ'
  set ES : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | |gSampH (bTW J) k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
      sdn p.1.1 p.1.2.1 p.1.2.2 / 2} with hES
  set EP : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
      Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} with hEP
  have hsub : ES ⊆ EP ∪ {p | p.1 ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | t.1 ∉ goodWAG (Gwin n)}} := by
    intro p hp
    by_cases hW : p.1.1 ∈ goodWAG (Gwin n)
    · refine Or.inl ?_
      have hτ : 0 < tauWA p.1.1 := (hwin (p.1.1.1, p.1.1.2.1) hW).2.1
      show |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2
      rw [fullProg150_gSampH p.1.1 p.1.2.1 p.1.2.2 p.2 hτ]
      exact hp
    · exact Or.inr hW
  have hm := measureReal_mono (μ := μ') hsub (measure_ne_top _ _)
  have hu := measureReal_union_le (μ := μ') EP
    {p | p.1 ∈ {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | t.1 ∉ goodWAG (Gwin n)}}
  have hpf := BstLean.Part139.prod_fst_real (mlpTriple 2 n) (gamK k n)
    {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWAG (Gwin n)}
  rw [← hμ'] at hpf
  have hq : (1 : ℝ) / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
    rw [qA_cast]
    have e1 : (68000000 : ℝ) / (10000 * (n : ℝ)) ^ 2 = 68 / 100 / (n : ℝ) ^ 2 := by
      field_simp; ring
    have e2 : (68 : ℝ) / 100 / (n : ℝ) ^ 2 ≤ 1 / 2 / (n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      nlinarith
    have e3 : (1 : ℝ) / 50000 / (n : ℝ) ≤ 1 / 2 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    rw [e1]
    have e4 : (1 : ℝ) / 2 / (n : ℝ) + 1 / 2 / (n : ℝ) = 1 / (n : ℝ) := by ring
    linarith
  linarith


/-! ## Numbers at the thresholds of `onePassA149` -/

lemma LamN_le (hn : 4096 ≤ n) : LamN n (9 / 100) (1 / 10) ≤ 11 / 400 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hv : (6 : ℝ) / n ≤ 6 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hv0 : (0 : ℝ) ≤ 6 / (n : ℝ) := by positivity
  have h1 : √(6 / (n : ℝ)) ≤ 383 / 10000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num at hv ⊢; linarith only [hv]
  have hv2 : (6 / (n : ℝ)) ^ 2 ≤ (6 / 4096) ^ 2 := pow_le_pow_left₀ hv0 hv 2
  have h2 : √((2 * (6 / (n : ℝ)) * (9 / 100) ^ 2 + (6 / (n : ℝ)) ^ 2 / 2) * (1 + 9 / 100)) ≤
      53 / 10000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    norm_num at hv hv2 ⊢; linarith only [hv, hv2]
  have h3 : 6 / (n : ℝ) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 / (n : ℝ) / 2) ≤
      6 / 4096 * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 / 4096 / 2) :=
    mul_le_mul hv (by linarith only [hv]) (by positivity) (by norm_num)
  unfold LamN
  norm_num at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

lemma sigma_ok (hn : 4096 ≤ n) :
    (2 / 5 : ℝ) ≤ (1 - 9 / 100) / 2 - 2 * LamN n (9 / 100) (1 / 10) := by
  have := LamN_le hn
  linarith only [this]

/-- `xiBin2 n (2/5) (mA n) ≤ 10/n²`: the binomial part with `J = n` atoms. -/
theorem xiBin2_n (hn : 4096 ≤ n) : xiBin2 n (2 / 5) (mA n) ≤ 10 / (n : ℝ) ^ 2 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have ha := alphaJ_le (J := n) (by omega)
  have hb := betaJ_le (J := n) hn
  have ha0 := alphaJ_nonneg n
  have hb0 := betaJ_nonneg n
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 4096 := one_div_le_one_div_of_le (by norm_num) hx
  have ha' : alphaJ n ≤ 1792 / 10000 * t := by
    refine ha.trans (le_of_eq ?_); rw [ht]; ring
  have hb' : betaJ n ≤ 81 / 1000 * t := by
    refine hb.trans (le_of_eq ?_); rw [ht]; ring
  have hasq : alphaJ n ^ 2 ≤ (1792 / 10000 * t) ^ 2 := pow_le_pow_left₀ ha0 ha' 2
  have hasq' : alphaJ n ^ 2 ≤ 1 / 10000 * t := by
    have h1 : (1792 / 10000 * t) ^ 2 ≤ 1 / 10000 * t := by
      have := mul_le_mul_of_nonneg_left ht1 ht0.le
      nlinarith only [this, ht0]
    exact hasq.trans h1
  set κ : ℝ := betaJ n + 2 * alphaJ n + alphaJ n ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκ1 : κ ≤ 44 / 100 * t := by rw [hκ]; linarith only [ha', hb', hasq', ht0]
  have hκsq : κ ^ 2 ≤ (44 / 100 * t) ^ 2 := pow_le_pow_left₀ hκ0 hκ1 2
  have hmA : (mA n : ℝ) = (n : ℝ) ^ 2 := mA_eqR n
  have hm1 : 1 + 2 / (mA n : ℝ) ≤ 1001 / 1000 := by
    rw [hmA]
    have : (2 : ℝ) / (n : ℝ) ^ 2 ≤ 2 / 4096 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
    norm_num at this ⊢; linarith only [this]
  have hpi := Real.pi_gt_d2
  have hpi0 := Real.pi_pos
  have hcoef : 16 * (1 + 2 / (mA n : ℝ)) / (Real.pi * (2 / 5)) ≤ 1276 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num at hpi ⊢
    linarith only [hm1, hpi]
  have hsum0 : 0 ≤ κ ^ 2 + alphaJ n ^ 2 := by positivity
  have h1 : 16 * (1 + 2 / (mA n : ℝ)) / (Real.pi * (2 / 5)) * (κ ^ 2 + alphaJ n ^ 2) ≤
      1276 / 100 * (κ ^ 2 + alphaJ n ^ 2) := mul_le_mul_of_nonneg_right hcoef hsum0
  have e10 : (10 : ℝ) / (n : ℝ) ^ 2 = 10 * t ^ 2 := by rw [ht]; field_simp
  unfold xiBin2
  rw [← hκ, e10]
  have t2 : 0 ≤ t ^ 2 := by positivity
  nlinarith only [h1, hκsq, hasq, t2]

/-- The second-order displacement constant with `J = n` atoms, `lam = √n/10`, `σ = 2/5`. -/
theorem xiA2_le (hn : 4096 ≤ n) :
    xiArith2 n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) (dQb149 n) (2 / 5) ≤
      20 / (n : ℝ) ^ 2 + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2 := by
  have h1 := xiA_le hn n
  have h2 := xiBin2_n hn
  have e : xiArith2 n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) (dQb149 n) (2 / 5) =
      2 * xiBin2 n (2 / 5) (mA n) + (xiA n n (√(n : ℝ) / 10) - 2 * xiBin n) := by
    unfold xiArith2 xiA xiArith; ring
  rw [e]
  have e20 : (20 : ℝ) / (n : ℝ) ^ 2 = 2 * (10 / (n : ℝ) ^ 2) := by ring
  rw [e20]
  linarith only [h1, h2]

/-- **The arithmetic program with `J = n` atoms** (the main form of the paper): explicit terms. -/
theorem arithProgN150 (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {η₄ η₅ : ℝ} (hη₄ : 0 < η₄)
    (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n +
          (20 / (n : ℝ) ^ 2 + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2) *
            (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k) + 1 / (n : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
            Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have hlam : (0 : ℝ) < √(n : ℝ) / 10 := by positivity
  have hd := arith_dispOK2 hn (goodEvFR hn).to0 (winOK2_149 hn) (εD := 9 / 100) (εQ := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam (σ := 2 / 5) (by norm_num)
    (sigma_ok hn) (J := n) (by omega) (fun _ h1 h2 => dQ1_le hn h1 h2)
    (fun _ h1 h2 => dQ1_nonneg h1 h2 (by omega))
  have hξ0 : 0 ≤ xiArith2 n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) (dQb149 n) (2 / 5) := by
    have h1 := xiBin2_nonneg n (σ := 2 / 5) (by norm_num) (mA n)
    have h2 := CQn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    have h3 := CEn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num)
    have h4 := C0n_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    unfold xiArith2
    positivity
  have h := arithProg150_of hn hk hξ0 hd hη₄ hη₅
  refine le_trans ?_ h
  have hxi := xiA2_le hn
  have hK : (0 : ℝ) ≤ 625 + (1 + 1 / η₄) * 235 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hxi hK
  have h2 := mul_le_mul_of_nonneg_left
    (add_le_add_left h1 ((1 + η₄) * p149 n)) (by positivity : (0 : ℝ) ≤ 1 + η₅)
  linarith only [h2]

/-- **`J = n` atoms: success at least `7/10` for every `n ≥ 16 384`, `k ≥ 100n`.** -/
theorem arithProgN150_16384 (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    7 / 10 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (1638400 : ℝ) ≤ k := by
    have : (100 * n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := arithProgN150 hn4 hk1 (η₄ := 1 / 4) (by norm_num) (η₅ := 1 / 100) (by norm_num)
  refine le_trans ?_ h
  have hp := p149_le_16384 hn
  have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (16384 * 128) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 16384 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have h3' : (3850 : ℝ) / (n : ℝ) ^ 2 = 3850 * (1 / (n : ℝ) ^ 2) := by ring
  have h3'' : (20 : ℝ) / (n : ℝ) ^ 2 = 20 * (1 / (n : ℝ) ^ 2) := by ring
  have h4 : (19 : ℝ) / k ≤ 19 / 1638400 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  have h5 : (1 : ℝ) / n ≤ 1 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  rw [h3', h3'']
  norm_num at hp h2 h3 h4 h5 ⊢
  linarith only [hp, h2, h3, h4, h5]

/-- **`J = n` atoms: success at least `99/100` for every `n ≥ 400 000`, `k ≥ n`.** -/
theorem arithProgN150_99 (hn : 400000 ≤ n) {k : ℕ} (hk : n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (400000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (632 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (400000 : ℝ) ≤ k := by
    have : (n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := arithProgN150 hn4 hk1 (η₄ := 1 / 2) (by norm_num) (η₅ := 1 / 10) (by norm_num)
  refine le_trans ?_ h
  have h1 : (1835 : ℝ) / n ≤ 1835 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1b : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ 130287 / (400000 * 632) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 400000 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have h1c : (5368347 : ℝ) / (n : ℝ) ^ 2 = 5368347 * (1 / (n : ℝ) ^ 2) := by ring
  have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (400000 * 632) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3' : (3850 : ℝ) / (n : ℝ) ^ 2 = 3850 * (1 / (n : ℝ) ^ 2) := by ring
  have h3'' : (20 : ℝ) / (n : ℝ) ^ 2 = 20 * (1 / (n : ℝ) ^ 2) := by ring
  have h4 : (19 : ℝ) / k ≤ 19 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  have h5 : (1 : ℝ) / n ≤ 1 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold p149
  rw [h3', h3'', h1c]
  norm_num at h1 h1b h2 h3 h4 h5 ⊢
  linarith only [h1, h1b, h2, h3, h4, h5]

end BstLean.Part150
