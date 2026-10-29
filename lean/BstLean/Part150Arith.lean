import BstLean.Part150NormB
import BstLean.Part150Bin
import BstLean.Part150DispNum

/-!
# Part 150, item 5: the displacement of the ARITHMETIC centre from the oracle centre of Part 149

Role: `delegations/statements/p150-spec.md`, item 5.

* `bTW J (W, (A₁, A₂)) = bT J J A₁ A₂ ĉ τ̃₀ / ρ` (`ĉ = cenA W`, `τ̃₀ = tauWA W`,
  `ρ = rhoC ĉ τ̃₀`): the arithmetic centre of the paper's program `P45` (binomial sums with
  `J + 1` atoms in both layers; no oracle).
* `arith_inner`, **`arith_dispOK`**: `E[1_good·|bTW − bMF|²] ≤ (m/n)·xiArith`, with
  `xiArith = 2·xiBin J + 2·(CQn·dQb² + CEn·5/m + C0n)`: the binomial part (`Part150Bin`) and the
  normalization part (`Part150NormB`: the paper's oracle centre has no normalization of the
  stand-in input to the sphere; the oracle centre of Part 149 has).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part141 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- **The arithmetic centre** of the last hidden layer of `A`: `bT/ρ`. -/
noncomputable def bTW (J : ℕ) : CMap n := fun x =>
  (1 / rhoC (cenA x.1) (tauWA x.1)) • bT J J x.2.1 x.2.2 (cenA x.1) (tauWA x.1)

lemma measurable_bTW (J : ℕ) : Measurable (bTW (n := n) J) := by
  have h1 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      bT J J x.2.1 x.2.2 (cenA x.1) (tauWA x.1)) := by
    have h := (measurable_bT (n := n) (m := mA n) J J).comp measurable_cτθ
    simp only [Function.comp_def] at h
    exact h
  have h0 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      (cenA x.1, tauWA x.1)) :=
    (measurable_cenA.comp measurable_fst).prodMk (measurable_tauWA.comp measurable_fst)
  have h3 := (measurable_rhoC (n := n)).comp h0
  simp only [Function.comp_def] at h3
  have h2 : Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
      1 / rhoC (cenA x.1) (tauWA x.1)) := measurable_const.div h3
  rw [measurable_pi_iff]
  intro j
  show Measurable (fun x : MlpParam (2 * n) (mW n) n × HidParam n (mA n) =>
    1 / rhoC (cenA x.1) (tauWA x.1) * bT J J x.2.1 x.2.2 (cenA x.1) (tauWA x.1) j)
  exact h2.mul ((measurable_pi_apply j).comp h1)

lemma normSq_add_le2 {m : ℕ} (u v : Fin m → ℝ) : normSq (u + v) ≤ 2 * normSq u + 2 * normSq v := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Pi.add_apply]
  nlinarith only [sq_nonneg (u j - v j)]

/-- The constant of the displacement of the arithmetic centre. -/
noncomputable def xiArith (n J : ℕ) (εD εQ lam dQb : ℝ) : ℝ :=
  2 * xiBin J + 2 * (CQn n εD εQ lam * dQb ^ 2 + CEn n εD εQ * (5 / (mA n : ℝ)) + C0n n εD εQ lam)

lemma CQn_nonneg {n : ℕ} {εD εQ lam : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hlam : 0 < lam) : 0 ≤ CQn n εD εQ lam := by
  have h1 : 0 < 1 - εD := by linarith
  have := Real.pi_pos
  unfold CQn; positivity

lemma CEn_nonneg {n : ℕ} {εD εQ : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ) :
    0 ≤ CEn n εD εQ := by
  have h1 : 0 < 1 - εD := by linarith
  have := Real.pi_pos
  unfold CEn; positivity

lemma C0n_nonneg {n : ℕ} {εD εQ lam : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hlam : 0 < lam) : 0 ≤ C0n n εD εQ lam := by
  have h1 : 0 < 1 - εD := by linarith
  have := Real.pi_pos
  unfold C0n; positivity

/-- The binomial part, in mean over `(A₁, A₂)`. -/
lemma arith_bin_part {m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ θ : HidParam n m, ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
        (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ))) ∂hidGauss n m ≤
      ENNReal.ofReal (2 * ((m : ℝ) / n * xiBin J)) := by
  have e0 : hidGauss n m = (gaussMat m n (2 / (n : ℝ))).prod (gaussMat m m (2 / (m : ℝ))) := rfl
  have h0 : Measurable (fun θ : HidParam n m => ((c, τ), θ)) :=
    measurable_const.prodMk measurable_id
  have hX : Measurable (fun θ : HidParam n m => normSq ((1 / rhoC c τ) •
      (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ))) := by
    have h := (measurable_binDispX (n := n) (m := m) J).comp h0
    simp only [Function.comp_def] at h
    exact h
  have mg1 : Measurable (fun θ : HidParam n m => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
      (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ)))) :=
    ENNReal.measurable_ofReal.comp (hX.const_mul 2)
  have mX : Measurable (fun θ : HidParam n m => ENNReal.ofReal (normSq ((1 / rhoC c τ) •
      (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ)))) := ENNReal.measurable_ofReal.comp hX
  have e : ∀ θ : HidParam n m, ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) •
      (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ))) = ENNReal.ofReal 2 *
        ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J θ.1 θ.2 c τ - bO θ.1 θ.2 c τ))) :=
    fun θ => ENNReal.ofReal_mul (by norm_num)
  simp_rw [e]
  rw [lintegral_const_mul _ mX, e0, lintegral_prod _ mX.aemeasurable]
  refine (mul_le_mul' le_rfl (bin_disp_mean hn hm hJ c hτ)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]

/-- The normalization part, in mean over `(A₁, A₂)`, on the good event of `A₁`. -/
lemma arith_norm_part {m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {k εD εQ lam : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hεD0 : 0 ≤ εD) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : k * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD)) (hlam : 0 < lam) :
    ∫⁻ θ : HidParam n m,
        ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
            Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
          (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) • bO θ.1 θ.2 c τ - bMF c τ θ)))
          θ.1 ∂hidGauss n m ≤
      ENNReal.ofReal (2 * CQn n εD εQ lam / ((m : ℝ) / n)) *
          ∫⁻ A₁, ENNReal.ofReal (Qk k c τ A₁) ∂gaussMat m n (2 / (n : ℝ)) +
        (ENNReal.ofReal (2 * CEn n εD εQ / ((m : ℝ) / n)) *
            ∫⁻ A₁, ENNReal.ofReal (errD1 c τ A₁) ∂gaussMat m n (2 / (n : ℝ)) +
          ENNReal.ofReal (2 * ((m : ℝ) / n * C0n n εD εQ lam))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < (m : ℝ) / n := by positivity
  have hCQ := CQn_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have hCE := CEn_nonneg (n := n) hεD0 hεD1 hεQ0
  have hC0 := C0n_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have e0 : hidGauss n m = (gaussMat m n (2 / (n : ℝ))).prod (gaussMat m m (2 / (m : ℝ))) := rfl
  have mQ : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => ENNReal.ofReal (Qk k c τ A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => ((k, c, τ), A₁)) :=
      measurable_const.prodMk measurable_id
    have h2 := (measurable_Qk (n := n) (m := m)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have mD : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      ENNReal.ofReal (errD1 c τ A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => ((c, τ), A₁)) :=
      measurable_const.prodMk measurable_id
    have h2 := (measurable_errD1 (n := n) (m := m)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have key : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ,
      ∫⁻ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ -
              bMF c τ (A₁, A₂)))) A₁ ∂gaussMat m m (2 / (m : ℝ)) ≤
        ENNReal.ofReal (2 * CQn n εD εQ lam / ((m : ℝ) / n)) * ENNReal.ofReal (Qk k c τ A₁) +
          (ENNReal.ofReal (2 * CEn n εD εQ / ((m : ℝ) / n)) * ENNReal.ofReal (errD1 c τ A₁) +
            ENNReal.ofReal (2 * ((m : ℝ) / n * C0n n εD εQ lam))) := by
    intro A₁
    have hQ0 : 0 ≤ Qk k c τ A₁ := integral_nonneg fun _ => sq_nonneg _
    have hD0 : 0 ≤ errD1 c τ A₁ := integral_nonneg fun _ => sq_nonneg _
    by_cases hA : errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
        Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2
    · have e : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ -
              bMF c τ (A₁, A₂)))) A₁ =
          ENNReal.ofReal 2 * ENNReal.ofReal
            (normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ - bMF c τ (A₁, A₂))) := by
        intro A₂
        rw [Set.indicator_of_mem (by exact hA), ENNReal.ofReal_mul (by norm_num)]
      simp_rw [e]
      have h := normII_fixed hn hm c hτ A₁ hk0 hk1 hεD0 hεD1 hεQ0 hcond hlam hA.1 hA.2
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine (mul_le_mul' le_rfl h).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    · have e : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
          ({A₁ : Matrix (Fin m) (Fin n) ℝ | errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2 ∧
              Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2}).indicator
            (fun _ => ENNReal.ofReal (2 * normSq ((1 / rhoC c τ) • bO A₁ A₂ c τ -
              bMF c τ (A₁, A₂)))) A₁ = 0 := by
        intro A₂
        rw [Set.indicator_of_notMem (by exact hA)]
      simp_rw [e]
      simp
  rw [e0]
  refine (lintegral_prod_le _).trans ?_
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_add_left (mQ.const_mul _), lintegral_add_left (mD.const_mul _),
    lintegral_const_mul _ mQ, lintegral_const_mul _ mD]
  simp

/-- The mean over `(A₁, A₂)` of the displacement, for a fixed `W`. -/
lemma arith_inner (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {εD εQ lam : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : 62714 / 100000 * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hlam : 0 < lam) {J : ℕ} (hJ : 1 ≤ J) (W : MlpParam (2 * n) (mW n) n) :
    ∫⁻ θ, (goodX1 G εD εQ).indicator (fun x => ENNReal.ofReal (dispH (bTW J) x)) (W, θ)
        ∂hidGauss n (mA n) ≤
      (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin J)) +
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
  have hb1 := arith_bin_part (m := mA n) hn1 hmA hJ (cenA W) hτ'
  have hb2 := arith_norm_part (m := mA n) hn1 hmA (cenA W) hτ' hkq0
    (hkq1.trans (by norm_num)) hεD0 hεD1 hεQ0 hcond' hlam
  have mQ : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((kappa (qTh (W.1, W.2.1)), cenA W, tauWA W), A₁)) :=
      measurable_const.prodMk measurable_id
    have h2 := (measurable_Qk (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have mD : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
      ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ =>
        ((cenA W, tauWA W), A₁)) := measurable_const.prodMk measurable_id
    have h2 := (measurable_errD1 (n := n) (m := mA n)).comp h0
    simp only [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp h2
  have eq1 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mQ
  have eq2 : ∫⁻ θ : HidParam n (mA n), ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) =
      ∫⁻ A₁, ENNReal.ofReal (errD1 (cenA W) (tauWA W) A₁)
        ∂gaussMat (mA n) n (2 / (n : ℝ)) := lint_hid_fst mD
  rw [eq1, eq2]
  have h0 : Measurable (fun θ : HidParam n (mA n) => ((cenA W, tauWA W), θ)) :=
    measurable_const.prodMk measurable_id
  have mg1 : Measurable (fun θ : HidParam n (mA n) => ENNReal.ofReal (2 * normSq
      ((1 / rhoC (cenA W) (tauWA W)) •
        (bT J J θ.1 θ.2 (cenA W) (tauWA W) - bO θ.1 θ.2 (cenA W) (tauWA W))))) := by
    have h := (measurable_binDispX (n := n) (m := mA n) J).comp h0
    simp only [Function.comp_def] at h
    exact ENNReal.measurable_ofReal.comp (h.const_mul 2)
  refine le_trans ?_ (add_le_add hb1 hb2)
  rw [← lintegral_add_left mg1]
  refine lintegral_mono fun θ => ?_
  by_cases hθ : errD1 (cenA W) (tauWA W) θ.1 ≤ ((mA n : ℝ) / n * εD) ^ 2 ∧
      Qk (kappa (qTh (W.1, W.2.1))) (cenA W) (tauWA W) θ.1 ≤ ((mA n : ℝ) / n * εQ) ^ 2
  · have h1 : (W, θ) ∈ goodX1 G εD εQ := ⟨hW, hθ.1, hθ.2⟩
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem (by exact hθ)]
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

/-- **The displacement of the arithmetic centre from the oracle centre of Part 149, in mean on
the good event**: `E[1_good·|bTW − bMF|²] ≤ (m/n)·xiArith`. -/
theorem arith_dispOK (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {alo ahi : ℝ} (hwin : WinOK2 n G alo ahi) {εD εQ lam : ℝ} (hεD0 : 0 ≤ εD) (hεD1 : εD < 1)
    (hεQ0 : 0 ≤ εQ) (hcond : 62714 / 100000 * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hlam : 0 < lam) {J : ℕ} (hJ : 1 ≤ J) {dQb : ℝ}
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q) :
    DispOK n G εD εQ (bTW J) (xiArith n J εD εQ lam dQb) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmAR : (0 : ℝ) < mA n := by exact_mod_cast hmA
  have hd0 : (0 : ℝ) < (mA n : ℝ) / n := by positivity
  have hCQ := CQn_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have hCE := CEn_nonneg (n := n) hεD0 hεD1 hεQ0
  have hC0 := C0n_nonneg (n := n) hεD0 hεD1 hεQ0 hlam
  have hxb := xiBin_nonneg J
  have mGW := goodWAG0_meas hG hn1
  have mIQ : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_qkW).lintegral_prod_right'
  have mID : Measurable (fun W : MlpParam (2 * n) (mW n) n =>
      ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n)) :=
    (ENNReal.measurable_ofReal.comp measurable_d1W).lintegral_prod_right'
  unfold DispOK
  refine (lintegral_mono fun W => arith_inner hn hwin hεD0 hεD1 hεQ0 hcond hlam hJ W).trans ?_
  have e : ∀ W : MlpParam (2 * n) (mW n) n, (goodWAG G).indicator (fun W =>
        ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin J)) +
          (ENNReal.ofReal (2 * CQn n εD εQ lam / ((mA n : ℝ) / n)) *
              ∫⁻ θ, ENNReal.ofReal (qkW W θ) ∂hidGauss n (mA n) +
            (ENNReal.ofReal (2 * CEn n εD εQ / ((mA n : ℝ) / n)) *
                ∫⁻ θ, ENNReal.ofReal (d1W W θ) ∂hidGauss n (mA n) +
              ENNReal.ofReal (2 * ((mA n : ℝ) / n * C0n n εD εQ lam))))) W ≤
      ENNReal.ofReal (2 * ((mA n : ℝ) / n * xiBin J)) +
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
  unfold xiArith
  field_simp
  ring

end BstLean.Part150

open BstLean.Part150 in
#print axioms arith_dispOK
