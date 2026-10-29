import BstLean.Part154App
import BstLean.Part154MFa

/-!
# Part 154: the hypotheses (M1), (M2), (M3) of Lemma MF for the first layer of `A`
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

variable {n m : ℕ}

private lemma le_of_sq_le_aux {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : 0 < a + b)]

private lemma int_pow4_aux {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : BstLean.Part148.EuLip g L) (hg : ∀ x, 0 ≤ g x) :
    Integrable (fun x => g x ^ 4) (stdGauss ι) := by
  have hc := hL.continuous hL0
  obtain ⟨h1, -⟩ := gaussConc_moment hL0 hL 2
  set e := ∫ y, g y ∂stdGauss ι with he
  have hdom : Integrable (fun x => 8 * ((max (g x - e) 0) ^ (2 * 2) + |e| ^ 4)) (stdGauss ι) :=
    (h1.add (integrable_const _)).const_mul 8
  refine hdom.mono' (hc.measurable.pow_const 4).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ha : 0 ≤ max (g x - e) 0 := le_max_right _ _
  have hb : 0 ≤ |e| := abs_nonneg e
  have hga : g x ≤ max (g x - e) 0 + |e| := by
    have h1 := le_max_left (g x - e) 0
    have h2 := le_abs_self e
    linarith
  generalize max (g x - e) 0 = a at ha hga
  generalize |e| = b at hb hga
  have h4 : g x ^ 4 ≤ (a + b) ^ 4 := pow_le_pow_left₀ (hg x) hga 4
  have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have h3 : ((a + b) ^ 2) ^ 2 ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
  have h5 : (2 * (a ^ 2 + b ^ 2)) ^ 2 ≤ 8 * (a ^ (2 * 2) + b ^ 4) := by
    have e4 : a ^ (2 * 2) = a ^ 4 := by norm_num
    rw [e4]
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have h6 : (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
  linarith

open Filter Topology in
private lemma trunc_var_aux {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : BstLean.Part148.EuLip g L) (hg : ∀ x, 0 ≤ g x) (N : ℝ) (hN : 0 ≤ N) :
    ∫ x, ((min (g x) N) ^ 2 - ∫ y, (min (g y) N) ^ 2 ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      ∫ x, 4 * L ^ 2 * g x ^ 2 ∂stdGauss ι := by
  have hLN : ∀ x y, |min (g x) N - min (g y) N| ≤ L * √(∑ i, (x i - y i) ^ 2) := by
    intro x y
    have h := abs_min_sub_min_le_max (g x) N (g y) N
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h
    exact h.trans (hL x y)
  have h0 : ∀ x, 0 ≤ min (g x) N := fun x => le_min (hg x) hN
  have hF : BstLean.Part148.EuLip (fun x => (min (g x) N) ^ 2) (2 * N * L) := by
    intro x y
    have e : (min (g x) N) ^ 2 - (min (g y) N) ^ 2 =
        (min (g x) N - min (g y) N) * (min (g x) N + min (g y) N) := by ring
    have hs : |min (g x) N + min (g y) N| ≤ 2 * N := by
      rw [abs_of_nonneg (add_nonneg (h0 x) (h0 y))]
      linarith [min_le_right (g x) N, min_le_right (g y) N]
    simp only [e, abs_mul]
    calc |min (g x) N - min (g y) N| * |min (g x) N + min (g y) N|
        ≤ (L * √(∑ i, (x i - y i) ^ 2)) * (2 * N) :=
          mul_le_mul (hLN x y) hs (abs_nonneg _) (by positivity)
      _ = 2 * N * L * √(∑ i, (x i - y i) ^ 2) := by ring
  have hΓ : Integrable (fun x => 4 * L ^ 2 * g x ^ 2) (stdGauss ι) :=
    (BstLean.Part151.lip_memLp hL0 hL).integrable_sq.const_mul _
  refine BstLean.Part151.poincare_lip_le (by positivity) hF hΓ (ae_of_all _ fun x => ?_)
  have key := BstLean.Part153.gradSq_le_of_local (f := fun x => (min (g x) N) ^ 2) (ξ := x)
    (ℓ := 2 * g x * L) ?_
  · calc _ ≤ (2 * g x * L) ^ 2 := key
      _ = 4 * L ^ 2 * g x ^ 2 := by ring
  intro δ hδ
  have hcont : Continuous fun y : ι → ℝ => L ^ 2 * √(∑ i, (y i - x i) ^ 2) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => ((continuous_apply i).sub continuous_const).pow 2))
  have hev : ∀ᶠ y in 𝓝 x, L ^ 2 * √(∑ i, (y i - x i) ^ 2) < δ := by
    refine Filter.Tendsto.eventually_lt_const ?_ (hcont.tendsto x)
    simpa using hδ
  filter_upwards [hev] with y hy
  have hab := hLN y x
  have hd0 : 0 ≤ √(∑ i, (y i - x i) ^ 2) := Real.sqrt_nonneg _
  generalize √(∑ i, (y i - x i) ^ 2) = d at hy hab hd0
  have hbx : min (g x) N ≤ g x := min_le_left _ _
  have ha0 := h0 y
  have hb0 := h0 x
  generalize min (g y) N = a at hab ha0
  generalize min (g x) N = b at hab hb0 hbx
  have e : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg ha0 hb0)]
  have h1 : |a - b| * (a + b) ≤ (L * d) * (2 * g x + L * d) :=
    mul_le_mul hab (by linarith [le_abs_self (a - b)]) (add_nonneg ha0 hb0) (by positivity)
  have h2 : L ^ 2 * d * d ≤ δ * d := mul_le_mul_of_nonneg_right hy.le hd0
  have e2 : (L * d) * (2 * g x + L * d) = 2 * g x * L * d + L ^ 2 * d * d := by ring
  have e3 : (2 * g x * L + δ) * d = 2 * g x * L * d + δ * d := by ring
  linarith

private lemma inv_sqrt2_le_aux {ϱ : ℝ} (h : ϱ < 1 / 4) : 1 / √2 ≤ √(1 - 2 * ϱ) := by
  rw [Real.le_sqrt' (by positivity), div_pow, Real.sq_sqrt (by norm_num)]
  linarith

private lemma proj_contr_aux (b u : Fin m → ℝ) (γ : ℝ) (hγ : γ * normSq b = u ⬝ᵥ b) :
    normSq (u - γ • b) ≤ normSq u := by
  have e : u - γ • b = u + (-γ) • b := by rw [neg_smul, sub_eq_add_neg]
  rw [e, normSq_add', dotProduct_smul, smul_eq_mul, normSq_smul, ← hγ]
  nlinarith [mul_nonneg (sq_nonneg γ) (normSq_nonneg b)]

/-- For a nonnegative `L`-Lipschitz function `g` of a standard Gaussian vector:
`Var(g²) ≤ 4L²·E g²` (the Poincaré inequality for the locally Lipschitz function `g²`). -/
theorem var_sq_le_of_lip {ι : Type} [Fintype ι] [DecidableEq ι] {g : (ι → ℝ) → ℝ} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : BstLean.Part148.EuLip g L) (hg : ∀ x, 0 ≤ g x) :
    Integrable (fun x => g x ^ 4) (stdGauss ι) ∧
    ∫ x, (g x ^ 2 - ∫ y, g y ^ 2 ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      4 * L ^ 2 * ∫ x, g x ^ 2 ∂stdGauss ι := by
  have hμ : IsProbabilityMeasure (stdGauss ι) := inferInstance
  have hc := hL.continuous hL0
  have h4 := int_pow4_aux hL0 hL hg
  have h2 : Integrable (fun x => g x ^ 2) (stdGauss ι) :=
    (BstLean.Part151.lip_memLp hL0 hL).integrable_sq
  refine ⟨h4, ?_⟩
  set c := ∫ y, g y ^ 2 ∂stdGauss ι with hcdef
  have hc0 : 0 ≤ c := integral_nonneg fun x => sq_nonneg _
  have hpt : ∀ x, ∀ᶠ k : ℕ in Filter.atTop, min (g x) (k : ℝ) = g x := fun x => by
    filter_upwards [Filter.eventually_ge_atTop ⌈g x⌉₊] with k hk
    exact min_eq_left ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  have hmeas : ∀ k : ℕ, Measurable fun x => (min (g x) (k : ℝ)) ^ 2 := fun k =>
    (hc.measurable.min measurable_const).pow_const 2
  have hle : ∀ (k : ℕ) x, (min (g x) (k : ℝ)) ^ 2 ≤ g x ^ 2 := fun k x =>
    pow_le_pow_left₀ (le_min (hg x) (Nat.cast_nonneg k)) (min_le_left _ _) 2
  have hlim : ∀ x, Filter.Tendsto (fun k : ℕ => (min (g x) (k : ℝ)) ^ 2) Filter.atTop
      (nhds (g x ^ 2)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpt x] with k hk
    rw [hk]
  have T1 : Filter.Tendsto (fun k : ℕ => ∫ x, (min (g x) (k : ℝ)) ^ 2 ∂stdGauss ι) Filter.atTop
      (nhds c) := by
    refine tendsto_integral_of_dominated_convergence (fun x => g x ^ 2)
      (fun k => (hmeas k).aestronglyMeasurable) h2 (fun k => ae_of_all _ fun x => ?_)
      (ae_of_all _ hlim)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle k x
  have hcN0 : ∀ k : ℕ, 0 ≤ ∫ x, (min (g x) (k : ℝ)) ^ 2 ∂stdGauss ι := fun k =>
    integral_nonneg fun x => sq_nonneg _
  have hcNle : ∀ k : ℕ, ∫ x, (min (g x) (k : ℝ)) ^ 2 ∂stdGauss ι ≤ c := fun k =>
    integral_mono (h2.mono' (hmeas k).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle k x)) h2 (hle k)
  have hbd : Integrable (fun x => (g x ^ 2 + c) ^ 2) (stdGauss ι) := by
    have e : ∀ x, (g x ^ 2 + c) ^ 2 = g x ^ 4 + 2 * c * g x ^ 2 + c ^ 2 := fun x => by ring
    simp only [e]
    exact (h4.add (h2.const_mul _)).add (integrable_const _)
  have T2 : Filter.Tendsto (fun k : ℕ => ∫ x, ((min (g x) (k : ℝ)) ^ 2 -
      ∫ y, (min (g y) (k : ℝ)) ^ 2 ∂stdGauss ι) ^ 2 ∂stdGauss ι) Filter.atTop
      (nhds (∫ x, (g x ^ 2 - c) ^ 2 ∂stdGauss ι)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (g x ^ 2 + c) ^ 2)
      (fun k => (((hmeas k).sub measurable_const).pow_const 2).aestronglyMeasurable) hbd
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ((hlim x).sub T1).pow 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have a1 := hle k x
    have a2 : (0 : ℝ) ≤ (min (g x) (k : ℝ)) ^ 2 := sq_nonneg _
    have a3 := hcN0 k
    have a4 := hcNle k
    exact sq_le_sq' (by linarith) (by linarith)
  have hfin := le_of_tendsto' T2 fun k : ℕ => trunc_var_aux hL0 hL hg (k : ℝ) (Nat.cast_nonneg k)
  rwa [integral_const_mul] at hfin

/-- `π̄` is nondecreasing on `(0, 1/4)`. -/
theorem piBar_mono {ϱ ϱ' : ℝ} (h0 : 0 < ϱ) (h : ϱ ≤ ϱ') (h1 : ϱ' < 1 / 4) :
    piBar ϱ ≤ piBar ϱ' := by
  unfold piBar
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h12 := inv_sqrt2_le_aux h1
  have hmono : √(1 - 2 * ϱ') ≤ √(1 - 2 * ϱ) := Real.sqrt_le_sqrt (by linarith)
  exact div_le_div₀ (sq_nonneg _)
    (pow_le_pow_left₀ (sub_nonneg.2 h12) (by linarith) 2) (by linarith) (by linarith)

theorem piBar_le_one {ϱ : ℝ} (h0 : 0 < ϱ) : piBar ϱ ≤ 1 := by
  unfold piBar
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (sq_nonneg _) (by linarith)))

theorem piBar_nonneg (ϱ : ℝ) : 0 ≤ piBar ϱ := by
  exact (Real.exp_pos _).le

/-- **The hypotheses of Lemma MF hold for `fA`** with every `ℓ` such that
`t·τ²·opN(A₁)² ≤ ℓ²`, `ϱ = ℓ²/s_h² < 1/4`, and every `π_g ≥ π̄(ϱ)`. -/
theorem MFHyp_fA (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ ℓ : ℝ}
    (hτ : 0 < τ) (hℓ : 0 < ℓ) (hop : 2 / (m : ℝ) * τ ^ 2 * opN A₁ ^ 2 ≤ ℓ ^ 2)
    (hs : 0 < sO2 A₁ c τ) (hϱ : ℓ ^ 2 / sO2 A₁ c τ < 1 / 4) {πg : ℝ}
    (hπ : piBar (ℓ ^ 2 / sO2 A₁ c τ) ≤ πg) (hπ1 : πg ≤ 1) :
    MFHyp (stdGauss (Fin n)) (fA A₁ c τ) ℓ πg := by
  have hμ : IsProbabilityMeasure (stdGauss (Fin n)) := inferInstance
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hG : 0 < GamBarF (stdGauss (Fin n)) (fA A₁ c τ) := by
    rw [GamBarF_fA]
    exact mul_pos (by positivity) (hO_pos_of_sO2 hm A₁ c hτ hs)
  have hsF : sF2 (stdGauss (Fin n)) (fA A₁ c τ) = sO2 A₁ c τ := sF2_fA hm A₁ c τ
  have hM1 : ∀ w : Fin m → ℝ, ∫ ω, (w ⬝ᵥ fA A₁ c τ ω -
      w ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 ∂stdGauss (Fin n) ≤ ℓ ^ 2 * normSq w :=
    fun w => (M1_fA A₁ c τ w).trans (mul_le_mul_of_nonneg_right hop (normSq_nonneg w))
  -- `ς` is Lipschitz
  have hς2 : ∀ ξ, nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) ^ 2 =
      sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ := fun ξ => BstLean.Part153.nrm_sq _
  have hℓ0 : √(2 / (m : ℝ)) * (|τ| * opN A₁) ≤ ℓ := by
    refine le_of_sq_le_aux hℓ.le ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    linarith
  have hLip : BstLean.Part148.EuLip
      (fun ξ => nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ)) ℓ := by
    intro ξ ξ'
    set fb := fbar (stdGauss (Fin n)) (fA A₁ c τ) with hfb
    set G := GamBarF (stdGauss (Fin n)) (fA A₁ c τ) with hGd
    have hNb : normSq fb = G := rfl
    have e0 : gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ' =
        (fA A₁ c τ ξ - fA A₁ c τ ξ') -
          (betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ - betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ') •
            fb := by
      simp only [gF]
      rw [sub_smul]
      abel
    have hγ : (betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ -
        betaF (stdGauss (Fin n)) (fA A₁ c τ) ξ') * normSq fb =
        (fA A₁ c τ ξ - fA A₁ c τ ξ') ⬝ᵥ fb := by
      rw [hNb, sub_dotProduct]
      simp only [betaF]
      rw [← hfb, ← hGd]
      field_simp
    have h1 : nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ') ≤
        nrm (fA A₁ c τ ξ - fA A₁ c τ ξ') := by
      rw [e0]
      exact Real.sqrt_le_sqrt (proj_contr_aux _ _ _ hγ)
    have e1 : fA A₁ c τ ξ - fA A₁ c τ ξ' =
        √(2 / (m : ℝ)) • (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
      simp only [fA]
      rw [smul_sub]
    have e2 : A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ') = A₁ *ᵥ (τ • (ξ - ξ')) := by
      rw [← Matrix.mulVec_sub]
      congr 1
      rw [smul_sub]
      abel
    have e3 : √(∑ i, (ξ i - ξ' i) ^ 2) = nrm (ξ - ξ') := rfl
    rw [e3]
    calc |nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ')|
        ≤ nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ - gF (stdGauss (Fin n)) (fA A₁ c τ) ξ') :=
          BstLean.Part153.abs_nrm_sub_le _ _
      _ ≤ nrm (fA A₁ c τ ξ - fA A₁ c τ ξ') := h1
      _ = √(2 / (m : ℝ)) * nrm (reluV (A₁ *ᵥ (c + τ • ξ)) - reluV (A₁ *ᵥ (c + τ • ξ'))) := by
          rw [e1, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (c + τ • ξ) - A₁ *ᵥ (c + τ • ξ')) :=
          mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_reluV_sub_le _ _) (Real.sqrt_nonneg _)
      _ = √(2 / (m : ℝ)) * nrm (A₁ *ᵥ (τ • (ξ - ξ'))) := by rw [e2]
      _ ≤ √(2 / (m : ℝ)) * (opN A₁ * nrm (τ • (ξ - ξ'))) :=
          mul_le_mul_of_nonneg_left (BstLean.Part153.nrm_mulVec_le _ _) (Real.sqrt_nonneg _)
      _ = √(2 / (m : ℝ)) * (|τ| * opN A₁) * nrm (ξ - ξ') := by
          rw [BstLean.Part153.nrm_smul]; ring
      _ ≤ ℓ * nrm (ξ - ξ') := mul_le_mul_of_nonneg_right hℓ0 (BstLean.Part153.nrm_nonneg _)
  have hM2 : ∫ ω, (sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω -
      ∫ ω', sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω' ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      4 * ℓ ^ 2 * ∫ ω, sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω ∂stdGauss (Fin n) := by
    have h := (var_sq_le_of_lip hℓ.le hLip (fun ξ => BstLean.Part153.nrm_nonneg _)).2
    simp only [hς2] at h
    exact h
  have H1 : MFHyp (stdGauss (Fin n)) (fA A₁ c τ) ℓ 1 :=
    ⟨measurable_fA A₁ c τ, integrable_fA4 A₁ c τ, hG, hsF ▸ hs, hℓ, zero_le_one, le_rfl, hM1, hM2,
      measureReal_le_one⟩
  refine ⟨measurable_fA A₁ c τ, integrable_fA4 A₁ c τ, hG, hsF ▸ hs, hℓ,
    (piBar_nonneg _).trans hπ, hπ1, hM1, hM2, ?_⟩
  refine le_trans ?_ hπ
  obtain ⟨_, _, _, hd0, hd1⟩ := H1.F1
  obtain ⟨hsi, hsv⟩ := H1.F2
  obtain ⟨hςi', _, _⟩ := H1.sig_int
  have hςi : Integrable (fun ξ => nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ)) (stdGauss (Fin n)) :=
    hςi'
  obtain ⟨hvi, hvar⟩ := gaussVar_le_sharp hℓ.le hLip
  rw [hsF] at hsv ⊢
  set s2 := sO2 A₁ c τ with hs2
  set e := ∫ ξ, nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) ∂stdGauss (Fin n) with he
  set E2 := ∫ ω, sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω ∂stdGauss (Fin n) with hE2
  have he0 : 0 ≤ e := integral_nonneg fun ξ => BstLean.Part153.nrm_nonneg _
  have hvar_eq : ∫ ξ, (nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - e) ^ 2 ∂stdGauss (Fin n) =
      E2 - e ^ 2 := by
    have ex : ∀ ξ, (nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) - e) ^ 2 =
        sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ -
          2 * e * nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) + e ^ 2 := fun ξ => by
      rw [← hς2]; ring
    simp only [ex]
    have hA : Integrable (fun ξ => sig2F (stdGauss (Fin n)) (fA A₁ c τ) ξ -
        2 * e * nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ)) (stdGauss (Fin n)) :=
      hsi.sub (hςi.const_mul _)
    rw [integral_add hA (integrable_const _),
      integral_sub hsi (hςi.const_mul _), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    rw [← he, ← hE2]
    ring
  rw [hvar_eq] at hvar
  set ϱ := ℓ ^ 2 / s2 with hϱd
  have hℓϱ : ℓ ^ 2 = ϱ * s2 := by rw [hϱd, div_mul_cancel₀ _ hs.ne']
  have hs0 : 0 < √s2 := Real.sqrt_pos.2 hs
  have hssq : √s2 ^ 2 = s2 := Real.sq_sqrt hs.le
  have hr0 : 0 ≤ 1 - 2 * ϱ := by linarith
  have hrsq : √(1 - 2 * ϱ) ^ 2 = 1 - 2 * ϱ := Real.sq_sqrt hr0
  have h12 := inv_sqrt2_le_aux hϱ
  have hsr : √s2 * √(1 - 2 * ϱ) ≤ e := by
    refine le_of_sq_le_aux he0 ?_
    rw [mul_pow, hssq, hrsq]
    nlinarith
  set t₀ := √s2 * (√(1 - 2 * ϱ) - 1 / √2) with ht₀
  have ht0 : 0 ≤ t₀ := mul_nonneg hs0.le (sub_nonneg.2 h12)
  have hsub : {ω | sig2F (stdGauss (Fin n)) (fA A₁ c τ) ω < s2 / 2} ⊆
      {ξ | nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) ≤ e - t₀} := by
    intro ξ hξ
    simp only [Set.mem_ofPred_eq] at hξ ⊢
    have h1 : nrm (gF (stdGauss (Fin n)) (fA A₁ c τ) ξ) < √(s2 / 2) :=
      Real.sqrt_lt_sqrt (sig2F_nonneg _ _ _) hξ
    rw [Real.sqrt_div hs.le] at h1
    have e4 : e - t₀ = e - √s2 * √(1 - 2 * ϱ) + √s2 / √2 := by rw [ht₀]; ring
    rw [e4]
    linarith
  refine (measureReal_mono hsub).trans ((gaussConc_lower_sharp hℓ.le hLip ht0).trans (le_of_eq ?_))
  unfold piBar
  congr 1
  rw [ht₀, mul_pow, hssq, hℓϱ]
  have hϱ0 : ϱ ≠ 0 := by
    rw [hϱd]; exact (div_pos (pow_pos hℓ 2) hs).ne'
  generalize (√(1 - 2 * ϱ) - 1 / √2) = q
  field_simp

end BstLean.Part154
