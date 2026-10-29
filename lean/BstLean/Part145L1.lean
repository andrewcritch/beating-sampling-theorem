import BstLean.Part143Var2
import BstLean.Part143HidC2

/-!
# Part 145 (pointwise frame constant), file 1: the window event and the pointwise frame bound

Parts 136 to 145 bound the frame constant of the computed centre `b̂` by its supremum on a good
event. This file gives the frame constant as an explicit function of `θ = (M₁, M₂)`.

Notation: `N = 2n`, `m = mW n`, `S0 = m/N`, `γ = 2/N`.

* `Gwin n`: the window event `0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. `Gwin_compl`:
  `Pr((Gwin n)ᶜ) ≤ cW/m`, `cW = 15640`. `Gwin_compl_n`: `Pr((Gwin n)ᶜ) ≤ (cW/2³⁰)/n`.
* `covX`: the frame bound of the centred hidden features for EVERY `θ` (the proof of
  `cov_of_good` of Part 140 with `√(errK θ)` in the place of the threshold of the good event).
* `cDet n`, `LfX s ε₁ ε₂ n θ`: the pointwise frame constant.
* `frameX_gen`: the pointwise frame bound for general `N`, `m`, without the cap `min 1`.
* **`frameLfX`**: for `θ ∈ Gwin n`: `E_u ⟨ê(u), w⟩² ≤ (LfX s ε₁ ε₂ n θ/n)·|w|²`.
* `LfX_meas`, `LfX_nonneg`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142
open BstLean.Part143

/-! ## The window event -/

/-- **The window event**: `0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. -/
def Gwin (n : ℕ) : Set (HidParam (2 * n) (mW n)) :=
  {θ | 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
       Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)}

lemma Gwin_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (Gwin n) :=
  (measurableSet_le measurable_const (measurable_Bh (by omega))).inter
    (measurableSet_le (measurable_Bh (by omega)) measurable_const)

/-- The constant of the window event: `2.944/0.01372² ≤ 15640`. -/
noncomputable def cW : ℝ := 15640

/-- **The probability of the window event**: `Pr((Gwin n)ᶜ) ≤ 15640/m_W`. -/
theorem Gwin_compl {n : ℕ} (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ cW / (mW n : ℝ) := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  have h := bhatNorm_L2_143 (N := 2 * n) (m := mW n) hN hm
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 2 / ((2 * n : ℕ) : ℝ) := ⟨_, rfl⟩
  have hγpos : 0 < γ := by rw [hγ]; positivity
  rw [← hγ] at h
  set ε : ℝ := γ * (1372 / 100000) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss (2 * n) (mW n))
    (f := fun θ => (Bh (2 * n) (mW n) θ - γ * kap1 (2 * n)) ^ 2)
    (Filter.Eventually.of_forall fun θ => sq_nonneg _) h.int_sq (ε ^ 2)
  have hsub : (Gwin n)ᶜ ⊆
      {θ | ε ^ 2 ≤ (Bh (2 * n) (mW n) θ - γ * kap1 (2 * n)) ^ 2} := by
    intro θ hθ
    simp only [Gwin, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le, ← hγ] at hθ
    change ε ^ 2 ≤ (Bh (2 * n) (mW n) θ - γ * kap1 (2 * n)) ^ 2
    have hg1 : γ * (49372 / 100000) ≤ γ * kap1 (2 * n) := mul_le_mul_of_nonneg_left hk1 hγpos.le
    have hg2 : γ * kap1 (2 * n) ≤ γ * (4938 / 10000) := mul_le_mul_of_nonneg_left hk2 hγpos.le
    rw [← sq_abs (Bh (2 * n) (mW n) θ - γ * kap1 (2 * n))]
    refine pow_le_pow_left₀ hεpos.le ?_ 2
    rcases hθ with hθ | hθ
    · rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      rw [hε]
      linarith
    · refine le_trans ?_ (le_abs_self _)
      rw [hε]
      linarith
  have hmono := measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)
  have h6 : ε ^ 2 * (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤
      (γ * cB143 (2 * n) (mW n)) ^ 2 :=
    (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans (hmk.trans h.le)
  have hcB := cB143_sq_le (N := 2 * n) (m := mW n) (by omega) hmM
  have h7 : γ ^ 2 * ((1372 / 100000) ^ 2 * (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ) ≤
      γ ^ 2 * (2944 / 1000 / (mW n : ℝ)) := by
    have e1 : γ ^ 2 * ((1372 / 100000) ^ 2 * (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ) =
        ε ^ 2 * (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ := by rw [hε]; ring
    rw [e1]
    refine h6.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hcB (sq_nonneg _)
  have h8 := le_of_mul_le_mul_left h7 (by positivity : (0 : ℝ) < γ ^ 2)
  have h9 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤
      2944 / 1000 / (mW n : ℝ) / (1372 / 100000) ^ 2 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  refine h9.trans ?_
  unfold cW
  rw [div_right_comm]
  exact div_le_div_of_nonneg_right (by norm_num) hmpos.le

/-- The window event in units of `1/n`: `Pr((Gwin n)ᶜ) ≤ (15640/2³⁰)/n`, about `0.0000146/n`. -/
theorem Gwin_compl_n {n : ℕ} (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ cW / 1073741824 / (n : ℝ) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hρ := nsq_div_mW_le hn
  refine (Gwin_compl hn).trans ?_
  have hm2 : 1073741824 * (n : ℝ) ≤ mW n := by
    rw [div_le_iff₀ hmpos] at hρ
    have h1 : (n : ℝ) ^ 2 * (64 * (n : ℝ)) ≤ mW n := by
      have := mul_le_mul_of_nonneg_right hρ (by positivity : (0 : ℝ) ≤ 64 * (n : ℝ))
      refine this.trans (le_of_eq ?_)
      field_simp
    have h2 : (4096 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hn' 2
    nlinarith
  have hcW : (0 : ℝ) ≤ cW := by unfold cW; norm_num
  rw [div_div]
  exact div_le_div_of_nonneg_left hcW (by positivity) hm2

/-! ## The centred features, for every `θ` -/

section cov

variable {N m : ℕ}

/-- **The frame bound of the centred hidden features, for every `θ`** (`cov_of_good` of Part 140
with `√(errK θ)` in the place of the threshold of the good event):
`E_u ⟨h(u) − h̄, w⟩² ≤ (m/N)·(b/N + 2c₂/(N(N + 2)) + √(errK θ)/(m/N) + η√3/N +
K₃√(15/(N(N+2)(N+4))))·|w|²`. -/
theorem covX (hN : 1 ≤ N) (hm : 1 ≤ m) {b c2 η K₃ : ℝ}
    (hb0 : 0 ≤ b) (hc2 : 0 ≤ c2) (hη : 0 ≤ η) (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    (θ : HidParam N m) (w : Fin m → ℝ) :
    ∫ u, (∑ j, (hid2 θ.1 θ.2 u j - hbar (uniformSphere N) (hid2 θ.1 θ.2) j) * w j) ^ 2
        ∂uniformSphere N ≤
      (m : ℝ) / N * (b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) +
        (√(errK θ) / ((m : ℝ) / N) + η * (√3 / (N : ℝ)) +
          K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4))))) * ∑ j, w j ^ 2 := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = kappa (kappa 0) := ⟨_, rfl⟩
  have hE0 : 0 ≤ √(errK θ) := Real.sqrt_nonneg _
  obtain ⟨dX, hdX⟩ : ∃ dX : ℝ, dX = √(errK θ) / S0 + η * (√3 / (N : ℝ)) +
      K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4))) := ⟨_, rfl⟩
  have hdX0 : 0 ≤ dX := by rw [hdX]; positivity
  have hcontK : Continuous (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ)) :=
    continuous_fK.comp (continuous_id.prodMk continuous_const)
  -- the finite-width part
  have hfw : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ))
      (√(errK θ)) := by
    refine ⟨hcontK.aestronglyMeasurable, lawU2_cont_integrable hN (hcontK.pow 2), ?_⟩
    rw [Real.sq_sqrt (errK_nonneg θ)]
    exact le_of_eq rfl
  -- the part of `κ∘κ`
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hd6 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2| ^ 3)
      (√(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    unfold lawU2
    refine L2le.prod_const_left ((hmd.abs).pow_const 3).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot6 hN hy
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2) :=
    ((((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const).sub (hmd.const_mul b)).sub ((hmd.pow_const 2).const_mul c2)
  have hbd := (hd4.const_mul_nonneg hη).add0 (hd6.const_mul_nonneg hK₃) (by positivity)
    (by positivity)
  have hdet0 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2)
      (η * (√3 / (N : ℝ)) + K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    refine L2le.abs_le_ae_R hmk.aestronglyMeasurable hbd ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h := hmodel _ (unit_dot_mem huu.1 huu.2)
    rw [← hq] at h
    rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ η * dotp uu.1 uu.2 ^ 2 + K₃ * |dotp uu.1 uu.2| ^ 3)]
    exact h
  have hdet := hdet0.const_mul_nonneg hS0.le
  have hsum := hfw.add0 hdet hE0 (by positivity)
  have hD : ∫ uu, (dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
      S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ))) ^ 2 ∂lawU2 N ≤
      (S0 * dX) ^ 2 := by
    have h1 := (hsum.congr_fun (g := fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
        S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ)))
      (fun uu => by simp only [fK, hS0def, hq]; ring)).le
    refine h1.trans (le_of_eq ?_)
    rw [hdX]
    field_simp
    ring
  have key := sphere_cov hN (continuous_hid2 θ.1 θ.2) (a := S0 * (q + c2 / (N : ℝ)))
    (c := S0 * b) (c₂ := S0 * c2) (Δ := S0 * dX) (by positivity) (by positivity)
    (by positivity) hD w
  refine key.trans (le_of_eq ?_)
  rw [← hS0def, ← hdX]
  ring

end cov

/-! ## The pointwise frame constant -/

/-- The deterministic part of the frame constant of the centred features, in units of `m/N`:
`0.3017/N + 0.138·2/(N(N+2)) + 0.001·√3/N + 0.4·√(15/(N(N+2)(N+4)))`, `N = 2n`. -/
noncomputable def cDet (n : ℕ) : ℝ :=
  3017 / 10000 / ((2 * n : ℕ) : ℝ) +
    138 / 1000 * (2 / (((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) + 2))) +
    1 / 1000 * (√3 / ((2 * n : ℕ) : ℝ)) +
    2 / 5 * √(15 / (((2 * n : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) + 2) * (((2 * n : ℕ) : ℝ) + 4)))

lemma cDet_nonneg (n : ℕ) : 0 ≤ cDet n := by unfold cDet; positivity

/-- **The pointwise frame constant** of the computed centre at `θ = (M₁, M₂)`, in units of `1/n`:
`n·((cDet n + √(errK θ)/S0 + (N/2)·dist2 θ)/s + min(1, (N/2)²·errT θ/ε₂² + errD θ/S0²/ε₁²))`,
`N = 2n`, `S0 = m_W/N`. -/
noncomputable def LfX (s ε₁ ε₂ : ℝ) (n : ℕ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  (n : ℝ) * ((cDet n + √(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
      ((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ) / s +
    min 1 ((((2 * n : ℕ) : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 +
      errD θ / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / ε₁ ^ 2))

lemma LfX_meas {n : ℕ} (hn : 1 ≤ n) (s ε₁ ε₂ : ℝ) : Measurable (LfX s ε₁ ε₂ n) := by
  have hN : 1 ≤ 2 * n := by omega
  unfold LfX
  exact measurable_const.mul
    ((((measurable_const.add ((measurable_errK hN).sqrt.div_const _)).add
      ((measurable_dist2 hN).const_mul _)).div_const _).add
    (measurable_const.min
      ((((measurable_errT hN).const_mul _).div_const _).add
        (((measurable_errD hN).div_const _).div_const _))))

lemma LfX_nonneg {n : ℕ} {s ε₁ ε₂ : ℝ} (hs : 0 ≤ s) (θ : HidParam (2 * n) (mW n)) :
    0 ≤ LfX s ε₁ ε₂ n θ := by
  have h1 := cDet_nonneg n
  have h2 := dist2_nonneg θ
  have h3 := errT_nonneg θ
  have h4 := errD_nonneg θ
  have h5 : 0 ≤ ((2 * n : ℕ) : ℝ) / 2 := by positivity
  have h6 : 0 ≤ min 1 ((((2 * n : ℕ) : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 +
      errD θ / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / ε₁ ^ 2) :=
    le_min zero_le_one (by positivity)
  unfold LfX
  have h7 : 0 ≤ (cDet n + √(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
      ((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ) / s := by positivity
  positivity

section gen

variable {N m : ℕ}

/-- **The pointwise frame bound, general `N`, `m`**, without the cap `min 1`: for every `θ` with
`t|b̂|² ≥ 0.48·γ`. -/
theorem frameX_gen (hN : 1 ≤ N) (hm : 1 ≤ m) {s ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hs : 0 < s) (hk0 : 0 ≤ kap1 N) (hsle : s ≤ 1 - ε₁ - (kap1 N + ε₂) ^ 2 / (48 / 100))
    {θ : HidParam N m} (hBl : 2 / (N : ℝ) * (48 / 100) ≤ Bh N m θ) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere N ≤
      ((3017 / 10000 / (N : ℝ) + 138 / 1000 * (2 / ((N : ℝ) * ((N : ℝ) + 2))) +
          1 / 1000 * (√3 / (N : ℝ)) +
          2 / 5 * √(15 / ((N : ℝ) * ((N : ℝ) + 2) * ((N : ℝ) + 4))) +
          √(errK θ) / ((m : ℝ) / N) + (N : ℝ) / 2 * dist2 N m θ) / s +
        (((N : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 + errD θ / ((m : ℝ) / N) ^ 2 / ε₁ ^ 2)) *
        ∑ j, w j ^ 2 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hNrpos : (0 : ℝ) < N := by exact_mod_cast hN
  have := uniformSphere_isProbability N hN
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  have hmS : (m : ℝ) = S0 * N := by rw [hS0def]; field_simp
  have hcov := covX (N := N) (m := m) hN hm hb0 (by norm_num : (0 : ℝ) ≤ 138 / 1000)
    (by norm_num : (0 : ℝ) ≤ 1 / 1000) (by norm_num : (0 : ℝ) ≤ 2 / 5) hmodel θ
  rw [← hS0def] at hcov ⊢
  -- the frame constant of the centred features
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℝ, A1 = 3017 / 10000 / (N : ℝ) +
      138 / 1000 * (2 / ((N : ℝ) * ((N : ℝ) + 2))) +
      1 / 1000 * (√3 / (N : ℝ)) + 2 / 5 * √(15 / ((N : ℝ) * ((N : ℝ) + 2) * ((N : ℝ) + 4))) +
      √(errK θ) / S0 := ⟨_, rfl⟩
  have hA10 : 0 ≤ A1 := by rw [hA1]; positivity
  have hA : ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, (hid2 θ.1 θ.2 u j - hbar (uniformSphere N) (hid2 θ.1 θ.2) j) * w j) ^ 2
          ∂uniformSphere N ≤ S0 * A1 * ∑ j, w j ^ 2 := by
    intro w
    refine (hcov w).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hS0.le
    rw [hA1]
    have : b / (N : ℝ) ≤ 3017 / 10000 / (N : ℝ) := div_le_div_of_nonneg_right hb1 hNrpos.le
    linarith
  -- the three hypotheses on the centre
  obtain ⟨ξ', hξ'⟩ : ∃ ξ' : ℝ, ξ' = (N : ℝ) / 2 * dist2 N m θ := ⟨_, rfl⟩
  have hξ'0 : 0 ≤ ξ' := by rw [hξ']; exact mul_nonneg (by positivity) (dist2_nonneg θ)
  have hξ : ∑ j, (hbar (uniformSphere N) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 ≤ S0 * ξ' := by
    have e : ∑ j, (hbar (uniformSphere N) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 =
        normSq (bhat θ - hbarW θ) := by
      rw [normSq_sub_comm]
      rfl
    rw [e, hξ']
    unfold dist2
    refine le_of_eq ?_
    rw [hmS]
    field_simp
  have hE0 : 0 ≤ √(errT θ) := Real.sqrt_nonneg _
  have hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 N) ^ 2
      ∂uniformSphere N ≤ (S0 * ((N : ℝ) / 2 * √(errT θ))) ^ 2 := by
    have e : ∀ u : Fin N → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j - S0 * kap1 N) ^ 2 =
        ((m : ℝ) / 2) ^ 2 * (That N m u θ - 2 / (N : ℝ) * kap1 N) ^ 2 := by
      intro u
      have e1 : That N m u θ = 2 / (m : ℝ) * ∑ j, hid2 θ.1 θ.2 u j * bhat θ j := rfl
      rw [e1, hmS]
      field_simp
    simp_rw [e]
    rw [integral_const_mul]
    change ((m : ℝ) / 2) ^ 2 * errT θ ≤ _
    refine le_of_eq ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (errT_nonneg θ), hmS]
    ring
  have hD0 : 0 ≤ √(errD θ) := Real.sqrt_nonneg _
  have hd : ∫ u, (normSq (hid2 θ.1 θ.2 u) - S0) ^ 2 ∂uniformSphere N ≤
      (√(errD θ)) ^ 2 := by
    rw [Real.sq_sqrt (errD_nonneg θ), hS0def]
    exact le_of_eq rfl
  have hβb : S0 * (48 / 100) ≤ normSq (bhat θ) := by
    unfold Bh at hBl
    have := mul_le_mul_of_nonneg_left hBl (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2)
    have e2 : (m : ℝ) / 2 * (2 / (m : ℝ) * normSq (bhat θ)) = normSq (bhat θ) := by
      field_simp
    have e3 : (m : ℝ) / 2 * (2 / (N : ℝ) * (48 / 100)) = S0 * (48 / 100) := by
      rw [hS0def]; field_simp
    linarith
  have hsle' : S0 * s ≤ S0 - S0 * ε₁ - (S0 * kap1 N + S0 * ε₂) ^ 2 / (S0 * (48 / 100)) := by
    have e : (S0 * kap1 N + S0 * ε₂) ^ 2 / (S0 * (48 / 100)) =
        S0 * ((kap1 N + ε₂) ^ 2 / (48 / 100)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hsle hS0.le
    linarith
  have key := sphere_frame_b hN (continuous_hid2 θ.1 θ.2) (b := bhat θ) (A := S0 * A1)
    (ξ := S0 * ξ') (a := S0 * kap1 N) (δ₂ := S0 * ((N : ℝ) / 2 * √(errT θ))) (d := S0)
    (δ := √(errD θ)) (ε₁ := S0 * ε₁) (ε₂ := S0 * ε₂) (β := S0 * (48 / 100)) (s := S0 * s)
    (by positivity) hA hξ hX hd (by positivity) (by positivity) (by positivity) (by positivity)
    hβb (by positivity) hsle' w
  refine key.trans (le_of_eq ?_)
  congr 1
  have e1 : (S0 * A1 + S0 * ξ') / (S0 * s) = (A1 + ξ') / s := by
    field_simp
  have e2 : (S0 * ((N : ℝ) / 2 * √(errT θ))) ^ 2 / (S0 * ε₂) ^ 2 =
      ((N : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (errT_nonneg θ)]
    field_simp
  have e3 : (√(errD θ)) ^ 2 / (S0 * ε₁) ^ 2 = errD θ / S0 ^ 2 / ε₁ ^ 2 := by
    rw [Real.sq_sqrt (errD_nonneg θ), mul_pow, div_div]
  rw [e1, e2, e3, hA1, hξ']
  ring

/-- The trivial frame bound: `E_u ⟨e_b(u), w⟩² ≤ |w|²`. -/
lemma frame_triv (hN : 1 ≤ N) (bc : Fin m → ℝ) (h : (Fin N → ℝ) → Fin m → ℝ) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir bc (h u) j * w j) ^ 2 ∂uniformSphere N ≤ ∑ j, w j ^ 2 := by
  have := uniformSphere_isProbability N hN
  have ptb : ∀ u, (∑ j, eDir bc (h u) j * w j) ^ 2 ≤ ∑ j, w j ^ 2 := by
    intro u
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => eDir bc (h u) j) w
    have h1 : ∑ j, eDir bc (h u) j ^ 2 ≤ 1 := by
      rcases eDir_unit_or_zero bc (h u) with h1 | h1
      · exact h1.le
      · rw [h1]; simp
    have hW0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have h2 := integral_mono_of_nonneg (μ := uniformSphere N)
    (Filter.Eventually.of_forall fun u => sq_nonneg (∑ j, eDir bc (h u) j * w j))
    (integrable_const (∑ j, w j ^ 2)) (Filter.Eventually.of_forall ptb)
  simpa using h2

end gen

/-- **The pointwise frame bound of the computed centre**: for every `n ≥ 4096` and every
`θ ∈ Gwin n`: `E_u ⟨ê(u), w⟩² ≤ (LfX s ε₁ ε₂ n θ/n)·|w|²`. -/
theorem frameLfX {n : ℕ} (hn : 4096 ≤ n) {s ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hs : 0 < s)
    (hs' : s ≤ 1 - ε₁ - (4938 / 10000 + ε₂) ^ 2 / (48 / 100))
    {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ Gwin n) (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      LfX s ε₁ ε₂ n θ / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  have hk0 : 0 ≤ kap1 (2 * n) := by linarith
  have hW0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsle : s ≤ 1 - ε₁ - (kap1 (2 * n) + ε₂) ^ 2 / (48 / 100) := by
    have h1 : (kap1 (2 * n) + ε₂) ^ 2 ≤ (4938 / 10000 + ε₂) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (kap1 (2 * n) + ε₂) ^ 2 / (48 / 100) ≤ (4938 / 10000 + ε₂) ^ 2 / (48 / 100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    linarith
  have key := frameX_gen (N := 2 * n) (m := mW n) hN hm hε₁ hε₂ hs hk0 hsle hθ.1 w
  have triv := frame_triv (N := 2 * n) (m := mW n) hN (bhat θ) (hid2 θ.1 θ.2) w
  have e : LfX s ε₁ ε₂ n θ / (n : ℝ) =
      (cDet n + √(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
        ((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ) / s +
      min 1 ((((2 * n : ℕ) : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 +
        errD θ / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / ε₁ ^ 2) := by
    unfold LfX
    rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hnpos.ne']
  rw [e]
  have hA0 : 0 ≤ (cDet n + √(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
        ((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ) / s := by
    have h1 := cDet_nonneg n
    have h2 := dist2_nonneg θ
    have h5 : 0 ≤ ((2 * n : ℕ) : ℝ) / 2 := by positivity
    positivity
  rcases le_total ((((2 * n : ℕ) : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 +
        errD θ / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / ε₁ ^ 2) 1 with hT1 | hT1
  · rw [min_eq_right hT1]
    refine key.trans (le_of_eq ?_)
    unfold cDet
    ring
  · rw [min_eq_left hT1]
    refine triv.trans ?_
    have := mul_nonneg hA0 hW0
    linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms Gwin_compl
open BstLean.Part145 in
#print axioms Gwin_compl_n
open BstLean.Part145 in
#print axioms covX
open BstLean.Part145 in
#print axioms frameX_gen
open BstLean.Part145 in
#print axioms frameLfX
