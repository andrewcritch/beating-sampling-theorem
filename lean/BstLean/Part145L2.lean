import BstLean.Part145L1
import BstLean.Part145G4
import BstLean.Part143World
import BstLean.Part143HidK

/-!
# Part 145 (pointwise frame constant), file 2: the means

Notation: `N = 2n`, `m = mW n`, `S0 = m/N`. The measure is `hidGauss N m`, the distribution of
`θ = (M₁, M₂)`.

* `errK_L2_X`: `‖√(errK θ)/S0‖₂ ≤ √0.372·cF2o m`. `errD_mean_X`: `E errD/S0² ≤ 0.448·cF2o m²`.
* `dist_L2_X`: `‖(N/2)·dist2 θ − (q_N − κ(q₁))‖₂ ≤ cDst143s N m`. `nd0_le`:
  `n·(q_N − κ(q₁)) ≤ 4/25`.
* `errT_mean_X`: `E (N/2)²·errT ≤ cHat143 N m²`.
* `lam0 s n`, `rho1 s n`, `r2 ε₁ ε₂ n`: the constant part of `LfX`, the bound of the `L²` norm of
  its first fluctuating part, and the bound of the mean of its capped part.
* `prod_mean_core`: the abstract bound of `E[L·(D + L/c)]`.
* **`LfX_DKV_mean`**: `E[1_{Gwin}·LfX·(DKV + LfX/n)] ≤
  lam0·v + rho1·√(2v) + 5·r2 + (3/n)·(lam0² + rho1²)`.
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

/-! ## The means of the four quantities -/

section means

variable {N m : ℕ}

lemma cF2o_sq_eq (hm : 1 ≤ m) :
    cF2o m ^ 2 = (6 * (1 + 5 / (m : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold cF2o
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- `‖√(errK θ)/S0‖_{L²(θ)} ≤ √0.372·cF2o m`, for `N ≥ 8192`, `m ≥ 10⁶`. -/
theorem errK_L2_X (hN8 : 8192 ≤ N) (hmM : 1000000 ≤ m) :
    L2le (hidGauss N m) (fun θ => √(errK θ) / ((m : ℝ) / N))
      (√(372 / 1000) * cF2o m) := by
  have hN : 1 ≤ N := by omega
  have hm : 1 ≤ m := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  obtain ⟨iK, eK⟩ := errK_mean143 (N := N) (m := m) hN hm
  rw [← hS0def] at eK ⊢
  have e : (fun θ : HidParam N m => (√(errK θ) / S0) ^ 2) = fun θ => errK θ / S0 ^ 2 := by
    funext θ
    rw [div_pow, Real.sq_sqrt (errK_nonneg θ)]
  refine ⟨((measurable_errK hN).sqrt.div_const _).aestronglyMeasurable, ?_, ?_⟩
  · rw [e]
    exact iK.div_const _
  · rw [e, integral_div, mul_pow, Real.sq_sqrt (by norm_num), cF2o_sq_eq hm,
      div_le_iff₀ (by positivity)]
    refine eK.trans ?_
    have h1 := cK143_le hN8 hmM
    have h2 : 0 ≤ S0 ^ 2 / (m : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring

/-- `E_θ errD θ/S0² ≤ 0.448·cF2o m²`, for `m ≥ 10⁶`. -/
theorem errD_mean_X (hN : 1 ≤ N) (hmM : 1000000 ≤ m) :
    Integrable (fun θ : HidParam N m => errD θ / ((m : ℝ) / N) ^ 2) (hidGauss N m) ∧
      ∫ θ, errD θ / ((m : ℝ) / N) ^ 2 ∂hidGauss N m ≤ 448 / 1000 * cF2o m ^ 2 := by
  have hm : 1 ≤ m := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  obtain ⟨iD, eD⟩ := errD_mean143 (N := N) (m := m) hN hm
  rw [← hS0def] at eD ⊢
  refine ⟨iD.div_const _, ?_⟩
  rw [integral_div, cF2o_sq_eq hm, div_le_iff₀ (by positivity)]
  refine eD.trans ?_
  have h1 := cD143_le hmM
  have h2 : 0 ≤ S0 ^ 2 / (m : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_)) <;> ring

/-- `‖(N/2)·dist2 θ − (q_N − κ(q₁))‖_{L²(θ)} ≤ cDst143s N m`. -/
theorem dist_L2_X (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => (N : ℝ) / 2 * dist2 N m θ - (qN N - kap1 N))
      (cDst143s N m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (dist2_L2_143s (N := N) (m := m) hN hm).const_mul ((N : ℝ) / 2)
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)] at h
  refine (h.congr_fun fun θ => ?_).congr_bound ?_
  · field_simp
  · field_simp

/-- `E_θ (N/2)²·errT θ ≤ cHat143 N m²`. -/
theorem errT_mean_X (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ : HidParam N m => ((N : ℝ) / 2) ^ 2 * errT θ) (hidGauss N m) ∧
      ∫ θ, ((N : ℝ) / 2) ^ 2 * errT θ ∂hidGauss N m ≤ cHat143 N m ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨iT, eT⟩ := errT_mean143 (N := N) (m := m) hN hm
  refine ⟨iT.const_mul _, ?_⟩
  rw [integral_const_mul]
  have := mul_le_mul_of_nonneg_left eT (sq_nonneg ((N : ℝ) / 2))
  refine this.trans (le_of_eq ?_)
  field_simp

end means

/-- `n·(q_N − κ(q₁)) ≤ 4/25`, `N = 2n`. -/
lemma nd0_le {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) * (qN (2 * n) - kap1 (2 * n)) ≤ 4 / 25 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := qN_sub_kap1_le (N := 2 * n) (by omega)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hNcast] at h
  have := mul_le_mul_of_nonneg_left h hnpos.le
  refine this.trans (le_of_eq ?_)
  field_simp
  norm_num

lemma d0_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ qN (2 * n) - kap1 (2 * n) := by
  have := kap1_le (N := 2 * n) (by omega)
  linarith

/-! ## The three constants -/

/-- The constant part of `LfX`: `n·(cDet n + (q_N − κ(q₁)))/s`. -/
noncomputable def lam0 (s : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (cDet n + (qN (2 * n) - kap1 (2 * n))) / s

/-- The bound of the `L²` norm of the first fluctuating part of `LfX`:
`(n·√0.372·cF2o m + n·cDst143s N m)/s`. -/
noncomputable def rho1 (s : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * √(372 / 1000) * cF2o (mW n) + (n : ℝ) * cDst143s (2 * n) (mW n)) / s

/-- The bound of the mean of the capped part of `LfX`:
`n·(cHat143 N m²/ε₂² + 0.448·cF2o m²/ε₁²)`. -/
noncomputable def r2 (ε₁ ε₂ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (cHat143 (2 * n) (mW n) ^ 2 / ε₂ ^ 2 + 448 / 1000 * cF2o (mW n) ^ 2 / ε₁ ^ 2)

lemma lam0_nonneg {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ lam0 s n := by
  have h1 := cDet_nonneg n
  have h2 := d0_nonneg hn
  unfold lam0
  positivity

lemma rho1_nonneg {n : ℕ} (hn : 4096 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ rho1 s n := by
  have h1 := Part136.cF2o_pos (m := mW n) (by have := mW_ge_million hn; omega)
  have h2 := cDst143s_nonneg (2 * n) (mW n)
  unfold rho1
  positivity

/-! ## The abstract bound of the mean of the product -/

section core

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The mean of `L·(D + L/c)`**: `0 ≤ L ≤ lam + R₁ + R₂`, `‖R₁‖₂ ≤ rho`, `0 ≤ R₂ ≤ c`,
`E R₂ ≤ r2`, `0 ≤ D ≤ 2`, `E D ≤ v`. Then, on every measurable set `G`,
`E[1_G·L·(D + L/c)] ≤ lam·v + rho·√(2v) + 5·r2 + (3/c)·(lam² + rho²)`. -/
theorem prod_mean_core {L D R₁ R₂ : Ω → ℝ} {lam rho r2 v c : ℝ} {G : Set Ω}
    (hG : MeasurableSet G) (hLm : AEStronglyMeasurable L μ) (hL0 : ∀ ω, 0 ≤ L ω)
    (hLle : ∀ ω, L ω ≤ lam + R₁ ω + R₂ ω) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hR₁ : L2le μ R₁ rho)
    (hR₂0 : ∀ ω, 0 ≤ R₂ ω) (hR₂c : ∀ ω, R₂ ω ≤ c) (hc : 0 < c) (hR₂i : Integrable R₂ μ)
    (hR₂ : ∫ ω, R₂ ω ∂μ ≤ r2)
    (hv : 0 ≤ v) (hD0 : ∀ ω, 0 ≤ D ω) (hD2 : ∀ ω, D ω ≤ 2) (hDi : Integrable D μ)
    (hDv : ∫ ω, D ω ∂μ ≤ v) :
    Integrable (G.indicator fun ω => L ω * (D ω + L ω / c)) μ ∧
      ∫ ω, G.indicator (fun ω => L ω * (D ω + L ω / c)) ω ∂μ ≤
        lam * v + rho * √(2 * v) + 5 * r2 + 3 / c * (lam ^ 2 + rho ^ 2) := by
  -- `D` in `L²`
  have hDL : L2le μ D (√(2 * v)) := by
    have i2 : Integrable (fun ω => 2 * D ω) μ := hDi.const_mul 2
    refine L2le.of_sq_le hDi.aestronglyMeasurable i2 (fun ω => ?_) ?_
    · nlinarith [hD0 ω, hD2 ω]
    · rw [integral_const_mul, Real.sq_sqrt (by positivity)]
      linarith
  have iRD := l2_mul_integrable hR₁ hDL
  have cs := (le_abs_self _).trans
    (l2_abs_integral_mul_le hrho (Real.sqrt_nonneg _) hR₁ hDL)
  -- the dominating function
  have i1 : Integrable (fun ω => lam * D ω) μ := hDi.const_mul lam
  have i3 : Integrable (fun ω => 2 * R₂ ω) μ := hR₂i.const_mul 2
  have i4a : Integrable (fun ω => lam ^ 2 + R₁ ω ^ 2) μ :=
    (integrable_const (lam ^ 2)).add hR₁.int_sq
  have i4b : Integrable (fun ω => c * R₂ ω) μ := hR₂i.const_mul c
  have i4 : Integrable (fun ω => lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) μ := i4a.add i4b
  have i5 : Integrable (fun ω => 3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω)) μ :=
    i4.const_mul (3 / c)
  have i12 : Integrable (fun ω => lam * D ω + R₁ ω * D ω) μ := i1.add iRD
  have i123 : Integrable (fun ω => lam * D ω + R₁ ω * D ω + 2 * R₂ ω) μ := i12.add i3
  have ig : Integrable (fun ω => lam * D ω + R₁ ω * D ω + 2 * R₂ ω +
      3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω)) μ := i123.add i5
  have hpt : ∀ ω, L ω * (D ω + L ω / c) ≤ lam * D ω + R₁ ω * D ω + 2 * R₂ ω +
      3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) := by
    intro ω
    have a1 : L ω * D ω ≤ (lam + R₁ ω + R₂ ω) * D ω :=
      mul_le_mul_of_nonneg_right (hLle ω) (hD0 ω)
    have a2 : R₂ ω * D ω ≤ R₂ ω * 2 := mul_le_mul_of_nonneg_left (hD2 ω) (hR₂0 ω)
    have a3 : L ω ^ 2 ≤ (lam + R₁ ω + R₂ ω) ^ 2 := pow_le_pow_left₀ (hL0 ω) (hLle ω) 2
    have a4 : (lam + R₁ ω + R₂ ω) ^ 2 ≤ 3 * (lam ^ 2 + R₁ ω ^ 2 + R₂ ω ^ 2) := by
      nlinarith [sq_nonneg (lam - R₁ ω), sq_nonneg (lam - R₂ ω), sq_nonneg (R₁ ω - R₂ ω)]
    have a5 : R₂ ω ^ 2 ≤ c * R₂ ω := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hR₂c ω) (hR₂0 ω)
    have a6 : L ω ^ 2 ≤ 3 * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) := by linarith
    have a7 : L ω * (L ω / c) ≤ 3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) := by
      have e1 : L ω * (L ω / c) = L ω ^ 2 / c := by ring
      have e2 : 3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) =
          3 * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) / c := by ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right a6 hc.le
    have e3 : L ω * (D ω + L ω / c) = L ω * D ω + L ω * (L ω / c) := by ring
    rw [e3]
    nlinarith
  have hf0 : ∀ ω, 0 ≤ L ω * (D ω + L ω / c) := fun ω =>
    mul_nonneg (hL0 ω) (add_nonneg (hD0 ω) (div_nonneg (hL0 ω) hc.le))
  have hind0 : ∀ ω, 0 ≤ G.indicator (fun ω => L ω * (D ω + L ω / c)) ω := fun ω =>
    Set.indicator_nonneg (fun ω _ => hf0 ω) ω
  have hindle : ∀ ω, G.indicator (fun ω => L ω * (D ω + L ω / c)) ω ≤
      lam * D ω + R₁ ω * D ω + 2 * R₂ ω + 3 / c * (lam ^ 2 + R₁ ω ^ 2 + c * R₂ ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]
      exact hpt ω
    · rw [Set.indicator_of_notMem hω]
      exact (hf0 ω).trans (hpt ω)
  have hfm : AEStronglyMeasurable (fun ω => L ω * (D ω + L ω / c)) μ :=
    hLm.mul (hDi.aestronglyMeasurable.add (hLm.aemeasurable.div_const c).aestronglyMeasurable)
  have iind : Integrable (G.indicator fun ω => L ω * (D ω + L ω / c)) μ := by
    refine Integrable.mono' ig (hfm.indicator hG) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hind0 ω)]
    exact hindle ω
  refine ⟨iind, ?_⟩
  refine (integral_mono iind ig hindle).trans ?_
  rw [integral_add i123 i5, integral_add i12 i3, integral_add i1 iRD, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_add i4a i4b,
    integral_add (integrable_const (lam ^ 2)) hR₁.int_sq, integral_const_mul, integral_const]
  have hu : μ.real Set.univ = 1 := by simp
  rw [hu, one_smul]
  have b1 : lam * ∫ ω, D ω ∂μ ≤ lam * v := mul_le_mul_of_nonneg_left hDv hlam
  have b4 := hR₁.le
  have h3c : 0 ≤ 3 / c := by positivity
  have b5 : 3 / c * (lam ^ 2 + ∫ ω, R₁ ω ^ 2 ∂μ + c * ∫ ω, R₂ ω ∂μ) ≤
      3 / c * (lam ^ 2 + rho ^ 2 + c * r2) := by
    refine mul_le_mul_of_nonneg_left ?_ h3c
    have := mul_le_mul_of_nonneg_left hR₂ hc.le
    linarith
  have e5 : 3 / c * (lam ^ 2 + rho ^ 2 + c * r2) = 3 / c * (lam ^ 2 + rho ^ 2) + 3 * r2 := by
    field_simp
  linarith

end core

/-! ## The mean of the product -/

/-- **The mean of `LfX·(DKV + LfX/n)` on the window event**: for `n ≥ 4096`, `s > 0`, and a
bound `v` of the mean of `DKV` (with `DKV ≤ 2`):
`E[1_{Gwin}·LfX·(DKV + LfX/n)] ≤ lam0·v + rho1·√(2v) + 5·r2 + (3/n)·(lam0² + rho1²)`. -/
theorem LfX_DKV_mean {n : ℕ} (hn : 4096 ≤ n) {s ε₁ ε₂ : ℝ} (hs : 0 < s)
    {v : ℝ} (hv : 0 ≤ v) (hDi : Integrable (DKV n) (hidGauss (2 * n) (mW n)))
    (hDv : ∫ θ, DKV n θ ∂hidGauss (2 * n) (mW n) ≤ v) (hD2 : ∀ θ, DKV n θ ≤ 2) :
    Integrable ((Gwin n).indicator fun θ =>
        LfX s ε₁ ε₂ n θ * (DKV n θ + LfX s ε₁ ε₂ n θ / (n : ℝ))) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, (Gwin n).indicator (fun θ =>
          LfX s ε₁ ε₂ n θ * (DKV n θ + LfX s ε₁ ε₂ n θ / (n : ℝ))) θ
        ∂hidGauss (2 * n) (mW n) ≤
        lam0 s n * v + rho1 s n * √(2 * v) + 5 * r2 ε₁ ε₂ n +
          3 / (n : ℝ) * (lam0 s n ^ 2 + rho1 s n ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hN8 : 8192 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hcF := Part136.cF2o_pos hm
  have hd0 := d0_nonneg hn1
  -- the four means
  have hK := errK_L2_X (N := 2 * n) (m := mW n) hN8 hmM
  obtain ⟨iD, eD⟩ := errD_mean_X (N := 2 * n) (m := mW n) hN hmM
  have hdst := dist_L2_X (N := 2 * n) (m := mW n) hN hm
  obtain ⟨iT, eT⟩ := errT_mean_X (N := 2 * n) (m := mW n) hN hm
  -- the first fluctuating part
  have habs : L2le (hidGauss (2 * n) (mW n))
      (fun θ => |((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ -
        (qN (2 * n) - kap1 (2 * n))|) (cDst143s (2 * n) (mW n)) :=
    L2le.of_abs_le hdst.aesm.norm hdst (fun θ => by rw [abs_abs])
  have hsum := hK.add' habs (by positivity) (cDst143s_nonneg _ _)
  have hR₁ : L2le (hidGauss (2 * n) (mW n))
      (fun θ => (n : ℝ) / s * (√(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
        |((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ - (qN (2 * n) - kap1 (2 * n))|))
      (rho1 s n) := by
    refine (hsum.const_mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / s)).congr_bound ?_
    unfold rho1
    field_simp
  -- the capped part
  obtain ⟨Tf, hTf⟩ : ∃ Tf : HidParam (2 * n) (mW n) → ℝ, Tf = fun θ =>
      (((2 * n : ℕ) : ℝ) / 2) ^ 2 * errT θ / ε₂ ^ 2 +
        errD θ / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / ε₁ ^ 2 := ⟨_, rfl⟩
  have hTf0 : ∀ θ, 0 ≤ Tf θ := by
    intro θ
    have h3 := errT_nonneg θ
    have h4 := errD_nonneg θ
    rw [hTf]
    positivity
  have iTf : Integrable Tf (hidGauss (2 * n) (mW n)) := by
    rw [hTf]
    exact (iT.div_const _).add (iD.div_const _)
  have eTf : ∫ θ, Tf θ ∂hidGauss (2 * n) (mW n) ≤
      cHat143 (2 * n) (mW n) ^ 2 / ε₂ ^ 2 + 448 / 1000 * cF2o (mW n) ^ 2 / ε₁ ^ 2 := by
    rw [hTf, integral_add (iT.div_const _) (iD.div_const _), integral_div, integral_div]
    exact add_le_add (div_le_div_of_nonneg_right eT (sq_nonneg _))
      (div_le_div_of_nonneg_right eD (sq_nonneg _))
  have mTf : Measurable Tf := by
    rw [hTf]
    exact (((measurable_errT hN).const_mul _).div_const _).add
      (((measurable_errD hN).div_const _).div_const _)
  have iR₂ : Integrable (fun θ => (n : ℝ) * min 1 (Tf θ)) (hidGauss (2 * n) (mW n)) := by
    refine Integrable.mono' (iTf.const_mul (n : ℝ))
      ((measurable_const.min mTf).const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg hnpos.le (le_min zero_le_one (hTf0 θ)))]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hnpos.le
  have eR₂ : ∫ θ, (n : ℝ) * min 1 (Tf θ) ∂hidGauss (2 * n) (mW n) ≤ r2 ε₁ ε₂ n := by
    have h1 := integral_mono iR₂ (iTf.const_mul (n : ℝ))
      (fun θ => mul_le_mul_of_nonneg_left (min_le_right 1 (Tf θ)) hnpos.le)
    refine h1.trans ?_
    rw [integral_const_mul]
    unfold r2
    exact mul_le_mul_of_nonneg_left eTf hnpos.le
  -- the pointwise bound of `LfX`
  have hLle : ∀ θ, LfX s ε₁ ε₂ n θ ≤ lam0 s n +
      (n : ℝ) / s * (√(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) +
        |((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ - (qN (2 * n) - kap1 (2 * n))|) +
      (n : ℝ) * min 1 (Tf θ) := by
    intro θ
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = √(errK θ) / ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) := ⟨_, rfl⟩
    obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = ((2 * n : ℕ) : ℝ) / 2 * dist2 (2 * n) (mW n) θ := ⟨_, rfl⟩
    obtain ⟨d0, hd0'⟩ : ∃ d0 : ℝ, d0 = qN (2 * n) - kap1 (2 * n) := ⟨_, rfl⟩
    unfold LfX lam0
    rw [hTf, ← ha, ← hξ, ← hd0']
    have h1 : ξ ≤ d0 + |ξ - d0| := by linarith [le_abs_self (ξ - d0)]
    have h2 : (cDet n + a + ξ) / s ≤ (cDet n + d0) / s + (a + |ξ - d0|) / s := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hs.le
    have h3 := mul_le_mul_of_nonneg_left h2 hnpos.le
    have e1 : (n : ℝ) * ((cDet n + d0) / s + (a + |ξ - d0|) / s) =
        (n : ℝ) * (cDet n + d0) / s + (n : ℝ) / s * (a + |ξ - d0|) := by ring
    rw [e1] at h3
    rw [mul_add]
    linarith
  exact prod_mean_core (μ := hidGauss (2 * n) (mW n)) (Gwin_meas hn1)
    (LfX_meas hn1 s ε₁ ε₂).aestronglyMeasurable (fun θ => LfX_nonneg hs.le θ) hLle
    (lam0_nonneg hn1 hs.le) (rho1_nonneg hn hs.le)
    hR₁
    (fun θ => mul_nonneg hnpos.le (le_min zero_le_one (hTf0 θ)))
    (fun θ => by
      have := mul_le_mul_of_nonneg_left (min_le_left 1 (Tf θ)) hnpos.le
      linarith)
    hnpos iR₂ eR₂ hv (DKV_nonneg n) hD2 hDi hDv

end BstLean.Part145

open BstLean.Part145 in
#print axioms errK_L2_X
open BstLean.Part145 in
#print axioms errD_mean_X
open BstLean.Part145 in
#print axioms dist_L2_X
open BstLean.Part145 in
#print axioms errT_mean_X
open BstLean.Part145 in
#print axioms prod_mean_core
open BstLean.Part145 in
#print axioms LfX_DKV_mean
