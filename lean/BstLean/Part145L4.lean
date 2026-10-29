import BstLean.Part145L3

/-!
# Part 145 (pointwise frame constant), file 4: the mean of the product with an `L²` bound of `DKV`

`prod_mean_core2`, `LfX_DKV_mean2`: `prod_mean_core`, `LfX_DKV_mean` of file 2 with the
hypothesis `‖D‖₂ ≤ dL` (`‖DKV‖₂ ≤ dL`); the Cauchy–Schwarz term is `rho·dL` in the place of
`rho·√(2v)`.
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

section core

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The mean of `L·(D + L/c)`**: `0 ≤ L ≤ lam + R₁ + R₂`, `‖R₁‖₂ ≤ rho`, `0 ≤ R₂ ≤ c`,
`E R₂ ≤ r2`, `0 ≤ D ≤ 2`, `E D ≤ v`, `‖D‖₂ ≤ dL`. Then, on every measurable set `G`,
`E[1_G·L·(D + L/c)] ≤ lam·v + rho·dL + 5·r2 + (3/c)·(lam² + rho²)`. -/
theorem prod_mean_core2 {L D R₁ R₂ : Ω → ℝ} {lam rho r2 v c dL : ℝ} {G : Set Ω}
    (hG : MeasurableSet G) (hLm : AEStronglyMeasurable L μ) (hL0 : ∀ ω, 0 ≤ L ω)
    (hLle : ∀ ω, L ω ≤ lam + R₁ ω + R₂ ω) (hlam : 0 ≤ lam) (hrho : 0 ≤ rho)
    (hR₁ : L2le μ R₁ rho)
    (hR₂0 : ∀ ω, 0 ≤ R₂ ω) (hR₂c : ∀ ω, R₂ ω ≤ c) (hc : 0 < c) (hR₂i : Integrable R₂ μ)
    (hR₂ : ∫ ω, R₂ ω ∂μ ≤ r2)
    (hD0 : ∀ ω, 0 ≤ D ω) (hD2 : ∀ ω, D ω ≤ 2) (hDi : Integrable D μ)
    (hDv : ∫ ω, D ω ∂μ ≤ v) (hdL : 0 ≤ dL) (hDL : L2le μ D dL) :
    Integrable (G.indicator fun ω => L ω * (D ω + L ω / c)) μ ∧
      ∫ ω, G.indicator (fun ω => L ω * (D ω + L ω / c)) ω ∂μ ≤
        lam * v + rho * dL + 5 * r2 + 3 / c * (lam ^ 2 + rho ^ 2) := by
  have iRD := l2_mul_integrable hR₁ hDL
  have cs := (le_abs_self _).trans
    (l2_abs_integral_mul_le hrho hdL hR₁ hDL)
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
bound `v` of the mean of `DKV` (with `DKV ≤ 2`) and a bound `dL` of its `L²` norm:
`E[1_{Gwin}·LfX·(DKV + LfX/n)] ≤ lam0·v + rho1·dL + 5·r2 + (3/n)·(lam0² + rho1²)`. -/
theorem LfX_DKV_mean2 {n : ℕ} (hn : 4096 ≤ n) {s ε₁ ε₂ : ℝ} (hs : 0 < s)
    {v : ℝ} (hDi : Integrable (DKV n) (hidGauss (2 * n) (mW n)))
    (hDv : ∫ θ, DKV n θ ∂hidGauss (2 * n) (mW n) ≤ v) (hD2 : ∀ θ, DKV n θ ≤ 2)
    {dL : ℝ} (hdL : 0 ≤ dL) (hDL : L2le (hidGauss (2 * n) (mW n)) (DKV n) dL) :
    Integrable ((Gwin n).indicator fun θ =>
        LfX s ε₁ ε₂ n θ * (DKV n θ + LfX s ε₁ ε₂ n θ / (n : ℝ))) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, (Gwin n).indicator (fun θ =>
          LfX s ε₁ ε₂ n θ * (DKV n θ + LfX s ε₁ ε₂ n θ / (n : ℝ))) θ
        ∂hidGauss (2 * n) (mW n) ≤
        lam0 s n * v + rho1 s n * dL + 5 * r2 ε₁ ε₂ n +
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
  exact prod_mean_core2 (μ := hidGauss (2 * n) (mW n)) (Gwin_meas hn1)
    (LfX_meas hn1 s ε₁ ε₂).aestronglyMeasurable (fun θ => LfX_nonneg hs.le θ) hLle
    (lam0_nonneg hn1 hs.le) (rho1_nonneg hn hs.le)
    hR₁
    (fun θ => mul_nonneg hnpos.le (le_min zero_le_one (hTf0 θ)))
    (fun θ => by
      have := mul_le_mul_of_nonneg_left (min_le_left 1 (Tf θ)) hnpos.le
      linarith)
    hnpos iR₂ eR₂ (DKV_nonneg n) hD2 hDi hDv hdL hDL

end BstLean.Part145

open BstLean.Part145 in
#print axioms prod_mean_core2
open BstLean.Part145 in
#print axioms LfX_DKV_mean2
