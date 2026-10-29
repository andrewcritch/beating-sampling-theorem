import BstLean.Part171Tay

/-!
# Part 171 (file `Row`): the bias of one row, on an abstract probability space

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "conditioning the transverse row gives the two biases
`E_v G(g_j + δ_v, v_v) − G(g_j, ς²)` and the same expression with `G₂`", and the bounds
`t7:p08:T`, `t7:p08:U`.

`(V, μ)` is a probability space (the latitude sphere), `δ : V → ℝ` (the paper's
`δ_v = z_U·(F_s(v) − F̄)`), `w : V → ℝ` (the paper's `v_v = |Π_{U^⊥}F_s(v)|²`), `s > 0` (`ς`).
`RowStat` collects the statistics: `|δ| ≤ Δ`, `0 ≤ w ≤ Γ`, `s² ≤ Γ`, `E δ = 0`, `E δ² ≤ D`,
`|E(w − s²)| ≤ h` (the paper's `h_U`), `E(w − s²)² ≤ V₂` (the paper's `V₂ = v_ε + h_U²`) and
`μ{w < s²/2} ≤ π` (the paper's `π_g`).

* `bias_split`: `|E X| ≤ |E L| + E T + K·μ(B)` if `|X − L| ≤ T` off `B` and `≤ K` on `B`.
* **`rowF`**: `|E_v G(a + δ, w) − G(a, s²)| ≤ TF`,
  `TF = φ(0)h/(2s) + ½(√2φ(0)D/s + 2φ(1)√D√V₂/s² + φ(0)V₂/(√2 s³)) + π(2Δ + (3/2)φ(0)Γ/s)`
  (the paper's `T₁ + ⋯ + T₅`).
* **`rowW`**: `|E_v G₂(a + δ, w) − G₂(a, s²)| ≤ TW`,
  `TW = h + D + √2φ(0)√D√V₂/s + φ(1)V₂/(2s²) + π((|a| + Δ)² + a² + 2(|a| + s)Δ + 4Γ)`
  (the paper's `U₁ + ⋯ + U₅`).
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter
open BstLean.Part130 (relu)
open BstLean.Part137 (psiS measurable_psiS)
open BstLean.Part153 (phiG PhiG phiG_pos PhiG_pos PhiG_le_one)
open BstLean.Part154 (phiG_le_zero)
open BstLean.Part170 (G2)

variable {V : Type*} [MeasurableSpace V] {μ : Measure V}

/-- The statistics of one row. -/
structure RowStat (μ : Measure V) (δ w : V → ℝ) (s Δ Γ D h V₂ pg : ℝ) : Prop where
  mδ : Measurable δ
  mw : Measurable w
  hs : 0 < s
  hΔ : 0 ≤ Δ
  hδb : ∀ v, |δ v| ≤ Δ
  hw0 : ∀ v, 0 ≤ w v
  hwΓ : ∀ v, w v ≤ Γ
  hsΓ : s ^ 2 ≤ Γ
  hδ0 : ∫ v, δ v ∂μ = 0
  hD : ∫ v, δ v ^ 2 ∂μ ≤ D
  hh : |∫ v, (w v - s ^ 2) ∂μ| ≤ h
  hV : ∫ v, (w v - s ^ 2) ^ 2 ∂μ ≤ V₂
  hπ : μ.real {v | w v < s ^ 2 / 2} ≤ pg

lemma measurable_G2 : Measurable (fun p : ℝ × ℝ => G2 p.1 p.2) := by
  have hF : Measurable (fun q : (ℝ × ℝ) × ℝ => relu (q.1.2 + q.1.1 * q.2) ^ 2) :=
    ((BstLean.Part130.continuous_relu.comp (by fun_prop)).pow 2).measurable
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

lemma sq_abs_le {x C : ℝ} (h : |x| ≤ C) : |x ^ 2| ≤ C ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma bdd_int [IsFiniteMeasure μ] {f : V → ℝ} (hf : Measurable f) {C : ℝ} (h : ∀ v, |f v| ≤ C) :
    Integrable f μ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact h v)

/-- `|E X| ≤ |E L| + E T + K·μ(B)` if `|X − L| ≤ T` off `B` and `|X − L| ≤ K` on `B`. -/
lemma bias_split [IsProbabilityMeasure μ] {X L T : V → ℝ} {K : ℝ} {B : Set V}
    (hX : Integrable X μ) (hL : Integrable L μ) (hT : Integrable T μ) (hB : MeasurableSet B)
    (hT0 : ∀ v, 0 ≤ T v) (_hK0 : 0 ≤ K)
    (hgood : ∀ v, v ∉ B → |X v - L v| ≤ T v) (hbad : ∀ v, v ∈ B → |X v - L v| ≤ K) :
    |∫ v, X v ∂μ| ≤ |∫ v, L v ∂μ| + ∫ v, T v ∂μ + K * μ.real B := by
  have hIB : Integrable (B.indicator (fun _ => K)) μ := (integrable_const K).indicator hB
  have hpt : ∀ v, |X v - L v| ≤ T v + B.indicator (fun _ => K) v := by
    intro v
    by_cases hv : v ∈ B
    · rw [indicator_of_mem hv]; have := hbad v hv; linarith [hT0 v]
    · rw [indicator_of_notMem hv]; have := hgood v hv; linarith
  have e : ∫ v, X v ∂μ = ∫ v, L v ∂μ + ∫ v, (X v - L v) ∂μ := by
    rw [integral_sub hX hL]; ring
  have h1 : |∫ v, (X v - L v) ∂μ| ≤ ∫ v, (T v + B.indicator (fun _ => K) v) ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact integral_mono (hX.sub hL).abs (hT.add hIB) hpt
  rw [integral_add hT hIB, integral_indicator_const _ hB, smul_eq_mul, mul_comm] at h1
  rw [e]
  calc _ ≤ |∫ v, L v ∂μ| + |∫ v, (X v - L v) ∂μ| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- `TF`: the bound of the location row bias (the paper's `T₁ + ⋯ + T₅`). -/
noncomputable def TF (s Δ Γ D h V₂ pg : ℝ) : ℝ :=
  phiG 0 / (2 * s) * h +
    1 / 2 * (√2 * phiG 0 / s * D + 2 * phiG 1 / s ^ 2 * (√D * √V₂) +
      phiG 0 / (√2 * s ^ 3) * V₂) +
    pg * (2 * Δ + 3 / 2 * phiG 0 / s * Γ)

/-- `TW`: the bound of the energy row bias (the paper's `U₁ + ⋯ + U₅`). -/
noncomputable def TW (a s Δ Γ D h V₂ pg : ℝ) : ℝ :=
  h + (D + √2 * phiG 0 / s * (√D * √V₂) + phiG 1 / (2 * s ^ 2) * V₂) +
    pg * ((|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ)

lemma abs_w_sub_le {Γ x s : ℝ} (hx0 : 0 ≤ x) (hxΓ : x ≤ Γ) (hsΓ : s ^ 2 ≤ Γ) :
    |x - s ^ 2| ≤ Γ := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg s]

/-- **The location row bias** (the paper's `T₁ + ⋯ + T₅`). -/
theorem rowF [IsProbabilityMeasure μ] {δ w : V → ℝ} {s Δ Γ D h V₂ pg : ℝ}
    (H : RowStat μ δ w s Δ Γ D h V₂ pg) (a : ℝ) :
    |∫ v, psiS (√(w v)) (a + δ v) ∂μ - psiS s a| ≤ TF s Δ Γ D h V₂ pg := by
  have hs := H.hs
  have hφ0 := phiG_pos 0
  have hφ1 := phiG_pos 1
  have hΔ : 0 ≤ Δ := H.hΔ
  have hΓ : 0 ≤ Γ := (sq_nonneg s).trans H.hsΓ
  have hwm : Measurable (fun v => w v - s ^ 2) := H.mw.sub_const _
  -- integrability
  have iδ : Integrable δ μ := bdd_int H.mδ H.hδb
  have iδ2 : Integrable (fun v => δ v ^ 2) μ := bdd_int (H.mδ.pow_const 2) (C := Δ ^ 2)
    (fun v => sq_abs_le (H.hδb v))
  have hwb : ∀ v, |w v - s ^ 2| ≤ Γ := fun v => abs_w_sub_le (H.hw0 v) (H.hwΓ v) H.hsΓ
  have iw : Integrable (fun v => w v - s ^ 2) μ := bdd_int hwm hwb
  have iw2 : Integrable (fun v => (w v - s ^ 2) ^ 2) μ := bdd_int (hwm.pow_const 2) (C := Γ ^ 2)
    (fun v => sq_abs_le (hwb v))
  obtain ⟨iδw, hCS⟩ := BstLean.Part132.integral_mul_le_sqrt H.mδ hwm iδ2 iw2
  have mX : Measurable (fun v => psiS (√(w v)) (a + δ v)) :=
    measurable_psiS.comp (H.mw.sqrt.prodMk (measurable_const.add H.mδ))
  have iX0 : Integrable (fun v => psiS (√(w v)) (a + δ v)) μ := by
    refine bdd_int mX (C := |a| + Δ + √Γ) (fun v => ?_)
    rw [abs_of_nonneg (BstLean.Part137.psiS_nonneg _ _)]
    refine (BstLean.Part154.psiS_le_abs _ _).trans ?_
    have h1 : |a + δ v| ≤ |a| + Δ := (abs_add_le _ _).trans (by linarith [H.hδb v])
    have h2 : |√(w v)| * √(2 / π) ≤ √Γ := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hc : √(2 / Real.pi) ≤ 1 := by
        rw [Real.sqrt_le_one, div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      calc √(w v) * √(2 / Real.pi) ≤ √(w v) * 1 := by gcongr
        _ ≤ √Γ := by rw [mul_one]; exact Real.sqrt_le_sqrt (H.hwΓ v)
    linarith
  set c := phiG (a / s) / (2 * s) with hc
  have hc0 : 0 ≤ c := by have := phiG_pos (a / s); positivity
  have hc1 : c ≤ phiG 0 / (2 * s) := by
    have := phiG_le_zero (a / s); rw [hc]; gcongr
  set X : V → ℝ := fun v => psiS (√(w v)) (a + δ v) - psiS s a with hXd
  set L : V → ℝ := fun v => PhiG (a / s) * δ v + c * (w v - s ^ 2) with hLd
  set T : V → ℝ := fun v => 1 / 2 * (√2 * phiG 0 / s * δ v ^ 2 +
        2 * phiG 1 / s ^ 2 * (|δ v| * |w v - s ^ 2|) +
        phiG 0 / (√2 * s ^ 3) * (w v - s ^ 2) ^ 2) with hTd
  set K := 2 * Δ + 3 / 2 * phiG 0 / s * Γ with hKd
  set B := {v | w v < s ^ 2 / 2} with hBd
  have hB : MeasurableSet B := measurableSet_lt H.mw measurable_const
  have iX : Integrable X μ := iX0.sub (integrable_const _)
  have iL : Integrable L μ := (iδ.const_mul _).add (iw.const_mul _)
  have iT : Integrable T μ :=
    (((iδ2.const_mul _).add (iδw.const_mul _)).add (iw2.const_mul _)).const_mul _
  have hT0 : ∀ v, 0 ≤ T v := fun v => by simp only [hTd]; positivity
  have hK0 : 0 ≤ K := by positivity
  have hgood : ∀ v, v ∉ B → |X v - L v| ≤ T v := by
    intro v hv
    have hv' : s ^ 2 / 2 ≤ w v := not_lt.mp hv
    exact G_taylor_gen hs hv'
  have hbad : ∀ v, v ∈ B → |X v - L v| ≤ K := by
    intro v _
    refine (G_rough_gen hs (H.hw0 v)).trans ?_
    have := H.hδb v
    have h2 : phiG 0 / s * |w v - s ^ 2| ≤ phiG 0 / s * Γ := by gcongr; exact hwb v
    rw [hKd]
    have e1 : 3 / 2 * phiG 0 / s * |w v - s ^ 2| = 3 / 2 * (phiG 0 / s * |w v - s ^ 2|) := by ring
    have e2 : 3 / 2 * phiG 0 / s * Γ = 3 / 2 * (phiG 0 / s * Γ) := by ring
    rw [e1, e2]; linarith
  have main := bias_split iX iL iT hB hT0 hK0 hgood hbad
  have eX : ∫ v, X v ∂μ = ∫ v, psiS (√(w v)) (a + δ v) ∂μ - psiS s a := by
    simp only [hXd]; rw [integral_sub iX0 (integrable_const _)]; simp
  have eL : ∫ v, L v ∂μ = c * ∫ v, (w v - s ^ 2) ∂μ := by
    simp only [hLd]
    rw [integral_add (iδ.const_mul _) (iw.const_mul _), integral_const_mul, integral_const_mul,
      H.hδ0]; ring
  have eT : ∫ v, T v ∂μ = 1 / 2 * (√2 * phiG 0 / s * ∫ v, δ v ^ 2 ∂μ +
        2 * phiG 1 / s ^ 2 * ∫ v, |δ v| * |w v - s ^ 2| ∂μ +
        phiG 0 / (√2 * s ^ 3) * ∫ v, (w v - s ^ 2) ^ 2 ∂μ) := by
    simp only [hTd]
    have j1 : Integrable (fun v => √2 * phiG 0 / s * δ v ^ 2 +
        2 * phiG 1 / s ^ 2 * (|δ v| * |w v - s ^ 2|)) μ := (iδ2.const_mul _).add (iδw.const_mul _)
    rw [integral_const_mul, integral_add j1 (iw2.const_mul _),
      integral_add (iδ2.const_mul _) (iδw.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [eX, eL, eT] at main
  have hLb : |c * ∫ v, (w v - s ^ 2) ∂μ| ≤ phiG 0 / (2 * s) * h := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul hc1 H.hh (abs_nonneg _) (by positivity)
  have hDV : ∫ v, |δ v| * |w v - s ^ 2| ∂μ ≤ √D * √V₂ := by
    refine hCS.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt H.hD) (Real.sqrt_le_sqrt H.hV) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have hTb : 1 / 2 * (√2 * phiG 0 / s * ∫ v, δ v ^ 2 ∂μ +
        2 * phiG 1 / s ^ 2 * ∫ v, |δ v| * |w v - s ^ 2| ∂μ +
        phiG 0 / (√2 * s ^ 3) * ∫ v, (w v - s ^ 2) ^ 2 ∂μ) ≤
      1 / 2 * (√2 * phiG 0 / s * D + 2 * phiG 1 / s ^ 2 * (√D * √V₂) +
        phiG 0 / (√2 * s ^ 3) * V₂) := by
    have a1 : √2 * phiG 0 / s * ∫ v, δ v ^ 2 ∂μ ≤ √2 * phiG 0 / s * D := by gcongr; exact H.hD
    have a2 : 2 * phiG 1 / s ^ 2 * ∫ v, |δ v| * |w v - s ^ 2| ∂μ ≤
        2 * phiG 1 / s ^ 2 * (√D * √V₂) := by gcongr
    have a3 : phiG 0 / (√2 * s ^ 3) * ∫ v, (w v - s ^ 2) ^ 2 ∂μ ≤ phiG 0 / (√2 * s ^ 3) * V₂ := by
      gcongr; exact H.hV
    linarith
  have hKb : K * μ.real B ≤ pg * K := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right H.hπ hK0
  unfold TF
  rw [← hKd]
  linarith

/-- **The energy row bias** (the paper's `U₁ + ⋯ + U₅`). -/
theorem rowW [IsProbabilityMeasure μ] {δ w : V → ℝ} {s Δ Γ D h V₂ pg : ℝ}
    (H : RowStat μ δ w s Δ Γ D h V₂ pg) (a : ℝ) :
    |∫ v, G2 (√(w v)) (a + δ v) ∂μ - G2 s a| ≤ TW a s Δ Γ D h V₂ pg := by
  have hs := H.hs
  have hφ0 := phiG_pos 0
  have hφ1 := phiG_pos 1
  have hΔ : 0 ≤ Δ := H.hΔ
  have hΓ : 0 ≤ Γ := (sq_nonneg s).trans H.hsΓ
  have hwm : Measurable (fun v => w v - s ^ 2) := H.mw.sub_const _
  have iδ : Integrable δ μ := bdd_int H.mδ H.hδb
  have iδ2 : Integrable (fun v => δ v ^ 2) μ := bdd_int (H.mδ.pow_const 2) (C := Δ ^ 2)
    (fun v => sq_abs_le (H.hδb v))
  have hwb : ∀ v, |w v - s ^ 2| ≤ Γ := fun v => abs_w_sub_le (H.hw0 v) (H.hwΓ v) H.hsΓ
  have iw : Integrable (fun v => w v - s ^ 2) μ := bdd_int hwm hwb
  have iw2 : Integrable (fun v => (w v - s ^ 2) ^ 2) μ := bdd_int (hwm.pow_const 2) (C := Γ ^ 2)
    (fun v => sq_abs_le (hwb v))
  obtain ⟨iδw, hCS⟩ := BstLean.Part132.integral_mul_le_sqrt H.mδ hwm iδ2 iw2
  have mX : Measurable (fun v => G2 (√(w v)) (a + δ v)) :=
    measurable_G2.comp (H.mw.sqrt.prodMk (measurable_const.add H.mδ))
  have iX0 : Integrable (fun v => G2 (√(w v)) (a + δ v)) μ := by
    refine bdd_int mX (C := (|a| + Δ) ^ 2 + Γ) (fun v => ?_)
    rw [abs_of_nonneg (G2_nonneg _ _)]
    refine (G2_le _ _).trans ?_
    rw [Real.sq_sqrt (H.hw0 v)]
    have h1 : |a + δ v| ≤ |a| + Δ := (abs_add_le _ _).trans (by linarith [H.hδb v])
    have h2 : (a + δ v) ^ 2 ≤ (|a| + Δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    linarith [H.hwΓ v]
  set c := PhiG (a / s) with hc
  have hc0 : 0 ≤ c := (PhiG_pos _).le
  have hc1 : c ≤ 1 := PhiG_le_one _
  set X : V → ℝ := fun v => G2 (√(w v)) (a + δ v) - G2 s a with hXd
  set L : V → ℝ := fun v => 2 * psiS s a * δ v + c * (w v - s ^ 2) with hLd
  set T : V → ℝ := fun v => δ v ^ 2 + √2 * phiG 0 / s * (|δ v| * |w v - s ^ 2|) +
        phiG 1 / (2 * s ^ 2) * (w v - s ^ 2) ^ 2 with hTd
  set K := (|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ with hKd
  set B := {v | w v < s ^ 2 / 2} with hBd
  have hB : MeasurableSet B := measurableSet_lt H.mw measurable_const
  have iX : Integrable X μ := iX0.sub (integrable_const _)
  have iL : Integrable L μ := (iδ.const_mul _).add (iw.const_mul _)
  have iT : Integrable T μ :=
    ((iδ2.add (iδw.const_mul _)).add (iw2.const_mul _))
  have hT0 : ∀ v, 0 ≤ T v := fun v => by simp only [hTd]; positivity
  have hK0 : 0 ≤ K := by positivity
  have hgood : ∀ v, v ∉ B → |X v - L v| ≤ T v := by
    intro v hv
    have hv' : s ^ 2 / 2 ≤ w v := not_lt.mp hv
    exact G2_taylor hs hv'
  have hbad : ∀ v, v ∈ B → |X v - L v| ≤ K := by
    intro v _
    refine (G2_rough hs (H.hw0 v)).trans ?_
    have hd := H.hδb v
    have h1 : |a + δ v| ≤ |a| + Δ := (abs_add_le _ _).trans (by linarith)
    have h2 : (a + δ v) ^ 2 ≤ (|a| + Δ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : 2 * (|a| + s) * |δ v| ≤ 2 * (|a| + s) * Δ := by
      have : 0 ≤ |a| + s := by positivity
      gcongr
    have h4 := H.hwΓ v
    have h5 := H.hsΓ
    rw [hKd]; linarith
  have main := bias_split iX iL iT hB hT0 hK0 hgood hbad
  have eX : ∫ v, X v ∂μ = ∫ v, G2 (√(w v)) (a + δ v) ∂μ - G2 s a := by
    simp only [hXd]; rw [integral_sub iX0 (integrable_const _)]; simp
  have eL : ∫ v, L v ∂μ = c * ∫ v, (w v - s ^ 2) ∂μ := by
    simp only [hLd]
    rw [integral_add (iδ.const_mul _) (iw.const_mul _), integral_const_mul, integral_const_mul,
      H.hδ0]; ring
  have eT : ∫ v, T v ∂μ = ∫ v, δ v ^ 2 ∂μ +
        √2 * phiG 0 / s * ∫ v, |δ v| * |w v - s ^ 2| ∂μ +
        phiG 1 / (2 * s ^ 2) * ∫ v, (w v - s ^ 2) ^ 2 ∂μ := by
    simp only [hTd]
    have j1 : Integrable (fun v => δ v ^ 2 +
        √2 * phiG 0 / s * (|δ v| * |w v - s ^ 2|)) μ := iδ2.add (iδw.const_mul _)
    rw [integral_add j1 (iw2.const_mul _),
      integral_add iδ2 (iδw.const_mul _), integral_const_mul, integral_const_mul]
  rw [eX, eL, eT] at main
  have hLb : |c * ∫ v, (w v - s ^ 2) ∂μ| ≤ h := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |∫ v, (w v - s ^ 2) ∂μ| ≤ 1 * h := mul_le_mul hc1 H.hh (abs_nonneg _) zero_le_one
      _ = h := one_mul h
  have hDV : ∫ v, |δ v| * |w v - s ^ 2| ∂μ ≤ √D * √V₂ := by
    refine hCS.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt H.hD) (Real.sqrt_le_sqrt H.hV) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have a2 : √2 * phiG 0 / s * ∫ v, |δ v| * |w v - s ^ 2| ∂μ ≤ √2 * phiG 0 / s * (√D * √V₂) := by
    gcongr
  have a3 : phiG 1 / (2 * s ^ 2) * ∫ v, (w v - s ^ 2) ^ 2 ∂μ ≤ phiG 1 / (2 * s ^ 2) * V₂ := by
    gcongr; exact H.hV
  have hKb : K * μ.real B ≤ pg * K := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right H.hπ hK0
  have hD := H.hD
  unfold TW
  rw [← hKd]
  linarith

end BstLean.Part171
