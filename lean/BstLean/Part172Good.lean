import BstLean.Part172Mk
import BstLean.Part172Node
import BstLean.Part172Sig

/-!
# Part 172 (file `Good`): the four node statistics on the good set

No proof is left open; no `native_decide` or `axiom` is used.

Fix World data `wr` in the window, `A₁` with `‖A₁‖_op ≤ O₁` and a node `g < J_s`. The three
direction fields are `F₁ = e₁`, `F₂ = e₂` (Part 171's plane directions) and
`F₃ = √t_A·ĉ'(x)` (the unit direction of `Π_{U⊥}a₁(x)`). If
* `1/(5n) ≤ ς² ≤ 12/(5n)`,
* almost every `v` is not a kink of `A₁` at `x_v`,
* `E_v |T_k|⁶⁴ ≤ K_k⁶⁴` (`K₁ = K₂ = 7.9/n²`, `K₃ = 6.4/n²`),
then **`node_good`**: `LowStat2 (mkR wr (A₁, 0)) g` holds.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part134 (res)
open BstLean.Part161 (xLat uHat)
open BstLean.Part162 (dirW tanSq)
open BstLean.Part167 (latSq D1A1)
open BstLean.Part170 (tA hB mkR windowW node_bulk)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- `K₁ = 7.9/n²`. -/
noncomputable def K1N (n : ℕ) : ℝ := 79 / (10 * (n : ℝ) ^ 2)

/-- The direction field `F₁ = e₁`. -/
noncomputable def F1 (wr : WRet n) : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) →
    Fin (mA n) → ℝ := fun A _ => e1v (mkR wr (A, 0))

/-- The direction field `F₂ = e₂` at node `g`. -/
noncomputable def F2 (wr : WRet n) (g : ℕ) : Matrix (Fin (mA n)) (Fin n) ℝ →
    (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ := fun A _ => e2v (mkR wr (A, 0)) g

/-- The direction field `F₃ = √t_A·ĉ'(x_v)` at node `g`. -/
noncomputable def F3 (wr : WRet n) (g : ℕ) : Matrix (Fin (mA n)) (Fin n) ℝ →
    (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ := fun A v =>
  √(tA n) • cdirP (mkR wr (A, 0)) (nodeS (mkR wr (0, 0)) g)
    (reluV (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)))

lemma gd_F3_le (wr : WRet n) (g : ℕ) (A' : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ) :
    normSq (F3 wr g A' v) ≤ tA n := by
  unfold F3 cdirP
  rw [smul_smul]
  exact fr_scaled_le _ _ (tA_nonneg n)

lemma gd_relu_cont : Continuous (fun q : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin n → ℝ) =>
    reluV (q.1 *ᵥ q.2)) := by
  unfold reluV relu
  refine continuous_pi fun i => continuous_const.max ?_
  simp only [mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)

lemma gd_F3_meas (wr : WRet n) (g : ℕ) :
    Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F3 wr g p.1 p.2) := by
  have hx : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 p.2)) :=
    BstLean.Part161.measurable_xLat_comp _ measurable_const
      (BstLean.Part53.measurable_unitF.comp measurable_snd)
  have hy : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      reluV (p.1 *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 p.2))) :=
    gd_relu_cont.measurable.comp (measurable_fst.prodMk hx)
  have h := ((fr_meas_cdir wr (nodeS (mkR wr (0, 0)) g)).comp (measurable_fst.prodMk hy)).const_smul
    (√(tA n))
  exact h

lemma gd_meas_left (c₀ : Ret n) (s : ℝ)
    {F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ}
    (hF : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : Measurable (fun v => Tf c₀ s F A v) :=
  (mk_meas_Tf c₀ s hF).comp (f := fun v : Fin (n - 1) → ℝ => (A, v))
    (measurable_const.prodMk measurable_id)

/-- The moment chain `64 → 1`. -/
lemma gd_chain {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
    {f : V → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) {K : ℝ} (hK : 0 < K)
    (h : ∫ v, |f v| ^ 64 ∂μ ≤ K ^ 64) :
    ∫ v, |f v| ^ 8 ∂μ ≤ K ^ 8 ∧ ∫ v, |f v| ^ 4 ∂μ ≤ K ^ 4 ∧ ∫ v, |f v| ^ 2 ∂μ ≤ K ^ 2 ∧
      ∫ v, |f v| ∂μ ≤ K := by
  have hm : Measurable (fun v => |f v|) := hf.abs
  have hC' : ∀ v, |(|f v|)| ≤ C := fun v => by rw [abs_abs]; exact hC v
  have h32 := mo_half hm hC' 32 hK (by simpa using h)
  have h16 := mo_half hm hC' 16 hK (by simpa using h32)
  have h8 := mo_half hm hC' 8 hK (by simpa using h16)
  have h4 := mo_half hm hC' 4 hK (by simpa using h8)
  have h2 := mo_half hm hC' 2 hK (by simpa using h4)
  have h1 := mo_half hm hC' 1 hK (by simpa using h2)
  exact ⟨h8, h4, h2, by simpa using h1⟩

/-- `∫ f ≤ ∫ |g|` if `f ≤ g` a.e. and `g` is integrable. -/
lemma gd_int_le {V : Type*} [MeasurableSpace V] {μ : Measure V} {f g : V → ℝ}
    (hg : Integrable g μ) (h : ∀ᵐ v ∂μ, f v ≤ g v) : ∫ v, f v ∂μ ≤ ∫ v, |g v| ∂μ := by
  by_cases hf : Integrable f μ
  · exact (integral_mono_ae hf hg h).trans (integral_mono hg hg.abs fun v => le_abs_self _)
  · rw [integral_undef hf]; exact integral_nonneg fun _ => abs_nonneg _

/-- **The four node statistics on the good set.** -/
theorem node_good (hn : 80000 ≤ n) {wr : WRet n} (hw : windowW wr)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (h1 : OpB A (O1n n)) {g : ℕ} (hg : g < Js n)
    (hσl : SminN n ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g))
    (hσu : vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) ≤ 12 / (5 * (n : ℝ)))
    (hk : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ i, (A *ᵥ xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (unitF53 v)) i ≠ 0)
    (hb1 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F1 wr) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K1N n ^ 64)
    (hb2 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F2 wr g) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K1N n ^ 64)
    (hb3 : ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v| ^ 64
      ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ 64) :
    LowStat2 (mkR wr (A, 0)) g := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (nodeS (mkR wr (0, 0)) g) ^ 2 ≤ 1 := node_bulk hn hw (A, 0) hg
  have hc : (mkR wr (0, 0)).1.2 ≠ 0 := sg_wr_ne hn1 hw
  have hc' : (mkR wr (A, 0)).1.2 ≠ 0 := hc
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hK1 : 0 < K1N n := by unfold K1N; positivity
  have hK3 : 0 < K3N n := by unfold K3N; positivity
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part168.stdGauss_zero (by omega)
    rw [ae_iff]; simpa using h0
  -- measurability and bounds of the three statistics in `v`
  have hmT : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      Measurable (fun v => Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v) := fun F hF =>
    gd_meas_left _ _ hF A
  have hF1m : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      F1 wr p.1 p.2) := (fr_meas_e1 wr).comp measurable_fst
  have hF2m : Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) =>
      F2 wr g p.1 p.2) := (fr_meas_e2 wr g).comp measurable_fst
  have hF3m := gd_F3_meas wr g
  have hB1 : ∀ A' v, normSq (F1 wr A' v) ≤ tA n := fun A' v => e1v_normSq_le _
  have hB2 : ∀ A' v, normSq (F2 wr g A' v) ≤ tA n := fun A' v => e2v_normSq_le _ _
  have hB3 : ∀ A' v, normSq (F3 wr g A' v) ≤ tA n := gd_F3_le wr g
  have hCb : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      (∀ A' v, normSq (F A' v) ≤ tA n) → ∀ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ≤
        |1 - (nodeS (mkR wr (0, 0)) g) ^ 2| * (tA n * (∑ i, ∑ l, A i l ^ 2) * 3) :=
    fun F hF v => mk_bdd hn1 hc (nodeS (mkR wr (0, 0)) g) F hF A v
  obtain ⟨-, -, -, h11⟩ := gd_chain (hmT _ hF1m) (hCb _ hB1) hK1 hb1
  obtain ⟨-, -, -, h21⟩ := gd_chain (hmT _ hF2m) (hCb _ hB2) hK1 hb2
  obtain ⟨h38, h34, h32, h31⟩ := gd_chain (hmT _ hF3m) (hCb _ hB3) hK3 hb3
  have hi : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) → ∀ k : ℕ,
      Integrable (fun v => |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ^ k) (stdGauss (Fin (n - 1))) := fun F hF hB k =>
    mo_bdd_pow (hmT F hF).abs (fun v => by rw [abs_abs]; exact hCb F hB v) k
  -- DstN
  have hT1i : ∀ F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) → Fin (mA n) → ℝ,
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) →
      Integrable (fun v => Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v) (stdGauss (Fin (n - 1))) := fun F hF hB =>
    mo_bdd_int (hmT F hF) (hCb F hB)
  have hDe : ∀ (e : Fin (mA n) → ℝ) (F : Matrix (Fin (mA n)) (Fin n) ℝ → (Fin (n - 1) → ℝ) →
      Fin (mA n) → ℝ), (∀ v, F A v = e) →
      Measurable (fun p : Matrix (Fin (mA n)) (Fin n) ℝ × (Fin (n - 1) → ℝ) => F p.1 p.2) →
      (∀ A' v, normSq (F A' v) ≤ tA n) →
      ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v| ∂stdGauss (Fin (n - 1)) ≤ K1N n →
      ∫ v, tanSq (fun x => e ⬝ᵥ reluV ((A1 (mkR wr (A, 0))) *ᵥ x)) (mkR wr (A, 0))
        (nodeS (mkR wr (A, 0)) g) v ∂stdGauss (Fin (n - 1)) ≤ K1N n := by
    intro e F hFe hF hB hK
    have hcg : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
        tanSq (fun x => e ⬝ᵥ reluV ((A1 (mkR wr (A, 0))) *ᵥ x)) (mkR wr (A, 0))
          (nodeS (mkR wr (A, 0)) g) v = Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) F A v := by
      filter_upwards [hnz, hk] with v hv hkv
      have ht := tan_dot (s := nodeS (mkR wr (A, 0)) g) hn1 hc' hs hv (A1 (mkR wr (A, 0))) e hkv
      rw [ht]
      simp only [Tf, hFe]
      rfl
    rw [integral_congr_ae hcg]
    exact (integral_mono (hT1i F hF hB) (hT1i F hF hB).abs fun v => le_abs_self _).trans hK
  have hD1 := hDe (e1v (mkR wr (A, 0))) (F1 wr) (fun v => rfl) hF1m hB1 h11
  have hD2 := hDe (e2v (mkR wr (A, 0)) g) (F2 wr g) (fun v => rfl) hF2m hB2 h21
  have hDst : DstN (mkR wr (A, 0)) g ≤ DmN n := by
    have H := DstN_le_tan (by omega) (mkR wr (A, 0)) g hs hO h1
    have H2 : ((n : ℝ) - 2) * DstN (mkR wr (A, 0)) g ≤ 2 * K1N n := by
      have := add_le_add hD1 hD2
      linarith
    unfold DmN
    unfold K1N at H2
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    rw [le_div_iff₀ (by positivity)]
    have hD0 := DstN_nonneg (mkR wr (A, 0)) g
    have e : DstN (mkR wr (A, 0)) g ≤ 2 * (79 / (10 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2) := by
      rw [le_div_iff₀ hn2]; linarith
    calc DstN (mkR wr (A, 0)) g * (n : ℝ) ^ 3 ≤ 2 * (79 / (10 * (n : ℝ) ^ 2)) / ((n : ℝ) - 2) * (n : ℝ) ^ 3 := by
          gcongr
      _ ≤ 16 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hn2]
          field_simp
          nlinarith
  -- the field `S`
  have hrh : ∑ j, res (hB (mkR wr (A, 0))) (a1Bar (mkR wr (A, 0)) (nodeS (mkR wr (0, 0)) g)) j * hB (mkR wr (A, 0)) j = 0 := by
    rw [← BstLean.Part170.perp_eq_res]; exact gr_perp_orth _ _
  have hSle : ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v ≤ Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v := by
    filter_upwards [hnz, hk] with v hv hkv
    exact tan_sqrtw hn1 hc' hs hv A (tA n) (hB (mkR wr (A, 0))) (res (hB (mkR wr (A, 0))) (a1Bar (mkR wr (A, 0)) (nodeS (mkR wr (0, 0)) g))) hrh hkv
  have hT1 : ∫ v, tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n :=
    (gd_int_le (hT1i _ hF3m hB3) hSle).trans h31
  have hTq : ∀ q : ℕ, 1 ≤ q → ∫ v, |Tf (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g) (F3 wr g) A v| ^ q ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ q →
      ∫ v, |√(tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v)| ^ (2 * q) ∂stdGauss (Fin (n - 1)) ≤ K3N n ^ q := by
    intro q _ hq
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun v => by positivity)
      (hi _ hF3m hB3 q) ?_) hq
    filter_upwards [hSle] with v hv
    rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul]
    rcases le_total 0 (tanSq (SN (mkR wr (A, 0)) g) (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) g) v) with ht | ht
    · rw [Real.sq_sqrt ht]
      exact pow_le_pow_left₀ ht (hv.trans (le_abs_self _)) q
    · rw [Real.sqrt_eq_zero'.mpr ht]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [zero_pow (by omega)]; positivity
  have hT2 := hTq 2 (by norm_num) h32
  have hT4 := hTq 4 (by norm_num) h34
  have hT8 := hTq 8 (by norm_num) h38
  exact ⟨hσl, hDst, V2N_of_tan (mkR wr (A, 0)) g hn hs h1 hσu hDst hT1 hT2,
    piN_of_tan (mkR wr (A, 0)) g hn hs h1 hσl hσu hDst hT1 hT4 hT8⟩

end BstLean.Part172
