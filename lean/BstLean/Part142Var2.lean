import BstLean.Part142Var

/-!
# Part 142 (step S1): the error term with the variance of the stand-in

Role: `delegations/statements/p142-spec.md`, item 4 (the stand-in term). `Part142Var` has the
bound for fixed `(M₁, M₂)`; this file integrates over `(M₁, M₂)` and carries the gain to the
sample estimate of Part 141.

* `Vb n = 1 − κ^{∘6}(0) + σ₄·(eWr + sU) + eAFr + 1.83/n ≤ 0.2736` (`Vb_le`): the bound of the
  mean variance of `F∘A` under the stand-in, in units of `S = 4/n` (Parts 139 to 141 use `1`).
* `XA142 n ζ η η′ = (1 + η′)((1 + η)(1.83/n)·Vb n + 4(1 + 1/η)·EHH n ζ) + (1 + 1/η′)·pertA n`;
  `XA142_le`: `XA142 n (1/20) (1/20) (1/100) ≤ 0.64/n` (Part 141: `XA ≤ 2.05/n`).
* `tX_L2_W`, `DTh_mean`: `E_θ D_θ ≤ 1 − κ^{∘6}(0) + σ₄·(eWr + sU)`.
* **`errVecHat142_lint`**, **`errVecA142_lint`**, **`errSampleA142_lint`**,
  **`errSampleTailA142`**: the statements `errVecHat_lint`, `errVecA_lint`, `errSampleA_lint`,
  `errSampleTailA` of Parts 140 and 141 with the factor `Vb n` in the stand-in term (the proofs
  are those of Parts 140 and 141 with `errFixedHat142` in the place of `errFixedHat`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-- **The bound of the mean variance under the stand-in**, in units of `S = 4/n`. -/
noncomputable def Vb (n : ℕ) : ℝ :=
  1 - kappa^[6] 0 + sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) + eAFr n (mA n) (mF n) +
    183 / 100 / (n : ℝ)

/-- The constant of the error term with the variance of the stand-in. -/
noncomputable def XA142 (n : ℕ) (ζ η η' : ℝ) : ℝ :=
  (1 + η') * ((1 + η) * (183 / 100 / (n : ℝ)) * Vb n + 4 * (1 + 1 / η) * EHH n ζ) +
    (1 + 1 / η') * pertA n

lemma eWr_nonneg142 {n : ℕ} (hn : 1 ≤ n) (N mW : ℕ) : 0 ≤ eWr N n mW := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := q_mem
  have hsm := eWsmall_nonneg n mW
  have hsU := sU_nonneg N
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  unfold eWr; positivity

lemma eAFr_nonneg142 {n mA mF : ℕ} (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    0 ≤ eAFr n mA mF := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcF := BstLean.Part133.cF2o_pos hmF
  have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn
  unfold eAFr; positivity

lemma Vb_nonneg {n : ℕ} (hn : 4096 ≤ n) : 0 ≤ Vb n := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have h1 : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h2 := sig4_nonneg
  have h3 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have h4 := sU_nonneg (2 * n)
  have h5 := eAFr_nonneg142 hn1 hmA hmF
  have h6 : (0 : ℝ) ≤ 1 - kappa^[6] 0 := by linarith
  unfold Vb
  positivity

/-- `Vb n ≤ 0.2736` for `n ≥ 4096`. -/
lemma Vb_le {n : ℕ} (hn : 4096 ≤ n) : Vb n ≤ 2736 / 10000 := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_scale hn
  have h2 := eWr_scale hn
  have h3 := sU_scale hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have hQ : 7771 / 10000 ≤ kappa^[6] 0 := kappa6_zero_ge'
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 64 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hs
  have e1 : (25365 : ℝ) / 10000 / √(n : ℝ) = 25365 / 10000 * t := by rw [ht]; ring
  have e2 : (11746 : ℝ) / 10000 / √(n : ℝ) = 11746 / 10000 * t := by rw [ht]; ring
  have e3 : (3629 : ℝ) / 10000 / √(n : ℝ) = 3629 / 10000 * t := by rw [ht]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (15375 / 10000 * t) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  have h6 : 183 / 100 / (n : ℝ) ≤ 183 / 100 / 4096 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold Vb
  nlinarith

lemma XA142_nonneg {n : ℕ} (hn : 4096 ≤ n) (ζ : ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ}
    (hη' : 0 < η') : 0 ≤ XA142 n ζ η η' := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have hV := Vb_nonneg hn
  unfold XA142
  positivity

/-- `XA142 n (1/20) (1/20) (1/100) ≤ 0.64/n` (Part 141: `XA n (1/20) (1/20) (1/100) ≤ 2.05/n`).
-/
lemma XA142_le {n : ℕ} (hn : 4096 ≤ n) :
    XA142 n (1 / 20) (1 / 20) (1 / 100) ≤ 64 / 100 * (1 / (n : ℝ)) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hEH' := EHH_scale hn
  have hEH0 := EHH_nonneg hn (1 / 20)
  have hp := pertA_eq (n := n) (by omega)
  have ht0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hV := Vb_le hn
  have hV0 := Vb_nonneg hn
  unfold XA142
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * (1 / (n : ℝ)) := by ring
  rw [e183, hp]
  have e84 : (4 : ℝ) * (1 + 1 / (1 / 20)) = 84 := by norm_num
  have e101 : (1 : ℝ) + 1 / (1 / 100) = 101 := by norm_num
  rw [e84, e101]
  have h1 : 183 / 100 * (1 / (n : ℝ)) * Vb n ≤ 183 / 100 * (1 / (n : ℝ)) * (2736 / 10000) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  nlinarith

/-! ## The mean of `D_θ` -/

section tx

variable {N mW n : ℕ}

/-- `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ eWr + sU` under `(u, u′) ⊗ W`. -/
theorem tX_L2_W (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        tX (N := N) (mW := mW) (n := n) z - kappa (kappa 0)) (eWr N n mW + sU N) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hq := q_mem
  have hsU := sU_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have := lawU2_prob hN
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCos n := by unfold jCos; positivity
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2b (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmall
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp uu.1 uu.2))
      (eWr N n mW) := by
    have h1 := sphere_gW_L2 hN (1 / √(n : ℝ)) (by positivity)
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmall n mW)
        (eWsmall n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have h3 := h1.add0 h2 (by unfold sU at hsU; positivity) hsm
    exact h3
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU N) := sphere_kk_L2r hN
  have hW0 : 0 ≤ eWr N n mW := by unfold eWr; positivity
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have md : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      dotp z.1.1 z.1.2) :=
    measurable_dotp_comp (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
  have m2 : Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      tX (N := N) (mW := mW) (n := n) z - kappa (kappa (dotp z.1.1 z.1.2))) :=
    measurable_tX.sub (hkk.comp md)
  have A2 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        tX (N := N) (mW := mW) (n := n) z - kappa (kappa (dotp z.1.1 z.1.2))) (eWr N n mW) := by
    refine L2le.prod' m2.aestronglyMeasurable hgW ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    exact hW uu.1 uu.2 huu.1 huu.2
  have A3 : L2le ((lawU2 N).prod (mlpGauss N mW n))
      (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
        kappa (kappa (dotp z.1.1 z.1.2)) - kappa (kappa 0)) (sU N) := hU.comp_fst
  refine ((A2.add0 A3 hW0 hsU).congr_fun fun z => ?_)
  ring

end tx

/-- **The mean of `D_θ`**: `E_θ D_θ ≤ 1 − κ^{∘6}(0) + σ₄·(eWr + sU)`. -/
theorem DTh_mean {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (DTh n) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, DTh n θ ∂hidGauss (2 * n) (mW n) ≤
        1 - kappa^[6] 0 + sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  have := lawU2_prob hN
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set r : (HidParam (2 * n) (mW n) × Matrix (Fin n) (Fin (mW n)) ℝ) ×
      ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) → ℝ := fun q =>
    1 - kappa^[4] (tX (N := 2 * n) (mW := mW n) (n := n)
      (q.2, ((q.1.1.1, q.1.1.2, q.1.2) : MlpParam (2 * n) (mW n) n))) with hr
  have br : BM r := bm_rD hn1
  have bΦ : BM (fun q : HidParam (2 * n) (mW n) × Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ uu, r (q, uu) ∂lawU2 (2 * n)) := br.integral_right (lawU2 (2 * n))
  have bD : BM (fun θ : HidParam (2 * n) (mW n) =>
      ∫ M₃, (∫ uu, r ((θ, M₃), uu) ∂lawU2 (2 * n)) ∂gM) := bΦ.integral_right gM
  have iD : Integrable (DTh n) (hidGauss (2 * n) (mW n)) := bD.integrable _
  refine ⟨iD, ?_⟩
  have e1 : ∫ θ, DTh n θ ∂hidGauss (2 * n) (mW n) =
      ∫ q, (∫ uu, r (q, uu) ∂lawU2 (2 * n)) ∂((hidGauss (2 * n) (mW n)).prod gM) :=
    (integral_prod (fun q : HidParam (2 * n) (mW n) × Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ uu, r (q, uu) ∂lawU2 (2 * n)) (bΦ.integrable _)).symm
  -- the same integral over `(u, u′) ⊗ W`
  set Fz : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n → ℝ :=
    fun z => 1 - kappa^[4] (tX (N := 2 * n) (mW := mW n) (n := n) z) with hFz
  have bF : BM Fz := by
    refine ⟨measurable_const.sub ((continuous_kappa.iterate 4).measurable.comp measurable_tX),
      1, fun z => ?_⟩
    have h := k4_mem (tX_mem (N := 2 * n) (mW := mW n) hn1 z)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have e2 : ∫ z, Fz z ∂((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n)) =
      ∫ q, (∫ uu, r (q, uu) ∂lawU2 (2 * n)) ∂((hidGauss (2 * n) (mW n)).prod gM) := by
    rw [integral_prod_symm Fz (bF.integrable _), e,
      integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable
        (bF.integral_left (lawU2 (2 * n))).meas.aestronglyMeasurable]
    rfl
  rw [e1, ← e2]
  -- the bound
  have hL := tX_L2_W (N := 2 * n) (mW := mW n) hn1 hN hmW
  set g : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × MlpParam (2 * n) (mW n) n → ℝ :=
    fun z => |tX (N := 2 * n) (mW := mW n) (n := n) z - kappa (kappa 0)| with hg
  have bg : BM g := by
    refine ⟨(measurable_tX.sub measurable_const).abs, 2, fun z => ?_⟩
    have h := tX_mem (N := 2 * n) (mW := mW n) hn1 z
    have hq := q_mem
    rw [hg, abs_abs, abs_le]
    constructor <;> linarith [h.1, h.2, hq.1, hq.2]
  have hB0 : 0 ≤ eWr (2 * n) n (mW n) + sU (2 * n) := by
    have := eWr_nonneg142 hn1 (2 * n) (mW n)
    have := sU_nonneg (2 * n)
    linarith
  have hgint : ∫ z, g z ∂((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n)) ≤
      eWr (2 * n) n (mW n) + sU (2 * n) := by
    have h1 := sq_integral_le (ρ := (lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n))
      (f := g) (bg.sq.integrable _)
    have h2 : ∫ z, g z ^ 2 ∂((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n)) =
        ∫ z, (tX (N := 2 * n) (mW := mW n) (n := n) z - kappa (kappa 0)) ^ 2
          ∂((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by rw [hg]; exact sq_abs _)
    rw [h2] at h1
    exact (abs_le_of_sq_le_sq' (h1.trans hL.le) hB0).2
  have hs4 := sig4_nonneg
  have hpt : ∀ z, Fz z ≤ (1 - kappa^[6] 0) + sig4 * g z := by
    intro z
    have h := iter4_chord (tX_mem (N := 2 * n) (mW := mW n) hn1 z)
    have h' := (abs_le.mp h).1
    rw [hFz, hg]
    linarith
  have hi2 : Integrable (fun z => (1 - kappa^[6] 0) + sig4 * g z)
      ((lawU2 (2 * n)).prod (mlpGauss (2 * n) (mW n) n)) :=
    (integrable_const _).add ((bg.integrable _).const_mul _)
  have h3 := integral_mono (bF.integrable _) hi2 hpt
  rw [integral_add (integrable_const _) ((bg.integrable _).const_mul _), integral_const_mul]
    at h3
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h3
  have h4 := mul_le_mul_of_nonneg_left hgint hs4
  linarith

/-! ## Joint over `(W, A, F)` -/

/-- **`errVecHat_lint` of Part 140 with the variance of the stand-in.** -/
theorem errVecHat142_lint {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) * Vb n +
        4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := goodHat_meas (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGH n t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
  set G : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hG
  have mG : Measurable G := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, G W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mG MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => G (MeasurableEquiv.prodAssoc a))
      (mG.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := (1 + η) * (183 / 100 / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have he0 : 0 ≤ eAFr n (mA n) (mF n) := by
    have hcF := BstLean.Part133.cF2o_pos hmF
    have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
    unfold eAFr; positivity
  set δ : ℝ := 183 / 100 / (n : ℝ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  set dd : HidParam (2 * n) (mW n) → ℝ := fun θ => DTh n θ + eAFr n (mA n) (mF n) + δ with hdd
  have hdd0 : ∀ θ, 0 ≤ dd θ := fun θ => by
    have := DTh_nonneg hn1 θ
    rw [hdd]; positivity
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * (goodHat n).indicator dd θ +
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ (goodHat n).indicator dd θ :=
      Set.indicator_nonneg (fun θ _ => hdd0 θ) _
    have h2 : 0 ≤ (goodHat n).indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ goodHat n
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWH n := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapHat W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapHat hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapHat gHat
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapHat at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errGH, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      refine (errFixedHat142 hn hθ hζ0.le hζ1 hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS, hdd, hδ]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWH n := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGH, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarH_mean hn hζ0 hζ1
  obtain ⟨iD, hDb⟩ := DTh_mean hn
  have idd : Integrable dd (hidGauss (2 * n) (mW n)) :=
    (iD.add (integrable_const _)).add (integrable_const _)
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * (goodHat n).indicator dd θ) (hidGauss (2 * n) (mW n)) :=
    (idd.indicator mE).const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * (goodHat n).indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, G (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have e1 : ∫ θ, (goodHat n).indicator dd θ ∂hidGauss (2 * n) (mW n) ≤ Vb n := by
          have h0 : ∫ θ, (goodHat n).indicator dd θ ∂hidGauss (2 * n) (mW n) ≤
              ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) :=
            integral_mono (idd.indicator mE) idd
              (fun θ => Set.indicator_le_self' (fun θ _ => hdd0 θ) θ)
          have h1 : ∫ θ, dd θ ∂hidGauss (2 * n) (mW n) =
              (∫ θ, DTh n θ ∂hidGauss (2 * n) (mW n)) + eAFr n (mA n) (mF n) + δ := by
            have e' : dd = fun θ => (DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ) +
                (fun _ => δ) θ := by rw [hdd]
            rw [e', integral_add (f := fun θ => DTh n θ + (fun _ => eAFr n (mA n) (mF n)) θ)
                (iD.add (integrable_const _)) (integrable_const _),
              integral_add (f := fun θ => DTh n θ) iD (integrable_const _)]
            simp
          unfold Vb
          rw [h1] at h0
          linarith
        have h1 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        rw [ha, hS] at h1
        rw [hS] at h2
        rw [ha, hS]
        linarith


/-- **`errVecA_lint` of Part 141 with the variance of the stand-in.** -/
theorem errVecA142_lint {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ}
    (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (XA142 n ζ η η' * (4 / (n : ℝ))) := by
  have hVb := Vb_nonneg hn
  unfold XA142
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGH n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGH hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGA n t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGA hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGA n t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t) := by
    intro t
    have h0 := errGH_nonneg n t
    have h0' := dGA_nonneg n t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWA n
    · have ht' : t.1 ∈ goodWH n := goodWA_sub n ht
      simp only [errGA, errGH, dGA, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGA, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGH n t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGA n t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGH n t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGA n t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * (183 / 100 / (n : ℝ)) * Vb n +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHat142_lint hn hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecA_lint hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring


/-- **`errSampleA_lint` of Part 141 with the variance of the stand-in.** For `n ≥ 4096`,
`0 < ζ < 1`, `k ≥ 1`: `E[1_good(W)·(g̃_k − B)²] ≤ (XA142 n ζ η η′ + 1/k)·(4/n)`. -/
theorem errSampleA142_lint {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XA142_nonneg hn ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSA k n p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSA hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set L : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hL
  have mL : Measurable L := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, L t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, L (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSA k n (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preA W) := measurable_preA_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preA W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWA n
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSA k n ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSA, Set.indicator_of_mem hW, gSampleA]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preA W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] := he
      rw [he', ← gA_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n))]
      have hG : errGA n (W, A, F) = (gA W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGA, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hL]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hG,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSA k n ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSA, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSA k n (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGA n t) + ENNReal.ofReal ((k : ℝ)⁻¹) * L t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGA n t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGA n t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGA hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XA142 n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecA142_lint hn hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring

/-- The tail form: for `s > 0`:
`Pr(W good and (g̃_k − B)² ≥ s) ≤ (XA n ζ η η′ + 1/k)·(4/n)/s`. -/
theorem errSampleTailA142 {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hX := XA142_nonneg hn ζ hη hη'
  have h := errSampleA142_lint hn hζ0 hζ1 hη hη' hk
  have hc : (0 : ℝ) ≤ (XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by positivity
  have h0 : 0 ≤ᵐ[(mlpTriple 2 n).prod (gamK k n)] errSA k n :=
    Filter.Eventually.of_forall (errSA_nonneg k n)
  have hm := (measurable_errSA hn1 k).aestronglyMeasurable
    (μ := (mlpTriple 2 n).prod (gamK k n))
  have hi : Integrable (errSA k n) ((mlpTriple 2 n).prod (gamK k n)) :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  have hb : ∫ p, errSA k n p ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      (XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by
    rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
    exact ENNReal.toReal_le_of_le_ofReal hc h
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := (mlpTriple 2 n).prod (gamK k n))
    (f := errSA k n) h0 hi s
  rw [le_div_iff₀ hs]
  linarith


end BstLean.Part142

open BstLean.Part142 in
#print axioms DTh_mean
open BstLean.Part142 in
#print axioms errVecHat142_lint
open BstLean.Part142 in
#print axioms errVecA142_lint
open BstLean.Part142 in
#print axioms errSampleA142_lint
open BstLean.Part142 in
#print axioms errSampleTailA142
open BstLean.Part142 in
#print axioms Vb_le
open BstLean.Part142 in
#print axioms Vb_nonneg
open BstLean.Part142 in
#print axioms XA142_le
