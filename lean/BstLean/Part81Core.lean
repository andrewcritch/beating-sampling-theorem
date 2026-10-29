import BstLean.Part81Defs
import BstLean.Part81Mean
import BstLean.Part81Bridge

/-!
# Part 81, core: the transfer chain of Part 78 with the constants as parameters, map degree `d`

* `Core.det_core`: the deterministic core, with the smoothing constant `e` and floor constant `β`.
* `Core.pw_core`: the sphere quantities in terms of the Gaussian ones.
* `uw_fail`: the failure probability in the split coordinates, on the good radius event.
* `fail81_core`: the failure probability of `g₀` on the coefficient sphere, parametric form.
-/

namespace BstLean.Part81.Core

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part78 (nsq frobH trH qfun aU zv Phi markov_gt meas_le_ofReal nsq_nonneg
  frobH_nonneg trH_sq_le abc_sq qexp varU_affine_lower nsq_aU0_int GaussLin)
open BstLean.Part81

variable {n d : ℕ}

/-- Deterministic core, parametrized by the smoothing constant `e` and the floor constant `β`. -/
lemma det_core {τ VS VGa VQ eS eG e2 trt Wfv v nR δ ε ε₁ κ lam TQ T2 e β : ℝ}
    (hτ : |τ - 1| ≤ δ) (hδ : δ ≤ 1 / 100) (hβ : 0 < β)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hVQ0 : 0 ≤ VQ) (hv : 0 ≤ v) (hTQ : 0 ≤ TQ)
    (hT2 : 0 ≤ T2) (hnR : 0 ≤ nR)
    (hVS : τ ^ 2 * ((1 - lam) * VGa - (1 / lam) * (τ - 1) ^ 2 * VQ) ≤ VS)
    (heS : eS = τ * eG + τ * (τ - 1) * e2 + e * trt * (τ ^ 2 - 1))
    (h1 : κ * Wfv ≤ VGa) (h2 : VQ ≤ TQ * v) (h3 : e2 ^ 2 ≤ T2 * v) (h4 : eG ^ 2 ≤ ε₁ ^ 2 * Wfv)
    (h5 : trt ^ 2 ≤ nR * v) (h6 : β * v ≤ Wfv)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 22 * (409 / 100) * e ^ 2 * δ ^ 2 * nR
        + ε ^ 2 * δ ^ 2 * TQ / lam) / β ≤ ε ^ 2 * (1 - lam) * κ) :
    eS ^ 2 ≤ ε ^ 2 * VS := by
  obtain ⟨hτl, hτu⟩ := abs_le.mp hτ
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hτ
  have hτlo : 99 / 100 ≤ τ := by linarith
  have hτhi : τ ≤ 101 / 100 := by linarith
  have hd2 : (τ - 1) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hd20 : 0 ≤ (τ - 1) ^ 2 := sq_nonneg _
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg _
  have hbb : ((τ - 1) * e2) ^ 2 ≤ δ ^ 2 * (T2 * v) := by
    have : ((τ - 1) * e2) ^ 2 = (τ - 1) ^ 2 * e2 ^ 2 := by ring
    rw [this]
    exact mul_le_mul hd2 h3 (sq_nonneg _) (sq_nonneg _)
  have hτ1 : (τ + 1) ^ 2 ≤ 409 / 100 * τ ^ 2 := by nlinarith
  have hcc : (e * trt * (τ - 1) * (τ + 1)) ^ 2 ≤
      τ ^ 2 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v)) := by
    have e' : (e * trt * (τ - 1) * (τ + 1)) ^ 2 =
        e ^ 2 * ((τ + 1) ^ 2 * ((τ - 1) ^ 2 * trt ^ 2)) := by ring
    have m1 : (τ - 1) ^ 2 * trt ^ 2 ≤ δ ^ 2 * (nR * v) :=
      mul_le_mul hd2 h5 (sq_nonneg _) (sq_nonneg _)
    have m0 : 0 ≤ (τ - 1) ^ 2 * trt ^ 2 := by positivity
    have m3 := mul_le_mul hτ1 m1 m0 (by positivity : (0 : ℝ) ≤ 409 / 100 * τ ^ 2)
    have m5 := mul_le_mul_of_nonneg_left m3 (sq_nonneg e)
    rw [e']
    refine m5.trans (le_of_eq ?_)
    ring
  have key : eS ^ 2 ≤ 11 / 10 * (τ ^ 2 * eG ^ 2) + 22 * (τ ^ 2 * ((τ - 1) * e2) ^ 2) +
      22 * (e * trt * (τ - 1) * (τ + 1)) ^ 2 := by
    have : eS = τ * eG + τ * ((τ - 1) * e2) + e * trt * (τ - 1) * (τ + 1) := by
      rw [heS]; ring
    have h := abc_sq (τ * eG) (τ * ((τ - 1) * e2)) (e * trt * (τ - 1) * (τ + 1))
    have e1 : (τ * eG) ^ 2 = τ ^ 2 * eG ^ 2 := by ring
    have e2' : (τ * ((τ - 1) * e2)) ^ 2 = τ ^ 2 * ((τ - 1) * e2) ^ 2 := by ring
    rw [e1, e2'] at h
    rw [this]; exact h
  have hlamVQ : (1 / lam) * (τ - 1) ^ 2 * VQ ≤ (1 / lam) * (δ ^ 2 * (TQ * v)) := by
    have : (1 / lam) * (τ - 1) ^ 2 * VQ = (1 / lam) * ((τ - 1) ^ 2 * VQ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hd2 h2 hVQ0 (sq_nonneg _)) (by positivity)
  have hVS' : τ ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v))) ≤ VS := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hτ2) hVS
    have : (1 - lam) * (κ * Wfv) ≤ (1 - lam) * VGa :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  have hW0 : 0 ≤ Wfv := le_trans (mul_nonneg hβ.le hv) h6
  have hcoef : 0 ≤ 22 * δ ^ 2 * T2 + 22 * (409 / 100) * e ^ 2 * δ ^ 2 * nR
      + ε ^ 2 * δ ^ 2 * TQ / lam := by positivity
  have h6' : v ≤ Wfv / β := by rw [le_div_iff₀ hβ]; linarith
  have hsc : 11 / 10 * (ε₁ ^ 2 * Wfv) + 22 * (δ ^ 2 * (T2 * v))
      + 22 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v))
      ≤ ε ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v))) := by
    have a1 := mul_le_mul_of_nonneg_right hnum hW0
    have a2 := mul_le_mul_of_nonneg_left h6' hcoef
    have a3 : ε ^ 2 * ((1 / lam) * (δ ^ 2 * (TQ * v))) = ε ^ 2 * δ ^ 2 * TQ / lam * v := by
      ring
    have a5 : (11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 22 * (409 / 100) * e ^ 2 * δ ^ 2 * nR
        + ε ^ 2 * δ ^ 2 * TQ / lam) / β) * Wfv = 11 / 10 * (ε₁ ^ 2 * Wfv) +
        (22 * δ ^ 2 * T2 + 22 * (409 / 100) * e ^ 2 * δ ^ 2 * nR
        + ε ^ 2 * δ ^ 2 * TQ / lam) * (Wfv / β) := by ring
    have a6 : (22 * δ ^ 2 * T2 + 22 * (409 / 100) * e ^ 2 * δ ^ 2 * nR
        + ε ^ 2 * δ ^ 2 * TQ / lam) * v = 22 * (δ ^ 2 * (T2 * v))
        + 22 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v)) + ε ^ 2 * δ ^ 2 * TQ / lam * v := by
      ring
    have a7 : ε ^ 2 * (1 - lam) * κ * Wfv = ε ^ 2 * ((1 - lam) * (κ * Wfv)) := by ring
    rw [mul_sub, a3]
    rw [a5] at a1
    rw [a6] at a2
    rw [a7] at a1
    linarith
  calc eS ^ 2 ≤ 11 / 10 * (τ ^ 2 * eG ^ 2) + 22 * (τ ^ 2 * ((τ - 1) * e2) ^ 2) +
      22 * (e * trt * (τ - 1) * (τ + 1)) ^ 2 := key
    _ ≤ τ ^ 2 * (11 / 10 * (ε₁ ^ 2 * Wfv) + 22 * (δ ^ 2 * (T2 * v))
          + 22 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v))) := by
        have q1 := mul_le_mul_of_nonneg_left h4 hτ2
        have q2 := mul_le_mul_of_nonneg_left hbb hτ2
        have q3 : τ ^ 2 * (11 / 10 * (ε₁ ^ 2 * Wfv) + 22 * (δ ^ 2 * (T2 * v))
          + 22 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v))) =
          11 / 10 * (τ ^ 2 * (ε₁ ^ 2 * Wfv)) + 22 * (τ ^ 2 * (δ ^ 2 * (T2 * v)))
          + 22 * (τ ^ 2 * ((409 / 100) * e ^ 2) * (δ ^ 2 * (nR * v))) := by ring
        rw [q3]
        linarith
    _ ≤ τ ^ 2 * (ε ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v)))) :=
        mul_le_mul_of_nonneg_left hsc hτ2
    _ = ε ^ 2 * (τ ^ 2 * ((1 - lam) * (κ * Wfv) - (1 / lam) * (δ ^ 2 * (TQ * v)))) := by ring
    _ ≤ ε ^ 2 * VS := mul_le_mul_of_nonneg_left hVS' (sq_nonneg _)

lemma FG_split (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (W : WIdx n d → ℝ)
    (x : Fin n → ℝ) :
    FG (aU ℓ H u) H W x = FG ℓ 0 W x + FG (aU 0 H u) H W x := by
  unfold FG Phi aU
  simp only [Matrix.zero_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    add_mul, Finset.sum_add_distrib]
  ring

lemma FG_lin (ℓ : Fin n → ℝ) (W : WIdx n d → ℝ) (x : Fin n → ℝ) :
    FG ℓ 0 W x = ∑ i, ℓ i * zv W (pf x) i := by
  unfold FG Phi
  simp

lemma FG_quad (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (W : WIdx n d → ℝ) (x : Fin n → ℝ) :
    FG (aU 0 H u) H W x = ∑ i, (2 * ∑ j, H i j * u j) * zv W (pf x) i +
      ∑ i, ∑ j, H i j * zv W (pf x) i * zv W (pf x) j := by
  unfold FG Phi aU
  simp

/-- **The sphere quantities in terms of the Gaussian ones**, at one point `(u, W)`. -/
lemma pw_core (hn : 1 ≤ n) (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (sD D s : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0) (hℓ : ∀ i, ℓ₀ i = sD * ℓ i)
    (hHs : ∀ i j, H₀ i j = D * H i j) (u : Fin n → ℝ) (W : WIdx n d → ℝ) (lam : ℝ)
    (hl0 : 0 < lam) :
    (sD * s) ^ 2 * ((1 - lam) * VG (aU ℓ H u) H W -
        (1 / lam) * (sD * s - 1) ^ 2 * VG (aU 0 H u) H W) ≤
      varU (uniformSphere n) (fun x => qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i))) ∧
    (∫ x, qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i)) ∂uniformSphere n) -
        (qfun f0 ℓ₀ H₀ (fun i => s * u i) + eD d / D * trH H₀) =
      (sD * s) * errG (aU ℓ H u) H W + (sD * s) * (sD * s - 1) * errG (aU 0 H u) H W +
        eD d * trH H * ((sD * s) ^ 2 - 1) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  set τ := sD * s with hτ
  set K0 := qfun f0 ℓ₀ H₀ (fun i => s * u i) with hK0
  have hS : (fun x => qfun f0 ℓ₀ H₀ (fun i => s * (u i + zv W (pf x) i))) =
      fun x => K0 + τ * FG (aU ℓ H u) H W x + τ * (τ - 1) * FG (aU 0 H u) H W x := by
    funext x
    rw [qexp f0 ℓ₀ ℓ H₀ H hH sD D s hsD hℓ hHs u (zv W (pf x)), FG_split, FG_lin, FG_quad]
    ring
  have cg := cont_FG (aU ℓ H u) H W
  have ch := cont_FG (aU 0 H u) H W
  obtain ⟨hv, hm⟩ := varU_affine_lower hn cg ch K0 τ (τ - 1) lam hl0
  rw [hS]
  refine ⟨hv, ?_⟩
  rw [hm]
  have htr : trH H₀ = D * trH H := by
    unfold trH; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hHs i i
  unfold errG
  rw [htr]
  field_simp
  ring

lemma VG_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : WIdx n d → ℝ) :
    0 ≤ VG a H W := by
  unfold VG varU; exact integral_nonneg fun _ => sq_nonneg _

lemma cont_aU (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => (aU ℓ H p.1, p.2)) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun i => ?_
  unfold aU
  exact continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_fst)))

lemma cont_Wf (α β : ℝ) (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => Wf α β (aU ℓ H p.1) H) := by
  unfold Wf nsq
  refine (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)).add continuous_const
  exact (((continuous_apply i).comp (continuous_fst.comp (cont_aU ℓ H)))).pow 2

lemma cheb_floor (hn : 1 ≤ n) {α β M1 E2 UA Uv cW κ : ℝ}
    (hM : MB n d α β M1 E2 UA Uv) (hV : VarBoundW n d α β cW) (hcW : 0 ≤ cW) (hκ0 : 0 ≤ κ)
    (hκ : κ < 1)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < Wf α β a H) :
    stdGauss (WIdx n d) {W | VG a H W < κ * Wf α β a H} ≤
      ENNReal.ofReal (cW / (n * (1 - κ) ^ 2)) := by
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n d) with hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hi1, hi2, -, hfl, -, -⟩ := hM a H hH
  have hmpos : 0 < m := lt_of_lt_of_le hpos hfl
  have hint : Integrable (fun W => (VG a H W - m) ^ 2) (stdGauss (WIdx n d)) := by
    have : (fun W : WIdx n d → ℝ => (VG a H W - m) ^ 2) = fun W => VG a H W ^ 2 - 2 * m * VG a H W + m ^ 2 := by
      funext W; ring
    rw [this]; exact (hi2.sub (hi1.const_mul _)).add (integrable_const _)
  have hvar := hV a H hH
  have hB : ∫ W, (VG a H W - m) ^ 2 ∂stdGauss (WIdx n d) ≤ cW / n * m * m := by
    refine hvar.trans ?_
    have hc : 0 ≤ cW / (n : ℝ) := div_nonneg hcW hnpos.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfl hc) hmpos.le
  have h1κ : 0 < 1 - κ := by linarith
  have ht : 0 < ((1 - κ) * m) ^ 2 := by positivity
  have hmk := markov_gt (μ := stdGauss (WIdx n d)) (fun W => sq_nonneg (VG a H W - m)) hint ht hB
  have hsub : {W : WIdx n d → ℝ | VG a H W < κ * Wf α β a H} ⊆
      {W | ((1 - κ) * m) ^ 2 < (VG a H W - m) ^ 2} := by
    intro W hW
    simp only [Set.mem_ofPred_eq] at hW ⊢
    have h2 : VG a H W < κ * m := lt_of_lt_of_le hW (mul_le_mul_of_nonneg_left hfl hκ0)
    have h3 : (1 - κ) * m < m - VG a H W := by linarith
    have h4 : 0 < (1 - κ) * m := by positivity
    nlinarith
  refine (measure_mono hsub).trans (hmk.trans (le_of_eq ?_))
  congr 1
  field_simp

lemma markov_err (hn : 1 ≤ n) {α β M1 E2 UA Uv c1 T : ℝ}
    (hM : MB n d α β M1 E2 UA Uv) (hc1 : M1 ≤ c1 * α) (hc1' : E2 ≤ c1 * β) (hT : 0 < T)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < Wf α β a H) :
    stdGauss (WIdx n d) {W | T * Wf α β a H < errG a H W ^ 2} ≤
      ENNReal.ofReal (c1 / (n * T)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨-, -, hi3, -, herr, -⟩ := hM a H hH
  have hB : ∫ W, errG a H W ^ 2 ∂stdGauss (WIdx n d) ≤ c1 * Wf α β a H / n := by
    refine herr.trans ?_
    apply div_le_div_of_nonneg_right _ hnpos.le
    unfold Wf
    have q1 := mul_le_mul_of_nonneg_right hc1 (nsq_nonneg a)
    have q2 := mul_le_mul_of_nonneg_right hc1' (frobH_nonneg H)
    have q3 : c1 * (α * nsq a + β * frobH H) = c1 * α * nsq a + c1 * β * frobH H := by ring
    rw [q3]; linarith
  have hmk := markov_gt (μ := stdGauss (WIdx n d)) (fun W => sq_nonneg (errG a H W)) hi3
    (mul_pos hT hpos) hB
  refine hmk.trans (le_of_eq ?_)
  congr 1
  field_simp

/-- `1/r` in the split coordinates. -/
noncomputable def sOf (p : (Fin n → ℝ) × (WIdx n d → ℝ)) : ℝ :=
  1 / Real.sqrt (∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2)

end BstLean.Part81.Core

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU)
open BstLean.Part59 (polyEval TopNZ g0Q BP varP)
open BstLean.Part78 (nsq frobH trH qfun aU zv Phi markov_gt meas_le_ofReal nsq_nonneg
  frobH_nonneg trH_sq_le nsq_aU0_int GaussLin tau_close)

set_option maxHeartbeats 1600000 in
/-- **The failure probability in the split coordinates, on the good radius event.** -/
theorem uw_fail (n d : ℕ) (hn : 1 ≤ n) {α β M1 E2 UA Uv cW c1 κ ε ε₁ lam TQ T2 δ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hM1 : 0 ≤ M1) (hE2 : 0 ≤ E2) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n d α β M1 E2 UA Uv) (hV : VarBoundW n d α β cW) (hR : RegIface n d)
    (hG : BstLean.Part78.GaussLin) (hcW : 0 ≤ cW)
    (hc1 : M1 ≤ c1 * α) (hc1' : E2 ≤ c1 * β) (hc10 : 0 ≤ c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hTQ : 0 < TQ) (hT2 : 0 < T2) (hδ : δ ≤ 1 / 100)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 22 * (409 / 100) * eD d ^ 2 * δ ^ 2 * (n : ℝ)
        + ε ^ 2 * δ ^ 2 * TQ / lam) / β ≤ ε ^ 2 * (1 - lam) * κ)
    (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hv : 0 < frobH H) (sD D : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j) :
    ((stdGauss (Fin n)).prod (stdGauss (WIdx n d))) {p | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD d / D * trH H₀)) ^ 2} ≤
      ENNReal.ofReal (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
        (4 * UA + Uv) / TQ + (4 * M1 + E2) / (n * T2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set v := frobH H with hvdef
  set E : Set ((Fin n → ℝ) × (WIdx n d → ℝ)) :=
    (({p | VG (aU ℓ H p.1) H p.2 < κ * Wf α β (aU ℓ H p.1) H} ∪
      {p | ε₁ ^ 2 * Wf α β (aU ℓ H p.1) H < errG (aU ℓ H p.1) H p.2 ^ 2}) ∪
      {p | TQ * v < VG (aU 0 H p.1) H p.2}) ∪
      {p | T2 * v < errG (aU 0 H p.1) H p.2 ^ 2} with hE
  have cV1 : Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => VG (aU ℓ H p.1) H p.2) :=
    (hR H).1.comp (Core.cont_aU ℓ H)
  have cE1 : Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => errG (aU ℓ H p.1) H p.2) :=
    (hR H).2.comp (Core.cont_aU ℓ H)
  have cV2 : Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => VG (aU 0 H p.1) H p.2) :=
    (hR H).1.comp (Core.cont_aU 0 H)
  have cE2 : Continuous (fun p : (Fin n → ℝ) × (WIdx n d → ℝ) => errG (aU 0 H p.1) H p.2) :=
    (hR H).2.comp (Core.cont_aU 0 H)
  have cWf := Core.cont_Wf (n := n) (d := d) α β ℓ H
  have hEm : MeasurableSet E := by
    refine (((measurableSet_lt cV1.measurable (continuous_const.mul cWf).measurable).union
      (measurableSet_lt (continuous_const.mul cWf).measurable (cE1.pow 2).measurable)).union
      (measurableSet_lt measurable_const cV2.measurable)).union
      (measurableSet_lt measurable_const (cE2.pow 2).measurable)
  have hsub : {p : (Fin n → ℝ) × (WIdx n d → ℝ) | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) ∂uniformSphere n) -
          (qfun f0 ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD d / D * trH H₀)) ^ 2} ⊆ E := by
    intro p hp
    obtain ⟨hτ, hfail⟩ := hp
    by_contra hnot
    simp only [hE, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hnot
    obtain ⟨hVS, heS⟩ := Core.pw_core hn f0 ℓ₀ ℓ H₀ H hH sD D (Core.sOf p) hsD hD hℓ hHs
      p.1 p.2 lam hlam0
    have h6 : β * v ≤ Wf α β (aU ℓ H p.1) H := by
      unfold Wf
      have := mul_nonneg hα (nsq_nonneg (aU ℓ H p.1))
      linarith
    have := Core.det_core (ε := ε) (κ := κ) (ε₁ := ε₁) (TQ := TQ) (T2 := T2) hτ hδ hβ hlam0 hlam1
      (Core.VG_nonneg _ _ _) hv.le hTQ.le hT2.le hnpos.le hVS heS g1 g3 g4 g2 (trH_sq_le H) h6 hnum
    exact absurd hfail (not_lt.mpr this)
  refine (measure_mono hsub).trans ?_
  have : IsProbabilityMeasure (stdGauss (Fin n)) := inferInstance
  rw [Measure.prod_apply hEm]
  set g : (Fin n → ℝ) → ℝ := fun u =>
    c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) +
      ((M1 * nsq (aU 0 H u) + E2 * v) / n) / (T2 * v) with hg
  have hcond : ∀ u : Fin n → ℝ,
      stdGauss (WIdx n d) (Prod.mk u ⁻¹' E) ≤ ENNReal.ofReal (g u) := by
    intro u
    have hWpos : 0 < Wf α β (aU ℓ H u) H := by
      unfold Wf
      have := mul_nonneg hα (nsq_nonneg (aU ℓ H u))
      have := mul_pos hβ hv
      linarith
    have b1 := Core.cheb_floor hn hM hV hcW hκ0.le hκ (aU ℓ H u) H hH hWpos
    have b2 := Core.markov_err hn (T := ε₁ ^ 2) hM hc1 hc1' (by positivity) (aU ℓ H u) H hH hWpos
    obtain ⟨hi1, -, hi3, -, herr, hup⟩ := hM (aU 0 H u) H hH
    have b3 := markov_gt (μ := stdGauss (WIdx n d)) (fun W => Core.VG_nonneg (aU 0 H u) H W) hi1
      (mul_pos hTQ hv) hup
    have b4 := markov_gt (μ := stdGauss (WIdx n d)) (fun W => sq_nonneg (errG (aU 0 H u) H W)) hi3
      (mul_pos hT2 hv) herr
    have hpre : Prod.mk u ⁻¹' E =
        (({W | VG (aU ℓ H u) H W < κ * Wf α β (aU ℓ H u) H} ∪
          {W | ε₁ ^ 2 * Wf α β (aU ℓ H u) H < errG (aU ℓ H u) H W ^ 2}) ∪
          {W | TQ * v < VG (aU 0 H u) H W}) ∪
          {W | T2 * v < errG (aU 0 H u) H W ^ 2} := rfl
    rw [hpre]
    have ha := nsq_nonneg (aU 0 H u)
    have p1 : 0 ≤ c1 / (n * ε₁ ^ 2) := by positivity
    have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
    have p3 : 0 ≤ (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) := by positivity
    have p4 : 0 ≤ ((M1 * nsq (aU 0 H u) + E2 * v) / n) / (T2 * v) := by positivity
    rw [hg]
    simp only
    rw [ENNReal.ofReal_add (by positivity) p4, ENNReal.ofReal_add (by positivity) p3,
      ENNReal.ofReal_add p1 p2]
    refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans ?_) b3)) b4)
    rw [add_comm]
    exact add_le_add b2 b1
  obtain ⟨hni, hnv⟩ := nsq_aU0_int hG H
  have hgi : Integrable g (stdGauss (Fin n)) := by
    rw [hg]
    exact ((integrable_const _).add
      (((hni.const_mul _).add (integrable_const _)).div_const _)).add
      ((((hni.const_mul _).add (integrable_const _)).div_const _).div_const _)
  have hg0 : ∀ u, 0 ≤ g u := by
    intro u
    have ha := nsq_nonneg (aU 0 H u)
    rw [hg]; simp only
    have p1 : 0 ≤ c1 / (n * ε₁ ^ 2) := by positivity
    have p2 : 0 ≤ cW / (n * (1 - κ) ^ 2) := by positivity
    have p3 : 0 ≤ (UA * nsq (aU 0 H u) + Uv * v) / (TQ * v) := by positivity
    have p4 : 0 ≤ ((M1 * nsq (aU 0 H u) + E2 * v) / n) / (T2 * v) := by positivity
    linarith
  refine (lintegral_mono hcond).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hgeq : ∀ u, g u = (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (Uv * v) / (TQ * v) + (E2 * v / n) / (T2 * v)) +
      (UA / (TQ * v) + M1 / n / (T2 * v)) * nsq (aU 0 H u) := by
    intro u; rw [hg]; ring
  have hint : ∫ u, g u ∂stdGauss (Fin n) =
      (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
      (Uv * v) / (TQ * v) + (E2 * v / n) / (T2 * v)) +
      (UA / (TQ * v) + M1 / n / (T2 * v)) * (4 * v) := by
    simp only [hgeq]
    rw [integral_add (integrable_const _) (hni.const_mul _), integral_const_mul, hnv]
    simp
    exact Or.inl hvdef.symm
  rw [hint]
  have hvne : v ≠ 0 := hv.ne'
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- **Failure probability of `g₀` on the coefficient sphere**, parametric form, map degree `d`. -/
theorem fail81_core (n d : ℕ) (hn : 1 ≤ n) {α β M1 E2 UA Uv cW c1 κ ε ε₁ lam TQ T2 δ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hM1 : 0 ≤ M1) (hE2 : 0 ≤ E2) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n d α β M1 E2 UA Uv) (hV : VarBoundW n d α β cW) (hcW : 0 ≤ cW)
    (hc1 : M1 ≤ c1 * α) (hc1' : E2 ≤ c1 * β) (hc10 : 0 ≤ c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hTQ : 0 < TQ) (hT2 : 0 < T2) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 100)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 * δ ^ 2 * T2 + 22 * (409 / 100) * eD d ^ 2 * δ ^ 2 * (n : ℝ)
        + ε ^ 2 * δ ^ 2 * TQ / lam) / β ≤ ε ^ 2 * (1 - lam) * κ)
    (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n d 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (2 / DD n d / δ ^ 2 + (c1 / (n * ε₁ ^ 2) + cW / (n * (1 - κ) ^ 2) +
        (4 * UA + Uv) / TQ + (4 * M1 + E2) / (n * T2))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨ℓ₀, H₀, hH₀, hpoly, htop, hg0⟩ := coefBridge n d c
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  set D := DD n d with hDdef
  set sD := Real.sqrt D with hsDdef
  have hsD0 : 0 < sD := Real.sqrt_pos.mpr hD
  have hsD : sD ^ 2 = D := Real.sq_sqrt hD.le
  set ℓ : Fin n → ℝ := fun i => ℓ₀ i / sD with hℓdef
  set H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => H₀ i j / D with hHdef
  have hH : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [hHdef, Matrix.of_apply]
    rw [hH₀.apply j i]
  have hℓ : ∀ i, ℓ₀ i = sD * ℓ i := fun i => by simp only [hℓdef]; field_simp
  have hHs : ∀ i j, H₀ i j = D * H i j := fun i j => by
    simp only [hHdef, Matrix.of_apply]; field_simp
  have hv : 0 < frobH H := by
    have h0 := htop hc
    have : frobH H = frobH H₀ / D ^ 2 := by
      unfold frobH
      simp only [hHdef, Matrix.of_apply, div_pow]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
    rw [this]; positivity
  set UW : Set ((Fin n → ℝ) × (WIdx n d → ℝ)) := {p | |sD * Core.sOf p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) <
        ((∫ x, qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))
            ∂uniformSphere n) -
          (qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD d / D * trH H₀)) ^ 2}
    with hUW
  have hsub : {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n d 2 c (unitOfD Z)) ^ 2} ⊆
      {Z | δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2} ∪ (Br.combEquiv n d).symm ⁻¹' UW := by
    intro Z hZ
    obtain ⟨hZ0, hfail⟩ := hZ
    by_cases hr : δ ^ 2 < ((∑ α, Z α ^ 2) / D - 1) ^ 2
    · exact Or.inl hr
    right
    simp only [Set.mem_preimage]
    set p := (Br.combEquiv n d).symm Z with hp
    have hZp : Br.combEquiv n d (p.1, p.2) = Z := by
      show Br.combEquiv n d p = Z
      rw [hp]; exact (Br.combEquiv n d).apply_symm_apply Z
    obtain ⟨f1, f2, f3⟩ := Br.comb_facts (n := n) (d := d) p.1 p.2
    rw [hZp] at f1 f2 f3
    have hq : 0 < ∑ α, Z α ^ 2 := by
      by_contra hc0
      apply hZ0
      have h0 : ∑ α, Z α ^ 2 = 0 :=
        le_antisymm (not_lt.mp hc0) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      funext α
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 α
        (Finset.mem_univ α)
      simpa using this
    have hs : Core.sOf p = 1 / Real.sqrt (∑ α, Z α ^ 2) := by unfold Core.sOf; rw [f3]
    have hunit : unitOfD Z = Core.sOf p • Z := by unfold unitOfD; rw [hs]
    have hτ : |sD * Core.sOf p - 1| ≤ δ := by
      rw [hs]
      exact tau_close hq hD hδ0.le (by linarith) (not_lt.mp hr)
    have hmap : ∀ x : Fin n → ℝ, polyEval 2 c (mapMD (Core.sOf p • Z) x) =
        qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i)) := by
      intro x
      rw [hpoly]
      congr 1
      funext i
      rw [BstLean.Part52.mapMD_smul, f2]
    have hcol : colM (Core.sOf p • Z) default = fun i => Core.sOf p * p.1 i := by
      funext i
      have := congrFun f1 i
      simp only [colM, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this]
    refine ⟨hτ, ?_⟩
    have e1 : varP (uniformSphere n) 2 c (unitOfD Z) = varU (uniformSphere n)
        (fun x => qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))) := by
      unfold varP; rw [hunit]; simp only [hmap]
    have e2 : BP (uniformSphere n) 2 c (unitOfD Z) =
        ∫ x, qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * (p.1 i + zv p.2 (pf x) i))
          ∂uniformSphere n := by
      unfold BP; rw [hunit]; simp only [hmap]
    have e3 : g0Q n d 2 c (unitOfD Z) =
        qfun (c default) ℓ₀ H₀ (fun i => Core.sOf p * p.1 i) + eD d / D * trH H₀ := by
      rw [hunit, hg0, hcol]
    rw [e1, e2, e3] at hfail
    exact hfail
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hrad := radTail n d hn δ hδ0
  have hpre : stdGauss (CoefIdxD n d) ((Br.combEquiv n d).symm ⁻¹' UW) =
      ((stdGauss (Fin n)).prod (stdGauss (WIdx n d))) UW := by
    rw [← (Br.combEquiv_preserving (n := n) (d := d)).measure_preimage_equiv,
      ← Set.preimage_comp]
    simp
  have huw := uw_fail n d hn (cW := cW) (c1 := c1)
    (κ := κ) (ε := ε) (ε₁ := ε₁) (lam := lam) (TQ := TQ) (T2 := T2) (δ := δ)
    hα hβ hM1 hE2 hUA hUv hM hV (regIface n d hn) BstLean.Part78.gaussLin hcW hc1 hc1' hc10
    hκ0 hκ hε₁ hlam0 hlam1 hTQ hT2 hδ hnum
    (c default) ℓ₀ ℓ H₀ H hH hv sD D hsD hD.ne' hℓ hHs
  rw [hpre]
  refine (add_le_add hrad huw).trans ?_
  have h1κ : 0 < 1 - κ := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end BstLean.Part81

#print axioms BstLean.Part81.Core.det_core
#print axioms BstLean.Part81.uw_fail
#print axioms BstLean.Part81.fail81_core
