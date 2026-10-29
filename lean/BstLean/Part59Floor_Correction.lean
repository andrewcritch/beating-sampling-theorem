import BstLean.Part53Floor_Heat
import BstLean.Part53Floor_Energy
import BstLean.Part59Floor_Moments
import BstLean.Part43Floor

namespace BstLean.Part59.FloorCorrection59x

open BstLean.Part53

open MeasureTheory
open BstLean.Part41 (Mono phiM phiSq Tens frob)
open FloorHeat FloorEnergy

variable {n d : ℕ}

lemma feature_tensor_sq (c : ℕ) (x : Fin n → ℝ) :
    (∑ p : Fin c → Mono n d, (∏ t, phiM x (p t)) ^ 2) = phiSq d x ^ c := by
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin c) (p : Mono n d) => phiM x p ^ 2)]
  simp [phiSq]

noncomputable def baseKernel (s : ℝ) (B : Tens n) (i : EnergyIndex n d)
    (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (i.1.factorial : ℝ) * s ^ i.1 * B i.1 i.2.1 * ∏ t, phiM x (i.2.2 t)

lemma kernel_correction_sq (k c : ℕ) (s v : ℝ) (A : Tens n) (x : Fin n → ℝ) :
    (∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
      (energyKernel k s A ⟨c, a, p⟩ x - baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2) =
      (c.factorial : ℝ) * s ^ (2 * c) * phiSq d x ^ c *
        frob (fun a => heatA k (s ^ 2 * phiSq d x) A c a - heatA k v A c a) := by
  classical
  have hnsq : nsq (fun p : Mono n d => phiM x p) = phiSq d x := rfl
  have hterm (a : Fin c → Fin n) (p : Fin c → Mono n d) :
      (energyKernel k s A ⟨c, a, p⟩ x - baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2 =
      (c.factorial : ℝ) * s ^ (2 * c) *
        (heatA k (s ^ 2 * phiSq d x) A c a - heatA k v A c a) ^ 2 *
          (∏ t, phiM x (p t)) ^ 2 := by
    unfold energyKernel baseKernel
    dsimp only
    rw [hnsq]
    have hs : s ^ (2 * c) = (s ^ c) ^ 2 := by rw [mul_comm 2 c, pow_mul]
    rw [hs]
    have hf := Real.sq_sqrt (Nat.cast_nonneg c.factorial : (0 : ℝ) ≤ c.factorial)
    ring_nf
    rw [hf]
    ring
  simp_rw [hterm, ← Finset.mul_sum, feature_tensor_sq]
  unfold frob
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma shifted_correction_frob (k c : ℕ) (v w : ℝ) (A : Tens n) (hc : c ≤ k)
    (hTr : LemmaTr53) :
    frob (fun z => heatA k v A c z - heatA k w A c z) ≤
      (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          heatWeight c i (v - w) ^ 2 * (n : ℝ) ^ i *
            frob (heatA k w A (c + 2 * i)) := by
  have hh := heatA_correction_frob k c (v - w) (heatA k w A) hc hTr
  simpa only [heatA_shift] using hh

lemma weighted_feature_deviation_moment (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : UpLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (c i : ℕ) (hi : 1 ≤ i) :
    (∫ x, phiSq d x ^ c * (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      ((d : ℝ) + 1) ^ c * max Λ 1 * (d : ℝ) ^ (2 * i) *
        (((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i)) := by
  have hsph := FloorMoments59x.dens_sph hμ
  have hcont : Continuous (fun x : Fin n → ℝ => phiSq d x) :=
    continuous_finsetSum _ (fun p _ => (continuous_multiset_prod p.2.1
      (fun j _ => continuous_apply j)).pow 2)
  have hδ : Continuous (fun x : Fin n → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (hcont.sub continuous_const).pow (2 * i)
  have hb : (∫ x, phiSq d x ^ c * (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      ((d : ℝ) + 1) ^ c * (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      (sphere_cont_integrable hsph ((hcont.pow c).mul hδ))
      (sphere_cont_integrable hsph (continuous_const.mul hδ))
    filter_upwards [hsph.sphere] with x hx
    have hphi := BstLean.Part43.phiSq_bounds hd x hx
    have hδ0 : 0 ≤ (phiSq d x - c0 d) ^ (2 * i) := by
      rw [mul_comm 2 i, pow_mul]
      exact sq_nonneg _
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_trans (by norm_num) hphi.1) hphi.2 c) hδ0
  have hm := FloorMoments59x.feature_deviation_moment hn hμ hU hS i hi
  calc
    _ ≤ _ := hb
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hm
        (pow_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1) c)
      simpa only [mul_assoc] using hh

lemma sg_pow_even (hn : 1 ≤ n) (c : ℕ) :
    sg n d ^ (2 * c) = 1 / BstLean.Part36.DD n d ^ c := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hs : sg n d ^ 2 = 1 / BstLean.Part36.DD n d := by
    rw [sg, div_pow, one_pow, Real.sq_sqrt hD.le]
  rw [pow_mul, hs, div_pow, one_pow]

noncomputable def heatFactor (c i : ℕ) : ℝ :=
  ((c + 2 * i).factorial : ℝ) /
    ((c.factorial : ℝ) * (i.factorial : ℝ) * 2 ^ i)

lemma heatWeight_sq (c i : ℕ) (v : ℝ) :
    heatWeight c i v ^ 2 = heatFactor c i ^ 2 * v ^ (2 * i) := by
  unfold heatWeight heatFactor
  rw [mul_comm 2 i, pow_mul]
  rw [div_pow]
  have hc : (c.factorial : ℝ) ≠ 0 := by positivity
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ i ≠ 0 := by positivity
  rw [div_pow]
  field_simp

lemma dimension_moment_decay (hn : 1 ≤ n) (i : ℕ) (hi : 1 ≤ i) :
    (n : ℝ) ^ i / (n : ℝ) ^ (2 * i) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ i := by
    simpa using (pow_le_pow_right₀ hn1 hi)
  rw [two_mul, pow_add, div_mul_cancel_left₀ (pow_ne_zero _ hn0.ne')]
  simpa only [one_div] using one_div_le_one_div_of_le hn0 hp

noncomputable def correctionConstant (d c i : ℕ) (Λ : ℝ) : ℝ :=
  (c.factorial : ℝ) * heatFactor c i ^ 2 * ((d : ℝ) + 1) ^ c *
    max Λ 1 * (d : ℝ) ^ (2 * i) * ((8 * i - 1).doubleFactorial : ℝ)

lemma correctionConstant_nonneg (d c i : ℕ) (Λ : ℝ) :
    0 ≤ correctionConstant d c i Λ := by unfold correctionConstant; positivity

lemma scaled_heat_moment (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : UpLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (c i : ℕ) (hi : 1 ≤ i) :
    (c.factorial : ℝ) * sg n d ^ (2 * c) * (n : ℝ) ^ i *
      (∫ x, phiSq d x ^ c *
        heatWeight c i ((phiSq d x - c0 d) / BstLean.Part36.DD n d) ^ 2 ∂μ) ≤
      correctionConstant d c i Λ / (n : ℝ) / BstLean.Part36.DD n d ^ (c + 2 * i) := by
  let D := BstLean.Part36.DD n d
  have hD : 0 < D := BstLean.Part36.DD_pos hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he (x : Fin n → ℝ) :
      phiSq d x ^ c * heatWeight c i ((phiSq d x - c0 d) / D) ^ 2 =
        (heatFactor c i ^ 2 / D ^ (2 * i)) *
          (phiSq d x ^ c * (phiSq d x - c0 d) ^ (2 * i)) := by
    rw [heatWeight_sq, div_pow]
    ring
  rw [show (fun x : Fin n → ℝ => phiSq d x ^ c *
      heatWeight c i ((phiSq d x - c0 d) / BstLean.Part36.DD n d) ^ 2) =
      (fun x => (heatFactor c i ^ 2 / D ^ (2 * i)) *
        (phiSq d x ^ c * (phiSq d x - c0 d) ^ (2 * i))) from funext he,
    integral_const_mul, sg_pow_even hn]
  have hm := weighted_feature_deviation_moment hn hd hμ hU hS c i hi
  have hh := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (c.factorial : ℝ) * (1 / D ^ c) * (n : ℝ) ^ i *
      (heatFactor c i ^ 2 / D ^ (2 * i)) by positivity)
  have heq : (c.factorial : ℝ) * (1 / D ^ c) * (n : ℝ) ^ i *
      (heatFactor c i ^ 2 / D ^ (2 * i)) *
        (((d : ℝ) + 1) ^ c * max Λ 1 * (d : ℝ) ^ (2 * i) *
          (((8 * i - 1).doubleFactorial : ℝ) / (n : ℝ) ^ (2 * i))) =
      (correctionConstant d c i Λ / D ^ (c + 2 * i)) *
        ((n : ℝ) ^ i / (n : ℝ) ^ (2 * i)) := by
    unfold correctionConstant
    rw [pow_add]
    ring
  calc
    _ ≤ _ := by simpa only [mul_assoc] using hh
    _ = _ := heq
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (dimension_moment_decay hn i hi)
        (show 0 ≤ correctionConstant d c i Λ / D ^ (c + 2 * i) from
          div_nonneg (correctionConstant_nonneg _ _ _ _) (pow_nonneg hD.le _))
      convert hb using 1; ring

lemma phiSq_continuous : Continuous (fun x : Fin n → ℝ => phiSq d x) :=
  continuous_finsetSum _ (fun p _ => (continuous_multiset_prod p.2.1
    (fun j _ => continuous_apply j)).pow 2)

lemma baseKernel_continuous (s : ℝ) (B : Tens n) (i : EnergyIndex n d) :
    Continuous (baseKernel s B i) := by
  unfold baseKernel
  exact continuous_const.mul (continuous_finsetProd _ (fun t _ =>
    continuous_multiset_prod (i.2.2 t).2.1 (fun j _ => continuous_apply j)))

noncomputable def kernelErrorSq (k c : ℕ) (s v : ℝ) (A : Tens n) (x : Fin n → ℝ) : ℝ :=
  ∑ a : Fin c → Fin n, ∑ p : Fin c → Mono n d,
    (energyKernel k s A ⟨c, a, p⟩ x - baseKernel s (heatA k v A) ⟨c, a, p⟩ x) ^ 2

lemma kernelErrorSq_continuous (k c : ℕ) (s v : ℝ) (A : Tens n) :
    Continuous (kernelErrorSq (d := d) k c s v A) := by
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro p hp
  exact ((energyKernel_continuous k s A ⟨c, a, p⟩).sub
    (baseKernel_continuous s (heatA k v A) ⟨c, a, p⟩)).pow 2

lemma kernel_correction_integral (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : UpLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (hTr : LemmaTr53)
    (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    (∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / BstLean.Part36.DD n d) A x ∂μ) ≤
      (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          correctionConstant d c i Λ / (n : ℝ) *
            (frob (heatA k (c0 d / BstLean.Part36.DD n d) A (c + 2 * i)) /
              BstLean.Part36.DD n d ^ (c + 2 * i)) := by
  classical
  let D := BstLean.Part36.DD n d
  let B := heatA k (c0 d / D) A
  let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
  let P := (c.factorial : ℝ) * sg n d ^ (2 * c)
  let Q (i : ℕ) (x : Fin n → ℝ) :=
    phiSq d x ^ c * heatWeight c i ((phiSq d x - c0 d) / D) ^ 2
  have hsph := FloorMoments59x.dens_sph hμ
  have hD : 0 < D := BstLean.Part36.DD_pos hn
  have hP : 0 ≤ P := by
    dsimp [P]
    rw [mul_comm 2 c, pow_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hQc (i : ℕ) : Continuous (Q i) := by
    have hf : Continuous (fun x : Fin n → ℝ => phiSq d x) := phiSq_continuous
    dsimp [Q, heatWeight]
    fun_prop
  have hQi (i : ℕ) : Integrable (Q i) μ := sphere_cont_integrable hsph (hQc i)
  have hright (i : ℕ) : Integrable
      (fun x => (P * (n : ℝ) ^ i * frob (B (c + 2 * i))) * Q i x) μ :=
    (hQi i).const_mul _
  have hp (x : Fin n → ℝ) :
      kernelErrorSq (d := d) k c (sg n d) (c0 d / D) A x ≤
        (k + 1 : ℝ) * ∑ i ∈ S,
          (P * (n : ℝ) ^ i * frob (B (c + 2 * i))) * Q i x := by
    unfold kernelErrorSq
    rw [kernel_correction_sq]
    have hφ : 0 ≤ phiSq d x := Finset.sum_nonneg (fun p _ => sq_nonneg _)
    have hscale : sg n d ^ 2 * phiSq d x - c0 d / D =
        (phiSq d x - c0 d) / D := by
      rw [sg_pow_even hn 1]
      simp only [pow_one]
      ring
    have hb := mul_le_mul_of_nonneg_left
      (shifted_correction_frob k c (sg n d ^ 2 * phiSq d x) (c0 d / D) A hc hTr)
      (show 0 ≤ P * phiSq d x ^ c from mul_nonneg hP (pow_nonneg hφ _))
    rw [hscale] at hb
    convert hb using 1
    simp only [S, B, Q, P]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ ≤ ∫ x, (k + 1 : ℝ) * ∑ i ∈ S,
        (P * (n : ℝ) ^ i * frob (B (c + 2 * i))) * Q i x ∂μ := by
      apply integral_mono
        (sphere_cont_integrable hsph (kernelErrorSq_continuous k c _ _ A))
        ((integrable_finsetSum S (fun i _ => hright i)).const_mul _)
      exact hp
    _ = (k + 1 : ℝ) * ∑ i ∈ S,
        (P * (n : ℝ) ^ i * frob (B (c + 2 * i))) * (∫ x, Q i x ∂μ) := by
      rw [integral_const_mul, integral_finsetSum S (fun i _ => hright i)]
      simp_rw [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hi0 : 1 ≤ i := by have := (Finset.mem_erase.mp hi).1; omega
      have hm := scaled_heat_moment hn hd hμ hU hS c i hi0
      have hf : 0 ≤ frob (B (c + 2 * i)) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hh := mul_le_mul_of_nonneg_right hm hf
      convert hh using 1 <;> dsimp [Q, P, B, D] <;> ring

noncomputable def totalCorrectionConstant (d k : ℕ) (Λ : ℝ) : ℝ :=
  (k + 1 : ℝ) * ∑ c ∈ Finset.Icc 1 k,
    ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
      correctionConstant d c i Λ

lemma totalCorrectionConstant_nonneg (d k : ℕ) (Λ : ℝ) :
    0 ≤ totalCorrectionConstant d k Λ := by
  unfold totalCorrectionConstant
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
    (fun i _ => correctionConstant_nonneg d c i Λ))

lemma Ncirc_nonneg (hn : 1 ≤ n) (k : ℕ) (f0 : ℝ) (T : Tens n) :
    0 ≤ Ncirc n d k f0 T := by
  unfold Ncirc
  apply Finset.sum_nonneg
  intro c hc
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · exact pow_nonneg (BstLean.Part36.DD_pos (d := d) hn).le _

lemma Ncirc_term_le (hn : 1 ≤ n) (k j : ℕ) (f0 : ℝ) (T : Tens n)
    (hj : j ∈ Finset.Icc 1 k) :
    frob (Tcirc n d k f0 T j) / BstLean.Part36.DD n d ^ j ≤ Ncirc n d k f0 T := by
  unfold Ncirc
  apply Finset.single_le_sum _ hj
  intro c hc
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · exact pow_nonneg (BstLean.Part36.DD_pos (d := d) hn).le _

lemma total_kernel_correction (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (hμ : UpLaw n μ Λ)
    (hU : LemmaU53 d) (hS : LemmaS53) (hTr : LemmaTr53)
    (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ Finset.Icc 1 k,
      ∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / BstLean.Part36.DD n d)
        (TF k f0 T) x ∂μ) ≤
      totalCorrectionConstant d k Λ / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 k, (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          correctionConstant d c i Λ / (n : ℝ) *
            (frob (Tcirc n d k f0 T (c + 2 * i)) /
              BstLean.Part36.DD n d ^ (c + 2 * i)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact kernel_correction_integral hn hd hμ hU hS hTr k c
        (Finset.mem_Icc.mp hc).2 (TF k f0 T)
    _ ≤ ∑ c ∈ Finset.Icc 1 k, (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          correctionConstant d c i Λ / (n : ℝ) * Ncirc n d k f0 T := by
      apply Finset.sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hj : c + 2 * i ∈ Finset.Icc 1 k := by
        have hci := (Finset.mem_Icc.mp hc).1
        have hi' := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
        exact Finset.mem_Icc.mpr ⟨by omega, hi'⟩
      exact mul_le_mul_of_nonneg_left (Ncirc_term_le hn k (c + 2 * i) f0 T hj)
        (div_nonneg (correctionConstant_nonneg d c i Λ) hn0.le)
    _ = _ := by
      unfold totalCorrectionConstant
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
      ring

end BstLean.Part59.FloorCorrection59x
