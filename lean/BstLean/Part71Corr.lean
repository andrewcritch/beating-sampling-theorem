import BstLean.Part59Floor_Correction

/-!
# Part 71: the kernel correction under an abstract trace-moment bound

A copy of the second half of `Part59Floor_Correction.lean`, with the hypothesis `UpLaw n μ Λ`
replaced by `SphLaw n μ` and the trace-moment bound `DevW n d μ w`:
`E_μ δ°^{2i} ≤ w(i)·d^{2i}/n^{2i}` for `i ≥ 1`. The `UpLaw` weight is `w i = max Λ 1·(8i−1)!!`;
the chi-square weight (`Part71Transfer.chi_dev`) is `w i = √(1+K)·√((16i−1)!!)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open BstLean.Part53
open BstLean.Part59.FloorCorrection59x

open MeasureTheory
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq Tens frob)
open FloorHeat FloorEnergy

variable {n d : ℕ}

/-- The trace-moment bound with weight `w`. -/
def DevW (n d : ℕ) (μ : Measure (Fin n → ℝ)) (w : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → (∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤ w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)

/-- `corr(d,c,i) = c!·heatFactor(c,i)²·(d+1)^c·d^{2i}·w(i)`. -/
noncomputable def corrW (d c i : ℕ) (w : ℕ → ℝ) : ℝ :=
  (c.factorial : ℝ) * heatFactor c i ^ 2 * ((d : ℝ) + 1) ^ c * (d : ℝ) ^ (2 * i) * w i

lemma corrW_nonneg (d c i : ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) : 0 ≤ corrW d c i w := by
  unfold corrW; have := hw i; positivity

lemma weighted_dev_W (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hsph : SphLaw n μ) {w : ℕ → ℝ} (hdev : DevW n d μ w)
    (c i : ℕ) (hi : 1 ≤ i) :
    (∫ x, phiSq d x ^ c * (phiSq d x - c0 d) ^ (2 * i) ∂μ) ≤
      ((d : ℝ) + 1) ^ c * (w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i)) := by
  have hcont : Continuous (fun x : Fin n → ℝ => phiSq d x) := phiSq_continuous
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
  exact hb.trans (mul_le_mul_of_nonneg_left (hdev i hi) (by positivity))

lemma scaled_heat_W (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hsph : SphLaw n μ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdev : DevW n d μ w) (c i : ℕ) (hi : 1 ≤ i) :
    (c.factorial : ℝ) * sg n d ^ (2 * c) * (n : ℝ) ^ i *
      (∫ x, phiSq d x ^ c *
        heatWeight c i ((phiSq d x - c0 d) / BstLean.Part36.DD n d) ^ 2 ∂μ) ≤
      corrW d c i w / (n : ℝ) / BstLean.Part36.DD n d ^ (c + 2 * i) := by
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
  have hm := weighted_dev_W hn hd hsph hdev c i hi
  have hh := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ (c.factorial : ℝ) * (1 / D ^ c) * (n : ℝ) ^ i *
      (heatFactor c i ^ 2 / D ^ (2 * i)) by positivity)
  have heq : (c.factorial : ℝ) * (1 / D ^ c) * (n : ℝ) ^ i *
      (heatFactor c i ^ 2 / D ^ (2 * i)) *
        (((d : ℝ) + 1) ^ c * (w i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i))) =
      (corrW d c i w / D ^ (c + 2 * i)) *
        ((n : ℝ) ^ i / (n : ℝ) ^ (2 * i)) := by
    unfold corrW
    rw [pow_add]
    ring
  calc
    _ ≤ _ := by simpa only [mul_assoc] using hh
    _ = _ := heq
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (dimension_moment_decay hn i hi)
        (show 0 ≤ corrW d c i w / D ^ (c + 2 * i) from
          div_nonneg (corrW_nonneg _ _ _ _ hw) (pow_nonneg hD.le _))
      convert hb using 1; ring

lemma kernel_correction_W (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hsph : SphLaw n μ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdev : DevW n d μ w) (hTr : LemmaTr53)
    (k c : ℕ) (hc : c ≤ k) (A : Tens n) :
    (∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / BstLean.Part36.DD n d) A x ∂μ) ≤
      (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          corrW d c i w / (n : ℝ) *
            (frob (heatA k (c0 d / BstLean.Part36.DD n d) A (c + 2 * i)) /
              BstLean.Part36.DD n d ^ (c + 2 * i)) := by
  classical
  let D := BstLean.Part36.DD n d
  let B := heatA k (c0 d / D) A
  let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
  let P := (c.factorial : ℝ) * sg n d ^ (2 * c)
  let Q (i : ℕ) (x : Fin n → ℝ) :=
    phiSq d x ^ c * heatWeight c i ((phiSq d x - c0 d) / D) ^ 2
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
      have hm := scaled_heat_W hn hd hsph hw hdev c i hi0
      have hf : 0 ≤ frob (B (c + 2 * i)) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hh := mul_le_mul_of_nonneg_right hm hf
      convert hh using 1 <;> dsimp [Q, P, B, D] <;> ring

/-- The total correction constant over the orders `c ∈ s`:
`(k+1)·Σ_{c ∈ s} Σ_{i ≥ 1, c+2i ≤ k} corr(d,c,i)`. -/
noncomputable def totW (d k : ℕ) (s : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  (k + 1 : ℝ) * ∑ c ∈ s,
    ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0, corrW d c i w

lemma totW_nonneg (d k : ℕ) (s : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ totW d k s w := by
  unfold totW
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i _ => corrW_nonneg d c i w hw))

/-- The total kernel correction over the orders `c ∈ s ⊆ [0, k]`. -/
lemma total_correction_W (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hsph : SphLaw n μ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdev : DevW n d μ w) (hTr : LemmaTr53)
    (k : ℕ) (s : Finset ℕ) (hs : ∀ c ∈ s, c ≤ k) (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ s,
      ∫ x, kernelErrorSq (d := d) k c (sg n d) (c0 d / BstLean.Part36.DD n d)
        (TF k f0 T) x ∂μ) ≤
      totW d k s w / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ ∑ c ∈ s, (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          corrW d c i w / (n : ℝ) *
            (frob (Tcirc n d k f0 T (c + 2 * i)) /
              BstLean.Part36.DD n d ^ (c + 2 * i)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact kernel_correction_W hn hd hsph hw hdev hTr k c (hs c hc) (TF k f0 T)
    _ ≤ ∑ c ∈ s, (k + 1 : ℝ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          corrW d c i w / (n : ℝ) * Ncirc n d k f0 T := by
      apply Finset.sum_le_sum
      intro c hc
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      have hj : c + 2 * i ∈ Finset.Icc 1 k := by
        have hi0 := (Finset.mem_erase.mp hi).1
        have hi' := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
        exact Finset.mem_Icc.mpr ⟨by omega, hi'⟩
      exact mul_le_mul_of_nonneg_left (Ncirc_term_le hn k (c + 2 * i) f0 T hj)
        (div_nonneg (corrW_nonneg d c i w hw) hn0.le)
    _ = _ := by
      unfold totW
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
      ring

end BstLean.Part71
