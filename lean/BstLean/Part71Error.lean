import BstLean.Part71Iface
import BstLean.Part71Transfer
import BstLean.Part71Corr

/-!
# Part 71: Prop E under a chi-square bound (no mixing step)

A copy of the end of `Part59Error_Bound.lean` (`error53_feature_tensor` … `normalized_bound59x`), with
the density hypothesis replaced by `SphLaw n μ`, the trace-moment bound `DevW n d μ w` and the
feature-operator bound `E_μ (a·φ)² ≤ W_F·((d+1)/n)‖a‖²`. The mixing step of Part 63 (`mix_dens59x`,
factor `10`) is not needed. `propE71` instantiates it for `ChiLaw n μ K` with
`w(i) = √(1+|K|)·√((16i−1)!!)` (`chi_dev`) and `W_F = √(1+|K|)·√C` (`chi_feature`, Lemma SH with
constant `C`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part71

open MeasureTheory BstLean.Part53
open BstLean.Part59
open BstLean.Part29 (uniformSphere stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM frob Tens TSymm)
open BstLean.Part43 (BofQ)
open FloorEnergy FloorCorrection
variable {n d : ℕ}

private lemma phi_zero (x : Fin n → ℝ) : phiM x (default : Mono n d) = 1 := by
  rfl

private lemma phi_cont (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) :=
  continuous_multiset_prod p.2.1 (fun i _ => continuous_apply i)

/-- The feature-operator bound with weight `W_F`. -/
def FeatOp (n d : ℕ) (μ : Measure (Fin n → ℝ)) (WF : ℝ) : Prop :=
  ∀ a : Mono n d → ℝ, a default = 0 →
    ∫ x, (∑ p, a p * phiM x p) ^ 2 ∂μ ≤ WF * (((d : ℝ) + 1) / n * nsq a)

/-- The main-term feature tensor estimate. -/
theorem feature_tensor71 {μ : Measure (Fin n → ℝ)} {WF : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hsph : SphLaw n μ) (hWF : 0 < WF) (hop : FeatOp n d μ WF) (c : ℕ) :
    frob (fun w : Fin c → Mono n d =>
      (∫ x, ∏ t, phiM x (w t) ∂μ) - ∏ t, if w t = default then (1 : ℝ) else 0) ≤
        (4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1) / n) := by
  classical
  let e : Mono n d → ℝ := fun p => if p = default then 1 else 0
  let η : ℝ := WF * ((d : ℝ) + 1) / n
  have hη : 0 < η := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp [η]
    positivity
  have he : ∑ p, e p ^ 2 = 1 := by simp [e]
  have hbound : ∀ᵐ x ∂μ, ∑ p : Mono n d, phiM x p ^ 2 ≤ (d : ℝ) + 1 := by
    filter_upwards [hsph.sphere] with x hx
    exact (BstLean.Part43.phiSq_bounds (by omega) x hx).2
  have hop' : ∀ a : Mono n d → ℝ,
      ∫ x, (∑ p, a p * (phiM x p - e p)) ^ 2 ∂μ ≤ η * ∑ p, a p ^ 2 := by
    intro a
    let b : Mono n d → ℝ := fun p => if p = default then 0 else a p
    have hb0 : b default = 0 := by simp [b]
    have hsum (x : Fin n → ℝ) :
        (∑ p, a p * (phiM x p - e p)) = ∑ p, b p * phiM x p := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = default
      · subst p
        simp [e, b, phi_zero]
      · simp [e, b, hp]
    simp_rw [hsum]
    have hb : nsq b ≤ ∑ p, a p ^ 2 := by
      unfold nsq
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : p = default
      · simp [b, hp, sq_nonneg]
      · simp [b, hp]
    have h1 := hop b hb0
    have h2 : WF * (((d : ℝ) + 1) / n * nsq b) = η * nsq b := by dsimp [η]; ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hb hη.le)
  exact error53_tensor_mean hsph (fun p x => phiM x p) phi_cont e he
    η ((d : ℝ) + 1) hη (by have := Nat.cast_nonneg (α := ℝ) d; linarith) hbound hop' c

/-- `main = Σ_{c=1}^k c!·(4(d+1))^c·W_F·(d+1)`. -/
noncomputable def mainW (d k : ℕ) (WF : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 k, (c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1))

private lemma main_zero {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ)
    (s : ℝ) (B : Tens n) : error53_main_energy (d := d) μ s B 0 = 0 := by
  let := hμ.prob
  rw [error53_main_energy_formula]
  simp [frob]

private lemma main_bound71 (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {WF : ℝ} (hsph : SphLaw n μ) (hWF : 0 < WF) (hop : FeatOp n d μ WF)
    (k c : ℕ) (hc : c ∈ Finset.Icc 1 k) (f0 : ℝ) (T : Tens n) :
    error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c ≤
      ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1))) /
        (n : ℝ) * Ncirc n d k f0 T := by
  have hh := feature_tensor71 hn hd hsph hWF hop c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hf : 0 ≤ frob (Tcirc n d k f0 T c) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ (c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c *
      (WF * ((d : ℝ) + 1)) := by positivity
  rw [error53_main_energy_formula, BstLean.Part59.FloorCorrection59x.sg_pow_even hn c]
  calc
    _ ≤ (c.factorial : ℝ) * (1 / BstLean.Part36.DD n d ^ c) *
        frob (Tcirc n d k f0 T c) *
          ((4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1) / n)) := by
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ = ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1))) /
        (n : ℝ) * (frob (Tcirc n d k f0 T c) / BstLean.Part36.DD n d ^ c) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (BstLean.Part59.FloorCorrection59x.Ncirc_term_le hn k c f0 T hc) (div_nonneg hC hn0.le)

private theorem total_main71 (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} {WF : ℝ} (hsph : SphLaw n μ) (hWF : 0 < WF) (hop : FeatOp n d μ WF)
    (k : ℕ) (f0 : ℝ) (T : Tens n) :
    (∑ c ∈ Finset.range (k + 1), error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) ≤
      mainW d k WF / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  have he : (∑ c ∈ Finset.range (k + 1),
      error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) =
      ∑ c ∈ Finset.Icc 1 k, error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c := by
    rw [Finset.sum_range_succ', main_zero hsph, add_zero]
    rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm 1 i]
  rw [he]
  calc
    _ ≤ ∑ c ∈ Finset.Icc 1 k,
        ((c.factorial : ℝ) * (4 * ((d : ℝ) + 1)) ^ c * (WF * ((d : ℝ) + 1))) /
          (n : ℝ) * Ncirc n d k f0 T :=
      Finset.sum_le_sum (fun c hc => main_bound71 hn hd hsph hWF hop k c hc f0 T)
    _ = _ := by unfold mainW; rw [← Finset.sum_mul, ← Finset.sum_div]

/-- **Prop E, generic form**: `E_Z (B − g₀)(σZ)² ≤ (2·corr + 2·main)/n · N°`. -/
theorem normalized_bound71 (hn : 1 ≤ n) (hd : 1 ≤ d)
    {μ : Measure (Fin n → ℝ)} (hsph : SphLaw n μ) {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdev : DevW n d μ w) {WF : ℝ} (hWF : 0 < WF) (hop : FeatOp n d μ WF) (hTr : LemmaTr53)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) :
    (∫ Z, (BofQ μ k f0 T (sg n d • Z) - g0 n d k f0 T (sg n d • Z)) ^ 2
      ∂stdGauss (CoefIdxD n d)) ≤
    (2 * totW d k (Finset.range (k + 1)) w + 2 * mainW d k WF) / (n : ℝ) * Ncirc n d k f0 T := by
  classical
  rw [error53_error_energy_split hn k f0 T hT hsph]
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1),
        (2 * (∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact error53_mean_perturbation hsph k c (sg n d)
        (c0 d / BstLean.Part36.DD n d) (TF k f0 T)
    _ = 2 * (∑ c ∈ Finset.range (k + 1),
        ∫ x, kernelErrorSq (d := d) k c (sg n d)
          (c0 d / BstLean.Part36.DD n d) (TF k f0 T) x ∂μ) +
        2 * (∑ c ∈ Finset.range (k + 1),
          error53_main_energy (d := d) μ (sg n d) (Tcirc n d k f0 T) c) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (totW d k (Finset.range (k + 1)) w / (n : ℝ) * Ncirc n d k f0 T) +
        2 * (mainW d k WF / (n : ℝ) * Ncirc n d k f0 T) := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        (mul_le_mul_of_nonneg_left (total_main71 hn hd hsph hWF hop k f0 T) (by norm_num))
      exact total_correction_W hn hd hsph hw hdev hTr k (Finset.range (k + 1))
        (fun c hc => by have := Finset.mem_range.mp hc; omega) f0 T
    _ = _ := by ring

/-! ## The chi-square instance -/

/-- The chi-square trace-moment weight `w(i) = √(1+|K|)·√((16i−1)!!)`. -/
noncomputable def wChi (K : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (1 + |K|) * Real.sqrt ((16 * i - 1).doubleFactorial : ℝ)

lemma wChi_nonneg (K : ℝ) (i : ℕ) : 0 ≤ wChi K i := by unfold wChi; positivity

/-- The chi-square feature weight `W_F = √(1+|K|)·√C`. -/
noncomputable def WFchi (K C : ℝ) : ℝ := Real.sqrt (1 + |K|) * Real.sqrt C

lemma WFchi_pos (K C : ℝ) (hC : 0 < C) : 0 < WFchi K C := by
  unfold WFchi
  have : 0 < 1 + |K| := by positivity
  positivity

lemma chiLaw_abs {μ : Measure (Fin n → ℝ)} {K : ℝ} (h : ChiLaw n μ K) : ChiLaw n μ |K| := by
  obtain ⟨hp, ρ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hp, ρ, h1, h2, h3, h4, h5.trans (by linarith [le_abs_self K])⟩

lemma devW_chi (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K : ℝ} (hμ : ChiLaw n μ K) :
    DevW n d μ (wChi K) := by
  intro i hi
  have h := chi_dev (d := d) hn (chiLaw_abs hμ) (lemmaU53 d) lemmaS53 i hi
  simpa only [wChi] using h

lemma featOp_chi (hn : 1 ≤ n) {μ : Measure (Fin n → ℝ)} {K C : ℝ} (hμ : ChiLaw n μ K)
    (hSH : SphereFourth71 d C) : FeatOp n d μ (WFchi K C) := by
  intro a ha
  have h := chi_feature hn (chiLaw_abs hμ) hSH a ha
  simpa only [WFchi] using h

/-- **The Prop E constant** `C_E = 2·corrE + 2·main` (no mixing factor). -/
noncomputable def CE71 (d k : ℕ) (K C : ℝ) : ℝ :=
  2 * totW d k (Finset.range (k + 1)) (wChi K) + 2 * mainW d k (WFchi K C)

/-- **Prop E under a chi-square bound**, from Lemma SH with constant `C > 0`. -/
theorem propE71 (d k : ℕ) (hd : 1 ≤ d) (K C : ℝ) (hC : 0 < C) (hSH : SphereFourth71 d C) :
    PropE71 d k K (CE71 d k K C) 1 := by
  intro n hn μ hμ f0 T hT hTk
  have hsph := chiLaw_sph hμ
  exact ⟨BstLean.Part53.error53_integrable hsph k f0 T (sg n d),
    normalized_bound71 hn hd hsph (wChi_nonneg K) (devW_chi hn hμ) (WFchi_pos K C hC)
      (featOp_chi hn hμ hSH) lemmaTr53 k f0 T hT⟩

end BstLean.Part71
