import BstLean.Part241Price

/-! The regular and exceptional squared prices give one comparison root. -/
namespace BstLean.Part241
open MeasureTheory Real
open BstLean.Part161 (hellG2)

theorem free_epsilon_price {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n)
    {γ e χ d ε vmax aw af Hf Cv cA2 : ℝ} (hγ : 0 < γ) (he : 0 < e) (hd : 1 / 5 ≤ d)
    (hc0 : 0 ≤ cA2) (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    {fb ft wb wt V : α → ℝ} (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 2) K μ)
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 6) K μ)
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ)
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 4) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ)
    (if4 : IntegrableOn (fun a => fb a ^ 4) K μ)
    (if24 : IntegrableOn (fun a => fb a ^ 24) K μ)
    (ifF2 : IntegrableOn (fun a => fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (ifF6 : IntegrableOn (fun a => fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) K μ)
    (iV : IntegrableOn (fun a => ((n : ℝ) * V a) ^ 2) K μ)
    (hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8)
    (hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8)
    (hf4 : ∫ a in K, fb a ^ 4 ∂μ ≤ Hf ^ 4)
    (hf24 : ∫ a in K, fb a ^ 24 ∂μ ≤ Hf ^ 24)
    (hV : ∫ a in K, ((n : ℝ) * V a) ^ 2 ∂μ ≤ Cv ^ 2) :
    ∫ a in K, hellG2 n ((fb a / √e - ft a / √e) ^ 2 * cA2) (γ * (wb a - fb a ^ 2 - V a))
        (γ * max (1 / 5) (wt a - ft a ^ 2)) ∂μ ≤ squaredPrice n χ d ε vmax aw af Hf Cv := by
  rw [squaredPrice_eq_PB]
  exact BstLean.Part169.bias_price_paper μ hK hK1 n hn hγ he hd hc0 hc hε1 hT
    haw haf hHf hCv mfb mft mwb mwt mV hSbd hVm iW2 iW6 iW8 iF2 iF4 iF8
    if4 if24 ifF2 ifF6 iV hW8 hF8 hf4 hf24 hV

theorem free_epsilon_root {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n)
    {γ e χ d ε vmax aw af Hf Cv cA2 : ℝ} (hγ : 0 < γ) (he : 0 < e) (hd : 1 / 5 ≤ d)
    (hc0 : 0 ≤ cA2) (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    {fb ft wb wt V : α → ℝ} (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 2) K μ)
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 6) K μ)
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ)
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 4) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ)
    (if4 : IntegrableOn (fun a => fb a ^ 4) K μ)
    (if24 : IntegrableOn (fun a => fb a ^ 24) K μ)
    (ifF2 : IntegrableOn (fun a => fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) K μ)
    (ifF6 : IntegrableOn (fun a => fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) K μ)
    (iV : IntegrableOn (fun a => ((n : ℝ) * V a) ^ 2) K μ)
    (hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8)
    (hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8)
    (hf4 : ∫ a in K, fb a ^ 4 ∂μ ≤ Hf ^ 4)
    (hf24 : ∫ a in K, fb a ^ 24 ∂μ ≤ Hf ^ 24)
    (hV : ∫ a in K, ((n : ℝ) * V a) ^ 2 ∂μ ≤ Cv ^ 2) :
    √(∫ a in K, hellG2 n ((fb a / √e - ft a / √e) ^ 2 * cA2) (γ * (wb a - fb a ^ 2 - V a))
        (γ * max (1 / 5) (wt a - ft a ^ 2)) ∂μ) ≤ biasRoot n χ d ε vmax aw af Hf Cv := by
  exact Real.sqrt_le_sqrt (free_epsilon_price μ hK hK1 n hn hγ he hd hc0 hc hε1 hT
    haw haf hHf hCv mfb mft mwb mwt mV hSbd hVm iW2 iW6 iW8 iF2 iF4 iF8
    if4 if24 ifF2 ifF6 iV hW8 hF8 hf4 hf24 hV)

end BstLean.Part241
