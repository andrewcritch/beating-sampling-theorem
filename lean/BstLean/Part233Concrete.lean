import BstLean.Part233Paper
import BstLean.Part218ConcreteDistance

/-! S08 and S09 supply the actual first-layer event for cancellation grouping. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part214 BstLean.Part218
open BstLean.Part141 (rowS)
open BstLean.Part134 BstLean.Part140 BstLean.Part157 BstLean.Part159
open BstLean.Part227 BstLean.Part192

noncomputable def concreteGroupPayment (n : ℕ) (εω ph Δ Xc : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  e1Charge (2 * n) (mW n) εω ph ε +
    cancellationPayment n Xc (((2 * n : ℕ) : ℝ) * (1 + εω) * Δ) εω +
      outputNormPayment n εω

/-- All network event and moment premises are supplied; scalar certificates remain explicit. -/
theorem concrete_distanceGroup_charge {n : ℕ} (hn : 4096 ≤ n)
    {εω ph Δ Xc : ℝ} {ε : Fin 4 → ℝ}
    (hεω : 0 < εω) (hεω1 : εω ≤ 1 / 1000)
    (hph : 0 < ph) (hε : ∀ i, 0 < ε i) (hΔ0 : 0 ≤ Δ)
    (hΔ : e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc) :
    (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤
      concreteGroupPayment n εω ph Δ Xc ε := by
  have hN : 2 ≤ 2 * n := by omega
  have hm : 2 ≤ mW n := by have := BstLean.Part132.mW_ge hn; omega
  have hm1 : 1 ≤ mW n := by omega
  have hmp : (0 : ℝ) < mW n := by exact_mod_cast hm1
  have hn' : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  have hεωlt : εω < 1 := by linarith
  obtain ⟨hE, hc⟩ := concreteFirstLayerEvent_charge hN hm hεω hεωlt hph hε
  apply paper_distanceGroup_charge hn hE hεω.le hεω1 (by positivity) hX hc
  · intro M₁ h₁
    have hω := h₁.1
    change |firstOmega M₁ - 1| ≤ εω at hω
    have he : rowS M₁ / (mW n : ℝ) / 2 = firstOmega M₁ := by
      unfold firstOmega
      rw [div_div, mul_comm (mW n : ℝ) 2]
    rwa [he]
  · intro M₁ h₁
    exact (energy_window (by omega) hm1 M₁ hεωlt h₁.1).1
  · intro M₁ h₁
    exact (energy_window (by omega) hm1 M₁ hεωlt h₁.1).2.2
  · intro M₁ h₁
    have hQ := (energy_window (by omega) hm1 M₁ hεωlt h₁.1).1
    have hr := (world_ratio_window hn hm1 M₁ hQ).2.le
    exact (div_le_iff₀ hQ).mp hr
  · intro M₁ h₁
    have hQ := energy_window (by omega) hm1 M₁ hεωlt h₁.1
    have hTaylor : meanBound (normSq (h1bar M₁) / firstQ M₁)
        (worldT M₁) (worldNu M₁) ≤ Δ := by
      rw [world_ratio (by omega) hm1 M₁ hQ.1]
      exact (e1_worldMean hn hm1 hεωlt h₁).trans hΔ
    have hb := normalized_mean_bound hn hm1 M₁ hQ.1 hΔ0 hQ.2.2 hTaylor
    unfold normalizedMean at hb
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 / (((2 * n : ℕ) : ℝ) ^ 2))
    convert hh using 1 <;> field_simp [hmp.ne', hn'.ne'] <;> ring

/-- The concrete cancellation payment replaces all three separate hidden payments. -/
theorem concrete_hidden_charge {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB εω ph Δ : ℝ} {ε : Fin 4 → ℝ}
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hdT : 0 < dT) (heB : 0 < eB)
    (hεω : 0 < εω) (hεω1 : εω ≤ 1 / 1000)
    (hph : 0 < ph) (hε : ∀ i, 0 < ε i) (hΔ0 : 0 ≤ Δ)
    (hΔ : e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      groupedCharge n sp p₂ dT eB (concreteGroupPayment n εω ph Δ Xc ε) :=
  hidden_charge_of_group hn hsp hp₂ hdT heB
    (concrete_distanceGroup_charge hn hεω hεω1 hph hε hΔ0 hΔ hX)

/-- S08, S09 and the grouped concentration supply the unchanged exact-moment World package. -/
noncomputable def concreteWorldPackage {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB εω ph Δ Alo Ahi ζ : ℝ} {ε : Fin 4 → ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 < dT) (hdT : dT ≤ 1 / 400000) (heB : 0 < eB)
    (hεω : 0 < εω) (hεω1 : εω ≤ 1 / 1000)
    (hph : 0 < ph) (hε : ∀ i, 0 < ε i) (hΔ0 : 0 ≤ Δ)
    (hΔ : e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc)
    (c : FrameCertificate n sp p₂ Xc dT eB)
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    WorldPackage (paperProgram n)
      (groupedWorldParameters c (concreteGroupPayment n εω ph Δ Xc ε) Alo Ahi ζ) :=
  worldPackage_of_group hn hsp hp₂
    (concrete_distanceGroup_charge hn hεω hεω1 hph hε hΔ0 hΔ hX)
    hXc hdT0 hdT heB c hk hAlo hlo hhi hζ0 hζ1

end BstLean.Part233
#print BstLean.Part233.concrete_distanceGroup_charge
#print axioms BstLean.Part233.concrete_distanceGroup_charge
#print axioms BstLean.Part233.concrete_hidden_charge
#print BstLean.Part233.concreteWorldPackage
#print axioms BstLean.Part233.concreteWorldPackage
