import BstLean.Part290FirstLayer

namespace BstLean.Part290
open Real MeasureTheory Set Matrix
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part205 BstLean.Part214
open BstLean.Part218 BstLean.Part227 BstLean.Part233
open BstLean.Part141 (rowS)

noncomputable def worldFirstEvent (n : ℕ) :
    Set (Matrix (Fin (mW n)) (Fin (2*n)) ℝ) :=
  concreteFirstLayerEvent (2*n) (mW n) (1/10^6) (1/10^7) worldEps

structure FirstLayerSupply (n : ℕ) : Prop where
  measurable : MeasurableSet (worldFirstEvent n)
  charge : (gaussMat (mW n) (2*n) (2/((2*n : ℕ) : ℝ))).real (worldFirstEvent n)ᶜ ≤ 804001/10^12
  mean_nonneg : 0 ≤ worldMean
  mean_reserve : worldMean < 525/10000
  row_sum : ∀ M₁ ∈ worldFirstEvent n, |rowS M₁/(mW n : ℝ)/2-1| ≤ 1/10^6
  energy_pos : ∀ M₁ ∈ worldFirstEvent n, 0 < firstQ M₁
  energy_upper : ∀ M₁ ∈ worldFirstEvent n,
    firstQ M₁ ≤ (1+1/10^6)*(mW n : ℝ)/((2*n : ℕ) : ℝ)
  centre : ∀ M₁ ∈ worldFirstEvent n, normSq (h1bar M₁) ≤ (31835/100000)*firstQ M₁
  distance : ∀ M₁ ∈ worldFirstEvent n,
    2/(mW n : ℝ)*worldDelta M₁ ≤ 2*worldMean/((2*n : ℕ) : ℝ)^2

theorem firstLayerSupply {n : ℕ} (ha : 8000 ≤ n) : FirstLayerSupply n := by
  have hn : 4096 ≤ n := by omega
  have hN : 2 ≤ 2*n := by omega
  have hm : 2 ≤ mW n := by have := BstLean.Part132.mW_ge hn; omega
  have hm1 : 1 ≤ mW n := by omega
  have hmp : (0 : ℝ) < mW n := by exact_mod_cast hm1
  have hNp : 0 < ((2*n : ℕ) : ℝ) := by positivity
  have hε : ∀ i, 0 < worldEps i := by intro i; fin_cases i <;> norm_num [worldEps]
  obtain ⟨hE,hc⟩ := concreteFirstLayerEvent_charge hN hm
    (by norm_num : (0 : ℝ) < 1/10^6) (by norm_num : (1/10^6 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1/10^7) hε
  refine ⟨hE, hc.trans (first_layer_charge ha), mean_reserve.1, mean_reserve.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro M₁ h₁
    have hω := h₁.1
    change |firstOmega M₁-1| ≤ 1/10^6 at hω
    have he : rowS M₁/(mW n : ℝ)/2 = firstOmega M₁ := by
      unfold firstOmega
      rw [div_div, mul_comm (mW n : ℝ) 2]
    rwa [he]
  · intro M₁ h₁
    exact (energy_window (by omega) hm1 M₁ (by norm_num : (1/10^6 : ℝ) < 1) h₁.1).1
  · intro M₁ h₁
    exact (energy_window (by omega) hm1 M₁ (by norm_num : (1/10^6 : ℝ) < 1) h₁.1).2.2
  · intro M₁ h₁
    have hQ := (energy_window (by omega) hm1 M₁ (by norm_num : (1/10^6 : ℝ) < 1) h₁.1).1
    exact (div_le_iff₀ hQ).mp ((world_ratio_window hn hm1 M₁ hQ).2.le)
  · intro M₁ h₁
    have hQ := energy_window (by omega) hm1 M₁ (by norm_num : (1/10^6 : ℝ) < 1) h₁.1
    have hTaylor : meanBound (normSq (h1bar M₁)/firstQ M₁) (worldT M₁) (worldNu M₁) ≤ meanDelta n := by
      rw [world_ratio (by omega) hm1 M₁ hQ.1]
      exact (e1_worldMean hn hm1 (by norm_num : (1/10^6 : ℝ) < 1) h₁).trans (mean_certificate ha)
    have hb := normalized_mean_bound hn hm1 M₁ hQ.1
      (show 0 ≤ meanDelta n by unfold meanDelta meanAllowance; positivity) hQ.2.2 hTaylor
    unfold normalizedMean at hb
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2/((2*n : ℕ) : ℝ)^2)
    rw [← mean_identity ha]
    convert hh using 1 <;> field_simp [hmp.ne',hNp.ne'] <;> ring

end BstLean.Part290

namespace BstLean.BlueprintLow

theorem worldFirstLayerBand {n : ℕ} (ha : 8000 ≤ n) (_hb : n ≤ 11882) :
    BstLean.Part290.FirstLayerSupply n := BstLean.Part290.firstLayerSupply ha

theorem worldRatioBand {n : ℕ} (ha : 8000 ≤ n) (_hb : n ≤ 11882) :
    BstLean.Part228.Bounds (BstLean.Part290.radiusOffset n) (1/2) (25001/50000) :=
  BstLean.Part290.radiusOffset_bounds ha

end BstLean.BlueprintLow
