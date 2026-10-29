import BstLean.Part252TableEnvelope
import BstLean.Part154NumA

namespace BstLean.Part252
open Real
open BstLean.Part130 BstLean.Part153 BstLean.Part170 BstLean.Part171 BstLean.Part220

structure TableCoefficientCertificate (C : ℝ) : Prop where
  f0 : (tableEnvelope C).f0 12225 160 ≤ 520 / 10 ^ 11
  f1 : (tableEnvelope C).f1 12225 160 ≤ 180 / 10 ^ 11
  f2 : (tableEnvelope C).f2 ≤ 42 / 10 ^ 11
  w0 : (tableEnvelope C).w0 12225 160 ≤ 210 / 10 ^ 13
  w1 : (tableEnvelope C).w1 12225 160 ≤ 150 / 10 ^ 13
  w2 : (tableEnvelope C).w2 12225 160 ≤ 54 / 10 ^ 13

theorem table_coefficient_certificate {C : ℝ} (hC : 0 ≤ C) (hC4 : C ≤ 4) :
    TableCoefficientCertificate C := by
  let d := tableEnvelope C
  have hd : 0 ≤ d.D ∧ d.D ≤ 535 / 10 ^ 14 := table_envelope_D hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 535 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 175 / 10 ^ 17 := table_envelope_V hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 7 / 10 ^ 15 := table_envelope_P hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (372 / 100000 : ℝ) ≤ √(17 / (100 * 12225) : ℝ) :=
    le_sqrt_of_sq_le (by norm_num)
  have hsm0 : 0 ≤ √(17 / (100 * 12225) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2314 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 4184 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA 12225) * 160 ≤ 186 / 10000 := by
    have hs : √(tA 12225) ≤ 116 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num [tA, mA])
    linarith
  have hS : √(26 / (10 * 12225) : ℝ) ≤ 146 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hG : tA 12225 * (160 : ℝ) ^ 2 + 26 / (10 * 12225) ≤ 56 / 100000 := by
    norm_num [tA, mA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * 12225) : ℝ)) (tA 12225 * 160 ^ 2 + 26 / (10 * 12225)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (372 / 100000)) * (535 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (372 / 100000) ^ 3) * (175 / 10 ^ 17)) + (7 / 10 ^ 15) * (3 / 2 * (39895 / 100000) / (372 / 100000) * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * 12225) : ℝ)) d.D d.V d.P (√(tA 12225) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (372 / 100000) ^ 2 * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11))) + (7 / 10 ^ 15) * (2 * (2 * (14143 / 10000) * (186 / 10000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * 12225) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (372 / 100000) * (535 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * 12225) : ℝ)) (tA 12225 * 160 ^ 2 + 26 / (10 * 12225)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (372 / 100000) ^ 2) * (175 / 10 ^ 17) + (7 / 10 ^ 15) * (4 * (56 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * 12225) : ℝ)) (√(26 / (10 * 12225) : ℝ)) d.D d.V d.P (√(tA 12225) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (372 / 100000) * ((2314 / 10 ^ 9) * (4184 / 10 ^ 11)) + (7 / 10 ^ 15) * (4 * (14143 / 10000) * (186 / 10000) * (146 / 10000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA 12225) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (535 / 10 ^ 14 : ℝ) + (7 / 10 ^ 15) * (28 * (186 / 10000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
          | norm_num [tA, mA]
        all_goals positivity
      _ ≤ _ := by norm_num

end BstLean.Part252
