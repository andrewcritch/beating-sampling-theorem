import BstLean.Part292Normalized
import BstLean.Part154NumA

/-! Coarser coefficient caps spend the exact-centering slack to simplify the band proof. -/
namespace BstLean.Part292
open Real BstLean.Part153

theorem normF0_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normF0 x (391/1000) (605/1000) (sqrt (999/2000)) 7 (1035/100) (414/10) (8*10^14) ≤ 36/10000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normF0
  calc
    _ ≤ (77782/100000 : ℝ)*(39895/100000 : ℝ)/(2*(70675/100000 : ℝ))*(1035/100 : ℝ)*(1/8000 : ℝ)+(39895/100000 : ℝ)/(2*(14142/10000 : ℝ)*(70675/100000 : ℝ)^3)*((414/10 : ℝ)/(62529/100000 : ℝ)*(1/8000 : ℝ)+(77782/100000 : ℝ)*(1035/100 : ℝ)^2*(1/8000 : ℝ)^3)+(3/2)*(39895/100000 : ℝ)*7/((70675/100000 : ℝ)*(62529/100000 : ℝ)*(391/1000 : ℝ)^4)*(8*10^14 : ℝ)*(1/8000 : ℝ)^7 := by gcongr
    _ ≤ _ := by norm_num

theorem normF1_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normF1 x (391/1000) (605/1000) (sqrt (999/2000)) 3 (1035/100) (414/10) (8*10^14) ≤ 126/100000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normF1
  calc
    _ ≤ (24198/100000 : ℝ)/(70675/100000 : ℝ)^2*((32172/10000 : ℝ)*(64343/10000 : ℝ)*(1/8000 : ℝ)+(77782/100000 : ℝ)*(32172/10000 : ℝ)*(1035/100 : ℝ)*(1/8000 : ℝ)^2)+4*(14143/10000 : ℝ)*3/(391/1000 : ℝ)^4*(8*10^14 : ℝ)*(1/8000 : ℝ)^7 := by gcongr
    _ ≤ _ := by norm_num

theorem normF2_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normF2 x (605/1000) (sqrt (999/2000)) (1035/100) ≤ 41/100000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normF2
  calc
    _ ≤ (77782/100000 : ℝ)*(39895/100000 : ℝ)/((14142/10000 : ℝ)*(70675/100000 : ℝ))*(1035/100 : ℝ)*(1/8000 : ℝ) := by gcongr
    _ ≤ _ := by norm_num

theorem normW0_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normW0 x (391/1000) (605/1000) (sqrt (999/2000)) 7 (1035/100) (414/10) (8*10^14) ≤ 205/100000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normW0
  calc
    _ ≤ (605/1000 : ℝ)*(1035/100 : ℝ)*(1/8000 : ℝ)+(24198/100000 : ℝ)/(2*(70675/100000 : ℝ)^2)*((414/10 : ℝ)*(1/8000 : ℝ)+(605/1000 : ℝ)*(1035/100 : ℝ)^2*(1/8000 : ℝ)^3)+4*7/(391/1000 : ℝ)^4*(8*10^14 : ℝ)*(1/8000 : ℝ)^7 := by gcongr
    _ ≤ _ := by norm_num

theorem normW1_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normW1 x (391/1000) (605/1000) (sqrt (999/2000)) 3 2 (1035/100) (414/10) (8*10^14) ≤ 161/100000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normW1
  calc
    _ ≤ (14143/10000 : ℝ)*(39895/100000 : ℝ)/(70675/100000 : ℝ)*((77782/100000 : ℝ)*(32172/10000 : ℝ)*(64343/10000 : ℝ)*(1/8000 : ℝ)+(605/1000 : ℝ)*(32172/10000 : ℝ)*(1035/100 : ℝ)*(1/8000 : ℝ)^2)+4*(14143/10000 : ℝ)*3*2/(391/1000 : ℝ)^4*(8*10^14 : ℝ)*(1/8000 : ℝ)^7 := by gcongr
    _ ≤ _ := by norm_num

theorem normW2_cap {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1/8000) :
    normW2 x (391/1000) (605/1000) 3 (1035/100) (8*10^14) ≤ 79/100000 := by
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hsl : (70675/100000 : ℝ) ≤ sqrt (999/2000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hrl : (62529/100000 : ℝ) ≤ sqrt (391/1000) := by
    apply le_sqrt_of_sq_le; norm_num
  have hru : sqrt (605/1000 : ℝ) ≤ 77782/100000 := by
    apply sqrt_le_iff.mpr; norm_num
  have h2l : (14142/10000 : ℝ) ≤ sqrt 2 := by
    apply le_sqrt_of_sq_le; norm_num
  have h2u : sqrt (2 : ℝ) ≤ 14143/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hdu : sqrt (1035/100 : ℝ) ≤ 32172/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  have hvu : sqrt (414/10 : ℝ) ≤ 64343/10000 := by
    apply sqrt_le_iff.mpr; norm_num
  unfold normW2
  calc
    _ ≤ (605/1000 : ℝ)*(1035/100 : ℝ)*(1/8000 : ℝ)+28*3^2/(391/1000 : ℝ)^4*(8*10^14 : ℝ)*(1/8000 : ℝ)^7 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part292
