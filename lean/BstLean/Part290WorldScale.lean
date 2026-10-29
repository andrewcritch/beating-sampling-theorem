import BstLean.Part290Kernel
import BstLean.Part290Scale
import BstLean.Part271MomentScale
import BstLean.Part233Concrete
import BstLean.Part236Frame

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part140 BstLean.Part159
open BstLean.Part227 BstLean.Part233 BstLean.Part228
open BstLean.Part271.R3 (arCore chCore lxCore arW_scale lxG_scale)

noncomputable def worldR0 (n : ℕ) : ℝ := 1/((n : ℝ)*√(n : ℝ))
noncomputable def worldK0 (n : ℕ) : ℝ := √((2235/100)*worldR0 n)
noncomputable def worldK6 (n : ℕ) : ℝ := √(15/(8*(n : ℝ)))
noncomputable def worldS (n : ℕ) : ℝ :=
  1-22287/10^6-(4938/10000+12375/10^6)^2/centreLower n (1232/10^7)
noncomputable def worldAK (n : ℕ) : ℝ := (1+1/10^9)*worldK0 n/worldS n
noncomputable def worldAD (n : ℕ) : ℝ :=
  (1+1/10^9)*(2235/100)*worldR0 n/((n : ℝ)*(22287/10^6)^2)
noncomputable def worldC1 (n : ℕ) : ℝ :=
  (3017/20000+(138/1000)/(2*(n : ℝ))+(1/1000)*(17321/20000)+
    (2/5)*worldK6 n+centreDistance n (525/10000))/worldS n+
      centreFluctuation n (25/10^7)/(12375/10^6)^2+
        worldAK n*(1/10^6)+worldAD n*(1/10^12)

theorem inverse_n {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (1/(n : ℝ)) 0 (1/8000) := by
  have hn : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hn⟩

theorem worldR0_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldR0 n) 0 (1/715520) := by
  have hn : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hs : (2236/25 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  unfold worldR0
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ?_⟩
  nlinarith [mul_le_mul hn hs (by norm_num : (0 : ℝ) ≤ 2236/25) (by positivity)]

theorem width_four {n : ℕ} (ha : 8000 ≤ n) : mW n ≤ n^4 := by
  apply (mW_le_iff _ _).mpr
  calc
    n^7 = n^7*1 := by ring
    _ ≤ n^7*n := Nat.mul_le_mul_left _ (by omega)
    _ = (n^4)^2 := by ring

theorem calibration_bound {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (BstLean.Part210.Rnew n) 0 (92/10000) := by
  have hn := n_positive ha
  have hn' : (8000 : ℝ) ≤ n := by exact_mod_cast ha
  have hs : (2236/25 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hw : (mW n : ℝ) ≤ (n : ℝ)^4 := by exact_mod_cast width_four ha
  have hroot : √(mW n : ℝ) ≤ (n : ℝ)^2 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith only [hw]⟩
  have hfirst : (501/1000 : ℝ)/√(n : ℝ) ≤ (501/1000)/(2236/25) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hsecond : (406/10^7 : ℝ)*√(mW n : ℝ)/(n : ℝ)^2 ≤ 406/10^7 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hroot]
  unfold BstLean.Part210.Rnew
  exact ⟨by positivity, by linarith only [hfirst, hsecond]⟩

theorem arW_scaled_inverse {n : ℕ} :
    arW n = arCore n*√(1/(mW n : ℝ)) := by
  unfold arW arCore
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 10+25/(mW n : ℝ))]
  congr 1
  ring

theorem chCore_inverse {n : ℕ} (hn : 0 < (n : ℝ)) :
    chCore n = √(6*(1+5/(mW n : ℝ))+
      ((1/π)*(√5+√(1/(n : ℝ)))+√((1+1/(n : ℝ))/2))^2) := by
  have he : (2 : ℝ)/(2*(n : ℝ)) = 1/(n : ℝ) := by field_simp [ne_of_gt hn]
  simp only [chCore,kappa_zero,Nat.cast_mul,Nat.cast_ofNat,he]

noncomputable def worldMomentMain (n : ℕ) : ℝ :=
  ((202798/100000)/(1-22/1000)^2*(arCore n+(2+22/1000)*lxCore n))^2/
    (((202278/100000)-1)^2*cRhoG (202278/100000) (202798/100000) (22/1000))
noncomputable def worldMomentResidual (n : ℕ) : ℝ :=
  2*(arCore n^2+lxCore n^2)/(22/1000)^2

theorem world_moment_scale {n : ℕ} (hm : 1 < (mW n : ℝ)) :
    momentValue n (202278/100000) (202798/100000) (22/1000) =
      (((2*n : ℕ) : ℝ)/(mW n : ℝ))/2*worldMomentMain n+
        (1/(mW n : ℝ))*worldMomentResidual n := by
  have hmp : 0 < (mW n : ℝ) := by linarith
  unfold momentValue vPert
  rw [lxG_scale hmp, arW_scale hmp]
  have hs := Real.sq_sqrt hmp.le
  calc
    _ = ((n : ℝ)*worldMomentMain n+worldMomentResidual n)/(√(mW n : ℝ))^2 := by
      unfold worldMomentMain worldMomentResidual
      ring
    _ = _ := by rw [hs]; push_cast; ring

theorem grouped_charge_scaled {n : ℕ} (hn : 0 < (n : ℝ)) (sp p₂ dT eB p : ℝ) :
    groupedCharge n sp p₂ dT eB p =
      372/1000*sp^2+448/1000*p₂+p+
        (4465/1000)*((((2*n : ℕ) : ℝ)/(mW n : ℝ))/2)/dT+
          (1716/1000)^2*(1/(mW n : ℝ))/eB^2 := by
  unfold groupedCharge
  push_cast
  field_simp [ne_of_gt hn]
  <;> ring

end BstLean.Part290
