import BstLean.Part287WorldConstants
import BstLean.Part271GlobalMaster

/-! One World package from the endpoint witnesses and scaled width bounds.
The construction uses no dimension-indexed list of exact width computations. -/
namespace BstLean.Part287.World

open Real BstLean.Part130 BstLean.Part137 BstLean.Part192 BstLean.Part227
open BstLean.Part271.R3

noncomputable def q (n : ℕ) : ℝ := q0 * n / 13225

theorem square_width {n : ℕ} (ha : 13225 ≤ n) :
    (n : ℝ)^2 / mW n ≤ 1 / (115 * 13225) := by
  have hn := Band.n_positive ha
  have hm : 0 < (mW n : ℝ) := (by norm_num : (0 : ℝ) < 1).trans (Band.width_positive ha)
  have hw : 115 * (n : ℝ)^3 ≤ mW n := by exact_mod_cast Band.width_cube ha
  have hnR : (13225 : ℝ) ≤ n := by exact_mod_cast ha
  calc
    (n : ℝ)^2 / mW n ≤ 1 / (115 * (n : ℝ)) := by
      apply (div_le_div_iff₀ hm (by positivity)).mpr
      nlinarith only [hw]
    _ ≤ _ := one_div_le_one_div_of_le (by norm_num) (by linarith only [hnR])

theorem linear_width {n : ℕ} (ha : 13225 ≤ n) :
    (n : ℝ) / mW n ≤ 1 / (115 * 13225^2) := by
  have h := (Band.dimension_width ha).2
  push_cast at h
  rw [mul_div_assoc] at h
  linarith only [h]

theorem inverse_n {n : ℕ} (ha : 13225 ≤ n) :
    1 / (n : ℝ) ≤ 1 / 13225 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha)

theorem hidden_bound {n : ℕ} (ha : 13225 ≤ n) :
    hiddenChargeWithDistance n (44945/10^6) (4/10000) (178/10^8) (1232/10^7)
      (paymentBound n (q n)) ≤ BstLean.Part271.GlobalMaster.world.hiddenCharge := by
  have hn := Band.n_positive ha
  have hm : 0 < (mW n : ℝ) := (by norm_num : (0 : ℝ) < 1).trans (Band.width_positive ha)
  have hW := (Band.inverse_width ha).2
  have hN := inverse_n ha
  have hNW := linear_width ha
  have hNNW := square_width ha
  have hWN : (1 / (mW n : ℝ)) * (1 / (n : ℝ)) ≤
      (1 / 266001988046875 : ℝ) * (1 / 13225) :=
    mul_le_mul hW hN (by positivity) (by norm_num)
  calc
    _ = (372 / 1000 : ℝ) * (44945 / 10^6)^2 + (448 / 1000) * (4 / 10000) +
      1/10^7 + 1/10^12 +
      ((279045642763226033/50000000000000) * 2 * q0 / 13225) * ((n : ℝ)^2 / mW n) +
      (((100000000024860904419623/1250000000000) +
        (800041348922962029453/100000000000000))/2 + 10^6) *
        ((1 / (mW n : ℝ)) * (1 / (n : ℝ))) +
      ((34507377374543524728617/100000000000000) +
        (1716/1000)^2 / (1232/10^7)^2) * (1 / (mW n : ℝ)) +
      ((1187885043021/20000000000000)/2) * (1 / (n : ℝ)) +
      ((4465/1000)/(178/10^8)) * ((n : ℝ) / mW n) + 9/10^8 := by
        unfold hiddenChargeWithDistance paymentBound q
        push_cast
        field_simp [ne_of_gt hn, ne_of_gt hm] <;> ring
    _ ≤ (372 / 1000 : ℝ) * (44945 / 10^6)^2 + (448 / 1000) * (4 / 10000) +
      1/10^7 + 1/10^12 +
      ((279045642763226033/50000000000000) * 2 * q0 / 13225) * (1 / (115 * 13225)) +
      (((100000000024860904419623/1250000000000) +
        (800041348922962029453/100000000000000))/2 + 10^6) *
        ((1 / 266001988046875) * (1 / 13225)) +
      ((34507377374543524728617/100000000000000) +
        (1716/1000)^2 / (1232/10^7)^2) * (1 / 266001988046875) +
      ((1187885043021/20000000000000)/2) * (1 / 13225) +
      ((4465/1000)/(178/10^8)) * (1 / (115 * 13225^2)) + 9/10^8 := by
        have hq0 : 0 ≤ q0 := by norm_num [q0]
        gcongr
    _ ≤ _ := by norm_num [q0, BstLean.Part271.GlobalMaster.world]

theorem moment_bound {n : ℕ} (ha : 13225 ≤ n) :
    momentEnvelope n ≤ BstLean.Part271.GlobalMaster.world.moment := by
  have hW := (Band.inverse_width ha).2
  have hNW := linear_width ha
  calc
    _ = (75935996087121/500000000000 : ℝ) * ((n : ℝ) / mW n) +
      (9840972690524073/40000000000) * (1 / (mW n : ℝ)) := by
        unfold momentEnvelope
        ring
    _ ≤ (75935996087121/500000000000 : ℝ) * (1/(115*13225^2)) +
      (9840972690524073/40000000000) * (1/266001988046875) := by gcongr
    _ ≤ _ := by norm_num [BstLean.Part271.GlobalMaster.world]

theorem frame_bound {n : ℕ} (ha : 13225 ≤ n) :
    frameEnvelope n r0 k0 k6 ≤ BstLean.Part271.GlobalMaster.world.frame := by
  have hnR : (13225 : ℝ) ≤ n := by exact_mod_cast ha
  have hr : 0 ≤ r0 := by norm_num [r0]
  calc
    _ ≤ frameEnvelope 13225 r0 k0 k6 := by
      unfold frameEnvelope
      gcongr
    _ ≤ _ := by norm_num [frameEnvelope, r0, k0, k6, BstLean.Part271.GlobalMaster.world]

noncomputable def arithmetic (n : ℕ) (ha : 13225 ≤ n) :
    RowArithmetic n BstLean.Part271.GlobalMaster.world.hiddenCharge
      BstLean.Part271.GlobalMaster.world.frame BstLean.Part271.GlobalMaster.world.moment where
  r0 := r0
  k0 := k0
  k6 := k6
  q := q n
  r0_nonneg := by norm_num [r0]
  radius := by
    have hnR : (13225 : ℝ) ≤ n := by exact_mod_cast ha
    exact (by norm_num [r0] : (1 : ℝ) ≤ r0^2 * (13225 : ℝ)^3).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hnR 3) (sq_nonneg r0))
  k0_nonneg := by norm_num [k0]
  kernel := by norm_num [r0, k0]
  k6_nonneg := by norm_num [k6]
  sixth := by
    have hnR : (13225 : ℝ) ≤ n := by exact_mod_cast ha
    refine le_trans (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 15)
      (by norm_num : (0 : ℝ) < 8 * 13225) (by linarith only [hnR])) ?_
    norm_num [k6]
  q_nonneg := by unfold q q0; positivity
  q_square := by
    have hnR : (13225 : ℝ) ≤ n := by exact_mod_cast ha
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsq : (13225 : ℝ) * n ≤ (n : ℝ)^2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hnR hn0
    norm_num [q, q0, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hsq, hn0]
  hidden_payment := hidden_bound ha
  frame_payment := frame_bound ha
  moment_payment := moment_bound ha

noncomputable def worldPackage (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    WorldPackage (paperProgram n) BstLean.Part271.GlobalMaster.world :=
  (arithmetic n ha).worldPackage ha hb

theorem product_lower {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (202225/100000 : ℝ) ≤ productLower n (1232/10^7) :=
  (by norm_num : (202225/100000 : ℝ) ≤ _).trans (FrameBand.productlo ha hb).1

theorem product_upper {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    productUpper n (1232/10^7) ≤ (202831/100000 : ℝ) :=
  (FrameBand.producthi ha hb).2.trans (by norm_num)

end BstLean.Part287.World
