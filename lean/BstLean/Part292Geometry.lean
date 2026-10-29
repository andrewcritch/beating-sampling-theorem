import BstLean.Part280Table

/-! Uniform bulk geometry from the joint circle identity, without dimension rows. -/
namespace BstLean.Part292
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

def tableWorldGuard {n : ℕ} (wr : WRet n) : Prop :=
  windowW wr ∧ BstLean.Part150.thetaC wr.2 (tau0p wr.1) ≤ 528/1000

theorem tableWorldGuard_measurable {n : ℕ} :
    MeasurableSet {wr : WRet n | tableWorldGuard wr} := by
  have ht : Measurable (fun wr : WRet n => tau0p wr.1) := measurable_tau0p.comp measurable_fst
  have hθ : Measurable (fun wr : WRet n => BstLean.Part150.thetaC wr.2 (tau0p wr.1)) := by
    unfold BstLean.Part150.thetaC
    exact ((ht.pow_const 2).const_mul _).div
      (((BstLean.Part150.measurable_rhoC (n := n)).comp (measurable_snd.prodMk ht)).pow_const 2)
  exact measurableSet_windowW.inter (measurableSet_le hθ measurable_const)

theorem circle_upper_low {N a b : ℝ} (hN : 8000 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a^2+N*b^2=1)
    (hl : 46/100 ≤ N*b^2) (hu : N*b^2 ≤ 54/100) :
    a+6*b ≤ 78038/100000 := by
  have hN0 : 0 < N := by linarith
  let a0 : ℝ := sqrt (54/100)
  let b0 : ℝ := sqrt ((46/100)/N)
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have hb0 : 0 ≤ b0 := sqrt_nonneg _
  have ha02 : a0^2 = 54/100 := sq_sqrt (by norm_num)
  have hb02 : N*b0^2 = 46/100 := by
    dsimp [b0]
    rw [sq_sqrt (by positivity)]
    field_simp
  have haa : a ≤ a0 := by
    apply (sq_le_sq₀ ha ha0.le).mp
    nlinarith only [hc, hl, ha02]
  have hbb : b0 ≤ b := by
    have h : b0^2 ≤ b^2 := by
      apply (mul_le_mul_iff_right₀ hN0).mp
      nlinarith only [hb02, hl]
    exact (sq_le_sq₀ hb0 hb).mp h
  have hbN : 6 ≤ N*b0 := by
    have hmul := congrArg (fun t : ℝ => N*t) hb02
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6)
      (mul_nonneg hN0.le hb0)).mp
    nlinarith only [hmul, hN]
  have hlin : 6*(a+a0) ≤ N*(b+b0) := by
    have ha1 : a ≤ 1 := by
      apply (sq_le_sq₀ ha (by norm_num : (0 : ℝ) ≤ 1)).mp
      nlinarith only [hc, hl]
    have ha01 : a0 ≤ 1 := by
      apply (sq_le_sq₀ ha0.le (by norm_num : (0 : ℝ) ≤ 1)).mp
      nlinarith only [ha02]
    have hNb : 6 ≤ N*b := hbN.trans (mul_le_mul_of_nonneg_left hbb hN0.le)
    nlinarith only [ha1, ha01, hbN, hNb]
  have hprod := mul_nonneg (sub_nonneg.mpr hbb) (sub_nonneg.mpr hlin)
  have hprod' : 0 ≤ (a+a0)*(a0+6*b0-a-6*b) := by
    nlinarith only [hprod, hc, ha02, hb02]
  have hsum : a+6*b ≤ a0+6*b0 := by
    have hpos : 0 < a+a0 := by linarith only [ha, ha0]
    have h' := nonneg_of_mul_nonneg_right hprod' hpos
    linarith only [h']
  have haU : a0 ≤ 734847/1000000 := by
    apply sqrt_le_iff.mpr
    norm_num
  have hbU : b0 ≤ 7583/1000000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hN0).mpr
    nlinarith only [hN]
  linarith only [hsum, haU, hbU]

theorem circle_bulk_low {N a b s : ℝ} (hN : 8000 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a^2+N*b^2=1)
    (hl : 46/100 ≤ N*b^2) (hu : N*b^2 ≤ 54/100)
    (hs : a-6*b ≤ s ∧ s ≤ a+6*b) :
    0 ≤ s ∧ 391/1000 ≤ 1-s^2 ∧ 1-s^2 ≤ 605/1000 := by
  have hsU := hs.2.trans (circle_upper_low hN ha hb hc hl hu)
  have haL : 6782/10000 ≤ a := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6782/10000) ha).mp
    nlinarith only [hc, hu]
  have hbU' : b ≤ 822/100000 := by
    have hb2 : (8000 : ℝ)*b^2 ≤ 54/100 :=
      (mul_le_mul_of_nonneg_right hN (sq_nonneg b)).trans hu
    apply (sq_le_sq₀ hb (by norm_num : (0 : ℝ) ≤ 822/100000)).mp
    nlinarith only [hb2]
  have hsL : 62888/100000 ≤ s := by linarith [hs.1]
  have hs0 : 0 ≤ s := by linarith only [hsL]
  have hsqL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 62888/100000) hsL 2
  have hsqU := pow_le_pow_left₀ hs0 hsU 2
  exact ⟨hs0, by nlinarith only [hsqU], by nlinarith only [hsqL]⟩

theorem node_geometry_low {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n}
    (hw : tableWorldGuard wr) (θ : AHid n) {g : ℕ} (hg : g < Js n) :
    0 ≤ nodeS (mkR wr θ) g ∧ 391/1000 ≤ 1-nodeS (mkR wr θ) g^2 ∧
      1-nodeS (mkR wr θ) g^2 ≤ 605/1000 := by
  let c := mkR wr θ
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hLH, _, _⟩ := bulk_of_window (by omega) c hw.1.1 hw.1.2.1 hw.1.2.2
  have hs := nodeS_mem c hLH hg
  let ρ := rhoR c
  have hρ2 : ρ^2 = normSq c.1.2+(n : ℝ)*tauR c^2 :=
    sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))
  have hτ : 0 < tauR c := hw.1.1
  have hρ0 : 0 < ρ := by
    apply sqrt_pos.mpr
    exact add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos hn0 (sq_pos_of_pos hτ))
  let a := sqrt (normSq c.1.2)/ρ
  let b := tauR c/ρ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a^2+(n : ℝ)*b^2=1 := by
    dsimp [a,b]
    rw [div_pow, div_pow, sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have htheta : BstLean.Part150.thetaC c.1.2 (tauR c) = (n : ℝ)*b^2 := by
    unfold BstLean.Part150.thetaC
    change _/ρ^2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hlo : 46/100 ≤ (n : ℝ)*b^2 := by
    rw [← htheta]
    exact hw.1.2.1
  have hhi : (n : ℝ)*b^2 ≤ 54/100 := by
    rw [← htheta]
    have h : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 528/1000 := hw.2
    linarith
  apply circle_bulk_low hnR ha hb hab hlo hhi
  have hL : nodeL c = a-6*b := by dsimp [nodeL, a, b]; ring
  have hH : nodeH c = a+6*b := by dsimp [nodeH, a, b]; ring
  simpa only [hL, hH] using hs

end BstLean.Part292
