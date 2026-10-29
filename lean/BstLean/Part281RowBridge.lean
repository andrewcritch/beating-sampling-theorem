import BstLean.Part281FrameAdapter
import BstLean.Part280Cert12224
import BstLean.Part259Family

namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part188 BstLean.Part192 BstLean.Part196 BstLean.Part263 BstLean.Part280

noncomputable def localRoot_from_numerics {n : ℕ} (hn : 11883 ≤ n) (hu : n ≤ 12224)
    {wp : WorldParameters} (W : WorldPackage (paperProgram n) wp)
    (hidden_eq : W.hidden = BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (upper : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    (R : ScalarRow n)
    (N : ∀ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) →
      BstLean.Part277.CellSourceNumericsP n (R.table i) R.M R.H R.xi
        1.22 1.12 1.25 0.665 0.47199 0.52358)
    (hM : R.M ≤ m2Caps.Mcap) (hH : R.H ≤ m2Caps.Hcap n) (hxi : R.xi ≤ m2Caps.xiCap)
    (hE : ∀ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) → (R.table i).energy ≤ m2Caps.Ecap) :
    SharpLocalSupply n m2Caps (sharpTableN n) (m2Guard n) (Hof W.hidden) := by
  have window (c : Ret n) (hw : c ∈ Hof W.hidden)
      (hc : c ∈ sharpSourceBase n (sharpTableN n)) :=
    paid_world_window (by omega) W hidden_eq lower upper hw hc.1
  have hup := BstLean.Part277.world_upper_11883 hn
  have events (c : Ret n) (hw : c ∈ Hof W.hidden)
      (hc : c ∈ sharpSourceBase n (sharpTableN n)) :=
    paid_events_from_window (by omega) W hw hc.1 hup (by norm_num) (window c hw hc)
  have network (c : Ret n) (hw : c ∈ Hof W.hidden)
      (hc : c ∈ sharpSourceBase n (sharpTableN n)) :
      ∃ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) ∧
        Nonempty (NetworkInputs n c (R.table i) R.M R.H R.xi) := by
    obtain ⟨i,hi,hm⟩ := scalarRow_world_cover R (window c hw hc)
    exact ⟨i,hi,⟨BstLean.Part277.network_from_numericsP (by omega) (by omega)
      (N i hi) (scalarRow_cell_subset R i hm)
      (BstLean.Part277.direction_from_exact_windowP hup (by norm_num) (by norm_num)
        (window c hw hc)) (events c hw hc)⟩⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro c hw hc
    exact BstLean.Part252.window_of_theta (by omega) (paperDesignP n) c
      (events c hw hc).scale_pos
      ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans (window c hw hc).1,
        (window c hw hc).2.trans (hup.trans (by norm_num))⟩
  · intro c hw hc
    exact (window c hw hc).2.trans (noiseUpper_le_524 hn)
  · intro c hw hc
    obtain ⟨i,hi,⟨F⟩⟩ := network c hw hc
    refine ⟨BstLean.Part219.directionMoment_mono F.interfaces.direction hM,?_,?_⟩
    · exact ⟨F.interfaces.energy.1.trans hH,F.interfaces.energy.2.1,
        F.interfaces.energy.2.2.trans (pow_le_pow_left₀ F.interfaces.energy.1 hH 32)⟩
    · exact ⟨F.interfaces.parallel.1.trans hxi,F.interfaces.parallel.2.trans
        (sqrt_le_sqrt (div_le_div_of_nonneg_right hxi (Nat.cast_nonneg n)))⟩
  · intro c hw hc
    obtain ⟨i,hi,⟨F⟩⟩ := network c hw hc
    exact F.centre_energy.trans (hE i hi)

noncomputable def row_from_sharp {n : ℕ} (hn : 11883 ≤ n) (hu : n ≤ 12224)
    (F : BstLean.Part264b.FrameData n) (a : AgentParameters)
    (C : MasterCertificate n F.worldParameters a)
    {root : ℝ} (K : SharpRootCertificate n root m2Caps (sharpTableN n) (m2Guard n))
    (L : SharpLocalSupply n m2Caps (sharpTableN n) (m2Guard n) (Hof F.world.hidden))
    (hroot : root ≤ a.root)
    (hbase : F.baseEvent = sharpSourceBase n (sharpTableN n))
    (hframe : F.frameAllowance = a.frame)
    (hpay : (1444145/10^9 : ℝ) + 3/10000 ≤ a.charge)
    (hcompatible : a.charge ≤ C.retainedCharge) : BstLean.Part259.RowInputs n where
  dimension := hn
  worldParameters := F.worldParameters
  agentParameters := a
  world := F.world
  certificate := C
  covarianceEvent := F.covarianceEvent
  cell := F.cell
  caps := F.caps
  covariance_measurable := F.covariance_measurable
  covariance_payment := F.covariance_payment
  baseEvent := F.baseEvent
  base_measurable := F.base_measurable
  baseCharge := 1444145/10^9
  base_payment := by rw [hbase]; exact sharp_base_payment hn hu _
  frame := by
    intro c hc
    simpa only [hframe] using F.frame c hc
  root := by
    intro t c hc
    have hb : c ∈ sharpSourceBase n (sharpTableN n) := by simpa only [hbase] using hc.2.1
    have P := K.inputs t c (L.window c hc.1.1 hb) (L.guard c hc.1.1 hb) hb
      (L.interfaces c hc.1.1 hb) (L.energy_cap c hc.1.1 hb)
    exact ⟨{ P with scalar := P.scalar.trans hroot }⟩
  payment := hpay
  charge_compatible := hcompatible

end BstLean.Part281
