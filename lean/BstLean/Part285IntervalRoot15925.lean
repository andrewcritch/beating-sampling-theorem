import BstLean.Part285IntervalSharp
import BstLean.Part285IntervalBands
import BstLean.Part285IntervalHQ15925

/-! Sharp root certificate for every integer in 15925–16199. No per-row proof data. -/
namespace BstLean.Part285.Interval.Band15925
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part252 BstLean.Part275 BstLean.Part280
open BstLean.Part285.Interval
open BstLean.Part150 (c1F c2F)
variable {n : ℕ} [Fact (15925 ≤ n ∧ n ≤ 16199)]

local instance globalBand : Fact (12000 ≤ n ∧ n ≤ 16199) := by
  have h : 15925 ≤ n ∧ n ≤ 16199 := Fact.out
  exact ⟨by omega⟩

noncomputable def aw : ℝ := (158445747 / 1000000000)
noncomputable def af : ℝ := (8370901 / 156250000)
noncomputable def root : ℝ := (5280737 / 1000000000)
noncomputable def requirement : ℝ := (1166257 / 200000000)
noncomputable def tableCap : ℝ := (1899 / 10000000)
noncomputable def worldRadius : ℝ := (19810049 / 5000000000)
noncomputable def tauPlus : ℝ := (2565034431 / 10000000000)
noncomputable def tauMinus : ℝ := (-6549829261 / 10000000000)

theorem end_parameters : 0 < worldRadius ∧ 0 < tauPlus ∧ tauMinus < 0 := by
  norm_num [worldRadius, tauPlus, tauMinus]

theorem root_le_requirement : root ≤ requirement := by norm_num [root, requirement]

theorem dimension : 15925 ≤ n ∧ n ≤ 16199 := Fact.out

theorem sqrt_bounds : ((63097147 / 500000) : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) ≤ (127275293 / 1000000) := by
  have hl : (15925 : ℝ) ≤ n := by exact_mod_cast (dimension (n := n)).1
  have hu : (n : ℝ) ≤ 16199 := by exact_mod_cast (dimension (n := n)).2
  exact ⟨le_sqrt_of_sq_le (by linarith), sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩⟩

theorem rule_size : ((2009643 / 1) : ℝ) ≤ Jz n ∧ 1000000 ≤ Jz n := by
  have hn := dimension (n := n)
  have hl : (15925 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hr := (sqrt_bounds (n := n)).1
  have hx : (n : ℝ) * √(n : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    rw [← rpow_three_halves]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have : (1 : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by nlinarith
    exact_mod_cast this
  have he : (Jz n : ℝ) = (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    rw [Nat.cast_sub hc]
    simp
  have hh : ((2009643 / 1) : ℝ) ≤ Jz n := by rw [he]; nlinarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz n by linarith)⟩

theorem grid_width : DeltaP n ≤ ((8649151 / 1000000000000000) : ℝ) := by
  have hl : (15925 : ℝ) ≤ n := by exact_mod_cast (dimension (n := n)).1
  have hu : (n : ℝ) ≤ 16199 := by exact_mod_cast (dimension (n := n)).2
  have hs : √(55 / 100 / (n : ℝ)) ≤ (1469202413 / 250000000000) :=
    sqrt_le_iff.mpr ⟨by norm_num, by interval_num⟩
  unfold DeltaP
  have hp : (0 : ℝ) < n := by linarith
  have h := div_le_div₀ (by norm_num : (0 : ℝ) ≤ 12 * (1469202413 / 250000000000))
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 12))
    (by norm_num : (0 : ℝ) < 512 * 15925)
    (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 512))
  exact h.trans (by norm_num)

noncomputable def numerics : SharpNumerics n aw af := by
  have hn := dimension (n := n)
  have hl : (15925 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hu : (n : ℝ) ≤ 16199 := by exact_mod_cast hn.2
  have hp : (0 : ℝ) < n := by linarith
  have hsq := sqrt_bounds (n := n)
  have hbulk := bulk_radius (n := n) (by omega)
  have hb0 : 0 < √(qB n) := by linarith
  have hs0 : 0 < √(n : ℝ) := sqrt_pos.mpr hp
  have hJ := rule_size (n := n)
  refine {
    dimension := ⟨by omega, by omega⟩
    O := (184389 / 1000)
    sigma := (16515381 / 1000000000)
    er := (3205363 / 1000000000)
    eg := (760527 / 200000000)
    lr := (3219257 / 1000000000)
    lg := (91961 / 200000000)
    operator_pos := by norm_num
    sigma_pos := by norm_num
    operator := ?_
    variance := ?_
    location_grid := ?_
    energy_grid := ?_
    location_rule := ?_
    energy_rule := ?_
    location_total := ?_
    energy_total := ?_ }
  · have hs : √(2 / (n : ℝ)) ≤ (5603318147 / 500000000000) := sqrt_le_iff.mpr
      ⟨by norm_num, by interval_num⟩
    unfold firstOp
    exact (mul_le_mul hs (by linarith : (n : ℝ) + 2 * √n ≤ 16199 + 2 * ((127275293 / 1000000)))
      (by positivity) (by norm_num)).trans (by norm_num)
  · interval_num
  · intro d hd
    have hd' := hd.trans (grid_width (n := n))
    have hden : ((63097147 / 500000) : ℝ) * (63 / 100) ≤ √(n : ℝ) * √(qB n) :=
      mul_le_mul hsq.1 hbulk (by norm_num) (sqrt_nonneg _)
    rw [mul_div_assoc', div_le_iff₀ (mul_pos hs0 hb0)]
    have hmul := mul_le_mul_of_nonneg_left hd' hp.le
    have hupper : (n : ℝ) * ((8649151 / 1000000000000000)) ≤ 16199 * ((8649151 / 1000000000000000)) :=
      mul_le_mul_of_nonneg_right hu (by norm_num)
    nlinarith
  · intro d hd
    have hd' := hd.trans (grid_width (n := n))
    have hden : (15925 : ℝ) * (63 / 100) ≤ n * √(qB n) :=
      mul_le_mul hl hbulk (by norm_num) hp.le
    rw [mul_div_assoc', div_le_iff₀ (mul_pos hp hb0)]
    have hmul := mul_le_mul_of_nonneg_left hd' hp.le
    have hupper : (n : ℝ) * ((8649151 / 1000000000000000)) ≤ 16199 * ((8649151 / 1000000000000000)) :=
      mul_le_mul_of_nonneg_right hu (by norm_num)
    nlinarith
  · have hC := BstLean.Part169.c1F_le hJ.2
    have hC0 := BstLean.Part169.c1F_nonneg (Jz n)
    have hm := mul_le_mul hsq.2 hC hC0 (by norm_num : (0 : ℝ) ≤ (127275293 / 1000000))
    have hm2 := mul_le_mul hu hm (by positivity) (by positivity)
    rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz n)]
    nlinarith
  · have hC := BstLean.Part169.c2F_le hJ.2
    have hnn : (n : ℝ) ^ 2 ≤ (16199 : ℝ) ^ 2 := pow_le_pow_left₀ hp.le hu 2
    have hm := mul_le_mul hnn hC (BstLean.Part169.c2F_nonneg (Jz n)) (by positivity)
    rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz n)]
    nlinarith
  · norm_num [af, BstLean.Part276.tableF]
  · norm_num [aw, BstLean.Part276.tableW]

theorem table_charge : (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ tableCap := by
  have hn := dimension (n := n)
  refine (sharpTable_band_charge (by omega) (by omega)).trans ?_
  unfold bandTablePrice tableCap
  split_ifs <;> first | omega | norm_num

theorem bias_bound : BstLean.Part241.biasRoot n PilotA.chi PilotA.biasFloor PilotA.epsilon
    PilotA.varianceMax aw af PilotA.locationNorm PilotA.varianceNorm ≤ (3541127 / 1000000000) := by
  have hn := dimension (n := n)
  refine sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
  refine (BstLean.Part285.squaredPrice_band (a := 15925) (by norm_num) hn.1
    (by norm_num [PilotA.chi])
    (by norm_num [PilotA.biasFloor, PilotA.eta, PilotA.mixtureFloor])
    (by norm_num [PilotA.epsilon])
    (by norm_num [PilotA.epsilon, PilotA.varianceMax, PilotA.biasFloor, PilotA.eta, PilotA.mixtureFloor])
    (by norm_num [PilotA.locationNorm]) (by norm_num [PilotA.varianceNorm])
    (by norm_num [aw]) (le_refl _) (by norm_num [af]) (le_refl _)).trans ?_
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass,
    PilotA.chi, PilotA.biasFloor, PilotA.eta, PilotA.mixtureFloor, PilotA.epsilon,
    PilotA.varianceMax, PilotA.locationNorm, PilotA.varianceNorm, aw, af]

noncomputable def certificate :
    SharpRootCertificate n root (intervalCaps tableCap) (sharpTableN n) (m2Guard n) :=
  intervalCertificate numerics (by norm_num [aw]) (by norm_num [aw, PilotA.energyError])
    (by norm_num [af]) (by norm_num [af, PilotA.locationError]) table_charge bias_bound
    (by norm_num [root] : ((173959 / 100000000) : ℝ) + ((3541127 / 1000000000)) + 1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ root)
    (fun t c hw ha hp hm => by
      have hm' : BstLean.Part285.Interval.HQ15925.LowResidualMass c := by
        simpa [PilotLowMass, BstLean.Part285.Interval.HQ15925.LowResidualMass, BstLean.Part285.Interval.HQ15925.rowSigma] using hm
      simpa [pilotSplit, BstLean.Part285.Interval.HQ15925.hqSplit] using BstLean.Part285.Interval.HQ15925.hq_fluctuation t hw ha hp hm')

/-- The same root with the smaller dimension-dependent table payment. -/
noncomputable def certificate_per_n :
    SharpRootCertificate n root (intervalCaps (smallerTablePrice n)) (sharpTableN n) (m2Guard n) where
  dimension := certificate.dimension
  table_measurable := certificate.table_measurable
  source_charge := certificate.source_charge
  table_payment := sharpTable_smaller_charge (by have := dimension (n := n); omega)
    (by have := dimension (n := n); omega)
  inputs := certificate.inputs

end BstLean.Part285.Interval.Band15925
