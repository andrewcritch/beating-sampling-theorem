import BstLean.Part248Network
import BstLean.Part222MassOrders

/-! The same direction and energy interfaces supply D1 on the actual latitude distribution. -/
namespace BstLean.Part248
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part242 BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

lemma stand_norm_eq (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) {f : (Fin n → ℝ) → ℝ} (mf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun q : Ix n × (Fin (n - 1) → ℝ) =>
      f (xLat c (latC D c q.1) (unitF53 q.2))) p
      ((muI n).prod (stdGauss (Fin (n - 1)))) =
    eLpNorm (fun ξ => f (sphPt (c.1.2 + D.tau0 c • ξ))) p (stdGauss (Fin n)) := by
  have ml : Measurable (fun q : Ix n × (Fin (n - 1) → ℝ) =>
      xLat c (latC D c q.1) (unitF53 q.2)) :=
    measurable_xLat_comp c ((measurable_latC _ c).comp measurable_fst)
      (measurable_unitF.comp measurable_snd)
  have ms : Measurable (fun ξ => sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_id.const_smul (D.tau0 c)))
  have eq : nuStand D c = ((muI n).prod (stdGauss (Fin (n - 1)))).map
      (fun q => xLat c (latC D c q.1) (unitF53 q.2)) :=
    nuStand_latitude hn D c hc hτ
  calc
    _ = eLpNorm f p (nuStand D c) := by
      rw [eq]
      exact (eLpNorm_map_measure mf.aestronglyMeasurable ml.aemeasurable).symm
    _ = _ := eLpNorm_map_measure mf.aestronglyMeasurable ms.aemeasurable

noncomputable def fullMean (c : Ret n) : ℝ :=
  ∫ ξ, centreCoordinate (paperDesignP n) c ξ ∂stdGauss (Fin n)

theorem direction_latitude (hn : 50 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    {p : ℕ} (hp : 1 ≤ p) (hp12 : p ≤ 12) {M : ℝ}
    (hdir : DirectionMoment (paperDesignP n) c M) :
    LBound ((muI n).prod (stdGauss (Fin (n - 1)))) ((2 * p : ℕ) : ℝ≥0∞)
      (fun q => fLatitude c q - fullMean c)
      (BstLean.Part195.rotationConstant p * sqrt (M / n)) := by
  obtain ⟨hi, hm⟩ := BstLean.Part222.directional_moment_even hn hp hp12
    (paperDesignP n) c hτ hb hdir
  have mφ : Measurable (fun ξ => centreCoordinate (paperDesignP n) c ξ - fullMean c) :=
    (measurable_centreCoordinate _ c).sub measurable_const
  have hmn : 0 ≤ M / (n : ℝ) := div_nonneg hdir.1 (Nat.cast_nonneg _)
  have he : (BstLean.Part195.rotationConstant p * sqrt (M / n)) ^ (2 * p) =
      BstLean.Part195.rotationConstant p ^ (2 * p) * (M / n) ^ p := by
    simp only [mul_pow, pow_mul, sq_sqrt hmn]
  have hg : LBound (stdGauss (Fin n)) ((2 * p : ℕ) : ℝ≥0∞)
      (fun ξ => centreCoordinate (paperDesignP n) c ξ - fullMean c)
      (BstLean.Part195.rotationConstant p * sqrt (M / n)) := by
    apply LBound.ofMoment (by omega : 2 * p ≠ 0)
    refine ⟨mφ, mul_nonneg (BstLean.Part195.rotationConstant_nonneg p) (sqrt_nonneg _), ?_⟩
    dsimp only [fullMean]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ξ => pow_nonneg (abs_nonneg _) _), he]
    exact ENNReal.ofReal_le_ofReal hm
  refine ⟨(measurable_fLatitude c).sub measurable_const, hg.nonneg, ?_⟩
  have eq := stand_norm_eq (by omega) (paperDesignP n) c hc hτ
    ((continuous_fX c).measurable.sub_const (fullMean c)) ((2 * p : ℕ) : ℝ≥0∞)
  have ef : (fun ξ => fX c (sphPt (c.1.2 + (paperDesignP n).tau0 c • ξ)) - fullMean c) =
      fun ξ => centreCoordinate (paperDesignP n) c ξ - fullMean c := rfl
  change eLpNorm (fun q => fLatitude c q - fullMean c) _ _ = _ at eq
  rw [eq, ef]
  exact hg.bound

theorem energy_latitude (hn : 2 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < (paperDesignP n).tau0 c) {H : ℝ}
    (hen : EnergyMoment (paperDesignP n) c H) :
    LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun q => |sqrt (wLatitude c q) - 1|) H := by
  have mg : Measurable (fun ξ => |sqrt (inputEnergy (paperDesignP n) c ξ) - 1|) :=
    ((measurable_inputEnergy _ c).sqrt.sub measurable_const).abs
  have hi : Integrable (fun ξ => |sqrt (inputEnergy (paperDesignP n) c ξ) - 1| ^ 32)
      (stdGauss (Fin n)) := by
    simpa only [show (32 : ℕ) = 2 * 16 from rfl, pow_abs_two_mul] using hen.2.1
  have hg : LBound (stdGauss (Fin n)) 32
      (fun ξ => |sqrt (inputEnergy (paperDesignP n) c ξ) - 1|) H := by
    apply LBound.ofMoment (by norm_num : (32 : ℕ) ≠ 0)
    refine ⟨mg, hen.1, ?_⟩
    simp only [abs_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun ξ => pow_nonneg (abs_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [show (32 : ℕ) = 2 * 16 from rfl, pow_abs_two_mul] using hen.2.2
  refine ⟨((measurable_wLatitude c).sqrt.sub measurable_const).abs, hg.nonneg, ?_⟩
  have eq := stand_norm_eq hn (paperDesignP n) c hc hτ
    (f := fun x => |sqrt (wX c x) - 1|)
    (((continuous_wX c).measurable.sqrt.sub measurable_const).abs) (32 : ℝ≥0∞)
  change eLpNorm (fun q => |sqrt (wLatitude c q) - 1|) _ _ = _ at eq
  rw [eq]
  exact hg.bound

/-- D1 now uses the direction, energy and parallel interfaces from S17/S18 directly.
No extra retained event or independent weights enter this transfer. -/
theorem D1_from_WF (hn : 50 ≤ n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < (paperDesignP n).tau0 c) (hb : 0 < normSq (bR c))
    {M H xi E : ℝ} (hI : WFInterfaces (paperDesignP n) c M H xi)
    (hE : centreEnergy (paperDesignP n) c ≤ E) :
    DeficitOrders (muI n) (fun a => (dP c).Sb a / (2 / (n : ℝ)))
      (1 - (sqrt E + sqrt (xi / n)) ^ 2)
      (deficitConstant 4 H (sqrt E + sqrt (xi / n)) (sqrt (M / n)))
      (deficitConstant 8 H (sqrt E + sqrt (xi / n)) (sqrt (M / n)))
      (deficitConstant 12 H (sqrt E + sqrt (xi / n)) (sqrt (M / n))) := by
  have hμ : |fullMean c| ≤ sqrt E + sqrt (xi / n) := by
    have hlo := (abs_le.mp hI.parallel.2).1
    have hhi := (abs_le.mp hI.parallel.2).2
    have hs := sqrt_le_sqrt hE
    have hs0 := sqrt_nonneg (centreEnergy (paperDesignP n) c)
    apply abs_le.mpr
    constructor <;> dsimp [fullMean] <;> linarith [sqrt_nonneg E, sqrt_nonneg (xi / n)]
  apply D1_network_orders (by omega) c hb.ne' hμ ?_ ?_ (energy_latitude (by omega) c hc hτ hI.energy)
  · intro q hq
    rcases hq with rfl | rfl | rfl
    · exact direction_latitude hn c hc hτ hb (p := 2) (by omega) (by omega) hI.direction
    · exact direction_latitude hn c hc hτ hb (p := 4) (by omega) (by omega) hI.direction
    · exact direction_latitude hn c hc hτ hb (p := 6) (by omega) (by omega) hI.direction
  · intro q hq
    rcases hq with rfl | rfl | rfl
    · exact direction_latitude hn c hc hτ hb (p := 4) (by omega) (by omega) hI.direction
    · exact direction_latitude hn c hc hτ hb (p := 8) (by omega) (by omega) hI.direction
    · exact direction_latitude hn c hc hτ hb (p := 12) (by omega) (by omega) hI.direction

#print axioms stand_norm_eq
#print axioms direction_latitude
#print axioms energy_latitude
#print axioms D1_from_WF
end BstLean.Part248
