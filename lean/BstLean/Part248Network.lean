import BstLean.Part248Junction
import BstLean.Part242ZNetwork
import BstLean.Part195Rotation

/-! D1 and R apply to the original network residual scale. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242 BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def deficitConstant (q : ℕ) (H μ0 s : ℝ) : ℝ :=
  2 * H + 2 * μ0 * (BstLean.Part195.rotationConstant (q / 2) * s) +
    (BstLean.Part195.rotationConstant q * s) ^ 2

def deficitOrder (q : ℕ) : Prop := q = 4 ∨ q = 8 ∨ q = 12

variable {n : ℕ}

/-- D1 uses actual full latitude moments at orders q and 2*q.
The directional and energy event supplies remain explicit inputs. -/
theorem D1_network (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    {q : ℕ} (hq : deficitOrder q) {m μ0 s H : ℝ} (hμ : |m| ≤ μ0)
    (hphiQ : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) q
      (fun x => fLatitude c x - m) (BstLean.Part195.rotationConstant (q / 2) * s))
    (hphi2Q : LBound ((muI n).prod (stdGauss (Fin (n - 1))))
      ((2 * q : ℕ) : ℝ≥0∞) (fun x => fLatitude c x - m)
      (BstLean.Part195.rotationConstant q * s))
    (hen : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun x => |sqrt (wLatitude c x) - 1|) H) :
    LBound (muI n) q
      (fun a => max 0 ((1 - μ0 ^ 2) - (dP c).Sb a / (2 / (n : ℝ))))
      (deficitConstant q H μ0 s) := by
  have hq1 : 1 ≤ q := by rcases hq with rfl | rfl | rfl <;> omega
  have hq32 : q ≤ 32 := by rcases hq with rfl | rfl | rfl <;> omega
  have he : Even q := by rcases hq with rfl | rfl | rfl <;> decide
  have hfB : ∀ a v, |fLatitude c (a, v)| ≤
      sqrt (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / sqrt (n : ℝ) :=
    fun a v => bdd_fX hn c
      (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v)
  have hw0 : ∀ x, 0 ≤ wLatitude c x := fun x =>
    div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)
  have hwB : ∀ a v, wLatitude c (a, v) ≤
      BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n := fun a v =>
    (le_abs_self _).trans (bdd_wX c
      (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v))
  have heQ := hen.lower (by exact_mod_cast (by omega : q ≠ 0)) (by norm_num)
    (by exact_mod_cast hq32 : (q : ℝ≥0∞) ≤ 32) (by simp)
  have h := D1_from_full (muI n) (stdGauss (Fin (n - 1))) hq1 he
    (measurable_fLatitude c) (measurable_wLatitude c) hμ hfB hw0 hwB hphiQ hphi2Q heQ
  simpa only [network_Y_eq hn c hb, deficitConstant] using h

theorem D1_network_orders (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    {m μ0 s H : ℝ} (hμ : |m| ≤ μ0)
    (hphiQ : ∀ q, deficitOrder q →
      LBound ((muI n).prod (stdGauss (Fin (n - 1)))) q
        (fun x => fLatitude c x - m) (BstLean.Part195.rotationConstant (q / 2) * s))
    (hphi2Q : ∀ q, deficitOrder q →
      LBound ((muI n).prod (stdGauss (Fin (n - 1)))) ((2 * q : ℕ) : ℝ≥0∞)
        (fun x => fLatitude c x - m) (BstLean.Part195.rotationConstant q * s))
    (hen : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun x => |sqrt (wLatitude c x) - 1|) H) :
    DeficitOrders (muI n) (fun a => (dP c).Sb a / (2 / (n : ℝ))) (1 - μ0 ^ 2)
      (deficitConstant 4 H μ0 s) (deficitConstant 8 H μ0 s) (deficitConstant 12 H μ0 s) := by
  have hf q (hq : deficitOrder q) := D1_network hn c hb hq hμ (hphiQ q hq) (hphi2Q q hq) hen
  exact ⟨hf 4 (Or.inl rfl), hf 8 (Or.inr (Or.inl rfl)), hf 12 (Or.inr (Or.inr rfl))⟩

/-- The bias reciprocal enters the existing SY interface with its own floor. -/
theorem R_bias_network (c : Ret n) {K : Set (Ix n)} (hK : MeasurableSet K)
    {η dl μ0 X4 X8 X12 : ℝ} (hη : η < 1) (hdl : 0 < dl) (hY0 : 0 < 1 - μ0 ^ 2)
    (hfloor : ∀ a ∈ K, (1 - η) * dl ≤ (dP c).Sb a / (2 / (n : ℝ)))
    (hdef : DeficitOrders (muI n) (fun a => (dP c).Sb a / (2 / (n : ℝ)))
      (1 - μ0 ^ 2) X4 X8 X12) :
    LBound ((muI n).restrict K) 4 (fun a => 1 / ((dP c).Sb a / (2 / (n : ℝ))))
      (bestBound ((1 - η) * dl) (1 - μ0 ^ 2) X4 X8 X12) :=
  R_best hK (by simp) ((dP c).mSb.div_const _) (by positivity) hY0 hfloor hdef

/-- The mixture reciprocal retains the original good transverse restriction and floor dl. -/
theorem R_mixture_network (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    (split : SplitData n) {μ0 H dl X4 X8 X12 τ8 τ16 τ24 V : ℝ}
    (hdl : 0 < dl) (hY0 : 0 < 1 - μ0 ^ 2)
    (hcut : ∀ a ∈ keptIx (paperDesignP n) c split, ∀ v ∈ slice split a,
      sqrt dl ≤ zLatitude c (a, v))
    (hdef : DeficitOrders (muI n) (fun a => (dP c).Sb a / (2 / (n : ℝ)))
      (1 - μ0 ^ 2) X4 X8 X12)
    (hen : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun x => |sqrt (wLatitude c x) - 1|) H)
    (hc8 : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 8
      (fun q => zLatitude c q - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) q.1) τ8)
    (hc16 : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 16
      (fun q => zLatitude c q - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) q.1) τ16)
    (hc24 : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 24
      (fun q => zLatitude c q - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) q.1) τ24)
    (hvar : LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1)))
        (fun v => zLatitude c (a, v))) V) :
    LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 4
      (fun a => 1 / goodMeanSq (stdGauss (Fin (n - 1))) (slice split a)
        (fun v => zLatitude c (a, v)))
      (bestBound dl (1 - μ0 ^ 2)
        (mixtureConstant X4 H τ8 split.eta V) (mixtureConstant X8 H τ16 split.eta V)
        (mixtureConstant X12 H τ24 split.eta V)) := by
  let ν := stdGauss (Fin (n - 1))
  let K := keptIx (paperDesignP n) c split
  have mK : MeasurableSet K :=
    measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  obtain ⟨M, hM⟩ := bounded_zLatitude hn c hb
  have hz24 : LBound ((muI n).prod ν) 24 (zLatitude c) (1 + H) :=
    z_norm_order _ (by simp [ν]) (q := 24) (by omega) (by omega)
      (measurable_zLatitude c) (zLatitude_nonneg c)
      (fun q => by rw [zLatitude_sq hn c hb]; nlinarith [sq_nonneg (fLatitude c q)]) hen
  have hgood : ∀ a ∈ K, 1 - split.eta ≤ ν.real {v | (a, v) ∈ split.good} := by
    intro a ha
    have ms := measurableSet_slice split a
    have hcomp := measureReal_compl (μ := ν) ms
    rw [probReal_univ] at hcomp
    change removed ν split.good a = 1 - ν.real {v | (a, v) ∈ split.good} at hcomp
    have hβ := ha.2
    linarith
  have hfloor : ∀ a ∈ K, dl ≤
      goodMeanSq ν {v | (a, v) ∈ split.good} (fun v => zLatitude c (a, v)) := by
    intro a ha
    have hm : 0 < ν.real {v | (a, v) ∈ split.good} := by
      have hh := hgood a ha
      have he := split.eta_lt
      linarith
    have mzA : Measurable (fun v => zLatitude c (a, v)) :=
      (measurable_zLatitude c).comp measurable_prodMk_left
    have hh := good_mean_sq_lower ν (split.mgood.preimage measurable_prodMk_left) hm
      mzA (hM a) (sqrt_nonneg dl) (hcut a ha)
    simpa only [sq_sqrt hdl.le, Set.preimage] using hh
  have hbase : DeficitOrders (muI n) (latitudeMean ν (fun q => zLatitude c q ^ 2))
      (1 - μ0 ^ 2) X4 X8 X12 := by
    have eq : latitudeMean ν (fun q => zLatitude c q ^ 2) =
        fun a => (dP c).Sb a / (2 / (n : ℝ)) := by
      funext a
      exact latitudeMean_zLatitude_sq hn c a
    rw [eq]
    exact hdef
  have hmix := mixture_orders (muI n) ν (by simp) mK split.mgood split.eta_pos.le
    split.eta_lt hgood hM hz24 hc8 hc16 hc24 hvar hbase
  have mz : Measurable
      (fun a => goodMeanSq ν {v | (a, v) ∈ split.good} (fun v => zLatitude c (a, v))) := by
    have eq : (fun a => goodMeanSq ν {v | (a, v) ∈ split.good}
        (fun v => zLatitude c (a, v))) =
        fun a => BstLean.Part161.goodMean ν split.good (zLatitude c) a ^ 2 := by
      funext a
      exact goodMeanSq_eq_goodMean ν split.mgood a
    rw [eq]
    exact (BstLean.Part161.measurable_goodMean ν split.mgood (measurable_zLatitude c)).pow_const 2
  exact R_best_kept mK (by simp) mz hdl hY0 hfloor hmix

#print axioms D1_network
#print axioms D1_network_orders
#print axioms R_bias_network
#print axioms R_mixture_network
end BstLean.Part248
