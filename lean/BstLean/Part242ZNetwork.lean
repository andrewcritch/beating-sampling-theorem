import BstLean.Part242Network
import BstLean.Part242SY2
import BstLean.Part242MomentSupply

/-! The SY2 field is the actual normalized residual standard deviation. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)
open BstLean.Part162 (sgA)

variable {n : ℕ}

noncomputable def zLatitude (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) : ℝ :=
  sgA (paperDesignP n) c q.1 q.2 / sqrt (2 / (n : ℝ))

lemma measurable_zLatitude (c : Ret n) : Measurable (zLatitude c) :=
  (BstLean.Part162.measurable_sgA _ c).div_const _

lemma zLatitude_nonneg (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) :
    0 ≤ zLatitude c q := div_nonneg (BstLean.Part162.sgA_nonneg _ c _ _) (sqrt_nonneg _)

lemma zLatitude_sq_div (hn : 1 ≤ n) (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) :
    zLatitude c q ^ 2 = sA (paperDesignP n) c q.1 q.2 / (2 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hγ : (0 : ℝ) ≤ 2 / n := by positivity
  unfold zLatitude
  rw [div_pow, sq_sqrt hγ, BstLean.Part162.sA_eq]

lemma zLatitude_sq (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    (q : Ix n × (Fin (n - 1) → ℝ)) :
    zLatitude c q ^ 2 = wLatitude c q - fLatitude c q ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [zLatitude_sq_div hn c q]
  unfold sA sigX
  rw [paperDesignP_bA, BstLean.Part169.sA_eq (by omega) hb]
  change (2 / (n : ℝ) * (wLatitude c q - fLatitude c q ^ 2)) / (2 / (n : ℝ)) = _
  field_simp

lemma latitudeMean_zLatitude_sq (hn : 1 ≤ n) (c : Ret n) (a : Ix n) :
    latitudeMean (stdGauss (Fin (n - 1))) (fun q => zLatitude c q ^ 2) a =
      (dP c).Sb a / (2 / (n : ℝ)) := by
  change (∫ v, zLatitude c (a, v) ^ 2 ∂stdGauss (Fin (n - 1))) =
    (∫ v, sA (paperDesignP n) c a v ∂stdGauss (Fin (n - 1))) / (2 / (n : ℝ))
  rw [← integral_div]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => zLatitude_sq_div hn c (a, v))

lemma bounded_zLatitude (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0) :
    ∃ M, ∀ a v, |zLatitude c (a, v)| ≤ M := by
  refine ⟨sqrt (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n), ?_⟩
  intro a v
  have hsq : zLatitude c (a, v) ^ 2 ≤
      BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n := by
    rw [zLatitude_sq hn c hb]
    have hw := bdd_wX c (normSq_xLat_le' hn c
      (BstLean.Part162.latC_sq_le (paperDesignP n) c a) v)
    change |wLatitude c (a, v)| ≤ _ at hw
    have hle := le_abs_self (wLatitude c (a, v))
    nlinarith [sq_nonneg (fLatitude c (a, v))]
  rw [abs_of_nonneg (zLatitude_nonneg c (a, v)), ← sqrt_sq (zLatitude_nonneg c (a, v))]
  exact sqrt_le_sqrt hsq

theorem SY2_network (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    (split : SplitData n) {m μ0 g8 H dl τ8 V : ℝ}
    (hμ : |m| ≤ μ0) (hdl : 0 < dl) (hY0 : dl < 1 - μ0 ^ 2)
    (hcut : ∀ a ∈ keptIx (paperDesignP n) c split, ∀ v ∈ slice split a,
      sqrt dl ≤ zLatitude c (a, v))
    (hdev : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 8
      (fun q => fLatitude c q - m) g8)
    (hen : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun q => |sqrt (wLatitude c q) - 1|) H)
    (hzcent : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 8
      (fun q => zLatitude c q - latitudeMean (stdGauss (Fin (n - 1))) (zLatitude c) q.1) τ8)
    (hvar : LBound (muI n) 4
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v))) V) :
    LBound ((muI n).restrict (keptIx (paperDesignP n) c split)) 4
      (fun a => 1 / goodMeanSq (stdGauss (Fin (n - 1))) (slice split a)
        (fun v => zLatitude c (a, v)))
      (gMix dl (1 - μ0 ^ 2) H μ0 g8 split.eta τ8 V) := by
  let ν := stdGauss (Fin (n - 1))
  let K := keptIx (paperDesignP n) c split
  have mK : MeasurableSet K :=
    measurableSet_keptSet _ split.mgood (measurableSet_bulkIx _ c) _
  obtain ⟨M, hM⟩ := bounded_zLatitude hn c hb
  have hgood : ∀ a ∈ K, 1 - split.eta ≤ ν.real {v | (a, v) ∈ split.good} := by
    intro a ha
    have ms := measurableSet_slice split a
    have hcomp := measureReal_compl (μ := ν) ms
    rw [probReal_univ] at hcomp
    change removed ν split.good a = 1 - ν.real {v | (a, v) ∈ split.good} at hcomp
    have hβ := ha.2
    linarith
  have hfloor : ∀ a ∈ K, dl ≤ goodMeanSq ν {v | (a, v) ∈ split.good} (fun v => zLatitude c (a, v)) := by
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
  have hz : LBound ((muI n).prod ν) 8 (zLatitude c) (1 + H) :=
    z_norm_from_energy _ (by simp [ν]) (measurable_zLatitude c) (zLatitude_nonneg c)
      (fun q => by rw [zLatitude_sq hn c hb]; nlinarith [sq_nonneg (fLatitude c q)]) hen
  have hfB : ∀ a v, |fLatitude c (a, v)| ≤
      sqrt (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / sqrt (n : ℝ) :=
    fun a v => bdd_fX hn c (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v)
  have hw0 : ∀ q, 0 ≤ wLatitude c q := fun q => div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)
  have hwB : ∀ a v, wLatitude c (a, v) ≤
      BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n := fun a v =>
    (le_abs_self _).trans (bdd_wX c (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v))
  have he4 := hen.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 32) (by simp)
  have hbase := conditional_deficit (muI n) ν (by simp) (measurable_fLatitude c)
    (measurable_wLatitude c) hμ hfB hw0 hwB hdev he4
  have hbase' : LBound (muI n) 4
      (fun a => max 0 ((1 - μ0 ^ 2) - latitudeMean ν (fun q => zLatitude c q ^ 2) a))
      (2 * H + g8 * (2 * μ0 + g8)) := by
    simpa only [ν, ← network_Y_eq hn c hb, latitudeMean_zLatitude_sq hn c] using hbase
  exact SY2_kept (muI n) ν (by simp) mK split.mgood split.eta_pos.le split.eta_lt
    hdl hY0 hgood hM hz hzcent hvar hbase' hfloor

end BstLean.Part242
