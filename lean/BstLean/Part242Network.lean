import BstLean.Part242Deficit
import BstLean.Part169Var

/-! The FB and SY input distributions are the actual retained stand-in distributions. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

theorem FB_general (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] (p : ℕ) (hp : 1 ≤ p) (hmass : ρ univ ≤ 1)
    {f : A × V → ℝ} {m μ0 g M : ℝ} (hμ : |m| ≤ μ0)
    (hM : ∀ a v, |f (a, v)| ≤ M)
    (hdev : LBound (ρ.prod ν) (2 * p) (fun q => f q - m) g) :
    LBound ρ (2 * p) (latitudeMean ν f) (μ0 + g) := by
  let k := 2 * p
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hμ0 : 0 ≤ μ0 := (abs_nonneg _).trans hμ
  have hm : (ρ.prod ν) univ ≤ 1 := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
    exact hmass
  have hc0 := LBound.const (μ := ρ.prod ν) hk hm hμ0
  have hc : LBound (ρ.prod ν) (k : ℝ≥0∞) (fun _ => m) μ0 :=
    hc0.mono measurable_const (Filter.Eventually.of_forall fun q => by
      simpa only [abs_of_nonneg hμ0] using hμ)
  have hdev' : LBound (ρ.prod ν) (k : ℝ≥0∞) (fun q => f q - m) g := by
    simpa only [k, Nat.cast_mul, Nat.cast_ofNat] using hdev
  have hs := hc.add (by exact_mod_cast hk1) hdev'
  have hf : LBound (ρ.prod ν) (k : ℝ≥0∞) f (μ0 + g) := by
    convert hs using 1
    funext q
    ring
  have h := LBound.ofMoment hk (conditional_moment ρ ν
    (show Even k from ⟨p, by dsimp [k]; omega⟩) (hf.toMoment hk) hM)
  simpa only [k, Nat.cast_mul, Nat.cast_ofNat] using h

variable {n : ℕ}

noncomputable def fLatitude (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) : ℝ :=
  fX c (xLat c (latC (paperDesignP n) c q.1) (unitF53 q.2))

noncomputable def wLatitude (c : Ret n) (q : Ix n × (Fin (n - 1) → ℝ)) : ℝ :=
  wX c (xLat c (latC (paperDesignP n) c q.1) (unitF53 q.2))

lemma measurable_fLatitude (c : Ret n) : Measurable (fLatitude c) :=
  (continuous_fX c).measurable.comp
    (measurable_xLat_comp c ((measurable_latC _ c).comp measurable_fst)
      (measurable_unitF.comp measurable_snd))

lemma measurable_wLatitude (c : Ret n) : Measurable (wLatitude c) :=
  (continuous_wX c).measurable.comp
    (measurable_xLat_comp c ((measurable_latC _ c).comp measurable_fst)
      (measurable_unitF.comp measurable_snd))

lemma latitudeMean_fLatitude (c : Ret n) :
    latitudeMean (stdGauss (Fin (n - 1))) (fLatitude c) = fbR c := by
  funext a
  rw [fbR_eq]
  rfl

lemma latitudeMean_wLatitude (c : Ret n) :
    latitudeMean (stdGauss (Fin (n - 1))) (wLatitude c) = wbR c := rfl

lemma network_Y_eq (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0) (a : Ix n) :
    (dP c).Sb a / (2 / (n : ℝ)) =
      latitudeMean (stdGauss (Fin (n - 1))) (wLatitude c) a -
        latitudeMean (stdGauss (Fin (n - 1))) (fun q => fLatitude c q ^ 2) a := by
  have h := VR_eq hn c hb a
  unfold VR at h
  change wbR c a - fbR c a ^ 2 - (dP c).Sb a / (2 / (n : ℝ)) =
    latitudeMean (stdGauss (Fin (n - 1))) (fun q => fLatitude c q ^ 2) a - fbR c a ^ 2 at h
  rw [latitudeMean_wLatitude]
  linarith

/-- FB uses one retained field and the complete conditional transverse distribution. -/
theorem FB_network (hn : 1 ≤ n) (c : Ret n) (p : ℕ) (hp : 1 ≤ p)
    (K : Set (Ix n)) {m μ0 g : ℝ} (hμ : |m| ≤ μ0)
    (hdev : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) (2 * p)
      (fun q => fLatitude c q - m) g) :
    LBound ((muI n).restrict K) (2 * p) (fbR c) (μ0 + g) := by
  have hb : ∀ a v, |fLatitude c (a, v)| ≤
      sqrt (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / sqrt (n : ℝ) :=
    fun a v => bdd_fX hn c (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v)
  have h := FB_general (muI n) (stdGauss (Fin (n - 1))) p hp (by simp) hμ hb hdev
  rw [latitudeMean_fLatitude] at h
  exact h.restrict K

/-- SY uses the residual scale of the original paper split and no new event. -/
theorem SY_network (hn : 1 ≤ n) (c : Ret n) (hb : normSq (bR c) ≠ 0)
    {K : Set (Ix n)} (hK : MeasurableSet K) {m μ0 g8 H d : ℝ}
    (hμ : |m| ≤ μ0) (hd : 0 < d) (hY0 : d < 1 - μ0 ^ 2)
    (hfloor : ∀ a ∈ K, d ≤ (dP c).Sb a / (2 / (n : ℝ)))
    (hdev : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 8
      (fun q => fLatitude c q - m) g8)
    (hen : LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun q => |sqrt (wLatitude c q) - 1|) H) :
    LBound ((muI n).restrict K) 4 (fun a => 1 / ((dP c).Sb a / (2 / (n : ℝ))))
      (gammaY d (1 - μ0 ^ 2) H μ0 g8) := by
  have hfB : ∀ a v, |fLatitude c (a, v)| ≤
      sqrt (BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / sqrt (n : ℝ) :=
    fun a v => bdd_fX hn c (normSq_xLat_le' hn c (BstLean.Part162.latC_sq_le _ c a) v)
  have hw0 : ∀ q, 0 ≤ wLatitude c q := fun q =>
    div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)
  have hwB : ∀ a v, wLatitude c (a, v) ≤
      BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n := fun a v =>
    (le_abs_self _).trans (bdd_wX c (normSq_xLat_le' hn c
      (BstLean.Part162.latC_sq_le _ c a) v))
  have he4 := hen.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 32) (by simp)
  have hdef := conditional_deficit (muI n) (stdGauss (Fin (n - 1))) (by simp)
    (measurable_fLatitude c) (measurable_wLatitude c) hμ hfB hw0 hwB hdev he4
  have hdef' : LBound (muI n) 4
      (fun a => max 0 ((1 - μ0 ^ 2) - (dP c).Sb a / (2 / (n : ℝ))))
      (2 * H + g8 * (2 * μ0 + g8)) := by
    simpa only [network_Y_eq hn c hb] using hdef
  exact SY hK (by simp) ((dP c).mSb.div_const _) hd hY0 hfloor hdef'

end BstLean.Part242
