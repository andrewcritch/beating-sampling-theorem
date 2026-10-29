import BstLean.Part252Pass
import BstLean.Part242Network
import BstLean.Part222EnergyEvent

/-! The existing energy event supplies the full conditional location moments.
The latitude measure is the original stand-in measure. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part242
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

theorem latitude_integral_eq (hn : 2 ≤ n) (D : Design n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < D.tau0 c) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) :
    (∫ p : Ix n × (Fin (n - 1) → ℝ),
      F (xLat c (latC D c p.1) (unitF53 p.2))
        ∂(muI n).prod (stdGauss (Fin (n - 1)))) =
    ∫ ξ, F (sphPt (c.1.2 + D.tau0 c • ξ)) ∂stdGauss (Fin n) := by
  have mx := measurable_xLat_comp c ((measurable_latC D c).comp measurable_fst)
    (measurable_unitF.comp measurable_snd)
  have ms : Measurable (fun ξ : Fin n → ℝ =>
      sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp
      (measurable_const.add (measurable_const_smul (D.tau0 c)))
  change (∫ p, F ((fun x => xLat c ((latC D c ∘ Prod.fst) x)
    ((unitF53 ∘ Prod.snd) x)) p) ∂(muI n).prod (stdGauss (Fin (n - 1)))) = _
  rw [← integral_map mx.aemeasurable hF.aestronglyMeasurable]
  change (∫ x, F x ∂(((ProbabilityTheory.gaussianReal 0 1).prod
    (stdGauss (Fin (n - 1)))).prod (stdGauss (Fin (n - 1)))).map
      (fun p => xLat c (latitude (√(normSq c.1.2)) (D.tau0 c) p.1) (unitF53 p.2))) = _
  rw [← nuStand_latitude hn D c hc hτ]
  exact integral_map ms.aemeasurable hF.aestronglyMeasurable

theorem energy_latitude_norm (hn : 2 ≤ n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) {H : ℝ}
    (he : BstLean.Part188.EnergyMoment (paperDesignP n) c H) :
    LBound ((muI n).prod (stdGauss (Fin (n - 1)))) 32
      (fun p => |√(wLatitude c p) - 1|) H := by
  let F := fun x : Fin n → ℝ => (√(wX c x) - 1) ^ 32
  have mf : Measurable F := ((continuous_wX c).measurable.sqrt.sub_const 1).pow_const 32
  have eq := latitude_integral_eq hn (paperDesignP n) c hc hτ mf
  have hb : ∫ p : Ix n × (Fin (n - 1) → ℝ),
      (√(wLatitude c p) - 1) ^ 32 ∂(muI n).prod (stdGauss (Fin (n - 1))) ≤ H ^ 32 :=
    eq.trans_le he.2.2
  have mdev := ((measurable_wLatitude c).sqrt.sub_const 1).abs
  have hi : Integrable (fun p : Ix n × (Fin (n - 1) → ℝ) =>
      (√(wLatitude c p) - 1) ^ 32) ((muI n).prod (stdGauss (Fin (n - 1)))) := by
    let B := BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c) / n
    apply Integrable.of_bound
      ((((measurable_wLatitude c).sqrt.sub_const 1).pow_const 32).aestronglyMeasurable)
      ((√B + 1) ^ 32)
    apply Filter.Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hwb : wLatitude c p ≤ B := (le_abs_self _).trans
      (bdd_wX c (normSq_xLat_le' (by omega) c
        (BstLean.Part162.latC_sq_le _ c p.1) p.2))
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (sqrt_nonneg _), abs_one]
      linarith [sqrt_le_sqrt hwb])
  apply LBound.ofMoment (by norm_num : (32 : ℕ) ≠ 0)
  refine ⟨mdev, he.1, ?_⟩
  simp only [abs_abs, Even.pow_abs (by decide : Even 32)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun p => by positivity)]
  exact ENNReal.ofReal_le_ofReal hb

theorem location_sq_le_energy (hn : 1 ≤ n) (c : Ret n)
    (p : Ix n × (Fin (n - 1) → ℝ)) : fLatitude c p ^ 2 ≤ wLatitude c p := by
  unfold fLatitude
  rw [fX_eq_lam]
  exact BstLean.Part177.fv_sq_le hn c p.1 p.2

/-- Every even location moment through order 32 follows from the existing energy interface. -/
theorem full_location_moment (hn : 2 ≤ n) (c : Ret n)
    (hc : c.1.2 ≠ 0) (hτ : 0 < (paperDesignP n).tau0 c) {H : ℝ}
    (he : BstLean.Part188.EnergyMoment (paperDesignP n) c H)
    {k : ℕ} (hk : 1 ≤ k) (hke : Even k) (hk32 : k ≤ 32) (K : Set (Ix n)) :
    ∫ a in K, fbR c a ^ k ∂muI n ≤ (1 + H) ^ k := by
  have hk0 : k ≠ 0 := by omega
  let μ := (muI n).prod (stdGauss (Fin (n - 1)))
  have he32 := energy_latitude_norm hn c hc hτ he
  have hek : LBound μ k (fun p => |√(wLatitude c p) - 1|) H :=
    he32.lower (by exact_mod_cast hk0) (by norm_num)
      (by exact_mod_cast hk32) (by simp [μ])
  have h1 : LBound μ k (fun _ => (1 : ℝ)) 1 :=
    LBound.const hk0 (by simp [μ]) (by norm_num)
  have hf : LBound μ k (fLatitude c) (1 + H) := by
    apply (h1.add (by exact_mod_cast hk) hek).mono (measurable_fLatitude c)
    apply Filter.Eventually.of_forall
    intro p
    have hs := sqrt_le_sqrt (location_sq_le_energy (by omega) c p)
    rw [sqrt_sq_eq_abs] at hs
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 + |√(wLatitude c p) - 1|)]
    linarith [le_abs_self (√(wLatitude c p) - 1)]
  have hM : ∀ a v, |fLatitude c (a, v)| ≤
      √(BstLean.Part131.frob (A2 c) * BstLean.Part131.frob (A1 c)) / √(n : ℝ) :=
    fun a v => bdd_fX (by omega) c (normSq_xLat_le' (by omega) c
      (BstLean.Part162.latC_sq_le _ c a) v)
  have hb := conditional_moment (muI n) (stdGauss (Fin (n - 1))) hke
    (hf.toMoment hk0) hM
  rw [latitudeMean_fLatitude] at hb
  have hres := ((LBound.ofMoment hk0 hb).restrict K).toMoment hk0
  have hp : 0 ≤ (1 + H) ^ k := pow_nonneg (by linarith [he.1]) k
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hres.moment
  rw [ENNReal.toReal_ofReal hp] at hreal
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun a => hke.pow_nonneg _)
    ((measurable_fbR c).pow_const k).aestronglyMeasurable]
  simpa only [hke.pow_abs] using hreal

end BstLean.Part252
