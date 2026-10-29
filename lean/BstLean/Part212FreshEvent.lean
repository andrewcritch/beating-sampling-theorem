import BstLean.Part212WeightedEvent
import BstLean.Part212Latitude

/-! The fresh order-160 event uses the twelfth latitude coefficient. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix muI consV)
open BstLean.Part166 (certI psiK fK sK winC)
open BstLean.Part153 (nuA)
open BstLean.Part150 (thetaC)

theorem latitude_fields_weighted_moment80 {n : ℕ} (hn : 1 ≤ n) {K2 : ℝ}
    (hLJ : LatitudeMoment160 n K2) (c : Fin n → ℝ) (τ : ℝ) (hw : winC c τ)
    (a : Ix n) {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    (∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 80) ∂nuA n) ≤
      ENNReal.ofReal ((K2 / n * (1 - latitude (n := n) (√(normSq c)) τ a ^ 2)) ^ 80) ∧
    (∫⁻ θ, ENNReal.ofReal (((n : ℝ) / 2 * psiK sK ((c, τ), θ) a v) ^ 80) ∂nuA n) ≤
      ENNReal.ofReal ((K2 / n * (1 - latitude (n := n) (√(normSq c)) τ a ^ 2)) ^ 80) := by
  obtain ⟨hf, hz⟩ := hLJ c τ hw a v hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by convert hf using 1 <;> congr 2 <;> ring, ?_⟩
  simp_rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ n / 2) 80)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right hz _).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ n / 2) 80),
    ← mul_pow]
  have he : (n : ℝ) / 2 *
      ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * (2 / n) * K2 / n) =
      K2 / n * (1 - latitude (n := n) (√(normSq c)) τ a ^ 2) := by
    field_simp <;> ring
  rw [he, mul_pow]

theorem latitude_weight_positive {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ a ∂muI n, 0 < 1 - latitude (n := n) (√(normSq c)) τ a ^ 2 := by
  have hz : muI n {a : Ix n | normSq a.2 = 0} = 0 := by
    have he : {a : Ix n | normSq a.2 = 0} =
        Set.univ ×ˢ {v : Fin (n - 1) → ℝ | normSq v = 0} := by ext a; simp
    rw [he, muI, Measure.prod_prod, BstLean.Part161.stdGauss_normSq_zero (by omega), mul_zero]
  have hae : ∀ᵐ a ∂muI n, normSq a.2 ≠ 0 := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hae] with a ha
  rw [latitude_ratio (by omega) _ _ hτ a ha]
  have hg : 0 < normSq a.2 := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ha)
  have hd : 0 < normSq (consV (n := n) (√(normSq c)) 0 + τ • consV a.1 a.2) := by
    rw [← BstLean.Part161.consV_smul, ← BstLean.Part161.consV_add,
      BstLean.Part161.normSq_consV (by omega), zero_add, normSq_smul]
    positivity
  exact mul_pos (div_pos (sq_pos_of_pos hτ) hd) hg

theorem latitudeCoefficient_pos {n p : ℕ} (hp : 1 ≤ p) (hn : 4 * p + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < latitudeCoefficient n p (thetaC c τ) := by
  have hnR : 4 * (p : ℝ) + 2 < n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hi := inverseLatitude_identity (j := 2 * p) (by omega) c hτ
  unfold latitudeCoefficient
  rw [mul_div_right_comm, hi]
  apply mul_pos
  · apply div_pos (sq_pos_of_pos hτ)
    apply add_pos_of_nonneg_of_pos (normSq_nonneg c)
    apply mul_pos _ (sq_pos_of_pos hτ)
    push_cast
    linarith
  · linarith

noncomputable def freshLatitudeConstant160 (n q : ℕ) (θ : ℝ) : ℝ :=
  latitudeConstant (√(latitudeJacobianSquared160 n q)) (latitudeCoefficient n 12 θ) (1 / 10000)

theorem fresh_latitude_charge160_of_moment {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (c : Fin n → ℝ) {τ Θ : ℝ} (hw : winC c τ) (hΘ : 0 < Θ)
    (hΘmom : ∫⁻ a, ENNReal.ofReal
      ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 12) ∂muI n ≤
      ENNReal.ofReal (Θ ^ 12)) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (latitudeConstant (√(latitudeJacobianSquared160 n q)) Θ
        (1 / 10000) / n))} ≤ 1 / 10000 := by
  have hτ : 0 < τ := hw.1
  let w := fun a : Ix n => 1 - latitude (n := n) (√(normSq c)) τ a ^ 2
  have hm : Measurable w := measurable_const.sub
    ((measurable_latitude_comp measurable_const measurable_const measurable_id).pow_const 2)
  have hw0 : ∀ a, 0 ≤ w a := fun a => sub_nonneg.mpr (BstLean.Part162.latitude_sq_le _ _ _)
  have hw1 : ∀ a, w a ≤ 1 := fun a =>
    sub_le_self 1 (sq_nonneg (latitude (n := n) (√(normSq c)) τ a))
  have hpos := latitude_weight_positive (by omega) c hτ
  have hK := latitudeJacobianSquared_pos160 hn hq
  have hB : 0 ≤ latitudeJacobianSquared160 n q / n := div_nonneg hK.le (Nat.cast_nonneg _)
  have hj := latitudeMoment160_proved hn hq
  have hf := key_weighted_score80 (by omega) c τ fK BstLean.Part166.measurable_psiK_f
    hm hw0 hpos hw1 (by norm_num : (0 : ℝ) ≤ 1) hB hΘ.le hΘmom
    (fun a v hv => by simpa only [one_mul] using
      (latitude_fields_weighted_moment80 (by omega) hj c τ hw a hv).1)
  have hz := key_weighted_score80 (by omega) c τ sK BstLean.Part166.measurable_psiK_s
    hm hw0 hpos hw1 (scale := (n : ℝ) / 2) (by positivity) hB hΘ.le hΘmom
    (fun a v hv => (latitude_fields_weighted_moment80 (by omega) hj c τ hw a hv).2)
  have hs : √(latitudeJacobianSquared160 n q) ^ 2 = latitudeJacobianSquared160 n q :=
    Real.sq_sqrt hK.le
  apply latitudeEvent_charge_oneTenThousand (by omega) c τ (Real.sqrt_pos.mpr hK) hΘ
  · simpa only [hs, ENNReal.ofReal_one, one_pow, one_mul, div_mul_eq_mul_div] using hf
  · simpa only [hs, latitudeCertZ, div_mul_eq_mul_div] using hz

theorem fresh_latitude_charge160_exact {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (c : Fin n → ℝ) {τ : ℝ} (hw : winC c τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (freshLatitudeConstant160 n q (thetaC c τ) / n))} ≤ 1 / 10000 :=
  fresh_latitude_charge160_of_moment hn hq c hw
    (latitudeCoefficient_pos (by norm_num) (by omega) c hw.1)
    (latitude_moment_exact (by norm_num) (by omega) c hw.1)

theorem fresh_latitude_charge160_window {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (c : Fin n → ℝ) {τ θplus : ℝ} (hw : winC c τ)
    (hθ : thetaC c τ ≤ θplus) (hθ1 : θplus ≤ 1) :
    (nuA n).real {θ | ((c, τ), θ) ∉ latitudeEvent n
      (ENNReal.ofReal (freshLatitudeConstant160 n q θplus / n))} ≤ 1 / 10000 := by
  have hm := latitudeCoefficient_mono (n := n) (p := 12) (by norm_num) (by omega)
    (by linarith [hw.2.1] : 0 ≤ thetaC c τ) hθ hθ1
  have hp := latitudeCoefficient_pos (p := 12) (by norm_num) (by omega) c hw.1
  apply fresh_latitude_charge160_of_moment hn hq c hw (hp.trans_le hm)
  exact (latitude_moment_exact (p := 12) (by norm_num) (by omega) c hw.1).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hp.le hm 12))
theorem fresh_latitude_retained_charge_window {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (D : Design n) (hτ : TauWorld D)
    {Γ : Set ((Fin n → ℝ) × ℝ)} (hΓ : MeasurableSet Γ) {θplus : ℝ} (hθ1 : θplus ≤ 1)
    (hwin : ∀ c τ, (c, τ) ∈ Γ → winC c τ ∧ thetaC c τ ≤ θplus) :
    (retDist D.toCentres).real
      (agentEv D (guardedLatitudeEvent n Γ
        (ENNReal.ofReal (freshLatitudeConstant160 n q θplus / n))))ᶜ ≤ 1 / 10000 := by
  apply guardedLatitudeEvent_retained_charge D hτ hΓ (by norm_num)
  intro c τ _ hc
  obtain ⟨hw, hθ⟩ := hwin c τ hc
  exact fresh_latitude_charge160_window hn hq c hw hθ hθ1
def latitudeWorldWindow (n : ℕ) : Set ((Fin n → ℝ) × ℝ) := {p | winC p.1 p.2}

theorem measurableSet_latitudeWorldWindow (n : ℕ) : MeasurableSet (latitudeWorldWindow n) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × ℝ => thetaC p.1 p.2) := by
    unfold thetaC BstLean.Part150.rhoC normSq
    fun_prop
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const))

def freshRetainedEvent160 (n q : ℕ) : Set (AgFam n) :=
  guardedLatitudeEvent n (latitudeWorldWindow n)
    (ENNReal.ofReal (freshLatitudeConstant160 n q (55 / 100) / n))

theorem measurableSet_freshRetainedEvent160 (n q : ℕ) :
    MeasurableSet (freshRetainedEvent160 n q) :=
  measurableSet_guardedLatitudeEvent (measurableSet_latitudeWorldWindow n) _

theorem fresh_retained_charge160 {n q : ℕ} (hn : 8000 ≤ n) (hq : 1 ≤ q)
    (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (freshRetainedEvent160 n q))ᶜ ≤ 1 / 10000 := by
  apply fresh_latitude_retained_charge_window hn hq D hτ
    (measurableSet_latitudeWorldWindow n) (by norm_num : (55 / 100 : ℝ) ≤ 1)
  intro c τ hw
  exact ⟨hw, hw.2.2⟩

theorem freshRetainedEvent160_fields {n q : ℕ} {k : AgFam n}
    (hk : k ∈ freshRetainedEvent160 n q) (hw : winC k.1.1 k.1.2) :
    k ∈ latitudeEvent n (ENNReal.ofReal (freshLatitudeConstant160 n q (55 / 100) / n)) :=
  hk hw
end BstLean.Part212
