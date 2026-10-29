import BstLean.Part184BF1
import BstLean.Part184BF2
import BstLean.Part184EnB
import BstLean.Part184Def2

/-!
# Part 184 (file `BF3`): the location fluctuation bound of the row moment expansion, PROVED

No proof is left open; no `native_decide` or `axiom` is used.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part157 (cOf reb)
open BstLean.Part150 (hT sT)

variable {n : ℕ}

/-- The image of the centre direction under the plane-split matrix. -/
lemma Mpl0_mulVec_h (h r c₂ : Fin (mA n) → ℝ) (ξ₁ : Fin (mA n) → ℝ) (t : ℝ) :
    Mpl h r (cOf t h ξ₁) c₂ 0 *ᵥ h = (√t * √(normSq h)) • ξ₁ := by
  by_cases hh : h = 0
  · subst hh
    have : normSq (0 : Fin (mA n) → ℝ) = 0 := by simp [normSq]
    simp [this]
  · unfold Mpl
    rw [reb_mulVec_self hh]
    rfl

/-- The centre weights are a scaled `Fw` profile. -/
lemma bOfY_eq (c : Ret n) (y : Fin (mA n) → ℝ) :
    bOfY c y = (BstLean.Part150.rhoC c.1.2 (tau0p c.1.1))⁻¹ •
      (fun j => Fw n (sT n (A1 c) c.1.2 (tau0p c.1.1)) (y j)) := by
  funext j
  simp only [bOfY, Fw, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- `P²W ≤ Q⁴·R₄(b)` and `P ≤ Q` for the location moments. -/
lemma loc_PW (b : Fin (mA n) → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    let κ := (n : ℝ) / (√(n : ℝ) * √(normSq b))
    (∑ j, (κ * b j) ^ 2 * x) ≤ n * x ∧
      (∑ j, (κ * b j) ^ 2 * x) ^ 2 * ∑ j, ((κ * b j) ^ 2 * x) ^ 2 ≤ (n * x) ^ 4 * R4 b := by
  intro κ
  have hk := kappa_b_le n b
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : 0 ≤ normSq b := by unfold normSq; positivity
  have hk2 : κ ^ 2 * normSq b ≤ n := by
    have h1 := pow_le_pow_left₀ (by positivity) hk 2
    rw [mul_pow, sq_abs, Real.sq_sqrt hS0, Real.sq_sqrt hn0] at h1
    exact h1
  have e1 : ∑ j, (κ * b j) ^ 2 * x = κ ^ 2 * normSq b * x := by
    unfold normSq; rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, ((κ * b j) ^ 2 * x) ^ 2 = κ ^ 4 * x ^ 2 * ∑ j, b j ^ 4 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hk20 : 0 ≤ κ ^ 2 * normSq b := by positivity
  refine ⟨?_, ?_⟩
  · rw [e1]; exact mul_le_mul_of_nonneg_right hk2 hx
  · rw [e1, e2]
    have h4 : ∑ j, b j ^ 4 = R4 b * normSq b ^ 2 := by
      unfold R4 normSq
      rcases eq_or_lt_of_le (show 0 ≤ ∑ j, b j ^ 2 by positivity) with h | h
      · have hb : ∀ j, b j = 0 := fun j => by
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (b i))).mp h.symm j
            (Finset.mem_univ j)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        simp [hb]
      · field_simp
    rw [h4]
    have hR := R4_nonneg b
    have : (κ ^ 2 * normSq b) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ hk20 hk2 4
    calc (κ ^ 2 * normSq b * x) ^ 2 * (κ ^ 4 * x ^ 2 * (R4 b * normSq b ^ 2))
        = (κ ^ 2 * normSq b) ^ 4 * x ^ 4 * R4 b := by ring
      _ ≤ (n : ℝ) ^ 4 * x ^ 4 * R4 b := by gcongr
      _ = _ := by ring

/-- The numeric closure: `Q⁴(105 + 46600·47400/m) ≤ FflB⁸`, `Q = n·tΛ/4`, `m = n² ≥ 16000²`. -/
lemma fflb_closure (hn : 16000 ≤ n) {O q : ℝ} (hO : 0 < O) (hq : 0 < q) :
    105 * ((n : ℝ) * (tA n * (q * O ^ 2 / ((n : ℝ) - 2)) / 4)) ^ 4 +
      46600 * ((n : ℝ) * (tA n * (q * O ^ 2 / ((n : ℝ) - 2)) / 4)) ^ 4 * (47400 / (mA n : ℝ)) ≤
      FflB n O q ^ 8 := by
  have hx : (16000 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have hΛ : 0 < Λ := by positivity
  set Q := (n : ℝ) * (tA n * Λ / 4) with hQd
  have hQ : 0 ≤ Q := by positivity
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hm2 : (16000 : ℝ) ^ 2 ≤ mA n := by rw [hm]; exact pow_le_pow_left₀ (by norm_num) hx 2
  have hA : FflB n O q ^ 8 = (181 / 100) ^ 8 * Q ^ 4 := by
    unfold FflB
    rw [← hΛd]
    have e : (181 / 100 * √(n : ℝ) * √(tA n * Λ) / 2) ^ 8 =
        (181 / 100) ^ 8 * ((√(n : ℝ) ^ 2) * (√(tA n * Λ) ^ 2) / 4) ^ 4 := by ring
    rw [e, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hQd]
    ring
  rw [hA]
  have hfrac : 47400 / (mA n : ℝ) ≤ 47400 / 16000 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm2
  have hQ4 : 0 ≤ Q ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ 46600 * Q ^ 4)
  have hc : (105 : ℝ) + 46600 * (47400 / 16000 ^ 2) ≤ (181 / 100) ^ 8 := by norm_num
  nlinarith

/-- **The location fluctuation at a node by the row moment expansion.** -/
theorem exFn_mom_B_of (hn : 16000 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 < O) (h1 : OpB (A1 c) O) {q : ℝ} (hq1 : 1 / 10 ≤ q) (hq : 1 - nodeS c g ^ 2 ≤ q)
    {B : ℝ} (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((FflB n O q + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := q * O ^ 2 / ((n : ℝ) - 2) with hΛd
  have hq0 : 0 < q := by linarith
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := fun e =>
    (BstLean.Part173.cov_bound_lat hn3 c hs hO.le h1 e).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg O)) h2n.le)
      (normSq_nonneg e))
  set A := FflB n O q with hAd
  have hA : 0 < A := by
    rw [hAd]; unfold FflB
    have : 0 < √(tA n * (q * O ^ 2 / ((n : ℝ) - 2))) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  set Q := (n : ℝ) * (tA n * Λ / 4) with hQd
  have hQ0 : 0 ≤ Q := by positivity
  set S := sT n (A1 c) c.1.2 (tau0p c.1.1) with hSd
  set σ := √(tA n) * √(normSq h) with hσd
  have hσ : 0 ≤ σ := by positivity
  set Rf : (Fin (mA n) → ℝ) → ℝ≥0∞ := fun ξ₁ =>
    ENNReal.ofReal (105 * Q ^ 4) + ENNReal.ofReal (46600 * Q ^ 4) *
      ENNReal.ofReal (R4 (fun j => Fw n S (σ * ξ₁ j))) with hRfd
  have mR4 : Measurable (fun ξ₁ : Fin (mA n) → ℝ => R4 (fun j => Fw n S (σ * ξ₁ j))) :=
    measurable_R4.comp (continuous_pi fun j => (continuous_Fw n S).comp
      (continuous_const.mul (continuous_apply j))).measurable
  have mRf : Measurable Rf :=
    measurable_const.add (measurable_const.mul (ENNReal.measurable_ofReal.comp mR4))
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal k₁ * Rf ξ₁ + ENNReal.ofReal k₂ * ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set b₀ := bOfY c (M₀ *ᵥ h)
    set ψ₀ : Fin (mA n) → ℝ := fun j => BstLean.Part137.psiS √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set κ₀ := (n : ℝ) / (√(n : ℝ) * √(normSq b₀))
    set E := flE (stdGauss (Fin (n - 1))) (aLat c s) h M₀ b₀ ψ₀ κ₀
    have hE : ∀ N, exFn (withA2 c (reb h c₁ (reb r c₂ N))) g = E N := fun N =>
      exFn_Mpl hn1 c g hK c₁ c₂ N
    have hmE : ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) = biasF c g ξ₁ ξ₂ := by
      unfold biasF
      exact integral_congr_ae (Filter.Eventually.of_forall fun N => (hE N).symm)
    simp_rw [hE]
    have hc := continuous_flE (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀
    have hpt : ∀ N, ENNReal.ofReal (E N ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
        ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
      intro N
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n))
        (∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)) hA hB0
      rw [sub_add_cancel, hmE] at this
      have e8 : |biasF c g ξ₁ ξ₂| ^ 8 = biasF c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      rw [hmE]
      exact this
    have mfl : Measurable (fun N => ENNReal.ofReal
        (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const 8)
    -- the row moment expansion
    have mo := measurable_matOf (m := mA n) (tA n)
    have hint : ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n) =
        ∫ ζ, E (matOf (tA n) ζ) ∂stdGauss (Fin (mA n) × Fin (mA n)) := by
      rw [gaussMat_eq, integral_map mo.aemeasurable hc.aestronglyMeasurable]
    have hfl : ∫⁻ N, ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ≤ Rf ξ₁ := by
      rw [hint, gaussMat_eq, lintegral_map (f := fun N => ENNReal.ofReal (|E N -
        ∫ ζ, E (matOf (tA n) ζ) ∂stdGauss (Fin (mA n) × Fin (mA n))| ^ 8))
        (ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const 8)) mo]
      refine (flE_rows8 (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀ htA.le).trans ?_
      obtain ⟨hP1, hP2⟩ := loc_PW (n := n) b₀ (x := tA n * Λ / 4) (by positivity)
      have hP0 : 0 ≤ ∑ j, (κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4) :=
        Finset.sum_nonneg fun j _ => by positivity
      have e1 : ∀ j, (κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4) = (κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4) := fun j => rfl
      have hR : R4 b₀ ≤ R4 (fun j => Fw n S (σ * ξ₁ j)) := by
        have hb : b₀ = (BstLean.Part150.rhoC c.1.2 (tau0p c.1.1))⁻¹ •
            (fun j => Fw n S (σ * ξ₁ j)) := by
          simp only [b₀, M₀, c₁]
          rw [bOfY_eq, Mpl0_mulVec_h]
          rfl
        rw [hb]; exact R4_smul_le _ _
      have hQ4 : 0 ≤ Q ^ 4 := by positivity
      calc ENNReal.ofReal (105 * (∑ j, (κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4)) ^ 4 +
            46600 * ((∑ j, (κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4)) ^ 2 *
              ∑ j, ((κ₀ * b₀ j) ^ 2 * (tA n * Λ / 4)) ^ 2))
          ≤ ENNReal.ofReal (105 * Q ^ 4 + 46600 * Q ^ 4 * R4 (fun j => Fw n S (σ * ξ₁ j))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h4 := pow_le_pow_left₀ hP0 hP1 4
            have h5 : (n : ℝ) * (tA n * Λ / 4) = Q := rfl
            rw [h5] at h4 hP2
            have h6 := mul_le_mul_of_nonneg_left hR hQ4
            nlinarith
        _ = Rf ξ₁ := by
            simp only [Rf]
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by have := R4_nonneg (fun j => Fw n S (σ * ξ₁ j)); positivity)]
    calc ∫⁻ N, ENNReal.ofReal (E N ^ 8) ∂gaussMat (mA n) (mA n) (tA n)
        ≤ ∫⁻ N, (ENNReal.ofReal k₁ *
          ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
          ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8)) ∂gaussMat (mA n) (mA n) (tA n) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ N, ENNReal.ofReal
            (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)
            ∂gaussMat (mA n) (mA n) (tA n) + ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * Rf ξ₁ + ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  have hdeloc := deloc (m := mA n) (J := n) hn1 (by unfold mA; nlinarith) S hσ
  have hRint : ∫⁻ ξ₁, ∫⁻ ξ₂, Rf ξ₁ ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ≤
      ENNReal.ofReal (105 * Q ^ 4 + 46600 * Q ^ 4 * (47400 / (mA n : ℝ))) := by
    simp only [lintegral_const, measure_univ, mul_one]
    simp only [Rf]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (105 * Q ^ 4) + ENNReal.ofReal (46600 * Q ^ 4) *
          ∫⁻ ξ₁, ENNReal.ofReal (R4 (fun j => Fw n S (σ * ξ₁ j))) ∂stdGauss (Fin (mA n))
        ≤ ENNReal.ofReal (105 * Q ^ 4) + ENNReal.ofReal (46600 * Q ^ 4) *
          ENNReal.ofReal (47400 / (mA n : ℝ)) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
  have hnum : 105 * Q ^ 4 + 46600 * Q ^ 4 * (47400 / (mA n : ℝ)) ≤ A ^ 8 :=
    fflb_closure hn hO hq0
  have mRu : Measurable (Function.uncurry fun (ξ₁ _ξ₂ : Fin (mA n) → ℝ) => Rf ξ₁) :=
    mRf.comp measurable_fst
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal k₁ * Rf ξ₁ + ENNReal.ofReal k₂ *
          ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal k₁ * ∫⁻ ξ₁, ∫⁻ ξ₂, Rf ξ₁ ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) +
          ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)
          ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        dbl_comb2 (stdGauss (Fin (mA n))) mRu
          (fun ξ₁ ξ₂ => ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
        exact hRint.trans (ENNReal.ofReal_le_ofReal hnum)
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_mul hk₂,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

/-- **The location fluctuation bound of the row moment expansion** (`EnFB_stmt`). -/
theorem EnFB_proved : EnFB_stmt := by
  intro n hn c g hs O hO h1 q hq1 hq B hB0 hBias
  exact exFn_mom_B_of hn c g hs hO h1 hq1 hq hB0 hBias

end BstLean.Part184

#print axioms BstLean.Part184.deloc
#print axioms BstLean.Part184.flE_rows8
#print axioms BstLean.Part184.exFn_mom_B_of
#print axioms BstLean.Part184.EnFB_proved
