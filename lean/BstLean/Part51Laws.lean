import BstLean.Part51Defs
import BstLean.Part50Laws

/-!
# Part 51, wave 1: the exponent, the computed shift, and the laws

Specification: `delegations/answers/p51-spec-opus.md` §3 (file `Part51Laws`).

* `polR_shiftR`: `polR (shiftR b i0 N) = polR b − (evalE b i0 − N)` everywhere.
* `evalE_eq`: `evalE b i0 = polR b e_{i0}`.
* `shiftR_range`: under `OscLE (polR b) Λ` and `Λ ≤ N`, `0 ≤ polR (shiftR b i0 N) ≤ 2N` on the sphere.
* `shiftR_coef`: under `CoefLE b B`, `CoefLE (shiftR b i0 ⌈Λ⌉₊) (aB r B Λ)` (EF-B).
* `lawE_sph`, `lawKE_sph`: the laws are probability laws on the sphere.
* `uniform_antipodal`: the uniform law is antipodal.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part51

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part50 (NofL Antipodal)

variable {n d : ℕ}

theorem continuous_xl (o : Lin n) : Continuous (fun x : Fin n → ℝ => xl x o) := by
  cases o with
  | none => exact continuous_const
  | some i => exact continuous_apply i

theorem continuous_polR {r : ℕ} (b : WordR n r → ℝ) : Continuous (polR b) := by
  unfold polR
  exact continuous_finsetSum _ fun w _ =>
    continuous_const.mul (continuous_finsetProd _ fun k _ => continuous_xl (w k))

private lemma prod_w0 {r : ℕ} (x : Fin n → ℝ) : ∏ k : Fin r, xl x ((w0 : WordR n r) k) = 1 := by
  simp [w0, xl]

/-- `polR (shiftR b i0 N) = polR b − (evalE b i0 − N)`. -/
theorem polR_shiftR {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) (N : ℕ) (x : Fin n → ℝ) :
    polR (shiftR b i0 N) x = polR b x - (evalE b i0 - N) := by
  classical
  unfold polR shiftR
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, prod_w0, mul_one]

private lemma xl_single (i0 : Fin n) (o : Lin n) :
    xl (Pi.single i0 1) o = if o = none ∨ o = some i0 then 1 else 0 := by
  cases o with
  | none => simp [xl]
  | some i =>
    by_cases h : i = i0
    · subst h; simp [xl]
    · simp [xl, h, Pi.single_apply]

theorem evalE_eq {r : ℕ} (b : WordR n r → ℝ) (i0 : Fin n) :
    evalE b i0 = polR b (Pi.single i0 1) := by
  classical
  unfold evalE polR
  apply Finset.sum_congr rfl; intro w _
  simp only [xl_single]
  by_cases h : inE i0 w
  · rw [if_pos h, Finset.prod_eq_one (fun k _ => if_pos (h k)), mul_one]
  · rw [if_neg h]
    unfold inE at h
    push_neg at h
    obtain ⟨k, hk⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (by tauto)), mul_zero]

theorem single_unit (i0 : Fin n) : ∑ i, (Pi.single i0 (1 : ℝ) : Fin n → ℝ) i ^ 2 = 1 := by
  classical
  rw [Finset.sum_eq_single i0]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

theorem osc_nonneg (hn : 1 ≤ n) {U : (Fin n → ℝ) → ℝ} {Λ : ℝ} (h : OscLE U Λ) : 0 ≤ Λ := by
  have := h (Pi.single ⟨0, by omega⟩ 1) (Pi.single ⟨0, by omega⟩ 1) (single_unit _) (single_unit _)
  linarith

/-- **The shifted range**: `0 ≤ v ≤ 2N` on the sphere. -/
theorem shiftR_range {r : ℕ} (b : WordR n r → ℝ) (Λ : ℝ) (hosc : OscLE (polR b) Λ) (i0 : Fin n)
    (N : ℕ) (hN : Λ ≤ N) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    0 ≤ polR (shiftR b i0 N) x ∧ polR (shiftR b i0 N) x ≤ 2 * N := by
  rw [polR_shiftR, evalE_eq]
  have h1 := hosc x (Pi.single i0 1) hx (single_unit i0)
  have h2 := hosc (Pi.single i0 1) x (single_unit i0) hx
  constructor <;> linarith

private lemma card_inE (r : ℕ) (i0 : Fin n) :
    ((Finset.univ : Finset (WordR n r)).filter (inE i0)).card ≤ 2 ^ r := by
  classical
  let g : (Fin r → Bool) → WordR n r := fun c k => if c k then some i0 else none
  have hsub : (Finset.univ : Finset (WordR n r)).filter (inE i0) ⊆ Finset.univ.image g := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    refine Finset.mem_image.mpr ⟨fun k => decide (w k = some i0), Finset.mem_univ _, ?_⟩
    funext k
    rcases hw' k with h | h <;> simp [g, h]
  calc _ ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin r → Bool)).card := Finset.card_image_le
    _ = 2 ^ r := by simp

/-- **EF-B coefficient bound** of the shifted exponent. -/
theorem shiftR_coef {r : ℕ} (b : WordR n r → ℝ) (B : ℝ) (hB : CoefLE b B) (i0 : Fin n) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) : CoefLE (shiftR b i0 (NofL Λ)) (aB r B Λ) := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB w0)
  have hev : |evalE b i0| ≤ 2 ^ r * B := by
    unfold evalE
    rw [← Finset.sum_filter]
    calc |∑ w ∈ Finset.univ.filter (inE i0), b w| ≤ ∑ w ∈ Finset.univ.filter (inE i0), |b w| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w ∈ Finset.univ.filter (inE i0), B := Finset.sum_le_sum fun w _ => hB w
      _ = ((Finset.univ : Finset (WordR n r)).filter (inE i0)).card * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ r * B := by
          apply mul_le_mul_of_nonneg_right _ hB0
          exact_mod_cast card_inE r i0
  have hN0 : (0 : ℝ) ≤ NofL Λ := Nat.cast_nonneg _
  intro w
  unfold shiftR aB
  split_ifs
  · have := hB w
    calc |b w - (evalE b i0 - NofL Λ)| ≤ |b w| + |evalE b i0| + NofL Λ := by
          have h1 := abs_sub (b w) (evalE b i0 - NofL Λ)
          have h2 := abs_sub (evalE b i0) (NofL Λ : ℝ)
          rw [abs_of_nonneg hN0] at h2
          linarith
      _ ≤ _ := by nlinarith
  · simp only [sub_zero]
    have := hB w
    have : (0 : ℝ) ≤ 2 ^ r * B := by positivity
    nlinarith

private lemma sphere_cont_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma normalized_prob (hn : 1 ≤ n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x)
    (hz : 0 < ∫ x, w x ∂uniformSphere n) :
    IsProbabilityMeasure ((uniformSphere n).withDensity
      (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂uniformSphere n))) := by
  have hi := (sphere_cont_integrable hn hw).div_const (∫ y, w y ∂uniformSphere n)
  have h0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x / ∫ y, w y ∂uniformSphere n :=
    hw0.mono (fun x hx => div_nonneg hx hz.le)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi h0, integral_div,
    div_self hz.ne', ENNReal.ofReal_one]

theorem taylor_ge_one (K : ℕ) (v : ℝ) (hv : 0 ≤ v) : 1 ≤ BstLean.Part37.taylorExp K v := by
  unfold BstLean.Part37.taylorExp
  rw [Finset.sum_range_succ']
  have : 0 ≤ ∑ i ∈ Finset.range K, v ^ (i + 1) / ((i + 1).factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hv _) (by positivity)
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  linarith

theorem lawE_sph (hn : 1 ≤ n) (U : (Fin n → ℝ) → ℝ) (hU : Continuous U) : SphLaw n (lawE n U) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => Real.exp (U x)) := Real.continuous_exp.comp hU
  have hz : 0 < ∫ x, Real.exp (U x) ∂uniformSphere n :=
    integral_exp_pos (sphere_cont_integrable hn hc)
  exact ⟨normalized_prob hn hc (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hz,
    (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)⟩

theorem ZKE_ge_one (hn : 1 ≤ n) (K : ℕ) (V : (Fin n → ℝ) → ℝ) (hV : Continuous V) (h0 : NonnegS V) :
    1 ≤ ZKE n K V := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => BstLean.Part37.taylorExp K (V x)) := by
    unfold BstLean.Part37.taylorExp; fun_prop
  have hge : ∀ᵐ y ∂uniformSphere n, 1 ≤ BstLean.Part37.taylorExp K (V y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact taylor_ge_one K _ (h0 y hy)
  have h := integral_mono_ae (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) hge
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

theorem lawKE_sph (hn : 1 ≤ n) (K : ℕ) (V : (Fin n → ℝ) → ℝ) (hV : Continuous V) (h0 : NonnegS V) :
    SphLaw n (lawKE n K V) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hc : Continuous (fun x => BstLean.Part37.taylorExp K (V x)) := by
    unfold BstLean.Part37.taylorExp; fun_prop
  have hw0 : ∀ᵐ y ∂uniformSphere n, 0 ≤ BstLean.Part37.taylorExp K (V y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact zero_le_one.trans (taylor_ge_one K _ (h0 y hy))
  have hz : 0 < ∫ x, BstLean.Part37.taylorExp K (V x) ∂uniformSphere n :=
    zero_lt_one.trans_le (ZKE_ge_one hn K V hV h0)
  exact ⟨normalized_prob hn hc hw0 hz,
    (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)⟩

/-- The uniform law is antipodal (it is `binghamA n 0`). -/
theorem uniform_antipodal (hn : 1 ≤ n) : Antipodal n (uniformSphere n) := by
  have h := BstLean.Part50.binghamA_antipodal hn (0 : Matrix (Fin n) (Fin n) ℝ)
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hq : ∀ x, BstLean.Part50.qA (0 : Matrix (Fin n) (Fin n) ℝ) x = 0 := by
    intro x; simp [BstLean.Part50.qA]
  have hZ : BstLean.Part50.ZA n 0 = 1 := by
    simp [BstLean.Part50.ZA, hq]
  have he : BstLean.Part50.binghamA n 0 = uniformSphere n := by
    unfold BstLean.Part50.binghamA
    simp [hq, hZ]
  rw [he] at h
  exact h

end BstLean.Part51
