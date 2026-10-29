import BstLean.Part50Defs
import BstLean.Part43Surr

/-!
# Part 50, wave 1 (proved): Lemma K′ (the bias of the non-diagonal surrogate)

Specification: `delegations/answers/p50-spec-opus.md` §3 (file `Part50Surr`). Paper: omGA-opus-prover §5.1.

* `surrA_bias`: `Part43Surr.surr_bias` for `D(A) = binghamA n A` and the Taylor law of any `B` with
  `qA A = qA B + c` on the sphere and `0 ≤ qA B ≤ L` on the sphere, at `K = Kof43 L ε`. Proof: a copy of
  `Part43Surr` from `bingham_shift` on, with `qth (bmin θ) x` replaced by `qA B x` and `spread θ` by `L`.
  The proof uses only the pointwise range `qA B x ∈ [0, L]` on the sphere.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part50

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)
open BstLean.Part43

variable {n d : ℕ}

open BstLean.Part37 (taylorExp)

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


private lemma taylor_ge_one (K : ℕ) (v : ℝ) (hv : 0 ≤ v) : 1 ≤ taylorExp K v := by
  classical
  have h := Finset.single_le_sum (s := Finset.range (K + 1))
    (f := fun j => v ^ j / (j.factorial : ℝ))
    (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.zero_lt_succ K))
  simpa [taylorExp] using h


private lemma etaQ_pos {ε : ℝ} (hε : 0 < ε) : 0 < etaQ ε := by
  unfold etaQ xi43
  exact lt_min (by positivity) (by norm_num)

private lemma Leta_pos {ε : ℝ} (hε : 0 < ε) : 0 < Leta ε := by
  apply Real.log_pos
  apply (lt_div_iff₀ (etaQ_pos hε)).mpr
  linarith

private lemma ustar_equation {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ustar A ε ^ 2 = (2 / 3 : ℝ) * Leta ε * ustar A ε + 2 * A * Leta ε := by
  have hL := Leta_pos hε
  have hs := Real.sq_sqrt (show 0 ≤ Leta ε ^ 2 / 9 + 2 * A * Leta ε by positivity)
  unfold ustar
  nlinarith

private lemma Kof43_ge {A ε : ℝ} : A + ustar A ε ≤ (Kof43 A ε : ℝ) :=
  Nat.le_ceil _

private lemma exp_sum (s : ℝ) :
    HasSum (fun k : ℕ => s ^ k / (k.factorial : ℝ)) (Real.exp s) := by
  simpa [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp s

private lemma taylor_tail_chernoff (K : ℕ) (v t : ℝ) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    Real.exp (-v) * (Real.exp v - taylorExp K v) ≤
      Real.exp (v * (Real.exp t - 1) - t * (K + 1)) := by
  have hs := (exp_sum v).summable
  have hs' := (exp_sum (v * Real.exp t)).summable
  have htail := hs.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum v).tsum_eq] at htail
  have htail' := hs'.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum (v * Real.exp t)).tsum_eq] at htail'
  have hbound : (∑' j : ℕ, (v * Real.exp t) ^ (j + (K + 1)) /
      ((j + (K + 1)).factorial : ℝ)) ≤ Real.exp (v * Real.exp t) := by
    have h0 : 0 ≤ ∑ j ∈ Finset.range (K + 1),
        (v * Real.exp t) ^ j / (j.factorial : ℝ) := by positivity
    linarith
  have hterm (j : ℕ) : v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) ≤
      Real.exp (-t * (K + 1)) *
        ((v * Real.exp t) ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : 1 ≤ Real.exp (-t * (K + 1)) * Real.exp ((j + (K + 1) : ℕ) * t) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast
      nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have h0 : 0 ≤ v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) := by positivity
    calc
      _ ≤ (Real.exp (-t * (K + 1)) * Real.exp ((j + (K + 1) : ℕ) * t)) *
          (v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ)) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he h0
      _ = _ := by ring
  have hle := (hs.comp_injective (add_left_injective (K + 1))).tsum_le_tsum hterm
    ((hs'.comp_injective (add_left_injective (K + 1))).mul_left (Real.exp (-t * (K + 1))))
  rw [tsum_mul_left] at hle
  have hle' := hle.trans (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le)
  have heq : Real.exp v - taylorExp K v =
      ∑' j : ℕ, v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) := by
    unfold taylorExp
    linarith
  rw [heq]
  calc
    _ ≤ Real.exp (-v) * (Real.exp (-t * (K + 1)) * Real.exp (v * Real.exp t)) :=
      mul_le_mul_of_nonneg_left hle' (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


private lemma factorial_ge (j : ℕ) : (2 : ℝ) * 3 ^ j ≤ ((j + 2).factorial : ℝ) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have h : (3 : ℝ) ≤ j + 2 + 1 := by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
    have hj : 0 ≤ ((j + 2).factorial : ℝ) := by positivity
    calc
      2 * (3 ^ j * 3) = 3 * (2 * 3 ^ j) := by ring
      _ ≤ 3 * ((j + 2).factorial : ℝ) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_right h hj

private lemma exp_bernstein (t : ℝ) (ht : 0 ≤ t) (ht3 : t < 3) :
    Real.exp t - 1 - t ≤ t ^ 2 / (2 * (1 - t / 3)) := by
  have hs := (exp_sum t).summable
  have htail := hs.sum_add_tsum_nat_add 2
  rw [(exp_sum t).tsum_eq] at htail
  have hg := hasSum_geometric_of_lt_one (show 0 ≤ t / 3 by positivity)
    (show t / 3 < 1 by linarith)
  have hterm (j : ℕ) : t ^ (j + 2) / ((j + 2).factorial : ℝ) ≤
      (t ^ 2 / 2) * (t / 3) ^ j := by
    calc
      _ ≤ t ^ (j + 2) / (2 * 3 ^ j) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_ge j)
      _ = _ := by rw [pow_add, div_pow]; field_simp
  have hle := (hs.comp_injective (add_left_injective 2)).tsum_le_tsum hterm
    (hg.summable.mul_left (t ^ 2 / 2))
  rw [tsum_mul_left, hg.tsum_eq] at hle
  norm_num [Finset.sum_range_succ] at htail
  calc
    _ = ∑' j : ℕ, t ^ (j + 2) / ((j + 2).factorial : ℝ) := by linarith
    _ ≤ (t ^ 2 / 2) * (1 - t / 3)⁻¹ := hle
    _ = _ := by rw [div_mul_eq_div_mul_one_div, one_div]

private lemma cutoff_tail (A ε v : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hv : 0 ≤ v) (hvA : v ≤ A) :
    Real.exp (-v) * (Real.exp v - taylorExp (Kof43 A ε) v) ≤
      etaQ ε / (1 + etaQ ε) := by
  have hη := etaQ_pos hε
  have hL := Leta_pos hε
  have hdelta : Real.exp (-Leta ε) = etaQ ε / (1 + etaQ ε) := by
    unfold Leta
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  by_cases hAz : A = 0
  · have hvz : v = 0 := by linarith
    rw [hvz]
    have hz : taylorExp (Kof43 A ε) 0 = 1 := by
      classical
      unfold taylorExp
      rw [Finset.sum_eq_single 0]
      · norm_num
      · intro j hj hj0; simp [zero_pow hj0]
      · simp
    rw [hz]
    simp only [Real.exp_zero, sub_self, mul_zero]
    positivity
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  let u := ustar A ε
  let c := A + u / 3
  let t := u / c
  have hu : 0 < u := by dsimp [u, ustar]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht3 : t < 3 := by
    dsimp [t]
    apply (div_lt_iff₀ hc).mpr
    dsimp [c]
    linarith
  have htden : 0 < 1 - t / 3 := by linarith
  have hcut := Kof43_ge (A := A) (ε := ε)
  have he := exp_bernstein t ht ht3
  have hrem : 0 ≤ Real.exp t - 1 - t := by linarith [Real.add_one_le_exp t]
  have hexp : v * (Real.exp t - 1) - t * ((Kof43 A ε : ℝ) + 1) ≤ -Leta ε := by
    have h1 := mul_le_mul_of_nonneg_left (show v ≤ A from hvA) hrem
    have h2 := mul_le_mul_of_nonneg_left he hA
    have h3 := mul_le_mul_of_nonneg_left (show A + u ≤ (Kof43 A ε : ℝ) + 1 by
      dsimp [u]; linarith) ht
    have hid : A * (t ^ 2 / (2 * (1 - t / 3))) - t * u = -Leta ε := by
      have huEq := ustar_equation hA hε
      change u ^ 2 = (2 / 3 : ℝ) * Leta ε * u + 2 * A * Leta ε at huEq
      dsimp [t, c]
      field_simp
      nlinarith [huEq]
    have h4 := mul_le_mul_of_nonneg_left hvA ht
    nlinarith only [h1, h2, h3, h4, hid]
  calc
    _ ≤ Real.exp (v * (Real.exp t - 1) - t * ((Kof43 A ε : ℝ) + 1)) :=
      taylor_tail_chernoff _ v t hv ht
    _ ≤ Real.exp (-Leta ε) := Real.exp_le_exp.mpr hexp
    _ = _ := hdelta



private lemma taylor_le_exp (K : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    taylorExp K v ≤ Real.exp v := by
  have h := (exp_sum v).summable.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum v).tsum_eq] at h
  have h0 : 0 ≤ ∑' j : ℕ, v ^ (j + (K + 1)) / ((j + (K + 1)).factorial : ℝ) :=
    tsum_nonneg fun j => by positivity
  unfold taylorExp
  linarith


private lemma normalized_ratio_abs (a e za ze η : ℝ)
    (ha : 0 ≤ a) (he : 0 < e) (hza : 0 < za) (hze : 0 < ze) (hη : 0 ≤ η)
    (hlo : e ≤ (1 + η) * a) (hhi : a ≤ e)
    (hzlo : ze ≤ (1 + η) * za) (hzhi : za ≤ ze) :
    |(a / za) / (e / ze) - 1| ≤ η := by
  have hd : 0 < za * e := mul_pos hza he
  have hnumhi : a * ze ≤ (1 + η) * (za * e) := by
    calc
      _ ≤ e * ze := mul_le_mul_of_nonneg_right hhi hze.le
      _ ≤ e * ((1 + η) * za) := mul_le_mul_of_nonneg_left hzlo he.le
      _ = _ := by ring
  have hrawlo : (1 - η) * e ≤ a := by
    have h := mul_le_mul_of_nonneg_left hhi hη
    nlinarith only [hlo, h]
  have hnumlo : (1 - η) * (za * e) ≤ a * ze := by
    calc
      _ = ((1 - η) * e) * za := by ring
      _ ≤ a * za := mul_le_mul_of_nonneg_right hrawlo hza.le
      _ ≤ a * ze := mul_le_mul_of_nonneg_left hzhi ha
  have hform : (a / za) / (e / ze) - 1 = (a * ze - za * e) / (za * e) := by
    field_simp
  rw [hform, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  exact abs_le.mpr ⟨by nlinarith only [hnumlo], by nlinarith only [hnumhi]⟩

private lemma sphere_integrable {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    (hs : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma weighted {w : (Fin n → ℝ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂(uniformSphere n).withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, f x * w x ∂uniformSphere n := by
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [hw0] with x hx
  simp [ENNReal.toReal_ofReal hx, mul_comm]


private lemma continuous_fval_map (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    Continuous (fun x => fval k f0 T (mapMD M x)) := by
  classical
  have hm (a : Fin n) : Continuous (fun x => mapMD M x a) := by
    unfold mapMD
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro β hβ
    apply Continuous.mul continuous_const
    unfold BstLean.Part36.monoVal
    exact continuous_multiset_prod β.1 (fun b _ => continuous_apply b)
  unfold fval contr
  apply Continuous.add continuous_const
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro w hw
  apply Continuous.mul continuous_const
  apply continuous_finsetProd
  intro t ht
  exact hm (w t)


private lemma continuous_qA (B : Matrix (Fin n) (Fin n) ℝ) : Continuous (qA B) := by
  unfold qA; fun_prop

private lemma taylor_relativeA (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (L : ℝ)
    (hr : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → 0 ≤ qA B x ∧ qA B x ≤ L) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    Real.exp (qA B x) ≤ (1 + etaQ ε) * taylorExp (Kof43 L ε) (qA B x) ∧
    taylorExp (Kof43 L ε) (qA B x) ≤ Real.exp (qA B x) := by
  have hv := hr x hx
  have hL : 0 ≤ L := hv.1.trans hv.2
  have h := cutoff_tail _ ε _ hL hε hv.1 hv.2
  have hη := etaQ_pos hε
  have hη1 : 0 < 1 + etaQ ε := by positivity
  have he : 0 < Real.exp (qA B x) := Real.exp_pos _
  have h' : (Real.exp (qA B x) - taylorExp (Kof43 L ε) (qA B x)) / Real.exp (qA B x) ≤
      etaQ ε / (1 + etaQ ε) := by
    simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using h
  have h'' := (div_le_div_iff₀ he hη1).mp h'
  constructor
  · nlinarith only [h'']
  · exact taylor_le_exp _ _ hv.1

private lemma ZA_pos (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) : 0 < ZA n B := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  exact integral_exp_pos (sphere_cont_integrable hn (Real.continuous_exp.comp (continuous_qA B)))

private lemma surrogate_ratioA (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (L : ℝ)
    (hr : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → 0 ≤ qA B x ∧ qA B x ≤ L) (ε : ℝ) (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |(taylorExp (Kof43 L ε) (qA B x) / ZKA n (Kof43 L ε) B) /
      (Real.exp (qA B x) / ZA n B) - 1| ≤ etaQ ε := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let K := Kof43 L ε
  have hc : Continuous (fun x => taylorExp K (qA B x)) := by
    unfold taylorExp; have := continuous_qA B; fun_prop
  have hce : Continuous (fun x => Real.exp (qA B x)) := Real.continuous_exp.comp (continuous_qA B)
  have hbd : ∀ᵐ y ∂uniformSphere n,
      Real.exp (qA B y) ≤ (1 + etaQ ε) * taylorExp K (qA B y) ∧
      taylorExp K (qA B y) ≤ Real.exp (qA B y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact taylor_relativeA hn B L hr ε hε y hy
  have hge : ∀ᵐ y ∂uniformSphere n, 1 ≤ taylorExp K (qA B y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact taylor_ge_one K _ (hr y hy).1
  have hpos : 0 < ZKA n K B := by
    have h := integral_mono_ae (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) hge
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact zero_lt_one.trans_le h
  have hzlo : ZA n B ≤ (1 + etaQ ε) * ZKA n K B := by
    have h := integral_mono_ae (sphere_cont_integrable hn hce)
      ((sphere_cont_integrable hn hc).const_mul (1 + etaQ ε)) (hbd.mono fun _ h => h.1)
    simpa only [integral_const_mul, ZKA, ZA] using h
  have hzhi : ZKA n K B ≤ ZA n B :=
    integral_mono_ae (sphere_cont_integrable hn hc) (sphere_cont_integrable hn hce)
      (hbd.mono fun _ h => h.2)
  exact normalized_ratio_abs _ _ _ _ _ (zero_le_one.trans (taylor_ge_one K _ (hr x hx).1))
    (Real.exp_pos _) hpos (ZA_pos hn B) (etaQ_pos hε).le
    (taylor_relativeA hn B L hr ε hε x hx).1 (taylor_relativeA hn B L hr ε hε x hx).2 hzlo hzhi

private lemma binghamA_shift (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hsh : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → qA A x = qA B x + c) :
    binghamA n A = binghamA n B := by
  have he : (fun x => Real.exp (qA A x)) =ᵐ[uniformSphere n]
      (fun x => Real.exp c * Real.exp (qA B x)) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [← Real.exp_add, hsh x hx, add_comm]
  have hz : ZA n A = Real.exp c * ZA n B := by
    unfold ZA
    rw [integral_congr_ae he, integral_const_mul]
  unfold binghamA
  apply withDensity_congr_ae
  filter_upwards [he] with x hx
  rw [hx, hz, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

private lemma bias_from_ratioA (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (K : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hT : ∀ᵐ x ∂uniformSphere n, 0 ≤ taylorExp K (qA B x))
    (hZ : 0 < ZKA n K B)
    (hbound : ∀ x : Fin n → ℝ, (∑ i, x i ^ 2 = 1) →
      |(taylorExp K (qA B x) / ZKA n K B) / (Real.exp (qA B x) / ZA n B) - 1| ≤ η)
    (h : (Fin n → ℝ) → ℝ) (ch : Continuous h) :
    |(∫ x, h x ∂binghamA n B) - (∫ x, h x ∂binghamKA n K B)| ≤
      η * Real.sqrt (varU (binghamA n B) h) := by
  let μ := binghamA n B
  have hz := ZA_pos hn B
  have ce : Continuous (fun x => Real.exp (qA B x)) := Real.continuous_exp.comp (continuous_qA B)
  have : IsProbabilityMeasure μ := normalized_prob hn ce
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hz
  have hs : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)
  let r : (Fin n → ℝ) → ℝ := fun x =>
    (taylorExp K (qA B x) / ZKA n K B) / (Real.exp (qA B x) / ZA n B)
  have ct : Continuous (fun x => taylorExp K (qA B x)) := by
    unfold taylorExp; have := continuous_qA B; fun_prop
  have cr : Continuous r :=
    (ct.div_const _).div (ce.div_const _) (fun x => div_ne_zero (Real.exp_ne_zero _) hz.ne')
  have : IsProbabilityMeasure (binghamKA n K B) := normalized_prob hn ct hT hZ
  have transfer (f : (Fin n → ℝ) → ℝ) :
      ∫ x, f x * r x ∂μ = ∫ x, f x ∂binghamKA n K B := by
    dsimp [μ]
    unfold binghamA binghamKA
    rw [weighted (w := fun x => Real.exp (qA B x) / ZA n B)
      (ce.div_const _)
      (Filter.Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hz.le),
      weighted (w := fun x => taylorExp K (qA B x) / ZKA n K B)
        (ct.div_const _)
        (hT.mono fun x hx => div_nonneg hx hZ.le)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp [r]
      field_simp [hz.ne', hZ.ne']
  have ir : ∫ x, r x ∂μ = 1 := by simpa using transfer (fun _ => 1)
  let Bv := ∫ x, h x ∂μ
  let u : (Fin n → ℝ) → ℝ := fun x => h x - Bv
  have cu : Continuous u := ch.sub continuous_const
  have integrable_cont {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f μ :=
    sphere_integrable hs hf
  have iu := integrable_cont cu
  have ie : Integrable (fun x => r x - 1) μ := integrable_cont (cr.sub continuous_const)
  have ieu : Integrable (fun x => (r x - 1) * u x) μ :=
    integrable_cont ((cr.sub continuous_const).mul cu)
  have ihr : Integrable (fun x => h x * r x) μ := integrable_cont (ch.mul cr)
  have ih := integrable_cont ch
  have he : ∫ x, r x - 1 ∂μ = 0 := by
    rw [integral_sub (integrable_cont cr) (integrable_const _), ir]
    simp
  have hd : (∫ x, h x ∂binghamKA n K B) - Bv = ∫ x, (r x - 1) * u x ∂μ := by
    have hp : (fun x => (r x - 1) * u x) =
        (fun x => (h x * r x - h x) - Bv * (r x - 1)) := by
      funext x
      dsimp [u]
      ring
    rw [hp, integral_sub (f := fun x => h x * r x - h x)
      (g := fun x => Bv * (r x - 1)) (ihr.sub ih) (ie.const_mul _),
      integral_sub ihr ih, integral_const_mul, he, transfer h]
    simp [Bv]
  have hb : ∀ᵐ x ∂μ, |(r x - 1) * u x| ≤ η * |u x| := by
    filter_upwards [hs] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
  have ha : |∫ x, (r x - 1) * u x ∂μ| ≤ η * ∫ x, |u x| ∂μ := by
    calc
      _ ≤ ∫ x, |(r x - 1) * u x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, η * |u x| ∂μ := integral_mono_ae ieu.abs (iu.abs.const_mul _) hb
      _ = _ := integral_const_mul _ _
  let a := ∫ x, |u x| ∂μ
  have ha0 : 0 ≤ a := integral_nonneg (fun _ => abs_nonneg _)
  have hv : a ^ 2 ≤ ∫ x, u x ^ 2 ∂μ := by
    have hp : (fun x => (|u x| - a) ^ 2) =
        (fun x => (u x ^ 2 - (2 * a) * |u x|) + a ^ 2) := by
      funext x
      nlinarith [sq_abs (u x)]
    have hi2 : Integrable (fun x => u x ^ 2) μ := integrable_cont (cu.pow 2)
    have hh : 0 ≤ ∫ x, (|u x| - a) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
    rw [hp, integral_add (f := fun x => u x ^ 2 - (2 * a) * |u x|)
      (g := fun _ => a ^ 2) (hi2.sub (iu.abs.const_mul _)) (integrable_const _),
      integral_sub hi2 (iu.abs.const_mul _), integral_const_mul] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    dsimp [a] at *
    nlinarith
  have hv0 : 0 ≤ ∫ x, u x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hasqrt : a ≤ Real.sqrt (∫ x, u x ^ 2 ∂μ) := by
    nlinarith [Real.sq_sqrt hv0, Real.sqrt_nonneg (∫ x, u x ^ 2 ∂μ)]
  rw [abs_sub_comm, hd]
  exact ha.trans (mul_le_mul_of_nonneg_left hasqrt hη)

/-- **Lemma K′**: `|B_{D(A)} − B_{Q̃}| ≤ η_Q sd_{D(A)}`. -/
theorem surrA_bias (hn : 1 ≤ n) (A B : Matrix (Fin n) (Fin n) ℝ) (c L : ℝ)
    (hsh : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → qA A x = qA B x + c)
    (hr : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → 0 ≤ qA B x ∧ qA B x ≤ L)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (f0 : ℝ) (T : Tens n) (M : CoefIdxD n d → ℝ) :
    |BofQ (binghamA n A) k f0 T M - BofQ (binghamKA n (Kof43 L ε) B) k f0 T M| ≤
      etaQ ε * Real.sqrt (varFQ (binghamA n A) k f0 T M) := by
  rw [binghamA_shift A B c hsh]
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let K := Kof43 L ε
  have hc : Continuous (fun x => taylorExp K (qA B x)) := by
    unfold taylorExp; have := continuous_qA B; fun_prop
  have hge : ∀ᵐ y ∂uniformSphere n, 1 ≤ taylorExp K (qA B y) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with y hy
    exact taylor_ge_one K _ (hr y hy).1
  have hZ : 0 < ZKA n K B := by
    have h := integral_mono_ae (integrable_const (1 : ℝ)) (sphere_cont_integrable hn hc) hge
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact zero_lt_one.trans_le h
  exact bias_from_ratioA hn B K (etaQ ε) (etaQ_pos hε).le (hge.mono fun x hx => zero_le_one.trans hx)
    hZ (surrogate_ratioA hn B L hr ε hε) (fun x => fval k f0 T (mapMD M x))
    (continuous_fval_map k f0 T M)

end BstLean.Part50
