import BstLean.Part56Defs
import BstLean.Part53T2
import BstLean.Part53Wick
import BstLean.Part53Elem
import BstLean.Part50Laws

/-!
# Part 56, wave 1: Prop T2′ (floor on the coefficient sphere)

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56T2`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Status: proved (no `sorry`); adapted from `Part53T2.lean` and `Part53T2_Tail.lean`, reusing the
public `Part53T2_*` lemmas (`floor_transfer`, `radial_sd_comparison`, `raw_gaussian_moment`, …).
Proof route (`omRK-opus-prover.md` §6, T2′; copy `Part53T2*.lean` with the floor `s · EV` in place of
`N°/8`): `√V(W) ≥ √V(λW) − Σ_{j≥1} |λ^j − 1| sd_j(W)`; `{V(W) < s EV} ⊆ {V(σZ) < t_sb EV} ∪
{Σ_j |λ^j−1| sd_j(W) ≥ √(s EV)}` with `s = t_sb/4`; the first event by `SBLevel (2k)`
(`V(σZ)` is a nonnegative Gaussian polynomial of degree `≤ 2k`); the second by Markov and polar
independence, with `E|λ^j − 1|² ≤ c_j/P`, the upper bound `E_Z V_j(σZ) ≤ c_j (d+1)^j n^{⌊j/2⌋} ‖T̂_j‖²`,
and the lower bound `EV ≥ (1 − δ) c_L n^{−⌊(k−1)/2⌋} Σ_j ‖T̂_j‖²` (floor part of RK-G, Prop D, `PropLow56`);
the ratio is `≤ C n^{k−1}/P ≤ C₂/n` for `k ≤ d`.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM colM contr frob Tens TSymm fval varU sdU uJ Pcal)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part50 (qA)
open BstLean.Part53 (sg linZ nsq LemmaR53 GaussPolar53 LemmaW53 LemmaTr53)
open BstLean.Part53.T2Aux

variable {n d : ℕ}

private lemma map_linear56 (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    mapMD M x = linZ M (fun p => phiM x p) := by
  classical
  funext a
  unfold mapMD linZ BstLean.Part36.coefD
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    (if h : i < d + 1 then M ⟨⟨i, h⟩, (β, a)⟩ else 0) * BstLean.Part36.monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  simp [colM, phiM, i.2]

/-- `σ^{2j} E_Z Var_μ u_j ≤ C n^{⌊j/2⌋} ‖T_j‖²/𝒟^j`. -/
private lemma gauss_var56 (d k : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (T : Tens n), TSymm k T →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (sg n d) ^ (2 * j) * (∫ Z, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
        C * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) := by
  obtain ⟨CW, hCW, hbW⟩ := raw_gaussian_moment k (BstLean.Part53.lemmaW53 k)
    BstLean.Part53.lemmaTr53 (d + 1) (by positivity)
  refine ⟨CW, hCW, ?_⟩
  intro n hn μ hμ T hT j hj hjk
  let := hμ.prob
  have hv := expected_var_le_raw (d := d) μ hμ hn T j
  have hi := raw_second_expectation_integrable (d := d) μ hμ hn T j
  have hraw : (∫ x, ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2
      ∂stdGauss (CoefIdxD n d) ∂μ) ≤ CW * (n : ℝ) ^ (j / 2) * frob (T j) := by
    have hb := integral_mono_ae hi (integrable_const (CW * (n : ℝ) ^ (j / 2) * frob (T j)))
      (show (fun x => ∫ Z : CoefIdxD n d → ℝ, uJ T j Z x ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ᵐ[μ]
        fun _ => CW * (n : ℝ) ^ (j / 2) * frob (T j) by
        filter_upwards [hμ.sphere] with x hx
        have hphi : nsq (fun p : Mono n d => phiM x p) ≤ (d : ℝ) + 1 :=
          (BstLean.Part43.phiSq_bounds hd x hx).2
        have h := (hbW n d j hn hjk (T j) (hT j hj hjk) _ hphi).2
        simpa only [uJ, map_linear56] using h)
    simpa using hb
  have hsg : 0 ≤ sg n d := by unfold sg; positivity
  calc
    _ ≤ (sg n d) ^ (2 * j) * (CW * (n : ℝ) ^ (j / 2) * frob (T j)) :=
      mul_le_mul_of_nonneg_left (hv.trans hraw) (pow_nonneg hsg _)
    _ = CW * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) := by
      rw [sg_pow_even n d j hn]
      ring

private lemma defect_square_le56 (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
    (Z : CoefIdxD n d → ℝ) :
    radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2 ≤
      (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
        (radialScale n d Z ^ j - 1) ^ 2 * varU μ (uJ T j (unitOfD Z)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
    (f := fun j => |radialScale n d Z ^ j - 1| * sdU μ (uJ T j (unitOfD Z)))
  have hc : (Finset.Icc 1 k).card = k := by simp
  rw [hc] at h
  unfold radialDefect
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow, sq_abs, sdU]
  have hv : 0 ≤ varU μ (uJ T j (unitOfD Z)) := integral_nonneg fun _ => sq_nonneg _
  rw [Real.sq_sqrt hv]

private lemma radial_variance_product56 (hP : GaussPolar53) (μ : Measure (Fin n → ℝ))
    (hμ : SphLaw n μ) (hn : 1 ≤ n) (T : Tens n) (j : ℕ)
    (hi : Integrable (fun Z : CoefIdxD n d → ℝ => (radialScale n d Z ^ j - 1) ^ 2)
      (stdGauss (CoefIdxD n d))) :
    (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2 *
        varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) =
      ENNReal.ofReal (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) *
        ∫⁻ Z, ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d) := by
  let a := fun r : ℝ => ENNReal.ofReal (((r / Real.sqrt (DD n d)) ^ j - 1) ^ 2)
  let b := fun W : CoefIdxD n d → ℝ => ENNReal.ofReal (varU μ (uJ T j W))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hb : Measurable b := (varU_uJ_measurable μ hμ hn T j).ennreal_ofReal
  have hp := polar_product hP a b ha hb
  change (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) *
      ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) ∂stdGauss (CoefIdxD n d)) = _ at hp
  have hm (Z : CoefIdxD n d → ℝ) : ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2 *
      varU μ (uJ T j (unitOfD Z))) = ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) *
      ENNReal.ofReal (varU μ (uJ T j (unitOfD Z))) :=
    ENNReal.ofReal_mul (sq_nonneg _)
  simp_rw [hm]
  rw [hp]
  change (∫⁻ Z, ENNReal.ofReal ((radialScale n d Z ^ j - 1) ^ 2) ∂stdGauss (CoefIdxD n d)) * _ = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun Z => sq_nonneg _)]

/-- `Σ_{j=1}^k ‖T_j‖²/𝒟^j`. -/
noncomputable def Ssum56 (n d k : ℕ) (T : Tens n) : ℝ := ∑ j ∈ Finset.Icc 1 k, frob (T j) / DD n d ^ j

private lemma defect_moment56 (d k : ℕ) (hd : 1 ≤ d) (hP : GaussPolar53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (T : Tens n), TSymm k T →
      (∫⁻ Z, ENNReal.ofReal (radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2)
        ∂stdGauss (CoefIdxD n d)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (k / 2) / DD n d * Ssum56 n d k T) := by
  obtain ⟨CR, hCR, hbR⟩ := radialScale_uniform_second_moment k
  obtain ⟨CA, hCA, hbA⟩ := gauss_var56 d k hd
  refine ⟨(k : ℝ) * CR * CA, by positivity, fun n hn μ hμ T hT => ?_⟩
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let F := fun (j : ℕ) (Z : CoefIdxD n d → ℝ) =>
    (radialScale n d Z ^ j - 1) ^ 2 * varU μ (uJ T j (unitOfD Z))
  have hF0 (j : ℕ) (Z : CoefIdxD n d → ℝ) : 0 ≤ F j Z :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hFm (j : ℕ) : Measurable (fun Z => ENNReal.ofReal (F j Z)) :=
    (((((radialScale_continuous n d).measurable.pow_const j).sub measurable_const).pow_const 2).mul
      ((varU_uJ_measurable μ hμ hn T j).comp measurable_unit)).ennreal_ofReal
  let G := fun j : ℕ => CR / DD n d * (CA * (n : ℝ) ^ (k / 2) * (frob (T j) / DD n d ^ j))
  have hG0 (j : ℕ) : 0 ≤ G j := by
    dsimp [G]; have : 0 ≤ frob (T j) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 k) :
      (∫⁻ Z, ENNReal.ofReal (F j Z) ∂stdGauss (CoefIdxD n d)) ≤ ENNReal.ofReal (G j) := by
    obtain ⟨hi, hb⟩ := hbR n d hn j (Finset.mem_Icc.mp hj).2
    rw [radial_variance_product56 hP μ hμ hn T j hi]
    have h1 := ENNReal.ofReal_le_ofReal hb
    have h2 := (angular_variance_le_gaussian hP μ hμ hn T j).trans
      (ENNReal.ofReal_le_ofReal (hbA n hn μ hμ T hT j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2))
    have h3 : CA * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) ≤
        CA * (n : ℝ) ^ (k / 2) * (frob (T j) / DD n d ^ j) := by
      have : 0 ≤ frob (T j) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnR
        (Nat.div_le_div_right (Finset.mem_Icc.mp hj).2)) hCA
    calc
      _ ≤ ENNReal.ofReal (CR / DD n d) *
          ENNReal.ofReal (CA * (n : ℝ) ^ (k / 2) * (frob (T j) / DD n d ^ j)) := by
        gcongr
        exact h2.trans (ENNReal.ofReal_le_ofReal h3)
      _ = _ := (ENNReal.ofReal_mul (div_nonneg hCR hD.le)).symm
  calc
    _ ≤ ∫⁻ Z, ENNReal.ofReal ((k : ℝ) * ∑ j ∈ Finset.Icc 1 k, F j Z)
        ∂stdGauss (CoefIdxD n d) :=
      lintegral_mono fun Z => ENNReal.ofReal_le_ofReal (defect_square_le56 μ k T Z)
    _ = ENNReal.ofReal (k : ℝ) * ∑ j ∈ Finset.Icc 1 k,
        ∫⁻ Z, ENNReal.ofReal (F j Z) ∂stdGauss (CoefIdxD n d) := by
      simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg k),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => hF0 j _)]
      rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun j _ => hFm j)),
        lintegral_finsetSum _ (fun j _ => hFm j)]
    _ ≤ ENNReal.ofReal (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, ENNReal.ofReal (G j) := by
      gcongr with j hj
      exact hterm j hj
    _ = ENNReal.ofReal ((k : ℝ) * ∑ j ∈ Finset.Icc 1 k, G j) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hG0 j), ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
    _ = _ := by
      congr 1
      dsimp [G, Ssum56]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

private lemma qA_rk1_T2 (t : ℝ) (v x : Fin n → ℝ) : qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  unfold qA rk1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma DD_lower56 (n d : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ (d + 1) / (d.factorial : ℝ) ≤ DD n d := by
  have h := Nat.pow_le_choose (α := ℝ) d (n + d)
  have he : n + d + 1 - d = n + 1 := by omega
  rw [he] at h
  have hc : DD n d = n * ((n + d).choose d : ℝ) := by
    unfold DD; rw [BstLean.Part36.card_coefIdxD]; push_cast; ring
  rw [hc, pow_succ]
  have hnn : (n : ℝ) ^ d ≤ ((n + 1 : ℕ) : ℝ) ^ d := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _); push_cast; linarith
  have hf : (0 : ℝ) < d.factorial := by positivity
  have : (n : ℝ) ^ d / d.factorial ≤ ((n + d).choose d : ℝ) :=
    le_trans (div_le_div_of_nonneg_right hnn hf.le) h
  calc (n : ℝ) ^ d * n / d.factorial = n * ((n : ℝ) ^ d / d.factorial) := by ring
    _ ≤ n * ((n + d).choose d : ℝ) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

/-- **Prop T2′**, from the small-ball level, polar independence, RK-G, Prop D and the lower bound. -/
theorem propT2_56_of (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (C p tsb : ℝ) (hSB : SBLevel (2 * k) p tsb)
    (htsb : 0 < tsb) (hP : GaussPolar53) (_hE : PropRKGErr56 d k) (hF : PropRKGFloor56 d k)
    (CD : ℝ) (hD : PropD56 d CD) (cL : ℝ) (nL : ℕ) (hcL : 0 < cL) (hL : PropLow56 d k C cL nL) :
    ∃ (C2 : ℝ) (n0 : ℕ), PropT2_56 d k C p (tsb / 4) C2 n0 := by
  classical
  have hd : 1 ≤ d := by omega
  obtain ⟨CM, hCM, hM⟩ := defect_moment56 d k hd hP
  set s := tsb / 4 with hsdef
  have hs : 0 < s := by positivity
  set C2 : ℝ := 2 * CM * (d.factorial : ℝ) / (s * cL) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C2, max (max nL 40) (⌈8 * |CD|⌉₊ + 2), ?_⟩
  intro n hn v hv t ht0 ht f0 T hT hTk
  have hnL : nL ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn40 : 40 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnCD : ⌈8 * |CD|⌉₊ + 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set D := lawRK n t v with hDdef
  have hDS : SphLaw n D := (BstLean.Part50.binghamA_antipodal hn1 _).sph
  have := hDS.prob
  have hDpos := BstLean.Part36.DD_pos (d := d) hn1
  -- `S > 0`
  set S := Ssum56 n d k T with hSdef
  have hSpos : 0 < S := by
    refine lt_of_lt_of_le (div_pos hTk (pow_pos hDpos k)) ?_
    exact Finset.single_le_sum (f := fun j => frob (T j) / DD n d ^ j)
      (fun j _ => div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (pow_nonneg hDpos.le _))
      (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
  -- `δ ≤ 1/2`
  set δ := Real.sqrt (deltaSq D d v) with hδ
  have hδhalf : δ ≤ 1 / 2 := by
    have h1 := hD n (by omega) v hv t
    have hn2 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
      have : (40 : ℝ) ≤ n := by exact_mod_cast hn40
      linarith
    have h2 : deltaSq D d v ≤ 1 / 4 := by
      refine h1.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have : (8 * |CD| : ℝ) ≤ ⌈8 * |CD|⌉₊ := Nat.le_ceil _
      have : ((⌈8 * |CD|⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnCD
      push_cast at this
      nlinarith [le_abs_self CD]
    rw [hδ, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h2
  -- the lower bound on `EV`
  set EV := EV56 d D k f0 T with hEV
  set Sf := ∫ Z, Sfl D d k f0 T v (sg n d • Z) ∂stdGauss (CoefIdxD n d) with hSf
  have hfl := hF n D hDS v hv f0 T hT
  have hlow := hL n hnL v hv t ht0 ht f0 T hT
  set m := (n : ℝ) ^ ((k - 1) / 2) with hm
  have hm0 : 0 < m := by positivity
  have hlow' : cL * S / m ≤ Sf := hlow
  have hEVlow : cL * S / (2 * m) ≤ EV := by
    have hSf0 : 0 ≤ Sf := le_trans (by positivity) hlow'
    have : (1 / 2) * Sf ≤ (1 - δ) * Sf := mul_le_mul_of_nonneg_right (by linarith) hSf0
    have e : cL * S / (2 * m) = (1 / 2) * (cL * S / m) := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hlow' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hEVpos : 0 < EV := lt_of_lt_of_le (by positivity) hEVlow
  -- the small-ball event
  have hgauss : stdGauss (CoefIdxD n d) {Z | varFQ D k f0 T (sg n d • Z) < 4 * s * EV} ≤
      ENNReal.ofReal p := by
    obtain ⟨P, hdeg, hPe⟩ := BstLean.Part45.var_poly45 (d := d) hDS k T
    have heq (Z : CoefIdxD n d → ℝ) : MvPolynomial.eval Z P = varFQ D k f0 T (sg n d • Z) := by
      rw [hPe, gaussian_variance_eq D hDS]
    have hnonneg (Z : CoefIdxD n d → ℝ) : 0 ≤ MvPolynomial.eval Z P := by
      rw [hPe]; exact integral_nonneg fun _ => sq_nonneg _
    have hb := hSB (CoefIdxD n d) P hdeg hnonneg
    apply le_trans (measure_mono ?_) hb
    intro Z hZ
    change MvPolynomial.eval Z P < tsb * ∫ Z', MvPolynomial.eval Z' P ∂stdGauss (CoefIdxD n d)
    simp_rw [heq]
    have h4 : 4 * s = tsb := by rw [hsdef]; ring
    rw [← h4]
    exact hZ
  -- the radial tail
  have hsN : 0 < s * EV := mul_pos hs hEVpos
  have hrad : stdGauss (CoefIdxD n d) {Z | Real.sqrt (s * EV) ≤
      radialDefect D k T (unitOfD Z) (radialScale n d Z)} ≤ ENNReal.ofReal (C2 / n) := by
    have hfm := ((radialDefect_measurable (d := d) D hDS hn1 k T).pow_const 2).ennreal_ofReal
    have hsub : {Z : CoefIdxD n d → ℝ | Real.sqrt (s * EV) ≤
          radialDefect D k T (unitOfD Z) (radialScale n d Z)} ⊆
        {Z | ENNReal.ofReal (s * EV) ≤
          ENNReal.ofReal (radialDefect D k T (unitOfD Z) (radialScale n d Z) ^ 2)} := by
      intro Z hZ
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hZ)).mpr hZ
      rw [Real.sq_sqrt hsN.le] at hsq
      exact ENNReal.ofReal_le_ofReal hsq
    apply le_trans (measure_mono hsub)
      ((meas_ge_le_lintegral_div hfm.aemeasurable
        (by simpa using hsN) ENNReal.ofReal_ne_top).trans ?_)
    apply le_trans (ENNReal.div_le_div_right (hM n hn1 D hDS T hT) _)
    rw [← ENNReal.ofReal_div_of_pos hsN]
    apply ENNReal.ofReal_le_ofReal
    -- `CM n^{⌊k/2⌋} S/(𝒟 s EV) ≤ C₂/n`
    have hexp : (n : ℝ) ^ (k / 2) * m = (n : ℝ) ^ (k - 1) := by
      rw [hm, ← pow_add]; congr 1; omega
    have hDl := DD_lower56 n d hn1
    have hf : (0 : ℝ) < d.factorial := by positivity
    have hkey : (n : ℝ) ^ (k - 1) * n ≤ (d.factorial : ℝ) * DD n d := by
      have h1 : (n : ℝ) ^ (k - 1) * n ≤ (n : ℝ) ^ (d + 1) := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hnR1 (by omega)
      have h2 : (n : ℝ) ^ (d + 1) ≤ d.factorial * DD n d := by
        rw [div_le_iff₀ hf] at hDl; linarith
      linarith
    rw [div_le_div_iff₀ hsN hnR]
    -- LHS: CM n^{k/2}/DD * S * n ≤ C2 * (s * EV)
    have hEV2 : cL * S ≤ 2 * m * EV := by
      rw [div_le_iff₀ (by positivity)] at hEVlow; linarith
    rw [hC2]
    rw [show 2 * CM * (d.factorial : ℝ) / (s * cL) * (s * EV) = 2 * CM * d.factorial * EV / cL by
      field_simp]
    rw [le_div_iff₀ hcL]
    have hA : CM * (n : ℝ) ^ (k / 2) / DD n d * S * n * cL =
        CM * ((n : ℝ) ^ (k / 2)) * n * (cL * S) / DD n d := by ring
    rw [hA, div_le_iff₀ hDpos]
    calc CM * (n : ℝ) ^ (k / 2) * n * (cL * S) ≤ CM * (n : ℝ) ^ (k / 2) * n * (2 * m * EV) :=
          mul_le_mul_of_nonneg_left hEV2 (by positivity)
      _ = 2 * CM * EV * ((n : ℝ) ^ (k / 2) * m * n) := by ring
      _ = 2 * CM * EV * ((n : ℝ) ^ (k - 1) * n) := by rw [hexp]
      _ ≤ 2 * CM * EV * ((d.factorial : ℝ) * DD n d) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 * CM * d.factorial * EV * DD n d := by ring
  have hcomp (Z : CoefIdxD n d → ℝ) (hZ : Z ∈ {Z : CoefIdxD n d → ℝ | Z ≠ 0}) :
      Real.sqrt (varFQ D k f0 T (sg n d • Z)) ≤
        Real.sqrt (varFQ D k f0 T (unitOfD Z)) +
          radialDefect D k T (unitOfD Z) (radialScale n d Z) := by
    have h := radial_sd_comparison hDS k f0 T (unitOfD Z) (radialScale n d Z)
    rw [scale_unit Z hZ] at h
    exact h
  have hp := smallball_probability_nonneg (2 * k) (by omega) p tsb hSB htsb
  exact floor_transfer (stdGauss (CoefIdxD n d))
    (fun Z => varFQ D k f0 T (unitOfD Z))
    (fun Z => varFQ D k f0 T (sg n d • Z))
    (fun Z => radialDefect D k T (unitOfD Z) (radialScale n d Z))
    {Z | Z ≠ 0} s EV p (C2 / n) hsN.le hp (by positivity)
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    (fun Z _ => integral_nonneg fun _ => sq_nonneg _)
    hcomp hgauss hrad

end BstLean.Part56
