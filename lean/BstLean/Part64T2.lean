import BstLean.Part56T2
import BstLean.Part64Radial

/-!
# Part 64: Prop T2′ with explicit constants (copy of `Part56T2` with the witnesses stated)

* `momentBudget64 k L`, `CW64 k L = (k+1) · momentBudget64 k L`: `raw_gaussian_moment64`.
* `CA64 d k = CW64 k (d+1)`: `gauss_var64`.
* `CM64 d k = k · CR64 k · CA64 d k`: `defect_moment64`.
* `C2T2_64 d k tsb cL = 2 · CM64 d k · d!/((tsb/4) cL)`, `n2T2_64 CD nL = max (max nL 40) (⌈8|CD|⌉₊ + 2)`:
  `propT2_64_of : PropT2_56 d k C p (tsb/4) (C2T2_64 d k tsb cL) (n2T2_64 CD nL)`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM colM contr frob Tens TSymm fval varU sdU uJ Pcal IsSymmT)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part50 (qA)
open BstLean.Part53 (sg linZ nsq LemmaR53 GaussPolar53 LemmaW53 LemmaTr53)
open BstLean.Part53 (fvA heatA tinner wpair)
open BstLean.Part53.T2Aux
open BstLean.Part56

variable {n d : ℕ}

private lemma singleFamily_at (j : ℕ) (U : (Fin j → Fin n) → ℝ) :
    singleFamily j U j = U := by
  funext w
  simp [singleFamily]

private lemma singleFamily_off (j c : ℕ) (U : (Fin j → Fin n) → ℝ) (h : c ≠ j) :
    singleFamily j U c = 0 := by
  funext w
  simp [singleFamily, h]

private lemma singleFamily_symm (j : ℕ) (U : (Fin j → Fin n) → ℝ)
    (hU : IsSymmT U) : ∀ c, IsSymmT (singleFamily j U c) := by
  intro c
  by_cases hc : c = j
  · subst c
    rw [singleFamily_at]
    exact hU
  · rw [singleFamily_off j c U hc]
    intro σ w
    rfl

private lemma singleFamily_eval (k j : ℕ) (hj : j ≤ k)
    (U : (Fin j → Fin n) → ℝ) (y : Fin n → ℝ) :
    fvA k (singleFamily j U) y = contr U (fun _ => y) := by
  classical
  unfold fvA
  rw [Finset.sum_eq_single j]
  · rw [singleFamily_at]
  · intro c _ hc
    rw [singleFamily_off j c U hc]
    simp [contr]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private lemma singleFamily_frob (j c : ℕ) (U : (Fin j → Fin n) → ℝ) :
    frob (singleFamily j U c) = if c = j then frob U else 0 := by
  by_cases hc : c = j
  · subst c
    simp [singleFamily_at]
  · rw [singleFamily_off j c U hc, if_neg hc]
    simp [frob]

private lemma heatWeight_scale (v : ℝ) (c i : ℕ) :
    heatWeight v c i = v ^ i * heatWeight 1 c i := by
  unfold heatWeight
  rw [show v / 2 = v * (1 / 2) by ring, mul_pow]
  ring

noncomputable def momentBudget64 (k : ℕ) (L : ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
    (c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)

private lemma momentBudget64_nonneg (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    0 ≤ momentBudget64 k L := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity


/-- The explicit Gaussian moment constant `CW64 k L = (k+1) · momentBudget64 k L`. -/
noncomputable def CW64 (k : ℕ) (L : ℝ) : ℝ := (k + 1 : ℕ) * momentBudget64 k L

lemma CW64_nonneg (k : ℕ) (L : ℝ) (hL : 0 ≤ L) : 0 ≤ CW64 k L :=
  mul_nonneg (Nat.cast_nonneg _) (momentBudget64_nonneg k L hL)

/-- `Part53T2_WickMoment.raw_gaussian_moment` with the explicit constant `CW64 k L`. -/
lemma raw_gaussian_moment64 (k : ℕ) (hW : LemmaW53 k) (hTr : LemmaTr53)
    (L : ℝ) (hL : 0 ≤ L) :
    ∀ (n d j : ℕ), 1 ≤ n → j ≤ k →
      ∀ (U : (Fin j → Fin n) → ℝ), IsSymmT U →
      ∀ (ψ : Mono n d → ℝ), nsq ψ ≤ L →
      Integrable (fun Z => contr U (fun _ => linZ Z ψ) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, contr U (fun _ => linZ Z ψ) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
        CW64 k L * (n : ℝ) ^ (j / 2) * frob U := by
  unfold CW64
  classical
  intro n d j hn hj U hU ψ hψ
  let A := singleFamily j U
  let u := nsq ψ
  have hu : 0 ≤ u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hi, he⟩ := hW n d 1 A A (singleFamily_symm j U hU)
    (singleFamily_symm j U hU) ψ ψ
  have hself : (fun Z => fvA k A ((1 : ℝ) • linZ Z ψ) * fvA k A ((1 : ℝ) • linZ Z ψ)) =
      fun Z => contr U (fun _ => linZ Z ψ) ^ 2 := by
    funext Z
    simp only [one_smul, A, singleFamily_eval k j hj, pow_two]
  have hi' : Integrable (fun Z => contr U (fun _ => linZ Z ψ) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
    exact hself ▸ hi
  have he' : (∫ Z, contr U (fun _ => linZ Z ψ) ^ 2 ∂stdGauss (CoefIdxD n d)) =
      wpair k 1 A A ψ ψ := by
    calc
      _ = ∫ Z, fvA k A ((1 : ℝ) • linZ Z ψ) * fvA k A ((1 : ℝ) • linZ Z ψ)
          ∂stdGauss (CoefIdxD n d) := congrArg (fun f => ∫ Z, f Z ∂stdGauss (CoefIdxD n d)) hself.symm
      _ = _ := he
  refine ⟨hi', ?_⟩
  rw [he']
  have hup : ∑ p, ψ p * ψ p = u := by simp [u, nsq, pow_two]
  have hinner (c : ℕ) : tinner (heatA k u A c) (heatA k u A c) =
      frob (heatA k u A c) := by simp [tinner, frob, pow_two]
  simp only [wpair, one_pow, mul_one, one_mul]
  rw [show nsq ψ = u from rfl]
  simp_rw [hup]
  simp_rw [hinner]
  let F := (n : ℝ) ^ (j / 2) * frob U
  have hF : 0 ≤ F := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hterm (c i : ℕ) :
      (c.factorial : ℝ) * u ^ c *
        (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) ≤
      ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F := by
    by_cases hij : c + 2 * i = j
    · rw [show frob (A (c + 2 * i)) = frob U by simp [A, singleFamily_frob, hij],
        heatWeight_scale, mul_pow]
      have hiJ : i ≤ j / 2 := by omega
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hp := pow_le_pow_right₀ hnR hiJ
      have huL := pow_le_pow_left₀ hu hψ (c + 2 * i)
      calc
        _ = ((c.factorial : ℝ) * heatWeight 1 c i ^ 2) *
            u ^ (c + 2 * i) * ((n : ℝ) ^ i * frob U) := by
          rw [pow_add, pow_mul]
          ring
        _ ≤ ((c.factorial : ℝ) * heatWeight 1 c i ^ 2) *
            L ^ (c + 2 * i) * F := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left huL (by positivity)
          · exact mul_le_mul_of_nonneg_right hp
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          · positivity
    · simp only [A, singleFamily_frob, if_neg hij, mul_zero]
      positivity
  have hsum (c : ℕ) :
      (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        (c.factorial : ℝ) * u ^ c *
          (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)))) ≤
      ∑ i ∈ Finset.range (k + 1),
        ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F := by
    have hs : (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F) ≤
        ∑ i ∈ Finset.range (k + 1),
          ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    exact (Finset.sum_le_sum (fun i _ => hterm c i)).trans hs
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * u ^ c *
        ((k + 1 : ℕ) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
          heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) := by
      apply Finset.sum_le_sum
      intro c _
      have hb := frob_heatA_bound k c u A hTr
      calc
        _ = ((c.factorial : ℝ) * u ^ c) * frob (heatA k u A c) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb
          (show 0 ≤ (c.factorial : ℝ) * u ^ c by positivity)
    _ = (k + 1 : ℕ) * ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
          (c.factorial : ℝ) * u ^ c *
            (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (k + 1 : ℕ) * ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (k + 1),
          ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hsum c)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← Finset.sum_mul, momentBudget64, F]
      ring

private lemma map_linear64 (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
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


/-- The explicit angular Gaussian constant `CA64 d k = CW64 k (d+1)`. -/
noncomputable def CA64 (d k : ℕ) : ℝ := CW64 k ((d : ℝ) + 1)

private lemma gauss_var64 (d k : ℕ) (hd : 1 ≤ d) :
    0 ≤ CA64 d k ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (T : Tens n), TSymm k T →
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
      (sg n d) ^ (2 * j) * (∫ Z, varU μ (uJ T j Z) ∂stdGauss (CoefIdxD n d)) ≤
        CA64 d k * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) := by
  have hbW := raw_gaussian_moment64 k (BstLean.Part53.lemmaW53 k)
    BstLean.Part53.lemmaTr53 (d + 1) (by positivity)
  have hCW : 0 ≤ CA64 d k := CW64_nonneg k _ (by positivity)
  refine ⟨hCW, ?_⟩
  set CW := CA64 d k with hCWdef
  unfold CA64 at hCWdef
  rw [← hCWdef] at hbW
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
        simpa only [uJ, map_linear64] using h)
    simpa using hb
  have hsg : 0 ≤ sg n d := by unfold sg; positivity
  calc
    _ ≤ (sg n d) ^ (2 * j) * (CW * (n : ℝ) ^ (j / 2) * frob (T j)) :=
      mul_le_mul_of_nonneg_left (hv.trans hraw) (pow_nonneg hsg _)
    _ = CW * (n : ℝ) ^ (j / 2) * (frob (T j) / DD n d ^ j) := by
      rw [sg_pow_even n d j hn]
      ring

private lemma defect_square_le64 (μ : Measure (Fin n → ℝ)) (k : ℕ) (T : Tens n)
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

private lemma radial_variance_product64 (hP : GaussPolar53) (μ : Measure (Fin n → ℝ))
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


/-- The explicit defect constant `CM64 d k = k · CR64 k · CA64 d k`. -/
noncomputable def CM64 (d k : ℕ) : ℝ := (k : ℝ) * CR64 k * CA64 d k

private lemma defect_moment64 (d k : ℕ) (hd : 1 ≤ d) (hP : GaussPolar53) :
    0 ≤ CM64 d k ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (μ : Measure (Fin n → ℝ)), SphLaw n μ → ∀ (T : Tens n), TSymm k T →
      (∫⁻ Z, ENNReal.ofReal (radialDefect μ k T (unitOfD Z) (radialScale n d Z) ^ 2)
        ∂stdGauss (CoefIdxD n d)) ≤
        ENNReal.ofReal (CM64 d k * (n : ℝ) ^ (k / 2) / DD n d * Ssum56 n d k T) := by
  have hbR := radialScale_uniform_second_moment64 k
  have hCR := CR64_nonneg k
  obtain ⟨hCA, hbA⟩ := gauss_var64 d k hd
  set CR := CR64 k with hCRdef
  set CA := CA64 d k with hCAdef
  refine ⟨by unfold CM64; rw [← hCRdef, ← hCAdef]; positivity, fun n hn μ hμ T hT => ?_⟩
  unfold CM64
  rw [← hCRdef, ← hCAdef]
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
    rw [radial_variance_product64 hP μ hμ hn T j hi]
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
      lintegral_mono fun Z => ENNReal.ofReal_le_ofReal (defect_square_le64 μ k T Z)
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

private lemma qA_rk1_T2_64 (t : ℝ) (v x : Fin n → ℝ) : qA (rk1 t v) x = t * (∑ i, v i * x i) ^ 2 := by
  unfold qA rk1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma DD_lower64 (n d : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ (d + 1) / (d.factorial : ℝ) ≤ DD n d := by
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


/-- The explicit T2 constant `C₂ = 2 · CM64 d k · d!/((tsb/4) · cL)`. -/
noncomputable def C2T2_64 (d k : ℕ) (tsb cL : ℝ) : ℝ :=
  2 * CM64 d k * (d.factorial : ℝ) / (tsb / 4 * cL)

/-- The explicit T2 threshold `max (max nL 40) (⌈8|CD|⌉₊ + 2)`. -/
noncomputable def n2T2_64 (CD : ℝ) (nL : ℕ) : ℕ := max (max nL 40) (⌈8 * |CD|⌉₊ + 2)

/-- **Prop T2′** with explicit constants. -/
theorem propT2_64_of (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (C p tsb : ℝ) (hSB : SBLevel (2 * k) p tsb)
    (htsb : 0 < tsb) (hP : GaussPolar53) (_hE : PropRKGErr56 d k) (hF : PropRKGFloor56 d k)
    (CD : ℝ) (hD : PropD56 d CD) (cL : ℝ) (nL : ℕ) (hcL : 0 < cL) (hL : PropLow56 d k C cL nL) :
    PropT2_56 d k C p (tsb / 4) (C2T2_64 d k tsb cL) (n2T2_64 CD nL) := by
  have hd : 1 ≤ d := by omega
  have hM := (defect_moment64 d k hd hP).2
  have hCM := (defect_moment64 d k hd hP).1
  set CM := CM64 d k with hCMdef
  set s := tsb / 4 with hsdef
  have hs : 0 < s := by positivity
  set C2 : ℝ := 2 * CM * (d.factorial : ℝ) / (s * cL) with hC2
  show PropT2_56 d k C p (tsb / 4) (C2T2_64 d k tsb cL) (n2T2_64 CD nL)
  rw [show C2T2_64 d k tsb cL = C2 by rw [hC2, hsdef, hCMdef]; rfl]
  unfold n2T2_64
  have hC20 : 0 ≤ C2 := by positivity
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
    have hDl := DD_lower64 n d hn1
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

end BstLean.Part64
