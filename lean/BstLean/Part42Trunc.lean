import BstLean.Part42Defs
import BstLean.Part37Density
import BstLean.Part37Series

/-!
# Part 42, wave 1: the truncation error (Lemma T, second half) and the choice of `K`

Paper: Lemma T ("`(1−δ_K)N_α ≤ N^{(K)}_α ≤ N_α`, so every computed moment is within `1 ± η`"),
Lemma `choice of K`, and the facts about the spread. Specification:
`delegations/answers/p42-spec-opus.md`. Do not use `native_decide` or `axiom`.

Suggested route. `bingham n θ` has density `e^{Σθᵢxᵢ²}/Z` on the sphere; on the sphere
`Σθᵢxᵢ² = θ_{i0} + Σ bᵢxᵢ²` with `b = bsh θ i0 ≥ 0`, so `E_D h = N_h/N_1` with
`N_h = Σ_k E_σ[h (b·u)^k]/k!` (Tonelli / dominated convergence, `0 ≤ b·u ≤ A`). For an even monomial
`h ≥ 0` every term is `≥ 0` and the tail beyond `K` is `≤ δ_K N_h`; an odd monomial gives `0` on both
sides. Then `|Ñ_h/Ñ_1 − N_h/N_1| ≤ 2δ_K N_h/N_1 ≤ η N_h/N_1`. `deltaK_le`: `K + 1 ≥ e²A ≥ 2A`, so the
tail is at most twice its first term, and `(K+1)! ≥ ((K+1)/e)^{K+1}`.
-/

namespace BstLean.Part42

open MeasureTheory
open BstLean.Part37 (bingham)
open BstLean.Part40 (Mono constM momE momG)

variable {n : ℕ}

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

private lemma exp_sum (s : ℝ) :
    HasSum (fun k : ℕ => s ^ k / (k.factorial : ℝ)) (Real.exp s) := by
  simpa [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp s

private lemma delta_tail (A : ℝ) (K : ℕ) :
    deltaK A K = ∑' k : ℕ, A ^ (k + (K + 1)) / ((k + (K + 1)).factorial : ℝ) := by
  have h := (exp_sum A).summable.sum_add_tsum_nat_add (K + 1)
  rw [(exp_sum A).tsum_eq] at h
  unfold deltaK
  linarith

private lemma taylor_bounds (A s : ℝ) (K : ℕ) (hs : 0 ≤ s) (hsa : s ≤ A) :
    (1 - deltaK A K) * Real.exp s ≤ BstLean.Part37.taylorExp K s ∧
      BstLean.Part37.taylorExp K s ≤ Real.exp s := by
  have hA : 0 ≤ A := hs.trans hsa
  have hd : 0 ≤ deltaK A K := by
    rw [delta_tail]
    exact tsum_nonneg (fun k => by positivity)
  have hds : 0 ≤ deltaK s K := by
    rw [delta_tail]
    exact tsum_nonneg (fun k => by positivity)
  have hle : deltaK s K ≤ deltaK A K := by
    rw [delta_tail, delta_tail]
    exact ((exp_sum s).summable.comp_injective (add_left_injective (K + 1))).tsum_le_tsum
      (fun k => div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsa _) (by positivity))
      ((exp_sum A).summable.comp_injective (add_left_injective (K + 1)))
  have he := Real.one_le_exp hs
  change (1 - deltaK A K) * Real.exp s ≤
    ∑ k ∈ Finset.range (K + 1), s ^ k / (k.factorial : ℝ) ∧ _
  dsimp [deltaK] at hd hds hle
  constructor
  · unfold deltaK
    nlinarith
  · unfold BstLean.Part37.taylorExp; linarith

private lemma nt_integral (hn : 1 ≤ n) (b : Fin n → ℝ) (K : ℕ)
    (h : (Fin n → ℝ) → ℝ) (hc : Continuous h) :
    NT b K h = ∫ x, h x * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x)
      ∂BstLean.Part29.uniformSphere n := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold NT BstLean.Part37.taylorExp
  rw [← integral_finsetSum]
  · congr 1
    funext x
    simp only [Finset.mul_sum, BstLean.Part37.qth, mul_div_assoc]
  · intro k _
    exact sphere_integrable (BstLean.Part29.uniformSphere_ae_sphere n) (by fun_prop)

private lemma shift_ratio (hn : 1 ≤ n) (θ : Fin n → ℝ) (i0 : Fin n)
    (h : (Fin n → ℝ) → ℝ) (_hc : Continuous h) :
    (∫ x, h x ∂bingham n θ) =
      (∫ x, h x * Real.exp (BstLean.Part37.qth (bsh θ i0) x)
        ∂BstLean.Part29.uniformSphere n) / BstLean.Part37.Zth n (bsh θ i0) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have he : (fun x => Real.exp (BstLean.Part37.qth θ x)) =ᵐ[BstLean.Part29.uniformSphere n]
      (fun x => Real.exp (θ i0) * Real.exp (BstLean.Part37.qth (bsh θ i0) x)) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [← Real.exp_add]
    congr 1
    unfold BstLean.Part37.qth bsh
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx, mul_one]
    ring
  have hz : BstLean.Part37.Zth n θ = Real.exp (θ i0) *
      BstLean.Part37.Zth n (bsh θ i0) := by
    unfold BstLean.Part37.Zth
    rw [integral_congr_ae he, integral_const_mul]
  rw [BstLean.Part37.integral_bingham hn θ]
  simp_rw [← mul_div_assoc]
  rw [integral_div, hz]
  have hhe : (fun x => h x * Real.exp (BstLean.Part37.qth θ x)) =ᵐ[BstLean.Part29.uniformSphere n]
      (fun x => Real.exp (θ i0) * (h x * Real.exp (BstLean.Part37.qth (bsh θ i0) x))) := by
    filter_upwards [he] with x hx
    rw [hx]
    ring
  rw [integral_congr_ae hhe, integral_const_mul, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

private lemma nonneg_rel (hn : 1 ≤ n) (θ : Fin n → ℝ) (i0 : Fin n)
    (hmin : ∀ j, θ i0 ≤ θ j) (A : ℝ) (hA : ∀ j, θ j - θ i0 ≤ A)
    (K : ℕ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 2) (hδ : deltaK A K ≤ η / 2)
    (h : (Fin n → ℝ) → ℝ) (hc : Continuous h) (hp : ∀ x, 0 ≤ h x) :
    |NT (bsh θ i0) K h / NT (bsh θ i0) K (fun _ => 1) - ∫ x, h x ∂bingham n θ| ≤
      η * |∫ x, h x ∂bingham n θ| := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let b := bsh θ i0
  let Z := BstLean.Part37.Zth n b
  let H := ∫ x, h x * Real.exp (BstLean.Part37.qth b x) ∂BstLean.Part29.uniformSphere n
  let T := NT b K h
  let U := NT b K (fun _ => 1)
  let δ := deltaK A K
  have hA0 : 0 ≤ A := (sub_nonneg.mpr (hmin i0)).trans (hA i0)
  have hd0 : 0 ≤ δ := by
    dsimp [δ]; rw [delta_tail]; exact tsum_nonneg (fun k => by positivity)
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have hZ : 0 < Z := BstLean.Part37.Zth_pos hn b
  have hH : 0 ≤ H := integral_nonneg (fun x => mul_nonneg (hp x) (Real.exp_pos _).le)
  have bounds (f : (Fin n → ℝ) → ℝ) (fc : Continuous f) (fp : ∀ x, 0 ≤ f x) :
      (1 - δ) * (∫ x, f x * Real.exp (BstLean.Part37.qth b x) ∂BstLean.Part29.uniformSphere n) ≤ NT b K f ∧
      NT b K f ≤ ∫ x, f x * Real.exp (BstLean.Part37.qth b x) ∂BstLean.Part29.uniformSphere n := by
    have hb : ∀ᵐ x ∂BstLean.Part29.uniformSphere n,
        (1 - δ) * (f x * Real.exp (BstLean.Part37.qth b x)) ≤
          f x * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x) ∧
        f x * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x) ≤
          f x * Real.exp (BstLean.Part37.qth b x) := by
      filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      have hq0 : 0 ≤ BstLean.Part37.qth b x := by
        unfold BstLean.Part37.qth b bsh
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (sub_nonneg.mpr (hmin j)) (sq_nonneg _))
      have hqA : BstLean.Part37.qth b x ≤ A := by
        calc
          _ ≤ ∑ j, A * x j ^ 2 := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (hA j) (sq_nonneg _))
          _ = A := by rw [← Finset.mul_sum, hx, mul_one]
      have ht := taylor_bounds A _ K hq0 hqA
      constructor
      · simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left ht.1 (fp x)
      · exact mul_le_mul_of_nonneg_left ht.2 (fp x)
    have hiE : Integrable (fun x => f x * Real.exp (BstLean.Part37.qth b x))
        (BstLean.Part29.uniformSphere n) := sphere_integrable
          (BstLean.Part29.uniformSphere_ae_sphere n) (by unfold BstLean.Part37.qth; fun_prop)
    have hiT : Integrable (fun x => f x * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x))
        (BstLean.Part29.uniformSphere n) := sphere_integrable
          (BstLean.Part29.uniformSphere_ae_sphere n) (by unfold BstLean.Part37.qth BstLean.Part37.taylorExp; fun_prop)
    rw [nt_integral hn b K f fc]
    constructor
    · rw [← integral_const_mul]
      exact integral_mono_ae (hiE.const_mul _) hiT (hb.mono (fun x hx => hx.1))
    · exact integral_mono_ae hiT hiE (hb.mono (fun x hx => hx.2))
  have hT : (1 - δ) * H ≤ T ∧ T ≤ H := bounds h hc hp
  have hU : (1 - δ) * Z ≤ U ∧ U ≤ Z := by
    simpa [Z, U, BstLean.Part37.Zth] using bounds (fun _ => 1) continuous_const (fun _ => by norm_num)
  have hU0 : 0 < U := (mul_pos (by linarith : 0 < 1 - δ) hZ).trans_le hU.1
  rw [shift_ratio hn θ i0 h hc]
  change |T / U - H / Z| ≤ η * |H / Z|
  rw [abs_of_nonneg (div_nonneg hH hZ.le), abs_le]
  have hdz : δ ≤ η * (1 - δ) := by dsimp [δ]; nlinarith
  have hT0 : 0 ≤ T := (mul_nonneg (by linarith : 0 ≤ 1 - δ) hH).trans hT.1
  constructor
  · have hgoal : ((1 - η) * H) / Z ≤ T / U := by
      calc
        _ ≤ T / Z := div_le_div_of_nonneg_right (by
          have hdη : δ ≤ η := by dsimp [δ]; linarith
          exact (mul_le_mul_of_nonneg_right (by linarith : 1 - η ≤ 1 - δ) hH).trans hT.1) hZ.le
        _ ≤ T / U := div_le_div_of_nonneg_left hT0 hU0 hU.2
    have heq : ((1 - η) * H) / Z = H / Z - η * (H / Z) := by ring
    rw [heq] at hgoal
    linarith only [hgoal]
  · apply (sub_le_iff_le_add).mpr
    rw [← mul_div_assoc, ← add_div]
    apply (div_le_div_iff₀ hU0 hZ).mpr
    have hZU : Z ≤ (1 + η) * U := by
      have hm := mul_le_mul_of_nonneg_left hU.1 (by linarith : 0 ≤ 1 + η)
      have hd := mul_nonneg (sub_nonneg.mpr hdz) hZ.le
      nlinarith only [hm, hd]
    calc
      T * Z ≤ H * Z := mul_le_mul_of_nonneg_right hT.2 hZ.le
      _ ≤ H * ((1 + η) * U) := mul_le_mul_of_nonneg_left hZU hH
      _ = (η * H + H) * U := by ring

private lemma product_rel (hn : 1 ≤ n) (θ : Fin n → ℝ) (i0 : Fin n)
    (hmin : ∀ j, θ i0 ≤ θ j) (A : ℝ) (hA : ∀ j, θ j - θ i0 ≤ A)
    (K : ℕ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 2) (hδ : deltaK A K ≤ η / 2)
    (r : ℕ) (τ : Fin r → Fin n) :
    |NT (bsh θ i0) K (fun x => ∏ s, x (τ s)) /
        NT (bsh θ i0) K (fun _ => 1) - ∫ x, ∏ s, x (τ s) ∂bingham n θ| ≤
      η * |∫ x, ∏ s, x (τ s) ∂bingham n θ| := by
  classical
  by_cases ho : ∃ i, Odd (Finset.univ.filter (fun s => τ s = i)).card
  · have := BstLean.Part29.uniformSphere_isProbability n hn
    let b := bsh θ i0
    have hA0 : 0 ≤ A := (sub_nonneg.mpr (hmin i0)).trans (hA i0)
    have hb (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) : |BstLean.Part37.qth b x| ≤ A := by
      have hq0 : 0 ≤ BstLean.Part37.qth b x := by
        unfold BstLean.Part37.qth b bsh
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (sub_nonneg.mpr (hmin j)) (sq_nonneg _))
      rw [abs_of_nonneg hq0]
      calc
        _ ≤ ∑ j, A * x j ^ 2 := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hA j) (sq_nonneg _))
        _ = A := by rw [← Finset.mul_sum, hx, mul_one]
    have hs : HasSum (fun k : ℕ => ∫ x, (∏ s, x (τ s)) *
        (BstLean.Part37.qth b x ^ k / (k.factorial : ℝ)) ∂BstLean.Part29.uniformSphere n)
        (∫ x, (∏ s, x (τ s)) * Real.exp (BstLean.Part37.qth b x)
          ∂BstLean.Part29.uniformSphere n) := by
      apply hasSum_integral_of_dominated_convergence
        (fun k x => |∏ s, x (τ s)| * (A ^ k / (k.factorial : ℝ)))
      · intro k
        exact (sphere_integrable (BstLean.Part29.uniformSphere_ae_sphere n)
          (by unfold BstLean.Part37.qth; fun_prop)).aestronglyMeasurable
      · intro k
        filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
          abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ))]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hb x hx) k)
            (by positivity)) (abs_nonneg _)
      · exact Filter.Eventually.of_forall (fun x => (exp_sum A).summable.mul_left _)
      · simp_rw [tsum_mul_left, (exp_sum A).tsum_eq]
        exact (sphere_integrable (BstLean.Part29.uniformSphere_ae_sphere n)
          (by fun_prop)).mul_const _
      · exact Filter.Eventually.of_forall (fun x => (exp_sum (BstLean.Part37.qth b x)).mul_left _)
    have hz (k : ℕ) : (∫ x, (∏ s, x (τ s)) *
        (BstLean.Part37.qth b x ^ k / (k.factorial : ℝ)) ∂BstLean.Part29.uniformSphere n) = 0 := by
      simp_rw [← mul_div_assoc, integral_div,
        BstLean.Part37.sphere_odd_moment hn b r τ k ho, zero_div]
    have htrue : (∫ x, ∏ s, x (τ s) ∂bingham n θ) = 0 := by
      rw [shift_ratio hn θ i0 _ (by fun_prop)]
      simp_rw [hz] at hs
      rw [hs.unique hasSum_zero, zero_div]
    have hnt : NT b K (fun x => ∏ s, x (τ s)) = 0 := by
      unfold NT
      apply Finset.sum_eq_zero
      intro k _
      simpa only [BstLean.Part37.qth, mul_div_assoc] using hz k
    change |NT b K _ / NT b K _ - _| ≤ _
    rw [hnt, htrue]
    simp
  · apply nonneg_rel hn θ i0 hmin A hA K η hη0 hη hδ _ (by fun_prop)
    intro x
    rw [← Finset.prod_fiberwise' Finset.univ τ x]
    apply Finset.prod_nonneg
    intro i _
    rw [Finset.prod_const]
    exact (Nat.not_odd_iff_even.mp (fun h => ho ⟨i, h⟩)).pow_nonneg (x i)

private lemma phi_product (p : Mono n) : ∃ r : ℕ, ∃ τ : Fin r → Fin n,
    BstLean.Part40.phi p = (fun x => ∏ s, x (τ s)) := by
  rcases p with u | i | p
  · refine ⟨0, Fin.elim0, ?_⟩
    funext x
    simp [BstLean.Part40.phi]
  · refine ⟨1, fun _ => i, ?_⟩
    funext x
    simp [BstLean.Part40.phi]
  · refine ⟨2, ![p.1.1, p.1.2], ?_⟩
    funext x
    simp [BstLean.Part40.phi, Fin.prod_univ_two]

/-- **Lemma T (truncation).** Every truncated ratio is within the relative factor `1 ± η`. -/
theorem trunc_rel (hn : 2 ≤ n) (θ : Fin n → ℝ) (i0 : Fin n) (hmin : ∀ j, θ i0 ≤ θ j) (A : ℝ)
    (hA : ∀ j, θ j - θ i0 ≤ A) (K : ℕ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hδ : deltaK A K ≤ η / 2) :
    (∀ p q : Mono n, |momGT (bsh θ i0) K p q - momG (bingham n θ) p q| ≤
        η * |momG (bingham n θ) p q|) ∧
    ∀ p : Mono n, |momET (bsh θ i0) K p - momE (bingham n θ) p| ≤ η * |momE (bingham n θ) p| := by
  have hn1 : 1 ≤ n := by omega
  constructor
  · intro p q
    obtain ⟨r, τ, hp⟩ := phi_product p
    obtain ⟨s, υ, hq⟩ := phi_product q
    have he : (fun x => BstLean.Part40.phi p x * BstLean.Part40.phi q x) =
        (fun x => ∏ t : Fin (r + s), x (Fin.append τ υ t)) := by
      funext x
      rw [hp, hq, Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    unfold momGT momG
    rw [he]
    exact product_rel hn1 θ i0 hmin A hA K η hη0 hη hδ (r + s) (Fin.append τ υ)
  · intro p
    obtain ⟨r, τ, hp⟩ := phi_product p
    unfold momET momE
    rw [hp]
    exact product_rel hn1 θ i0 hmin A hA K η hη0 hη hδ r τ

/-- `S₄ = Σᵢ E_D xᵢ⁴ ≤ 1`. -/
theorem S4_le_one (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    ∑ i, momG (bingham n θ) (sqM i) (sqM i) ≤ 1 := by
  classical
  have := BstLean.Part37.bingham_isProb (by omega : 1 ≤ n) θ
  have hs := BstLean.Part37.bingham_ae_sphere θ
  have hi (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i ^ 4) (bingham n θ) :=
    sphere_integrable hs (by fun_prop)
  have he (i : Fin n) : momG (bingham n θ) (sqM i) (sqM i) =
      ∫ x, x i ^ 4 ∂bingham n θ := by
    unfold momG sqM BstLean.Part40.phi
    congr 1
    funext x
    ring
  simp_rw [he]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have hb : ∀ᵐ x ∂bingham n θ, ∑ i, x i ^ 4 ≤ (1 : ℝ) := by
    filter_upwards [hs] with x hx
    calc
      ∑ i, x i ^ 4 ≤ ∑ i, x i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
        rw [hx] at h
        nlinarith [sq_nonneg (x i)]
      _ = 1 := hx
  simpa using integral_mono_ae (integrable_finsetSum _ (fun i _ => hi i))
    (integrable_const (1 : ℝ)) hb

/-- **The choice of `K`.** -/
theorem deltaK_le (A η : ℝ) (hA : 0 ≤ A) (hη0 : 0 < η) (hη : η ≤ 1 / 2) :
    deltaK A (Kof A η) ≤ η / 2 := by
  let N := ⌈max (Real.exp 2 * A) (Real.log (4 / η))⌉₊
  have hl : 0 < Real.log (4 / η) := Real.log_pos (by
    apply (lt_div_iff₀ hη0).mpr
    linarith)
  have hN0 : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (lt_max_of_lt_right hl)
  have hN : Kof A η + 1 = N := by unfold Kof; change N - 1 + 1 = N; omega
  have hceil : max (Real.exp 2 * A) (Real.log (4 / η)) ≤ (N : ℝ) := Nat.le_ceil _
  have hNA : Real.exp 2 * A ≤ (N : ℝ) := (le_max_left _ _).trans hceil
  have hNL : Real.log (4 / η) ≤ (N : ℝ) := (le_max_right _ _).trans hceil
  have ht (k : ℕ) : A ^ (k + N) / ((k + N).factorial : ℝ) ≤
      Real.exp (-2 * N) * ((Real.exp 2 * A) ^ (k + N) / ((k + N).factorial : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : 1 ≤ Real.exp (-2 * N) * Real.exp ((k + N : ℕ) * 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      push_cast
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
    have hp : 0 ≤ A ^ (k + N) / ((k + N).factorial : ℝ) := by positivity
    calc
      _ ≤ (Real.exp (-2 * N) * Real.exp ((k + N : ℕ) * 2)) *
          (A ^ (k + N) / ((k + N).factorial : ℝ)) := by nlinarith
      _ = _ := by ring
  have hs := (exp_sum (Real.exp 2 * A)).summable
  have htail := hs.sum_add_tsum_nat_add N
  rw [(exp_sum (Real.exp 2 * A)).tsum_eq] at htail
  have htaille : (∑' k : ℕ, (Real.exp 2 * A) ^ (k + N) / ((k + N).factorial : ℝ)) ≤
      Real.exp (Real.exp 2 * A) := by
    have hz : 0 ≤ ∑ k ∈ Finset.range N, (Real.exp 2 * A) ^ k / (k.factorial : ℝ) := by
      positivity
    linarith
  have hbound : deltaK A (Kof A η) ≤ Real.exp (-(N : ℝ)) := by
    rw [delta_tail, hN]
    calc
      _ ≤ ∑' k : ℕ, Real.exp (-2 * N) *
          ((Real.exp 2 * A) ^ (k + N) / ((k + N).factorial : ℝ)) :=
        (exp_sum A).summable.comp_injective (add_left_injective N) |>.tsum_le_tsum ht
          ((hs.comp_injective (add_left_injective N)).mul_left _)
      _ = Real.exp (-2 * N) * ∑' k : ℕ,
          (Real.exp 2 * A) ^ (k + N) / ((k + N).factorial : ℝ) := tsum_mul_left
      _ ≤ Real.exp (-2 * N) * Real.exp (Real.exp 2 * A) :=
        mul_le_mul_of_nonneg_left htaille (Real.exp_pos _).le
      _ = Real.exp (-2 * N + Real.exp 2 * A) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(N : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  apply hbound.trans
  calc
    Real.exp (-(N : ℝ)) ≤ Real.exp (-Real.log (4 / η)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = η / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    _ ≤ η / 2 := by linarith

/-- The spread bounds every difference, and is nonnegative. -/
theorem spread_ge (θ : Fin n → ℝ) (i j : Fin n) : θ j - θ i ≤ spread θ := by
  classical
  unfold spread
  have hi : (⨅ k, θ k) ≤ θ i := ciInf_le (Set.finite_range θ).bddBelow i
  have hj : θ j ≤ ⨆ k, θ k := le_ciSup (Set.finite_range θ).bddAbove j
  linarith

theorem spread_nonneg (hn : 1 ≤ n) (θ : Fin n → ℝ) : 0 ≤ spread θ := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  simpa using spread_ge θ i i

end BstLean.Part42

