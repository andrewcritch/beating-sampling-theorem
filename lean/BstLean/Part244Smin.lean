import BstLean.Part244Net

/-! Part 244: **the Davidson–Szarek lower bound for the mean smallest singular value** from
Gordon's comparison. For an `N × d` matrix with independent `N(0, v)` entries,
`E s_min ≥ √v (E|g_N| - √d)`, where `g_N` is a standard Gaussian vector of `ℝ^N`. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg e0 gaussMat measurable_ofFlat)
open BstLean.Part152 (opN opN_nonneg mulVec_le_opN dot_le_norm bil_flat coord_sq sqrt_le_half
  tensor_inc opN_mean_le opN_mean_std integrable_dot opN_continuous)
open BstLean.Part153 (nrm nrm_nonneg)
open BstLean.Part208 (minStretch minStretch_le minStretch_continuous minStretch_nonneg)

/-- The Gaussian norm mean `a_N = E|g_N|`. -/
noncomputable def gaussNormMean (N : ℕ) : ℝ := ∫ g, nrm g ∂stdGauss (Fin N)

lemma minmax_integrable_gen {κ I J : Type} [Fintype κ] [Fintype I] [Fintype J] [Nonempty I]
    [Nonempty J] (c : I × J → κ → ℝ) :
    Integrable (fun ζ : κ → ℝ => minmax (fun s => c s ⬝ᵥ ζ)) (stdGauss κ) := by
  have hm : Measurable fun ζ : κ → ℝ => minmax (fun s => c s ⬝ᵥ ζ) := by
    unfold minmax
    have hrow : ∀ i ∈ (Finset.univ : Finset I), Continuous fun ζ : κ → ℝ =>
        Finset.univ.sup' Finset.univ_nonempty (fun j => c (i, j) ⬝ᵥ ζ) := by
      intro i _
      exact Continuous.finset_sup'_apply Finset.univ_nonempty fun j _ =>
        continuous_const.dotProduct continuous_id
    exact (Continuous.finset_inf'_apply Finset.univ_nonempty hrow).measurable
  exact Integrable.mono' (integrable_finsetSum _ fun s _ => (integrable_dot (c s)).abs)
    hm.aestronglyMeasurable (ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs]; exact minmax_abs_le _)

lemma nrm_le_half {d : ℕ} (hd : 1 ≤ d) (h : Fin d → ℝ) :
    nrm h ≤ (∑ i, h i ^ 2 + d) / (2 * √(d : ℝ)) :=
  sqrt_le_half (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by exact_mod_cast hd)

lemma nrm_measurable {ι : Type} [Fintype ι] : Measurable (fun g : ι → ℝ => nrm g) := by
  unfold nrm normSq; fun_prop

lemma nrm_integrable {ι : Type} [Fintype ι] : Integrable (fun g : ι → ℝ => nrm g) (stdGauss ι) := by
  refine Integrable.mono' ((integrable_finsetSum Finset.univ fun i _ =>
    (coord_sq (κ := ι) i).1).add (integrable_const (1 : ℝ))) nrm_measurable.aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
  unfold nrm normSq
  have h0 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  show √(∑ i, g i ^ 2) ≤ ∑ i, g i ^ 2 + 1
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (∑ i, g i ^ 2), sq_nonneg (√(∑ i, g i ^ 2) - 1)]

/-- `E|h| ≤ √d` for a standard Gaussian vector of `ℝ^d`. -/
lemma nrm_mean_le {d : ℕ} (hd : 1 ≤ d) : ∫ h, nrm h ∂stdGauss (Fin d) ≤ √(d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have i1 : Integrable (fun h : Fin d → ℝ => ∑ i, h i ^ 2) (stdGauss (Fin d)) :=
    integrable_finsetSum _ fun i _ => (coord_sq i).1
  have I1 : ∫ h : Fin d → ℝ, ∑ i, h i ^ 2 ∂stdGauss (Fin d) = d := by
    rw [integral_finsetSum _ fun i _ => (coord_sq i).1]
    simp [(coord_sq _).2]
  have j1 : Integrable (fun h : Fin d → ℝ => (∑ i, h i ^ 2 + d) / (2 * √(d : ℝ)))
      (stdGauss (Fin d)) := (i1.add (integrable_const _)).div_const _
  have J1 : ∫ h : Fin d → ℝ, (∑ i, h i ^ 2 + d) / (2 * √(d : ℝ)) ∂stdGauss (Fin d) = √d := by
    rw [integral_div, integral_add i1 (integrable_const _), I1, integral_const]
    simp only [probReal_univ, one_smul]
    rw [div_eq_iff (by positivity)]
    nlinarith [Real.sq_sqrt hdR.le]
  rw [← J1]
  exact integral_mono nrm_integrable j1 fun h => nrm_le_half hd h

/-- The quantitative step at net radius `ε`. -/
theorem minStretch_mean_step {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v : ℝ} (hv : 0 ≤ v)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    √v * ((1 - ε) * gaussNormMean N - √(d : ℝ)) - ε * (√v * (√(N : ℝ) + √(d : ℝ))) ≤
      ∫ M, minStretch M ∂gaussMat N d v := by
  classical
  obtain ⟨V, hV, hVnet⟩ := exists_net hd hε
  obtain ⟨U, hU, hUnet⟩ := exists_net hN hε
  haveI : Nonempty V := hV.coe_sort
  haveI : Nonempty U := hU.coe_sort
  -- the Gaussian vector and its blocks
  let rG : (((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ) → (Fin N × Fin d → ℝ) := fun ζ x => ζ (Sum.inl x)
  let rg : (((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ) → (Fin N → ℝ) := fun ζ r => ζ (Sum.inr (Sum.inl r))
  let rh : (((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ) → (Fin d → ℝ) := fun ζ c => ζ (Sum.inr (Sum.inr c))
  have hsplit := measurePreserving_sumPiEquivProdPi (fun _ : ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) => gaussianReal 0 1)
  have hsplit2 := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin N ⊕ Fin d => gaussianReal 0 1)
  have hpG : MeasurePreserving rG (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) (stdGauss (Fin N × Fin d)) :=
    (measurePreserving_fst (μ := stdGauss (Fin N × Fin d))
      (ν := stdGauss (Fin N ⊕ Fin d))).comp hsplit
  have hpR : MeasurePreserving (fun ζ : ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ => fun y => ζ (Sum.inr y)) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)))
      (stdGauss (Fin N ⊕ Fin d)) :=
    (measurePreserving_snd (μ := stdGauss (Fin N × Fin d))
      (ν := stdGauss (Fin N ⊕ Fin d))).comp hsplit
  have hpg : MeasurePreserving rg (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) (stdGauss (Fin N)) :=
    ((measurePreserving_fst (μ := stdGauss (Fin N)) (ν := stdGauss (Fin d))).comp hsplit2).comp
      hpR
  have hph : MeasurePreserving rh (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) (stdGauss (Fin d)) :=
    ((measurePreserving_snd (μ := stdGauss (Fin N)) (ν := stdGauss (Fin d))).comp hsplit2).comp
      hpR
  -- the two families
  let Mx : (((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ) → Matrix (Fin N) (Fin d) ℝ := fun ζ => Matrix.of fun i j => √v * rG ζ (i, j)
  let a : V × U → ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ := fun s =>
    Sum.elim (fun x : Fin N × Fin d => √v * (s.2.1 x.1 * s.1.1 x.2)) (fun _ => 0)
  let b : V × U → ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) → ℝ := fun s =>
    Sum.elim (fun _ => 0) (Sum.elim (fun r => √v * s.2.1 r) (fun c => √v * s.1.1 c))
  have hadot : ∀ s ζ, a s ⬝ᵥ ζ = s.2.1 ⬝ᵥ Mx ζ *ᵥ s.1.1 := by
    intro s ζ
    have : a s ⬝ᵥ ζ = (fun x : Fin N × Fin d => √v * (s.2.1 x.1 * s.1.1 x.2)) ⬝ᵥ rG ζ := by
      simp [a, rG, dotProduct, Fintype.sum_sum_type]
    rw [this, bil_flat]
  have hbdot : ∀ s ζ, b s ⬝ᵥ ζ = √v * (s.1.1 ⬝ᵥ rh ζ) + √v * (s.2.1 ⬝ᵥ rg ζ) := by
    intro s ζ
    simp only [b, rg, rh, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, zero_add, Finset.mul_sum]
    rw [add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hunitV : ∀ x : V, ∑ j, x.1 j ^ 2 = 1 := fun x => hVnet.1 x.1 x.2
  have hunitU : ∀ u : U, ∑ i, u.1 i ^ 2 = 1 := fun u => hUnet.1 u.1 u.2
  have ea : ∀ s s', ∑ k, (a s k - a s' k) ^ 2 =
      v * ∑ i, ∑ j, (s.2.1 i * s.1.1 j - s'.2.1 i * s'.1.1 j) ^ 2 := by
    intro s s'
    simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
  have eb : ∀ s s', ∑ k, (b s k - b s' k) ^ 2 =
      v * (∑ i, (s.2.1 i - s'.2.1 i) ^ 2 + ∑ j, (s.1.1 j - s'.1.1 j) ^ 2) := by
    intro s s'
    simp only [b, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [← mul_sub, mul_pow, Real.sq_sqrt hv]
  have hG := gordon a b
    (fun s s' => by simp [a, b, dotProduct, Fintype.sum_sum_type])
    (fun s s' h1 => by
      rw [ea, eb, ← h1]
      have e : ∑ i, ∑ j, (s.2.1 i * s.1.1 j - s'.2.1 i * s.1.1 j) ^ 2 =
          ∑ i, (s.2.1 i - s'.2.1 i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have : ∑ j, (s.2.1 i * s.1.1 j - s'.2.1 i * s.1.1 j) ^ 2 =
            (s.2.1 i - s'.2.1 i) ^ 2 * ∑ j, s.1.1 j ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, hunitV, mul_one]
      rw [e]
      simp)
    (fun s s' _ => by
      rw [ea, eb]
      exact mul_le_mul_of_nonneg_left (tensor_inc (hunitU s.2) (hunitU s'.2) (hunitV s.1)
        (hunitV s'.1)) hv)
  -- pointwise upper bound for the `a` side
  have hA : ∀ ζ, minmax (fun s => a s ⬝ᵥ ζ) ≤ minStretch (Mx ζ) + ε * opN (Mx ζ) := by
    intro ζ
    have h1 : minmax (fun s => a s ⬝ᵥ ζ) ≤ V.inf' hV (fun x => nrm (Mx ζ *ᵥ x)) := by
      refine Finset.le_inf' _ _ fun x hx => ?_
      unfold minmax
      refine (Finset.inf'_le _ (Finset.mem_univ (⟨x, hx⟩ : V))).trans ?_
      refine Finset.sup'_le _ _ fun u _ => ?_
      show a (⟨x, hx⟩, u) ⬝ᵥ ζ ≤ _
      rw [hadot]
      have := dot_le_norm (hunitU u) (Mx ζ *ᵥ x)
      exact this
    have h2 := minStretch_ge_net hd hV hε.le hVnet (Mx ζ)
    linarith
  -- pointwise lower bound for the `b` side
  have hB : ∀ ζ, √v * ((1 - ε) * nrm (rg ζ)) - √v * nrm (rh ζ) ≤ minmax (fun s => b s ⬝ᵥ ζ) := by
    intro ζ
    have hsep := minmax_sep_ge (I := V) (J := U) (fun x => √v * (x.1 ⬝ᵥ rh ζ))
      (fun u => √v * (u.1 ⬝ᵥ rg ζ))
    have he : (fun s : V × U => √v * (s.1.1 ⬝ᵥ rh ζ) + √v * (s.2.1 ⬝ᵥ rg ζ)) =
        fun s => b s ⬝ᵥ ζ := funext fun s => (hbdot s ζ).symm
    rw [he] at hsep
    have hinf : -(√v * nrm (rh ζ)) ≤
        Finset.univ.inf' Finset.univ_nonempty (fun x : V => √v * (x.1 ⬝ᵥ rh ζ)) := by
      refine Finset.le_inf' _ _ fun x _ => ?_
      have h1 := abs_dot_le x.1 (rh ζ)
      have hx1 : nrm x.1 = 1 := by
        unfold nrm; rw [hVnet.1 x.1 x.2, Real.sqrt_one]
      rw [hx1, one_mul] at h1
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le h1) (Real.sqrt_nonneg v)
      linarith
    have hsup : √v * ((1 - ε) * nrm (rg ζ)) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun u : U => √v * (u.1 ⬝ᵥ rg ζ)) := by
      obtain ⟨u0, hu0, hu0e⟩ := Finset.exists_mem_eq_sup' hU (fun u => u ⬝ᵥ rg ζ)
      have h1 := net_max_ge hU hUnet hε.le (rg ζ)
      rw [hu0e] at h1
      refine (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg v)).trans ?_
      exact Finset.le_sup' (fun u : U => √v * (u.1 ⬝ᵥ rg ζ)) (Finset.mem_univ ⟨u0, hu0⟩)
    linarith
  -- integrals
  set F : (Fin N × Fin d → ℝ) → ℝ :=
    fun ξ => minStretch (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin N) (Fin d) ℝ) with hF
  set O : (Fin N × Fin d → ℝ) → ℝ :=
    fun ξ => opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin N) (Fin d) ℝ) with hO
  have hFm : Measurable F := (minStretch_continuous hd).measurable.comp (measurable_ofFlat _)
  have hOm : Measurable O := opN_continuous.measurable.comp (measurable_ofFlat _)
  obtain ⟨iO, mO⟩ := opN_mean_std (p := N) (q := d) hv
  have iF : Integrable F (stdGauss (Fin N × Fin d)) := by
    refine Integrable.mono' iO hFm.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (minStretch_nonneg hd _)]
    refine (minStretch_le _ (BstLean.Part130.normSq_e0 hd)).trans ?_
    have h := mulVec_le_opN (Matrix.of fun i j => √v * ξ (i, j) : Matrix (Fin N) (Fin d) ℝ) (e0 d)
    have he : √(∑ j, e0 d j ^ 2) = 1 := by
      have := BstLean.Part130.normSq_e0 hd
      unfold normSq at this; rw [this, Real.sqrt_one]
    rw [he, mul_one] at h
    exact h
  have iFk : Integrable (F ∘ rG) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) := (hpG.integrable_comp hFm.aestronglyMeasurable).2 iF
  have iOk : Integrable (O ∘ rG) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) := (hpG.integrable_comp hOm.aestronglyMeasurable).2 iO
  have IF : ∫ ζ, (F ∘ rG) ζ ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) = ∫ M, minStretch M ∂gaussMat N d v := by
    show ∫ ζ, F (rG ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) = _
    rw [← integral_map hpG.measurable.aemeasurable hFm.aestronglyMeasurable, hpG.map_eq]
    unfold gaussMat
    rw [integral_map (measurable_ofFlat _).aemeasurable
      (minStretch_continuous hd).measurable.aestronglyMeasurable]
  have IO : ∫ ζ, (O ∘ rG) ζ ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) ≤ √v * (√(N : ℝ) + √(d : ℝ)) := by
    show ∫ ζ, O (rG ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) ≤ _
    rw [← integral_map hpG.measurable.aemeasurable hOm.aestronglyMeasurable, hpG.map_eq]
    exact mO
  have ig : Integrable (fun ζ => nrm (rg ζ)) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) :=
    (hpg.integrable_comp nrm_measurable.aestronglyMeasurable).2 nrm_integrable
  have ih : Integrable (fun ζ => nrm (rh ζ)) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) :=
    (hph.integrable_comp nrm_measurable.aestronglyMeasurable).2 nrm_integrable
  have Ig : ∫ ζ, nrm (rg ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) = gaussNormMean N := by
    unfold gaussNormMean
    rw [← hpg.map_eq, integral_map hpg.measurable.aemeasurable nrm_measurable.aestronglyMeasurable]
  have Ih : ∫ ζ, nrm (rh ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) ≤ √(d : ℝ) := by
    have : ∫ ζ, nrm (rh ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) = ∫ h, nrm h ∂stdGauss (Fin d) := by
      rw [← hph.map_eq, integral_map hph.measurable.aemeasurable
        nrm_measurable.aestronglyMeasurable]
    rw [this]; exact nrm_mean_le hd
  have iL : Integrable (fun ζ => √v * ((1 - ε) * nrm (rg ζ)) - √v * nrm (rh ζ)) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) :=
    ((ig.const_mul _).const_mul _).sub (ih.const_mul _)
  have iR : Integrable (fun ζ => minStretch (Mx ζ) + ε * opN (Mx ζ)) (stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d))) :=
    iFk.add (iOk.const_mul ε)
  have step1 := integral_mono iL (minmax_integrable_gen b) hB
  have step2 := integral_mono (minmax_integrable_gen a) iR hA
  have eL : ∫ ζ, (√v * ((1 - ε) * nrm (rg ζ)) - √v * nrm (rh ζ)) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) =
      √v * ((1 - ε) * gaussNormMean N) - √v * ∫ ζ, nrm (rh ζ) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) := by
    rw [integral_sub ((ig.const_mul _).const_mul _) (ih.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul, Ig]
  have eR : ∫ ζ, (minStretch (Mx ζ) + ε * opN (Mx ζ)) ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) =
      ∫ M, minStretch M ∂gaussMat N d v + ε * ∫ ζ, (O ∘ rG) ζ ∂stdGauss ((Fin N × Fin d) ⊕ (Fin N ⊕ Fin d)) := by
    have e0 : (fun ζ => minStretch (Mx ζ) + ε * opN (Mx ζ)) =
        fun ζ => (F ∘ rG) ζ + ε * (O ∘ rG) ζ := rfl
    rw [e0, integral_add iFk (iOk.const_mul ε), integral_const_mul, ← IF]
  rw [eL] at step1
  rw [eR] at step2
  have h1 := mul_le_mul_of_nonneg_left Ih (Real.sqrt_nonneg v)
  have h2 := mul_le_mul_of_nonneg_left IO hε.le
  linarith

/-- **Davidson–Szarek, mean form (Gordon).** `E s_min ≥ √v (E|g_N| - √d)`. -/
theorem minStretch_mean_ge {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) {v : ℝ} (hv : 0 ≤ v) :
    √v * (gaussNormMean N - √(d : ℝ)) ≤ ∫ M, minStretch M ∂gaussMat N d v := by
  have ha0 : 0 ≤ gaussNormMean N := integral_nonneg fun g => nrm_nonneg g
  set C := √v * gaussNormMean N + √v * (√(N : ℝ) + √(d : ℝ)) with hC
  have hC0 : 0 ≤ C := by positivity
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := min 1 (δ / (C + 1)) with hεd
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεC : ε * C ≤ δ := by
    have h1 : ε ≤ δ / (C + 1) := min_le_right _ _
    have h2 : ε * (C + 1) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have h := minStretch_mean_step hN hd hv hε hε1
  have e : √v * ((1 - ε) * gaussNormMean N - √(d : ℝ)) - ε * (√v * (√(N : ℝ) + √(d : ℝ))) =
      √v * (gaussNormMean N - √(d : ℝ)) - ε * C := by rw [hC]; ring
  rw [e] at h
  linarith

end BstLean.Part244
