import BstLean.Part108Defs

/-!
# Part 108, the core: Gaussian `W`, sphere `A`, sphere `F`, relative to the realized spread

`core_gauss`: for the Gaussian versions `(W, A₁, F_G)` (unit coefficient variance) and the `k`
blocks, the failure probability of `Succ W τ_P (phiAF (nrm A₁) (nrm F_G))` (`τ_P = tauOf (2d_A) 1`,
the ideal noise level) is at most the sum of four terms:
1. the lower tail of the spread of the linear part (Cantelli; `part107_tail_num`);
2. the error of the linear part (Markov; `lemmaE`);
3. the terms of degree `≥ 2` of `F` (Markov; `PertBound108`);
4. the radius of `A₁` (Chebyshev for a chi-square).
Every theorem takes the interface statements of `Part108Defs.lean` that it uses as hypotheses.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105
open BstLean.Part107 (qLin X1 PP Full gErr vbar)

/-! ## Bridges -/

section bridge

variable {N n d : ℕ}

lemma Bu_eq (W : CoefIdx N n d → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) :
    ∫ x, φ x ∂muW W = Bu W φ := by
  unfold muW Bu
  exact integral_map (measurable_muMap W).aemeasurable hφ.aestronglyMeasurable

lemma Vu_eq (W : CoefIdx N n d → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) :
    Var[φ; muW W] = Vu W φ := by
  rw [variance_eq_integral hφ.aemeasurable, Bu_eq W hφ]
  unfold muW Vu
  exact integral_map (measurable_muMap W).aemeasurable
    ((hφ.sub measurable_const).pow_const 2).aestronglyMeasurable

lemma measurable_qLin_x {dA : ℕ} (A : CoefIdx n n dA → ℝ) (ℓ : Fin n → ℝ) :
    Measurable (fun x => qLin A ℓ x) :=
  BstLean.Part107.sd_measurable_qLin measurable_const measurable_const measurable_id

lemma X1_eq_Vu {dA : ℕ} (W : CoefIdx N n d → ℝ) (A : CoefIdx n n dA → ℝ) (ℓ : Fin n → ℝ) :
    X1 W A ℓ = Vu W (fun x => qLin A ℓ x) := by
  unfold X1
  exact Vu_eq W (measurable_qLin_x A ℓ)

lemma Vu_nonneg (W : CoefIdx N n d → ℝ) (φ : (Fin n → ℝ) → ℝ) : 0 ≤ Vu W φ :=
  integral_nonneg fun _ => sq_nonneg _

lemma gErr_eq {dA k : ℕ} (σ : ℝ)
    (ω : ((CoefIdx N n d → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) × Draws N n k) :
    gErr σ ω = Err ω.1.1 (tauOf d σ) (fun x => qLin ω.1.2.1 ω.1.2.2 x) ω.2 := by
  unfold gErr Err BstLean.Part107.gProg BstLean.Part107.Bmean BstLean.Part106.gVal
  rw [Bu_eq _ (measurable_qLin_x _ _)]
  congr 1
  rw [one_div, mul_comm, div_eq_mul_inv]
  rfl

lemma c_measurable_bwNormSq {k q d : ℕ} : Measurable (bwNormSq (k := k) (q := q) (d := d)) := by
  unfold bwNormSq bwInner
  fun_prop

lemma c_gmom_nonneg (n j : ℕ) : 0 ≤ gmom n j :=
  integral_nonneg fun _ => by positivity

end bridge

/-! ## Measure tools -/

section tools

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma real_preimage_le {μ : Measure α} [IsFiniteMeasure μ] {f : α → β} (hf : Measurable f)
    (S : Set β) : μ.real (f ⁻¹' S) ≤ (μ.map f).real S :=
  ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_map_apply hf.aemeasurable S)

lemma real_fst_le (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (S : Set α) : (μ.prod ν).real {p | p.1 ∈ S} ≤ μ.real S := by
  have h := real_preimage_le (μ := μ.prod ν) measurable_fst S
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

lemma real_snd_le (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (S : Set β) : (μ.prod ν).real {p | p.2 ∈ S} ≤ ν.real S := by
  have h := real_preimage_le (μ := μ.prod ν) measurable_snd S
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

end tools

/-! ## The space of `(W, (A₁, F))` -/

/-- The coefficient vectors `(W, (A₁, F))` at `r = 2`. -/
abbrev Theta (n dA dF : ℕ) :=
  (CoefIdx (2 * n) n (2 * dA) → ℝ) × ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ))

/-- The Gaussian versions of `(W, (A₁, F))`, unit coefficient variance, independent. -/
noncomputable abbrev GamG (n dA dF : ℕ) : Measure (Theta n dA dF) :=
  (bwGauss (2 * n) n (2 * dA) 1).prod ((bwGauss n n dA 1).prod (bwGauss n 1 dF 1))

/-- `E X₁`: the mean of the realized spread of the linear part (Gaussian versions). -/
noncomputable def Mx1 (n dA : ℕ) : ℝ :=
  ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA 1

/-- The sum of the perturbation bound. -/
noncomputable def Ssum (n dA dF : ℕ) (c2 : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 dF, c2 ^ (j - 1) * ((dA : ℝ) + 1) ^ j * gmom n j

lemma Ssum_nonneg (n dA dF : ℕ) {c2 : ℝ} (hc2 : 0 ≤ c2) : 0 ≤ Ssum n dA dF c2 :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (pow_nonneg hc2 _) (by positivity)) (c_gmom_nonneg n j)

/-- The failure bound of the core (`core_gauss`). -/
noncomputable def coreBound (n dA dF k : ℕ) (θ ι : ℝ) : ℝ :=
  (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) +
    4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) /
      ((1 - lam0 (2 * n) (2 * dA)) * ((1 - ι) ^ 2 * (1 - θ))) +
    34 * Ssum n dA dF (4 / (Fintype.card (CoefIdx n n dA) : ℝ)) /
      (ι ^ 2 * (1 - θ) * ((n : ℝ) * ((dA : ℝ) + 1 - vbar dA n))) +
    32 / (9 * (Fintype.card (CoefIdx n n dA) : ℝ))

/-- The squared relative tolerance for the norm of the Gaussian version of `W`. -/
noncomputable def eps2 (n : ℕ) : ℝ := 4 / (10 ^ 9 * (n : ℝ) ^ 3)

/-- **The explicit failure bound `δ(n, k, θ, ι)` of Theorem W8-S in Lean**: the lower tail of the
spread (Cantelli), the error of the linear part (Markov), the terms of degree `≥ 2` of `F`, and a
remainder (radius of `A`, norm of `W`, the change of the noise level). -/
noncomputable def delta108 (n dA k : ℕ) (θ ι : ℝ) : ℝ :=
  (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) +
    4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) /
      ((1 - lam0 (2 * n) (2 * dA)) * ((1 - ι) ^ 2 * (1 - θ))) +
    10217 / (ι ^ 2 * (1 - θ) * (n : ℝ) ^ 3) +
    (64 / 10 ^ 6 + 1 / (9 * (n : ℝ)))

section core

variable {n dA dF k : ℕ}

lemma measurable_linF (hd : 1 ≤ dF) : Measurable (linF (n := n) hd) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- `(W, (A₁, F)) ↦ (W, (A₁, ℓ))`. -/
def toLin (hd : 1 ≤ dF) (t : Theta n dA dF) :
    (CoefIdx (2 * n) n (2 * dA) → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) :=
  (t.1, (t.2.1, linF hd t.2.2))

lemma measurable_toLin (hd : 1 ≤ dF) : Measurable (toLin (n := n) (dA := dA) hd) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    ((measurable_linF hd).comp (measurable_snd.comp measurable_snd)))

lemma map_toLin (hL : LinLaw108) (hd : 1 ≤ dF) :
    (GamG n dA dF).map (toLin hd) = PP (2 * n) n (2 * dA) dA 1 := by
  have h1 : ((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)).map (Prod.map id (linF hd)) =
      (bwGauss n n dA 1).prod (stdGauss (Fin n)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_linF hd), Measure.map_id, hL n dF hd]
  have h2 : (GamG n dA dF).map (Prod.map id (Prod.map id (linF hd))) =
      PP (2 * n) n (2 * dA) dA 1 := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap (measurable_linF hd)),
      Measure.map_id, h1]
  exact h2

/-- Event 1: the lower tail of the spread of the linear part. -/
lemma e1 (hL : LinLaw108) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hd : 1 ≤ dF) {θ : ℝ}
    (hθ : 0 < θ) :
    (GamG n dA dF).real
        {t | Vu t.1 (fun x => qLin t.2.1 (linF hd t.2.2) x) < (1 - θ) * Mx1 n dA} ≤
      (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) := by
  have h := BstLean.Part107.part107_tail_num n dA 1 hn hdA one_ne_zero hθ
  have h2 := real_preimage_le (μ := GamG n dA dF) (measurable_toLin (n := n) (dA := dA) hd)
    {ω | X1 ω.1 ω.2.1 ω.2.2 < (1 - θ) * ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA 1}
  rw [map_toLin hL hd] at h2
  refine le_trans (le_of_eq ?_) (h2.trans h)
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, toLin, X1_eq_Vu, Mx1]

lemma drawM_prob (N n k : ℕ) (hN : 1 ≤ N) : IsProbabilityMeasure (drawM N n k) := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  infer_instance

/-- Event 2: the error of the linear part. -/
lemma e2 (hL : LinLaw108) (hn : 1 ≤ n) (hdA : 1 ≤ dA) (hd : 1 ≤ dF) (hk : 1 ≤ k) {t : ℝ}
    (ht : 0 < t) (hlam : lam0 (2 * n) (2 * dA) < 1) :
    ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | t < Err p.1.1 (tauOf (2 * dA) 1) (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) p.2 ^ 2} ≤
      (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) * Mx1 n dA / ((1 - lam0 (2 * n) (2 * dA)) * t) := by
  have := drawM_prob (2 * n) n k (by omega)
  obtain ⟨hint, hE⟩ := BstLean.Part107.lemmaE (2 * n) n (2 * dA) dA k 1 (by omega) (by omega) hk
  have hmap : ((GamG n dA dF).prod (drawM (2 * n) n k)).map (Prod.map (toLin hd) id) =
      Full (2 * n) n (2 * dA) dA k 1 := by
    rw [← Measure.map_prod_map _ _ (measurable_toLin hd) measurable_id, Measure.map_id,
      map_toLin hL hd]
  have h2 := real_preimage_le (μ := (GamG n dA dF).prod (drawM (2 * n) n k))
    ((measurable_toLin (n := n) (dA := dA) hd).prodMap measurable_id)
    {ω | t ≤ gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) 1 ω ^ 2}
  rw [hmap] at h2
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (μ := Full (2 * n) n (2 * dA) dA k 1)
    (f := fun ω => gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) 1 ω ^ 2)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint t
  have h1l : 0 < 1 - lam0 (2 * n) (2 * dA) := by linarith
  have hsub : ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | t < Err p.1.1 (tauOf (2 * dA) 1) (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) p.2 ^ 2} ≤
      ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        (Prod.map (toLin hd) id ⁻¹'
          {ω | t ≤ gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) 1 ω ^ 2}) := by
    refine measureReal_mono ?_
    intro p hp
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hp ⊢
    rw [gErr_eq]
    exact hp.le
  refine hsub.trans (h2.trans ?_)
  rw [le_div_iff₀ (by positivity)]
  calc (Full (2 * n) n (2 * dA) dA k 1).real
          {ω | t ≤ gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) 1 ω ^ 2} *
        ((1 - lam0 (2 * n) (2 * dA)) * t)
      = (1 - lam0 (2 * n) (2 * dA)) * (t * (Full (2 * n) n (2 * dA) dA k 1).real
          {ω | t ≤ gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) 1 ω ^ 2}) := by
        ring
    _ ≤ (1 - lam0 (2 * n) (2 * dA)) * ∫ ω, gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA)
          (k := k) 1 ω ^ 2 ∂Full (2 * n) n (2 * dA) dA k 1 :=
        mul_le_mul_of_nonneg_left hmk h1l.le
    _ ≤ _ := hE

/-- Event 4: the radius of `A₁`. -/
lemma e4 (hn : 1 ≤ n) :
    (bwGauss n n dA 1).real
        {A | ¬ (1 ≤ 4 / (Fintype.card (CoefIdx n n dA) : ℝ) * bwNormSq A)} ≤
      32 / (9 * (Fintype.card (CoefIdx n n dA) : ℝ)) := by
  have hDpos : (0 : ℝ) < (Fintype.card (CoefIdx n n dA) : ℝ) := by
    have : Nonempty (CoefIdx n n dA) := ⟨(⟨0, hn⟩, ⟨0, Sym.nil⟩)⟩
    exact Nat.cast_pos.2 Fintype.card_pos
  set D : ℝ := (Fintype.card (CoefIdx n n dA) : ℝ) with hD
  have hS : MeasurableSet {A : CoefIdx n n dA → ℝ | ¬ (1 ≤ 4 / D * bwNormSq A)} :=
    (measurableSet_le measurable_const (c_measurable_bwNormSq.const_mul _)).compl
  unfold bwGauss
  rw [map_measureReal_apply (measurable_bwGaussMap 1) hS]
  have hc := BstLean.Part106.chiSq_cheb (CoefIdx n n dA) (t := 3 * D / 4) (by positivity)
  refine le_trans (measureReal_mono ?_) (hc.trans (le_of_eq ?_))
  · intro ξ hξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hξ ⊢
    have e : bwNormSq (bwOfCoord ((1 : ℝ) • ξ)) = ∑ i, ξ i ^ 2 := by
      unfold bwNormSq
      rw [bwInner_ofCoord]
      simp [sq]
    rw [e] at hξ
    have h1 : ∑ i, ξ i ^ 2 < D / 4 := by
      have := (lt_div_iff₀' (by positivity : (0 : ℝ) < 4 / D)).2 hξ
      calc ∑ i, ξ i ^ 2 < 1 / (4 / D) := this
        _ = D / 4 := by field_simp
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [← hD]
    field_simp
    ring

/-- The quantity of event 3: `|g − B| + sd_μ/2` for the perturbation. -/
noncomputable def Tp (hd : 1 ≤ dF) (τ : ℝ) (p : Theta n dA dF × Draws (2 * n) n k) : ℝ :=
  |Err p.1.1 τ (psi hd (Real.sqrt (bwNormSq p.1.2.1)) p.1.2.1 p.1.2.2) p.2| +
    1 / 2 * Real.sqrt (Vu p.1.1 (psi hd (Real.sqrt (bwNormSq p.1.2.1)) p.1.2.1 p.1.2.2))

lemma Tp_nonneg (hd : 1 ≤ dF) (τ : ℝ) (p : Theta n dA dF × Draws (2 * n) n k) : 0 ≤ Tp hd τ p := by
  unfold Tp
  positivity

lemma measurable_Tp (hMG : MeasGen108) (hMP : MeasPsi108) (hd : 1 ≤ dF) (τ : ℝ) :
    Measurable (Tp (n := n) (dA := dA) (k := k) hd τ) := by
  have hΦ : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) =>
      psi hd (Real.sqrt (bwNormSq p.1.2.1)) p.1.2.1 p.1.2.2 p.2) := by
    have hm : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) =>
        (((Real.sqrt (bwNormSq p.1.2.1), p.1.2.1, p.1.2.2), p.2) :
          (ℝ × (CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ))) := by
      have ha : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) => p.1.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_fst)
      have hf : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) => p.1.2.2) :=
        measurable_snd.comp (measurable_snd.comp measurable_fst)
      exact (((c_measurable_bwNormSq.comp ha).sqrt).prodMk (ha.prodMk hf)).prodMk measurable_snd
    exact (hMP n dA dF hd).comp hm
  obtain ⟨hg, hB, hV⟩ := hMG (2 * n) n (2 * dA) k (Theta n dA dF) (fun t => t.1) (fun _ => τ)
    (fun t => psi hd (Real.sqrt (bwNormSq t.2.1)) t.2.1 t.2.2) measurable_fst measurable_const hΦ
  unfold Tp Err
  exact ((hg.sub (hB.comp measurable_fst)).abs).add
    (((hV.comp measurable_fst).sqrt).const_mul _)

/-- Event 3: the terms of degree at least 2 of `F`. -/
lemma e3 (hP : PertBound108) (hMG : MeasGen108) (hMP : MeasPsi108) (hd : 1 ≤ dF) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (τ : ℝ) {c2 t : ℝ} (hc2 : 0 ≤ c2) (ht : 0 < t) :
    ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | 1 ≤ c2 * bwNormSq p.1.2.1 ∧ t < Tp hd τ p ^ 2} ≤
      17 / 2 * Ssum n dA dF c2 / t := by
  have := drawM_prob (2 * n) n k (by omega)
  set μ := (GamG n dA dF).prod (drawM (2 * n) n k) with hμ
  set G : Theta n dA dF × Draws (2 * n) n k → ENNReal := fun p =>
    if 1 ≤ c2 * bwNormSq p.1.2.1 then ENNReal.ofReal (Tp hd τ p ^ 2) else 0 with hG
  have hGm : Measurable G := by
    refine Measurable.ite ?_ ((measurable_Tp hMG hMP hd τ).pow_const 2).ennreal_ofReal
      measurable_const
    exact measurableSet_le measurable_const
      ((c_measurable_bwNormSq.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).const_mul _)
  have hsub : {p : Theta n dA dF × Draws (2 * n) n k |
      1 ≤ c2 * bwNormSq p.1.2.1 ∧ t < Tp hd τ p ^ 2} ⊆ {p | ENNReal.ofReal t ≤ G p} := by
    intro p hp
    simp only [Set.mem_ofPred_eq, hG]
    rw [if_pos hp.1]
    exact ENNReal.ofReal_le_ofReal hp.2.le
  have hmk := meas_ge_le_lintegral_div (μ := μ) hGm.aemeasurable
    (ε := ENNReal.ofReal t) (by simpa using ht) ENNReal.ofReal_ne_top
  have hint : ∫⁻ p, G p ∂μ ≤ ENNReal.ofReal (17 / 2 * Ssum n dA dF c2) := by
    rw [hμ, lintegral_prod _ hGm.aemeasurable]
    have hH : Measurable (fun t : Theta n dA dF => ∫⁻ ω, G (t, ω) ∂drawM (2 * n) n k) :=
      hGm.lintegral_prod_right'
    rw [lintegral_prod _ hH.aemeasurable]
    calc ∫⁻ w, ∫⁻ q, ∫⁻ ω, G ((w, q), ω) ∂drawM (2 * n) n k
            ∂((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) ∂bwGauss (2 * n) n (2 * dA) 1
        = ∫⁻ w, ∫⁻ ω, ∫⁻ q, G ((w, q), ω)
            ∂((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) ∂drawM (2 * n) n k
            ∂bwGauss (2 * n) n (2 * dA) 1 := by
          refine lintegral_congr fun w => ?_
          refine lintegral_lintegral_swap ?_
          exact (hGm.comp ((measurable_const.prodMk measurable_fst).prodMk
            measurable_snd)).aemeasurable
      _ ≤ ∫⁻ _w, ∫⁻ _ω, ENNReal.ofReal (17 / 2 * Ssum n dA dF c2) ∂drawM (2 * n) n k
            ∂bwGauss (2 * n) n (2 * dA) 1 := by
          refine lintegral_mono fun w => lintegral_mono fun ω => ?_
          exact hP (2 * n) n (2 * dA) dA dF k hd (by omega) hk w τ ω c2 hc2
      _ = ENNReal.ofReal (17 / 2 * Ssum n dA dF c2) := by simp
  have hfin : μ {p | 1 ≤ c2 * bwNormSq p.1.2.1 ∧ t < Tp hd τ p ^ 2} ≤
      ENNReal.ofReal (17 / 2 * Ssum n dA dF c2) / ENNReal.ofReal t :=
    (measure_mono hsub).trans (hmk.trans (ENNReal.div_le_div_right hint _))
  have hS0 : 0 ≤ 17 / 2 * Ssum n dA dF c2 := mul_nonneg (by norm_num) (Ssum_nonneg n dA dF hc2)
  have h2 := ENNReal.toReal_mono
    (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simpa using ht)) hfin
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hS0, ENNReal.toReal_ofReal ht.le] at h2
  exact h2

/-- The pointwise step: off the four events, success. -/
lemma point (hS : SuccParts108) (hd : 1 ≤ dF) (hn : 1 ≤ n) (hk : 1 ≤ k) (τ : ℝ)
    {θ ι M c2 : ℝ} (hθ1 : θ < 1) (hι : 0 < ι) (hι1 : ι < 1) (hM : 0 < M) (hc2 : 0 ≤ c2)
    (p : Theta n dA dF × Draws (2 * n) n k)
    (h1 : ¬ Vu p.1.1 (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) < (1 - θ) * M)
    (h2 : ¬ (1 - ι) ^ 2 * ((1 - θ) * M) / 4 <
      Err p.1.1 τ (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) p.2 ^ 2)
    (h3 : ¬ (1 ≤ c2 * bwNormSq p.1.2.1 ∧ ι ^ 2 * ((1 - θ) * M) / 4 < Tp hd τ p ^ 2))
    (h4 : 1 ≤ c2 * bwNormSq p.1.2.1) :
    Succ p.1.1 τ (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2 := by
  have hpos : 0 < bwNormSq p.1.2.1 := by
    by_contra h
    push Not at h
    have : c2 * bwNormSq p.1.2.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2 h
    linarith
  set ρ := Real.sqrt (bwNormSq p.1.2.1) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hQ : 0 ≤ (1 - θ) * M := mul_nonneg (by linarith) hM.le
  set R := Real.sqrt ((1 - θ) * M) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (1 - θ) * M := Real.sq_sqrt hQ
  have ha : |Err p.1.1 τ (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) p.2| ≤ (1 - ι) * R / 2 := by
    refine abs_le_of_sq_le_sq ?_ (by nlinarith)
    have h2' := not_lt.1 h2
    refine h2'.trans (le_of_eq ?_)
    rw [← hR2]; ring
  have h3' : Tp hd τ p ^ 2 ≤ ι ^ 2 * ((1 - θ) * M) / 4 := by
    by_contra h
    exact h3 ⟨h4, not_le.1 h⟩
  have hb : Tp hd τ p ≤ ι * R / 2 := by
    have := abs_le_of_sq_le_sq (a := Tp hd τ p) (b := ι * R / 2)
      (h3'.trans (le_of_eq (by rw [← hR2]; ring))) (by positivity)
    exact (le_abs_self _).trans this
  have hsum : (1 - ι) * R / 2 + ι * R / 2 ≤
      1 / 2 * Real.sqrt (Vu p.1.1 (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x)) := by
    have : R ≤ Real.sqrt (Vu p.1.1 (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x)) :=
      Real.sqrt_le_sqrt (not_lt.1 h1)
    linarith
  have := hS (2 * n) n (2 * dA) dA dF k hd (by omega) hk p.1.1 τ p.2 p.1.2.1 p.1.2.2 ρ
    ((1 - ι) * R / 2) (ι * R / 2) hρ0 ha hb hsum (1 / Real.sqrt (bwNormSq p.1.2.2)) (by positivity)
  have e : nrm p.1.2.1 = ρ⁻¹ • p.1.2.1 := by
    unfold nrm
    rw [one_div]
  rw [e]
  exact this

/-- **The core**: Gaussian `W`, sphere `A`, sphere `F` (in the Gaussian coordinates), the ideal
noise level, relative to the realized spread. -/
theorem core_gauss (hL : LinLaw108) (hP : PertBound108) (hMG : MeasGen108) (hMP : MeasPsi108)
    (hS : SuccParts108) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hd : 1 ≤ dF) (hk : 1 ≤ k)
    {θ ι : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hι : 0 < ι) (hι1 : ι < 1) :
    ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | ¬ Succ p.1.1 (tauOf (2 * dA) 1)
          (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ≤
      coreBound n dA dF k θ ι := by
  unfold coreBound
  have := drawM_prob (2 * n) n k (by omega)
  have hlam : lam0 (2 * n) (2 * dA) < 1 := by
    rcases hdA with rfl | rfl
    · exact BstLean.Part107.lam6_lt_one n hn
    · exact BstLean.Part107.lam8_lt_one n hn
  obtain ⟨-, hv, hMlow, -⟩ := BstLean.Part107.part107_spread n dA 1 hn hdA one_ne_zero
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow0 : 0 < (n : ℝ) * ((dA : ℝ) + 1 - vbar dA n) := mul_pos hn0 (by linarith)
  set M := Mx1 n dA with hMdef
  have hMlow' : (n : ℝ) * ((dA : ℝ) + 1 - vbar dA n) ≤ M := hMlow
  have hM : 0 < M := lt_of_lt_of_le hlow0 hMlow'
  set D : ℝ := (Fintype.card (CoefIdx n n dA) : ℝ) with hD
  have hDpos : 0 < D := by
    have : Nonempty (CoefIdx n n dA) := ⟨(⟨0, by omega⟩, ⟨0, Sym.nil⟩)⟩
    exact Nat.cast_pos.2 Fintype.card_pos
  set c2 : ℝ := 4 / D with hc2def
  have hc2 : 0 ≤ c2 := by positivity
  set τ := tauOf (2 * dA) 1 with hτ
  set μ := (GamG n dA dF).prod (drawM (2 * n) n k) with hμ
  set t2 : ℝ := (1 - ι) ^ 2 * ((1 - θ) * M) / 4 with ht2
  set t3 : ℝ := ι ^ 2 * ((1 - θ) * M) / 4 with ht3
  have h1θ : 0 < 1 - θ := by linarith
  have h1ι : 0 < 1 - ι := by linarith
  have ht2pos : 0 < t2 := by positivity
  have ht3pos : 0 < t3 := by positivity
  set S1 : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | Vu p.1.1 (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) < (1 - θ) * M} with hS1
  set S2 : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | t2 < Err p.1.1 τ (fun x => qLin p.1.2.1 (linF hd p.1.2.2) x) p.2 ^ 2} with hS2
  set S3 : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | 1 ≤ c2 * bwNormSq p.1.2.1 ∧ t3 < Tp hd τ p ^ 2} with hS3
  set S4 : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | ¬ (1 ≤ c2 * bwNormSq p.1.2.1)} with hS4
  have hsub : {p : Theta n dA dF × Draws (2 * n) n k | ¬ Succ p.1.1 τ
      (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ⊆ ((S1 ∪ S2) ∪ S3) ∪ S4 := by
    intro p hp
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨n1, n2⟩, n3⟩, n4⟩ := hnot
    refine hp (point hS hd (by omega) hk τ hθ1 hι hι1 hM hc2 p n1 n2 n3 ?_)
    simpa [hS4] using n4
  have b1 : μ.real S1 ≤ (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) :=
    (real_fst_le (GamG n dA dF) (drawM (2 * n) n k)
      {t | Vu t.1 (fun x => qLin t.2.1 (linF hd t.2.2) x) < (1 - θ) * M}).trans
      (e1 hL hn hdA hd hθ)
  have b2 : μ.real S2 ≤ 4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) /
      ((1 - lam0 (2 * n) (2 * dA)) * ((1 - ι) ^ 2 * (1 - θ))) := by
    refine (e2 hL (by omega) (by rcases hdA with h | h <;> omega) hd hk ht2pos hlam).trans
      (le_of_eq ?_)
    rw [ht2, ← hMdef]
    have h1l : 0 < 1 - lam0 (2 * n) (2 * dA) := by linarith
    field_simp
  have b3 : μ.real S3 ≤ 34 * Ssum n dA dF c2 /
      (ι ^ 2 * (1 - θ) * ((n : ℝ) * ((dA : ℝ) + 1 - vbar dA n))) := by
    refine (e3 hP hMG hMP hd (by omega) hk τ hc2 ht3pos).trans ?_
    have hS0 := Ssum_nonneg n dA dF hc2
    rw [div_le_div_iff₀ ht3pos (by positivity)]
    rw [ht3]
    have hι2 : 0 < ι ^ 2 * (1 - θ) := by positivity
    have : 17 / 2 * Ssum n dA dF c2 * (ι ^ 2 * (1 - θ) * ((n : ℝ) * ((dA : ℝ) + 1 - vbar dA n))) ≤
        17 / 2 * Ssum n dA dF c2 * (ι ^ 2 * (1 - θ) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMlow' hι2.le) (by positivity)
    nlinarith
  have b4 : μ.real S4 ≤ 32 / (9 * D) := by
    have h := real_fst_le (GamG n dA dF) (drawM (2 * n) n k)
      {t | ¬ (1 ≤ c2 * bwNormSq t.2.1)}
    have h' := real_snd_le (bwGauss (2 * n) n (2 * dA) 1)
      ((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) {q | ¬ (1 ≤ c2 * bwNormSq q.1)}
    have h'' := real_fst_le (bwGauss n n dA 1) (bwGauss n 1 dF 1)
      {A | ¬ (1 ≤ c2 * bwNormSq A)}
    exact h.trans (h'.trans (h''.trans (e4 (by omega))))
  calc μ.real {p | ¬ Succ p.1.1 τ (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2}
      ≤ μ.real (((S1 ∪ S2) ∪ S3) ∪ S4) := measureReal_mono hsub
    _ ≤ μ.real S1 + μ.real S2 + μ.real S3 + μ.real S4 := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ _ := by gcongr

end core

end BstLean.Part108
