import BstLean.Part154C16

/-!
# Part 154: joint measurability of the event `GoodC16` in the stand-in input `(c, τ)` and
`(A₁, A₂)`

Every quantity of the events is shown measurable "in composition form": for measurable maps
`c : X → ℝⁿ`, `τ : X → ℝ`, `A₁ : X → M₁`, `A₂ : X → M₂` on a measurable space `X`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part136 (HidParam)
open BstLean.Part137 (psiS measurable_psiS)
open BstLean.Part153 (nrm GamS Eop Pb Xi4 N1 N2 sq1 sq2 GoodAs GoodAs16 GoodA Bad1 Bad2 BadE
  BadBe BadN22 BadN24 BscS BXiS jacT measurable_lpNorm_param memLp_sq1_sub memLp_sq2_sub
  measurable_opN_jacT_joint continuous_nrm N12bar N14bar)

section compMeas

variable {n : ℕ} {X : Type*} [MeasurableSpace X] {c : X → Fin n → ℝ} {τ : X → ℝ}

private lemma m_mv {p q : ℕ} {M : X → Matrix (Fin p) (Fin q) ℝ} {v : X → Fin q → ℝ}
    (hM : Measurable M) (hv : Measurable v) : Measurable (fun x => M x *ᵥ v x) :=
  (BstLean.Part149.measurable_mulVec_joint (m := p) (k := q)).comp (hM.prodMk hv)

private lemma m_y {ξ : X → Fin n → ℝ} (hc : Measurable c) (hτ : Measurable τ)
    (hξ : Measurable ξ) : Measurable (fun x => c x + τ x • ξ x) := hc.add (hτ.smul hξ)

private lemma m_nrm {ι : Type*} [Fintype ι] {v : X → ι → ℝ} (hv : Measurable v) :
    Measurable (fun x => nrm (v x)) := (measurable_normSq.comp hv).sqrt

variable {m : ℕ} {A₁ : X → Matrix (Fin m) (Fin n) ℝ} {A₂ : X → Matrix (Fin m) (Fin m) ℝ}

/-- The map into the product space of Part 150 (`A₂` is a dummy when it is not used). -/
private lemma m_prod (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) :
    Measurable (fun x => (((c x, τ x), (A₁ x, A₂ x)) : ((Fin n → ℝ) × ℝ) × HidParam n m)) :=
  (hc.prodMk hτ).prodMk (hA₁.prodMk hA₂)

private lemma m_GamS (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => GamS (A₁ x) (c x) (τ x)) := by
  have hF : Measurable (fun q : X × (Fin n → ℝ) =>
      normSq (reluV (A₁ q.1 *ᵥ (c q.1 + τ q.1 • q.2)))) :=
    measurable_normSq.comp (measurable_reluV.comp (m_mv (hA₁.comp measurable_fst)
      (m_y (hc.comp measurable_fst) (hτ.comp measurable_fst) measurable_snd)))
  unfold GamS
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin n))).measurable.const_mul _

private lemma m_int_sqrtGam (m : ℕ) (v : ℝ) (hc : Measurable c) (hτ : Measurable τ) :
    Measurable (fun x => ∫ A : Matrix (Fin m) (Fin n) ℝ, √(GamS A (c x) (τ x))
      ∂gaussMat m n v) := by
  have hF : Measurable (fun q : X × Matrix (Fin m) (Fin n) ℝ => √(GamS q.2 (c q.1) (τ q.1))) :=
    (m_GamS (hc.comp measurable_fst) (hτ.comp measurable_fst) measurable_snd).sqrt
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := gaussMat m n v)).measurable

private lemma m_hO (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => hO (A₁ x) (c x) (τ x)) := by
  have h := (measurable_hO (n := n) (m := m)).comp
    (m_prod hc hτ hA₁ (measurable_const : Measurable fun _ : X => (0 : Matrix (Fin m) (Fin m) ℝ)))
  simpa only [Function.comp_def] using h

private lemma m_hT (J : ℕ) (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => hT J (A₁ x) (c x) (τ x)) := by
  have h := (measurable_hT (n := n) (m := m) J).comp
    (m_prod hc hτ hA₁ (measurable_const : Measurable fun _ : X => (0 : Matrix (Fin m) (Fin m) ℝ)))
  simpa only [Function.comp_def] using h

private lemma m_gO_prod :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => gO x.2.1 x.1.1 x.1.2) := by
  have hi : ∀ i : Fin m, Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m =>
      ∫ z, relu (mRow x.2.1 x.1.1 i + sRow x.2.1 x.1.2 i * z) ^ 2 ∂gaussianReal 0 1) := by
    intro i
    have hF : Measurable (fun q : (((Fin n → ℝ) × ℝ) × HidParam n m) × ℝ =>
        relu (mRow q.1.2.1 q.1.1.1 i + sRow q.1.2.1 q.1.1.2 i * q.2) ^ 2) :=
      (measurable_relu.comp (((measurable_mRowX i).comp measurable_fst).add
        (((measurable_sRowX i).comp measurable_fst).mul measurable_snd))).pow_const 2
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  unfold gO
  exact (Finset.measurable_sum _ fun i _ => hi i).const_mul _

private lemma m_gO (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => gO (A₁ x) (c x) (τ x)) := by
  have h := (m_gO_prod (n := n) (m := m)).comp
    (m_prod hc hτ hA₁ (measurable_const : Measurable fun _ : X => (0 : Matrix (Fin m) (Fin m) ℝ)))
  simpa only [Function.comp_def] using h

private lemma m_sO2 (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => sO2 (A₁ x) (c x) (τ x)) := by
  have hh : Measurable (fun x => ∑ i, hO (A₁ x) (c x) (τ x) i ^ 2) :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (m_hO hc hτ hA₁)).pow_const 2
  unfold sO2
  exact (m_gO hc hτ hA₁).sub (hh.const_mul _)

private lemma m_bO (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => bO (A₁ x) (A₂ x) (c x) (τ x)) := by
  have h := (measurable_bO (n := n) (m := m)).comp (m_prod hc hτ hA₁ hA₂)
  simpa only [Function.comp_def] using h

private lemma m_Pb (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => Pb (A₁ x) (c x) (τ x) (A₂ x)) := by
  unfold Pb
  exact (m_nrm (m_bO hc hτ hA₁ hA₂)).const_mul _

private lemma m_int_Pb (v : ℝ) (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => ∫ B, Pb (A₁ x) (c x) (τ x) B ∂gaussMat m m v) := by
  have hF : Measurable (fun q : X × Matrix (Fin m) (Fin m) ℝ =>
      Pb (A₁ q.1) (c q.1) (τ q.1) q.2) :=
    m_Pb (hc.comp measurable_fst) (hτ.comp measurable_fst) (hA₁.comp measurable_fst)
      measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := gaussMat m m v)).measurable

private lemma m_Xi4 (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => Xi4 (A₁ x) (A₂ x) (c x) (τ x)) := by
  have hy : Measurable (fun q : X × (Fin n → ℝ) => c q.1 + τ q.1 • q.2) :=
    m_y (hc.comp measurable_fst) (hτ.comp measurable_fst) measurable_snd
  have hJ : Measurable (fun q : X × (Fin n → ℝ) =>
      opN (jacT (A₁ q.1) (A₂ q.1) (sphPt (c q.1 + τ q.1 • q.2)))) := by
    have h := (measurable_opN_jacT_joint (n := n) (m := m) (m₂ := m)).comp
      (((hA₁.comp measurable_fst).prodMk (hA₂.comp measurable_fst)).prodMk
        (measurable_sphPt.comp hy))
    simpa only [Function.comp_def] using h
  have hF : Measurable (fun q : X × (Fin n → ℝ) =>
      opN (jacT (A₁ q.1) (A₂ q.1) (sphPt (c q.1 + τ q.1 • q.2))) ^ 4 *
        (normSq (c q.1 + τ q.1 • q.2))⁻¹ ^ 2) :=
    (hJ.pow_const 4).mul (((measurable_normSq.comp hy).inv).pow_const 2)
  unfold Xi4
  exact ((hτ.pow_const 2).const_mul _).mul
    ((hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable.sqrt)

private lemma m_fA {ξ : X → Fin n → ℝ} (hc : Measurable c) (hτ : Measurable τ)
    (hA₁ : Measurable A₁) (hξ : Measurable ξ) :
    Measurable (fun x => fA (A₁ x) (c x) (τ x) (ξ x)) := by
  unfold fA
  exact Measurable.const_smul (measurable_reluV.comp (m_mv hA₁ (m_y hc hτ hξ))) (√(2 / (m : ℝ)))

private lemma m_fbar (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => fbar (stdGauss (Fin n)) (fA (A₁ x) (c x) (τ x))) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hF : Measurable (fun q : X × (Fin n → ℝ) => fA (A₁ q.1) (c q.1) (τ q.1) q.2 i) :=
    (measurable_pi_apply i).comp (m_fA (hc.comp measurable_fst) (hτ.comp measurable_fst)
      (hA₁.comp measurable_fst) measurable_snd)
  unfold fbar
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

private lemma m_hsH (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => hsH (A₁ x) (c x) (τ x)) := by
  unfold hsH hsF
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    Measurable.pow_const ?_ 2
  have hb : Measurable (fun q : X × (Fin n → ℝ) =>
      fbar (stdGauss (Fin n)) (fA (A₁ q.1) (c q.1) (τ q.1))) :=
    m_fbar (hc.comp measurable_fst) (hτ.comp measurable_fst) (hA₁.comp measurable_fst)
  have hf : Measurable (fun q : X × (Fin n → ℝ) => fA (A₁ q.1) (c q.1) (τ q.1) q.2) :=
    m_fA (hc.comp measurable_fst) (hτ.comp measurable_fst) (hA₁.comp measurable_fst)
      measurable_snd
  have hF : Measurable (fun q : X × (Fin n → ℝ) =>
      (fA (A₁ q.1) (c q.1) (τ q.1) q.2 i -
          fbar (stdGauss (Fin n)) (fA (A₁ q.1) (c q.1) (τ q.1)) i) *
        (fA (A₁ q.1) (c q.1) (τ q.1) q.2 j -
          fbar (stdGauss (Fin n)) (fA (A₁ q.1) (c q.1) (τ q.1)) j)) :=
    (((measurable_pi_apply i).comp hf).sub ((measurable_pi_apply i).comp hb)).mul
      (((measurable_pi_apply j).comp hf).sub ((measurable_pi_apply j).comp hb))
  unfold covF
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

private lemma m_int_hsH (m : ℕ) (v : ℝ) (hc : Measurable c) (hτ : Measurable τ) :
    Measurable (fun x => ∫ A : Matrix (Fin m) (Fin n) ℝ, √(√(hsH A (c x) (τ x)))
      ∂gaussMat m n v) := by
  have hF : Measurable (fun q : X × Matrix (Fin m) (Fin n) ℝ =>
      √(√(hsH q.2 (c q.1) (τ q.1)))) :=
    (m_hsH (hc.comp measurable_fst) (hτ.comp measurable_fst) measurable_snd).sqrt.sqrt
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := gaussMat m n v)).measurable

private lemma m_hbar2 (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => hbar2 (A₁ x) (A₂ x) (c x) (τ x)) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have hF : Measurable (fun q : X × (Fin n → ℝ) =>
      hid2 (A₁ q.1) (A₂ q.1) (c q.1 + τ q.1 • q.2) j) :=
    (measurable_pi_apply j).comp (measurable_reluV.comp (m_mv (hA₂.comp measurable_fst)
      (measurable_reluV.comp (m_mv (hA₁.comp measurable_fst)
        (m_y (hc.comp measurable_fst) (hτ.comp measurable_fst) measurable_snd)))))
  unfold hbar2
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

private lemma m_dC (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => dC (A₁ x) (A₂ x) (c x) (τ x)) := by
  unfold dC
  exact (m_nrm ((m_hbar2 hc hτ hA₁ hA₂).sub (m_bO hc hτ hA₁ hA₂))).const_mul _

private lemma m_DelP (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁)
    (hA₂ : Measurable A₂) : Measurable (fun x => DelP (A₁ x) (A₂ x) (c x) (τ x)) := by
  unfold DelP Ph
  exact ((m_nrm (m_hbar2 hc hτ hA₁ hA₂)).const_mul _).sub (m_Pb hc hτ hA₁ hA₂)

private lemma m_int_dC (v : ℝ) (hc : Measurable c) (hτ : Measurable τ) (hA₁ : Measurable A₁) :
    Measurable (fun x => ∫ B, dC (A₁ x) B (c x) (τ x) ∂gaussMat m m v) := by
  have hF : Measurable (fun q : X × Matrix (Fin m) (Fin m) ℝ =>
      dC (A₁ q.1) q.2 (c q.1) (τ q.1)) :=
    m_dC (hc.comp measurable_fst) (hτ.comp measurable_fst) (hA₁.comp measurable_fst)
      measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := gaussMat m m v)).measurable

private lemma m_int_DelP (v : ℝ) (hc : Measurable c) (hτ : Measurable τ)
    (hA₁ : Measurable A₁) :
    Measurable (fun x => ∫ B, DelP (A₁ x) B (c x) (τ x) ∂gaussMat m m v) := by
  have hF : Measurable (fun q : X × Matrix (Fin m) (Fin m) ℝ =>
      DelP (A₁ q.1) q.2 (c q.1) (τ q.1)) :=
    m_DelP (hc.comp measurable_fst) (hτ.comp measurable_fst) (hA₁.comp measurable_fst)
      measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := gaussMat m m v)).measurable

/-! The norms `N₁ₖ`, `N₂ₖ` (width `mA n`). -/

variable {B₁ : X → Matrix (Fin (mA n)) (Fin n) ℝ} {B₂ : X → Matrix (Fin (mA n)) (Fin (mA n)) ℝ}

private lemma m_sq1 {ξ : X → Fin n → ℝ} (hc : Measurable c) (hτ : Measurable τ)
    (hB₁ : Measurable B₁) (hξ : Measurable ξ) :
    Measurable (fun x => sq1 (B₁ x) (c x) (τ x) (ξ x)) := by
  unfold sq1
  exact (m_nrm (measurable_reluV.comp
    (m_mv hB₁ (measurable_sphPt.comp (m_y hc hτ hξ))))).div_const _

private lemma m_sq2 {ξ : X → Fin n → ℝ} (hc : Measurable c) (hτ : Measurable τ)
    (hB₁ : Measurable B₁) (hB₂ : Measurable B₂) (hξ : Measurable ξ) :
    Measurable (fun x => sq2 (B₁ x) (B₂ x) (c x) (τ x) (ξ x)) := by
  unfold sq2
  exact (m_nrm (measurable_reluV.comp (m_mv hB₂ (measurable_reluV.comp
    (m_mv hB₁ (measurable_sphPt.comp (m_y hc hτ hξ))))))).div_const _

private lemma m_N1 (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hc : Measurable c) (hτ : Measurable τ)
    (hB₁ : Measurable B₁) : Measurable (fun x => N1 k (B₁ x) (c x) (τ x)) :=
  measurable_lpNorm_param (μ := stdGauss (Fin n)) (by omega)
    (G := fun (x : X) (ξ : Fin n → ℝ) => sq1 (B₁ x) (c x) (τ x) ξ - 1)
    ((m_sq1 (hc.comp measurable_fst) (hτ.comp measurable_fst) (hB₁.comp measurable_fst)
      measurable_snd).sub_const 1)
    (fun x => memLp_sq1_sub hn (B₁ x) (c x) (τ x) _)

private lemma m_N2 (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (hc : Measurable c) (hτ : Measurable τ)
    (hB₁ : Measurable B₁) (hB₂ : Measurable B₂) :
    Measurable (fun x => N2 k (B₁ x) (B₂ x) (c x) (τ x)) :=
  measurable_lpNorm_param (μ := stdGauss (Fin n)) (by omega)
    (G := fun (x : X) (ξ : Fin n → ℝ) => sq2 (B₁ x) (B₂ x) (c x) (τ x) ξ - 1)
    ((m_sq2 (hc.comp measurable_fst) (hτ.comp measurable_fst) (hB₁.comp measurable_fst)
      (hB₂.comp measurable_fst) measurable_snd).sub_const 1)
    (fun x => memLp_sq2_sub hn (B₁ x) (B₂ x) (c x) (τ x) _)

private lemma m_int_N2 (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (v : ℝ) (hc : Measurable c)
    (hτ : Measurable τ) (hB₁ : Measurable B₁) :
    Measurable (fun x => ∫ B, N2 k (B₁ x) B (c x) (τ x) ∂gaussMat (mA n) (mA n) v) := by
  have hF : Measurable (fun q : X × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      N2 k (B₁ q.1) q.2 (c q.1) (τ q.1)) :=
    m_N2 hn hk (hc.comp measurable_fst) (hτ.comp measurable_fst) (hB₁.comp measurable_fst)
      measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right'
    (ν := gaussMat (mA n) (mA n) v)).measurable

end compMeas

/-! ## The events -/

private abbrev XM (n : ℕ) : Type :=
  ((Fin n → ℝ) × ℝ) × (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

private lemma pc (n : ℕ) : Measurable (fun x : XM n => x.1.1) :=
  measurable_fst.comp measurable_fst
private lemma pτ (n : ℕ) : Measurable (fun x : XM n => x.1.2) :=
  measurable_snd.comp measurable_fst
private lemma pA1 (n : ℕ) : Measurable (fun x : XM n => x.2.1) :=
  measurable_fst.comp measurable_snd
private lemma pA2 (n : ℕ) : Measurable (fun x : XM n => x.2.2) :=
  measurable_snd.comp measurable_snd

/-- The family of the `A`-stage events, with a constant `K` for `Ξ₄`. -/
private lemma mGoodA_Meas {n : ℕ} (hn : 1 ≤ n) (K : ℝ) :
    MeasurableSet {x : XM n | x.2 ∈ GoodA n x.1.1 x.1.2 (BscS n x.1.1 x.1.2)
      {θ | K < Xi4 θ.1 θ.2 x.1.1 x.1.2}} := by
  have hc := pc n
  have hτ := pτ n
  have h1 := pA1 n
  have h2 := pA2 n
  have s1 : MeasurableSet {x : XM n | x.2.1 ∈ Eop n} :=
    measurableSet_le (opN_continuous.measurable.comp h1) measurable_const
  have s2 : MeasurableSet {x : XM n | x.2.1 ∈ BadE n x.1.1 x.1.2} :=
    measurableSet_lt
      (((((measurable_normSq.comp hc).add ((hτ.pow_const 2).const_mul _)).sqrt).const_mul
        _).const_mul _)
      (continuous_abs.measurable.comp (((m_GamS hc hτ h1).sqrt).sub
        (m_int_sqrtGam (mA n) _ hc hτ)))
  have s3 : MeasurableSet {x : XM n | N12bar n 12 < N1 2 x.2.1 x.1.1 x.1.2} :=
    measurableSet_lt measurable_const (m_N1 hn (by norm_num) hc hτ h1)
  have s4 : MeasurableSet {x : XM n | N14bar n 12 < N1 4 x.2.1 x.1.1 x.1.2} :=
    measurableSet_lt measurable_const (m_N1 hn (by norm_num) hc hτ h1)
  have s5 : MeasurableSet {x : XM n | x.2.1 ∈ BscS n x.1.1 x.1.2} :=
    measurableSet_lt (m_sO2 hc hτ h1) ((hτ.pow_const 2).const_mul _)
  have t1 : MeasurableSet {x : XM n | x.2.2 ∈ BadBe n x.1.1 x.1.2 x.2.1} :=
    measurableSet_lt ((m_int_Pb _ hc hτ h1).add (((m_gO hc hτ h1).const_mul _).sqrt))
      (m_Pb hc hτ h1 h2)
  have t2 : MeasurableSet {x : XM n | x.2.2 ∈ BadN22 n x.1.1 x.1.2 x.2.1} :=
    measurableSet_lt ((m_int_N2 hn (by norm_num) _ hc hτ h1).add
      ((((m_N1 hn (by norm_num) hc hτ h1).const_add 1).const_mul _).div_const _))
      (m_N2 hn (by norm_num) hc hτ h1 h2)
  have t3 : MeasurableSet {x : XM n | x.2.2 ∈ BadN24 n x.1.1 x.1.2 x.2.1} :=
    measurableSet_lt ((m_int_N2 hn (by norm_num) _ hc hτ h1).add
      ((((opN_continuous.measurable.comp h1).const_mul _).div_const _).const_mul _))
      (m_N2 hn (by norm_num) hc hτ h1 h2)
  have u : MeasurableSet {x : XM n | K < Xi4 x.2.1 x.2.2 x.1.1 x.1.2} :=
    measurableSet_lt measurable_const (m_Xi4 hc hτ h1 h2)
  exact ((((s1.compl.union s2).union s3).union s4).union s5).compl.inter
    ((((t1.union t2).union t3).compl).inter u.compl)

/-- The family of the events `GoodC n n c τ`, as a set of `((c, τ), (A₁, A₂))`, is measurable. -/
theorem measurableSet_SCgen {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet {x : ((Fin n → ℝ) × ℝ) ×
      (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) |
      x.2 ∈ GoodC n n x.1.1 x.1.2} := by
  have hc := pc n
  have hτ := pτ n
  have h1 := pA1 n
  have h2 := pA2 n
  have gA : MeasurableSet {x : XM n | x.2 ∈ GoodAs n x.1.1 x.1.2} := mGoodA_Meas hn _
  have hρ : Measurable (fun x : XM n => √(normSq x.1.1 + (n : ℝ) * x.1.2 ^ 2)) :=
    ((measurable_normSq.comp hc).add ((hτ.pow_const 2).const_mul _)).sqrt
  have hG : Measurable (fun x : XM n => √(GamS x.2.1 x.1.1 x.1.2)) := (m_GamS hc hτ h1).sqrt
  have bH : MeasurableSet {x : XM n | x.2.1 ∈ BadH n x.1.1 x.1.2 12} :=
    measurableSet_lt ((m_int_hsH (mA n) _ hc hτ).add ((hρ.const_mul _).const_mul _))
      ((m_hsH hc hτ h1).sqrt.sqrt)
  have bD : MeasurableSet {x : XM n | x.2.2 ∈ BadD x.2.1 x.1.1 x.1.2 12} :=
    measurableSet_lt ((m_int_dC _ hc hτ h1).add ((hG.const_mul 2).const_mul _))
      (m_dC hc hτ h1 h2)
  have bPi : MeasurableSet {x : XM n | x.2.2 ∈ BadPi x.2.1 x.1.1 x.1.2 12} :=
    measurableSet_lt ((hG.const_mul 2).const_mul _)
      (continuous_abs.measurable.comp ((m_DelP hc hτ h1 h2).sub (m_int_DelP _ hc hτ h1)))
  have bPb : MeasurableSet {x : XM n | x.2.2 ∈ BadPb x.2.1 x.1.1 x.1.2 12} :=
    measurableSet_lt (m_Pb hc hτ h1 h2) ((m_int_Pb _ hc hτ h1).sub (hG.const_mul _))
  have hd : Measurable (fun x : XM n => hT n x.2.1 x.1.1 x.1.2 - hO x.2.1 x.1.1 x.1.2) :=
    (m_hT n hc hτ h1).sub (m_hO hc hτ h1)
  have bChi : MeasurableSet {x : XM n | x.2.2 ∈ BadChi n n x.2.1 x.1.1 x.1.2 12} :=
    measurableSet_lt ((((measurable_normSq.comp hd).const_mul _).mul_const _).mul_const _)
      (measurable_normSq.comp (m_mv h2 hd))
  exact gA.inter (bH.compl.inter (bD.compl.inter (bPi.compl.inter
    (bPb.compl.inter bChi.compl))))

/-- The family of the events `GoodC16 n n c τ`, as a set of `((c, τ), (A₁, A₂))`. -/
def SC16 (n : ℕ) :
    Set (((Fin n → ℝ) × ℝ) ×
      (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) :=
  {x | x.2 ∈ GoodC16 n n x.1.1 x.1.2}

theorem measurableSet_SC16 {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (SC16 n) := by
  have gA16 : MeasurableSet {x : XM n | x.2 ∈ GoodAs16 n x.1.1 x.1.2} := mGoodA_Meas hn _
  exact (measurableSet_SCgen hn).inter gA16

end BstLean.Part154
