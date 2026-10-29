import BstLean.Part132Agent
import BstLean.Part132World

/-!
# Part 132, item 3: the lower bound of `b₂`

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3,
`onW4-opus-prover.md` Statement M: `b₂ ≥ S(Q − e_b)`, `Q = κ^{∘6}(0)`.

* `T_mean_lower`: `E_{W,u,u′} ⟨x(u), x(u′)⟩ ≥ κ(κ(0)) − eW n m λ`.
* `k4_mean_lower`: `E κ^{∘4}(⟨x(u), x(u′)⟩) ≥ κ^{∘6}(0) − eW n m λ` (the supporting line of
  `κ^{∘4}` at `q = κ(κ(0))`; this is Jensen in the direction needed).
* **`b2_lower`**: `b2 ≥ (4/n)·(κ^{∘6}(0) − eW n m_W λ − eA n m_A m_F)` for every `λ > 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131

variable {N mW n mA mF : ℕ}

/-- `t_x = ⟨x(u), x(u′)⟩` as a function of `((u, u′), W)`. -/
noncomputable def tX (z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) : ℝ :=
  dotp (xW z.2 z.1.1) (xW z.2 z.1.2)

lemma measurable_tX : Measurable (tX (N := N) (mW := mW) (n := n)) :=
  measurable_dotp_comp (measurable_xW_comp measurable_snd (measurable_fst.comp measurable_fst))
    (measurable_xW_comp measurable_snd (measurable_snd.comp measurable_fst))

lemma tX_mem (hn : 1 ≤ n) (z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n) :
    tX z ∈ Icc (-1 : ℝ) 1 := ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩

lemma lawU2_prob (hN : 1 ≤ N) : IsProbabilityMeasure (lawU2 N) := by
  have := uniformSphere_isProbability N hN
  unfold lawU2; infer_instance

lemma integrable_tX (hn : 1 ≤ n) (hN : 1 ≤ N) :
    Integrable (tX (N := N) (mW := mW) (n := n)) ((lawU2 N).prod (mlpGauss N mW n)) := by
  have := lawU2_prob hN
  refine Integrable.mono' (integrable_const (1 : ℝ)) measurable_tX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact tX_mem hn z

lemma lawU2_ae_unit (hN : 1 ≤ N) :
    ∀ᵐ uu ∂lawU2 N, normSq uu.1 = 1 ∧ normSq uu.2 = 1 := by
  have := uniformSphere_isProbability N hN
  have h1 : ∀ᵐ uu ∂lawU2 N, normSq uu.1 = 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := uniformSphere N) (ν := uniformSphere N)).ae
      (uniformSphere_ae_sphere N)
  have h2 : ∀ᵐ uu ∂lawU2 N, normSq uu.2 = 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := uniformSphere N) (ν := uniformSphere N)).ae
      (uniformSphere_ae_sphere N)
  filter_upwards [h1, h2] with uu a b using ⟨a, b⟩

lemma lawU2_dot (hN : 1 ≤ N) :
    Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) (lawU2 N) ∧
    ∫ uu, dotp uu.1 uu.2 ∂lawU2 N = 0 := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  constructor
  · unfold dotp lawU2
    exact integrable_finsetSum _ fun i _ => (hmom.int1 i).mul_prod (hmom.int1 i)
  · have h := dot_prod_integral (uniformSphere N) 1 (fun x : Fin N → ℝ => x) (fun x => x)
      hmom.int1 hmom.int1
    simp only [one_mul, hmom.m1, mul_zero, Finset.sum_const_zero] at h
    exact h

/-- The mean of `κ(κ(⟨u, u′⟩))` over two independent uniform unit vectors is at least
`κ(κ(0))` (supporting line at `0`; `E⟨u, u′⟩ = 0`). -/
lemma kk_sphere_lower (hN : 1 ≤ N) :
    Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => kappa (kappa (dotp uu.1 uu.2))) (lawU2 N) ∧
    kappa (kappa 0) ≤ ∫ uu, kappa (kappa (dotp uu.1 uu.2)) ∂lawU2 N := by
  have := lawU2_prob hN
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support KGood.zero_mem
  obtain ⟨iD, eD⟩ := lawU2_dot hN
  have hmeas : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2))) :=
    (continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable
  have hmem : ∀ᵐ uu ∂lawU2 N, dotp uu.1 uu.2 ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h := abs_dotp_le_nrm uu.1 uu.2
    rw [nrm_of_normSq_one huu.1, nrm_of_normSq_one huu.2, mul_one] at h
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
  have hint : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2))) (lawU2 N) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hmem] with uu huu
    have h := hG.nonneg_on huu
    have h' := hG.le_one huu
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by simp only [Function.comp] at h; linarith, h'⟩
  refine ⟨hint, ?_⟩
  have hlin : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => a + b * dotp uu.1 uu.2)
      (lawU2 N) := (integrable_const a).add (iD.const_mul b)
  have hmono := integral_mono_ae hlin hint (by
    filter_upwards [hmem] with uu huu using hab _ huu)
  have a1 := integral_add (integrable_const a) (iD.const_mul b)
  have a2 : ∫ uu : (Fin N → ℝ) × (Fin N → ℝ), b * dotp uu.1 uu.2 ∂lawU2 N =
      b * ∫ uu : (Fin N → ℝ) × (Fin N → ℝ), dotp uu.1 uu.2 ∂lawU2 N := integral_const_mul _ _
  beta_reduce at a1
  rw [a1, a2, eD] at hmono
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero] at hmono
  have : a = kappa (kappa 0) := by
    have := heq; simp only [mul_zero, add_zero, Function.comp] at this; exact this
  rw [← this]
  exact hmono

/-- `E_{W,u,u′} t_x ≥ κ(κ(0)) − eW n m λ`. -/
theorem T_mean_lower (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hn : 1 ≤ n) {lam : ℝ} (hl : 0 < lam) :
    kappa (kappa 0) - eW n mW lam ≤
      ∫ z, tX (N := N) (mW := mW) (n := n) z ∂((lawU2 N).prod (mlpGauss N mW n)) := by
  have := lawU2_prob hN
  have hi := integrable_tX (mW := mW) hn hN
  rw [integral_prod _ hi]
  obtain ⟨iK, lK⟩ := kk_sphere_lower hN
  have hg : Integrable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - eW n mW lam) (lawU2 N) := iK.sub (integrable_const _)
  have hmono := integral_mono_ae hg hi.integral_prod_left (by
    filter_upwards [lawU2_ae_unit hN] with uu huu
    exact world_cos_lower hN hmW hn huu.1 huu.2 hl)
  have a1 := integral_sub iK (integrable_const (eW n mW lam))
  beta_reduce at a1
  rw [a1] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  linarith

lemma kappa6_eq : kappa^[4] (kappa (kappa 0)) = kappa^[6] 0 := rfl

/-- `E κ^{∘4}(t_x) ≥ κ^{∘6}(0) − eW n m λ`. -/
theorem k4_mean_lower (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hn : 1 ≤ n) {lam : ℝ} (hl : 0 < lam) :
    Integrable (fun z => kappa^[4] (tX (N := N) (mW := mW) (n := n) z))
      ((lawU2 N).prod (mlpGauss N mW n)) ∧
    kappa^[6] 0 - eW n mW lam ≤
      ∫ z, kappa^[4] (tX (N := N) (mW := mW) (n := n) z) ∂((lawU2 N).prod (mlpGauss N mW n)) := by
  have := lawU2_prob hN
  have hG : KGood (kappa^[4]) := kGood_iterate 3
  have hq : kappa (kappa 0) ∈ Icc (-1 : ℝ) 1 := kappa_mem_Icc (kappa_mem_Icc KGood.zero_mem)
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support hq
  have hi := integrable_tX (mW := mW) hn hN
  have hint : Integrable (fun z => kappa^[4] (tX (N := N) (mW := mW) (n := n) z))
      ((lawU2 N).prod (mlpGauss N mW n)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hG.cont.measurable.comp measurable_tX).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hG.nonneg_on (tX_mem hn z)], hG.le_one (tX_mem hn z)⟩
  refine ⟨hint, ?_⟩
  have hlin : Integrable (fun z => a + b * tX (N := N) (mW := mW) (n := n) z)
      ((lawU2 N).prod (mlpGauss N mW n)) := (integrable_const a).add (hi.const_mul b)
  have hmono := integral_mono hlin hint (fun z => hab _ (tX_mem hn z))
  have a1 := integral_add (integrable_const a) (hi.const_mul b)
  have a2 : ∫ z, b * tX (N := N) (mW := mW) (n := n) z ∂((lawU2 N).prod (mlpGauss N mW n)) =
      b * ∫ z, tX (N := N) (mW := mW) (n := n) z ∂((lawU2 N).prod (mlpGauss N mW n)) :=
    integral_const_mul _ _
  beta_reduce at a1
  rw [a1, a2] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  have hT := T_mean_lower (N := N) hN hmW hn hl
  have heW : 0 ≤ eW n mW lam := by
    have h1 := epsW_nonneg mW
    have h2 : 0 ≤ kappa 0 := (kappa_mem (by norm_num) (by norm_num)).1
    unfold eW; positivity
  rw [← kappa6_eq, ← heq]
  nlinarith [mul_le_mul_of_nonneg_left hT hb0]

lemma kgen_fff_eq (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n)
    (p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1) :
    kgen false false false (uu, (w, p)) = kern p.2.2 p.1 p.1 (xW w uu.1) (xW w uu.2) := rfl

lemma kgen_fff_section (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    (uu : (Fin N → ℝ) × (Fin N → ℝ)) (w : MlpParam N mW n) :
    4 / (n : ℝ) * (kappa^[4] (tX (uu, w)) - eA n mA mF) ≤
      ∫ p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1, kgen false false false (uu, (w, p))
        ∂((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1))) := by
  simp only [kgen_fff_eq]
  exact kern_pair_lower hn hmA hmF (normSq_xW hn w uu.1) (normSq_xW hn w uu.2)

/-- **The lower bound of `b₂`** (paper Statement M, `b₂ ≥ S(Q − e_b)`): for every `λ > 0`,
`b2 ≥ (4/n)·(κ^{∘6}(0) − eW n m_W λ − eA n m_A m_F)`. -/
theorem b2_lower (hN : 1 ≤ N) (hmW : 1 ≤ mW) (hn : 1 ≤ n) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {lam : ℝ} (hl : 0 < lam) :
    4 / (n : ℝ) * (kappa^[6] 0 - eW n mW lam - eA n mA mF) ≤ b2 N mW n mA mF := by
  have := lawU2_prob hN
  obtain ⟨iK, lK⟩ := k4_mean_lower (N := N) hN hmW hn hl
  have hg : Integrable (fun z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n =>
      4 / (n : ℝ) * (kappa^[4] (tX z) - eA n mA mF)) ((lawU2 N).prod (mlpGauss N mW n)) :=
    (iK.sub (integrable_const _)).const_mul _
  have key := integral_assoc_ge (lawU2 N) (mlpGauss N mW n)
    ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    (f := kgen false false false) (kgen_integrable hn hN false false false) hg
    (kgen_fff_section hn hmA hmF)
  rw [b2_eq]
  refine le_trans ?_ key
  have a1 : ∫ z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n,
      4 / (n : ℝ) * (kappa^[4] (tX z) - eA n mA mF) ∂((lawU2 N).prod (mlpGauss N mW n)) =
      4 / (n : ℝ) * ∫ z : ((Fin N → ℝ) × (Fin N → ℝ)) × MlpParam N mW n,
      (kappa^[4] (tX z) - eA n mA mF) ∂((lawU2 N).prod (mlpGauss N mW n)) :=
    integral_const_mul _ _
  have a2 := integral_sub iK (integrable_const (eA n mA mF))
  beta_reduce at a2
  rw [a1, a2]
  simp only [integral_const, probReal_univ, one_smul]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end BstLean.Part132

open BstLean.Part132 in
#print axioms T_mean_lower
open BstLean.Part132 in
#print axioms b2_lower
