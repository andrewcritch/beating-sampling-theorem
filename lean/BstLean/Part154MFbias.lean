import BstLean.Part154MFa
import BstLean.Part154MFcalc
import BstLean.Part132Upper

/-!
# Part 154: Lemma MF, Step 3 (the bias term) for a fixed value `a` of `ā`
Statements fixed by the lead agent. Auxiliary: `phiG_le_phiG_zero`, `setInt_abs_le`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : Ω → Fin m → ℝ} {ℓ πg : ℝ}

/-- `φ(x) ≤ φ(0)`. -/
lemma phiG_le_phiG_zero (x : ℝ) : phiG x ≤ phiG 0 := by
  unfold phiG
  have h : rexp (-(x ^ 2 / 2)) ≤ rexp (-((0 : ℝ) ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Cauchy–Schwarz on a set: `E[|X|; B] ≤ √(μ B)·√(E X²)`. -/
lemma setInt_abs_le {X : Ω → ℝ} (hX : Measurable X) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    {B : Set Ω} (hB : MeasurableSet B) :
    Integrable (fun ω => B.indicator (fun _ => (1 : ℝ)) ω * |X ω|) μ ∧
    ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω * |X ω| ∂μ ≤ √(μ.real B) * √(∫ ω, X ω ^ 2 ∂μ) := by
  have hIm : Measurable (B.indicator (fun _ : Ω => (1 : ℝ))) := measurable_const.indicator hB
  have hsq : ∀ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω ^ 2 = B.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    intro ω; by_cases h : ω ∈ B <;> simp [h]
  have habs : ∀ ω, |B.indicator (fun _ : Ω => (1 : ℝ)) ω| = B.indicator (fun _ : Ω => (1 : ℝ)) ω := by
    intro ω; by_cases h : ω ∈ B <;> simp [h]
  have hI2 : Integrable (fun ω => B.indicator (fun _ : Ω => (1 : ℝ)) ω ^ 2) μ := by
    simp_rw [hsq]; exact (integrable_const (1 : ℝ)).indicator hB
  have hint : ∫ ω, B.indicator (fun _ : Ω => (1 : ℝ)) ω ^ 2 ∂μ = μ.real B := by
    simp_rw [hsq]; rw [integral_indicator_const _ hB]; simp
  have h := BstLean.Part132.integral_mul_le_sqrt hIm hX hI2 hX2
  simp_rw [habs] at h
  rw [hint] at h
  exact h

/-- **The bias term** for a fixed `a`: `|E_ω 𝒢(βa, ς²) − ψ_s(a)| ≤ s(𝔠₀ + 𝔠₁|ζ₀| + 𝔠₂ζ₀²)`,
`ζ₀ = a/√Γ̄`. -/
theorem MFHyp.YF_bias (H : MFHyp μ f ℓ πg) (a : ℝ) :
    Integrable (fun ω => psiS (√(sig2F μ f ω)) (betaF μ f ω * a)) μ ∧
    |∫ ω, psiS (√(sig2F μ f ω)) (betaF μ f ω * a) ∂μ - psiS (sF μ f) a| ≤
      sF μ f * (cc0 (ℓ ^ 2 / sF2 μ f) πg + cc1 (ℓ ^ 2 / sF2 μ f) πg * (|a| / √(GamBarF μ f)) +
        cc2 (ℓ ^ 2 / sF2 μ f) * (a ^ 2 / GamBarF μ f)) := by
  obtain ⟨hs, hs2⟩ := H.sF_pos
  obtain ⟨hbi, hb1, hb2i, hδ0, hΓδ⟩ := H.F1
  obtain ⟨hsi, hsint⟩ := H.F2
  obtain ⟨hd2i, hd2⟩ := H.F3
  have hM3 := H.M3
  have hπ0 := H.hπ0
  have hΓ := H.hbar
  have hS : sF2 μ f = sF μ f ^ 2 := hs2.symm
  rw [hS] at hd2i hd2 hsint hM3 ⊢
  have hδe : ∫ ω, (betaF μ f ω - 1) ^ 2 ∂μ = delta2 μ f := rfl
  generalize sF μ f = s at *
  generalize GamBarF μ f = Γ at *
  generalize delta2 μ f = δ at *
  have hβm := H.meas_beta
  have hvm := H.meas_sig
  have hv0 := sig2F_nonneg μ f
  generalize betaF μ f = β at *
  generalize sig2F μ f = v at *
  clear hS hs2 H
  -- the constants
  obtain ⟨ϱ, hϱ⟩ : ∃ ϱ : ℝ, ϱ = ℓ ^ 2 / s ^ 2 := ⟨_, rfl⟩
  rw [← hϱ] at hd2 ⊢
  have hϱ0 : 0 ≤ ϱ := by rw [hϱ]; positivity
  have hℓ2 : ℓ ^ 2 = ϱ * s ^ 2 := by rw [hϱ]; field_simp
  have hν0 : 0 ≤ nuR ϱ := by unfold nuR; positivity
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = nuR ϱ := ⟨_, rfl⟩
  have hcc0 : cc0 ϱ πg = phiG 0 * ϱ / 2 + phiG 0 * ν / (2 * √2) + 3 / 2 * phiG 0 * √(πg * ν) := by
    rw [hν]; rfl
  have hcc1 : cc1 ϱ πg = phiG 1 * √(ϱ * ν) + 2 * √(πg * ϱ) := by rw [hν]; rfl
  have hcc2 : cc2 ϱ = phiG 0 * ϱ / √2 := rfl
  rw [← hν] at hd2 hν0
  clear hν hϱ
  rw [hcc0, hcc1, hcc2]
  clear hcc0 hcc1 hcc2
  -- square roots
  have hw0 : 0 < √(2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hww : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hwinv : (√(2 : ℝ))⁻¹ = √2 / 2 := by
    rw [inv_eq_iff_eq_inv, inv_div, eq_div_iff hw0.ne']; exact hww
  rw [Real.sqrt_mul hπ0, Real.sqrt_mul hϱ0, Real.sqrt_mul hπ0]
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = √2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √ϱ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = √ν := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = √πg := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = √Γ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = √δ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hn0 : 0 ≤ n := hn ▸ Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := hp ▸ Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := hD ▸ Real.sqrt_nonneg _
  have hg0 : 0 < g := hg ▸ Real.sqrt_pos.mpr hΓ
  have hr2 : r ^ 2 = ϱ := hr ▸ Real.sq_sqrt hϱ0
  have hn2 : n ^ 2 = ν := hn ▸ Real.sq_sqrt hν0
  have hg2 : g ^ 2 = Γ := hg ▸ Real.sq_sqrt hΓ.le
  have hD2 : D ^ 2 = δ := hD ▸ Real.sq_sqrt hδ0
  rw [← hw, ← hr, ← hn, ← hp, ← hg]
  rw [← hw] at hw0 hww hwinv
  have hDle : D ≤ r * s / g := by
    rw [le_div_iff₀ hg0]
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    calc (D * g) ^ 2 = Γ * δ := by rw [mul_pow, hD2, hg2]; ring
      _ ≤ ℓ ^ 2 := hΓδ
      _ = (r * s) ^ 2 := by rw [hℓ2, mul_pow, hr2]
  have hδle : δ ≤ ϱ * s ^ 2 / Γ := by
    rw [le_div_iff₀ hΓ, ← hℓ2]; linarith
  -- the bad set
  obtain ⟨B, hBdef⟩ : ∃ B : Set Ω, B = {ω | v ω < s ^ 2 / 2} := ⟨_, rfl⟩
  have hB : MeasurableSet B := by rw [hBdef]; exact measurableSet_lt hvm measurable_const
  rw [← hBdef] at hM3
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = √(μ.real B) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ Real.sqrt_nonneg _
  have hqp : q ≤ p := by rw [hq, hp]; exact Real.sqrt_le_sqrt hM3
  have hbm : Measurable (fun ω => β ω - 1) := hβm.sub measurable_const
  have hdm : Measurable (fun ω => v ω - s ^ 2) := hvm.sub measurable_const
  obtain ⟨hJi, hJ⟩ := BstLean.Part132.integral_mul_le_sqrt hbm hdm hb2i hd2i
  obtain ⟨hJbi, hJb⟩ := setInt_abs_le hbm hb2i hB
  obtain ⟨hJdi, hJd⟩ := setInt_abs_le hdm hd2i hB
  rw [hδe, ← hD] at hJ
  rw [hδe, ← hD, ← hq] at hJb
  rw [← hq] at hJd
  have hE0 : 0 ≤ ∫ ω, (v ω - s ^ 2) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hele : √(∫ ω, (v ω - s ^ 2) ^ 2 ∂μ) ≤ n * s ^ 2 := by
    refine (Real.sqrt_le_sqrt hd2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hν0, ← hn, Real.sqrt_sq (by positivity)]
  obtain ⟨E2, hE2⟩ : ∃ E2 : ℝ, E2 = ∫ ω, (v ω - s ^ 2) ^ 2 ∂μ := ⟨_, rfl⟩
  rw [← hE2] at hJ hJd hele hd2 hE0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = √E2 := ⟨_, rfl⟩
  rw [← he] at hJ hJd hele
  obtain ⟨J, hJe⟩ : ∃ J : ℝ, J = ∫ ω, |β ω - 1| * |v ω - s ^ 2| ∂μ := ⟨_, rfl⟩
  obtain ⟨Jb, hJbe⟩ : ∃ J : ℝ, J = ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1| ∂μ :=
    ⟨_, rfl⟩
  obtain ⟨Jd, hJde⟩ : ∃ J : ℝ, J = ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω * |v ω - s ^ 2| ∂μ :=
    ⟨_, rfl⟩
  rw [← hJe] at hJ
  rw [← hJbe] at hJb
  rw [← hJde] at hJd
  have hInd0 : ∀ ω, 0 ≤ B.indicator (fun _ => (1 : ℝ)) ω := fun ω =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  -- coefficients
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = PhiG (a / s) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = phiG (a / s) / (2 * s) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact div_nonneg (BstLean.Part153.phiG_pos _).le (by positivity)
  have hQle : Q ≤ phiG 0 / (2 * s) := by
    rw [hQ]; exact div_le_div_of_nonneg_right (phiG_le_phiG_zero _) (by positivity)
  have hφ0 := (BstLean.Part153.phiG_pos 0).le
  have hφ1 := (BstLean.Part153.phiG_pos 1).le
  obtain ⟨φ0, hφ0e⟩ : ∃ φ : ℝ, φ = phiG 0 := ⟨_, rfl⟩
  obtain ⟨φ1, hφ1e⟩ : ∃ φ : ℝ, φ = phiG 1 := ⟨_, rfl⟩
  rw [← hφ0e] at hQle hφ0
  rw [← hφ1e] at hφ1
  rw [← hφ0e, ← hφ1e]
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = w * φ0 / (2 * s) * a ^ 2 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = φ1 / s ^ 2 * |a| := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = 1 / 2 * (φ0 / (w * s ^ 3)) := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ c : ℝ, c = 2 * |a| := ⟨_, rfl⟩
  obtain ⟨k2, hk2⟩ : ∃ c : ℝ, c = 3 / 2 * φ0 / s := ⟨_, rfl⟩
  have hc1' : 0 ≤ c1 := by rw [hc1]; positivity
  have hc2' : 0 ≤ c2 := by rw [hc2]; positivity
  have hc3' : 0 ≤ c3 := by rw [hc3]; positivity
  have hk1' : 0 ≤ k1 := by rw [hk1]; positivity
  have hk2' : 0 ≤ k2 := by rw [hk2]; positivity
  -- integrability
  have i1 : Integrable (fun ω => c1 * (β ω - 1) ^ 2) μ := hb2i.const_mul c1
  have i2 : Integrable (fun ω => c2 * (|β ω - 1| * |v ω - s ^ 2|)) μ := hJi.const_mul c2
  have i3 : Integrable (fun ω => c3 * (v ω - s ^ 2) ^ 2) μ := hd2i.const_mul c3
  have i4 : Integrable (fun ω => k1 * (B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1|)) μ :=
    hJbi.const_mul k1
  have i5 : Integrable (fun ω => k2 * (B.indicator (fun _ => (1 : ℝ)) ω * |v ω - s ^ 2|)) μ :=
    hJdi.const_mul k2
  have i12 : Integrable (fun ω => c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|)) μ :=
    i1.add i2
  have i123 : Integrable (fun ω => c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
      c3 * (v ω - s ^ 2) ^ 2) μ := i12.add i3
  have i1234 : Integrable (fun ω => c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
      c3 * (v ω - s ^ 2) ^ 2 + k1 * (B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1|)) μ :=
    i123.add i4
  have iBd : Integrable (fun ω => c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
      c3 * (v ω - s ^ 2) ^ 2 + k1 * (B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1|) +
      k2 * (B.indicator (fun _ => (1 : ℝ)) ω * |v ω - s ^ 2|)) μ := i1234.add i5
  have eBd : ∫ ω, (c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
      c3 * (v ω - s ^ 2) ^ 2 + k1 * (B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1|) +
      k2 * (B.indicator (fun _ => (1 : ℝ)) ω * |v ω - s ^ 2|)) ∂μ =
      c1 * δ + c2 * J + c3 * E2 + k1 * Jb + k2 * Jd := by
    rw [integral_add i1234 i5, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
    simp only [integral_const_mul]
    rw [hδe, ← hJe, ← hE2, ← hJbe, ← hJde]
  -- the linear part
  have iL1 : Integrable (fun ω => P * ((β ω - 1) * a)) μ :=
    ((hbi.sub (integrable_const 1)).mul_const a).const_mul P
  have iL2 : Integrable (fun ω => Q * (v ω - s ^ 2)) μ :=
    (hsi.sub (integrable_const _)).const_mul Q
  have iL : Integrable (fun ω => P * ((β ω - 1) * a) + Q * (v ω - s ^ 2)) μ := iL1.add iL2
  have eL : ∫ ω, (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2)) ∂μ = -(Q * (Γ * δ)) := by
    rw [integral_add iL1 iL2, integral_const_mul, integral_const_mul, integral_mul_const,
      integral_sub hbi (integrable_const _), integral_sub hsi (integrable_const _), hb1, hsint]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  -- the pointwise bound
  have hpt : ∀ ω, |psiS (√(v ω)) (β ω * a) - psiS s a -
      (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2))| ≤
      c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
      c3 * (v ω - s ^ 2) ^ 2 + k1 * (B.indicator (fun _ => (1 : ℝ)) ω * |β ω - 1|) +
      k2 * (B.indicator (fun _ => (1 : ℝ)) ω * |v ω - s ^ 2|) := by
    intro ω
    have hT0 : 0 ≤ c1 * (β ω - 1) ^ 2 + c2 * (|β ω - 1| * |v ω - s ^ 2|) +
        c3 * (v ω - s ^ 2) ^ 2 := by positivity
    have hR0 : 0 ≤ k1 * |β ω - 1| + k2 * |v ω - s ^ 2| := by positivity
    rw [hP, hQ]
    by_cases h : ω ∈ B
    · have hG := G_rough (s := s) (v := v ω) (a := a) (β := β ω) hs (hv0 ω)
      rw [← hφ0e] at hG
      rw [Set.indicator_of_mem h]
      have e1 : 2 * (|β ω - 1| * |a|) + 3 / 2 * φ0 / s * |v ω - s ^ 2| =
          k1 * |β ω - 1| + k2 * |v ω - s ^ 2| := by rw [hk1, hk2]; ring
      rw [e1] at hG
      linarith
    · have h' : s ^ 2 / 2 ≤ v ω := by
        rw [hBdef] at h; exact not_lt.mp h
      have hG := G_taylor (s := s) (v := v ω) (a := a) (β := β ω) hs h'
      rw [← hφ0e, ← hφ1e, ← hw] at hG
      rw [Set.indicator_of_notMem h]
      refine hG.trans (le_of_eq ?_)
      rw [hc1, hc2, hc3]; ring
  have hpm : Measurable (fun ω => psiS (√(v ω)) (β ω * a)) :=
    BstLean.Part137.measurable_psiS.comp (hvm.sqrt.prodMk (hβm.mul_const a))
  have hLm : Measurable (fun ω => P * ((β ω - 1) * a) + Q * (v ω - s ^ 2)) :=
    ((hbm.mul_const a).const_mul P).add (hdm.const_mul Q)
  have iFL : Integrable (fun ω => psiS (√(v ω)) (β ω * a) - psiS s a -
      (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2))) μ :=
    Integrable.mono' iBd ((hpm.sub measurable_const).sub hLm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  have hFLle : |∫ ω, (psiS (√(v ω)) (β ω * a) - psiS s a -
      (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2))) ∂μ| ≤
      c1 * δ + c2 * J + c3 * E2 + k1 * Jb + k2 * Jd := by
    rw [← eBd, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le iBd
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hpt ω)
  have iψ : Integrable (fun ω => psiS (√(v ω)) (β ω * a)) μ := by
    refine ((iFL.add iL).add (integrable_const (psiS s a))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; ring
  refine ⟨iψ, ?_⟩
  have e0 : ∫ ω, psiS (√(v ω)) (β ω * a) ∂μ - psiS s a =
      ∫ ω, (psiS (√(v ω)) (β ω * a) - psiS s a -
        (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2))) ∂μ + -(Q * (Γ * δ)) := by
    rw [← eL, ← integral_add iFL iL]
    have e1 : ∫ ω, (psiS (√(v ω)) (β ω * a) - psiS s a) ∂μ =
        ∫ ω, psiS (√(v ω)) (β ω * a) ∂μ - psiS s a := by
      rw [integral_sub iψ (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
    rw [← e1]
    congr 1
    funext ω
    ring
  rw [e0]
  have hQΓ : 0 ≤ Q * (Γ * δ) := by positivity
  have hmain : |∫ ω, (psiS (√(v ω)) (β ω * a) - psiS s a -
        (P * ((β ω - 1) * a) + Q * (v ω - s ^ 2))) ∂μ + -(Q * (Γ * δ))| ≤
      Q * (Γ * δ) + (c1 * δ + c2 * J + c3 * E2 + k1 * Jb + k2 * Jd) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_of_nonneg hQΓ]
    linarith
  refine hmain.trans ?_
  have he0 : 0 ≤ e := he ▸ Real.sqrt_nonneg _
  have ew1 : φ0 * ϱ / w = φ0 * ϱ * (w / 2) := by rw [div_eq_mul_inv, hwinv]
  have ew2 : φ0 * ν / (2 * w) = φ0 * ν * (w / 4) := by
    rw [div_eq_mul_inv, mul_inv, hwinv]; ring
  have ew3 : c3 = φ0 * (w / 4) / s ^ 3 := by
    rw [hc3, div_eq_mul_inv φ0, mul_inv, hwinv]; ring
  rw [ew1, ew2]
  have t0 : Q * (Γ * δ) ≤ s * (φ0 * ϱ / 2) := by
    calc Q * (Γ * δ) ≤ φ0 / (2 * s) * (ϱ * s ^ 2) :=
          mul_le_mul hQle (hΓδ.trans_eq hℓ2) (by positivity) (by positivity)
      _ = s * (φ0 * ϱ / 2) := by field_simp
  have t1 : c1 * δ ≤ s * (φ0 * ϱ * (w / 2) * (a ^ 2 / Γ)) := by
    calc c1 * δ ≤ c1 * (ϱ * s ^ 2 / Γ) := mul_le_mul_of_nonneg_left hδle hc1'
      _ = s * (φ0 * ϱ * (w / 2) * (a ^ 2 / Γ)) := by
          rw [hc1]; field_simp
  have t2 : c2 * J ≤ s * (φ1 * (r * n) * (|a| / g)) := by
    have hJ' : J ≤ (r * s / g) * (n * s ^ 2) :=
      hJ.trans (mul_le_mul hDle hele he0 (by positivity))
    calc c2 * J ≤ c2 * ((r * s / g) * (n * s ^ 2)) := mul_le_mul_of_nonneg_left hJ' hc2'
      _ = s * (φ1 * (r * n) * (|a| / g)) := by
          rw [hc2]; field_simp
  have t3 : c3 * E2 ≤ s * (φ0 * ν * (w / 4)) := by
    calc c3 * E2 ≤ c3 * (ν * (s ^ 2) ^ 2) := mul_le_mul_of_nonneg_left hd2 hc3'
      _ = s * (φ0 * ν * (w / 4)) := by
          rw [ew3]; field_simp
  have t4 : k1 * Jb ≤ s * (2 * (p * r) * (|a| / g)) := by
    have hJ' : Jb ≤ p * (r * s / g) :=
      hJb.trans (mul_le_mul hqp hDle hD0 hp0)
    calc k1 * Jb ≤ k1 * (p * (r * s / g)) := mul_le_mul_of_nonneg_left hJ' hk1'
      _ = s * (2 * (p * r) * (|a| / g)) := by
          rw [hk1]; field_simp
  have t5 : k2 * Jd ≤ s * (3 / 2 * φ0 * (p * n)) := by
    have hJ' : Jd ≤ p * (n * s ^ 2) :=
      hJd.trans (mul_le_mul hqp hele he0 hp0)
    calc k2 * Jd ≤ k2 * (p * (n * s ^ 2)) := mul_le_mul_of_nonneg_left hJ' hk2'
      _ = s * (3 / 2 * φ0 * (p * n)) := by
          rw [hk2]; field_simp
  have efin : s * (φ0 * ϱ / 2 + φ0 * ν * (w / 4) + 3 / 2 * φ0 * (p * n) +
      (φ1 * (r * n) + 2 * (p * r)) * (|a| / g) + φ0 * ϱ * (w / 2) * (a ^ 2 / Γ)) =
      s * (φ0 * ϱ / 2) + s * (φ0 * ϱ * (w / 2) * (a ^ 2 / Γ)) + s * (φ1 * (r * n) * (|a| / g)) +
      s * (φ0 * ν * (w / 4)) + s * (2 * (p * r) * (|a| / g)) + s * (3 / 2 * φ0 * (p * n)) := by
    ring
  rw [efin]
  linarith

/-- **The linear term**, integrated over `ā = ζ·√Γ̄`. -/
theorem MFHyp.lin_term (H : MFHyp μ f ℓ πg) :
    ∫ ζ, (∫ ω, (PhiG (betaF μ f ω * (ζ * √(GamBarF μ f)) / √(sig2F μ f ω)) -
        PhiG (ζ * √(GamBarF μ f) / sF μ f)) ^ 2 ∂μ) ∂gaussianReal 0 1 ≤
      1 / π * (2 * (ℓ ^ 2 / sF2 μ f) +
        4 * (√2 - 1) ^ 2 * (GamBarF μ f / sF2 μ f) * nuR (ℓ ^ 2 / sF2 μ f)) + πg := by
  obtain ⟨hs, hs2⟩ := H.sF_pos
  obtain ⟨hbi, hb1, hb2i, hδ0, hΓδ⟩ := H.F1
  obtain ⟨hd2i, hd2⟩ := H.F3
  have hM3 := H.M3
  have hΓ := H.hbar
  have hS : sF2 μ f = sF μ f ^ 2 := hs2.symm
  rw [hS] at hd2i hd2 hM3 ⊢
  have hδe : ∫ ω, (betaF μ f ω - 1) ^ 2 ∂μ = delta2 μ f := rfl
  generalize sF μ f = s at *
  generalize GamBarF μ f = Γ at *
  generalize delta2 μ f = δ at *
  have hvm := H.meas_sig
  generalize betaF μ f = β at *
  generalize sig2F μ f = v at *
  clear hS hs2 H
  obtain ⟨ϱ, hϱ⟩ : ∃ ϱ : ℝ, ϱ = ℓ ^ 2 / s ^ 2 := ⟨_, rfl⟩
  rw [← hϱ] at hd2 ⊢
  have hℓ2 : ℓ ^ 2 = ϱ * s ^ 2 := by rw [hϱ]; field_simp
  have hϱ0 : 0 ≤ ϱ := by rw [hϱ]; positivity
  have hν0 : 0 ≤ nuR ϱ := by unfold nuR; positivity
  generalize nuR ϱ = ν at *
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (√2 - 1) ^ 2 := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨B, hBdef⟩ : ∃ B : Set Ω, B = {ω | v ω < s ^ 2 / 2} := ⟨_, rfl⟩
  have hB : MeasurableSet B := by rw [hBdef]; exact measurableSet_lt hvm measurable_const
  rw [← hBdef] at hM3
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 / (2 * π) * Γ * (4 * δ / s ^ 2 + 8 * c * ν / s ^ 2) :=
    ⟨_, rfl⟩
  have hin : ∀ ζ : ℝ, ∫ ω, (PhiG (β ω * (ζ * √Γ) / √(v ω)) - PhiG (ζ * √Γ / s)) ^ 2 ∂μ ≤
      ζ ^ 2 * K + πg := by
    intro ζ
    obtain ⟨m1, hm1⟩ : ∃ m1 : ℝ, m1 = 1 / (2 * π) * (ζ * √Γ) ^ 2 * 4 / s ^ 2 := ⟨_, rfl⟩
    obtain ⟨m2, hm2⟩ : ∃ m2 : ℝ, m2 = 1 / (2 * π) * (ζ * √Γ) ^ 2 * (8 * c) / s ^ 6 := ⟨_, rfl⟩
    have hm1' : 0 ≤ m1 := by rw [hm1]; positivity
    have hm2' : 0 ≤ m2 := by rw [hm2]; positivity
    have j1 : Integrable (fun ω => m1 * (β ω - 1) ^ 2) μ := hb2i.const_mul _
    have j2 : Integrable (fun ω => m2 * (v ω - s ^ 2) ^ 2) μ := hd2i.const_mul _
    have j3 : Integrable (fun ω => B.indicator (fun _ => (1 : ℝ)) ω) μ :=
      (integrable_const (1 : ℝ)).indicator hB
    have j12 : Integrable (fun ω => m1 * (β ω - 1) ^ 2 + m2 * (v ω - s ^ 2) ^ 2) μ := j1.add j2
    have jU : Integrable (fun ω => m1 * (β ω - 1) ^ 2 + m2 * (v ω - s ^ 2) ^ 2 +
        B.indicator (fun _ => (1 : ℝ)) ω) μ := j12.add j3
    have hpt : ∀ ω, (PhiG (β ω * (ζ * √Γ) / √(v ω)) - PhiG (ζ * √Γ / s)) ^ 2 ≤
        m1 * (β ω - 1) ^ 2 + m2 * (v ω - s ^ 2) ^ 2 + B.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : ω ∈ B
      · rw [Set.indicator_of_mem h]
        have h1 := PhiG_diff_le_one (β ω * (ζ * √Γ) / √(v ω)) (ζ * √Γ / s)
        have h2 : 0 ≤ m1 * (β ω - 1) ^ 2 + m2 * (v ω - s ^ 2) ^ 2 := by positivity
        linarith
      · rw [Set.indicator_of_notMem h]
        have h' : s ^ 2 / 2 ≤ v ω := by
          rw [hBdef] at h; exact not_lt.mp h
        have hG := PhiG_diff_sq_le (s := s) (v := v ω) (a := ζ * √Γ) (β := β ω) hs h'
        rw [← hc] at hG
        refine hG.trans (le_of_eq ?_)
        rw [hm1, hm2]; ring
    calc ∫ ω, (PhiG (β ω * (ζ * √Γ) / √(v ω)) - PhiG (ζ * √Γ / s)) ^ 2 ∂μ
        ≤ ∫ ω, (m1 * (β ω - 1) ^ 2 + m2 * (v ω - s ^ 2) ^ 2 +
            B.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) jU
            (Filter.Eventually.of_forall hpt)
      _ = m1 * δ + m2 * (∫ ω, (v ω - s ^ 2) ^ 2 ∂μ) + μ.real B := by
          rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
            hδe, integral_indicator_const _ hB]
          simp only [smul_eq_mul, mul_one]
      _ ≤ m1 * δ + m2 * (ν * (s ^ 2) ^ 2) + πg := by
          have := mul_le_mul_of_nonneg_left hd2 hm2'
          linarith
      _ = ζ ^ 2 * K + πg := by
          rw [hm1, hm2, hK, mul_pow, Real.sq_sqrt hΓ.le]
          field_simp
  have iK : Integrable (fun ζ : ℝ => ζ ^ 2 * K) (gaussianReal 0 1) :=
    (BstLean.Part130.integrable_pow_gauss 2).mul_const K
  calc ∫ ζ, (∫ ω, (PhiG (β ω * (ζ * √Γ) / √(v ω)) - PhiG (ζ * √Γ / s)) ^ 2 ∂μ)
        ∂gaussianReal 0 1
      ≤ ∫ ζ, (ζ ^ 2 * K + πg) ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ζ => integral_nonneg fun ω => sq_nonneg _)
          (iK.add (integrable_const _)) (Filter.Eventually.of_forall hin)
    _ = K + πg := by
        rw [integral_add iK (integrable_const _), integral_mul_const,
          BstLean.Part29.gaussMom_eq 2]
        simp only [integral_const, probReal_univ, one_smul]
        norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
    _ ≤ 1 / π * (2 * ϱ + 4 * c * (Γ / s ^ 2) * ν) + πg := by
        have eK : K = 1 / π * (2 * (Γ * δ / s ^ 2) + 4 * c * (Γ / s ^ 2) * ν) := by
          rw [hK]; ring
        have h1 : Γ * δ / s ^ 2 ≤ ϱ := by
          rw [div_le_iff₀ (by positivity)]; linarith
        have h2 : (0 : ℝ) ≤ 1 / π := by positivity
        rw [eK]
        have := mul_le_mul_of_nonneg_left h1 h2
        nlinarith

end BstLean.Part154
