import BstLean.Part151VAfin
import BstLean.Part151Br

/-!
# Part 151, Proposition VA (b), second form: hypotheses on `(W, A₁, A₂)` only

Role: `delegations/statements/p151-spec.md`, items 3 and 4. The last matrix `A₃` of `A` enters
the hypotheses of `H2_of_Astage` only through `|c_A|² = |A₃b|²`; the event `E_c` of Lemma V
(`lemmaEc` of `Part151Br`, charge `e^{−L_c}`) handles it.

* `H2_of_Astage'`: `H2_of_Astage` with the hypotheses on `X3` needed only on `X12`.
* `X3c`: the event `E_c` as a set of values of `(W, A)` (certain outside `X12`).
* **`H2_of_A12`**: `H2` from a set `X12` of values of `(W, (A₁, A₂))` on which `b ≠ 0`,
  `e_b ≤ 1`, `‖C_r‖_op ≤ Mr`, `Dv ≤ D̄_v`.
* **`theorem5_frameA12`**, **`theorem5_frameProg`**: the success bounds for `gSampH bh k` and for
  the straight-line program `fullProg150 k n J`.
* `H2_of_A12_Cr`, `theorem5_frameA12_Cr`: with Lemma Cr in the place of `‖C_r‖_op ≤ Mr`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (tauWA)
open BstLean.Part149 (thA tauOutOf measurable_thA)
open BstLean.Part150 (CMap gSampH bTW measurable_bTW fullProg150 fullVal)

section va2

variable {k n : ℕ} {bh : CMap n}

/-- `H2_of_Astage` with the hypotheses on `X3` needed only where `(W, (A₁, A₂)) ∈ X12`. -/
theorem H2_of_Astage' (hn : 1 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)} (h3 : MeasurableSet X3)
    {p3 : ℝ} (hp3 : ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).real X3ᶜ ≤ p3)
    {Dbar Ebar : ℝ}
    (hD : ∀ W A, (W, A) ∈ X3 → (W, thA A) ∈ X12 → Dc bh W A ≤ Dbar)
    (hE : ∀ W A, (W, A) ∈ X3 → (W, thA A) ∈ X12 →
      normSq (cAv bh W A) + n * sigP bh W A ^ 2 ≤ Ebar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) :
    H2 n k bh univ (EVA k bh X12 X3 δ uF Mr Lc)
      (vbar n k δ Dbar Ebar (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4)
      (p12 + p3 + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ + 3 * Real.exp (-Lc)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the probability: from `H2_of_Astage` with trivial bounds is not available; redo the union
  refine ⟨EVA_meas hbh h12 h3 δ uF Mr Lc, ?_, ?_, fun _ _ => mem_univ _⟩
  · have e : (EVA k bh X12 X3 δ uF Mr Lc)ᶜ =
        B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ ∪
          Bs k bh uF Lc ∪ BU k bh X12 uF Mr Lc := compl_compl _
    rw [e]
    have q1 := prob_X12 (k := k) h12 hp12
    have q2 := prob_X3 (k := k) h3 hp3
    have q3 := prob_ON (k := k) hn huF
    have q4 := prob_Tm (k := k) hn hbh h12 hb hδ
    have q5 := prob_FE (k := k) hn hbh hδ
    have q6 := prob_JU (k := k) hn hbh hδ
    have q7 := prob_s hn hk hbh huF hLc
    have q8 := prob_U (k := k) hn hbh h12 hb hMr0 hCr huF hLc
    have u1 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ ∪
        Bs k bh uF Lc) (BU k bh X12 uF Mr Lc)
    have u2 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ)
      (Bs k bh uF Lc)
    have u3 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ) (BJU k bh δ)
    have u4 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ) (BFE k bh δ)
    have u5 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF) (BTm k bh X12 δ)
    have u6 := measureReal_union_le (μ := fixP k n) (B12 k X12 ∪ B3 k X3) (BON k uF)
    have u7 := measureReal_union_le (μ := fixP k n) (B12 k X12) (B3 k X3)
    linarith
  · intro ω hω
    -- on `E`, `(W, (A₁, A₂)) ∈ X12`; replace `X3` by `X3 ∩ {X12}`
    set X3' : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) :=
      {q | q ∈ X3 ∧ (q.1, thA q.2) ∈ X12} with hX3'
    have h12ω : (ω.1.1, thA ω.1.2.1) ∈ X12 := by
      by_contra h
      exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
    have hω' : ω ∈ EVA k bh X12 X3' δ uF Mr Lc := by
      intro hbad
      apply hω
      rcases hbad with ((((((h | h) | h) | h) | h) | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
      · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ?_))))))
        intro h3ω
        exact h ⟨h3ω, h12ω⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hg := good_of_EVA (X3 := X3') (Dbar := Dbar) (Ebar := Ebar) hb hCr
      (fun W A h => hD W A h.1 h.2) (fun W A h => hE W A h.1 h.2) hω'
    have hv : vHat bh k ω ≤ vbar n k δ Dbar Ebar (LFc n uF) Mr Lc :=
      vHat_le_of_good hn hk hδ hMr0.le hg
    refine hv.trans (le_of_eq ?_)
    field_simp

/-! ## The event `E_c` as a set of values of `(W, A)` -/

/-- **The event `E_c`** (certain outside `X12`): `|A₃b|² ≤ t_A|b|²·n(1 + δ_c)`,
`δ_c = deltaC n L`. -/
def X3c (bh : CMap n) (X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))) (L : ℝ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) :=
  {q | (q.1, thA q.2) ∈ X12 → normSq (q.2.2.2 *ᵥ bh (q.1, thA q.2)) ≤
    2 / (mA n : ℝ) * normSq (bh (q.1, thA q.2)) * n * (1 + deltaC n L)}

lemma X3c_meas (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (L : ℝ) : MeasurableSet (X3c bh X12 L) := by
  have hq : Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n =>
      (q.1, thA q.2)) := measurable_fst.prodMk (measurable_thA.comp measurable_snd)
  have hb : Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n =>
      bh (q.1, thA q.2)) := hbh.comp hq
  have hc : Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n =>
      q.2.2.2 *ᵥ bh (q.1, thA q.2)) :=
    meas_cAv (fW := fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n => q.1)
      (fA := fun q => q.2) hbh measurable_fst measurable_snd
  have hns : ∀ {d : ℕ}, Measurable (fun v : Fin d → ℝ => normSq v) := by
    intro d; unfold normSq; fun_prop
  have hle : MeasurableSet {q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n |
      normSq (q.2.2.2 *ᵥ bh (q.1, thA q.2)) ≤
        2 / (mA n : ℝ) * normSq (bh (q.1, thA q.2)) * n * (1 + deltaC n L)} :=
    measurableSet_le (hns.comp hc)
      (((measurable_const.mul (hns.comp hb)).mul measurable_const).mul measurable_const)
  have e : X3c bh X12 L = ((fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n =>
      (q.1, thA q.2)) ⁻¹' X12)ᶜ ∪ {q | normSq (q.2.2.2 *ᵥ bh (q.1, thA q.2)) ≤
        2 / (mA n : ℝ) * normSq (bh (q.1, thA q.2)) * n * (1 + deltaC n L)} := by
    ext q
    simp only [X3c, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
    tauto
  rw [e]
  exact (hq h12).compl.union hle

/-- `(W, A)` to `((W, (A₁, A₂)), A₃)`. -/
def eWA' (q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) :
    (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) × Matrix (Fin n) (Fin (mA n)) ℝ :=
  ((q.1, ((q.2.1, q.2.2.1) : HidParam n (mA n))), q.2.2.2)

def eWA (p : (MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ×
    Matrix (Fin n) (Fin (mA n)) ℝ) : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n :=
  (p.1.1, (p.1.2.1, p.1.2.2, p.2))

lemma WA_map :
    ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).map (eWA' (n := n)) =
      ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).prod
        (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
  have sA : (mlpGauss n (mA n) n).map
      (fun A : MlpParam n (mA n) n => (((A.1, A.2.1) : HidParam n (mA n)), A.2.2)) =
      (hidGauss n (mA n)).prod (gaussMat n (mA n) (2 / (mA n : ℝ))) := by
    unfold mlpGauss hidGauss
    exact assoc_symm_map _ _ _
  have h := map_snd_prod (mlpGauss (2 * n) (mW n) n) (by fun_prop) sA
  have h2 := assoc_symm_map (mlpGauss (2 * n) (mW n) n) (hidGauss n (mA n))
    (gaussMat n (mA n) (2 / (mA n : ℝ)))
  rw [← h, Measure.map_map (by fun_prop) (by fun_prop)] at h2
  rw [← h2]
  rfl

/-- `Pr(E_cᶜ) ≤ e^{−L}` (the set `X12ᶜ` is not charged). -/
theorem X3c_prob (hn : 1 ≤ n) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {L : ℝ} (hL : 0 ≤ L) :
    ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).real (X3c bh X12 L)ᶜ ≤
      Real.exp (-L) := by
  refine prob_slice _ _ _ (e' := eWA' (n := n)) (e := eWA (n := n)) (by unfold eWA'; fun_prop)
    (by unfold eWA; fun_prop) WA_map (fun _ => rfl) (X3c_meas hbh h12 L).compl
    (Real.exp_pos _).le ?_
  intro x
  refine (measureReal_mono ?_).trans (lemmaEc bh x.1 x.2.1 x.2.2 hn hL)
  intro A₃ hA
  simp only [mem_ofPred_eq, mem_compl_iff, X3c, eWA] at hA ⊢
  by_contra hcon
  exact hA fun _ => not_lt.mp hcon

/-! ## The frame with hypotheses on `(W, A₁, A₂)` only -/

/-- **Proposition VA (b) with hypotheses on `(W, A₁, A₂)` only.** `X12` is a measurable set of
values of `(W, (A₁, A₂))` with `Pr(X12ᶜ) ≤ p12`, on which: the centre `b` is not `0`;
`t_A|b|² ≤ 2/n` (`e_b ≤ 1`); `‖C_r‖_op ≤ Mr`; `Dv ≤ D̄_v` (`Dv = n·E|v − v_p|²`). Then `H2` holds
with `c_V = vbar(D̄ = (1 + δ_c)D̄_v, Ē = 2(1 + δ_c))·n²/4`, `δ_c = deltaC n L_c`, and
`p₂ = p12 + e^{−L_c} + 2e^{−u_F²/2} + 3·chF n δ + 3e^{−L_c}`. -/
theorem H2_of_A12 (hn : 1 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ)) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → Dv bh W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) :
    H2 n k bh univ (EVA k bh X12 (X3c bh X12 Lc) δ uF Mr Lc)
      (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc *
        (n : ℝ) ^ 2 / 4)
      (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
        3 * Real.exp (-Lc)) := by
  have hdc := deltaC_nonneg n hLc
  refine H2_of_Astage' hn hk hbh h12 hp12 hb hMr0 hCr (X3c_meas hbh h12 Lc)
    (X3c_prob hn hbh h12 hLc) ?_ ?_ hδ huF hLc
  · intro W A h3 hx
    have hc := h3 hx
    have h1 := Dc_le_Dv bh W A.1 A.2.1 hn (hb _ hx) hdc A.2.2 hc
    have h2 := hDv W A.1 A.2.1 hx
    have h4 : (1 + deltaC n Lc) * Dv bh W A.1 A.2.1 ≤ (1 + deltaC n Lc) * Dvbar :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    exact h1.trans h4
  · intro W A h3 hx
    have hc := h3 hx
    exact energy_le bh W A.1 A.2.1 hn hdc A.2.2 hc (he _ hx)

lemma vbar_pos' (n k : ℕ) {δ Dbar Ebar LF Mr Lc : ℝ} (hδ : 0 < δ) (hMr0 : 0 < Mr) :
    0 < vbar n k δ Dbar Ebar LF Mr Lc * (n : ℝ) ^ 2 / 4 ∨ (n : ℝ) = 0 := by
  by_cases h : (n : ℝ) = 0
  · exact Or.inr h
  · left
    have := vbar_pos n k (Dbar := Dbar) (Ebar := Ebar) (LF := LF) (Lc := Lc) hδ hMr0
    positivity

/-- **The frame of Theorem 5 with hypotheses on `(W, A₁, A₂)` only**, for the estimator
`gSampH bh k`, every `n ≥ 4096`. -/
theorem theorem5_frameA12 (hn : 4096 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ)) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → Dv bh W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc *
            (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := H2_of_A12 hn1 hk hbh h12 hp12 hb he hMr0 hCr hDv hδ huF hLc
  have hcV := (vbar_pos' n k (Dbar := (1 + deltaC n Lc) * Dvbar)
    (Ebar := 2 * (1 + deltaC n Lc)) (LF := LFc n uF) (Lc := Lc) hδ hMr0).resolve_right hn0.ne'
  exact condLeanSamp151 hn hbh h2 hcV hεW0 hεW hθ0 hθ1

/-- **The frame of Theorem 5 for the straight-line program `fullProg150 k n J` of Part 150**
(centre `bTW J`), with hypotheses on `(W, A₁, A₂)` only; one more hypothesis on `X12`:
`τ̃₀ > 0`. -/
theorem theorem5_frameProg (hn : 4096 ≤ n) (hk : 1 ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK (bTW J) W A₁ A₂ Mr)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc *
            (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := H2_of_A12 (k := k) hn1 hk (measurable_bTW J) h12 hp12 hb he hMr0 hCr hDv hδ huF hLc
  have hcV := (vbar_pos' n k (Dbar := (1 + deltaC n Lc) * Dvbar)
    (Ebar := 2 * (1 + deltaC n Lc)) (LF := LFc n uF) (Lc := Lc) hδ hMr0).resolve_right hn0.ne'
  have hτE : ∀ ω ∈ EVA k (bTW J) X12 (X3c (bTW J) X12 Lc) δ uF Mr Lc, 0 < tauWA ω.1.1 := by
    intro ω hω
    have h12ω : (ω.1.1, thA ω.1.2.1) ∈ X12 := by
      by_contra h
      exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
    have h := hτ (ω.1.1, thA ω.1.2.1) h12ω
    exact h
  exact condLeanProg151 hn h2 hτE hcV hεW0 hεW hθ0 hθ1

/-! ## With Lemma Cr -/

/-- `‖C_r‖_op ≤ Mcov + Mb` from the covariance bound `Mcov` of `a₂` and the centre error
`t_A|ā₂ − b|² ≤ Mb` (Lemma Cr). -/
lemma CrOK_of_cov (hn : 1 ≤ n) {W : MlpParam (2 * n) (mW n) n}
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (hb : bh (W, (A₁, A₂)) ≠ 0) {Mcov Mb : ℝ} (hM0 : 0 ≤ Mcov)
    (hcov : ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
      (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
        ∂stdGauss (Fin n) ≤ Mcov * ∑ j, w j ^ 2)
    (hcen : 2 / (mA n : ℝ) * normSq (fun j =>
      (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤ Mb) :
    CrOK bh W A₁ A₂ (Mcov + Mb) := by
  intro w
  refine (lemmaCr bh W A₁ A₂ hn hb hM0 hcov w).trans ?_
  have hw : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right (by linarith) hw

/-- `H2_of_A12` with Lemma Cr: the hypothesis `‖C_r‖_op ≤ Mr` is replaced by the covariance
bound `‖t_A·Cov_ξ(a₂)‖_op ≤ Mcov` and the centre error `t_A|ā₂ − b|² ≤ Mb`; `Mr = Mcov + Mb`. -/
theorem H2_of_A12_Cr (hn : 1 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ)) {Mcov Mb : ℝ}
    (hM0 : 0 ≤ Mcov) (hMr0 : 0 < Mcov + Mb)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ Mcov * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤ Mb)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → Dv bh W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) :
    H2 n k bh univ (EVA k bh X12 (X3c bh X12 Lc) δ uF (Mcov + Mb) Lc)
      (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF) (Mcov + Mb)
        Lc * (n : ℝ) ^ 2 / 4)
      (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
        3 * Real.exp (-Lc)) :=
  H2_of_A12 hn hk hbh h12 hp12 hb he hMr0
    (fun W A₁ A₂ hx => CrOK_of_cov hn (hb _ hx) hM0 (hcov W A₁ A₂ hx) (hcen W A₁ A₂ hx))
    hDv hδ huF hLc

/-- `theorem5_frameA12` with Lemma Cr. -/
theorem theorem5_frameA12_Cr (hn : 4096 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ)) {Mcov Mb : ℝ}
    (hM0 : 0 ≤ Mcov) (hMr0 : 0 < Mcov + Mb)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ Mcov * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤ Mb)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → Dv bh W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF)
            (Mcov + Mb) Lc * (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  exact theorem5_frameA12 hn hk hbh h12 hp12 hb he hMr0
    (fun W A₁ A₂ hx => CrOK_of_cov hn1 (hb _ hx) hM0 (hcov W A₁ A₂ hx) (hcen W A₁ A₂ hx))
    hDv hδ huF hLc hεW0 hεW hθ0 hθ1

end va2

end BstLean.Part151
