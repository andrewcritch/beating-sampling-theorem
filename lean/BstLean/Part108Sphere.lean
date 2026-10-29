import BstLean.Part108Core

/-!
# Part 108: the sphere version of `W` at the fixed noise level, and the transfer to `bwSphere`

* `succ_nrm`: for `W = G/‖G‖`, success of the program at the fixed noise level `tauPaper` with
  blocks `ω` is success for `G` at the ideal level `tauOf d 1` with the Gaussian part of every
  block scaled by `s = ‖G‖/√D`. The realized spread and `B` do not depend on the scale of `W`.
* `tv_transfer`: the total-variation step (from `DrawsTV108`), integrated over the coefficients.
* `gauss_fixed`: the failure probability at the fixed level is at most the failure probability at
  the ideal level, plus `2/(ε²D)` (Chebyshev for `‖G‖²`), plus the total-variation term.
* `sphere_succ`: the transfer from the Gaussian coordinates to the product of the three
  Bombieri–Weyl sphere distributions.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

section scale

variable {N n d k : ℕ}

lemma Bu_smul {s : ℝ} (hs : 0 < s) (W : CoefIdx N n d → ℝ) (φ : (Fin n → ℝ) → ℝ) :
    Bu (s • W) φ = Bu W φ := by
  unfold Bu
  simp only [BstLean.Part106.bwEval_smul, BstLean.Part106.sphProj_smul hs]

lemma Vu_smul {s : ℝ} (hs : 0 < s) (W : CoefIdx N n d → ℝ) (φ : (Fin n → ℝ) → ℝ) :
    Vu (s • W) φ = Vu W φ := by
  unfold Vu
  simp only [Bu_smul hs, BstLean.Part106.bwEval_smul, BstLean.Part106.sphProj_smul hs]

lemma gVal_scale (W : CoefIdx N n d → ℝ) (τ s : ℝ) (φ : (Fin n → ℝ) → ℝ) (ω : Draws N n k) :
    BstLean.Part106.gVal W (τ * s) φ ω = BstLean.Part106.gVal W τ φ (scaleDraws s ω) := by
  unfold BstLean.Part106.gVal BstLean.Part106.standIn scaleDraws
  simp only [mul_smul]

/-- **The coupling**: the program at the fixed level for `W/‖W‖` is the program at the ideal
level for `W` with scaled Gaussian inputs. -/
lemma succ_nrm (W : CoefIdx N n d → ℝ) (φ : (Fin n → ℝ) → ℝ) (ω : Draws N n k)
    (hpos : 0 < bwNormSq W) :
    Succ (nrm W) (BstLean.Part106.tauPaper N n d) φ ω ↔
      Succ W (tauOf d 1) φ
        (scaleDraws (Real.sqrt (bwNormSq W) / Real.sqrt (Fintype.card (CoefIdx N n d) : ℝ)) ω) := by
  set ρ := Real.sqrt (bwNormSq W) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hinv : 0 < 1 / ρ := one_div_pos.2 hρ0
  have hg : BstLean.Part106.gVal (nrm W) (BstLean.Part106.tauPaper N n d) φ ω =
      BstLean.Part106.gVal W (tauOf d 1)
        φ (scaleDraws (ρ / Real.sqrt (Fintype.card (CoefIdx N n d) : ℝ)) ω) := by
    rw [← gVal_scale]
    have h := BstLean.Part106.gVal_smul hinv W (ρ * BstLean.Part106.tauPaper N n d) φ ω
    have e1 : 1 / ρ * (ρ * BstLean.Part106.tauPaper N n d) = BstLean.Part106.tauPaper N n d := by
      field_simp
    have e2 : ρ * BstLean.Part106.tauPaper N n d =
        tauOf d 1 * (ρ / Real.sqrt (Fintype.card (CoefIdx N n d) : ℝ)) := by
      unfold BstLean.Part106.tauPaper
      ring
    rw [e1] at h
    rw [← e2]
    exact h
  unfold Succ Err
  rw [hg]
  unfold nrm
  rw [Bu_smul hinv, Vu_smul hinv]

lemma measurable_scaleDraws_joint :
    Measurable (fun p : ℝ × Draws N n k => scaleDraws p.1 p.2) := by
  unfold scaleDraws
  refine measurable_pi_iff.2 fun i => ?_
  have hi : Measurable (fun p : ℝ × Draws N n k => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact hi.fst.prodMk (measurable_fst.smul hi.snd)

/-- **The total-variation step, integrated over a parameter.** -/
lemma tv_transfer (hTV : DrawsTV108) {Θ : Type*} [MeasurableSpace Θ] (Γ : Measure Θ)
    [IsProbabilityMeasure Γ] (hN : 1 ≤ N) (s : Θ → ℝ) (hs : Measurable s)
    (Bad : Set (Θ × Draws N n k)) (hBad : MeasurableSet Bad) (Gd : Set Θ) (hGd : MeasurableSet Gd)
    {η : ℝ} (hη : 0 ≤ η)
    (hgood : ∀ θ ∈ Gd, 0 < s θ ∧ s θ ^ 2 < 2 ∧
      Real.sqrt ((Real.sqrt (s θ ^ 2 * (2 - s θ ^ 2)))⁻¹ ^ (k * n) - 1) ≤ η) :
    (Γ.prod (drawM N n k)).real {p | p.1 ∈ Gd ∧ (p.1, scaleDraws (s p.1) p.2) ∈ Bad} ≤
      (Γ.prod (drawM N n k)).real Bad + η := by
  have := drawM_prob N n k hN
  set π := drawM N n k with hπ
  have hmap : Measurable (fun p : Θ × Draws N n k => (p.1, scaleDraws (s p.1) p.2)) :=
    measurable_fst.prodMk
      (measurable_scaleDraws_joint.comp ((hs.comp measurable_fst).prodMk measurable_snd))
  set R : Set (Θ × Draws N n k) := {p | p.1 ∈ Gd ∧ (p.1, scaleDraws (s p.1) p.2) ∈ Bad} with hRdef
  have hR : MeasurableSet R := (measurable_fst hGd).inter (hmap hBad)
  have key : (Γ.prod π) R ≤ (Γ.prod π) Bad + ENNReal.ofReal η := by
    rw [Measure.prod_apply hR, Measure.prod_apply hBad]
    calc ∫⁻ θ, π (Prod.mk θ ⁻¹' R) ∂Γ
        ≤ ∫⁻ θ, (π (Prod.mk θ ⁻¹' Bad) + ENNReal.ofReal η) ∂Γ := by
          refine lintegral_mono fun θ => ?_
          by_cases hθ : θ ∈ Gd
          · obtain ⟨h1, h2, h3⟩ := hgood θ hθ
            have hB : MeasurableSet (Prod.mk θ ⁻¹' Bad) := measurable_prodMk_left hBad
            have h := hTV N n k hN _ hB (s θ) h1 h2
            have e : Prod.mk θ ⁻¹' R = {ω | scaleDraws (s θ) ω ∈ Prod.mk θ ⁻¹' Bad} := by
              ext ω
              simp [hRdef, hθ]
            rw [e]
            have h' : π.real {ω | scaleDraws (s θ) ω ∈ Prod.mk θ ⁻¹' Bad} ≤
                π.real (Prod.mk θ ⁻¹' Bad) + η := h.trans (by linarith)
            rw [← ofReal_measureReal, ← ofReal_measureReal (s := Prod.mk θ ⁻¹' Bad),
              ← ENNReal.ofReal_add measureReal_nonneg hη]
            exact ENNReal.ofReal_le_ofReal h'
          · have e : Prod.mk θ ⁻¹' R = ∅ := by
              ext ω
              simp [hRdef, hθ]
            rw [e]
            simp
      _ = ∫⁻ θ, π (Prod.mk θ ⁻¹' Bad) ∂Γ + ENNReal.ofReal η := by
          rw [lintegral_add_right _ measurable_const]
          simp
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) key
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη]
    at h2
  exact h2

lemma measurable_nrm {k q d : ℕ} : Measurable (nrm (k := k) (q := q) (d := d)) := by
  unfold nrm
  exact (measurable_const.div c_measurable_bwNormSq.sqrt).smul measurable_id

end scale

section fixed

variable {n dA dF k : ℕ}

/-- The failure set at a given level is measurable. -/
lemma measurableSet_bad (hMG : MeasGen108) (hMPhi : MeasPhi108) (τ : ℝ) :
    MeasurableSet {p : Theta n dA dF × Draws (2 * n) n k | ¬ Succ p.1.1 τ
      (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} := by
  have hΦ : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) =>
      BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2) p.2) := by
    have hm : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) =>
        (((nrm p.1.2.1, nrm p.1.2.2), p.2) :
          ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ))) :=
      ((measurable_nrm.comp (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
        (measurable_nrm.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))).prodMk
        measurable_snd
    exact (hMPhi n dA dF).comp hm
  obtain ⟨hg, hB, hV⟩ := hMG (2 * n) n (2 * dA) k (Theta n dA dF) (fun t => t.1) (fun _ => τ)
    (fun t => BstLean.Part106.phiAF (nrm t.2.1) (nrm t.2.2)) measurable_fst measurable_const hΦ
  unfold Succ Err
  exact (measurableSet_le ((hg.sub (hB.comp measurable_fst)).abs)
    (((hV.comp measurable_fst).sqrt).const_mul _)).compl

/-- **The fixed noise level** (Gaussian coordinates): the failure probability of the program at
the level `tauPaper` for `W/‖W‖` is at most the failure probability at the ideal level, plus
`2/(ε²·D_W)`, plus the total-variation term `η`. -/
theorem gauss_fixed (hTV : DrawsTV108) (hMG : MeasGen108) (hMPhi : MeasPhi108) (hn : 1 ≤ n)
    {δ η ε2 : ℝ} (hη : 0 ≤ η) (hε0 : 0 < ε2) (hε1 : ε2 < 1)
    (hcore : ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | ¬ Succ p.1.1 (tauOf (2 * dA) 1)
          (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ≤ δ)
    (hηb : ∀ s : ℝ, 0 < s → (s ^ 2 - 1) ^ 2 < ε2 →
      s ^ 2 < 2 ∧ Real.sqrt ((Real.sqrt (s ^ 2 * (2 - s ^ 2)))⁻¹ ^ (k * n) - 1) ≤ η) :
    ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | ¬ Succ (nrm p.1.1) (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
          (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ≤
      δ + 2 / (ε2 * (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ)) + η := by
  have := drawM_prob (2 * n) n k (by omega)
  set μ := (GamG n dA dF).prod (drawM (2 * n) n k) with hμ
  set D : ℝ := (Fintype.card (CoefIdx (2 * n) n (2 * dA)) : ℝ) with hD
  have hDpos : 0 < D := by
    have : Nonempty (CoefIdx (2 * n) n (2 * dA)) := ⟨(⟨0, hn⟩, ⟨0, Sym.nil⟩)⟩
    exact Nat.cast_pos.2 Fintype.card_pos
  set e := Real.sqrt ε2 with he
  have he0 : 0 < e := Real.sqrt_pos.2 hε0
  have he2 : e ^ 2 = ε2 := Real.sq_sqrt hε0.le
  have he1 : e < 1 := by
    have : e ^ 2 < 1 ^ 2 := by rw [he2]; simpa using hε1
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) this
  set Gd : Set (Theta n dA dF) := {t | |bwNormSq t.1 - D| < e * D} with hGd
  have hGdm : MeasurableSet Gd :=
    measurableSet_lt (((c_measurable_bwNormSq.comp measurable_fst).sub measurable_const).abs)
      measurable_const
  set s : Theta n dA dF → ℝ := fun t => Real.sqrt (bwNormSq t.1) / Real.sqrt D with hs
  have hsm : Measurable s := ((c_measurable_bwNormSq.comp measurable_fst).sqrt).div_const _
  set Bad : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | ¬ Succ p.1.1 (tauOf (2 * dA) 1)
      (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} with hBad
  have hBadm : MeasurableSet Bad := measurableSet_bad hMG hMPhi _
  have hposG : ∀ t ∈ Gd, 0 < bwNormSq t.1 := by
    intro t ht
    have ht' : |bwNormSq t.1 - D| < e * D := ht
    have h1 := (abs_lt.1 ht').1
    nlinarith
  have hgood : ∀ t ∈ Gd, 0 < s t ∧ s t ^ 2 < 2 ∧
      Real.sqrt ((Real.sqrt (s t ^ 2 * (2 - s t ^ 2)))⁻¹ ^ (k * n) - 1) ≤ η := by
    intro t ht
    have hp := hposG t ht
    have hs0 : 0 < s t := div_pos (Real.sqrt_pos.2 hp) (Real.sqrt_pos.2 hDpos)
    have hs2 : s t ^ 2 = bwNormSq t.1 / D := by
      simp only [hs, div_pow, Real.sq_sqrt hp.le, Real.sq_sqrt hDpos.le]
    have habs : |s t ^ 2 - 1| < e := by
      rw [hs2, show bwNormSq t.1 / D - 1 = (bwNormSq t.1 - D) / D by field_simp, abs_div,
        abs_of_pos hDpos, div_lt_iff₀ hDpos]
      exact ht
    have hsq : (s t ^ 2 - 1) ^ 2 < ε2 := by
      rw [← he2, ← sq_abs (s t ^ 2 - 1)]
      exact pow_lt_pow_left₀ habs (abs_nonneg _) (by norm_num)
    obtain ⟨h1, h2⟩ := hηb (s t) hs0 hsq
    exact ⟨hs0, h1, h2⟩
  have hsub : {p : Theta n dA dF × Draws (2 * n) n k |
      ¬ Succ (nrm p.1.1) (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
        (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ⊆
      {p | p.1 ∈ Gdᶜ} ∪ {p | p.1 ∈ Gd ∧ (p.1, scaleDraws (s p.1) p.2) ∈ Bad} := by
    intro p hp
    by_cases hG : p.1 ∈ Gd
    · right
      refine ⟨hG, ?_⟩
      simp only [hBad, Set.mem_ofPred_eq]
      intro hsucc
      exact hp ((succ_nrm p.1.1 _ p.2 (hposG p.1 hG)).2 hsucc)
    · left
      exact hG
  have b1 : μ.real {p | p.1 ∈ Gdᶜ} ≤ 2 / (ε2 * D) := by
    have h := real_fst_le (GamG n dA dF) (drawM (2 * n) n k) Gdᶜ
    have h' := real_fst_le (bwGauss (2 * n) n (2 * dA) 1)
      ((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)) {W | ¬ |bwNormSq W - D| < e * D}
    refine h.trans (h'.trans ?_)
    have hS : MeasurableSet {W : CoefIdx (2 * n) n (2 * dA) → ℝ | ¬ |bwNormSq W - D| < e * D} :=
      (measurableSet_lt ((c_measurable_bwNormSq.sub measurable_const).abs) measurable_const).compl
    unfold bwGauss
    rw [map_measureReal_apply (measurable_bwGaussMap 1) hS]
    have hc := BstLean.Part106.chiSq_cheb (CoefIdx (2 * n) n (2 * dA)) (t := e * D)
      (by positivity)
    refine le_trans (measureReal_mono ?_) (hc.trans (le_of_eq ?_))
    · intro ξ hξ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_lt] at hξ ⊢
      have e' : bwNormSq (bwOfCoord ((1 : ℝ) • ξ)) = ∑ i, ξ i ^ 2 := by
        unfold bwNormSq
        rw [bwInner_ofCoord]
        simp [sq]
      rw [e'] at hξ
      exact hξ
    · rw [← hD, mul_pow, he2]
      field_simp
  have b2 := tv_transfer hTV (GamG n dA dF) (N := 2 * n) (n := n) (k := k) (by omega) s hsm Bad
    hBadm Gd hGdm hη hgood
  calc μ.real {p | ¬ Succ (nrm p.1.1) (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
          (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2}
      ≤ μ.real ({p | p.1 ∈ Gdᶜ} ∪ {p | p.1 ∈ Gd ∧ (p.1, scaleDraws (s p.1) p.2) ∈ Bad}) :=
        measureReal_mono hsub
    _ ≤ μ.real {p | p.1 ∈ Gdᶜ} +
          μ.real {p | p.1 ∈ Gd ∧ (p.1, scaleDraws (s p.1) p.2) ∈ Bad} := measureReal_union_le _ _
    _ ≤ 2 / (ε2 * D) + (δ + η) := add_le_add b1 (b2.trans (by linarith))
    _ = δ + 2 / (ε2 * D) + η := by ring

/-! ## The transfer to the sphere distributions -/

lemma bwSphere_eq_map_nrm (k q d : ℕ) : bwSphere k q d = (bwGauss k q d 1).map nrm := by
  unfold bwSphere bwGauss
  rw [Measure.map_map measurable_nrm (measurable_bwGaussMap 1)]
  congr 1
  funext ξ
  simp only [Function.comp, nrm, one_smul]
  have e : bwNormSq (bwOfCoord ξ) = ∑ i, ξ i ^ 2 := by
    unfold bwNormSq
    rw [bwInner_ofCoord]
    simp [sq]
  rw [e, BstLean.Part106.bwOfCoord_smul]

/-- The product of the three Bombieri–Weyl sphere distributions and the blocks. -/
noncomputable abbrev PS (n dA dF k : ℕ) : Measure (Theta n dA dF × Draws (2 * n) n k) :=
  ((bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF))).prod
    (drawM (2 * n) n k)

/-- `(W, (A₁, F)) ↦ (W/‖W‖, (A₁/‖A₁‖, F/‖F‖))`. -/
noncomputable def nrm3 (t : Theta n dA dF) : Theta n dA dF := (nrm t.1, (nrm t.2.1, nrm t.2.2))

lemma measurable_nrm3 : Measurable (nrm3 (n := n) (dA := dA) (dF := dF)) :=
  (measurable_nrm.comp measurable_fst).prodMk
    ((measurable_nrm.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_nrm.comp (measurable_snd.comp measurable_snd)))

lemma PS_eq_map (hn : 1 ≤ n) :
    PS n dA dF k = ((GamG n dA dF).prod (drawM (2 * n) n k)).map (Prod.map nrm3 id) := by
  have := drawM_prob (2 * n) n k (by omega)
  have h1 : ((bwGauss n n dA 1).prod (bwGauss n 1 dF 1)).map (Prod.map nrm nrm) =
      (bwSphere n n dA).prod (bwSphere n 1 dF) := by
    rw [← Measure.map_prod_map _ _ measurable_nrm measurable_nrm, ← bwSphere_eq_map_nrm,
      ← bwSphere_eq_map_nrm]
  have h2 : (GamG n dA dF).map (Prod.map nrm (Prod.map nrm nrm)) =
      (bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF)) := by
    rw [← Measure.map_prod_map _ _ measurable_nrm (measurable_nrm.prodMap measurable_nrm), h1,
      ← bwSphere_eq_map_nrm]
  have h3 : (GamG n dA dF).map nrm3 =
      (bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF)) := h2
  unfold PS
  rw [← h3, ← Measure.map_prod_map _ _ measurable_nrm3 measurable_id, Measure.map_id]

/-- **The transfer**: from a failure bound in the Gaussian coordinates to a success bound under
the three sphere distributions. -/
theorem sphere_succ (hn : 1 ≤ n) {δ : ℝ}
    (h : ((GamG n dA dF).prod (drawM (2 * n) n k)).real
        {p | ¬ Succ (nrm p.1.1) (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
          (BstLean.Part106.phiAF (nrm p.1.2.1) (nrm p.1.2.2)) p.2} ≤ δ) :
    1 - δ ≤ (PS n dA dF k).real
      {p | Succ p.1.1 (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
        (BstLean.Part106.phiAF p.1.2.1 p.1.2.2) p.2} := by
  have := drawM_prob (2 * n) n k (by omega)
  set μ := (GamG n dA dF).prod (drawM (2 * n) n k) with hμ
  set S : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | Succ p.1.1 (BstLean.Part106.tauPaper (2 * n) n (2 * dA))
      (BstLean.Part106.phiAF p.1.2.1 p.1.2.2) p.2} with hS
  have h1 := real_preimage_le (μ := μ)
    ((measurable_nrm3 (n := n) (dA := dA) (dF := dF)).prodMap
      (measurable_id : Measurable (id : Draws (2 * n) n k → Draws (2 * n) n k))) S
  rw [← PS_eq_map hn] at h1
  have h2 : (1 : ℝ) ≤ μ.real (Prod.map nrm3 id ⁻¹' S) + μ.real (Prod.map nrm3 id ⁻¹' S)ᶜ := by
    have := measureReal_union_le (μ := μ) (Prod.map nrm3 id ⁻¹' S) (Prod.map nrm3 id ⁻¹' S)ᶜ
    rw [Set.union_compl_self] at this
    simpa using this
  have h3 : μ.real (Prod.map nrm3 id ⁻¹' S)ᶜ ≤ δ := by
    refine le_trans (measureReal_mono ?_) h
    intro p hp
    exact hp
  linarith

end fixed

end BstLean.Part108
