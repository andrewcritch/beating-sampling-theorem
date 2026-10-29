import BstLean.Part86Defs
import BstLean.Part80Surr
import BstLean.Part80Cost
import BstLean.Part84Poly
import BstLean.Part56Key_Projection
import BstLean.Part56PropD_Polar

/-!
# Part 86, the instance `modRK`: regularity, the slice hypotheses, the surrogate hypothesis

* `regRK`: `Reg (modRK m d t v E) d`.
* `sliceOp_modRK`: `SliceOp` from `SliceOpRK` and `RotFacts`.
* `sliceRH_modRK`: `SliceRH` from `SliceRHRK`.
* `surrHyp_modRK`: `SurrHyp` at `η = 1/40` for the surrogate of order `KRK 1 (m+1) e80`.
-/

namespace BstLean.Part86.XInst

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (Mono varU)
open BstLean.Part53 (radF53)
open BstLean.Part56 (UnitV lawRK surrRK KRK tauR KR axialMeasure polarState polarPoint perpDir
  axialR axialS)
open BstLean.Part56.Orth (residualFeature)
open BstLean.Part78 (zv)
open BstLean.Part80 (e80 etaQ_e80)

/-! ## Regularity -/

lemma axial_sq_le (a r : ℝ) : axialS a r ^ 2 + axialR a r ^ 2 ≤ 1 := by
  unfold axialS axialR
  by_cases h : a ^ 2 + r ^ 2 = 0
  · simp [h]
  · have hp : 0 < a ^ 2 + r ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_pow, div_pow, Real.sq_sqrt hp.le, ← add_div, div_self h]

lemma comb_sq {n : ℕ} (S R : ℝ) (v w : Fin n → ℝ) :
    ∑ i, (S • v + R • w) i ^ 2 =
      S ^ 2 * ∑ i, v i ^ 2 + 2 * S * R * ∑ i, v i * w i + R ^ 2 * ∑ i, w i ^ 2 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma polarState_sq_le {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (pg : (ℝ × (Fin m → ℝ)) × (Fin (m + 1) → ℝ)) : ∑ i, polarState v pg i ^ 2 ≤ 1 := by
  have e : polarState v pg = axialS pg.1.1 (radF53 pg.1.2) • v +
      axialR pg.1.1 (radF53 pg.1.2) • perpDir v pg.2 := rfl
  rw [e, comb_sq, BstLean.Part56.perpDir_orth56 v pg.2 hv]
  have h1 : ∑ i, v i ^ 2 = 1 := hv
  have h2 := BstLean.Part56.perpDir_sq_le_one56 v pg.2
  have h3 := axial_sq_le pg.1.1 (radF53 pg.1.2)
  have h4 : axialR pg.1.1 (radF53 pg.1.2) ^ 2 * ∑ i, perpDir v pg.2 i ^ 2 ≤
      axialR pg.1.1 (radF53 pg.1.2) ^ 2 := mul_le_of_le_one_right (sq_nonneg _) h2
  rw [h1]; linarith

lemma monoP_deg {n d : ℕ} (p : Mono n d) : (monoP p).totalDegree ≤ d := by
  unfold monoP
  refine (totalDegree_multiset_prod _).trans ?_
  rw [Multiset.map_map]
  have h : Multiset.map (totalDegree ∘ (X : Fin n → MvPolynomial (Fin n) ℝ))
      (p.2 : Multiset (Fin n)) = Multiset.map (fun _ => 1) (p.2 : Multiset (Fin n)) := by
    apply Multiset.map_congr rfl
    intro a _
    simp
  rw [h]
  have := p.1.2
  simp
  omega

lemma psPE_deg {n d : ℕ} (E : JR n d → Mono n d → ℝ) (q : JR n d) :
    (psPE E q).totalDegree ≤ d := by
  unfold psPE
  refine BstLean.Part84.totalDegree_finset_sum_le fun p _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact monoP_deg p

lemma bPE_deg {n : ℕ} (d : ℕ) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    (bPE d v j).totalDegree ≤ d := by
  unfold bPE
  refine BstLean.Part84.totalDegree_finset_sum_le fun p _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact monoP_deg p

/-- **Regularity of the model of `D_{t,v}`.** -/
theorem regRK (m d : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) : Reg (modRK m d t v E) d := by
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BstLean.Part56.axialMeasure_probability b v hb0 t
  · show IsProbabilityMeasure (stdGauss (Fin (m + 1)))
    infer_instance
  · exact BstLean.Part56.measurable_polarState v
  · exact fun pg => polarState_sq_le v hv pg
  · exact fun j => bPE_deg d v j
  · exact fun q => psPE_deg E q

/-! ## The slice hypotheses -/

/-- **Slice feature operator bound for the model**, from `SliceOpRK` and the rotation facts. -/
theorem sliceOp_modRK (m d : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E) (hRF : RotFacts (m + 1) d)
    (CLam : ℝ) (hOp : SliceOpRK m d CLam) : SliceOp (modRK m d t v E) (CLam / m) := by
  obtain ⟨-, -, -, hK, hres, -⟩ := hRF v hv E hE
  intro p
  obtain ⟨hτ, hop⟩ := hOp v hv p.1 (radF53 p.2) (Real.sqrt_nonneg _)
  refine ⟨axialR p.1 (radF53 p.2) ^ 2, sq_nonneg _, ?_, ?_⟩
  · change ∀ᵐ g ∂stdGauss (Fin (m + 1)), _
    filter_upwards [hτ] with g hg
    have e : kapm (modRK m d t v E) (polarPoint v (perpDir v g) p.1 (radF53 p.2))
        (polarPoint v (perpDir v g) p.1 (radF53 p.2)) =
        tauR d v (polarPoint v (perpDir v g) p.1 (radF53 p.2)) := hK _ _
    change _ ≤ kapm (modRK m d t v E) (polarPoint v (perpDir v g) p.1 (radF53 p.2))
        (polarPoint v (perpDir v g) p.1 (radF53 p.2))
    rw [e]; exact hg
  · intro c
    obtain ⟨c', hc', hcx⟩ := hres c
    have h := hop c'
    rw [hc'] at h
    have e : ∀ g : Fin (m + 1) → ℝ,
        (∑ q, c q * (modRK m d t v E).ps ((modRK m d t v E).X (p, g)) q) =
          ∑ p', c' p' * residualFeature v (polarPoint v (perpDir v g) p.1 (radF53 p.2)) p' :=
      fun g => hcx _
    simp only [e]
    exact h

/-- **Slice reverse Hölder inequality for the model**, from `SliceRHRK`. -/
theorem sliceRH_modRK (m d : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (D : ℕ) (hRH : SliceRHRK m D) :
    SliceRH (modRK m d t v E) D (8 * 9 ^ D) := by
  intro p Q hQ
  exact hRH v hv p.1 (radF53 p.2) Q hQ

/-! ## Continuity of `Φ₁` -/

section cont

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

omit [Fintype I] in
/-- `Φ_lam` is continuous in `x` (it is a polynomial function of `x`). -/
theorem Phi_cont (M : Mod n I J S G) (P : MvPolynomial (I ⊕ Fin n) ℝ) (lam : ℝ) :
    Continuous (Phi M P lam) := by
  classical
  let L : (Fin n → ℝ) → I ⊕ Fin n → MvPolynomial (J × Fin n) ℝ := fun x =>
    Sum.elim (fun j => C (M.b x j)) (fun i => ∑ q, C (lam * M.ps x q) * X (q, i))
  have hb : ∀ j, Continuous fun x => M.b x j := fun j => by
    unfold Mod.b; exact MvPolynomial.continuous_eval _
  have hps : ∀ q, Continuous fun x => M.ps x q := fun q => by
    unfold Mod.ps; exact MvPolynomial.continuous_eval _
  have hLd : ∀ x s, (L x s).totalDegree ≤ 1 := by
    intro x s
    rcases s with j | i
    · simp only [L, Sum.elim_inl, totalDegree_C]; omega
    · simp only [L, Sum.elim_inr]
      refine BstLean.Part84.totalDegree_finset_sum_le fun q _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_X _).le
  have hLc : ∀ s m, Continuous fun x => (L x s).coeff m := by
    intro s m
    rcases s with j | i
    · simp only [L, Sum.elim_inl, coeff_C]
      split_ifs
      · exact hb j
      · exact continuous_const
    · simp only [L, Sum.elim_inr, coeff_sum, coeff_C_mul]
      exact continuous_finsetSum _ fun q _ => (continuous_const.mul (hps q)).mul continuous_const
  have hF : ∀ W x, Fm M P lam W x = eval W (aeval (L x) P) := by
    intro W x
    unfold Fm
    rw [BstLean.Part84.eval_aeval']
    have hs : (Sum.elim (M.b x) fun i => lam * zv W (M.ps x) i) =
        fun s => eval W (L x s) := by
      funext s
      rcases s with j | i
      · simp [L]
      · simp only [L, Sum.elim_inr, map_sum, map_mul, eval_C, eval_X, zv, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    rw [hs]
  have hfin : {m : (J × Fin n) →₀ ℕ | (m.sum fun _ e => e) ≤ P.totalDegree}.Finite := by
    have := Finsupp.finite_of_degree_le (σ := J × Fin n) P.totalDegree
    refine this.subset (fun m hm => ?_)
    simpa [Finsupp.degree_apply, Finsupp.sum] using hm
  have hcc := BstLean.Part84.cont_coeff L hLc P
  have hev : ∀ (W : J × Fin n → ℝ) x, eval W (aeval (L x) P) =
      ∑ m ∈ hfin.toFinset, (aeval (L x) P).coeff m * eval W (monomial m (1 : ℝ)) := by
    intro W x
    have h1 : eval W (aeval (L x) P) = ∑ m ∈ (aeval (L x) P).support,
        (aeval (L x) P).coeff m * eval W (monomial m (1 : ℝ)) := by
      conv_lhs => rw [(aeval (L x) P).as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [eval_monomial]
    rw [h1]
    refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
    · rw [Set.Finite.mem_toFinset]
      exact (le_totalDegree hm).trans (BstLean.Part84.deg_aeval _ (hLd x) P)
    · rw [notMem_support_iff.mp hm, zero_mul]
  have hΦ : Phi M P lam = fun x => ∑ m ∈ hfin.toFinset, (aeval (L x) P).coeff m *
      ∫ W, eval W (monomial m (1 : ℝ)) ∂stdGauss (J × Fin n) := by
    funext x
    unfold Phi
    simp only [hF, hev]
    rw [integral_finsetSum _ fun m _ =>
      (BstLean.Part48.gauss_poly_integrable (monomial m (1 : ℝ))).const_mul _]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  rw [hΦ]
  exact continuous_finsetSum _ fun m _ => (hcc m).mul continuous_const

end cont

/-! ## The law of total variance over the slices -/

lemma int_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ a, |f a| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hC a)

lemma sq_bdd (u c C : ℝ) (hu : |u| ≤ C) : |(u - c) ^ 2| ≤ (C + |c|) ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 := abs_le.mp hu
  have h2 := neg_abs_le c
  have h3 := le_abs_self c
  exact sq_le_sq' (by linarith) (by linarith)

lemma ball_bound {n : ℕ} (Φ : (Fin n → ℝ) → ℝ) (hΦ : Continuous Φ) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → |Φ x| ≤ C := by
  have hc : IsCompact (Set.Icc (fun _ => -1) (fun _ => 1) : Set (Fin n → ℝ)) := isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x ?_
  · rwa [Real.norm_eq_abs] at h
  · rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
    have hi : ∀ i, x i ^ 2 ≤ 1 := fun i =>
      (Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)).trans hx
    exact ⟨fun i => by nlinarith [hi i], fun i => by nlinarith [hi i]⟩

/-- Mean and variance of a continuous function under the image of a product measure, slice by
slice. -/
theorem total_var {n : ℕ} {S G : Type} [MeasurableSpace S] [MeasurableSpace G]
    (π : Measure S) (γ : Measure G) [IsProbabilityMeasure π] [IsProbabilityMeasure γ]
    (X : S × G → Fin n → ℝ) (hX : Measurable X) (hb : ∀ pg, ∑ i, X pg i ^ 2 ≤ 1)
    (Φ : (Fin n → ℝ) → ℝ) (hΦ : Continuous Φ) :
    ∫ x, Φ x ∂(π.prod γ).map X = ∫ p, ∫ g, Φ (X (p, g)) ∂γ ∂π ∧
    varU ((π.prod γ).map X) Φ =
      ∫ p, ∫ g, (Φ (X (p, g)) - ∫ g', Φ (X (p, g')) ∂γ) ^ 2 ∂γ ∂π +
      ∫ p, ((∫ g, Φ (X (p, g)) ∂γ) - ∫ p', ∫ g, Φ (X (p', g)) ∂γ ∂π) ^ 2 ∂π := by
  obtain ⟨C, hC0⟩ := ball_bound Φ hΦ
  have hC : ∀ pg, |Φ (X pg)| ≤ C := fun pg => hC0 _ (hb pg)
  have hm : Measurable fun pg => Φ (X pg) := hΦ.measurable.comp hX
  have hint : Integrable (fun pg => Φ (X pg)) (π.prod γ) := int_bdd _ _ hm C hC
  have first : ∫ x, Φ x ∂(π.prod γ).map X = ∫ p, ∫ g, Φ (X (p, g)) ∂γ ∂π := by
    rw [integral_map hX.aemeasurable hΦ.aestronglyMeasurable, integral_prod _ hint]
  refine ⟨first, ?_⟩
  set gD := ∫ p, ∫ g, Φ (X (p, g)) ∂γ ∂π with hgD
  -- the slice means
  have hgm : Measurable fun p => ∫ g, Φ (X (p, g)) ∂γ :=
    (hm.stronglyMeasurable.integral_prod_right').measurable
  have hpi : ∀ p, Integrable (fun g => Φ (X (p, g))) γ := fun p =>
    int_bdd _ _ (hm.comp measurable_prodMk_left) C fun g => hC (p, g)
  have hgC : ∀ p, |∫ g, Φ (X (p, g)) ∂γ| ≤ C := by
    intro p
    have h := norm_integral_le_of_norm_le_const (μ := γ) (f := fun g => Φ (X (p, g)))
      (ae_of_all _ fun g => by rw [Real.norm_eq_abs]; exact hC (p, g))
    rw [Real.norm_eq_abs] at h
    simpa using h
  have hsq : ∀ (p : S) (c : ℝ), Integrable (fun g => (Φ (X (p, g)) - c) ^ 2) γ := fun p c =>
    int_bdd _ _ (((hm.comp measurable_prodMk_left).sub measurable_const).pow_const 2)
      ((C + |c|) ^ 2) fun g => sq_bdd _ _ _ (hC (p, g))
  -- the slice identity
  have hslice : ∀ p, ∫ g, (Φ (X (p, g)) - gD) ^ 2 ∂γ =
      ∫ g, (Φ (X (p, g)) - ∫ g', Φ (X (p, g')) ∂γ) ^ 2 ∂γ +
        ((∫ g, Φ (X (p, g)) ∂γ) - gD) ^ 2 := by
    intro p
    set gp := ∫ g, Φ (X (p, g)) ∂γ with hgp
    have e : ∀ g, (Φ (X (p, g)) - gD) ^ 2 =
        (Φ (X (p, g)) - gp) ^ 2 + ((2 * (gp - gD)) * (Φ (X (p, g)) - gp) + (gp - gD) ^ 2) :=
      fun g => by ring
    have i1 : Integrable (fun g => (2 * (gp - gD)) * (Φ (X (p, g)) - gp)) γ :=
      ((hpi p).sub (integrable_const _)).const_mul _
    simp only [e]
    have i2 : Integrable (fun g => (2 * (gp - gD)) * (Φ (X (p, g)) - gp) + (gp - gD) ^ 2) γ :=
      i1.add (integrable_const _)
    rw [integral_add (hsq p gp) i2,
      integral_add i1 (integrable_const _), integral_const_mul,
      integral_sub (hpi p) (integrable_const _)]
    simp only [integral_const, smul_eq_mul]
    have h1 : γ.real Set.univ = 1 := by simp
    rw [h1, ← hgp]
    ring
  unfold varU
  rw [first]
  have hc2 : Continuous fun x => (Φ x - gD) ^ 2 := (hΦ.sub continuous_const).pow 2
  have hint2 : Integrable (fun pg : S × G => (Φ (X pg) - gD) ^ 2) (π.prod γ) :=
    int_bdd _ _ ((hm.sub measurable_const).pow_const 2) ((C + |gD|) ^ 2)
      fun pg => sq_bdd _ _ _ (hC pg)
  rw [integral_map hX.aemeasurable hc2.aestronglyMeasurable, integral_prod _ hint2]
  simp only [hslice]
  have hm3 : Measurable fun pg : S × G => (Φ (X pg) - ∫ g', Φ (X (pg.1, g')) ∂γ) ^ 2 :=
    (hm.sub (hgm.comp measurable_fst)).pow_const 2
  have hint3 : Integrable (fun pg : S × G => (Φ (X pg) - ∫ g', Φ (X (pg.1, g')) ∂γ) ^ 2)
      (π.prod γ) :=
    int_bdd _ _ hm3 ((C + |C|) ^ 2) fun pg => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h1 := abs_le.mp (hC pg)
      have h2 := abs_le.mp (hgC pg.1)
      have h3 := le_abs_self C
      exact sq_le_sq' (by linarith) (by linarith)
  have iA : Integrable (fun p => ∫ g, (Φ (X (p, g)) - ∫ g', Φ (X (p, g')) ∂γ) ^ 2 ∂γ) π :=
    hint3.integral_prod_left
  have iB : Integrable (fun p => ((∫ g, Φ (X (p, g)) ∂γ) - gD) ^ 2) π :=
    int_bdd _ _ ((hgm.sub measurable_const).pow_const 2) ((C + |gD|) ^ 2)
      fun p => sq_bdd _ _ _ (hgC p)
  rw [integral_add iA iB]

/-! ## The surrogate hypothesis -/

/-- **The surrogate hypothesis for the model of `D_{t,v}`**, at `η = 1/40`, for the surrogate of
order `KRK 1 (m+1) e80`, `t ∈ [0, m+1]`. -/
theorem surrHyp_modRK (m d : ℕ) (hm : 1 ≤ m) (t : ℝ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (ht0 : 0 ≤ t) (htn : t ≤ ((m + 1 : ℕ) : ℝ)) :
    SurrHyp (modRK m d t v E) (1 / 40) (gqRK m d (KRK 1 (m + 1) e80) t v E) := by
  intro P
  have hΦ : Continuous (Phi (modRK m d t v E) P 1) := Phi_cont _ P 1
  obtain ⟨-, -, hs⟩ := BstLean.Part80.surrRK80 (m + 1) (by omega) e80
    (by unfold e80; norm_num) v hv t ht0 htn
  have h := hs _ hΦ
  rw [etaQ_e80] at h
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  have : IsProbabilityMeasure (axialMeasure t v) :=
    BstLean.Part56.axialMeasure_probability b v hb0 t
  have key := total_var (axialMeasure t v) (stdGauss (Fin (m + 1))) (polarState v)
    (BstLean.Part56.measurable_polarState v) (fun pg => polarState_sq_le v hv pg)
    (Phi (modRK m d t v E) P 1) hΦ
  rw [← BstLean.Part56.lawRK_eq_polar_map b v hb0 t] at key
  rw [key.1, key.2] at h
  exact h

end BstLean.Part86.XInst

#print axioms BstLean.Part86.XInst.regRK
#print axioms BstLean.Part86.XInst.sliceOp_modRK
#print axioms BstLean.Part86.XInst.sliceRH_modRK
#print axioms BstLean.Part86.XInst.surrHyp_modRK
