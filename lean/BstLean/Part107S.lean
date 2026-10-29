import BstLean.Part107Sd

/-!
# Part 107 S: Lemma S and Corollary S (`CorS107`)
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

theorem corS107 (hW : Wick107) (hQ : QDom107) (hO : OnePoint107) : CorS107 := by
  intro N n dW dA σ v J c hN hn hσ hvK hv hJ
  have := BstLean.Part29.uniformSphere_isProbability N hN
  obtain ⟨Q, hQm, hQ0, hQ4, hQb⟩ := hQ n dA
  let vW : (CoefIdx N n dW → ℝ) → ℝ := fun W =>
    ∫ p, kW dA W p.1 p.2 ∂((uniformSphere N).prod (uniformSphere N))
  let DW : (CoefIdx N n dW → ℝ) → ℝ := fun W =>
    ∫ p, (kW dA W p.1 p.2 - c) ^ 2 ∂((uniformSphere N).prod (uniformSphere N))
  have hkm : Measurable (fun a : (CoefIdx N n dW → ℝ) × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      kW dA a.1 a.2.1 a.2.2) :=
    measurable_kW dA measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd)
  have hvm : Measurable vW := hkm.stronglyMeasurable.integral_prod_right'.measurable
  have hDm : Measurable DW :=
    ((hkm.sub measurable_const).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hvC : ∀ W, |vW W| ≤ (dA : ℝ) + 1 := fun W => abs_int_le _ fun p => abs_kW_le dA W _ _
  have hDb : ∀ (W : CoefIdx N n dW → ℝ) (p : (Fin N → ℝ) × (Fin N → ℝ)),
      |(kW dA W p.1 p.2 - c) ^ 2| ≤ ((dA : ℝ) + 1 + |c|) ^ 2 := fun W p => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_sub _ _).trans (add_le_add_left (abs_kW_le dA W _ _) _)) 2
  have hDC : ∀ W, |DW W| ≤ ((dA : ℝ) + 1 + |c|) ^ 2 := fun W => abs_int_le _ (hDb W)
  have iκ : ∀ W : CoefIdx N n dW → ℝ, Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => kW dA W p.1 p.2)
      ((uniformSphere N).prod (uniformSphere N)) := fun W =>
    bm_int (measurable_kW dA measurable_const measurable_fst measurable_snd) _
      fun p => abs_kW_le dA W _ _
  have iD : ∀ W : CoefIdx N n dW → ℝ, Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (kW dA W p.1 p.2 - c) ^ 2)
      ((uniformSphere N).prod (uniformSphere N)) := fun W =>
    bm_int (((measurable_kW dA measurable_const measurable_fst measurable_snd).sub
      measurable_const).pow_const 2) _ (hDb W)
  have htv : twoPt N n dW σ (kap dA) = ∫ W, vW W ∂bwGauss N n dW σ := by
    unfold twoPt
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    exact (integral_prod (fun p : (Fin N → ℝ) × (Fin N → ℝ) => kW dA W p.1 p.2) (iκ W)).symm
  have htD : twoPt N n dW σ (fun a => (kap dA a - c) ^ 2) = ∫ W, DW W ∂bwGauss N n dW σ := by
    unfold twoPt
    refine integral_congr_ae (ae_of_all _ fun W => ?_)
    exact (integral_prod (fun p : (Fin N → ℝ) × (Fin N → ℝ) => (kW dA W p.1 p.2 - c) ^ 2)
      (iD W)).symm
  -- `W(u) ≠ 0` for almost every `W`, for almost every `u`
  have hae : ∀ᵐ W ∂bwGauss N n dW σ, ∀ᵐ u ∂uniformSphere N, bwEval W u ≠ 0 := by
    have hset : MeasurableSet
        {p : (Fin N → ℝ) × (CoefIdx N n dW → ℝ) | bwEval p.2 p.1 ≠ 0} :=
      (measurable_bwEval_comp measurable_snd measurable_fst (measurableSet_singleton 0)).compl
    have h1 : ∀ᵐ u ∂uniformSphere N, ∀ᵐ W ∂bwGauss N n dW σ, bwEval W u ≠ 0 :=
      (BstLean.Part29.uniformSphere_ae_sphere N).mono fun u hu =>
        hO N n dW σ u hn hσ (by simp only [dot, ← sq]; exact hu)
    exact (Measure.ae_ae_comm hset).1 h1
  have hXe : ∀ (W : CoefIdx N n dW → ℝ) (θ : (CoefIdx n n dA → ℝ) × (Fin n → ℝ)),
      X1 W θ.1 θ.2 = ∫ u, qLin θ.1 θ.2 (xi W u) ^ 2 ∂uniformSphere N -
        (∫ u, qLin θ.1 θ.2 (xi W u) ∂uniformSphere N) ^ 2 :=
    fun W θ => sd_X1_eq hN W θ.1 θ.2 (Q θ) (hQb θ)
  have hfix : ∀ᵐ W ∂bwGauss N n dW σ,
      ∫ θ, X1 W θ.1 θ.2 ∂AL n dA = (n : ℝ) * ((dA : ℝ) + 1 - vW W) ∧
      ∫ θ, X1 W θ.1 θ.2 ^ 2 ∂AL n dA ≤
        (n : ℝ) * ((n : ℝ) + 2) * (((dA : ℝ) + 1 - vW W) ^ 2 + 2 * DW W) ∧
      (vW W - c) ^ 2 ≤ DW W := by
    filter_upwards [hae] with W hWu
    have H := setup_inst hW Q hQm hQ0 hQ4 hQb (N := N) (dW := dW) W
    have hK : ∀ᵐ u ∂uniformSphere N, kW dA W u u = (dA : ℝ) + 1 := hWu.mono fun u hu => by
      unfold kW xi
      rw [dot_sphProj_self_eq _ hu, kap_one]
    have F := H.fixedW (ν := uniformSphere N) (by positivity) hK c
    simp_rw [hXe W]
    exact F
  have hgm : Measurable (fun a : ((CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ))) ×
      (Fin N → ℝ) => qLin a.1.2.1 a.1.2.2 (xi a.1.1 a.2)) :=
    sd_measurable_qLin (measurable_fst.comp (measurable_snd.comp measurable_fst))
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
      (measurable_xi (measurable_fst.comp measurable_fst) measurable_snd)
  have hXm : Measurable (fun z : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)) =>
      X1 z.1 z.2.1 z.2.2) := by
    simp_rw [hXe]
    exact (hgm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sub
      (hgm.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)
  have hXQ : ∀ z : (CoefIdx N n dW → ℝ) × ((CoefIdx n n dA → ℝ) × (Fin n → ℝ)),
      X1 z.1 z.2.1 z.2.2 ≤ Q z.2 ^ 2 := by
    intro z
    rw [hXe z.1 z.2]
    have h1 : |∫ u, qLin z.2.1 z.2.2 (xi z.1 u) ^ 2 ∂uniformSphere N| ≤ Q z.2 ^ 2 :=
      abs_int_le _ fun u => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hQb z.2 _ fun i => sphProj_coord _ i) 2
    have h2 := (abs_le.1 h1).2
    nlinarith [sq_nonneg (∫ u, qLin z.2.1 z.2.2 (xi z.1 u) ∂uniformSphere N)]
  have hsqb : ∀ x : ℝ, |x| ≤ (dA : ℝ) + 1 → |x ^ 2| ≤ ((dA : ℝ) + 1) ^ 2 := fun x hx => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  rw [htv] at hv
  rw [htD] at hJ
  exact overW (P := bwGauss N n dW σ) (γ := AL n dA)
    (fun z => X1 z.1 z.2.1 z.2.2) Q vW DW (n : ℝ) ((dA : ℝ) + 1) v J c hXm hQ4
    (fun z => variance_nonneg _ _) hXQ (by exact_mod_cast hn)
    (bm_int hvm _ hvC) (bm_int (hvm.pow_const 2) _ fun W => hsqb _ (hvC W)) (bm_int hDm _ hDC)
    (hfix.mono fun W h => h.1) (hfix.mono fun W h => h.2.1) (hfix.mono fun W h => h.2.2)
    hvK hv hJ

end BstLean.Part107

#print axioms BstLean.Part107.corS107
