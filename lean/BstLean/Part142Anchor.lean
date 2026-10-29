import BstLean.Part139All

/-!
# Part 142, item 2, first step (`kernel142a`): the chord of `κ^{∘4}` at the centre

Role: `delegations/statements/p142-spec.md`, item 2 (route (a)). In Part 133 the links of the
World network and of the inputs go through the 1-Lipschitz function `κ^{∘4}`. Here the centre
`q = κ(κ(0))` is FIXED, and `κ^{∘4}` is convex and nondecreasing on `[−1, 1]`, so
`|κ^{∘4}(t) − κ^{∘4}(q)| ≤ σ₄·|t − q|` with the chord slope
`σ₄ = (1 − κ^{∘6}(0))/(1 − κ(κ(0))) ≤ 0.4404`. No localization window is necessary.

* `sig4`, `sig4_le`, `iter4_chord`.
* `tX_L2`: `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ w + u` from the links of Part 133; `tX_L2_focus`.
* **`kernSame142`** (`kernel142a`): at the widths of the Focus, `n ≥ 4096`:
  `‖k − S·κ^{∘6}(0)‖₂ ≤ S·eP142 n`, `eP142 n = eAFr + σ₄·(eWr + sU) ≤ 3.214/√n`
  (Part 139: `4.074/√n`).
* `vSpread142a n = (e_V + eP142)² + 2·eP142² ≤ 42.7/n` (Part 139: `64/n`);
  `spreadLow142a`: `Pr(sd² < θ·S·(1 − Q)) ≤ vSpread142a n/((1 − θ)(1 − Q))²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139

/-- The chord slope of `κ^{∘4}` between `q = κ(κ(0))` and `1`. -/
noncomputable def sig4 : ℝ := (1 - kappa^[6] 0) / (1 - kappa (kappa 0))

lemma sig4_nonneg : 0 ≤ sig4 := by
  have h1 : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h2 := kappa2_zero_le
  unfold sig4
  exact div_nonneg (by linarith) (by linarith)

lemma sig4_le : sig4 ≤ 4404 / 10000 := by
  have h1 : 7771 / 10000 ≤ kappa^[6] 0 := kappa6_zero_ge'
  have h2 := kappa2_zero_le
  unfold sig4
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The chord bound of `κ^{∘4}` at the fixed centre `q = κ(κ(0))`**: for `t ∈ [−1, 1]`,
`|κ^{∘4}(t) − κ^{∘6}(0)| ≤ σ₄·|t − q|`. -/
lemma iter4_chord {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    |kappa^[4] t - kappa^[6] 0| ≤ sig4 * |t - kappa (kappa 0)| := by
  have hG : KGood (kappa^[4]) := kGood_iterate 3
  set q := kappa (kappa 0) with hq
  have hq0 : 0 < q := kappa2_zero_pos
  have hq1 : q < 1 := by have := kappa2_zero_le; linarith
  have hqm : q ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hq1.le⟩
  have h1m : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have e6 : kappa^[6] 0 = kappa^[4] q := rfl
  rw [e6]
  have hd : 0 < 1 - q := by linarith
  have hsig : sig4 * (1 - q) = 1 - kappa^[4] q := by
    change (1 - kappa^[6] 0) / (1 - q) * (1 - q) = 1 - kappa^[4] q
    rw [e6, div_mul_cancel₀ _ hd.ne']
  rcases le_total q t with h | h
  · -- `q ≤ t ≤ 1`: below the chord
    have hmono := hG.mono hqm ht h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    have hc := hG.conv.2 hqm h1m (show (0 : ℝ) ≤ (1 - t) / (1 - q) from
      div_nonneg (by linarith [ht.2]) hd.le) (show (0 : ℝ) ≤ (t - q) / (1 - q) from
      div_nonneg (by linarith) hd.le) (by field_simp; ring)
    have e : ((1 - t) / (1 - q)) • q + ((t - q) / (1 - q)) • (1 : ℝ) = t := by
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [e, hG.one] at hc
    simp only [smul_eq_mul] at hc
    have h2 := mul_le_mul_of_nonneg_right hc hd.le
    have e2 : ((1 - t) / (1 - q) * kappa^[4] q + (t - q) / (1 - q) * 1) * (1 - q) =
        (1 - t) * kappa^[4] q + (t - q) := by
      field_simp
    rw [e2] at h2
    nlinarith
  · -- `−1 ≤ t ≤ q`: the slope on `[t, q]` is at most the slope on `[q, 1]`
    have hmono := hG.mono ht hqm h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have hdt : 0 < 1 - t := by linarith
    have hc := hG.conv.2 ht h1m (show (0 : ℝ) ≤ (1 - q) / (1 - t) from
      div_nonneg hd.le hdt.le) (show (0 : ℝ) ≤ (q - t) / (1 - t) from
      div_nonneg (by linarith) hdt.le) (by field_simp; ring)
    have e : ((1 - q) / (1 - t)) • t + ((q - t) / (1 - t)) • (1 : ℝ) = q := by
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [e, hG.one] at hc
    simp only [smul_eq_mul] at hc
    have h2 := mul_le_mul_of_nonneg_right hc hdt.le
    have e2 : ((1 - q) / (1 - t) * kappa^[4] t + (q - t) / (1 - t) * 1) * (1 - t) =
        (1 - q) * kappa^[4] t + (q - t) := by
      field_simp
    rw [e2] at h2
    nlinarith

section General

variable {N mW n mA mF : ℕ}

section Kernels

variable {a w u : ℝ} {gW : ℝ → ℝ}

/-- **The cosine of the two inputs of `A` around its centre**:
`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ w + u`, from the World link and the link of the inputs. -/
theorem tX_L2 (hN : 1 ≤ N) (hw : 0 ≤ w) (hu : 0 ≤ u)
    (hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        (gW (dotp v v')))
    (hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => gW (dotp uu.1 uu.2)) w)
    (hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) u) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa 0)) (w + u) := by
  have := lawU2_prob hN
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have mt : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1)) :=
    measurable_tX.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have md : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      dotp ω.1.1 ω.1.2) :=
    measurable_dotp_comp (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
  have m2 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa (dotp ω.1.1 ω.1.2))) :=
    mt.sub (hkk.comp md)
  have A2 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa (dotp ω.1.1 ω.1.2))) w := by
    refine L2le.prod' m2.aestronglyMeasurable hgW ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h0 := (hW uu.1 uu.2 huu.1 huu.2).comp_fst
      (ν := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    unfold lawR
    exact h0
  have A3 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kappa (kappa (dotp ω.1.1 ω.1.2)) - kappa (kappa 0)) u := hU.comp_fst
  refine ((A2.add0 A3 hw hu).congr_fun fun ω => ?_)
  ring

/-- **The same-`A` kernel with the chord of `κ^{∘4}`**:
`‖k_{A,A}(x(u), x(u′)) − (4/n)·κ^{∘6}(0)‖₂ ≤ (4/n)·(a + σ₄·τ)`, from the bound `a` of the links
of `A` and `F` and a bound `τ` of `‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂`. -/
theorem kernSame142_of {τ : ℝ} (hn : 1 ≤ n) (hN : 1 ≤ N) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x')) (4 / (n : ℝ) * a))
    (hT : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa 0)) τ) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[6] 0)
      (4 / (n : ℝ) * (a + sig4 * τ)) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs4 := sig4_nonneg
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have mt : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1)) :=
    measurable_tX.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have m1 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kgen false false false ω - 4 / (n : ℝ) * kappa^[4] (tX (ω.1, ω.2.1))) :=
    (measurable_kgen false false false).sub ((hk4.comp mt).const_mul _)
  have A1 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[4] (tX (ω.1, ω.2.1)))
      (4 / (n : ℝ) * a) := by
    refine L2le.prod_const m1.aestronglyMeasurable (Filter.Eventually.of_forall fun uu => ?_)
    have m1' := m1.comp (measurable_prodMk_left (x := uu))
    unfold lawR
    refine L2le.prod_const m1'.aestronglyMeasurable (Filter.Eventually.of_forall fun W => ?_)
    exact hS (xW W uu.1) (xW W uu.2) (normSq_xW hn W uu.1) (normSq_xW hn W uu.2)
  have m2 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      4 / (n : ℝ) * (kappa^[4] (tX (ω.1, ω.2.1)) - kappa^[6] 0)) :=
    ((hk4.comp mt).sub measurable_const).const_mul _
  have A2 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        4 / (n : ℝ) * (kappa^[4] (tX (ω.1, ω.2.1)) - kappa^[6] 0))
      (4 / (n : ℝ) * (sig4 * τ)) := by
    have h0 := (hT.const_mul_nonneg hs4).const_mul_nonneg (c := 4 / (n : ℝ)) (by positivity)
    refine L2le.of_abs_le m2.aestronglyMeasurable h0 (fun ω => ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hs4]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact iter4_chord (tX_mem hn (ω.1, ω.2.1))
  have h12 := A1.add0 A2 (by positivity) (by positivity)
  refine (h12.congr_fun fun ω => ?_).congr_bound (by ring)
  ring

end Kernels

/-! ## The widths of the Focus -/

/-- **`‖⟨x(u), x(u′)⟩ − κ(κ(0))‖₂ ≤ eWr + sU`** at the widths of the Focus (general `mA`, `mF`).
-/
theorem tX_L2_focus (hn : 1 ≤ n) (hN : 1 ≤ N) (hmW : 1 ≤ mW) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1) - kappa (kappa 0))
      (eWr N n mW + sU N) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmW' : (0 : ℝ) < mW := by exact_mod_cast hmW
  have hq := q_mem
  have hsU := sU_nonneg N
  have hsm := eWsmall_nonneg n mW
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have := lawU2_prob hN
  have hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        ((fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp v v')) := by
    intro v v' hv hv'
    have hJ : 0 ≤ jCos n := by unfold jCos; positivity
    have h := world_cos_L2g hN hmW hn hJ (fun h h' hh hh' =>
      lin_cos_L2b (v := 2 / (mW : ℝ)) (by positivity) hn h h' hh hh') hv hv'
    refine h.congr_bound ?_
    unfold eWsmall
    ring
  have hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      (fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW) (dotp uu.1 uu.2))
      (eWr N n mW) := by
    have h1 := sphere_gW_L2 hN (1 / √(n : ℝ)) (by positivity)
    have h2 : L2le (lawU2 N) (fun _ : (Fin N → ℝ) × (Fin N → ℝ) => eWsmall n mW)
        (eWsmall n mW) := ⟨aestronglyMeasurable_const, integrable_const _, by simp⟩
    have h3 := h1.add0 h2 (by unfold sU at hsU; positivity) hsm
    exact h3
  have hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) (sU N) := sphere_kk_L2r hN
  have hW0 : 0 ≤ eWr N n mW := by unfold eWr; positivity
  exact tX_L2 (gW := fun t : ℝ => 1 / √(n : ℝ) * (1 - kappa (kappa t) ^ 2) + eWsmall n mW)
    hN hW0 hsU hW hgW hU

end General

/-- The constant `e_P` with the chord of `κ^{∘4}`: `‖k − S·Q‖₂ ≤ S·eP142 n`. -/
noncomputable def eP142 (n : ℕ) : ℝ :=
  eAFr n (mA n) (mF n) + sig4 * (eWr (2 * n) n (mW n) + sU (2 * n))

/-- **`kernSame142` (`kernel142a`).** For `n ≥ 4096`, at the widths of the Focus:
`‖k_{A,A}(x(u), x(u′)) − (4/n)·κ^{∘6}(0)‖₂ ≤ (4/n)·eP142 n`. -/
theorem kernSame142 {n : ℕ} (hn : 4096 ≤ n) :
    L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[6] 0)
      (4 / (n : ℝ) * eP142 n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hG0 : 3 / 10 ≤ (kappa ∘ kappa) 0 := by
    have := kappa2_zero_ge
    simp only [Function.comp_apply]
    linarith
  have hcF := cF2o_pos hmF
  have hcA := cAr_pos hG hmA hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hA0 : 0 ≤ eAFr n (mA n) (mF n) := by unfold eAFr; positivity
  have hsU := sU_nonneg (2 * n)
  have hq := q_mem
  have hsm := eWsmall_nonneg n (mW n)
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hW0 : 0 ≤ eWr (2 * n) n (mW n) := by unfold eWr; positivity
  have hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n (mA n) n).prod ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
        (fun p : MlpParam n (mA n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
          kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x'))
        (4 / (n : ℝ) * eAFr n (mA n) (mF n)) := fun x x' hx hx' =>
    kern_same_L2_of hn1 hmA hx hx' hcF hcA (fun y y' => KF_L2o hn1 hmF y y')
      (mlp_psi_L2r hG hG0 hmA hn1 hn1 x x')
  exact kernSame142_of hn1 hN hA0 (by positivity) hS (tX_L2_focus hn1 hN hmW)

/-- `eP142 n ≤ 3.214/√n` for `n ≥ 4096` (Part 139: `e_P ≤ 4.074/√n`). -/
lemma eP142_scale {n : ℕ} (hn : 4096 ≤ n) : eP142 n ≤ 3214 / 1000 / √(n : ℝ) := by
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_scale hn
  have h2 := eWr_scale hn
  have h3 := sU_scale hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 : 0 ≤ eWr (2 * n) n (mW n) := by
    have hq := q_mem
    have hsm := eWsmall_nonneg n (mW n)
    have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
    have hn' : (0 : ℝ) < n := by have := nR_ge hn; linarith
    unfold eWr; positivity
  unfold eP142
  have e : (3214 : ℝ) / 1000 / √(n : ℝ) = 3214 / 1000 * (1 / √(n : ℝ)) := by ring
  have e1 : (25365 : ℝ) / 10000 / √(n : ℝ) = 25365 / 10000 * (1 / √(n : ℝ)) := by ring
  have e2 : (11746 : ℝ) / 10000 / √(n : ℝ) = 11746 / 10000 * (1 / √(n : ℝ)) := by ring
  have e3 : (3629 : ℝ) / 10000 / √(n : ℝ) = 3629 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e]
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have ht : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (15375 / 10000 * (1 / √(n : ℝ))) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  nlinarith

lemma eP142_nonneg {n : ℕ} (hn : 4096 ≤ n) : 0 ≤ eP142 n := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  obtain ⟨-, -, -, -⟩ := vTot_nonneg (2 * n) (mW n) n (mA n) (mF n) hmF hmA hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hcF := cF2o_pos hmF
  have hcA := cAr_pos (kGood_kappa.comp_kappa) hmA hn1
  have hA0 : 0 ≤ eAFr n (mA n) (mF n) := by unfold eAFr; positivity
  have hsU := sU_nonneg (2 * n)
  have hq := q_mem
  have hsm := eWsmall_nonneg n (mW n)
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hW0 : 0 ≤ eWr (2 * n) n (mW n) := by unfold eWr; positivity
  have h40 := sig4_nonneg
  unfold eP142
  positivity

/-- `v_n` with the chord of `κ^{∘4}`: `(e_V + eP142)² + 2·eP142²`. -/
noncomputable def vSpread142a (n : ℕ) : ℝ :=
  (eV n (mA n) (mF n) + eP142 n) ^ 2 + 2 * eP142 n ^ 2

/-- `vSpread142a n ≤ 42.7/n` for `n ≥ 4096` (Part 139: `v_n ≤ 64/n`). -/
lemma vSpread142a_scale {n : ℕ} (hn : 4096 ≤ n) : vSpread142a n ≤ 427 / 10 / (n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have hP := eP142_scale hn
  have hV := eV_scale hn
  have hP0 := eP142_nonneg hn
  have hV0 : 0 ≤ eV n (mA n) (mF n) := Real.sqrt_nonneg _
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have et : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have eP : (3214 : ℝ) / 1000 / √(n : ℝ) = 3214 / 1000 * t := by rw [ht]; ring
  have eVV : (147 : ℝ) / 100 / √(n : ℝ) = 147 / 100 * t := by rw [ht]; ring
  rw [eP] at hP
  rw [eVV] at hV
  have e : (427 : ℝ) / 10 / (n : ℝ) = 427 / 10 * t ^ 2 := by rw [et]; ring
  rw [e]
  unfold vSpread142a
  have h1 : (eV n (mA n) (mF n) + eP142 n) ^ 2 ≤ ((147 / 100 + 3214 / 1000) * t) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : eP142 n ^ 2 ≤ (3214 / 1000 * t) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  nlinarith [sq_nonneg t]

/-- **The spread with the chord of `κ^{∘4}`.** For `n ≥ 4096` and `θ < 1`:
`Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ vSpread142a n/((1 − θ)(1 − Q))²`. -/
theorem spreadLow142a {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      vSpread142a n / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hmW : 1 ≤ mW n := by have := mW_ge hn; omega
  have hd : dChi n ≤ 1 := (dChi_bound hn).trans (by norm_num)
  obtain ⟨-, -, hDiag⟩ := kernels_general (N := 2 * n) hn1 hN hmW hmA hmF hd
  have hSame := kernSame142 hn
  have hP0 := eP142_nonneg hn
  have hV0 : 0 ≤ eV n (mA n) (mF n) := Real.sqrt_nonneg _
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hS : (0 : ℝ) < 4 / (n : ℝ) := by positivity
  have hy : 0 < 4 / (n : ℝ) - 4 / (n : ℝ) * kappa^[6] 0 := by nlinarith
  have h := spreadLow_general hn1 hN hmF (mul_nonneg hS.le hP0) (mul_nonneg hS.le hV0)
    hSame hDiag hy hθ
  have e1 : 4 / (n : ℝ) - 4 / (n : ℝ) * kappa^[6] 0 = 4 / (n : ℝ) * (1 - kappa^[6] 0) := by ring
  rw [e1] at h
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0]
  refine h.trans (le_of_eq ?_)
  have h1Q : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  unfold vSpread142a
  field_simp

end BstLean.Part142

open BstLean.Part142 in
#print axioms iter4_chord
open BstLean.Part142 in
#print axioms tX_L2_focus
open BstLean.Part142 in
#print axioms kernSame142
open BstLean.Part142 in
#print axioms eP142_scale
open BstLean.Part142 in
#print axioms vSpread142a_scale
open BstLean.Part142 in
#print axioms spreadLow142a
