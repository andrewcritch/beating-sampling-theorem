import BstLean.Part133Agent

/-!
# Part 133: the variance of `J` from the `L²` bounds of the links

Role: `delegations/statements/p133-spec.md`, items 1, 2 and 4 (general form). Paper source:
`onW4c-cx.md` §4 ("Conditional expectation reduction", "Totals").

* `kernSame_L2`, `kernCross_L2`, `kernDiag_L2`: the `L²` distance of the three two-input kernels
  from constants, under `(u, u′) ⊗ (W, A, A′, F)`.
* `section_L2` (item 2): `‖P − c‖₂ ≤ ‖k − c‖₂` for `P = E_{u,u′} k` (a conditional expectation of
  the two-input kernel); with `c` the mean this is `Var(P) ≤ Var(k)`.
* `J_L2` (item 1): the decomposition of `J − c_J` and the `L²` triangle inequality:
  `‖J − c_J‖₂ ≤ (4/n)·(3·e_P + 2·e_× + e_V)`.
* **`varJ_of_bounds`**: `Var J ≤ ((4/n)·(3(a + w + u) + 2b + eV))²` from bounds `a` (links `F`, `A`
  of the same-`A` kernel), `b` (cross kernel), `w` (the World), `u` (the inputs).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

variable {N mW n mA mF : ℕ}

lemma iter4_lip {s t : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    |kappa^[4] s - kappa^[4] t| ≤ |s - t| := by
  have hG : KGood (kappa^[4]) := kGood_iterate 3
  rcases le_total t s with h | h
  · have h1 := hG.lip ht.1 h hs.2
    have h2 := hG.mono ht hs h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact h1
  · have h1 := hG.lip hs.1 h ht.2
    have h2 := hG.mono hs ht h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

lemma kk_memIcc {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : kappa (kappa t) ∈ Icc (-1 : ℝ) 1 :=
  kappa_mem_Icc (kappa_mem_Icc ht)

lemma dotp_unit_mem {ι : Type*} [Fintype ι] {u u' : ι → ℝ} (hu : normSq u = 1)
    (hu' : normSq u' = 1) : dotp u u' ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_dotp_le_nrm u u'
  rw [nrm_of_normSq_one hu, nrm_of_normSq_one hu', mul_one] at h
  exact abs_le.mp h

/-! ## The three kernels under `(u, u′) ⊗ (W, A, A′, F)` -/

section Kernels

variable {a b w u : ℝ} {gW : ℝ → ℝ}

/-- **The same-`A` kernel**: `‖k_{A,A}(x(u), x(u′)) − (4/n)·κ^{∘6}(0)‖₂ ≤ (4/n)·(a + w + u)`. -/
theorem kernSame_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (ha : 0 ≤ a) (hw : 0 ≤ w) (hu : 0 ≤ u)
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x')) (4 / (n : ℝ) * a))
    (hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        (gW (dotp v v')))
    (hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => gW (dotp uu.1 uu.2)) w)
    (hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) u) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[6] 0) (4 / (n : ℝ) * (a + w + u)) := by
  have := lawU2_prob hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk4 : Measurable (kappa^[4]) := (continuous_kappa.iterate 4).measurable
  have hkk : Measurable (fun t : ℝ => kappa (kappa t)) :=
    (continuous_kappa.comp continuous_kappa).measurable
  have mt : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      tX (N := N) (mW := mW) (n := n) (ω.1, ω.2.1)) :=
    measurable_tX.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have md : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      dotp ω.1.1 ω.1.2) :=
    measurable_dotp_comp (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
  -- link 1: the networks `A`, `F`
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
  -- link 2: the World network
  have m2 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      4 / (n : ℝ) * (kappa^[4] (tX (ω.1, ω.2.1)) - kappa^[4] (kappa (kappa (dotp ω.1.1 ω.1.2))))) :=
    ((hk4.comp mt).sub (hk4.comp (hkk.comp md))).const_mul _
  have A2 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        4 / (n : ℝ) * (kappa^[4] (tX (ω.1, ω.2.1)) - kappa^[4] (kappa (kappa (dotp ω.1.1 ω.1.2)))))
      (4 / (n : ℝ) * w) := by
    refine L2le.prod' m2.aestronglyMeasurable (hgW.const_mul_nonneg (c := 4 / (n : ℝ))
      (by positivity)) ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have m2' := m2.comp (measurable_prodMk_left (x := uu))
    have h0 := ((hW uu.1 uu.2 huu.1 huu.2).const_mul_nonneg (c := 4 / (n : ℝ))
      (by positivity)).comp_fst
      (ν := (mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
    unfold lawR
    refine L2le.of_abs_le m2'.aestronglyMeasurable h0 (fun r => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact iter4_lip (tX_mem hn (uu, r.1)) (kk_memIcc (dotp_unit_mem huu.1 huu.2))
  -- link 3: the inputs
  have m3 : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      4 / (n : ℝ) * (kappa^[4] (kappa (kappa (dotp uu.1 uu.2))) - kappa^[4] (kappa (kappa 0)))) :=
    ((hk4.comp (hkk.comp (measurable_dotp_comp measurable_fst measurable_snd))).sub
      measurable_const).const_mul _
  have A3 : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        4 / (n : ℝ) * (kappa^[4] (kappa (kappa (dotp ω.1.1 ω.1.2))) - kappa^[4] (kappa (kappa 0))))
      (4 / (n : ℝ) * u) := by
    have h0 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
        4 / (n : ℝ) * (kappa^[4] (kappa (kappa (dotp uu.1 uu.2))) - kappa^[4] (kappa (kappa 0))))
        (4 / (n : ℝ) * u) := by
      refine L2le.of_abs_le_ae m3.aestronglyMeasurable
        (hU.const_mul_nonneg (c := 4 / (n : ℝ)) (by positivity)) ?_
      filter_upwards [lawU2_ae_unit hN] with uu huu
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact iter4_lip (kk_memIcc (dotp_unit_mem huu.1 huu.2)) (kk_memIcc KGood.zero_mem)
    exact h0.comp_fst
  have h12 := A1.add0 A2 (by positivity) (by positivity)
  have h123 := h12.add0 A3 (by positivity) (by positivity)
  refine (h123.congr_fun fun ω => ?_).congr_bound (by ring)
  have e6 : kappa^[4] (kappa (kappa 0)) = kappa^[6] 0 := rfl
  rw [e6]
  ring

/-- **The cross kernel**: `‖k_{A,A′}(x(u), x(u′)) − (4/n)·κ(κ(0))‖₂ ≤ (4/n)·b`. -/
theorem kernCross_L2 (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hX : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.2.1 x x' - 4 / (n : ℝ) * kappa (kappa 0)) (4 / (n : ℝ) * b)) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false true false ω - 4 / (n : ℝ) * kappa (kappa 0)) (4 / (n : ℝ) * b) := by
  have := lawU2_prob hN
  have m1 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kgen false true false ω - 4 / (n : ℝ) * kappa (kappa 0)) :=
    (measurable_kgen false true false).sub measurable_const
  refine L2le.prod_const m1.aestronglyMeasurable (Filter.Eventually.of_forall fun uu => ?_)
  have m1' := m1.comp (measurable_prodMk_left (x := uu))
  unfold lawR
  refine L2le.prod_const m1'.aestronglyMeasurable (Filter.Eventually.of_forall fun W => ?_)
  exact hX (xW W uu.1) (xW W uu.2) (normSq_xW hn W uu.1) (normSq_xW hn W uu.2)

/-- **The diagonal kernel**: `‖k_{A,A}(x(u), x(u)) − 4/n‖₂ ≤ (4/n)·eV`. -/
theorem kernDiag_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false true ω - 4 / (n : ℝ)) (4 / (n : ℝ) * eV n mA mF) := by
  have := lawU2_prob hN
  have m1 : Measurable (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
      kgen false false true ω - 4 / (n : ℝ)) :=
    (measurable_kgen false false true).sub measurable_const
  refine L2le.prod_const m1.aestronglyMeasurable (Filter.Eventually.of_forall fun uu => ?_)
  have m1' := m1.comp (measurable_prodMk_left (x := uu))
  unfold lawR
  refine L2le.prod_const m1'.aestronglyMeasurable (Filter.Eventually.of_forall fun W => ?_)
  exact (kern_diag_L2 hn hmA hmF (normSq_xW hn W uu.1)).congr_fun fun p => by
    rw [kgen_diag_eq]

end Kernels

/-! ## Item 2: the conditional expectation over the inputs -/

/-- The kernel with `A′` at both inputs has the same distribution as with `A`. -/
lemma swap_L2 (hN : 1 ≤ N) (dg : Bool) {c e : ℝ}
    (h : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false dg ω - c) e) :
    L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen true true dg ω - c) e := by
  have := lawU2_prob hN
  have hmap := Measure.map_prod_map (lawU2 N) (lawR N mW n mA mF) (f := id) (g := swapA)
    measurable_id measurable_swapA
  rw [Measure.map_id, lawR_swapA] at hmap
  have hm : Measurable (Prod.map (id : (Fin N → ℝ) × (Fin N → ℝ) → _)
      (swapA (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF))) :=
    measurable_id.prodMap measurable_swapA
  exact h.comp_map hm hmap.symm

/-- **Item 2** (`Var(P) ≤ Var(k)`): for `P(W, A, A′, F) = E_{u,u′} k`, a conditional expectation
of the two-input kernel `k`, and every constant `c`: `‖P − c‖₂ ≤ ‖k − c‖₂`. -/
theorem section_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) (pa pa' dg : Bool) {c e : ℝ}
    (h : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kgen pa pa' dg ω - c) e) :
    L2le (lawR N mW n mA mF)
      (fun r : Rest N mW n mA mF => (∫ uu, kgen pa pa' dg (uu, r) ∂lawU2 N) - c) e := by
  have := lawU2_prob hN
  have h1 := h.integral_left
  refine h1.congr_ae ?_
  have hi := kgen_integrable (mW := mW) (mA := mA) (mF := mF) hn hN pa pa' dg
  filter_upwards [hi.prod_left_ae] with r hr
  rw [integral_sub hr (integrable_const c)]
  simp

/-- A function with `‖f − c‖₂ ≤ e` is in `L²`. -/
lemma memLp_of_L2le_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} {c e : ℝ} (h : L2le μ (fun ω => f ω - c) e) : MemLp f 2 μ := by
  have h2 : MemLp (fun ω => f ω - c) 2 μ := (memLp_two_iff_integrable_sq h.aesm).2 h.int_sq
  have := h2.add (memLp_const c)
  refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
  simp

/-- **Item 2 in the form `Var(P) ≤ Var(k)`**: for each of the five kernels `k` (in `L²`) and
`P(W, A, A′, F) = E_{u,u′} k`, the conditional expectation of `k` given the four networks. -/
theorem var_section_le (hn : 1 ≤ n) (hN : 1 ≤ N) (pa pa' dg : Bool)
    (h2 : MemLp (kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg) 2
      ((lawU2 N).prod (lawR N mW n mA mF))) :
    Var[fun r : Rest N mW n mA mF => ∫ uu, kgen pa pa' dg (uu, r) ∂lawU2 N;
        lawR N mW n mA mF] ≤
      Var[kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg;
        (lawU2 N).prod (lawR N mW n mA mF)] := by
  have := lawU2_prob hN
  have hm := measurable_kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg
  have hv := variance_eq_integral (μ := (lawU2 N).prod (lawR N mW n mA mF)) hm.aemeasurable
  have hv0 : 0 ≤ Var[kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg;
      (lawU2 N).prod (lawR N mW n mA mF)] := variance_nonneg _ _
  have hL : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF => kgen pa pa' dg ω -
        ∫ ω, kgen pa pa' dg ω ∂((lawU2 N).prod (lawR N mW n mA mF)))
      (√(Var[kgen (N := N) (mW := mW) (n := n) (mA := mA) (mF := mF) pa pa' dg;
        (lawU2 N).prod (lawR N mW n mA mF)])) := by
    refine ⟨(hm.sub measurable_const).aestronglyMeasurable, ?_, ?_⟩
    · exact (h2.sub (memLp_const _)).integrable_sq
    · rw [Real.sq_sqrt hv0, hv]
  have h := variance_le_of_L2le (section_L2 hn hN pa pa' dg hL)
  rwa [Real.sq_sqrt hv0] at h

/-! ## Item 1: the decomposition of `J` and the triangle inequality -/

/-- The constant `c_J = 3·(4/n)κ^{∘6}(0) − 2·(4/n)κ(κ(0)) − 4/n` (it need not be `E J`). -/
noncomputable def cJ (n : ℕ) : ℝ :=
  3 * (4 / (n : ℝ) * kappa^[6] 0) - 2 * (4 / (n : ℝ) * kappa (kappa 0)) - 4 / (n : ℝ)

/-- **Item 1.** `J − c_J = (3/2)[(P_A − c₂) + (P_{A′} − c₂)] − 2(P_{AA′} − c₁₁) −
[(V_A − S) + (V_{A′} − S)]/2`, and the `L²` triangle inequality:
`‖J − c_J‖₂ ≤ 3·e_P + 2·e_× + e_V` from the `L²` bounds of the three kernels. -/
theorem J_L2 (hn : 1 ≤ n) (hN : 1 ≤ N) {eP eC eD : ℝ} (hP : 0 ≤ eP) (hC : 0 ≤ eC) (hD : 0 ≤ eD)
    (hSame : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false false ω - 4 / (n : ℝ) * kappa^[6] 0) eP)
    (hCross : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false true false ω - 4 / (n : ℝ) * kappa (kappa 0)) eC)
    (hDiag : L2le ((lawU2 N).prod (lawR N mW n mA mF))
      (fun ω : ((Fin N → ℝ) × (Fin N → ℝ)) × Rest N mW n mA mF =>
        kgen false false true ω - 4 / (n : ℝ)) eD) :
    L2le (lawAll N mW n mA mF) (fun t => Jall t - cJ n) (3 * eP + 2 * eC + eD) := by
  have s1 := section_L2 hn hN false false false hSame
  have s2 := section_L2 hn hN true true false (swap_L2 hN false hSame)
  have s3 := section_L2 hn hN false true false hCross
  have s4 := section_L2 hn hN false false true hDiag
  have s5 := section_L2 hn hN true true true (swap_L2 hN true hDiag)
  have t12 := (s1.add0 s2 hP hP).const_mul_nonneg (c := 3 / 2) (by norm_num)
  have t3 := (s3.const_mul_nonneg (c := 2) (by norm_num)).neg
  have t45 := ((s4.add0 s5 hD hD).const_mul_nonneg (c := 1 / 2) (by norm_num)).neg
  have tot := (t12.add0 t3 (by positivity) (by positivity)).add0 t45 (by positivity)
    (by positivity)
  have hR : L2le (lawR N mW n mA mF) (fun r : Rest N mW n mA mF => Jall (toAll r) - cJ n)
      (3 * eP + 2 * eC + eD) := by
    refine (tot.congr_fun fun r => ?_).congr_bound (by ring)
    rw [Jall_toAll hn hN r]
    unfold cJ
    ring
  have hm : AEStronglyMeasurable (fun t => Jall t - cJ n)
      ((lawR N mW n mA mF).map toAll) :=
    ((measurable_Jall hN).sub measurable_const).aestronglyMeasurable
  have := L2le.of_comp_map measurable_toAll hm hR
  rwa [lawR_map] at this

/-! ## The variance of `J` -/

/-- **The variance of `J` from the bounds of the links.** With `a` for the links `F`, `A_3`, `A_2`,
`A_1` of the same-`A` kernel, `b` for the cross kernel, `g_W`, `w` for the World network and `u`
for the inputs: `Var J ≤ ((4/n)·(3(a + w + u) + 2b + eV))²`. -/
theorem varJ_of_bounds (hn : 1 ≤ n) (hN : 1 ≤ N) (hmA : 1 ≤ mA) (hmF : 1 ≤ mF)
    {a b w u : ℝ} {gW : ℝ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (hu : 0 ≤ u)
    (hS : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.1 x x' - 4 / (n : ℝ) * kappa^[4] (dotp x x')) (4 / (n : ℝ) * a))
    (hX : ∀ x x' : Fin n → ℝ, normSq x = 1 → normSq x' = 1 →
      L2le ((mlpGauss n mA n).prod ((mlpGauss n mA n).prod (mlpGauss n mF 1)))
        (fun p : MlpParam n mA n × MlpParam n mA n × MlpParam n mF 1 =>
          kern p.2.2 p.1 p.2.1 x x' - 4 / (n : ℝ) * kappa (kappa 0)) (4 / (n : ℝ) * b))
    (hW : ∀ v v' : Fin N → ℝ, normSq v = 1 → normSq v' = 1 →
      L2le (mlpGauss N mW n)
        (fun W : MlpParam N mW n => dotp (xW W v) (xW W v') - kappa (kappa (dotp v v')))
        (gW (dotp v v')))
    (hgW : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => gW (dotp uu.1 uu.2)) w)
    (hU : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - kappa (kappa 0)) u) :
    Var[Jall; lawAll N mW n mA mF] ≤
      (4 / (n : ℝ) * (3 * (a + w + u) + 2 * b + eV n mA mF)) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : 0 ≤ eV n mA mF := Real.sqrt_nonneg _
  have h1 := kernSame_L2 (mW := mW) hn hN ha hw hu hS hW hgW hU
  have h2 := kernCross_L2 (N := N) (mW := mW) hn hN hX
  have h3 := kernDiag_L2 (N := N) (mW := mW) hn hN hmA hmF
  have hJ := J_L2 hn hN (by positivity) (by positivity) (by positivity) h1 h2 h3
  have := variance_le_of_L2le hJ
  refine this.trans (le_of_eq ?_)
  ring

end BstLean.Part133

open BstLean.Part133 in
#print axioms var_section_le
open BstLean.Part133 in
#print axioms J_L2
open BstLean.Part133 in
#print axioms varJ_of_bounds
